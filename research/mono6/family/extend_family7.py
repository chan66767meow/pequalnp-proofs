"""Add AO formulas with two extra variable occurrences and shared macros.

This enumerates fixed leaf-multiplicity patterns, not arbitrary circuits.
"""
import itertools
import json
import re
import time
import build_family as b

start = time.monotonic()
memo = {}

def formulas(counts):
    if counts in memo:
        return memo[counts]
    mask = sum(1 << i for i, c in enumerate(counts) if c)
    extra = sum(counts) - mask.bit_count()
    if extra == 0:
        return b.ro[mask]
    out = dict(b.ro[mask])
    for i, c in enumerate(counts):
        if c >= 2:
            out.update(b.rep[(mask, i)])
    if extra == 1:
        memo[counts] = out
        return out
    assert extra in (2, 3)
    for a in itertools.product(*(range(c+1) for c in counts)):
        d = tuple(c-x for c, x in zip(counts, a))
        if not any(a) or not any(d) or a > d:
            continue
        left, right = formulas(a), formulas(d)
        for ta, na in left.items():
            for tb, nb in right.items():
                for op, t in ((0, ta & tb), (1, ta | tb)):
                    if t not in out and b.essential(t) == mask:
                        out[t] = b.make(op, na, nb)
    memo[counts] = out
    return out

family = dict(b.family)
patterns = []
for i in range(6):
    counts = [1]*6
    counts[i] = 3
    patterns.append(tuple(counts))
for i, j in itertools.combinations(range(6), 2):
    counts = [1]*6
    counts[i] = counts[j] = 2
    patterns.append(tuple(counts))
for k, counts in enumerate(patterns):
    out = formulas(counts)
    for t, node in out.items():
        family.setdefault(t, {'node': node, 'family': 'two_extra_occurrences'})
    print(json.dumps({'phase': 'seven_gate_formula', 'pattern': k+1,
                      'pattern_tables': len(out), 'total_tables': len(family),
                      'seconds': time.monotonic()-start}), flush=True)

# Reuse one read-once macro in an exterior formula with two extra occurrences.
for core_size in (2, 3, 4):
    m = 6-core_size+1
    exterior = {}
    for second_repeat in range(m):
        counts = [1]*m + [0]*(6-m)
        counts[0] += 1
        counts[second_repeat] += 1
        exterior.update(formulas(tuple(counts)))
    for core_mask in range(1, 64):
        if core_mask.bit_count() != core_size:
            continue
        remaining = b.bits(63 ^ core_mask)
        assignments = [sum(((x >> var)&1) << (j+1) for j, var in enumerate(remaining))
                       for x in range(64)]
        lifted = []
        for u, node in exterior.items():
            lo = sum(((u >> z)&1) << x for x, z in enumerate(assignments))
            hi = sum(((u >> (z|1))&1) << x for x, z in enumerate(assignments))
            lifted.append((lo, hi, node))
        for core, core_node in b.ro[core_mask].items():
            mapping = [core_node] + remaining
            for lo, hi, node in lifted:
                t = (lo & (b.FULL ^ core)) | (hi & core)
                if t in family or b.essential(t) != 63:
                    continue
                result = b.substitute(node, mapping, {})
                assert b.values[result] == t
                family[t] = {'node': result, 'family': 'shared_macro_two_extra_occurrences'}
    print(json.dumps({'phase': 'seven_gate_shared_macro', 'core_size': core_size,
                      'total_tables': len(family), 'seconds': time.monotonic()-start}), flush=True)

# Two disjoint read-once cores, each reused twice in a small exterior formula.
for size_a, size_b in ((2, 2), (2, 3)):
    m = 6-size_a-size_b+2
    counts = tuple([2, 2]+[1]*(m-2)+[0]*(6-m))
    exterior = formulas(counts)
    for mask_a in range(1, 64):
        if mask_a.bit_count() != size_a:
            continue
        for mask_b in b.submasks(63 ^ mask_a):
            if mask_b.bit_count() != size_b or (size_a == size_b and mask_a > mask_b):
                continue
            remaining = b.bits(63 ^ (mask_a | mask_b))
            assignments = [sum(((x >> var)&1) << (j+2) for j, var in enumerate(remaining))
                           for x in range(64)]
            lifted = []
            for u, node in exterior.items():
                slices = [sum(((u >> (z | choice))&1) << x
                              for x, z in enumerate(assignments)) for choice in range(4)]
                lifted.append((slices, node))
            for ta, na in b.ro[mask_a].items():
                for tb, nb in b.ro[mask_b].items():
                    regions = [(b.FULL ^ ta) & (b.FULL ^ tb), ta & (b.FULL ^ tb),
                               (b.FULL ^ ta) & tb, ta & tb]
                    mapping = [na, nb] + remaining
                    for slices, node in lifted:
                        t = (slices[0]&regions[0]) | (slices[1]&regions[1]) | (slices[2]&regions[2]) | (slices[3]&regions[3])
                        if t in family or b.essential(t) != 63:
                            continue
                        result = b.substitute(node, mapping, {})
                        assert b.values[result] == t
                        family[t] = {'node': result, 'family': 'two_shared_subcircuits'}
    print(json.dumps({'phase': 'seven_gate_two_shared', 'core_sizes': [size_a, size_b],
                      'total_tables': len(family), 'seconds': time.monotonic()-start}), flush=True)

for t, entry in family.items():
    gs, output = b.gates(entry['node'])
    entry['gates'] = len(gs)
    assert len(gs) <= 7
    bank = list(b.inputs)
    for op, a, c in gs:
        assert a < len(bank) and c < len(bank)
        bank.append(bank[a] & bank[c] if op == 'and' else bank[a] | bank[c])
    assert bank[output] == t and b.essential(t) == 63
cache = {'description': __doc__, 'variables': 6, 'nodes': b.nodes,
         'tables': {str(t): e for t, e in family.items()},
         'seconds': time.monotonic()-start}
(b.root/'cache7.json').write_text(json.dumps(cache, separators=(',', ':')))

matches = []
for g in b.catalog['gaps']:
    m = b.pattern.search(g.get('title', '')) or b.pattern.search(g.get('statement', ''))
    if not m:
        continue
    t = int(m[1])*2**32+int(m[2])
    if t not in family:
        continue
    entry = family[t]
    gs, output = b.gates(entry['node'])
    matches.append({k: g.get(k) for k in ('id', 'title', 'statement', 'file', 'level',
                                        'depth', 'pr_open', 'pr_numbers', 'sketch')} |
                   {'table': t, 'positive': not g.get('statement', '').lstrip().startswith('¬'),
                    'gate_count': entry['gates'], 'family': entry['family'],
                    'witness_gates': gs, 'output': output})
report = {'catalog': str(b.catalog_path), 'catalog_updated_at': b.catalog.get('updated_at'),
          'note': 'Catalog matching only; no lease or lower-bound proof is claimed.',
          'matches': matches}
(b.root/'catalog-matches7.json').write_text(json.dumps(report, indent=2, ensure_ascii=False))
print(json.dumps({'phase': 'saved7', 'tables': len(family), 'nodes': len(b.nodes),
                  'catalog_matches': len(matches), 'positive_without_pr':
                  [g['id'] for g in matches if g['positive'] and not g['pr_numbers']],
                  'seconds': time.monotonic()-start}), flush=True)
