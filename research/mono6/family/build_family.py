"""Support-based AO witness families; never leases or proves a named gap.

Enumerates read-once formulas, formulas with one repeated input, and formulas
with one shared read-once subcircuit. This is not gate-by-gate circuit search.
"""
import argparse
import itertools
import json
import pathlib
import resource
import signal
import time

resource.setrlimit(resource.RLIMIT_AS, (2 * 1024**3, 2 * 1024**3))
signal.alarm(300)
p = argparse.ArgumentParser()
p.add_argument('--catalog', default='.pnp/gaps-1737.json')
args = p.parse_args()
root = pathlib.Path(__file__).resolve().parent
start = time.monotonic()
N = 6
FULL = (1 << 64) - 1
inputs = [sum(1 << x for x in range(64) if (x >> i) & 1) for i in range(N)]
zero_masks = [FULL ^ t for t in inputs]
nodes = [[-1, i, i] for i in range(N)]
values = list(inputs)
intern = {}

def make(op, a, b):
    a, b = min(a, b), max(a, b)
    key = (op, a, b)
    if key in intern:
        return intern[key]
    j = len(nodes)
    intern[key] = j
    nodes.append(list(key))
    values.append(values[a] & values[b] if op == 0 else values[a] | values[b])
    return j

def essential(t):
    return sum(1 << i for i in range(N) if ((t ^ (t >> (1 << i))) & zero_masks[i]))

def bits(mask):
    return [i for i in range(N) if (mask >> i) & 1]

def submasks(mask):
    sub = mask
    while sub:
        yield sub
        sub = (sub - 1) & mask

ro = {1 << i: {inputs[i]: i} for i in range(N)}
rep = {}
for size in range(2, N + 1):
    for mask in range(1, 1 << N):
        if mask.bit_count() != size:
            continue
        out = {}
        anchor = mask & -mask
        for a in submasks(mask):
            b = mask ^ a
            if not b or not (a & anchor):
                continue
            for ta, na in ro[a].items():
                for tb, nb in ro[b].items():
                    for op, t in ((0, ta & tb), (1, ta | tb)):
                        if t not in out:
                            out[t] = make(op, na, nb)
        ro[mask] = out
    print(json.dumps({'phase': 'read_once', 'support_size': size,
                      'per_support': len(ro[(1 << size)-1]), 'nodes': len(nodes)}), flush=True)

for size in range(1, N + 1):
    for mask in range(1, 1 << N):
        if mask.bit_count() != size:
            continue
        for repeated in bits(mask):
            rbit = 1 << repeated
            out = {}
            def add(ta, na, tb, nb):
                for op, t in ((0, ta & tb), (1, ta | tb)):
                    if t not in out and t not in ro[mask] and essential(t) == mask:
                        out[t] = make(op, na, nb)
            # At the repeated variable's lowest common ancestor, both sides
            # are read-once and their supports meet in precisely that variable.
            rest = mask ^ rbit
            anchor = rest & -rest
            for a0 in submasks(rest):
                b0 = rest ^ a0
                if not b0 or not (a0 & anchor):
                    continue
                for ta, na in ro[a0 | rbit].items():
                    for tb, nb in ro[b0 | rbit].items():
                        add(ta, na, tb, nb)
            # Above that ancestor, combine with a disjoint read-once context.
            for a in submasks(mask):
                b = mask ^ a
                if not b or not (a & rbit):
                    continue
                for ta, na in rep[(a, repeated)].items():
                    for tb, nb in ro[b].items():
                        add(ta, na, tb, nb)
            rep[(mask, repeated)] = out
    sample = (1 << size) - 1
    print(json.dumps({'phase': 'one_repeated_input', 'support_size': size,
                      'per_designated_input': len(rep[(sample, 0)]), 'nodes': len(nodes)}), flush=True)

family = {t: {'node': n, 'family': 'read_once'} for t, n in ro[63].items()}
for r in range(N):
    for t, n in rep[(63, r)].items():
        family.setdefault(t, {'node': n, 'family': 'one_repeated_input'})
print(json.dumps({'phase': 'before_sharing', 'tables': len(family)}), flush=True)

def substitute(node, mapping, memo):
    if node < N:
        return mapping[node]
    if node not in memo:
        op, a, b = nodes[node]
        memo[node] = make(op, substitute(a, mapping, memo), substitute(b, mapping, memo))
    return memo[node]

# Replace the repeated macro input of a small exterior formula by one
# read-once subcircuit. The identical node is reused at both occurrences.
for core_size in range(2, N):
    exterior_size = N - core_size + 1
    exterior = rep[((1 << exterior_size)-1, 0)]
    if not exterior:
        continue
    for core_mask in range(1, 64):
        if core_mask.bit_count() != core_size:
            continue
        remaining = bits(63 ^ core_mask)
        assignment = [sum(((x >> var) & 1) << (j+1) for j, var in enumerate(remaining))
                      for x in range(64)]
        lifted = []
        for u, exterior_node in exterior.items():
            lo = sum(((u >> z) & 1) << x for x, z in enumerate(assignment))
            hi = sum(((u >> (z | 1)) & 1) << x for x, z in enumerate(assignment))
            lifted.append((lo, hi, exterior_node))
        for core, core_node in ro[core_mask].items():
            mapping = [core_node] + remaining
            for lo, hi, exterior_node in lifted:
                t = (lo & (FULL ^ core)) | (hi & core)
                if t in family or essential(t) != 63:
                    continue
                node = substitute(exterior_node, mapping, {})
                assert values[node] == t
                family[t] = {'node': node, 'family': 'one_shared_subcircuit'}
    print(json.dumps({'phase': 'one_shared_subcircuit', 'core_size': core_size,
                      'tables': len(family), 'nodes': len(nodes)}), flush=True)

def gates(node):
    output = []
    wire = {i: i for i in range(N)}
    def visit(j):
        if j not in wire:
            op, a, b = nodes[j]
            a, b = visit(a), visit(b)
            wire[j] = N + len(output)
            output.append(['and' if op == 0 else 'or', a, b])
        return wire[j]
    result = visit(node)
    return output, result

for t, entry in family.items():
    gs, output = gates(entry['node'])
    entry['gates'] = len(gs)
    assert len(gs) <= 6
    bank = list(inputs)
    for op, a, b in gs:
        assert a < len(bank) and b < len(bank)
        bank.append(bank[a] & bank[b] if op == 'and' else bank[a] | bank[b])
    assert bank[output] == t and essential(t) == 63

cache = {'description': __doc__, 'variables': N, 'nodes': nodes,
         'tables': {str(t): e for t, e in family.items()},
         'seconds': time.monotonic()-start}
(root/'cache.json').write_text(json.dumps(cache, separators=(',', ':')))
print(json.dumps({'phase': 'saved', 'tables': len(family), 'nodes': len(nodes),
                  'seconds': time.monotonic()-start}), flush=True)

# Match existing catalog rows only; this neither solves their lower-bound
# statements nor claims that a listed gap is available for leasing.
import re
catalog_path = pathlib.Path(args.catalog)
catalog = json.loads(catalog_path.read_text())
pattern = re.compile(r'(\d{1,10})\s*\*\s*2\s*\^\s*32\s*\+\s*(\d{1,10})')
matches = []
for g in catalog['gaps']:
    m = pattern.search(g.get('title', '')) or pattern.search(g.get('statement', ''))
    if not m:
        continue
    t = int(m[1]) * 2**32 + int(m[2])
    if t not in family:
        continue
    entry = family[t]
    gs, output = gates(entry['node'])
    matches.append({k: g.get(k) for k in ('id', 'title', 'statement', 'file', 'level',
                                        'depth', 'pr_open', 'pr_numbers', 'sketch')} |
                   {'table': t, 'positive': not g.get('statement', '').lstrip().startswith('¬'),
                    'gate_count': entry['gates'], 'family': entry['family'],
                    'witness_gates': gs, 'output': output})
report = {'catalog': str(catalog_path), 'catalog_updated_at': catalog.get('updated_at'),
          'note': 'Catalog matching only; no lease or lower-bound proof is claimed.',
          'matches': matches}
(root/'catalog-matches.json').write_text(json.dumps(report, indent=2, ensure_ascii=False))
print(json.dumps({'phase': 'matched', 'rows': len(matches),
                  'positive_without_pr': [g['id'] for g in matches if g['positive'] and not g['pr_numbers']]}), flush=True)
