"""A bounded generic eight-gate family: three inputs duplicated in a formula.

All six variables are essential. This does not enumerate all eight-gate
circuits and does not prove any named catalog statement.
"""
import itertools
import json
import signal
import time
import extend_family7 as e

b = e.b
signal.alarm(55)
start = time.monotonic()
family = dict(e.family)
candidate_rows = {}
for g in b.catalog['gaps']:
    if g.get('statement', '').lstrip().startswith('¬') or g.get('pr_numbers'):
        continue
    m = b.pattern.search(g.get('title', '')) or b.pattern.search(g.get('statement', ''))
    if m:
        candidate_rows.setdefault(int(m[1])*2**32+int(m[2]), []).append(g)
seen_candidates = set()

for k, repeated in enumerate(itertools.combinations(range(6), 3)):
    counts = [1]*6
    for i in repeated:
        counts[i] = 2
    out = e.formulas(tuple(counts))
    for t, node in out.items():
        family.setdefault(t, {'node': node, 'family': 'three_distinct_repeated_inputs'})
    new_candidates = []
    for t in candidate_rows.keys() & family.keys():
        if t in seen_candidates:
            continue
        seen_candidates.add(t)
        entry = family[t]
        gs, output = b.gates(entry['node'])
        assert len(gs) <= 8
        new_candidates.extend({'id': g['id'], 'table': t, 'gate_count': len(gs),
                               'family': entry['family'], 'witness_gates': gs, 'output': output,
                               'statement': g['statement'], 'pr_numbers': g.get('pr_numbers')}
                              for g in candidate_rows[t])
    if new_candidates:
        path = b.root/'eight-gate-candidates-live.json'
        previous = json.loads(path.read_text()) if path.exists() else []
        existing = {g['id'] for g in previous}
        previous.extend(g for g in new_candidates if g['id'] not in existing)
        path.write_text(json.dumps(previous, indent=2, ensure_ascii=False))
    print(json.dumps({'phase': 'eight_gate_formula', 'pattern': k+1,
                      'repeated_inputs': repeated, 'pattern_tables': len(out),
                      'total_tables': len(family), 'nodes': len(b.nodes),
                      'new_positive_without_pr': [g['id'] for g in new_candidates],
                      'seconds': time.monotonic()-start}), flush=True)

for t, entry in family.items():
    gs, output = b.gates(entry['node'])
    entry['gates'] = len(gs)
    assert len(gs) <= 8
    bank = list(b.inputs)
    for op, a, c in gs:
        assert a < len(bank) and c < len(bank)
        bank.append(bank[a] & bank[c] if op == 'and' else bank[a] | bank[c])
    assert bank[output] == t and b.essential(t) == 63
cache = {'description': __doc__, 'variables': 6, 'nodes': b.nodes,
         'tables': {str(t): entry for t, entry in family.items()},
         'seconds': time.monotonic()-start}
with (b.root/'cache8.json').open('w') as f:
    json.dump(cache, f, separators=(',', ':'))
print(json.dumps({'phase': 'saved8', 'tables': len(family), 'nodes': len(b.nodes),
                  'positive_without_pr_count': len(seen_candidates),
                  'seconds': time.monotonic()-start}), flush=True)
