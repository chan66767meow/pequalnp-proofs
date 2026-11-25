"""Match a public catalog against a precomputed generic AO witness cache."""
import argparse
import collections
import json
import pathlib
import re

p = argparse.ArgumentParser()
p.add_argument('catalog')
p.add_argument('--cache', default=str(pathlib.Path(__file__).with_name('cache7.json')))
p.add_argument('--output')
args = p.parse_args()
catalog_path = pathlib.Path(args.catalog)
catalog = json.loads(catalog_path.read_text())
cache = json.loads(pathlib.Path(args.cache).read_text())
nodes = cache['nodes']

def gates(node):
    out = []
    wire = {i: i for i in range(6)}
    def visit(j):
        if j not in wire:
            op, a, b = nodes[j]
            a, b = visit(a), visit(b)
            wire[j] = 6 + len(out)
            out.append(['and' if op == 0 else 'or', a, b])
        return wire[j]
    output = visit(node)
    return out, output

pattern = re.compile(r'(\d{1,10})\s*\*\s*2\s*\^\s*32\s*\+\s*(\d{1,10})')
matches = []
for g in catalog['gaps']:
    m = pattern.search(g.get('title', '')) or pattern.search(g.get('statement', ''))
    if not m:
        continue
    t = int(m[1])*2**32 + int(m[2])
    entry = cache['tables'].get(str(t))
    if entry is None:
        continue
    gs, output = gates(entry['node'])
    matches.append({k: g.get(k) for k in ('id', 'title', 'statement', 'file', 'level',
                                        'depth', 'pr_open', 'pr_numbers', 'sketch')} |
                   {'table': t, 'positive': not g.get('statement', '').lstrip().startswith('¬'),
                    'gate_count': len(gs), 'family': entry['family'],
                    'witness_gates': gs, 'output': output})
report = {'catalog': str(catalog_path), 'catalog_updated_at': catalog.get('updated_at'),
          'cache': args.cache,
          'note': 'Catalog matching only; no lease or lower-bound proof is claimed.',
          'matches': matches}
output_path = pathlib.Path(args.output) if args.output else catalog_path.with_name(catalog_path.stem+'-matches7.json')
output_path.write_text(json.dumps(report, indent=2, ensure_ascii=False))
positive = [g for g in matches if g['positive']]
print(json.dumps({'catalog_updated_at': catalog.get('updated_at'),
                  'rows': len(matches), 'positive_rows': len(positive),
                  'positive_gate_counts': dict(collections.Counter(g['gate_count'] for g in positive)),
                  'positive_without_pr': [{'id': g['id'], 'gate_count': g['gate_count'],
                                           'family': g['family']} for g in positive if not g['pr_numbers']],
                  'output': str(output_path)}, ensure_ascii=False, indent=2))
