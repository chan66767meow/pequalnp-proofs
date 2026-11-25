SIX-VARIABLE AO WITNESS FAMILY CACHE

Purpose
  Reusable witness generation and catalog matching. These tools do not lease a
  task, create a named Lean theorem, or establish a circuit lower bound.

Verified witness counts
  cache.json   :  26,864 tables;  45,072 expression nodes;  2,560,746 bytes.
                 5,504 witnesses of 5 gates; 21,360 of 6 gates.
  cache7.json  : 116,584 tables; 234,170 expression nodes; 12,342,354 bytes.
                 Above plus 89,720 witnesses of 7 gates.
  cache8.json  : 332,612 tables; 899,939 expression nodes; 40,646,784 bytes.
                 Above plus 216,028 witnesses of 8 gates.

Exact structural scope
  1. Read-once AND/OR formulas on all six inputs.
  2. Formulas with one input repeated twice, and a disjoint read-once context.
  3. One shared read-once subcircuit substituted for the repeated input.
  4. Formulas with two extra input occurrences: either one input occurs three
     times, or two inputs each occur twice. Together with one shared read-once
     macro these produce additional witnesses with at most seven gates.
  5. Two disjoint shared read-once cores of sizes (2,2) or (2,3), substituted
     into a small exterior formula in which both macro inputs occur twice.
  6. An eight-gate formula family: three distinct inputs each occur twice,
     while the remaining three occur once. All 20 such multiplicity patterns
     were processed.

  These are structural witness families, not an exhaustive enumeration of all
  circuits with six, seven, or eight gates. In particular, absence from a cache
  is not a lower-bound certificate. No NOT circuits are enumerated.

Validation
  Every cached output was compiled to a topologically ordered binary AO gate
  list. Its full 64-bit evaluation was compared with its table, all six inputs
  were checked essential, and the recorded gate bound was checked. This is a
  computational witness audit, not a Lean proof or official project acceptance.

Encoding
  tables maps decimal 64-bit table strings to {node, family, gates} records.
  nodes[0..5] are [-1,i,i], the six input nodes. Later nodes [op,a,b] use op=0
  for AND, op=1 for OR, and refer to earlier node indices. Equal referenced
  nodes are shared. match_catalog.py compiles these nodes into gate lists with
  inputs 0..5 and successive gate-output numbers beginning at 6.

Commands (from the repository root)
  /workspace/scratch/b7ac7794fbe9/pnp-tools-venv/bin/python \
    research/mono6/family/build_family.py --catalog PATH_TO_GAPS_JSON
  /workspace/scratch/b7ac7794fbe9/pnp-tools-venv/bin/python \
    research/mono6/family/extend_family7.py --catalog PATH_TO_GAPS_JSON
  /workspace/scratch/b7ac7794fbe9/pnp-tools-venv/bin/python \
    research/mono6/family/extend_family8.py --catalog PATH_TO_GAPS_JSON
  /workspace/scratch/b7ac7794fbe9/pnp-tools-venv/bin/python \
    research/mono6/family/match_catalog.py PATH_TO_GAPS_JSON \
    --cache research/mono6/family/cache8.json --output OUTPUT_JSON

  Generation uses support/multiplicity dynamic programming, not gate-by-gate
  circuit search. The observed generation/extension times were approximately
  0.5 seconds, 4.4 seconds, and 18.2 seconds, respectively. Generators have a
  2 GiB address-space cap. The eight-gate extension resets its alarm to 55
  seconds after the approximately five-second lower-family preparation.

Latest observed catalog match
  Snapshot: 2026-11-25T17:44:47.387Z, saved as gaps-refresh.json.
  cache8.json matches 646 rows: 323 positive and 323 negative.
  Positive witnesses: 3 of 6 gates, 82 of 7 gates, 238 of 8 gates.
  Every matched positive row already had at least one PR in that snapshot.
  No matched positive row without a PR was found. PR absence, if encountered
  later, must not be mistaken for availability: only the desk can grant a lease.
  Exact row statements, PR metadata and witnesses: catalog-matches8.json.

Documented desk filters (tools/pnp.sh)
  next accepts --hard, --another, --level, --kind, --proof-of.
  There is no documented direction or topic selector; unknown flags fail.
  --proof-of sends gap=<id>&have=proof and requires a truly held checked proof.
  Normal next includes value=1. These tools do not call next or --proof-of.

Status
  Generic preparation completed and broadening stopped. No active process,
  lease, named proof, or submission was created by this family-generation task.
