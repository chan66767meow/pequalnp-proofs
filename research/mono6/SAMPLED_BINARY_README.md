# Sampled binary-gate lower certificates

This reusable method handles six-input truth tables. It does not allocate leases,
name a project gap, submit proofs, or run Lean automatically.

The Lean theory is adapted with attribution from
[PR17808](https://github.com/open-goat/pequalnp-proofs/pull/17808), whose compact
proof supplies the `build`, `live`, sample-separation search, and free-NOT
compilation framework. `SampledBinaryLowerSupport.lean` generalizes its target and
gate bound and includes a reusable monotone replacement theorem.

## Mathematical contract

A certificate consists of six 64-bit masks. Bit `k` of mask `i` is input `i` on
sample row `k`. Rows 0–31 must make the target true; rows 32–63 must make it false.
Samples may repeat. The six masks must be distinct.

The search uses `a AND b`, `a OR b`, `a AND NOT b`, and `b AND NOT a`, treating
complementation as free. It considers every subset of initial wires and the
possible ways to retain operands for later reuse. A rejection at budget `n`
therefore implies that every circuit computing the target has **more than `n`
non-NOT gates**.

For an independently validated AO witness of `m` gates, budget `n = m - 2`
suffices for the replacement theorem: a circuit containing a NOT gate has at
least `n + 2` total gates, while one without a NOT is already monotone. The
transfer also permits an AO witness smaller than `n + 2`.

The generator's integer search is computational evidence. The emitted Lean file
rechecks sample labels, rejection, and any supplied witness using
`decide +kernel`; the compiled binary is not trusted by the proof.

## Files

- `sampled_binary_search.cpp`: bounded single-thread C++ search; no dependencies.
- `sampled_binary.py`: sample construction, orchestration, independent Python
  replay, AO witness validation, and standalone Lean emission.
- `SampledBinaryLowerSupport.lean`: attributed, parameterized Lean framework.

## Build and use

From the repository root:

```bash
g++ -O3 -std=c++17 research/mono6/sampled_binary_search.cpp -o research/mono6/sampled_binary_search

python3 research/mono6/sampled_binary.py generate \
  --table 0x8000000000000000 --bound 4 \
  --seconds 20 --attempt-seconds 3 --attempts 8 --nodes 2000000 \
  --output research/mono6/example-certificate.json

python3 research/mono6/sampled_binary.py replay \
  research/mono6/example-certificate.json --engine both --seconds 10

python3 research/mono6/sampled_binary.py emit-lean \
  research/mono6/example-certificate.json \
  --namespace PEqualNP.Generated.Example \
  --output research/mono6/ExampleCertificate.lean
```

The example truth table is the conjunction of all six inputs. For an actual
project proof, use the namespace required by that live assignment. The emitter
inlines the generic support and uses only `import PEqualNP.Defs`; it does not add
an unchecked helper-module dependency.

The optional `--witness PATH` accepts JSON of the form:

```json
{"gates":[["and",0,1],["and",6,2],["and",7,3],["and",8,4],["and",9,5]],"output":10}
```

Alternatively, each gate may be `{"op":"and","inputs":[0,1]}`. Zero- and
one-input AND/OR gates are supported with the project semantics. Every wire must
refer backward. The tool checks the witness on all 64 assignments. If `--bound`
is omitted, it chooses `gate_count - 2`. A supplied witness is embedded in the
certificate and causes Lean emission to include the full generic replacement
theorem for that truth table.

## Status meanings and resource limits

- `exhaustive_rejection`: the bounded search completed and found no sampled
  free-complement circuit within the binary budget.
- `sample_feasible`: the chosen samples admit a small circuit. This is **not** a
  circuit for the entire function or a counterexample to monotone replacement.
- `time_limit`, `node_limit`, or `interrupted`: no rejection certificate was
  established for that attempt.
- `no_rejection_certificate`: all requested attempts ended without a rejection.

The C++ engine has one thread. Each invocation permits at most 60 seconds and
250,000 memoized rejected states; the caller also supplies a node cap. The
generator's overall default is 20 seconds. There are no background workers.
Python replay preserves literal list order, unlike the C++ permutation cache,
and can be considerably slower. A replay timeout does not invalidate or verify
the C++ result; Lean remains the final check.

All Lean invocations must use the project's shared lock:

```bash
source .pnp/env.sh
cd lean
flock ../.pnp/lean-build.lock ../tools/bin/lake env lean ../research/mono6/ExampleCertificate.lean
```

Use an outer wall-clock limit for large generated checks. `decide +kernel` may
take longer than the optimized integer search because it replays the search
without the external memoization cache. No success claim should be made until
the generated Lean file checks and the current project gates pass.
