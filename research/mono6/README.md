# Reusable circuit methods

Research work prepared for chan66767meow on 2026-11-26 (Asia/Tokyo).

These files are **research methods**, not accepted proofs of an assigned desk gap. This branch has no upstream proof pull request. The finite circuit cache is partial: absence from it proves no lower bound.

## Checked results

- `NotPremiumFromBinarySupport.lean`: an all-essential n-input Boolean function needs at least n-1 non-NOT gates in the project's fan-in-two circuit model. If an AND/OR witness has at most n gates, every signed circuit size bound can be matched by an AND/OR circuit. Lean exited 0 with no diagnostics.
- `SampledBinaryLowerSupport.lean`: a parameterized sample-separation lower-bound framework, with free complementation, plus the monotone replacement theorem.
- `SyntheticAnd6.lean`: an emitted complete replacement example, checked by Lean in 5.78 seconds.
- `SyntheticThreshold.lean`: an emitted certificate excluding seven or fewer binary gates for threshold three of six, checked by Lean in 9.92 seconds.

The support and compilation architecture is adapted from [PR17808](https://github.com/open-goat/pequalnp-proofs/pull/17808). Attribution is preserved in the sources. The general essential-input argument, parameterization, bounded generator, independent replay, and witness families were prepared in this research session. No novelty claim is made.

## Reproduce the Lean checks

Use the repository's pinned Lean 4.36.0 and Mathlib commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. Run the normal project setup first. From the repository root:

```bash
cd lean
lake env lean ../research/mono6/NotPremiumFromBinarySupport.lean
lake env lean ../research/mono6/SampledBinaryLowerSupport.lean
lake env lean ../research/mono6/SyntheticAnd6.lean
lake env lean ../research/mono6/SyntheticThreshold.lean
```

Verification JSON files record the checked bytes and timings. The generalized support proof is not claimed to establish the stronger witness-size-at-most-n+1 extension.

## Bounded certificate search

`sampled_binary.py` constructs 32 true and 32 false sample rows, validates them, invokes a bounded single-thread C++ search, offers an independent Python replay, and emits standalone Lean. The C++ executable is not trusted: the emitted proof repeats the finite check with `decide +kernel`.

For an m-gate AO witness, excluding m-2 binary gates is enough: a competing circuit with a NOT would have at least m total gates; a circuit without NOT already qualifies. See [the detailed method guide](SAMPLED_BINARY_README.md) for commands and limits.

## Witness families

The scripts under [family](family/) generate and validate witnesses on all 64 assignments:

| Maximum gates | Distinct all-essential truth tables |
|---|---:|
| 6 | 26,864 |
| 7 | 116,584 |
| 8 | 332,612 |

The largest extension took 18.2 seconds under a 2 GiB address-space limit. This covers specified formula and shared-subcircuit families, not every circuit of those sizes.

Against the public catalog snapshot at 2026-11-25 17:44:47 UTC, the eight-gate cache matched 323 positive task statements; all already had at least one PR. A PR is not an accepted verdict. Read [family/README.txt](family/README.txt) for the exact scope.

Only work on assigned gaps, use the exact statement and required namespace, and run the current project checks before any future proof submission. This research branch is not a substitute for that process.
