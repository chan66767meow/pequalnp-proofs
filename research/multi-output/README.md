# Two shared-input outputs require six gates

## Status

This is a locally kernel-checked proof of the exact proposition posted as L-meta-15074. It is preserved in this personal research branch. It has **not been submitted to, accepted by, or credited by the upstream project**.

Lean 4.36.0 checked `TwoOutputConjunction.lean` with exit code 0 and no diagnostics on 2026-11-26 at 03:30 JST (2026-11-25 at 18:30 UTC). The source SHA256 is `52ab3dd8fc5c219594a76b8b59d05337f46c9862b2bdaed6b8ec9ce67ef71843`.

After this check, the project's documented checked-proof route issued a racing lease. The official `tools/pnp.sh check L-meta-15074` then stopped with exit code 3 because the step was `pr_open`: an earlier pull request, https://github.com/open-goat/pequalnp-proofs/pull/19040, was awaiting review. The script was not bypassed. The lease was returned as `other`.

## Proposition and proof

On six Boolean inputs, consider

- F = (x0 AND x2) OR (x1 AND x3)
- G = (x0 AND x4) OR (x1 AND x5)

No single fan-in-at-most-two circuit using at most five total AND, OR and NOT gates computes both designated outputs. All NOT gates count toward the five-gate limit. The output indices are arbitrary, using the project's default-false `getD` semantics.

Append one AND gate reading the two designated outputs. The resulting circuit computes F AND G. The certificate establishes that this conjunction requires more than six non-NOT gates, even with free complementation. A circuit with five original gates plus one appended AND would have at most six non-NOT gates, which is a contradiction.

The conjunction truth table and all sample labels are checked by Lean. The finite search uses `decide +kernel`; no `native_decide`, new axiom, or `sorry` is used. Independent Python and C++ replays each rejected the six-binary-gate case after 85 visited states. Those external replays are evidence only; the Lean proof is the local verification result.

The lower bound is sharp: computing each of F and G with two AND gates and one OR gate uses six gates in total. This is a small circuit lower bound, not a resolution of P versus NP.

## Files and attribution

- `TwoOutputConjunction.lean`: complete self-contained Lean proof; imports only `PEqualNP.Defs`.
- `certificate.json`: sampled finite-search input and independent replay results.
- `verification.json`: local kernel-check record.
- `submission-status.json`: the official submission guard result.

The build/live/search framework and free-NOT compilation argument are adapted from https://github.com/open-goat/pequalnp-proofs/pull/17808. They are reused and attributed, not claimed as original here. The appended-output construction and its concrete instantiation are included in this research file.

To check in the project's pinned environment, run `lake env lean PATH/TwoOutputConjunction.lean` from the `lean` directory.
