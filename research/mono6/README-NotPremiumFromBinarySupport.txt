Generic no-NOT-advantage method
==============================

Checked file: NotPremiumFromBinarySupport.lean
Namespace: PEqualNP.Research.NotPremiumFromBinarySupport
Project import: PEqualNP.Defs only.
Clean Lean elaboration completed with exit0 and no diagnostics at
2026-11-25 17:39:49 UTC, using the project's Lean4.36.0 environment.
Command, from lean/ after sourcing ../.pnp/env.sh:
  flock ../.pnp/lean-build.lock ../tools/bin/lake env lean \
    ../research/mono6/NotPremiumFromBinarySupport.lean

This is a generic framework in the research workspace, not a proof of an
unleased gap. It makes no external submission and contains no search result.

MAIN API
--------
AllEssential f means that flipping any one input changes f on some assignment:
  forall i, exists x, f x != f (Function.update x i (!(x i))).

essential_binary_bound:
  If C is a FanInTwo AND/OR/NOT circuit computing an AllEssential n-input f,
  then n <= binaryCost C.gates + 1.
binaryCost counts all non-NOT gates (which are AND/OR gates under FanInTwo).

transfer_of_ao_size_le_inputs:
  Given AllEssential f and an explicit AO circuit W computing f with size<=n,
  every HasCircuitSize n f s witness can be replaced by an AO circuit of
  size<=s computing f.

Usage after copying this attributed framework into an allowed namespace in a
leased proof file:

  exact transfer_of_ao_size_le_inputs f hEssential W hMonotone
    hWitnessSize hWitnessCorrect s hs

For a concrete six-input table, hEssential can use six explicit assignments
(one per input), and hWitnessCorrect checks only the64 truth-table inputs.
Neither the generic support bound nor the transfer theorem performs search.

WHY THE PROOF WORKS
-------------------
Symbolic circuit wires are represented as Boolean functions. A signal and
its complement share one available representative, so NOT is free in the
binary-gate lower bound. Every legal AND/OR step either reuses an available
representative/constant, or adds one combination of two representatives.
Backward live-set compression then shows that k such binary steps can join
at most k+1 initially live signals.

For each essential input, an assignment and its one-input flip distinguish
the target. Boolean combination cannot create that distinction unless one
operand already has it. Hence the initial live set must contain every input
projection, so it has at least n members. This proves n<=k+1.

Now inspect an arbitrary signed circuit C computing f. If C has no NOT,
retain C. If it has a NOT, its non-NOT gate count is strictly smaller than
its total size; therefore n<=C.size. The supplied AO witness of size<=n
fits within C's size bound. This handles n=0 as well.

The semantic bridge explicitly handles project-specific cases: nullary and
unary gates, NOT gates with an ignored second input, and invalid/future reads
returning false. It does not impose an extra well-formed-wiring hypothesis.

ATTRIBUTION
-----------
The generic build/live compression and free-complement compilation
architecture is adapted from the proof of L-meta-13647 in PR17808:
https://github.com/open-goat/pequalnp-proofs/pull/17808
The local source was .pnp/13648-analysis/positive13647-pr17808.lean.
Here the signal type is generalized from fixed64-bit vectors to arbitrary
Boolean functions, and essential-input counting replaces certificate search.
The attribution is retained in the Lean source and should be preserved.

ASSESSMENT OF THE AO<=n+1 EXTENSION
---------------------------------
The counting inequality alone does not establish this extension. The only
new boundary case is an essential n-input function computed by a signed
circuit with n-1 binary gates and one NOT, for total size n.

The expected mathematical argument is to prune unused gates and analyze
equality in the support bound. Joining n essential inputs with exactly n-1
binary gates forces a read-once active computation: no sharing or repeated
input occurrence can consume a merge. An active lone NOT then makes the
output decreasing in some input below it, contradicting monotonicity. If
the NOT is unused, remove it and retain the resulting AO computation.

Formalizing that argument requires an equality/read-once theorem plus
pruning or circuit reconstruction, which the present framework does not
yet provide. In particular, it would be false to assert that every small
circuit computing a monotone function has no syntactic NOT: an unused NOT
can always be present. The n+1 extension is NOT claimed as checked here.
