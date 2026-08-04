# FreeFermionGraphs

Lean 4 formalisation effort for the graph-theoretic results in
*A Unified Graph-Theoretic Framework for Free-Fermion Solvability* by Adrian
Chapman, Samuel J. Elman, and Ryan L. Mann.

The checked-in development currently concentrates on finite claw-free graph
theory, hole deformations, token sliding, and the Definition 19 obstruction
search. It does not yet contain the Pauli/Hamiltonian operator algebra needed
to state or prove the manuscript's charge commutators, transfer-operator
identities, free-fermion reconstruction, or operator-Krylov formula.

## Toolchain

The repository currently uses:

- Lean 4.32.0
- mathlib through Lake

Install Lean with `elan`, then build the complete project with:

```bash
lake update
lake build
```

The current finite Lemma 14 bridge can be checked first with:

```bash
lake build FreeFermionGraphs.ObstructionSearchFiniteMixedExecutablePaperLemma14
```

## Current proof status

The main active proof program is the graph-combinatorial route toward Theorem
1(iii). The finite terminal-analysis route for manuscript Lemma 14 is imported
by `FreeFermionGraphs.lean` and exposes the conditional theorem

```lean
InitializationFiniteMixedSideExecutableLemma14Data.paperLemma14_of_executableData
```

This theorem proves the exact four-part `PaperLemma14Conclusion` from an
additional `InitializationFiniteMixedSideExecutableLemma14Data` premise and
claw-freeness. The additional premise is not yet constructed from
`InitializationFiniteMixedSideTerminalCoreData` alone.

The current route derives several important terminal facts rather than storing
the final Lemma 14 conclusion:

- terminal parity and endpoint-side facts are derived from coordinates of the
  form `j₀-k₀-⋯-k_(ℓ-1)-j_ℓ`;
- external degree is transported through finite `single` and `snoc` executions
  once local target balance has been supplied for each block;
- clone-to-flank adjacency is derived from an adjacent tether-link coordinate;
- unequal-centre traces must carry an `IsGenerated` derivation built from the
  finite `start` and `snoc` constructors.

The remaining fidelity boundary is substantive. The repository must still
derive the terminal coordinate package, local target-balance proofs, stopping
link data, and the propagation constructors' local avoidance and adjacency
inputs directly from the literal Definition 19/20 obstruction search. Until
that constructor exists, there is deliberately no unqualified theorem named
`paperLemma14`.

| Manuscript layer | Status |
|---|---|
| Finite claw-free graph theory, including Lemmas 6-10 | Lean implementations exist; complete paper-facing audit remains |
| Token sliding, deformation closures, and generalized-cycle sums | Combinatorial and generic additive definitions exist; operator charges are absent |
| Theorem 1(i)-(iii) | Not formalised at manuscript operator level |
| Lemma 11(a)-(b) | Substantial finite and mixed-side implementations exist; final statement and constructor audit remains |
| Corollary 11 | Proved on bounded mixed-side finite histories |
| Lemmas 12-13 | Implemented on supporting deformation interfaces; statement audit remains |
| Lemma 14(i)-(iv) | Exact conclusion proved conditionally from `InitializationFiniteMixedSideExecutableLemma14Data`; unconditional manuscript theorem remains open |
| Lemmas 15-18 | Not formalised as complete manuscript lemmas; some underlying graph definitions exist |
| Theorem 2 | Not formalised |
| Theorem 3 and Corollary 1 | Not formalised |

The next critical path is:

1. construct `InitializationFiniteMixedSideExecutableLemma14Data` from the
   literal initialized Definition 19/20 obstruction-search execution;
2. derive local target balance and the unequal-centre propagation inputs rather
   than accepting them in generated-data constructors;
3. expose an unqualified `paperLemma14` only after that provenance boundary is
   discharged;
4. formalise Lemmas 15-16 and complete the remaining combinatorial route to
   Theorem 1(iii);
5. introduce the Pauli/frustration-graph algebra required for Theorem 1;
6. formalise the exact free-fermion solution of Theorem 2 and the Krylov
   construction of Theorem 3.

## Manuscript fidelity policy

A successful `lake build` proves that the Lean terms typecheck. It does not by
itself establish that a theorem has the same hypotheses, quantifiers,
deformation stage, and conclusion as the manuscript.

Paper-facing results are therefore gated by
[`docs/PAPER_FIDELITY.md`](docs/PAPER_FIDELITY.md). In particular:

- every manuscript object must be matched to a Lean object;
- hole stages and degree expressions must be explicit;
- additional premises must be documented in theorem names and docstrings;
- boundary certificates may not appear in an unqualified paper theorem;
- an unqualified paper theorem must have no additional premise beyond the
  manuscript setup;
- any remaining constructor or provenance boundary must be recorded explicitly.

This policy is especially important for Definition 19, where one
fixed-pairing deformation may contain paths from both component families. A
one-sided or infinitely extended history cannot be used as the final
representation of the manuscript search.

## Repository layout

- `FreeFermionGraphs/`: individual definitions, lemmas, and integration modules
- `FreeFermionGraphs.lean`: root import for the complete development
- `FORMALIZATION.md`: dependency-oriented proof plan
- `docs/PAPER_FIDELITY.md`: current manuscript correspondence, provenance, and
  open proof boundaries
- `docs/PAPER_AUDIT_2026-08-01.md`: historical audit at the PR #196 baseline

## Development workflow

Every pull request touching a numbered manuscript result should be validated
with both a focused module build and the full project build:

```bash
lake build FreeFermionGraphs.<ModuleName>
lake build
```

A pull request should not be merged until the exact head has passed the
corresponding validation gate.
