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

The completed finite Lemma 14 integration can be checked first with:

```bash
lake build FreeFermionGraphs.ObstructionSearchFiniteMixedLemma14History
```

## Current proof status

The finite Definition 19/20 route now exposes the unqualified theorem

```lean
InitializationFiniteMixedSideLemma14History.paperLemma14
```

with hypotheses

```lean
(H : I.InitializationFiniteMixedSideLemma14History)
(hclaw : G.IsClawFree)
```

and conclusion `PaperLemma14Conclusion I`, the exact four-part manuscript
statement.

`InitializationFiniteMixedSideLemma14History` is the literal initialized search
history, not a post-hoc Lemma 14 certificate. It contains the finite execution
core, the manuscript inclusion `W ⊆ Cprime`, explicit empty/positive stopping
constructors, local terminal-path alternation, canonical adjacent stopping
links, and the inductively generated unequal-centre propagation history.

The four terminal facts are derived as follows:

- even/odd terminal coordinates are proved by induction from local colour
  alternation at consecutive path steps;
- a positive terminal clone is extracted by case analysis on the literal
  empty/positive stopping history;
- target commutation is derived from that clone using finite Lemma 11(a),
  Corollary 11, and parity through the later execution suffix;
- exact terminal degree three follows from commutation, even-hole parity, and
  Lemma 7;
- clone-to-flank adjacency follows from the canonical adjacent link;
- unequal-centre propagation witnesses must carry the indexed `IsGenerated`
  derivation built only by the finite `start` and `snoc` constructors.

The lower-level theorem

```lean
InitializationFiniteMixedSideExecutableLemma14Data.paperLemma14_of_executableData
```

remains available as an internal integration bridge. The paper-facing theorem
is the history-level theorem above.

| Manuscript layer | Status |
|---|---|
| Finite claw-free graph theory, including Lemmas 6-10 | Lean implementations exist; complete paper-facing audit remains |
| Token sliding, deformation closures, and generalized-cycle sums | Combinatorial and generic additive definitions exist; operator charges are absent |
| Theorem 1(i)-(iii) | Not formalised at manuscript operator level |
| Lemma 11(a)-(b) | Substantial finite and mixed-side implementations exist; final statement and constructor audit remains |
| Corollary 11 | Proved on bounded mixed-side finite histories |
| Lemmas 12-13 | Implemented on supporting deformation interfaces; statement audit remains |
| Lemma 14(i)-(iv) | Complete on the literal initialized finite Definition 19/20 history; exact unqualified `paperLemma14` exported |
| Lemmas 15-18 | Not formalised as complete manuscript lemmas; some underlying graph definitions exist |
| Theorem 2 | Not formalised |
| Theorem 3 and Corollary 1 | Not formalised |

The next critical path is:

1. formalise the induction of Lemma 15 over obstruction-search rerouting steps;
2. formalise Lemmas 16-18 and complete the remaining combinatorial route to
   Theorem 1(iii);
3. complete the paper-facing constructor audit for Lemma 11(b);
4. introduce the Pauli/frustration-graph algebra required for Theorem 1;
5. formalise the exact free-fermion solution of Theorem 2 and the Krylov
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

For Lemma 14, the manuscript setup is represented by the explicit initialized
finite history. `InitializationFiniteMixedSideTerminalCoreData` alone is not
intended to determine a run: it omits the local stopping and propagation choices
made by the Definition 19/20 search.

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
