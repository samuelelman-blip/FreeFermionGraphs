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

The completed finite Lemmas 14 and 15 integration can be checked first with:

```bash
lake build FreeFermionGraphs.ObstructionSearchReroutingProcess
```

## Current proof status

The finite Definition 19/20 route exposes the unqualified Lemma 14 theorem

```lean
InitializationFiniteMixedSideLemma14History.paperLemma14
```

and the all-steps Lemma 15 theorem

```lean
ObstructionSearchReroutingProcess.paperLemma15
```

The latter proves `PaperLemma14Conclusion` for every state of an explicit
finite corrective rerouting execution. Such an execution records the literal
nondeterministic Definition 19/20 histories at each state and one transition
for every application of Eqs. (C31) and (C32).

A transition records:

- the source and common obstruction removed from the initializer set;
- the surviving distinguished source and the rerouting initializer;
- the value-preserving embedding of the new initializer set into the old one;
- the unchanged outputs, dependent sets, and arcs of Eq. (C31);
- the exact optional empty/nonempty concatenation used in Eq. (C32);
- the finite continuation of that concatenated prefix by the rerun obstruction
  search.

The two removed vertices are proved absent from the next initializer set, the
survivor embedding is proved injective, the initializer set is proved to
strictly decrease, and both parent path collections are proved to occur in the
rerouted output.

No state or transition contains `PaperLemma14Conclusion`, any of its four
clauses, a terminal endpoint alternative, or a terminal claw. Each state
contains only the explicit finite history specifying that run of the
nondeterministic manuscript algorithm. Lemma 15 then applies the completed
history-level Lemma 14 theorem uniformly at every represented step.

| Manuscript layer | Status |
|---|---|
| Finite claw-free graph theory, including Lemmas 6-10 | Lean implementations exist; complete paper-facing audit remains |
| Token sliding, deformation closures, and generalized-cycle sums | Combinatorial and generic additive definitions exist; operator charges are absent |
| Theorem 1(i)-(iii) | Not formalised at manuscript operator level |
| Lemma 11(a)-(b) | Substantial finite and mixed-side implementations exist; final statement and constructor audit remains |
| Corollary 11 | Proved on bounded mixed-side finite histories |
| Lemmas 12-13 | Implemented on supporting deformation interfaces; statement audit remains |
| Lemma 14(i)-(iv) | Complete on the literal initialized finite Definition 19/20 history; exact unqualified `paperLemma14` exported |
| Lemma 15 | Complete for explicit finite corrective rerouting executions; exact all-steps `paperLemma15` exported |
| Lemmas 16-18 | Not formalised as complete manuscript lemmas; some underlying graph definitions exist |
| Theorem 2 | Not formalised |
| Theorem 3 and Corollary 1 | Not formalised |

The next critical path is:

1. formalise termination of the strictly decreasing corrective search and
   Lemma 16's unobstructed-palindromic conclusion;
2. formalise Lemmas 17-18 and complete the remaining combinatorial route to
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

For Lemmas 14 and 15, the nondeterministic manuscript setup is represented by
explicit finite execution histories. The core search output alone does not
determine the local stopping, propagation, concatenation, and rerun choices
made by the Definition 19/20 procedure.

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
