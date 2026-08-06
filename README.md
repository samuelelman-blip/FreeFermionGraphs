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

The finite Lemmas 14-16 integration can be checked first with:

```bash
lake build FreeFermionGraphs.ObstructionSearchReroutingProcess
lake build FreeFermionGraphs.Lemma16Paper
```

## Current proof status

The finite Definition 19/20 route exposes the history-level Lemma 14 theorem

```lean
InitializationFiniteMixedSideLemma14History.paperLemma14
```

and the all-state Lemma 15 theorem

```lean
ObstructionSearchReroutingProcess.paperLemma15
```

The paper-facing Lemma 16 theorem is

```lean
FiniteMixedSideSearchTrace.PaperLemma16Trace.paperLemma16
```

It derives the occurrence-level Corollaries 9-10 transport and constructs the
`Lemma12Definition19Data` certificate from an explicit completed finite trace.
For an unobstructed deformation it proves both
`dependentUnion ⊆ terminalHole` and the palindromic reverse run of Lemma 12.

The Lemma 15 theorem proves `PaperLemma14Conclusion` for every state of an
explicit finite corrective rerouting execution. Such an execution records the
selected finite Definition 19/20 history at each state and one transition for
every application of Eqs. (C31) and (C32).

A transition records the source/obstruction deletion, the surviving source,
the value-preserving embedding of the next initializer set, the retained data
of Eq. (C31), and the optional concatenation and continuation used in Eq.
(C32). The two removed vertices are absent from the next initializer set, the
survivor embedding is injective, and the initializer set strictly decreases.

No state contains `PaperLemma14Conclusion`, one of its four clauses, a terminal
endpoint alternative, or a terminal claw. The state history specifies an
actual run of the nondeterministic manuscript search.

## Fidelity audit

A repository-wide manuscript audit was performed against the 14 July 2026
paper. The complete findings are recorded in
[`docs/PAPER_FIDELITY_AUDIT_2026-08-05.md`](docs/PAPER_FIDELITY_AUDIT_2026-08-05.md).

The audit does **not** support a blanket claim that every numbered result
represented in the repository is already an exact formalisation of the printed
paper. The Lean terms are internally checked, but some earlier numbered files
are conditional cores or representation-level statements:

- the printed Lemma 8 omits an external-vertex premise used by its proof; Lean
  formalises the corrected intended statement;
- the generic Corollaries 7-10 interfaces still expose some coloring or
  occurrence information as premises, although Lemma 16 now derives its
  required occurrence-level Corollaries 9-10 transport from the finite trace;
- Lemma 11 still depends on `Lemma11AHistoryContext`;
- the general Lemma 12 theorem still consumes `Lemma12Definition19Data`, while
  Lemma 16 now constructs that data from `PaperLemma16Trace`;
- the Eq. (C32) optional-concatenation interface stores path-containment
  provenance that should eventually be derived from dependent index transport.

Accordingly, the status table distinguishes exact endpoints from conditional or
representation-level implementations.

| Manuscript layer | Status |
|---|---|
| Lemma 6 | Exact for the finite graph setting |
| Lemma 7 and Corollaries 2-3 | Exact indexed path/hole statements |
| Lemma 8 and Corollaries 4-5 | Corrected forms with the required external-vertex premise |
| Lemma 9 and Corollary 6 | Exact deformation-closure statements |
| Lemma 10 | Exact on the fixed-pairing component-family interface |
| Corollaries 7-10 | Conditional or occurrence-erasing cores; exact ordered-path wrappers remain |
| Lemma 11 and Corollary 11 | Substantial finite implementations; exact constructor audit remains |
| Lemma 12 | Conditional on `Lemma12Definition19Data` |
| Lemma 13 | Exact at the complete flattened Definition 19 interface |
| Lemma 14(i)-(iv) | Exact on explicit initialized finite histories |
| Lemma 15 | Exact all-state conclusion on an explicit finite rerouting process; Eq. (C32) provenance cleanup remains |
| Lemma 16 | Exact on an explicit completed finite Definition 19 trace |
| Lemmas 17-18 | Not yet formalised at manuscript level |
| Theorem 1(i)-(iii) | Not formalised at manuscript operator level |
| Theorem 2 | Not formalised |
| Theorem 3 and Corollary 1 | Not formalised |

The next critical path is:

1. connect strict initializer decrease to the terminal unobstructed state of
   the corrective process;
2. replace the remaining generic conditional Corollary 7-10, Lemma 11, and
   Lemma 12 interfaces by occurrence-indexed constructors;
3. formalise Lemmas 17-18 and complete the combinatorial route to Theorem 1(iii);
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
- `docs/PAPER_FIDELITY.md`: current manuscript correspondence and open proof
  boundaries
- `docs/PAPER_FIDELITY_AUDIT_2026-08-05.md`: result-by-result current audit
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
