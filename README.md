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

A single module can be checked first, for example:

```bash
lake build FreeFermionGraphs.ObstructionSearchTwoSidedMixedCorollary11
```

## Current proof status

The main active proof program is the graph-combinatorial route toward Theorem
1(iii). Its current integration boundary is the obstruction-search argument in
Lemma 14. No clause of Theorem 1 is yet exported as a manuscript-level
operator commutator theorem.

| Manuscript layer | Status |
|---|---|
| Finite claw-free graph theory, including Lemmas 6-10 | Lean implementations exist; complete paper-facing audit remains |
| Token sliding, deformation closures, and generalized-cycle sums | Combinatorial and generic additive definitions exist; operator charges are absent |
| Theorem 1(i)-(iii) | Not formalised at manuscript operator level |
| Lemma 11(a)-(b) | Conditional implementations exist; literal finite mixed-side history and endpoint-certificate construction remain |
| Corollary 11 | Proved on supplied mixed-side history data; construction from the literal search remains |
| Lemmas 12-13 | Implemented on a flattened deformation interface with explicit local fields; constructor audit remains |
| Lemma 14(i)-(iv) | Conditional integration only; no unconditional `paperLemma14` |
| Lemmas 15-18 | Not formalised as manuscript lemmas; some underlying graph definitions exist |
| Theorem 2 | Not formalised |
| Theorem 3 and Corollary 1 | Not formalised |

The remaining critical path for Lemma 14 is:

1. construct `FiniteMixedSideSearchTrace` from an executable obstruction-search
   loop, preserving the finite path blocks, their sides, and their exact map to
   flattened steps;
2. derive the local endpoint nonadjacency fields used by Lemma 11 directly from
   Definition 19 and the preceding graph lemmas;
3. port the bounded Lemma 11 and Corollary 11 arguments from the legacy total
   `Nat` history to the finite trace;
4. prove the terminal containment statement
   `P ∩ C_b ⊆ C_j^(m)` without excluding legitimate opposite-side overlaps;
5. derive the remaining terminal propagation data from the two initialized
   executions;
6. remove the terminal-analysis certificate boundary and expose the exact four
   conclusions of manuscript Lemma 14.

After Lemma 14, Lemmas 15-16, the search-update argument, the
unobstructed-palindromic step, and the complete Pauli/operator layer still
remain before Theorem 1(iii) is complete. Theorem 2 and Theorem 3 require their
own later operator-algebra developments.

## Manuscript fidelity policy

A successful `lake build` proves that the Lean terms typecheck. It does not by
itself establish that a theorem has the same hypotheses, quantifiers,
deformation stage, and conclusion as the manuscript.

Paper-facing results are therefore gated by
[`docs/PAPER_FIDELITY.md`](docs/PAPER_FIDELITY.md). In particular:

- every manuscript object must be matched to a Lean object;
- hole stages and degree expressions must be explicit;
- additional premises must be documented;
- boundary certificates may not appear in the final paper theorem;
- an unqualified name such as `paperLemma14` is reserved for the exact
  manuscript statement;
- conditional bridges retain names such as `paperLemma14_of_...` until every
  extra premise is discharged.

This policy is especially important for Definition 19, where one fixed-pairing
deformation may contain paths from both component families. A one-sided
history cannot be used as the final representation of the manuscript search.

## Repository layout

- `FreeFermionGraphs/`: individual definitions, lemmas, and integration modules
- `FreeFermionGraphs.lean`: root import for the complete development
- `FORMALIZATION.md`: dependency-oriented proof plan
- `docs/PAPER_FIDELITY.md`: manuscript correspondence, provenance, and open
  proof boundaries
- `docs/PAPER_AUDIT_2026-08-01.md`: statement-level audit of the current branch
  against the supplied manuscript
- issue `#144`: detailed tracking of the remaining Lemma 14 terminal analysis

## Development workflow

Hosted CI is currently avoided to conserve GitHub Actions usage. Pull requests
are validated locally with both a focused module build and the full project
build:

```bash
lake build FreeFermionGraphs.<ModuleName>
lake build
```

Commits made during this phase include `[skip ci]`. A pull request is not merged
until the corresponding local build has been reported successful.
