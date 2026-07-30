# FreeFermionGraphs

Lean 4 formalisation of the graph-theoretic and operator-algebraic results in
*A Unified Graph-Theoretic Framework for Free-Fermion Solvability* by Adrian
Chapman, Samuel J. Elman, and Ryan L. Mann.

The project formalises the proof that a Hamiltonian admits an exact
free-fermion description when its frustration graph is claw-free and contains
a simplicial clique. The development includes finite claw-free graph theory,
hole deformations, token sliding, generalized-cycle symmetries, transfer
operators, and the operator-Krylov construction.

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

The main active proof is Theorem 1(iii), the mutual commutation of the
generalized-cycle symmetries. Its longest combinatorial component is the
obstruction-search argument in Lemma 14.

| Manuscript layer | Status |
|---|---|
| Finite claw-free graph theory, including Lemmas 6-10 | Formalised |
| Token sliding, deformation closures, and generalized-cycle data | Formalised |
| Theorem 1(i), independent-set charges commute | Formalised |
| Theorem 1(ii), generalized-cycle charges commute with independent-set charges | Formalised |
| Lemma 11(a), Lemma 11(b), and their concrete history machinery | Formalised |
| Corollary 11 | Formalised on the concrete same-orientation interface; mixed-side integration is in progress |
| Lemmas 12-13 | Formalised |
| Lemma 14(i)-(iii) and most of Lemma 14(iv) | Formalised |
| Unconditional manuscript-level Lemma 14 | Not yet closed |
| Theorem 1(iii) | In progress |
| Theorem 2 and Theorem 3 layers | Substantial formalisation exists; final manuscript-level integration and audit remain |

The remaining critical path for Lemma 14 is:

1. complete Corollary 11 for a literal history mixing both Definition 19 path
   sides;
2. construct that mixed-side history from the concrete obstruction-search
   loop;
3. prove the terminal containment statement
   `P ∩ C_b ⊆ C_j^(m)` without excluding legitimate opposite-side overlaps;
4. derive the remaining terminal propagation data from the two initialized
   executions;
5. remove the terminal-analysis certificate boundary and expose the exact
   four conclusions of manuscript Lemma 14.

After Lemma 14, the search-update argument, the unobstructed-palindromic step,
and the final pairwise commutator cancellation remain before Theorem 1(iii) is
complete.

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
