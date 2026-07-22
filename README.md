# FreeFermionGraphs

Lean formalisation of the graph-theoretic and operator-algebraic results in
*A Unified Graph-Theoretic Framework for Free-Fermion Solvability*.

The project uses Lean 4.32.0 and mathlib. The current milestone is the
claw-free graph theory underlying the generalized-cycle-symmetry proof.

## Build

```bash
lake update
lake build
```

## Status

- [x] Lean/mathlib project scaffold and claw-free graph predicate
- [x] Lemma 6: bipartiteness and maximum-degree-two bound
- [x] Lemma 7 and Corollaries 2-3: neighboring-relation classification
- [x] Lemmas 8-9 and Corollaries 4-6: single-vertex deformations and neighborhood preservation
- [x] Token sliding, deformation closures, and generalized-cycle definitions
- [x] Lemmas 10-13 and Corollaries 7-12: fixed-pairing deformation combinatorics
- [ ] Lemma 14: initialization theorem, partially formalised. Parts (i)-(iii), the indegree bound, pairing labels, execution traces, and both terminal claw contradictions have been proved from explicit certificates. Constructing the remaining terminal certificates from the literal obstruction-search execution is ongoing.
- [ ] Lemmas 15-16 and completion of the palindromic search argument
- [ ] Theorem 1: conserved charges
- [ ] Lemmas 1-5 and Theorem 2: free-fermion solution
- [ ] Lemma 18, Theorem 3, and Corollary 1: Krylov construction

Theorems depending on explicit certificate structures or additional hypotheses
use names such as `..._of_...`. Paper theorem names are reserved for statements
whose translation assumptions have been fully discharged.

See [FORMALIZATION.md](FORMALIZATION.md) for the dependency order and proof-completeness policy.
