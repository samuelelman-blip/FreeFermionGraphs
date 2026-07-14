# FreeFermionGraphs

Lean formalisation of the graph-theoretic and operator-algebraic results in
*Free-Fermion Solvability and Frustration Graphs*.

The project uses Lean 4.32.0 and mathlib. The first milestone formalises the
claw-free graph theory used throughout the paper. In particular,
`SimpleGraph.lemma6` states that the subgraph induced by the symmetric
difference of two independent sets is bipartite and has maximum degree at most
two.

## Build

```bash
lake update
lake build
```

## Status

- [x] Lean/mathlib project scaffold
- [x] Claw-free graph predicate
- [x] Lemma 6: bipartiteness and degree bound
- [ ] Lemma 7 and neighboring-relation classification
- [ ] Deformations, token sliding, and generalized cycles
- [ ] Theorem 1: conserved charges
- [ ] Lemmas 1-5 and Theorem 2: free-fermion solution
- [ ] Lemma 18, Theorem 3, and Corollary 1: Krylov construction

See [FORMALIZATION.md](FORMALIZATION.md) for the proposed dependency order.
