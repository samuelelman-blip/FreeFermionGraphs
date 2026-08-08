# Lemma 17 manuscript fidelity

This document records the paper-facing correspondence for manuscript Lemma 17 of *A Unified Graph-Theoretic Framework for Free-Fermion Solvability*.

## Manuscript statement

For a simplicial clique `Ks` of the frustration graph `G`, define

`K_j = Γ[j] \ (Ks \ {j})`

for each `j ∈ Ks`, so that `Γ[j] = Ks ∪ K_j`. Then, for positive charge order,

`Q_G^(k) = Q_(G\Ks)^(k) + ∑_{j∈Ks} Q_(G\K_j)^(k-1) h_j`.

The Lean theorem shifts the natural-number index by one and therefore states the result at degree `k + 1`.

## Paper-facing theorem

The unqualified theorem is

```lean
SimpleGraph.PauliFrustrationRepresentation.paperLemma17
```

with hypotheses consisting only of:

- a finite frustration graph `G`;
- a ring-valued Hamiltonian term map `h_j`;
- adjacency iff anticommutation, matching manuscript Definition 1;
- commutation on nonedges, the Pauli commute/anticommute dichotomy;
- a simplicial clique `Ks`.

No independent-set product, Eq. (50) identity, D21/D22 expansion, pair-cancellation certificate, or D25 recursion is accepted as a premise of `paperLemma17`.

## Operator-product provenance

The manuscript product `h_S` on an independent set is constructed canonically in

```lean
FreeFermionGraphs/PauliFrustrationRepresentation.lean
```

using `Finset.noncommProd`. Pairwise commutation follows from independence and the nonedge commutation law. The left- and right-insertion identities are proved from this canonical product and then used to construct the internal `FrustrationOperatorModel`.

Thus the product-coherence laws used by the internal proof are derived facts, not additional paper-facing assumptions.

## Graph-theoretic provenance

`FreeFermionGraphs/SimplicialClique.lean` defines the manuscript simplicial-clique condition and proves:

- each `K_j = Γ[j] \ (Ks \ {j})` is a clique;
- `Γ[j] = Ks ∪ K_j` for `j ∈ Ks`.

## Charge provenance

`operatorIndependentSetCharge M W k` is the operator-valued Definition 4 charge on the induced graph with carrier `W` deleted. The full charge is the specialization `W = ∅`.

The degree-zero convention `Q^(0) = 1` is proved from the unique empty independent set rather than assumed.

## Eq. (50)

The clique charge recursion is proved by partitioning independent sets according to their unique possible clique vertex. The fixed-vertex family is reindexed by deleting that vertex and avoiding its closed neighborhood. Both left- and right-oriented operator forms are proved.

## Appendix D.2 correspondence

The proof is split into the same logical stages as the manuscript:

1. `lemma17_D21` specializes Eq. (50) to `Ks`.
2. `lemma17_D22` reapplies Eq. (50) after deleting `K_j`.
3. `lemma17_D23` substitutes D22 into D21.
4. `lemma17_orderedPair_cancel` proves the two-term cancellation for `(j,l)` and `(l,j)` using clique adjacency and anticommutation.
5. `lemma17_orderedDoubleSum_eq_zero` lifts this to the full ordered double sum via the swap involution.
6. `lemma17_D25_succ_succ` proves the recursion for degree at least two.
7. `lemma17_D25_one` proves degree one from `Q^(0) = 1`.
8. `lemma17_D25` combines all positive degrees.
9. `PauliFrustrationRepresentation.paperLemma17` exports the manuscript-level theorem.

## Fidelity classification

| Object | Provenance class | Paper-facing premise? |
|---|---|---|
| Hamiltonian term map | D | Yes |
| frustration adjacency iff anticommutation | D | Yes |
| nonedge commutation for Pauli terms | D | Yes |
| simplicial clique | D | Yes |
| `K_j` and `Γ[j] = Ks ∪ K_j` | E | No |
| independent-set product `h_S` | E | No |
| insertion/coherence identities | E | No |
| Eq. (50) | E | No |
| D21-D25 | E | No |
| ordered-pair cancellation | E | No |

Here D denotes literal manuscript setup and E denotes a theorem derived from that setup under the repository fidelity policy.

## Validation gate

Before merge, validate the exact branch head with:

```bash
lake build FreeFermionGraphs.Lemma17Paper
lake build FreeFermionGraphs
lake build

git grep -n -E '(^|[^[:alnum:]_])(sorry|admit)([^[:alnum:]_]|$)' -- '*.lean' || true
git grep -n -E '^[[:space:]]*(axiom|opaque)[[:space:]]' -- '*.lean' || true
```

The focused `Lemma17Paper` build has passed on the branch. Root and complete-project builds remain merge gates until reported successful at the final exact head.
