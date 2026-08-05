# Formalisation plan

The paper has three principal theorems and eighteen named lemmas. The proof
development is organised by mathematical dependency rather than paper order.

## 1. Finite claw-free graph theory

1. Independent sets, cliques, induced subgraphs, paths, holes, and simplicial
   cliques.
2. Lemma 6: the symmetric difference of independent sets induces a bipartite
   graph of maximum degree two.
3. Lemma 7 and Corollaries 2-3: classification of how an external vertex can
   meet an induced path or hole.
4. Lemmas 8-9 and Corollaries 4-6: single-vertex deformations and preservation
   of closed neighborhoods.
5. Token sliding and the connected components of the token-sliding graph.

## 2. Generalized-cycle combinatorics

1. Fixed-pairing-type deformations and obstruction graphs.
2. Lemmas 10-13 and Corollaries 7-12.
3. Lemma 14: completed on the literal initialized finite Definition 19/20
   history by
   `InitializationFiniteMixedSideLemma14History.paperLemma14`.
4. Lemma 15: transport the four Lemma 14 invariants through every corrective
   obstruction-search rerouting step.
5. Lemmas 16-18: termination, palindromic deformation, and the final
   generalized-cycle cancellation.
6. Deformation closures and generalized-cycle indexing data.

This is the longest purely combinatorial layer and is required for Theorem
1(iii).

## 3. Pauli and frustration-graph algebra

1. Finite Pauli strings and the binary symplectic commutation form.
2. Weighted Hamiltonian terms and frustration graphs.
3. Products indexed by independent sets and cycles, including ordering-sign
   lemmas.
4. Independent-set charges, transfer operators, and generalized
   characteristic polynomials.

## 4. Conserved charges

1. Theorem 1(i): independent-set charges commute.
2. Theorem 1(ii): generalized-cycle charges commute with independent-set
   charges.
3. Theorem 1(iii): generalized-cycle charges mutually commute.

## 5. Exact free-fermion solution

1. Lemma 1: symmetry-sector decomposition of the generalized characteristic
   polynomial.
2. Lemma 2 and Lemma 17: transfer-operator identity for a simplicial mode.
3. Lemmas 3-5: eigenmode equation, canonical anticommutation relations, and
   Hamiltonian reconstruction.
4. Theorem 2.

## 6. Krylov construction

1. Induced-path trees and the directed hopping graph.
2. Lemma 18: path-operator sign identity.
3. Theorem 3: the matrix-power formula for nested commutators.
4. Corollary 1: canonical fermionic modes from the Krylov sequence.

## Proof-completeness policy

Statements proved only under an explicit abstraction or additional hypothesis
will be marked as such in their theorem names and docstrings. The final paper
theorems will not be exposed under their paper names until every translation
assumption is discharged.

For nondeterministic manuscript algorithms, an explicit finite execution
history is part of the setup. It is acceptable in an unqualified theorem only
when its constructors contain literal algorithm branches and no field assumes
the numbered lemma's conclusion.
