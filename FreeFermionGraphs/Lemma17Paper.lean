import FreeFermionGraphs.Lemma17Recursion

/-!
# Paper-facing Lemma 17

The manuscript assumes a Hamiltonian together with its frustration graph.  At
this level of abstraction the relevant data are the Hamiltonian terms `h_j`,
the independent-set products `h_S`, and the statement that the graph records
exactly the pairwise anticommutation relations of the terms.  The auxiliary
`FrustrationOperatorModel` developed for the proof packages the same operator
products together with the insertion/coherence laws used to manipulate `h_S`.

This module bundles those ingredients as the manuscript Hamiltonian/frustration
graph representation and exports the unqualified Lemma 17 theorem.  No
additional cancellation, recursion, or algebraic certificate is accepted by
`paperLemma17` beyond this representation and the simplicial-clique premise.
-/

open Set
open scoped BigOperators

universe u w
variable {V : Type u}

namespace SimpleGraph

/-- Audited representation of a Hamiltonian together with its frustration
 graph, corresponding to manuscript Definition 1 and the subset products used
 throughout the paper.

`operatorModel.term j` is `h_j`, and `operatorModel.independentProduct S` is
`h_S` for an independent set `S`.  The final field records the defining
frustration-graph equivalence

`{j,k} ∈ E  ↔  h_j h_k = - h_k h_j`.

The insertion laws stored in `operatorModel` are not additional physical
hypotheses: they are the coherence of the notation `h_S` for products of
mutually commuting terms, which the manuscript notes is order-independent on
independent sets. -/
structure HamiltonianFrustrationRepresentation
    (G : SimpleGraph V) (A : Type w) [Ring A] [DecidableEq V] where
  operatorModel : G.FrustrationOperatorModel A
  adj_iff_anticommute :
    ∀ {j k : V},
      G.Adj j k ↔
        operatorModel.term j * operatorModel.term k =
          -(operatorModel.term k * operatorModel.term j)

namespace HamiltonianFrustrationRepresentation

variable {G : SimpleGraph V} {A : Type w} [Ring A] [DecidableEq V]

/-- Manuscript Hamiltonian term `h_j`. -/
abbrev term (H : G.HamiltonianFrustrationRepresentation A) (j : V) : A :=
  H.operatorModel.term j

/-- Manuscript charge `Q_{G\W}^{(k)}` on the vertex-deleted induced graph. -/
noncomputable abbrev deletedCharge
    [Fintype V]
    (H : G.HamiltonianFrustrationRepresentation A)
    (W : Set V) (k : Nat) : A :=
  G.operatorIndependentSetCharge H.operatorModel W k

/-- Manuscript charge `Q_G^(k)`. -/
noncomputable abbrev charge
    [Fintype V]
    (H : G.HamiltonianFrustrationRepresentation A)
    (k : Nat) : A :=
  G.operatorIndependentSetChargeFull H.operatorModel k

/-- The bundled graph really is the frustration graph in the sense of
manuscript Definition 1. -/
theorem frustrationGraph_iff
    (H : G.HamiltonianFrustrationRepresentation A)
    {j k : V} :
    G.Adj j k ↔ H.term j * H.term k = -(H.term k * H.term j) :=
  H.adj_iff_anticommute

/-- Manuscript Lemma 17, in positive-degree natural-number form.

For a simplicial clique `Ks`, with
`K_j = Γ[j] \ (Ks \ {j})`, this is

`Q_G^(k+1) = Q_(G\Ks)^(k+1) + ∑_{j∈Ks} Q_(G\K_j)^k h_j`.

This is exactly the printed recursion with the paper index shifted by one to
avoid truncated subtraction on natural numbers. -/
theorem paperLemma17
    {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    {A : Type w} [Ring A]
    (H : G.HamiltonianFrustrationRepresentation A)
    {Ks : Set V} (hKs : G.IsSimplicialClique Ks)
    (k : Nat) :
    H.charge (k + 1) =
      H.deletedCharge Ks (k + 1) +
        ∑ j ∈ verticesOfSet Ks,
          H.deletedCharge (G.lemma17CliqueAt Ks j) k * H.term j := by
  exact lemma17_D25 H.operatorModel hKs k

end HamiltonianFrustrationRepresentation

end SimpleGraph
