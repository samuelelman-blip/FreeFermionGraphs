import FreeFermionGraphs.PauliFrustrationRepresentation

/-!
# Paper-facing Lemma 17

The paper-facing theorem is stated directly for the Pauli Hamiltonian /
frustration-graph representation.  The independent-set product `h_S` and all
of its insertion/coherence laws are constructed internally from pairwise
commutation on independent sets by `PauliFrustrationRepresentation.toOperatorModel`.

Thus `paperLemma17` accepts no independent product, Eq. (50), cancellation,
or recursion certificate as a premise.  Its algebraic input is only the term
map together with the manuscript frustration-graph commute/anticommute
relations, plus the simplicial-clique hypothesis.
-/

open Set
open scoped BigOperators

universe u w
variable {V : Type u}

namespace SimpleGraph
namespace PauliFrustrationRepresentation

variable {G : SimpleGraph V} {A : Type w} [Ring A]

/-- Manuscript charge `Q_{G\W}^{(k)}` on the vertex-deleted induced graph,
constructed from the canonical independent-set products of the Pauli terms. -/
noncomputable abbrev deletedCharge
    [Fintype V] [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A)
    (W : Set V) (k : Nat) : A :=
  G.operatorIndependentSetCharge H.toOperatorModel W k

/-- Manuscript charge `Q_G^(k)`. -/
noncomputable abbrev charge
    [Fintype V] [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A)
    (k : Nat) : A :=
  G.operatorIndependentSetChargeFull H.toOperatorModel k

/-- The graph relation at the paper boundary is exactly manuscript Definition
1: adjacency is equivalent to anticommutation of the corresponding Hamiltonian
terms. -/
theorem frustrationGraph_iff
    (H : G.PauliFrustrationRepresentation A)
    {j k : V} :
    G.Adj j k ↔ H.term j * H.term k = -(H.term k * H.term j) :=
  H.adj_iff_anticommute

/-- Manuscript Lemma 17, in positive-degree natural-number form.

For a simplicial clique `Ks`, with
`K_j = Γ[j] \ (Ks \ {j})`, this is

`Q_G^(k+1) = Q_(G\Ks)^(k+1) + ∑_{j∈Ks} Q_(G\K_j)^k h_j`.

This is the printed recursion with the paper index shifted by one to avoid
truncated subtraction on natural numbers.  The operator products entering the
charges are canonical `Finset.noncommProd` values on independent sets, so no
product-coherence certificate occurs among the theorem hypotheses. -/
theorem paperLemma17
    [Fintype V] [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A)
    {Ks : Set V} (hKs : G.IsSimplicialClique Ks)
    (k : Nat) :
    H.charge (k + 1) =
      H.deletedCharge Ks (k + 1) +
        ∑ j ∈ verticesOfSet Ks,
          H.deletedCharge (G.lemma17CliqueAt Ks j) k * H.term j := by
  exact lemma17_D25 H.toOperatorModel hKs k

end PauliFrustrationRepresentation
end SimpleGraph
