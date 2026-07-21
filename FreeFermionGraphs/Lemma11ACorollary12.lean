import FreeFermionGraphs.Lemma11APathBlock
import FreeFermionGraphs.Corollary11

/-!
# Lemma 11(a): the Corollary 12 endpoint bridge

The global part of Lemma 11(a.ii) uses Corollary 12 in one precise form:
if a prime-hole vertex anticommutes with two distinct Definition 19 paths,
then it must be the first introduced vertex of one of those paths.  The
path-block proof of Lemma 11(a) already supplies the missing conversion
from ``not the first vertex'' to Definition 20 membership.  This module
combines that conversion with the no-shared-dependent-witness statement of
Corollary 11.

The geometric proof of Corollary 11 itself remains a separate global
deformation task.  Nothing here assumes the endpoint conclusion.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O O' : FixedPairingPathFamily G} {Cprime : Set V}

/-- For an anticommuting prime-hole vertex, being different from the first
introduced path vertex already constructs a Definition 20 member.  The
degree equality in the displayed Lemma 11(a) equivalence is derived from
the path balance, rather than required here. -/
theorem exists_dependentAt_of_anticommuting_ne_first
    (D : ConcretePathDeformation O Cprime)
    (F : D.FullDefinition19Lemma11AData)
    (hclaw : G.IsClawFree)
    {u : V}
    (huPrime : u ∈ Cprime)
    (hanti : D.path.AnticommutesWith u)
    (huNeFirst : u ≠ (D.deformation.step D.firstIndex).introduced) :
    ∃ s : Nat, u ∈ D.dependentAt s := by
  have huOutside :=
    F.anticommuting_not_mem_path huPrime huNeFirst hanti
  have hbalance := D.anticommuting_neighborCount_balance
    F.neighborhood.pathOrder F.path_card_eq hclaw
    huOutside hanti
    (F.terminalAnticommutingNonadjacency huPrime huOutside hanti)
    (D.removedIntroducedRemovedExtension_of_fullDefinition19
      F hclaw huPrime)
  have hdegree :
      D.finalHole.externalDegree u =
        D.initialHole.externalDegree u + 1 :=
    D.finalDegree_eq_initial_add_one_of_neighborCount hbalance
  exact
    (D.lemma11a_membership_iff_ne_first_and_degree
      F hclaw huPrime hanti).mpr ⟨huNeFirst, hdegree⟩

/-- A no-shared-Definition-20-witness condition forces the Corollary 12
endpoint alternative for two anticommuting paths. -/
theorem anticommutes_endpoint_of_noSharedDependent
    (D : ConcretePathDeformation O Cprime)
    (E : ConcretePathDeformation O' Cprime)
    (F : D.FullDefinition19Lemma11AData)
    (H : E.FullDefinition19Lemma11AData)
    (hclaw : G.IsClawFree)
    (hnoShared :
      ¬SharedDependentAnticommutingWitness
        D.path E.path D.dependentAt E.dependentAt)
    {u : V}
    (huPrime : u ∈ Cprime)
    (hantiD : D.path.AnticommutesWith u)
    (hantiE : E.path.AnticommutesWith u) :
    u = (D.deformation.step D.firstIndex).introduced ∨
      u = (E.deformation.step E.firstIndex).introduced := by
  by_cases huD : u = (D.deformation.step D.firstIndex).introduced
  · exact Or.inl huD
  by_cases huE : u = (E.deformation.step E.firstIndex).introduced
  · exact Or.inr huE
  obtain ⟨s, hus⟩ :=
    D.exists_dependentAt_of_anticommuting_ne_first
      F hclaw huPrime hantiD huD
  obtain ⟨t, hut⟩ :=
    E.exists_dependentAt_of_anticommuting_ne_first
      H hclaw huPrime hantiE huE
  exact (hnoShared ⟨u, s, t, hus, hut, hantiD, hantiE⟩).elim

/-- Corollary 12 for two concrete Definition 19 path blocks, derived from
the repository's `Corollary11Property`. -/
theorem corollary12_of_corollary11
    (D : ConcretePathDeformation O Cprime)
    (E : ConcretePathDeformation O' Cprime)
    (F : D.FullDefinition19Lemma11AData)
    (H : E.FullDefinition19Lemma11AData)
    (hclaw : G.IsClawFree)
    (P : Nat → IndexedInducedPath G)
    (Q : Nat → IndexedInducedPath G)
    (U : Nat → Nat → Set V)
    (W : Nat → Nat → Set V)
    (hcor11 : O.Corollary11Property O' P Q U W)
    (hDPath : Set.range D.path.vertex ∈ O.paths)
    (hEPath : Set.range E.path.vertex ∈ O'.paths)
    (hpathNe : Set.range D.path.vertex ≠ Set.range E.path.vertex)
    (hP0 : P 0 = D.path)
    (hQ0 : Q 0 = E.path)
    (hU0 : U 0 = D.dependentAt)
    (hW0 : W 0 = E.dependentAt)
    {u : V}
    (huPrime : u ∈ Cprime)
    (hantiD : D.path.AnticommutesWith u)
    (hantiE : E.path.AnticommutesWith u) :
    u = (D.deformation.step D.firstIndex).introduced ∨
      u = (E.deformation.step E.firstIndex).introduced := by
  apply D.anticommutes_endpoint_of_noSharedDependent E F H hclaw
  have hnoShared := hcor11.2 (r := 0) (g := 0)
    (by rw [hP0]; exact hDPath)
    (by rw [hQ0]; exact hEPath)
    (by rw [hP0, hQ0]; exact hpathNe)
  simpa [hP0, hQ0, hU0, hW0] using hnoShared
  exact huPrime
  exact hantiD
  exact hantiE

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
