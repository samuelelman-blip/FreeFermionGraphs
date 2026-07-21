import FreeFermionGraphs.Lemma11ACorollary11History
import FreeFermionGraphs.Lemma11AEliminateEarlierAnti
import FreeFermionGraphs.Lemma11AOriginalHole

/-!
# Lemma 11(a.ii): completed finite-history argument

The concrete Corollary 11 geometry gives the endpoint alternative for every
earlier anticommuting path.  Neither alternative is possible for a current
dependent anticommuting vertex: an earlier first introduced vertex persists
to the current initial hole, while the current first introduced vertex is
excluded by the local Lemma 11(a) equivalence.  Thus every earlier path
commutes, and parity through the finite history proves the degree equivalence.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- Corollary 12 for every earlier block relative to the current block,
derived from the concrete Corollary 11 proof. -/
theorem earlierAnticommutingEndpointRule_of_fullDefinition19History
    (D : ConcretePathDeformation O Cprime)
    (X : D.FullDefinition19Lemma11AHistoryData)
    (hclaw : G.IsClawFree)
    {u : V}
    (huPrime : u ∈ Cprime)
    (hanti : D.path.AnticommutesWith u) :
    D.EarlierAnticommutingEndpointRule X.history X.priorCount u := by
  intro r hr hantiEarlier
  have hnoShared :=
    D.noSharedDependentAnticommutingWitness_of_fullDefinition19History
      X hclaw hr
  exact
    (X.history.block r).anticommutes_endpoint_of_noSharedDependent
      D (X.prior r) X.current hclaw hnoShared
      huPrime hantiEarlier hanti

/-- No earlier Definition 19 path anticommutes with a current dependent
anticommuting vertex.  This conclusion is independent of its final degree. -/
theorem no_earlierAnticommutation_of_fullDefinition19History
    (D : ConcretePathDeformation O Cprime)
    (X : D.FullDefinition19Lemma11AHistoryData)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPrime : u ∈ Cprime)
    (hanti : D.path.AnticommutesWith u) :
    ∀ r : Nat, r < X.priorCount →
      ¬(X.history.block r).path.AnticommutesWith u := by
  have hlocal :=
    (D.lemma11a_membership_iff_ne_first_and_degree
      X.current hclaw huPrime hanti).mp ⟨s, hu⟩
  have huOutsideCurrent :=
    D.dependent_not_mem_initialHole_of_anticommutes
      X.current hclaw hu huPrime hanti
  have hendpoint :=
    D.earlierAnticommutingEndpointRule_of_fullDefinition19History
      X hclaw huPrime hanti
  intro r hr hantiEarlier
  rcases hendpoint r hr hantiEarlier with hEarlierEndpoint | hCurrentEndpoint
  · apply huOutsideCurrent
    rw [hEarlierEndpoint]
    exact D.earlierFirstIntroduced_mem_currentInitial X hr
  · exact hlocal.1 hCurrentEndpoint

/-- Lemma 11(a.ii)'s numerical equivalence for a nonempty finite history,
with Corollary 11 and all outside-hole facts derived from Definition 19. -/
theorem lemma11aii_degree_iff_of_fullDefinition19History
    (D : ConcretePathDeformation O Cprime)
    (X : D.FullDefinition19Lemma11AHistoryData)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPrime : u ∈ Cprime)
    (hanti : D.path.AnticommutesWith u) :
    D.finalHole.externalDegree u = 4 ↔
      (X.history.block 0).initialHole.externalDegree u = 3 := by
  let last : Nat := X.priorCount - 1
  have hlast : last < X.priorCount := by
    dsimp [last]
    have hpos := X.priorCount_pos
    omega
  have hno :=
    D.no_earlierAnticommutation_of_fullDefinition19History
      X hclaw hu huPrime hanti
  have horiginalEven : Even (X.history.block 0).initialHole.card :=
    (X.prior 0).neighborhood.alternating.initialHole_even
  have hcurrentEven : Even D.initialHole.card :=
    X.current.neighborhood.alternating.initialHole_even
  exact
    D.finalDegree_four_iff_originalDegree_three_of_noEarlierAnticommutation_through
      X.current hclaw hu huPrime hanti X.history last
      X.final_before_current
      (fun r hr => hno r (lt_of_le_of_lt hr hlast))
      horiginalEven hcurrentEven

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
