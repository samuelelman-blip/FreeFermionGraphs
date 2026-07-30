import FreeFermionGraphs.ObstructionSearchTwoSidedMixedCorollary11
import FreeFermionGraphs.Lemma11AFullDefinition19HistoryComplete

/-!
# Completing Lemma 11(a.ii) on mixed-side Definition 19 histories

Once Corollary 11 is available for a history whose blocks may independently
use the `ac` or `bd` component side, the remainder of the finite-history
argument is carrier based.  Corollary 12 excludes every earlier
anticommuting path, and parity through the literal hole sequence transports the
original-hole degree.

This module proves the mixed-side analogues of the completed positive-history
Lemma 11(a.ii) argument.  It does not construct the history from the
obstruction-search loop and does not assume any conclusion of Lemma 14.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation

private theorem reorient_firstIntroduced_eq
    (D : ConcretePathDeformation O Cprime)
    (side : DeformationSide) :
    (((D.reorient side).deformation.step
      (D.reorient side).firstIndex).introduced) =
      (D.deformation.step D.firstIndex).introduced := by
  cases side <;> rfl

private theorem initialHole_even_of_reorient
    (D : ConcretePathDeformation O Cprime)
    (side : DeformationSide)
    (hEven : Even (D.reorient side).initialHole.card) :
    Even D.initialHole.card := by
  cases side <;> exact hEven

private theorem degree_step_of_reorient
    (D : ConcretePathDeformation O Cprime)
    (side : DeformationSide)
    (u : V)
    (hstep :
      (D.reorient side).finalHole.externalDegree u =
        (D.reorient side).initialHole.externalDegree u + 1) :
    D.finalHole.externalDegree u =
      D.initialHole.externalDegree u + 1 := by
  cases side <;> exact hstep

private theorem not_mem_initialHole_of_reorient
    (D : ConcretePathDeformation O Cprime)
    (side : DeformationSide)
    {u : V}
    (hu : u ∉ Set.range (D.reorient side).initialHole.vertex) :
    u ∉ Set.range D.initialHole.vertex := by
  cases side <;> exact hu

namespace MixedSideFullDefinition19Lemma11AHistoryData

variable {D : ConcretePathDeformation O Cprime}

/-- Corollary 12 for every earlier block relative to the current block in a
positive mixed-side Definition 19 history. -/
theorem earlierAnticommutingEndpointRule_of_mixedSideHistory
    (X : D.MixedSideFullDefinition19Lemma11AHistoryData)
    (hclaw : G.IsClawFree)
    {u : V}
    (huPrime : u ∈ Cprime)
    (hantiCurrent : D.path.AnticommutesWith u) :
    D.EarlierAnticommutingEndpointRule
      X.history.carrier X.priorCount u := by
  intro r hr hantiEarlier
  let A := X.history.orientedBlock r
  let E := X.orientedCurrent
  have hAData : A.FullDefinition19Lemma11AData := by
    simpa [A, MixedSidePathBlockHistory.orientedBlock] using
      X.history.localData r
  have hEData : E.FullDefinition19Lemma11AData := by
    simpa [E, orientedCurrent] using X.current
  have hnoCarrier :=
    noSharedDependentAnticommutingWitness_of_mixedSideHistory
      X hclaw hr
  have hnoOriented :
      ¬SharedDependentAnticommutingWitness
        A.path E.path A.dependentAt E.dependentAt := by
    intro hshared
    apply hnoCarrier
    rcases hshared with
      ⟨v, s, t, hvA, hvE, hantiA, hantiE⟩
    refine ⟨v, s, t, ?_, ?_, ?_, ?_⟩
    · rw [X.history.orientedBlock_dependentAt r s] at hvA
      exact hvA
    · rw [X.orientedCurrent_dependentAt t] at hvE
      exact hvE
    · simpa [A, MixedSidePathBlockHistory.orientedBlock] using hantiA
    · simpa [E, orientedCurrent] using hantiE
  have hantiA : A.path.AnticommutesWith u := by
    simpa [A, MixedSidePathBlockHistory.orientedBlock] using hantiEarlier
  have hantiE : E.path.AnticommutesWith u := by
    simpa [E, orientedCurrent] using hantiCurrent
  have hendpoint :=
    A.anticommutes_endpoint_of_noSharedDependent
      E hAData hEData hclaw hnoOriented
      huPrime hantiA hantiE
  rcases hendpoint with hA | hE
  · left
    calc
      u = ((A.deformation.step A.firstIndex).introduced) := hA
      _ = ((X.history.carrier.block r).deformation.step
          (X.history.carrier.block r).firstIndex).introduced := by
        simpa [A, MixedSidePathBlockHistory.orientedBlock] using
          reorient_firstIntroduced_eq
            (X.history.carrier.block r) (X.history.side r)
  · right
    calc
      u = ((E.deformation.step E.firstIndex).introduced) := hE
      _ = (D.deformation.step D.firstIndex).introduced := by
        simpa [E, orientedCurrent] using
          reorient_firstIntroduced_eq D X.currentSide

/-- No earlier path in a positive mixed-side history anticommutes with a
current dependent anticommuting vertex. -/
theorem no_earlierAnticommutation_of_mixedSideHistory
    (X : D.MixedSideFullDefinition19Lemma11AHistoryData)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPrime : u ∈ Cprime)
    (hanti : D.path.AnticommutesWith u) :
    ∀ r : Nat, r < X.priorCount →
      ¬(X.history.carrier.block r).path.AnticommutesWith u := by
  have huOriented : u ∈ X.orientedCurrent.dependentAt s := by
    rw [X.orientedCurrent_dependentAt s]
    exact hu
  have hantiOriented : X.orientedCurrent.path.AnticommutesWith u := by
    simpa using hanti
  have hlocal :=
    (X.orientedCurrent.lemma11a_membership_iff_ne_first_and_degree
      X.current hclaw huPrime hantiOriented).mp ⟨s, huOriented⟩
  have hfirstCurrent :
      ((X.orientedCurrent.deformation.step
        X.orientedCurrent.firstIndex).introduced) =
        (D.deformation.step D.firstIndex).introduced := by
    simpa [orientedCurrent] using
      reorient_firstIntroduced_eq D X.currentSide
  have hcurrentNotFirst :
      u ≠ (D.deformation.step D.firstIndex).introduced := by
    intro huFirst
    apply hlocal.1
    exact huFirst.trans hfirstCurrent.symm
  have huOutsideOriented :=
    X.orientedCurrent.dependent_not_mem_initialHole_of_anticommutes
      X.current hclaw huOriented huPrime hantiOriented
  have huOutsideCurrent :
      u ∉ Set.range D.initialHole.vertex := by
    apply not_mem_initialHole_of_reorient D X.currentSide
    simpa [orientedCurrent] using huOutsideOriented
  have hendpoint :=
    earlierAnticommutingEndpointRule_of_mixedSideHistory
      X hclaw huPrime hanti
  intro r hr hantiEarlier
  rcases hendpoint r hr hantiEarlier with
      hEarlierEndpoint | hCurrentEndpoint
  · apply huOutsideCurrent
    rw [hEarlierEndpoint]
    exact D.earlierFirstIntroduced_mem_currentInitial_of_mixedSideHistory
      X hr
  · exact hcurrentNotFirst hCurrentEndpoint

/-- Lemma 11(a.ii)'s numerical degree equivalence for a positive mixed-side
Definition 19 history. -/
theorem lemma11aii_degree_iff_of_mixedSideHistory
    (X : D.MixedSideFullDefinition19Lemma11AHistoryData)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPrime : u ∈ Cprime)
    (hanti : D.path.AnticommutesWith u) :
    D.finalHole.externalDegree u = 4 ↔
      (X.history.carrier.block 0).initialHole.externalDegree u = 3 := by
  have huOriented : u ∈ X.orientedCurrent.dependentAt s := by
    rw [X.orientedCurrent_dependentAt s]
    exact hu
  have hantiOriented : X.orientedCurrent.path.AnticommutesWith u := by
    simpa using hanti
  have hlocal :=
    (X.orientedCurrent.lemma11a_membership_iff_ne_first_and_degree
      X.current hclaw huPrime hantiOriented).mp ⟨s, huOriented⟩
  have hstep :
      D.finalHole.externalDegree u =
        D.initialHole.externalDegree u + 1 := by
    apply degree_step_of_reorient D X.currentSide u
    simpa [orientedCurrent] using hlocal.2
  let last : Nat := X.priorCount - 1
  have hlast : last < X.priorCount := by
    dsimp [last]
    have hpos := X.priorCount_pos
    omega
  have hno :=
    no_earlierAnticommutation_of_mixedSideHistory
      X hclaw hu huPrime hanti
  have hnotAntiOriented : ∀ r : Nat, r ≤ last →
      ¬(X.history.orientedBlock r).path.AnticommutesWith u := by
    intro r hrle hantiEarlier
    apply hno r (lt_of_le_of_lt hrle hlast)
    simpa using hantiEarlier
  have hhistory :=
    X.history.finalDegree_mod_two_eq_initial_of_no_oriented_anticommuting_through
      u last hnotAntiOriented
  have hlink :
      (X.history.carrier.block last).finalHole.externalDegree u =
        D.initialHole.externalDegree u :=
    (X.history.carrier.block last).finalHole.externalDegree_eq_of_range_eq
      D.initialHole X.final_before_current
  have horiginalEven :
      Even (X.history.carrier.block 0).initialHole.card := by
    apply initialHole_even_of_reorient
      (X.history.carrier.block 0) (X.history.side 0)
    simpa [MixedSidePathBlockHistory.orientedBlock] using
      (X.history.localData 0).neighborhood.alternating.initialHole_even
  have hcurrentEven : Even D.initialHole.card := by
    apply initialHole_even_of_reorient D X.currentSide
    simpa [orientedCurrent] using
      X.current.neighborhood.alternating.initialHole_even
  constructor
  · intro hfour
    have hcurrentThree : D.initialHole.externalDegree u = 3 := by
      omega
    have horiginalOdd :
        (X.history.carrier.block 0).initialHole.externalDegree u % 2 = 1 := by
      rw [← hhistory, hlink, hcurrentThree]
    exact IndexedInducedHole.externalDegree_eq_three_of_even_and_odd_any
      (X.history.carrier.block 0).initialHole
      hclaw horiginalEven horiginalOdd
  · intro horiginalThree
    have hcurrentOdd : D.initialHole.externalDegree u % 2 = 1 := by
      rw [← hlink, hhistory, horiginalThree]
    have hcurrentThree : D.initialHole.externalDegree u = 3 :=
      D.initialHole.externalDegree_eq_three_of_even_and_odd_any
        hclaw hcurrentEven hcurrentOdd
    omega

end MixedSideFullDefinition19Lemma11AHistoryData

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph