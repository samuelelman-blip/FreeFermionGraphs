import FreeFermionGraphs.ObstructionSearchFiniteMixedCorollary11
import FreeFermionGraphs.Lemma11AFullDefinition19HistoryComplete

/-!
# Lemma 11(a.ii) on bounded mixed-side histories

Corollary 11 yields the Corollary 12 endpoint alternative for every earlier
block.  Endpoint persistence then eliminates all earlier anticommuting paths,
and parity through the finite carrier prefix transports the original-hole
degree to the current block.

The entire argument is indexed by `Fin priorCount`; it introduces no infinite
history and assumes no conclusion of Lemma 11 or Lemma 14.
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
    (A : ConcretePathDeformation O Cprime)
    (side : DeformationSide) :
    ((A.reorient side).deformation.step
      (A.reorient side).firstIndex).introduced =
      (A.deformation.step A.firstIndex).introduced := by
  cases side <;> rfl

private theorem initialHole_even_of_reorient
    (A : ConcretePathDeformation O Cprime)
    (side : DeformationSide)
    (hEven : Even (A.reorient side).initialHole.card) :
    Even A.initialHole.card := by
  cases side <;> exact hEven

private theorem degree_step_of_reorient
    (A : ConcretePathDeformation O Cprime)
    (side : DeformationSide)
    (u : V)
    (hstep :
      (A.reorient side).finalHole.externalDegree u =
        (A.reorient side).initialHole.externalDegree u + 1) :
    A.finalHole.externalDegree u =
      A.initialHole.externalDegree u + 1 := by
  cases side <;> exact hstep

private theorem not_mem_initialHole_of_reorient
    (A : ConcretePathDeformation O Cprime)
    (side : DeformationSide)
    {u : V}
    (hu : u ∉ Set.range (A.reorient side).initialHole.vertex) :
    u ∉ Set.range A.initialHole.vertex := by
  cases side <;> exact hu

namespace FiniteMixedSideLemma11AHistoryData

variable {D : ConcretePathDeformation O Cprime}
  {originalHole : IndexedInducedHole G}

/-- Corollary 12's endpoint alternative for every earlier block in the
bounded mixed-side prefix. -/
theorem earlierAnticommutingEndpointRule
    (H : FiniteMixedSideLemma11AHistoryData D originalHole)
    (hclaw : G.IsClawFree)
    {u : V}
    (huPrime : u ∈ Cprime)
    (hantiCurrent : D.path.AnticommutesWith u) :
    ∀ r : Fin H.priorCount,
      (H.priorBlock r).path.AnticommutesWith u →
        u = ((H.priorBlock r).deformation.step
          (H.priorBlock r).firstIndex).introduced ∨
        u = (D.deformation.step D.firstIndex).introduced := by
  intro r hantiEarlier
  let A := H.orientedPrior r
  let E := D.reorient H.currentSide
  have hAData : A.FullDefinition19Lemma11AData := by
    simpa [A, orientedPrior] using H.priorData r
  have hEData : E.FullDefinition19Lemma11AData := by
    simpa [E] using H.current
  have hnoCarrier := H.noSharedDependentAnticommutingWitness hclaw r
  have hnoOriented :
      ¬SharedDependentAnticommutingWitness
        A.path E.path A.dependentAt E.dependentAt := by
    intro hshared
    apply hnoCarrier
    rcases hshared with
      ⟨v, s, t, hvA, hvE, hantiA, hantiE⟩
    refine ⟨v, s, t, ?_, ?_, ?_, ?_⟩
    · change v ∈
        ((H.priorBlock r).reorient (H.priorSide r)).dependentAt s at hvA
      rw [(H.priorBlock r).reorient_dependentAt (H.priorSide r) s] at hvA
      exact hvA
    · change v ∈ (D.reorient H.currentSide).dependentAt t at hvE
      rw [D.reorient_dependentAt H.currentSide t] at hvE
      exact hvE
    · simpa [A, orientedPrior] using hantiA
    · simpa [E] using hantiE
  have hantiA : A.path.AnticommutesWith u := by
    simpa [A, orientedPrior] using hantiEarlier
  have hantiE : E.path.AnticommutesWith u := by
    simpa [E] using hantiCurrent
  have hendpoint :=
    A.anticommutes_endpoint_of_noSharedDependent
      E hAData hEData hclaw hnoOriented
      huPrime hantiA hantiE
  rcases hendpoint with hA | hE
  · left
    calc
      u = (A.deformation.step A.firstIndex).introduced := hA
      _ = ((H.priorBlock r).deformation.step
          (H.priorBlock r).firstIndex).introduced := by
        simpa [A, orientedPrior] using
          reorient_firstIntroduced_eq
            (H.priorBlock r) (H.priorSide r)
  · right
    calc
      u = (E.deformation.step E.firstIndex).introduced := hE
      _ = (D.deformation.step D.firstIndex).introduced := by
        simpa [E] using
          reorient_firstIntroduced_eq D H.currentSide

/-- No earlier path anticommutes with a current dependent anticommuting
vertex. -/
theorem no_earlierAnticommutation
    (H : FiniteMixedSideLemma11AHistoryData D originalHole)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPrime : u ∈ Cprime)
    (hanti : D.path.AnticommutesWith u) :
    ∀ r : Fin H.priorCount,
      ¬(H.priorBlock r).path.AnticommutesWith u := by
  have huOriented : u ∈ (D.reorient H.currentSide).dependentAt s := by
    rw [D.reorient_dependentAt H.currentSide s]
    exact hu
  have hantiOriented :
      (D.reorient H.currentSide).path.AnticommutesWith u := by
    simpa using hanti
  have hlocal :=
    ((D.reorient H.currentSide).lemma11a_membership_iff_ne_first_and_degree
      H.current hclaw huPrime hantiOriented).mp ⟨s, huOriented⟩
  have hfirstCurrent :
      ((D.reorient H.currentSide).deformation.step
        (D.reorient H.currentSide).firstIndex).introduced =
        (D.deformation.step D.firstIndex).introduced :=
    reorient_firstIntroduced_eq D H.currentSide
  have hcurrentNotFirst :
      u ≠ (D.deformation.step D.firstIndex).introduced := by
    intro huFirst
    apply hlocal.1
    exact huFirst.trans hfirstCurrent.symm
  have huOutsideOriented :=
    (D.reorient H.currentSide).dependent_not_mem_initialHole_of_anticommutes
      H.current hclaw huOriented huPrime hantiOriented
  have huOutsideCurrent : u ∉ Set.range D.initialHole.vertex :=
    not_mem_initialHole_of_reorient D H.currentSide huOutsideOriented
  have hendpoint := H.earlierAnticommutingEndpointRule
    hclaw huPrime hanti
  intro r hantiEarlier
  rcases hendpoint r hantiEarlier with
      hEarlierEndpoint | hCurrentEndpoint
  · apply huOutsideCurrent
    rw [hEarlierEndpoint]
    exact H.earlierFirstIntroduced_mem_currentInitial r
  · exact hcurrentNotFirst hCurrentEndpoint

/-- Lemma 11(a.ii)'s numerical degree equivalence for a bounded positive
mixed-side Definition 19 history. -/
theorem lemma11aii_degree_iff
    (H : FiniteMixedSideLemma11AHistoryData D originalHole)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPrime : u ∈ Cprime)
    (hanti : D.path.AnticommutesWith u) :
    D.finalHole.externalDegree u = 4 ↔
      originalHole.externalDegree u = 3 := by
  have huOriented : u ∈ (D.reorient H.currentSide).dependentAt s := by
    rw [D.reorient_dependentAt H.currentSide s]
    exact hu
  have hantiOriented :
      (D.reorient H.currentSide).path.AnticommutesWith u := by
    simpa using hanti
  have hlocal :=
    ((D.reorient H.currentSide).lemma11a_membership_iff_ne_first_and_degree
      H.current hclaw huPrime hantiOriented).mp ⟨s, huOriented⟩
  have hstep :
      D.finalHole.externalDegree u =
        D.initialHole.externalDegree u + 1 :=
    degree_step_of_reorient D H.currentSide u hlocal.2
  have hno := H.no_earlierAnticommutation hclaw hu huPrime hanti
  have hhistory :=
    H.lastFinalDegree_mod_two_eq_original_of_no_oriented_anticommuting
      u (by
        intro r hantiEarlier
        exact hno r (by simpa [orientedPrior] using hantiEarlier))
  have hlink :
      (H.priorBlock H.lastIndex).finalHole.externalDegree u =
        D.initialHole.externalDegree u :=
    (H.priorBlock H.lastIndex).finalHole.externalDegree_eq_of_range_eq
      D.initialHole H.lastFinal_eq_current'
  let first : Fin H.priorCount := ⟨0, H.priorCount_pos⟩
  have hfirstEven : Even (H.priorBlock first).initialHole.card := by
    apply initialHole_even_of_reorient
      (H.priorBlock first) (H.priorSide first)
    simpa [orientedPrior] using
      (H.priorData first).neighborhood.alternating.initialHole_even
  have horiginalEven : Even originalHole.card := by
    have hcard :
        (H.priorBlock first).initialHole.card = originalHole.card :=
      IndexedInducedHole.card_eq_of_range_eq
        (H.priorBlock first).initialHole originalHole (by
          simpa [first] using H.firstInitial_eq_original)
    rw [← hcard]
    exact hfirstEven
  have hcurrentEven : Even D.initialHole.card := by
    apply initialHole_even_of_reorient D H.currentSide
    exact H.current.neighborhood.alternating.initialHole_even
  constructor
  · intro hfour
    have hcurrentThree : D.initialHole.externalDegree u = 3 := by
      omega
    have horiginalOdd : originalHole.externalDegree u % 2 = 1 := by
      rw [← hhistory, hlink, hcurrentThree]
    exact IndexedInducedHole.externalDegree_eq_three_of_even_and_odd_any
      originalHole hclaw horiginalEven horiginalOdd
  · intro horiginalThree
    have hcurrentOdd : D.initialHole.externalDegree u % 2 = 1 := by
      rw [← hlink, hhistory, horiginalThree]
    have hcurrentThree : D.initialHole.externalDegree u = 3 :=
      D.initialHole.externalDegree_eq_three_of_even_and_odd_any
        hclaw hcurrentEven hcurrentOdd
    omega

end FiniteMixedSideLemma11AHistoryData

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
