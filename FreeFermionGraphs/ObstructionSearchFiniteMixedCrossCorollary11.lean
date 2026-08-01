import FreeFermionGraphs.ObstructionSearchFiniteMixedContext
import FreeFermionGraphs.ObstructionSearchFiniteMixedCorollary11

/-!
# Corollary 11 between finite mixed-side contexts

Two literal path blocks from different initialized executions may be compared
provided their finite contexts are rooted at the same original hole.  This
module derives every hypothesis of the concrete Corollary 11 theorem from the
zero-or-positive finite contexts.

A shared dependent vertex first forces the two selected component sides to be
equal.  In that common orientation, evenness, original carrier colouring, and
both base common-neighbour properties are consequences of the stored local
Definition 19 data and bounded prefixes.  No infinite history is used.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation

private theorem even_initialHole_of_reorient
    (D : ConcretePathDeformation O Cprime)
    (side : DeformationSide)
    (hEven : Even (D.reorient side).initialHole.card) :
    Even D.initialHole.card := by
  cases side <;> exact hEven

private theorem mem_reorient_initialHole_of_mem_initialHole
    (D : ConcretePathDeformation O Cprime)
    (side : DeformationSide)
    {x : V}
    (hx : x ∈ Set.range D.initialHole.vertex) :
    x ∈ Set.range (D.reorient side).initialHole.vertex := by
  cases side <;> exact hx

private theorem mem_initialHole_of_mem_reorient_initialHole
    (D : ConcretePathDeformation O Cprime)
    (side : DeformationSide)
    {x : V}
    (hx : x ∈ Set.range (D.reorient side).initialHole.vertex) :
    x ∈ Set.range D.initialHole.vertex := by
  cases side <;> exact hx

private theorem mem_original_colors_of_mem_oriented_colors
    (side : DeformationSide)
    {x : V}
    (hx : x ∈ (side.family O).Ca ∪ (side.family O).Cb) :
    x ∈ O.Ca ∪ O.Cb := by
  cases side with
  | ac =>
      simpa [DeformationSide.family] using hx
  | bd =>
      simpa [DeformationSide.family, swapSides, Set.union_comm] using hx

private theorem mem_oriented_colors_of_mem_original_colors
    (side : DeformationSide)
    {x : V}
    (hx : x ∈ O.Ca ∪ O.Cb) :
    x ∈ (side.family O).Ca ∪ (side.family O).Cb := by
  cases side with
  | ac =>
      simpa [DeformationSide.family] using hx
  | bd =>
      simpa [DeformationSide.family, swapSides, Set.union_comm] using hx

private theorem side_eq_of_oriented_cd
    (sideD sideE : DeformationSide)
    {x : V}
    (hxD : x ∈ (sideD.family O).Cd)
    (hxE : x ∈ (sideE.family O).Cd)
    (hnotD : x ∈ (sideD.family O).Cc →
      x ∉ (sideD.family O).Cd)
    (hnotE : x ∈ (sideE.family O).Cc →
      x ∉ (sideE.family O).Cd) :
    sideD = sideE := by
  cases sideD with
  | ac =>
      cases sideE with
      | ac => rfl
      | bd =>
          exfalso
          apply hnotD (by
            simpa [DeformationSide.family, swapSides] using hxE)
          simpa [DeformationSide.family] using hxD
  | bd =>
      cases sideE with
      | ac =>
          exfalso
          apply hnotE (by
            simpa [DeformationSide.family, swapSides] using hxD)
          simpa [DeformationSide.family] using hxE
      | bd => rfl

namespace FiniteMixedSideLemma11AContext

variable {D : ConcretePathDeformation O Cprime}
  {originalHole : IndexedInducedHole G}

/-- The fixed original hole is even in both the first-block and bounded-prefix
cases. -/
theorem originalHole_even
    (X : FiniteMixedSideLemma11AContext D originalHole) :
    Even originalHole.card := by
  cases X with
  | first side F hOriginal =>
      have hEvenD : Even D.initialHole.card :=
        even_initialHole_of_reorient D side
          F.neighborhood.alternating.initialHole_even
      have hcard : D.initialHole.card = originalHole.card :=
        IndexedInducedHole.card_eq_of_range_eq
          D.initialHole originalHole hOriginal
      rw [← hcard]
      exact hEvenD
  | later H =>
      let first : Fin H.priorCount := ⟨0, H.priorCount_pos⟩
      have hEvenFirst : Even (H.priorBlock first).initialHole.card :=
        even_initialHole_of_reorient
          (H.priorBlock first) (H.priorSide first) (by
            simpa [FiniteMixedSideLemma11AHistoryData.orientedPrior] using
              (H.priorData first).neighborhood.alternating.initialHole_even)
      have hcard :
          (H.priorBlock first).initialHole.card = originalHole.card :=
        IndexedInducedHole.card_eq_of_range_eq
          (H.priorBlock first).initialHole originalHole (by
            simpa [first] using H.firstInitial_eq_original)
      rw [← hcard]
      exact hEvenFirst

/-- The fixed original-hole carrier lies in the two original colouring
classes, independently of the selected side of the represented block. -/
theorem originalHole_carrier_subset
    (X : FiniteMixedSideLemma11AContext D originalHole) :
    Set.range originalHole.vertex ⊆ O.Ca ∪ O.Cb := by
  cases X with
  | first side F hOriginal =>
      intro x hx
      have hxInitial : x ∈ Set.range D.initialHole.vertex := by
        rw [hOriginal]
        exact hx
      have hxOrientedInitial :
          x ∈ Set.range (D.reorient side).initialHole.vertex :=
        mem_reorient_initialHole_of_mem_initialHole D side hxInitial
      have hxBefore :
          x ∈ Set.range
            ((D.reorient side).deformation.step
              (D.reorient side).firstIndex).before.vertex := by
        simpa [ConcretePathDeformation.initialHole] using hxOrientedInitial
      have hxSelected :
          x ∈ (side.family O).Ca ∪ (side.family O).Cb :=
        (F.neighborhood.mechanical.stepGeometry
          (D.reorient side).firstIndex).before_subset hxBefore
      exact mem_original_colors_of_mem_oriented_colors side hxSelected
  | later H =>
      intro x hx
      let first : Fin H.priorCount := ⟨0, H.priorCount_pos⟩
      let A0 := H.orientedPrior first
      have hxCarrierInitial :
          x ∈ Set.range (H.priorBlock first).initialHole.vertex := by
        rw [H.firstInitial_eq_original]
        exact hx
      have hxOrientedInitial : x ∈ Set.range A0.initialHole.vertex := by
        simpa [A0, FiniteMixedSideLemma11AHistoryData.orientedPrior] using
          (mem_reorient_initialHole_of_mem_initialHole
            (H.priorBlock first) (H.priorSide first) hxCarrierInitial)
      have hxBefore :
          x ∈ Set.range
            (A0.deformation.step A0.firstIndex).before.vertex := by
        simpa [ConcretePathDeformation.initialHole] using hxOrientedInitial
      have hxSelected :
          x ∈ ((H.priorSide first).family O).Ca ∪
            ((H.priorSide first).family O).Cb :=
        ((H.priorData first).neighborhood.mechanical.stepGeometry
          A0.firstIndex).before_subset hxBefore
      exact mem_original_colors_of_mem_oriented_colors
        (H.priorSide first) hxSelected

/-- The base common neighbour of the represented oriented block lies on the
fixed original hole. -/
theorem baseCommonNeighborOn_originalHole
    (X : FiniteMixedSideLemma11AContext D originalHole)
    (hclaw : G.IsClawFree) :
    (X.side.family O).BaseCommonNeighborOn
      (D.reorient X.side) originalHole := by
  cases X with
  | first side F hOriginal =>
      intro u hu
      let A := D.reorient side
      obtain ⟨v, hvInitial, _hvFinal, huv, hjv, hkv,
          hvCb, _hvNotPrime⟩ :=
        A.lemma11ai_commonNeighbor_currentBlock F hclaw hu
      have hvCarrier : v ∈ Set.range D.initialHole.vertex :=
        mem_initialHole_of_mem_reorient_initialHole D side (by
          simpa [A] using hvInitial)
      have hvOriginal : v ∈ Set.range originalHole.vertex := by
        rw [← hOriginal]
        exact hvCarrier
      refine ⟨v, hvOriginal, huv, ?_, ?_, hvCb⟩
      · simpa [A, ConcretePathDeformation.firstIndex,
          FiniteMixedSideLemma11AContext.side] using hjv
      · simpa [A, ConcretePathDeformation.firstIndex,
          FiniteMixedSideLemma11AContext.side] using hkv
  | later H =>
      exact H.currentBaseCommonNeighborOn hclaw

/-- Every dependent vertex of the represented raw block belongs to the fixed
prime-hole carrier. -/
theorem dependent_mem_prime
    (_X : FiniteMixedSideLemma11AContext D originalHole)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s) :
    u ∈ Cprime := by
  let i : Fin D.deformation.stepCount :=
    ⟨s, D.index_lt_of_mem_dependentAt hu⟩
  have huStep : u ∈ (D.deformation.step i).dependentSet := by
    simpa [i] using D.mem_step_dependentSet_of_mem_dependentAt hu
  exact
    ((ConcreteDeformationStep.mem_dependentSet
      (D.deformation.step i)).1 huStep).1

/-- A dependent vertex lies in `C_d` after orienting by the recorded side. -/
theorem dependent_mem_oriented_cd
    (X : FiniteMixedSideLemma11AContext D originalHole)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s) :
    u ∈ (X.side.family O).Cd := by
  have huOriented : u ∈ (D.reorient X.side).dependentAt s := by
    rw [D.reorient_dependentAt X.side s]
    exact hu
  exact X.currentData.neighborhood.mechanical.dependent_mem_cd huOriented

/-- A shared dependent vertex forces two finite contexts to select the same
manuscript component side. -/
theorem side_eq_of_sharedDependentVertex
    {E : ConcretePathDeformation O Cprime}
    (A : FiniteMixedSideLemma11AContext D originalHole)
    (B : FiniteMixedSideLemma11AContext E originalHole)
    {s t : Nat} {u : V}
    (huD : u ∈ D.dependentAt s)
    (huE : u ∈ E.dependentAt t) :
    A.side = B.side := by
  have huDPrime : u ∈ Cprime := A.dependent_mem_prime huD
  have huEPrime : u ∈ Cprime := B.dependent_mem_prime huE
  have huDCd : u ∈ (A.side.family O).Cd :=
    A.dependent_mem_oriented_cd huD
  have huECd : u ∈ (B.side.family O).Cd :=
    B.dependent_mem_oriented_cd huE
  have hnotD : u ∈ (A.side.family O).Cc →
      u ∉ (A.side.family O).Cd := by
    intro huCc
    exact
      (A.currentData.neighborhood.overlapColoring.not_mem_ca_cd_of_mem_cc
        huDPrime huCc).2
  have hnotE : u ∈ (B.side.family O).Cc →
      u ∉ (B.side.family O).Cd := by
    intro huCc
    exact
      (B.currentData.neighborhood.overlapColoring.not_mem_ca_cd_of_mem_cc
        huEPrime huCc).2
  exact side_eq_of_oriented_cd A.side B.side huDCd huECd hnotD hnotE

/-- Corollary 11 for arbitrary distinct blocks from two finite contexts rooted
at the same original hole. -/
theorem noSharedDependentAnticommutingWitness
    {E : ConcretePathDeformation O Cprime}
    (A : FiniteMixedSideLemma11AContext D originalHole)
    (B : FiniteMixedSideLemma11AContext E originalHole)
    (hclaw : G.IsClawFree)
    (hpathNe :
      Set.range D.path.vertex ≠ Set.range E.path.vertex) :
    ¬SharedDependentAnticommutingWitness
      D.path E.path D.dependentAt E.dependentAt := by
  intro hshared
  rcases hshared with
    ⟨u, s, t, huD, huE, hantiD, hantiE⟩
  have hside : A.side = B.side :=
    A.side_eq_of_sharedDependentVertex B huD huE
  let DA : ConcretePathDeformation (A.side.family O) Cprime :=
    D.reorient A.side
  let EB : ConcretePathDeformation (A.side.family O) Cprime :=
    E.reorient A.side
  have hDataD : DA.FullDefinition19Lemma11AData := by
    simpa [DA] using A.currentData
  have hDataE : EB.FullDefinition19Lemma11AData := by
    have h := B.currentData
    rw [← hside] at h
    simpa [EB] using h
  have hEven : Even originalHole.card := A.originalHole_even
  have hcarrierOriginal :
      Set.range originalHole.vertex ⊆ O.Ca ∪ O.Cb :=
    A.originalHole_carrier_subset
  have hcarrier :
      Set.range originalHole.vertex ⊆
        (A.side.family O).Ca ∪ (A.side.family O).Cb := by
    intro x hx
    exact mem_oriented_colors_of_mem_original_colors
      A.side (hcarrierOriginal hx)
  have hpathNeOriented :
      Set.range DA.path.vertex ≠ Set.range EB.path.vertex := by
    simpa only [DA, EB, ConcretePathDeformation.reorient_path] using hpathNe
  have hcommonD :
      (A.side.family O).BaseCommonNeighborOn DA originalHole := by
    simpa [DA] using A.baseCommonNeighborOn_originalHole hclaw
  have hcommonE :
      (A.side.family O).BaseCommonNeighborOn EB originalHole := by
    have h := B.baseCommonNeighborOn_originalHole hclaw
    rw [← hside] at h
    simpa [EB] using h
  have hno :
      ¬SharedDependentAnticommutingWitness
        DA.path EB.path DA.dependentAt EB.dependentAt :=
    noSharedDependentAnticommutingWitness_of_concreteBlocks
      DA EB hDataD hDataE originalHole hclaw hEven hcarrier
      hpathNeOriented hcommonD hcommonE
  apply hno
  refine ⟨u, s, t, ?_, ?_, ?_, ?_⟩
  · change u ∈ (D.reorient A.side).dependentAt s
    rw [D.reorient_dependentAt A.side s]
    exact huD
  · change u ∈ (E.reorient A.side).dependentAt t
    rw [E.reorient_dependentAt A.side t]
    exact huE
  · simpa only [DA, ConcretePathDeformation.reorient_path] using hantiD
  · simpa only [EB, ConcretePathDeformation.reorient_path] using hantiE

end FiniteMixedSideLemma11AContext

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
