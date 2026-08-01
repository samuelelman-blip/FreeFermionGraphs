import FreeFermionGraphs.ObstructionSearchFiniteMixedLemma11A
import FreeFermionGraphs.ObstructionSearchTwoSidedMixedTypedClone

/-!
# Exact Lemma 11(a.ii) on bounded mixed-side histories

The finite trace retains the Definition 19 fact that every removed vertex of
the current block lies on the fixed original hole.  Together with the bounded
common-neighbour transport and numerical Lemma 11(a.ii), that datum forces the
clone centre into the opposite pairing class.

No extra carrier assumption, infinite history, or conclusion of Lemma 11 or
Lemma 14 is introduced.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation

private theorem removedAdj_of_reorient
    (A : ConcretePathDeformation O Cprime)
    (side : DeformationSide)
    (i : Fin A.deformation.stepCount)
    {v : V}
    (h : G.Adj
      (((A.reorient side).deformation.step i).before.vertex
        ((A.reorient side).deformation.step i).removedIndex) v) :
    G.Adj
      ((A.deformation.step i).before.vertex
        (A.deformation.step i).removedIndex) v := by
  cases side <;> exact h

private theorem mem_reorient_step_dependentSet
    (A : ConcretePathDeformation O Cprime)
    (side : DeformationSide)
    (i : Fin A.deformation.stepCount)
    {u : V}
    (h : u ∈ (A.deformation.step i).dependentSet) :
    u ∈ ((A.reorient side).deformation.step i).dependentSet := by
  cases side <;> exact h

namespace FiniteMixedSideLemma11AHistoryData

variable {D : ConcretePathDeformation O Cprime}
  {originalHole : IndexedInducedHole G}

/-- The fixed original hole is covered by the original colour classes in the
orientation selected by the current block. -/
theorem originalHole_subset_currentOriginalClasses
    (H : FiniteMixedSideLemma11AHistoryData D originalHole) :
    Set.range originalHole.vertex ⊆
      (H.currentSide.family O).Ca ∪
        (H.currentSide.family O).Cb := by
  intro x hx
  let first : Fin H.priorCount := ⟨0, H.priorCount_pos⟩
  have hxCarrierInitial :
      x ∈ Set.range (H.priorBlock first).initialHole.vertex := by
    rw [H.firstInitial_eq_original]
    exact hx
  have hxOriented :
      x ∈ Set.range (H.orientedPrior first).initialHole.vertex := by
    simpa [orientedPrior] using
      (show x ∈ Set.range
          ((H.priorBlock first).reorient
            (H.priorSide first)).initialHole.vertex by
        rw [(H.priorBlock first).reorient_initialHole_range
          (H.priorSide first)]
        exact hxCarrierInitial)
  have hxFirstSide :=
    ((H.priorData first).neighborhood.mechanical.stepGeometry
      (H.orientedPrior first).firstIndex).before_subset (by
        simpa [ConcretePathDeformation.initialHole] using hxOriented)
  have hxOriginal : x ∈ O.Ca ∪ O.Cb := by
    cases hside : H.priorSide first with
    | ac =>
        simpa [hside, DeformationSide.family] using hxFirstSide
    | bd =>
        rcases hxFirstSide with hxCb | hxCa
        · exact Or.inr (by
            simpa [hside, DeformationSide.family] using hxCb)
        · exact Or.inl (by
            simpa [hside, DeformationSide.family] using hxCa)
  cases hside : H.currentSide with
  | ac =>
      simpa [hside, DeformationSide.family] using hxOriginal
  | bd =>
      rcases hxOriginal with hxCa | hxCb
      · exact Or.inr (by
          simpa [hside, DeformationSide.family] using hxCa)
      · exact Or.inl (by
          simpa [hside, DeformationSide.family] using hxCb)

/-- The persistent common neighbour at an arbitrary dependent step of the
current block belongs to the fixed original hole. -/
theorem currentCommonNeighborOnOriginal
    (H : FiniteMixedSideLemma11AHistoryData D originalHole)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s) :
    ∃ v : V,
      v ∈ Set.range originalHole.vertex ∧
      G.Adj u v ∧
      G.Adj
        (D.deformation.step
          ⟨s, D.index_lt_of_mem_dependentAt hu⟩).introduced v ∧
      G.Adj
        ((D.deformation.step
          ⟨s, D.index_lt_of_mem_dependentAt hu⟩).before.vertex
            (D.deformation.step
              ⟨s, D.index_lt_of_mem_dependentAt hu⟩).removedIndex) v ∧
      v ∈ (H.currentSide.family O).Cb := by
  have huOriented :
      u ∈ (D.reorient H.currentSide).dependentAt s := by
    rw [D.reorient_dependentAt H.currentSide s]
    exact hu
  obtain ⟨v, hvCurrentInitial, _hvFinal, huv, hjv, hkv,
      hvCb, hvNotPrime⟩ :=
    (D.reorient H.currentSide).lemma11ai_commonNeighbor_currentBlock
      H.current hclaw huOriented
  have hvCarrierCurrentInitial : v ∈ Set.range D.initialHole.vertex := by
    rw [← D.reorient_initialHole_range H.currentSide]
    exact hvCurrentInitial
  have hvLast :
      v ∈ Set.range (H.priorBlock H.lastIndex).finalHole.vertex := by
    rw [H.lastFinal_eq_current']
    exact hvCarrierCurrentInitial
  have hvFirst := H.mem_firstInitial_of_mem_final_through
    H.lastIndex.val H.lastIndex.isLt (by simpa using hvLast) (by
      intro r _hr j hEq
      apply hvNotPrime
      rw [hEq]
      simpa [orientedPrior] using
        (H.priorData r).neighborhood.primeHole.introduced_mem j)
  have hvOriginal : v ∈ Set.range originalHole.vertex := by
    rw [H.firstInitial_eq_original] at hvFirst
    exact hvFirst
  refine ⟨v, hvOriginal, huv, ?_, ?_, hvCb⟩
  · simpa using hjv
  · exact removedAdj_of_reorient D H.currentSide
      ⟨s, D.index_lt_of_mem_dependentAt hu⟩ hkv

/-- The clone centre forced by degree three lies in the current orientation's
original `C_a` class. -/
theorem cloneCenter_mem_currentCa
    (H : FiniteMixedSideLemma11AHistoryData D originalHole)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    {q : Fin originalHole.card}
    (hclone : originalHole.SingleVertexDeformation u q) :
    originalHole.vertex q ∈ (H.currentSide.family O).Ca := by
  let i : Fin D.deformation.stepCount :=
    ⟨s, D.index_lt_of_mem_dependentAt hu⟩
  obtain ⟨v, hvOriginal, huv, _hjv, hkv, hvCb⟩ :=
    H.currentCommonNeighborOnOriginal hclaw hu
  let k : V := (D.deformation.step i).before.vertex
    (D.deformation.step i).removedIndex
  have hkOriginal : k ∈ Set.range originalHole.vertex := by
    simpa [k] using H.currentRemoved_mem_original i
  have hui : u ∈ (D.deformation.step i).dependentSet :=
    D.mem_step_dependentSet_of_mem_dependentAt hu
  have huk : ¬G.Adj u k := by
    simpa [k] using
      ((D.deformation.step i).mem_dependentSet.mp hui).2.2.2
  exact cloneCenter_mem_ca_of_commonNeighbor
    (H.currentSide.family O) originalHole
    H.current.neighborhood.colorClassesIndependent
    H.originalHole_subset_currentOriginalClasses hclone
    hvOriginal hvCb hkOriginal huv (by simpa [k] using hkv) huk

/-- Complete Lemma 11(a.ii), including the clone of opposite pairing type,
for a bounded positive mixed-side Definition 19 history. -/
theorem lemma11aii_exact
    (H : FiniteMixedSideLemma11AHistoryData D originalHole)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPrime : u ∈ Cprime)
    (hanti : D.path.AnticommutesWith u) :
    D.finalHole.externalDegree u = 4 ↔
      originalHole.externalDegree u = 3 ∧
        O.HasTypedClone .ad originalHole u := by
  have hdegree := H.lemma11aii_degree_iff hclaw hu huPrime hanti
  constructor
  · intro hfour
    have hthree : originalHole.externalDegree u = 3 :=
      hdegree.mp hfour
    have huOutside : u ∉ Set.range originalHole.vertex := by
      rintro ⟨q, rfl⟩
      have htwo := originalHole.externalDegree_vertex_eq_two q
      omega
    obtain ⟨q, hclone⟩ :=
      originalHole.exists_singleVertexDeformation_of_externalDegree_eq_three
        hclaw huOutside hthree
    have hcenter :
        originalHole.vertex q ∈ (H.currentSide.family O).Ca :=
      H.cloneCenter_mem_currentCa hclaw hu hclone
    let i : Fin D.deformation.stepCount :=
      ⟨s, D.index_lt_of_mem_dependentAt hu⟩
    have huiCarrier : u ∈ (D.deformation.step i).dependentSet :=
      D.mem_step_dependentSet_of_mem_dependentAt hu
    have huiOriented :
        u ∈ ((D.reorient H.currentSide).deformation.step i).dependentSet :=
      mem_reorient_step_dependentSet D H.currentSide i huiCarrier
    have huCd : u ∈ (H.currentSide.family O).Cd :=
      ((D.reorient H.currentSide).deformation.step i).dependent_mem_cd
        (H.current.neighborhood.mechanical.stepGeometry i) huiOriented
    have htypedCurrent :
        (H.currentSide.family O).HasTypedClone .ad originalHole u :=
      (H.currentSide.family O).hasTypedClone_opposite
        .ac originalHole hclone hcenter (by simpa using huCd)
    exact ⟨hthree,
      (DeformationSide.family_hasTypedClone_ad_iff
        H.currentSide O originalHole u).mp htypedCurrent⟩
  · rintro ⟨hthree, _htyped⟩
    exact hdegree.mpr hthree

end FiniteMixedSideLemma11AHistoryData

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
