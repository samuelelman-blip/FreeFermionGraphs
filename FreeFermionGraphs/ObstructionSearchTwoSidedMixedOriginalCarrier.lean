import FreeFermionGraphs.ObstructionSearchTwoSidedMixedCloneExistence

/-!
# Original-carrier data for positive mixed-side Lemma 11(a.ii)

Definition 19 labels every removed path vertex `k` as a vertex of the fixed
original hole `C`, even when the ordered deformation mixes the two component
sides.  The carrier-only mixed history does not by itself retain that global
label: opposite-side path components may intersect in `C ∩ C'`.

This module isolates the exact missing Definition 19 invariant for the current
block and uses it to complete the oppositely typed clone clause of Lemma
11(a.ii) for a positive mixed-side history.  No obstruction-search execution
is constructed, and no conclusion of Lemma 14 is assumed.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation

namespace MixedSideFullDefinition19Lemma11AHistoryData

variable {D : ConcretePathDeformation O Cprime}

/-- The current block's removed vertices retain their manuscript labels as
vertices of the fixed original hole.  This is direct Definition 19 data, not a
conclusion of Lemma 11 or Lemma 14. -/
def CurrentRemovedVerticesInOriginal
    (X : D.MixedSideFullDefinition19Lemma11AHistoryData) : Prop :=
  ∀ i : Fin D.deformation.stepCount,
    (D.deformation.step i).before.vertex
        (D.deformation.step i).removedIndex ∈
      Set.range X.originalHole.vertex

/-- The original hole is bipartitioned by the original colour classes in the
orientation selected by the current block.  Exchanging the two manuscript
sides only exchanges the order of the two sets in their union. -/
theorem originalHole_subset_currentOriginalClasses
    (X : D.MixedSideFullDefinition19Lemma11AHistoryData) :
    Set.range X.originalHole.vertex ⊆
      (X.currentSide.family O).Ca ∪ (X.currentSide.family O).Cb := by
  intro x hx
  have hxOriented :
      x ∈ Set.range (X.history.orientedBlock 0).initialHole.vertex := by
    simpa [MixedSideFullDefinition19Lemma11AHistoryData.originalHole,
      MixedSidePathBlockHistory.orientedBlock] using hx
  have hxFirstSide :=
    ((X.history.localData 0).neighborhood.mechanical.stepGeometry
      (X.history.orientedBlock 0).firstIndex).before_subset hxOriented
  have hxOriginal : x ∈ O.Ca ∪ O.Cb := by
    cases hside : X.history.side 0 with
    | ac =>
        simpa [hside, DeformationSide.family] using hxFirstSide
    | bd =>
        rcases hxFirstSide with hxCb | hxCa
        · exact Or.inr (by simpa [hside, DeformationSide.family] using hxCb)
        · exact Or.inl (by simpa [hside, DeformationSide.family] using hxCa)
  cases hside : X.currentSide with
  | ac =>
      simpa [hside, DeformationSide.family] using hxOriginal
  | bd =>
      rcases hxOriginal with hxCa | hxCb
      · exact Or.inr (by simpa [hside, DeformationSide.family] using hxCa)
      · exact Or.inl (by simpa [hside, DeformationSide.family] using hxCb)

/-- The persistent common neighbour at an arbitrary dependent step of the
current block belongs to the fixed original hole.  Its colour is read in the
current block's selected orientation. -/
theorem currentCommonNeighborOnOriginal
    (X : D.MixedSideFullDefinition19Lemma11AHistoryData)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s) :
    ∃ v : V,
      v ∈ Set.range X.originalHole.vertex ∧
      G.Adj u v ∧
      G.Adj
        (D.deformation.step
          ⟨s, D.index_lt_of_mem_dependentAt hu⟩).introduced v ∧
      G.Adj
        ((D.deformation.step
          ⟨s, D.index_lt_of_mem_dependentAt hu⟩).before.vertex
            (D.deformation.step
              ⟨s, D.index_lt_of_mem_dependentAt hu⟩).removedIndex) v ∧
      v ∈ (X.currentSide.family O).Cb := by
  have huOriented : u ∈ X.orientedCurrent.dependentAt s := by
    rw [X.orientedCurrent_dependentAt s]
    exact hu
  obtain ⟨v, hvCurrentInitial, _hvFinal, huv, hjv, hkv,
      hvCb, hvNotPrime⟩ :=
    X.orientedCurrent.lemma11ai_commonNeighbor_currentBlock
      X.current hclaw huOriented
  have hvOrientedCurrentInitial :
      v ∈ Set.range (D.reorient X.currentSide).initialHole.vertex := by
    simpa [MixedSideFullDefinition19Lemma11AHistoryData.orientedCurrent] using
      hvCurrentInitial
  have hvCarrierCurrentInitial : v ∈ Set.range D.initialHole.vertex := by
    rw [← D.reorient_initialHole_range X.currentSide]
    exact hvOrientedCurrentInitial
  let last : Nat := X.priorCount - 1
  have hvLast :
      v ∈ Set.range
        (X.history.carrier.block last).finalHole.vertex := by
    rw [X.final_before_current]
    exact hvCarrierCurrentInitial
  have hvFirst :
      v ∈ Set.range
        (X.history.carrier.block 0).initialHole.vertex :=
    X.history.carrier.mem_firstInitial_of_mem_final_through last hvLast (by
      intro r _hr j hEq
      apply hvNotPrime
      rw [hEq]
      simpa using
        (X.history.localData r).neighborhood.primeHole.introduced_mem j)
  have hvOriginal : v ∈ Set.range X.originalHole.vertex := by
    simpa [MixedSideFullDefinition19Lemma11AHistoryData.originalHole] using
      hvFirst
  refine ⟨v, hvOriginal, huv, ?_, ?_, hvCb⟩
  · simpa [MixedSideFullDefinition19Lemma11AHistoryData.orientedCurrent] using
      hjv
  · simpa [MixedSideFullDefinition19Lemma11AHistoryData.orientedCurrent,
      ConcretePathDeformation.reorient, ConcreteDeformation.reorient] using
      hkv

/-- The clone centre forced by degree three lies in the current orientation's
original `C_a` class.  This is the colour step at the end of the manuscript
proof of Lemma 11(a.ii). -/
theorem cloneCenter_mem_currentCa
    (X : D.MixedSideFullDefinition19Lemma11AHistoryData)
    (hremoved : X.CurrentRemovedVerticesInOriginal)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    {q : Fin X.originalHole.card}
    (hclone : X.originalHole.SingleVertexDeformation u q) :
    X.originalHole.vertex q ∈ (X.currentSide.family O).Ca := by
  let i : Fin D.deformation.stepCount :=
    ⟨s, D.index_lt_of_mem_dependentAt hu⟩
  obtain ⟨v, hvOriginal, huv, _hjv, hkv, hvCb⟩ :=
    X.currentCommonNeighborOnOriginal hclaw hu
  let k : V := (D.deformation.step i).before.vertex
    (D.deformation.step i).removedIndex
  have hkOriginal : k ∈ Set.range X.originalHole.vertex := by
    simpa [k] using hremoved i
  have hui : u ∈ (D.deformation.step i).dependentSet :=
    D.mem_step_dependentSet_of_mem_dependentAt hu
  have huk : ¬G.Adj u k := by
    simpa [k] using ((D.deformation.step i).mem_dependentSet.mp hui).2.2.2
  exact cloneCenter_mem_ca_of_commonNeighbor
    (X.currentSide.family O) X.originalHole
    X.current.neighborhood.colorClassesIndependent
    X.originalHole_subset_currentOriginalClasses hclone
    hvOriginal hvCb hkOriginal huv (by simpa [k] using hkv) huk

/-- Exact Lemma 11(a.ii) for a positive mixed-side Definition 19 history,
once the current removed vertices retain their defining original-hole labels. -/
theorem lemma11aii_exact_of_mixedSideHistory
    (X : D.MixedSideFullDefinition19Lemma11AHistoryData)
    (hremoved : X.CurrentRemovedVerticesInOriginal)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPrime : u ∈ Cprime)
    (hanti : D.path.AnticommutesWith u) :
    D.finalHole.externalDegree u = 4 ↔
      X.originalHole.externalDegree u = 3 ∧
        O.HasTypedClone .ad X.originalHole u := by
  have hdegree :=
    X.lemma11aii_degree_iff_of_mixedSideHistory
      hclaw hu huPrime hanti
  constructor
  · intro hfour
    have hthree : X.originalHole.externalDegree u = 3 :=
      hdegree.mp hfour
    have huOutside : u ∉ Set.range X.originalHole.vertex := by
      rintro ⟨q, rfl⟩
      have htwo := X.originalHole.externalDegree_vertex_eq_two q
      omega
    obtain ⟨q, hclone⟩ :=
      X.originalHole.exists_singleVertexDeformation_of_externalDegree_eq_three
        hclaw huOutside hthree
    have hcenter :
        X.originalHole.vertex q ∈ (X.currentSide.family O).Ca :=
      X.cloneCenter_mem_currentCa hremoved hclaw hu hclone
    let i : Fin D.deformation.stepCount :=
      ⟨s, D.index_lt_of_mem_dependentAt hu⟩
    have huiCarrier : u ∈ (D.deformation.step i).dependentSet :=
      D.mem_step_dependentSet_of_mem_dependentAt hu
    have huiOriented :
        u ∈ (X.orientedCurrent.deformation.step i).dependentSet := by
      simpa [MixedSideFullDefinition19Lemma11AHistoryData.orientedCurrent,
        ConcretePathDeformation.reorient, ConcreteDeformation.reorient] using
        huiCarrier
    have huCd : u ∈ (X.currentSide.family O).Cd :=
      (X.orientedCurrent.deformation.step i).dependent_mem_cd
        (X.current.neighborhood.mechanical.stepGeometry i) huiOriented
    have htypedCurrent :
        (X.currentSide.family O).HasTypedClone .ad X.originalHole u :=
      (X.currentSide.family O).hasTypedClone_opposite
        .ac X.originalHole hclone hcenter (by simpa using huCd)
    exact ⟨hthree,
      (DeformationSide.family_hasTypedClone_ad_iff
        X.currentSide O X.originalHole u).mp htypedCurrent⟩
  · rintro ⟨hthree, _htyped⟩
    exact hdegree.mpr hthree

end MixedSideFullDefinition19Lemma11AHistoryData

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
