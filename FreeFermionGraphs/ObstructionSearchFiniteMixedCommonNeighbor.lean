import FreeFermionGraphs.ObstructionSearchFiniteMixedPersistence
import FreeFermionGraphs.Lemma11ACorollary11Proof

/-!
# Common neighbours on bounded mixed-side histories

Lemma 11(a.i) gives a common original-hole neighbour for the base dependent
set of each Definition 19 path block.  This file transports those witnesses
backward through the literal finite prefix and proves the component-side
reduction used at the start of Corollary 11.

All prior blocks are indexed by `Fin priorCount`.  No infinite history and no
conclusion of Lemma 11 or Lemma 14 is assumed.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation

private theorem mem_initialHole_of_mem_reorient_initialHole
    (A : ConcretePathDeformation O Cprime)
    (side : DeformationSide)
    {x : V}
    (hx : x ∈ Set.range (A.reorient side).initialHole.vertex) :
    x ∈ Set.range A.initialHole.vertex := by
  cases side <;> exact hx

private theorem dependent_mem_prime_of_mem_dependentAt
    (A : ConcretePathDeformation O Cprime)
    {s : Nat} {x : V}
    (hx : x ∈ A.dependentAt s) :
    x ∈ Cprime := by
  let i : Fin A.deformation.stepCount :=
    ⟨s, A.index_lt_of_mem_dependentAt hx⟩
  have hxStep :
      x ∈ (A.deformation.step i).dependentSet := by
    simpa [i] using A.mem_step_dependentSet_of_mem_dependentAt hx
  exact
    ((ConcreteDeformationStep.mem_dependentSet
      (A.deformation.step i)).1 hxStep).1

private theorem side_eq_of_oriented_cd
    (sideA sideB : DeformationSide)
    {x : V}
    (hxACd : x ∈ (sideA.family O).Cd)
    (hxBCd : x ∈ (sideB.family O).Cd)
    (hnotA : x ∈ (sideA.family O).Cc →
      x ∉ (sideA.family O).Cd)
    (hnotB : x ∈ (sideB.family O).Cc →
      x ∉ (sideB.family O).Cd) :
    sideA = sideB := by
  cases sideA with
  | ac =>
      cases sideB with
      | ac => rfl
      | bd =>
          exfalso
          apply hnotA (by
            simpa [DeformationSide.family, swapSides] using hxBCd)
          simpa [DeformationSide.family] using hxACd
  | bd =>
      cases sideB with
      | ac =>
          exfalso
          apply hnotB (by
            simpa [DeformationSide.family, swapSides] using hxACd)
          simpa [DeformationSide.family] using hxBCd
      | bd => rfl

namespace FiniteMixedSideLemma11AHistoryData

variable {D : ConcretePathDeformation O Cprime}
  {originalHole : IndexedInducedHole G}

/-- Backward transport through blocks `0, ..., n` of the bounded prefix. -/
theorem mem_firstInitial_of_mem_final_through
    (H : FiniteMixedSideLemma11AHistoryData D originalHole)
    {x : V} (n : Nat) (hn : n < H.priorCount)
    (hxFinal : x ∈ Set.range
      (H.priorBlock ⟨n, hn⟩).finalHole.vertex)
    (hne : ∀ r : Fin H.priorCount, r.val ≤ n →
      ∀ j : Fin (H.priorBlock r).deformation.stepCount,
        x ≠ ((H.priorBlock r).deformation.step j).introduced) :
    x ∈ Set.range
      (H.priorBlock ⟨0, H.priorCount_pos⟩).initialHole.vertex := by
  induction n with
  | zero =>
      let current : Fin H.priorCount := ⟨0, hn⟩
      have hxCurrentFinal :
          x ∈ Set.range (H.priorBlock current).finalHole.vertex := by
        simpa [current] using hxFinal
      have hxCurrentInitial :=
        (H.priorBlock current).mem_initialHole_of_mem_finalHole_of_ne_introduced
          hxCurrentFinal (hne current (by simp [current]))
      simpa [current] using hxCurrentInitial
  | succ n ih =>
      have hnPrevious : n < H.priorCount := by omega
      let previous : Fin H.priorCount := ⟨n, hnPrevious⟩
      let current : Fin H.priorCount := ⟨n + 1, hn⟩
      have hxCurrentFinal :
          x ∈ Set.range (H.priorBlock current).finalHole.vertex := by
        simpa [current] using hxFinal
      have hxCurrentInitial :
          x ∈ Set.range (H.priorBlock current).initialHole.vertex :=
        (H.priorBlock current).mem_initialHole_of_mem_finalHole_of_ne_introduced
          hxCurrentFinal (hne current (by simp [current]))
      have hxPreviousFinal :
          x ∈ Set.range (H.priorBlock previous).finalHole.vertex := by
        rw [H.priorChain (r := previous) (q := current) (by
          simp [previous, current])]
        exact hxCurrentInitial
      apply ih hnPrevious (by simpa [previous] using hxPreviousFinal)
      intro r hr j
      exact hne r (by omega) j

/-- The base common neighbour of a prior oriented block lies on the literal
original hole. -/
theorem priorBaseCommonNeighborOn
    (H : FiniteMixedSideLemma11AHistoryData D originalHole)
    (hclaw : G.IsClawFree)
    (r : Fin H.priorCount) :
    ((H.priorSide r).family O).BaseCommonNeighborOn
      (H.orientedPrior r) originalHole := by
  intro u hu
  let A := H.orientedPrior r
  obtain ⟨v, hvInitial, _hvFinal, huv, hjv, hkv, hvCb, hvNotPrime⟩ :=
    A.lemma11ai_commonNeighbor_currentBlock (H.priorData r) hclaw hu
  have hvCarrierInitial :
      v ∈ Set.range (H.priorBlock r).initialHole.vertex := by
    apply mem_initialHole_of_mem_reorient_initialHole
      (H.priorBlock r) (H.priorSide r)
    simpa [A, orientedPrior] using hvInitial
  have hvOriginal : v ∈ Set.range originalHole.vertex := by
    by_cases hr : r.val = 0
    · have hindex : r = ⟨0, H.priorCount_pos⟩ := by
        apply Fin.ext
        exact hr
      rw [hindex] at hvCarrierInitial
      rw [← H.firstInitial_eq_original]
      exact hvCarrierInitial
    · have hrPos : 0 < r.val := Nat.pos_of_ne_zero hr
      have hprevious : r.val - 1 < H.priorCount := by omega
      let previous : Fin H.priorCount := ⟨r.val - 1, hprevious⟩
      have hvPreviousFinal :
          v ∈ Set.range (H.priorBlock previous).finalHole.vertex := by
        rw [H.priorChain (r := previous) (q := r) (by
          simp [previous]
          omega)]
        exact hvCarrierInitial
      have hvFirst := H.mem_firstInitial_of_mem_final_through
        (r.val - 1) hprevious
        (by simpa [previous] using hvPreviousFinal) (by
          intro q _hq j hEq
          apply hvNotPrime
          rw [hEq]
          simpa [orientedPrior] using
            (H.priorData q).neighborhood.primeHole.introduced_mem j)
      rw [H.firstInitial_eq_original] at hvFirst
      exact hvFirst
  refine ⟨v, hvOriginal, huv, ?_, ?_, hvCb⟩
  · simpa [A, ConcretePathDeformation.firstIndex] using hjv
  · simpa [A, ConcretePathDeformation.firstIndex] using hkv

/-- The current oriented block's base common neighbour also lies on the
literal original hole preceding the bounded prefix. -/
theorem currentBaseCommonNeighborOn
    (H : FiniteMixedSideLemma11AHistoryData D originalHole)
    (hclaw : G.IsClawFree) :
    (H.currentSide.family O).BaseCommonNeighborOn
      (D.reorient H.currentSide) originalHole := by
  intro u hu
  let A := D.reorient H.currentSide
  obtain ⟨v, hvCurrentInitial, _hvFinal, huv, hjv, hkv,
      hvCb, hvNotPrime⟩ :=
    A.lemma11ai_commonNeighbor_currentBlock H.current hclaw hu
  have hvCarrierCurrentInitial : v ∈ Set.range D.initialHole.vertex := by
    apply mem_initialHole_of_mem_reorient_initialHole D H.currentSide
    simpa [A] using hvCurrentInitial
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
  · simpa [A, ConcretePathDeformation.firstIndex] using hjv
  · simpa [A, ConcretePathDeformation.firstIndex] using hkv

/-- A shared Definition 20 dependent vertex forces the prior and current
blocks to use the same manuscript component side. -/
theorem priorSide_eq_currentSide_of_sharedDependentVertex
    (H : FiniteMixedSideLemma11AHistoryData D originalHole)
    {r : Fin H.priorCount} {s t : Nat} {u : V}
    (huPrior : u ∈ (H.priorBlock r).dependentAt s)
    (huCurrent : u ∈ D.dependentAt t) :
    H.priorSide r = H.currentSide := by
  have huPriorPrime : u ∈ Cprime :=
    dependent_mem_prime_of_mem_dependentAt (H.priorBlock r) huPrior
  have huCurrentPrime : u ∈ Cprime :=
    dependent_mem_prime_of_mem_dependentAt D huCurrent
  have huPriorOriented : u ∈ (H.orientedPrior r).dependentAt s := by
    change u ∈
      ((H.priorBlock r).reorient (H.priorSide r)).dependentAt s
    rw [(H.priorBlock r).reorient_dependentAt (H.priorSide r) s]
    exact huPrior
  have huCurrentOriented :
      u ∈ (D.reorient H.currentSide).dependentAt t := by
    rw [D.reorient_dependentAt H.currentSide t]
    exact huCurrent
  have huPriorCd : u ∈ ((H.priorSide r).family O).Cd :=
    (H.priorData r).neighborhood.mechanical.dependent_mem_cd
      huPriorOriented
  have huCurrentCd : u ∈ (H.currentSide.family O).Cd :=
    H.current.neighborhood.mechanical.dependent_mem_cd
      huCurrentOriented
  have hnotPrior :
      u ∈ ((H.priorSide r).family O).Cc →
        u ∉ ((H.priorSide r).family O).Cd := by
    intro huCc
    exact
      ((H.priorData r).neighborhood.overlapColoring.not_mem_ca_cd_of_mem_cc
        huPriorPrime huCc).2
  have hnotCurrent :
      u ∈ (H.currentSide.family O).Cc →
        u ∉ (H.currentSide.family O).Cd := by
    intro huCc
    exact
      (H.current.neighborhood.overlapColoring.not_mem_ca_cd_of_mem_cc
        huCurrentPrime huCc).2
  exact side_eq_of_oriented_cd
    (H.priorSide r) H.currentSide
    huPriorCd huCurrentCd hnotPrior hnotCurrent

/-- A shared dependent anticommuting witness therefore compares two blocks
on the same manuscript component side. -/
theorem priorSide_eq_currentSide_of_sharedDependentAnticommutingWitness
    (H : FiniteMixedSideLemma11AHistoryData D originalHole)
    (r : Fin H.priorCount)
    (hshared : SharedDependentAnticommutingWitness
      (H.priorBlock r).path D.path
      (H.priorBlock r).dependentAt D.dependentAt) :
    H.priorSide r = H.currentSide := by
  rcases hshared with
    ⟨u, s, t, huPrior, huCurrent, _hantiPrior, _hantiCurrent⟩
  exact H.priorSide_eq_currentSide_of_sharedDependentVertex
    huPrior huCurrent

end FiniteMixedSideLemma11AHistoryData

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
