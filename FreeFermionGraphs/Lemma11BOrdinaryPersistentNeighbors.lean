import FreeFermionGraphs.Lemma11BAlternatingBPersistence

/-!
# Lemma 11(b): the persistent neighbors in the ordinary outside branch

The ordinary outside-path branch uses Lemma 8 twice.  At the current
replacement, adjacency to the preceding `a`-vertex selects the left arm and
forces the common `b`-vertex.  At the earlier replacement, adjacency to the
next `a`-vertex selects the right arm and forces the preceding common
`b`-vertex.

This module first records those two small consequences of Lemma 8.  They are
the local ingredients needed to construct the paper's four final neighbors.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace EvenHoleLabeling

/-- A fixed-point-free cyclic successor on three indices has order three. -/
theorem next_next_next_eq_of_three
    (C : EvenHoleLabeling G 3) (r : Fin 3) :
    C.next (C.next (C.next r)) = r := by
  apply Fin.ext
  have hr := r.isLt
  have h₁ := (C.next r).isLt
  have h₂ := (C.next (C.next r)).isLt
  have h₃ := (C.next (C.next (C.next r))).isLt
  have h₁r : (C.next r).val ≠ r.val := by
    intro h
    exact C.next_ne r (Fin.ext h)
  have h₂r : (C.next (C.next r)).val ≠ r.val := by
    intro h
    exact C.next_next_ne (by omega) r (Fin.ext h)
  have h₂₁ :
      (C.next (C.next r)).val ≠ (C.next r).val := by
    intro h
    exact C.next_ne (C.next r) (Fin.ext h)
  have h₃₂ :
      (C.next (C.next (C.next r))).val ≠
        (C.next (C.next r)).val := by
    intro h
    exact C.next_ne (C.next (C.next r)) (Fin.ext h)
  have h₃₁ :
      (C.next (C.next (C.next r))).val ≠
        (C.next r).val := by
    intro h
    exact C.next_next_ne (by omega) (C.next r) (Fin.ext h)
  omega

/-- If a vertex distinguishes a clone from its original and also neighbors
the preceding `a`-vertex, Lemma 8 must choose its left arm. -/
theorem CloneAt.adj_b_of_adj_clone_of_not_adj_original_of_adj_prev
    {k : Nat} {C : EvenHoleLabeling G k}
    {clone t : V} {i : Fin k}
    (h : C.CloneAt clone i)
    (hclaw : G.IsClawFree)
    (htOutside : t ∉ Set.insert clone C.carrier)
    (htClone : G.Adj t clone)
    (htOriginal : ¬G.Adj t (C.a i))
    (hk : 2 < k)
    (htPrev : G.Adj t (C.a (C.prev i))) :
    G.Adj t (C.b i) := by
  obtain ⟨chosen, hchoice, hchosen, hside⟩ :=
    h.dependent_neighbor_restriction hclaw htOutside
      (Or.inl ⟨htClone, htOriginal⟩)
  rcases hside with hleft | hright
  · exact hleft.1
  · rcases hright with ⟨_htB, _htNext, hrestrict⟩
    have hprevMem :
        C.a (C.prev i) ∈ Set.insert clone C.carrier :=
      Set.mem_insert_iff.2
        (Or.inr (C.a_mem_carrier (C.prev i)))
    have hprevChosen : C.a (C.prev i) ≠ chosen := by
      rcases hchoice with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · intro heq
        exact h.outside
          (heq.symm ▸ C.a_mem_carrier (C.prev i))
      · exact C.a_ne_prev i
    have hprevB :
        C.a (C.prev i) ≠ C.b (C.next i) :=
      C.color_disjoint (C.prev i) (C.next i)
    have hprevNext :
        C.a (C.prev i) ≠ C.a (C.next i) := by
      intro heq
      exact C.prev_ne_next hk i (C.a_injective heq)
    rcases hrestrict (C.a (C.prev i)) hprevMem htPrev
        hprevChosen hprevB hprevNext with hbad | hbad
    · exact (C.color_disjoint (C.prev i) i hbad).elim
    · exact
        (C.color_disjoint
          (C.prev i) (C.next (C.next i)) hbad).elim

/-- Symmetrically, adjacency to the next `a`-vertex selects Lemma 8's right
arm when the original, rather than its clone, is adjacent. -/
theorem CloneAt.adj_b_next_of_not_adj_clone_of_adj_original_of_adj_next
    {k : Nat} {C : EvenHoleLabeling G k}
    {clone t : V} {i : Fin k}
    (h : C.CloneAt clone i)
    (hclaw : G.IsClawFree)
    (htOutside : t ∉ Set.insert clone C.carrier)
    (htClone : ¬G.Adj t clone)
    (htOriginal : G.Adj t (C.a i))
    (hk : 2 < k)
    (htNext : G.Adj t (C.a (C.next i))) :
    G.Adj t (C.b (C.next i)) := by
  obtain ⟨chosen, hchoice, hchosen, hside⟩ :=
    h.dependent_neighbor_restriction hclaw htOutside
      (Or.inr ⟨htClone, htOriginal⟩)
  rcases hside with hleft | hright
  · rcases hleft with ⟨_htB, _htPrev, hrestrict⟩
    have hnextMem :
        C.a (C.next i) ∈ Set.insert clone C.carrier :=
      Set.mem_insert_iff.2
        (Or.inr (C.a_mem_carrier (C.next i)))
    have hnextChosen : C.a (C.next i) ≠ chosen := by
      rcases hchoice with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · intro heq
        exact h.outside
          (heq.symm ▸ C.a_mem_carrier (C.next i))
      · exact C.a_ne_next i
    have hnextB : C.a (C.next i) ≠ C.b i :=
      C.color_disjoint (C.next i) i
    have hnextPrev :
        C.a (C.next i) ≠ C.a (C.prev i) := by
      intro heq
      exact C.prev_ne_next hk i (C.a_injective heq).symm
    rcases hrestrict (C.a (C.next i)) hnextMem htNext
        hnextChosen hnextB hnextPrev with hbad | hbad
    · exact (C.color_disjoint (C.next i) (C.prev i) hbad).elim
    · exact (C.color_disjoint (C.next i) (C.next i) hbad).elim
  · exact hright.1

end EvenHoleLabeling

namespace IndexedInducedHole

/-- Four named, pairwise distinct vertices on a hole give the indexed
four-neighbor certificate used by the concrete degree theorem. -/
theorem hasFourDistinctExternalNeighbors_of_named
    (C : IndexedInducedHole G)
    {u v₀ v₁ v₂ v₃ : V}
    (huOutside : u ∉ Set.range C.vertex)
    (hv₀ : v₀ ∈ Set.range C.vertex)
    (hv₁ : v₁ ∈ Set.range C.vertex)
    (hv₂ : v₂ ∈ Set.range C.vertex)
    (hv₃ : v₃ ∈ Set.range C.vertex)
    (h₀₁ : v₀ ≠ v₁) (h₀₂ : v₀ ≠ v₂) (h₀₃ : v₀ ≠ v₃)
    (h₁₂ : v₁ ≠ v₂) (h₁₃ : v₁ ≠ v₃) (h₂₃ : v₂ ≠ v₃)
    (hu₀ : G.Adj u v₀) (hu₁ : G.Adj u v₁)
    (hu₂ : G.Adj u v₂) (hu₃ : G.Adj u v₃) :
    C.HasFourDistinctExternalNeighbors u := by
  obtain ⟨p, hp⟩ := hv₀
  obtain ⟨q, hq⟩ := hv₁
  obtain ⟨r, hr⟩ := hv₂
  obtain ⟨s, hs⟩ := hv₃
  refine ⟨huOutside, p, q, r, s, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hpq
    apply h₀₁
    calc
      v₀ = C.vertex p := hp.symm
      _ = C.vertex q := congrArg C.vertex hpq
      _ = v₁ := hq
  · intro hpr
    apply h₀₂
    calc
      v₀ = C.vertex p := hp.symm
      _ = C.vertex r := congrArg C.vertex hpr
      _ = v₂ := hr
  · intro hps
    apply h₀₃
    calc
      v₀ = C.vertex p := hp.symm
      _ = C.vertex s := congrArg C.vertex hps
      _ = v₃ := hs
  · intro hqr
    apply h₁₂
    calc
      v₁ = C.vertex q := hq.symm
      _ = C.vertex r := congrArg C.vertex hqr
      _ = v₂ := hr
  · intro hqs
    apply h₁₃
    calc
      v₁ = C.vertex q := hq.symm
      _ = C.vertex s := congrArg C.vertex hqs
      _ = v₃ := hs
  · intro hrs
    apply h₂₃
    calc
      v₂ = C.vertex r := hr.symm
      _ = C.vertex s := congrArg C.vertex hrs
      _ = v₃ := hs
  · simpa [hp] using hu₀
  · simpa [hq] using hu₁
  · simpa [hr] using hu₂
  · simpa [hs] using hu₃

end IndexedInducedHole

namespace FixedPairingPathFamily

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

namespace ConcretePathDeformation

/-- Three consecutive deformation steps cannot occur on a four-cycle.  On
two alternating indices, the third removed coordinate would be the first
coordinate again, so the third removed vertex would equal the first clone,
contrary to Definition 19's injective path order. -/
theorem two_lt_halfLength_of_three_consecutive_steps
    {k : Nat} {D : ConcretePathDeformation O Cprime}
    (A : D.AlternatingLabelingSequence k)
    (L : Definition19GlobalOverlapPathOrder D)
    {earlier previous current : Fin D.deformation.stepCount}
    (hep : earlier.val + 1 = previous.val)
    (hpc : previous.val + 1 = current.val) :
    2 < k := by
  by_contra hk
  have hkTwo : k = 2 := by
    have htwo := (A.labeling earlier).two_le
    omega
  subst k
  let C0 : EvenHoleLabeling G 2 := A.labeling earlier
  let r0 : Fin 2 := A.removedAIndex earlier
  have hrPrevious :
      A.removedAIndex previous = C0.next r0 := by
    simpa [C0, r0] using A.removed_index_next hep
  have hrCurrent :
      A.removedAIndex current = r0 := by
    have h := A.removed_index_next hpc
    rw [A.transport_eq hep] at h
    rw [hrPrevious] at h
    calc
      A.removedAIndex current = C0.next (C0.next r0) := by
        simpa [C0, r0] using h
      _ = r0 := C0.next_next_eq_of_two r0
  have hpreviousAt :
      (A.labeling previous).a r0 =
        (D.deformation.step earlier).introduced := by
    rw [A.transport_eq hep]
    simpa [C0, r0] using
      (EvenHoleLabeling.deform_a_at
        (A.labeling earlier) (A.cloneAt earlier))
  have hcurrentAt :
      (A.labeling current).a r0 =
        (A.labeling previous).a r0 := by
    rw [A.transport_eq hpc]
    apply EvenHoleLabeling.deform_a_away
    intro heq
    have : r0 = C0.next r0 := by
      simpa [hrPrevious] using heq
    exact C0.next_ne r0 this.symm
  have hbad :
      (D.deformation.step earlier).introduced =
        (D.deformation.step current).before.vertex
          (D.deformation.step current).removedIndex := by
    calc
      (D.deformation.step earlier).introduced =
          (A.labeling previous).a r0 := hpreviousAt.symm
      _ = (A.labeling current).a r0 := hcurrentAt.symm
      _ = (A.labeling current).a
          (A.removedAIndex current) := by rw [hrCurrent]
      _ = (D.deformation.step current).before.vertex
          (D.deformation.step current).removedIndex :=
        (A.removed_eq current).symm
  exact
    (D.introduced_ne_later_removed L earlier current (by omega)) hbad

/-- At the current replacement, adjacency to the preceding clone selects
the left Lemma 8 arm and hence the paper's common vertex `w_(s-1)`. -/
theorem adj_next_b_of_adj_previous_introduced
    {k : Nat} (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (A : D.AlternatingLabelingSequence k)
    (hclaw : G.IsClawFree)
    (hk : 2 < k)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (previous : Fin D.deformation.stepCount)
    (hprevious : previous.val + 1 = s)
    (huPreviousIntroduced :
      G.Adj u (D.deformation.step previous).introduced) :
    G.Adj u
      ((A.labeling previous).b
        ((A.labeling previous).next
          (A.removedAIndex previous))) := by
  have hs : s < D.deformation.stepCount :=
    D.index_lt_of_mem_dependentAt hu
  let current : Fin D.deformation.stepCount := ⟨s, hs⟩
  have hij : previous.val + 1 = current.val := by
    simpa [current] using hprevious
  let C : EvenHoleLabeling G k := A.labeling previous
  let r : Fin k := A.removedAIndex previous
  let hpreviousClone := A.cloneAt previous
  let C1 : EvenHoleLabeling G k := C.deform hpreviousClone
  have hcurrent :
      C1.CloneAt
        (D.deformation.step current).introduced
        (C1.next r) := by
    have h := A.cloneAt current
    rw [A.transport_eq hij] at h
    rw [A.removed_index_next hij] at h
    simpa [C, C1, r, hpreviousClone] using h
  have hcarrierCurrent :
      C1.carrier =
        Set.range (D.deformation.step current).before.vertex := by
    calc
      C1.carrier = (A.labeling current).carrier := by
        rw [A.transport_eq hij]
      _ = _ := A.carrier_eq current
  have huStep :
      u ∈ (D.deformation.step current).dependentSet := by
    simpa [current] using
      D.mem_step_dependentSet_of_mem_dependentAt hu
  have hmem :=
    (ConcreteDeformationStep.mem_dependentSet
      (D.deformation.step current)).1 huStep
  have huOutsideCurrent :
      u ∉ Set.insert (D.deformation.step current).introduced
        C1.carrier := by
    rw [hcarrierCurrent]
    exact M.outsideHole current huStep
  have huNotCurrentOriginal :
      ¬G.Adj u (C1.a (C1.next r)) := by
    have hnot :
        ¬G.Adj u
          ((A.labeling current).a
            (A.removedAIndex current)) := by
      rw [← A.removed_eq current]
      exact hmem.2.2.2
    rw [A.transport_eq hij] at hnot
    rw [A.removed_index_next hij] at hnot
    simpa [C, C1, r, hpreviousClone] using hnot
  have huPreviousA :
      G.Adj u (C1.a (C1.prev (C1.next r))) := by
    rw [C1.prev_next r]
    simpa [C, C1, r, hpreviousClone] using
      huPreviousIntroduced
  have huB :=
    hcurrent.adj_b_of_adj_clone_of_not_adj_original_of_adj_prev
      hclaw huOutsideCurrent hmem.2.1 huNotCurrentOriginal
      hk huPreviousA
  simpa [C, C1, r, hpreviousClone] using huB

/-- The exact four-vertex active-path block identifies the preceding
replacement: `u` neighbors its removed vertex and misses its clone. -/
theorem earlier_original_adj_and_clone_not_adj_of_adj_previous_introduced
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    (horder : Definition19PathOrder M)
    (hopposite : D.BaseOppositeEndpointNonadjacency)
    {s t : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huOutside : u ∉ Set.range D.path.vertex)
    (hnotAnti : ¬D.path.AnticommutesWith u)
    (ht : t < D.deformation.stepCount)
    (hts : Nat.succ t = s)
    (huPreviousIntroduced :
      G.Adj u (D.deformation.step ⟨t, ht⟩).introduced) :
    ∃ earlier : Fin D.deformation.stepCount,
      earlier.val + 1 = t ∧
      G.Adj u
        ((D.deformation.step earlier).before.vertex
          (D.deformation.step earlier).removedIndex) ∧
      ¬G.Adj u (D.deformation.step earlier).introduced := by
  obtain ⟨hsTwo, x, hx, hux, hfour⟩ :=
    D.four_path_neighbor_block_of_adj_previous_introduced
      M L hclaw horder hopposite
      hu huOutside hnotAnti ht hts huPreviousIntroduced
  have hs : s < D.deformation.stepCount :=
    D.index_lt_of_mem_dependentAt hu
  have htPos : 0 < t := by omega
  let earlier : Fin D.deformation.stepCount :=
    ⟨t - 1, by omega⟩
  let previous : Fin D.deformation.stepCount := ⟨t, ht⟩
  let current : Fin D.deformation.stepCount := ⟨s, hs⟩
  have hep : earlier.val + 1 = previous.val := by
    dsimp [earlier, previous]
    omega
  let a : Fin D.path.card := L.introducedPathIndex previous
  let b : Fin D.path.card := L.removedPathIndex previous
  let c : Fin D.path.card := L.introducedPathIndex current
  let y : Fin D.path.card := L.introducedPathIndex earlier
  have hxval : x.val + 1 = a.val := by
    simpa [a, previous] using hx
  have haval : a.val = 2 * t := by
    simpa [a, previous] using L.introduced_index_val previous
  have hbval : b.val = 2 * t + 1 := by
    simpa [b, previous] using L.removed_index_val previous
  have hcval : c.val = 2 * s := by
    simpa [c, current] using L.introduced_index_val current
  have hyval : y.val = 2 * (t - 1) := by
    simpa [y, earlier] using L.introduced_index_val earlier
  have hxa : x ≠ a := by
    intro h
    have hval := congrArg Fin.val h
    omega
  have hxb : x ≠ b := by
    intro h
    have hval := congrArg Fin.val h
    omega
  have hxc : x ≠ c := by
    intro h
    have hval := congrArg Fin.val h
    omega
  have hab : a ≠ b := by
    intro h
    have hval := congrArg Fin.val h
    omega
  have hac : a ≠ c := by
    intro h
    have hval := congrArg Fin.val h
    omega
  have hbc : b ≠ c := by
    intro h
    have hval := congrArg Fin.val h
    omega
  have hua : G.Adj u (D.path.vertex a) := by
    rw [L.introduced_eq previous]
    simpa [previous] using huPreviousIntroduced
  obtain ⟨t', ht', ht's, huPreviousRemoved'⟩ :=
    D.adj_previous_removed_of_outside_commuting
      M L hclaw horder hopposite hu huOutside hnotAnti
  have htt : t' = t := by omega
  have hpreviousFin :
      (⟨t', ht'⟩ : Fin D.deformation.stepCount) = previous := by
    apply Fin.ext
    simpa [previous] using htt
  have hub : G.Adj u (D.path.vertex b) := by
    rw [L.removed_eq previous]
    rw [hpreviousFin] at huPreviousRemoved'
    exact huPreviousRemoved'
  have huStep :
      u ∈ (D.deformation.step current).dependentSet := by
    simpa [current] using
      D.mem_step_dependentSet_of_mem_dependentAt hu
  have hmem :=
    (ConcreteDeformationStep.mem_dependentSet
      (D.deformation.step current)).1 huStep
  have huc : G.Adj u (D.path.vertex c) := by
    rw [L.introduced_eq current]
    exact hmem.2.1
  let known : Set (Fin D.path.card) := {x, a, b, c}
  have hknownSubset :
      known ⊆ D.path.neighborIndexSet u := by
    intro z hz
    simp only [known, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact hux
    · exact hua
    · exact hub
    · exact huc
  have hknownCard : known.ncard = 4 := by
    apply Set.ncard_eq_four.mpr
    exact
      ⟨x, a, b, c, hxa, hxb, hxc,
        hab, hac, hbc, rfl⟩
  have hyNotKnown : y ∉ known := by
    simp only [known, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    intro hy
    rcases hy with hyx | hya | hyb | hyc
    · have hval := congrArg Fin.val hyx
      omega
    · have hval := congrArg Fin.val hya
      omega
    · have hval := congrArg Fin.val hyb
      omega
    · have hval := congrArg Fin.val hyc
      omega
  have huyNot : ¬G.Adj u (D.path.vertex y) := by
    intro huy
    have hinsertSubset :
        Set.insert y known ⊆ D.path.neighborIndexSet u := by
      intro z hz
      rcases Set.mem_insert_iff.1 hz with rfl | hz
      · exact huy
      · exact hknownSubset hz
    have hinsertCard : (Set.insert y known).ncard = 5 := by
      calc
        (Set.insert y known).ncard = known.ncard + 1 :=
          Set.ncard_insert_of_notMem hyNotKnown
        _ = 4 + 1 := by rw [hknownCard]
        _ = 5 := by omega
    have hle := Set.ncard_le_ncard hinsertSubset
    rw [hinsertCard, hfour] at hle
    omega
  have hxEarlierRemoved :
      x = L.removedPathIndex earlier := by
    have hremovedLeft :
        (L.removedPathIndex earlier).val + 1 = a.val := by
      have hremovedVal := L.removed_index_val earlier
      have hintroducedVal :
          a.val = 2 * previous.val := by
        simpa [a] using L.introduced_index_val previous
      omega
    apply Fin.ext
    omega
  refine ⟨earlier, by dsimp [earlier]; omega, ?_, ?_⟩
  · rw [← L.removed_eq earlier, ← hxEarlierRemoved]
    exact hux
  · rw [← L.introduced_eq earlier]
    simpa [y] using huyNot

/-- Applying the right-arm selector at the earlier replacement yields the
preceding persistent common vertex `w_(s-2)`, expressed in the transported
labeling of the following step. -/
theorem adj_removed_b_of_earlier_original_not_clone
    {k : Nat} (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (A : D.AlternatingLabelingSequence k)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    (hcolors : O.PrimeCarrierExactlyColored Cprime)
    (hk : 2 < k)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huOutside : u ∉ Set.range D.path.vertex)
    (earlier previous : Fin D.deformation.stepCount)
    (hep : earlier.val + 1 = previous.val)
    (huEarlierOriginal :
      G.Adj u
        ((D.deformation.step earlier).before.vertex
          (D.deformation.step earlier).removedIndex))
    (huNotEarlierClone :
      ¬G.Adj u (D.deformation.step earlier).introduced)
    (huPreviousOriginal :
      G.Adj u
        ((D.deformation.step previous).before.vertex
          (D.deformation.step previous).removedIndex)) :
    G.Adj u
      ((A.labeling previous).b
        (A.removedAIndex previous)) := by
  let C0 : EvenHoleLabeling G k := A.labeling earlier
  let r0 : Fin k := A.removedAIndex earlier
  let hearlierClone := A.cloneAt earlier
  have huExact :
      ExactlyOneOfFour u O.Ca O.Cb O.Cc O.Cd :=
    M.dependent_exactlyOne hcolors hu
  have huCd : u ∈ O.Cd := M.dependent_mem_cd hu
  have huNotFirstThree :
      u ∉ O.Ca ∧ u ∉ O.Cb ∧ u ∉ O.Cc :=
    huExact.not_mem_first_three_of_mem_fourth huCd
  have huOutsideEarlier :
      u ∉ Set.insert (D.deformation.step earlier).introduced
        C0.carrier := by
    intro huInsert
    rcases Set.mem_insert_iff.1 huInsert with huClone | huCarrier
    · apply huOutside
      refine ⟨L.introducedPathIndex earlier, ?_⟩
      exact (L.introduced_eq earlier).trans huClone.symm
    · have huBefore :
          u ∈ Set.range
            (D.deformation.step earlier).before.vertex := by
        rw [← A.carrier_eq earlier]
        exact huCarrier
      rcases (M.stepGeometry earlier).before_subset huBefore with
        huCa | huCb
      · exact huNotFirstThree.1 huCa
      · exact huNotFirstThree.2.1 huCb
  have huEarlierA : G.Adj u (C0.a r0) := by
    rw [← A.removed_eq earlier]
    simpa [C0, r0] using huEarlierOriginal
  have huNextA : G.Adj u (C0.a (C0.next r0)) := by
    have hrPrevious := A.removed_index_next hep
    have hremoved := A.removed_eq previous
    rw [A.transport_eq hep] at hremoved
    rw [hrPrevious] at hremoved
    have hnextAway : C0.next r0 ≠ r0 := C0.next_ne r0
    have hEq :
        (D.deformation.step previous).before.vertex
            (D.deformation.step previous).removedIndex =
          C0.a (C0.next r0) := by
      simpa [C0, r0, hearlierClone, hnextAway] using hremoved
    rw [← hEq]
    exact huPreviousOriginal
  have huB :=
    hearlierClone.adj_b_next_of_not_adj_clone_of_adj_original_of_adj_next
      hclaw huOutsideEarlier huNotEarlierClone huEarlierA hk huNextA
  have hrPrevious := A.removed_index_next hep
  rw [A.transport_eq hep]
  rw [hrPrevious]
  simpa [C0, r0, hearlierClone] using huB

/-- The ordinary outside branch has both persistent common `b`-neighbors
from the paper, written in the labeling immediately before the preceding
replacement. -/
theorem adj_two_persistent_b_of_adj_previous_introduced
    {k : Nat} (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (A : D.AlternatingLabelingSequence k)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    (hcolors : O.PrimeCarrierExactlyColored Cprime)
    (horder : Definition19PathOrder M)
    (hopposite : D.BaseOppositeEndpointNonadjacency)
    {s t : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huOutside : u ∉ Set.range D.path.vertex)
    (hnotAnti : ¬D.path.AnticommutesWith u)
    (ht : t < D.deformation.stepCount)
    (hts : Nat.succ t = s)
    (huPreviousIntroduced :
      G.Adj u (D.deformation.step ⟨t, ht⟩).introduced) :
    G.Adj u
        ((A.labeling ⟨t, ht⟩).b
          (A.removedAIndex ⟨t, ht⟩)) ∧
      G.Adj u
        ((A.labeling ⟨t, ht⟩).b
          ((A.labeling ⟨t, ht⟩).next
            (A.removedAIndex ⟨t, ht⟩))) := by
  have hs : s < D.deformation.stepCount :=
    D.index_lt_of_mem_dependentAt hu
  let previous : Fin D.deformation.stepCount := ⟨t, ht⟩
  let current : Fin D.deformation.stepCount := ⟨s, hs⟩
  obtain
      ⟨earlier, hearlier, huEarlierOriginal,
        huNotEarlierClone⟩ :=
    D.earlier_original_adj_and_clone_not_adj_of_adj_previous_introduced
      M L hclaw horder hopposite
      hu huOutside hnotAnti ht hts huPreviousIntroduced
  have hep : earlier.val + 1 = previous.val := by
    simpa [previous] using hearlier
  have hpc : previous.val + 1 = current.val := by
    dsimp [previous, current]
    omega
  have hk : 2 < k :=
    D.two_lt_halfLength_of_three_consecutive_steps
      A L hep hpc
  obtain ⟨t', ht', ht's, huPreviousOriginal'⟩ :=
    D.adj_previous_removed_of_outside_commuting
      M L hclaw horder hopposite hu huOutside hnotAnti
  have htt : t' = t := by omega
  have hpreviousFin :
      (⟨t', ht'⟩ : Fin D.deformation.stepCount) = previous := by
    apply Fin.ext
    simpa [previous] using htt
  have huPreviousOriginal :
      G.Adj u
        ((D.deformation.step previous).before.vertex
          (D.deformation.step previous).removedIndex) := by
    rw [← hpreviousFin]
    exact huPreviousOriginal'
  have huFirst :=
    D.adj_removed_b_of_earlier_original_not_clone
      M A L hclaw hcolors hk hu huOutside
      earlier previous hep huEarlierOriginal
      huNotEarlierClone huPreviousOriginal
  have huSecond :=
    D.adj_next_b_of_adj_previous_introduced
      M A hclaw hk hu previous
      (by simpa [previous] using hts) (by
        simpa [previous] using huPreviousIntroduced)
  simpa [previous] using And.intro huFirst huSecond

/-- The two persistent `b`-vertices and the two consecutive introduced
vertices are four distinct neighbors on the final hole. -/
theorem finalFourNeighbors_of_adj_previous_introduced
    {k : Nat} (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (A : D.AlternatingLabelingSequence k)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    (hcolors : O.PrimeCarrierExactlyColored Cprime)
    (horder : Definition19PathOrder M)
    (hopposite : D.BaseOppositeEndpointNonadjacency)
    {s t : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huOutside : u ∉ Set.range D.path.vertex)
    (hnotAnti : ¬D.path.AnticommutesWith u)
    (ht : t < D.deformation.stepCount)
    (hts : Nat.succ t = s)
    (huPreviousIntroduced :
      G.Adj u (D.deformation.step ⟨t, ht⟩).introduced) :
    D.finalHole.HasFourDistinctExternalNeighbors u := by
  have hs : s < D.deformation.stepCount :=
    D.index_lt_of_mem_dependentAt hu
  let previous : Fin D.deformation.stepCount := ⟨t, ht⟩
  let current : Fin D.deformation.stepCount := ⟨s, hs⟩
  let C : EvenHoleLabeling G k := A.labeling previous
  let r : Fin k := A.removedAIndex previous
  have hpc : previous.val + 1 = current.val := by
    dsimp [previous, current]
    omega
  have huB :=
    D.adj_two_persistent_b_of_adj_previous_introduced
      M A L hclaw hcolors horder hopposite
      hu huOutside hnotAnti ht hts huPreviousIntroduced
  have huB₀ : G.Adj u (C.b r) := by
    simpa [C, r, previous] using huB.1
  have huB₁ : G.Adj u (C.b (C.next r)) := by
    simpa [C, r, previous] using huB.2
  have huStep :
      u ∈ (D.deformation.step current).dependentSet := by
    simpa [current] using
      D.mem_step_dependentSet_of_mem_dependentAt hu
  have hmem :=
    (ConcreteDeformationStep.mem_dependentSet
      (D.deformation.step current)).1 huStep
  have huCurrentIntroduced :
      G.Adj u (D.deformation.step current).introduced :=
    hmem.2.1
  have huPreviousIntroduced' :
      G.Adj u (D.deformation.step previous).introduced := by
    simpa [previous] using huPreviousIntroduced
  have hb₀Final : C.b r ∈ Set.range D.finalHole.vertex := by
    simpa [C, r] using A.b_mem_finalHole previous r
  have hb₁Final :
      C.b (C.next r) ∈ Set.range D.finalHole.vertex := by
    simpa [C, r] using A.b_mem_finalHole previous (C.next r)
  have hpreviousFinal :
      (D.deformation.step previous).introduced ∈
        Set.range D.finalHole.vertex :=
    D.introduced_mem_finalHole L previous
  have hcurrentFinal :
      (D.deformation.step current).introduced ∈
        Set.range D.finalHole.vertex :=
    D.introduced_mem_finalHole L current
  have huFinal : u ∉ Set.range D.finalHole.vertex :=
    M.dependent_not_mem_finalHole hcolors hu
  have hb₀Previous :
      C.b r ≠ (D.deformation.step previous).introduced := by
    intro hEq
    apply (A.cloneAt previous).outside
    rw [← hEq]
    simpa [C, r] using C.b_mem_carrier r
  have hb₁Previous :
      C.b (C.next r) ≠
        (D.deformation.step previous).introduced := by
    intro hEq
    apply (A.cloneAt previous).outside
    rw [← hEq]
    simpa [C, r] using C.b_mem_carrier (C.next r)
  have hb₀b₁ : C.b r ≠ C.b (C.next r) := by
    intro hEq
    exact C.next_ne r (C.b_injective hEq).symm
  have hpreviousCurrent :
      (D.deformation.step previous).introduced ≠
        (D.deformation.step current).introduced :=
    D.introduced_ne_later_introduced
      L previous current (by omega)
  have hbCurrent :
      ∀ q : Fin k,
        C.b q ≠ (D.deformation.step current).introduced := by
    intro q hEq
    have hbEq :
        (A.labeling current).b q = C.b q := by
      simpa [C] using A.b_eq_later previous current (by omega) q
    apply (A.cloneAt current).outside
    have hmemB := (A.labeling current).b_mem_carrier q
    rw [hbEq, hEq] at hmemB
    exact hmemB
  exact
    D.finalHole.hasFourDistinctExternalNeighbors_of_named
      huFinal hb₀Final hpreviousFinal hb₁Final hcurrentFinal
      hb₀Previous hb₀b₁ (hbCurrent r)
      hb₁Previous.symm hpreviousCurrent (hbCurrent (C.next r))
      huB₀ huPreviousIntroduced' huB₁ huCurrentIntroduced

/-- Consequently, the ordinary outside-path branch has degree four in the
final deformed hole. -/
theorem finalDegree_eq_four_of_adj_previous_introduced
    {k : Nat} (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (A : D.AlternatingLabelingSequence k)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    (hInitialEven : Even D.initialHole.card)
    (hcolors : O.PrimeCarrierExactlyColored Cprime)
    (horder : Definition19PathOrder M)
    (hopposite : D.BaseOppositeEndpointNonadjacency)
    {s t : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huOutside : u ∉ Set.range D.path.vertex)
    (hnotAnti : ¬D.path.AnticommutesWith u)
    (ht : t < D.deformation.stepCount)
    (hts : Nat.succ t = s)
    (huPreviousIntroduced :
      G.Adj u (D.deformation.step ⟨t, ht⟩).introduced) :
    D.finalDegree s u = 4 := by
  exact
    D.finalDegree_eq_four_of_hasFourDistinctExternalNeighbors
      hclaw (D.finalHole_even_of_initialHole_even hInitialEven)
      (D.finalFourNeighbors_of_adj_previous_introduced
        M A L hclaw hcolors horder hopposite
        hu huOutside hnotAnti ht hts huPreviousIntroduced)

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
