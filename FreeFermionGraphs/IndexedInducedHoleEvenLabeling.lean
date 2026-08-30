import FreeFermionGraphs.EvenHoleLabeling

/-!
# Alternating labels from an indexed even hole

An indexed induced hole of even cardinality canonically splits into its even
and odd cyclic positions.  This supplies the `EvenHoleLabeling` required by
the generalized-cycle arcs in Definition 18.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- Every even indexed induced hole admits an alternating labeling with
exactly the same vertex carrier. -/
theorem IndexedInducedHole.exists_evenHoleLabeling
    (C : IndexedInducedHole G) (hEven : Even C.card) :
    ∃ (k : Nat) (E : EvenHoleLabeling G k),
      E.carrier = Set.range C.vertex := by
  rcases hEven with ⟨k, hcard⟩
  have hcardTwo : C.card = 2 * k := by omega
  have hkTwo : 2 ≤ k := by
    have := C.four_le_card
    omega
  let aIndex : Fin k → Fin C.card := fun i =>
    ⟨2 * i.val, by omega⟩
  let bIndex : Fin k → Fin C.card := fun i =>
    ⟨2 * i.val + 1, by omega⟩
  let nextIndex : Fin k → Fin k := fun i =>
    if hi : i.val = 0 then ⟨k - 1, by omega⟩
    else ⟨i.val - 1, by omega⟩
  let prevIndex : Fin k → Fin k := fun i =>
    if hi : i.val + 1 < k then ⟨i.val + 1, hi⟩
    else ⟨0, by omega⟩
  let E : EvenHoleLabeling G k :=
    { two_le := hkTwo
      a := fun i => C.vertex (aIndex i)
      b := fun i => C.vertex (bIndex i)
      next := nextIndex
      prev := prevIndex
      next_ne := by
        intro i hEq
        have hval := congrArg Fin.val hEq
        by_cases hi : i.val = 0
        · simp [nextIndex, hi] at hval
          omega
        · simp [nextIndex, hi] at hval
          omega
      next_next_ne := by
        intro hkThree i hEq
        have hval := congrArg Fin.val hEq
        by_cases hi : i.val = 0
        · have hkpos : k - 1 ≠ 0 := by omega
          simp [nextIndex, hi, hkpos] at hval
          omega
        · by_cases hiOne : i.val = 1
          · simp [nextIndex, hiOne] at hval
            omega
          · have hpredNonzero : i.val - 1 ≠ 0 := by omega
            simp [nextIndex, hi, hpredNonzero] at hval
            omega
      next_prev := by
        intro i
        apply Fin.ext
        by_cases hnext : i.val + 1 < k
        · have hnonzero : i.val + 1 ≠ 0 := by omega
          simp [prevIndex, nextIndex, hnext]
        · have hiLast : i.val = k - 1 := by omega
          have hlastNotLt : ¬k - 1 + 1 < k := by omega
          simp [prevIndex, nextIndex, hiLast, hlastNotLt]
      prev_next := by
        intro i
        apply Fin.ext
        by_cases hi : i.val = 0
        · have hlastNotLt : ¬k - 1 + 1 < k := by omega
          simp [nextIndex, prevIndex, hi, hlastNotLt]
        · have hpredLt : i.val - 1 + 1 < k := by omega
          simp [nextIndex, prevIndex, hi, hpredLt]
          omega
      a_injective := by
        intro i j hij
        apply Fin.ext
        have hindex := C.injective hij
        have hval := congrArg Fin.val hindex
        dsimp [aIndex] at hval
        omega
      b_injective := by
        intro i j hij
        apply Fin.ext
        have hindex := C.injective hij
        have hval := congrArg Fin.val hindex
        dsimp [bIndex] at hval
        omega
      color_disjoint := by
        intro i j hij
        have hindex := C.injective hij
        have hval := congrArg Fin.val hindex
        dsimp [aIndex, bIndex] at hval
        omega
      adj_aa := by
        intro i j hij
        have hcyclic := (C.adj_iff (aIndex i) (aIndex j)).1 hij
        unfold CyclicAdjacent at hcyclic
        dsimp [aIndex] at hcyclic
        omega
      adj_bb := by
        intro i j hij
        have hcyclic := (C.adj_iff (bIndex i) (bIndex j)).1 hij
        unfold CyclicAdjacent at hcyclic
        dsimp [bIndex] at hcyclic
        omega
      adj_ab_iff := by
        intro i j
        rw [C.adj_iff]
        unfold CyclicAdjacent
        dsimp [aIndex, bIndex]
        constructor
        · rintro (hforward | hbackward | hwrap | hwrapImpossible)
          · left
            apply Fin.ext
            omega
          · right
            apply Fin.ext
            by_cases hi : i.val = 0
            · simp [nextIndex, hi]
              omega
            · simp [nextIndex, hi]
              omega
          · right
            apply Fin.ext
            have hi : i.val = 0 := by omega
            have hj : j.val = k - 1 := by omega
            simpa [nextIndex, hi] using hj
          · omega
        · rintro (rfl | hnext)
          · exact Or.inl rfl
          · have hval := congrArg Fin.val hnext
            by_cases hi : i.val = 0
            · have hjLast : j.val = k - 1 := by
                simpa [nextIndex, hi] using hval
              exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))
            · have hjPrevious : j.val = i.val - 1 := by
                simpa [nextIndex, hi] using hval
              exact Or.inr (Or.inl (by omega)) }
  refine ⟨k, E, ?_⟩
  ext v
  constructor
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨aIndex i, rfl⟩
    · exact ⟨bIndex i, rfl⟩
  · rintro ⟨q, rfl⟩
    rcases Nat.even_or_odd q.val with hqEven | hqOdd
    · rcases hqEven with ⟨t, ht⟩
      have htlt : t < k := by
        have hq := q.isLt
        omega
      left
      refine ⟨⟨t, htlt⟩, ?_⟩
      apply congrArg C.vertex
      apply Fin.ext
      dsimp [aIndex]
      omega
    · rcases hqOdd with ⟨t, ht⟩
      have htlt : t < k := by
        have hq := q.isLt
        omega
      right
      refine ⟨⟨t, htlt⟩, ?_⟩
      apply congrArg C.vertex
      apply Fin.ext
      dsimp [bIndex]
      omega

end SimpleGraph
