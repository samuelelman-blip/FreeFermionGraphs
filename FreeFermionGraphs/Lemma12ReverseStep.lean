import FreeFermionGraphs.Lemma13

/-!
# Reverse steps for Lemma 12

The palindromic deformation in Lemma 12 traverses the Definition 19 steps
in reverse order.  This module supplies the two elementary facts used by
that construction:

* an indexed single-vertex deformation is reversible at the same index;
* performing the same swap in two carriers preserves their symmetric
  difference.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

open scoped symmDiff

variable {G : SimpleGraph V}

namespace IndexedInducedHole

/-- The removed vertex is a clone of the introduced vertex in the deformed
hole.  Thus a concrete single-vertex deformation can be traversed in reverse
at the same cyclic index. -/
theorem SingleVertexDeformation.reverse
    {C : IndexedInducedHole G} {s : V} {i : Fin C.card}
    (h : C.SingleVertexDeformation s i) :
    (C.deform h).SingleVertexDeformation (C.vertex i) i := by
  constructor
  · exact C.removed_vertex_not_mem_deform h
  · intro q
    by_cases hqi : q = i
    · subst q
      constructor
      · intro _
        exact Or.inl rfl
      · intro _
        simpa using h.adj_clone.symm
    · have haway : (C.deform h).vertex q = C.vertex q :=
        C.deform_vertex_away h hqi
      have hat : (C.deform h).vertex i = s :=
        C.deform_vertex_at h
      rw [haway, hat]
      constructor
      · intro hadj
        exact Or.inr ((h.adj_iff q).2 (Or.inr hadj))
      · rintro (hEq | hadj)
        · exact (hqi hEq).elim
        · exact ((h.adj_iff q).1 hadj).resolve_left hqi

/-- Reversing a single deformation restores the original carrier. -/
theorem SingleVertexDeformation.reverse_deform_range_eq
    {C : IndexedInducedHole G} {s : V} {i : Fin C.card}
    (h : C.SingleVertexDeformation s i) :
    Set.range ((C.deform h).deform h.reverse).vertex =
      Set.range C.vertex := by
  apply congrArg Set.range
  funext q
  by_cases hqi : q = i
  · subst q
    simp
  · rw [(C.deform h).deform_vertex_away h.reverse hqi,
      C.deform_vertex_away h hqi]

/-- A vertex other than the introduced clone which lies on the deformed
hole already lay on the original hole. -/
theorem SingleVertexDeformation.mem_original_of_mem_deform_of_ne_introduced
    {C : IndexedInducedHole G} {s x : V} {i : Fin C.card}
    (h : C.SingleVertexDeformation s i)
    (hx : x ∈ Set.range (C.deform h).vertex)
    (hxs : x ≠ s) :
    x ∈ Set.range C.vertex := by
  obtain ⟨q, hqx⟩ := hx
  by_cases hqi : q = i
  · subst q
    exact (hxs (by simpa using hqx.symm)).elim
  · refine ⟨q, ?_⟩
    calc
      C.vertex q = (C.deform h).vertex q :=
        (C.deform_vertex_away h hqi).symm
      _ = x := hqx

/-- An original-hole vertex other than the removed vertex remains on the
deformed hole. -/
theorem SingleVertexDeformation.mem_deform_of_mem_original_of_ne_removed
    {C : IndexedInducedHole G} {s x : V} {i : Fin C.card}
    (h : C.SingleVertexDeformation s i)
    (hx : x ∈ Set.range C.vertex)
    (hxi : x ≠ C.vertex i) :
    x ∈ Set.range (C.deform h).vertex := by
  obtain ⟨q, hqx⟩ := hx
  have hqi : q ≠ i := by
    intro hEq
    subst q
    exact hxi hqx.symm
  refine ⟨q, ?_⟩
  calc
    (C.deform h).vertex q = C.vertex q :=
      C.deform_vertex_away h hqi
    _ = x := hqx

end IndexedInducedHole

/-- If two carriers contain opposite members of a vertex pair, swapping
that pair in opposite directions preserves their symmetric difference. -/
theorem symmDiff_opposite_swap
    {A B : Set V} {a b : V}
    (haA : a ∈ A) (hbA : b ∉ A)
    (hbB : b ∈ B) (haB : a ∉ B) :
    Set.insert b (A \ {a}) ∆ Set.insert a (B \ {b}) = A ∆ B := by
  ext v
  rw [Set.mem_symmDiff, Set.mem_symmDiff]
  change
    (((v = b ∨ (v ∈ A ∧ v ≠ a)) ∧
        ¬ (v = a ∨ (v ∈ B ∧ v ≠ b))) ∨
      ((v = a ∨ (v ∈ B ∧ v ≠ b)) ∧
        ¬ (v = b ∨ (v ∈ A ∧ v ≠ a)))) ↔
      ((v ∈ A ∧ v ∉ B) ∨ (v ∈ B ∧ v ∉ A))
  by_cases hva : v = a
  · subst v
    have hab : a ≠ b := by
      intro hab
      exact hbA (hab ▸ haA)
    simp [haA, haB, hab]
  · by_cases hvb : v = b
    · subst v
      have hba : b ≠ a := by
        intro hba
        exact haB (hba ▸ hbB)
      simp [hbA, hbB, hba]
    · simp [hva, hvb]

/-- If both carriers contain `a` and omit `b`, replacing `a` by `b` in
both carriers preserves their symmetric difference. -/
theorem symmDiff_same_swap
    {A B : Set V} {a b : V}
    (haA : a ∈ A) (hbA : b ∉ A)
    (haB : a ∈ B) (hbB : b ∉ B) :
    Set.insert b (A \ {a}) ∆ Set.insert b (B \ {a}) = A ∆ B := by
  ext v
  rw [Set.mem_symmDiff, Set.mem_symmDiff]
  change
    (((v = b ∨ (v ∈ A ∧ v ≠ a)) ∧
        ¬ (v = b ∨ (v ∈ B ∧ v ≠ a))) ∨
      ((v = b ∨ (v ∈ B ∧ v ≠ a)) ∧
        ¬ (v = b ∨ (v ∈ A ∧ v ≠ a)))) ↔
      ((v ∈ A ∧ v ∉ B) ∨ (v ∈ B ∧ v ∉ A))
  by_cases hva : v = a
  · subst v
    have hab : a ≠ b := by
      intro hab
      exact hbA (hab ▸ haA)
    simp [haA, haB, hab]
  · by_cases hvb : v = b
    · subst v
      simp [hbA, hbB]
    · simp [hva, hvb]

end SimpleGraph
