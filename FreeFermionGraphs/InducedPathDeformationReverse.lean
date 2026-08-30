import FreeFermionGraphs.InducedPathDeformation

/-!
# Reversibility of induced-path deformations

Manuscript Definition 10 notes that a single-vertex deformation is reversible:
if `s ≺_P P.vertex i`, then the removed vertex `P.vertex i` is a clone of `s`
in the deformed path.  This module proves the corresponding indexed statement.
-/

universe u
variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace IndexedInducedPath

/-- A single-vertex deformation is locally reversible at the same path index.

If `s` replaces `P.vertex i`, then in `P.deform h` the original vertex
`P.vertex i` has exactly the required three-vertex path neighborhood around
`s`.  No equality of whole path structures is assumed here. -/
theorem SingleVertexDeformation.reverse
    (P : IndexedInducedPath G) {s : V} {i : Fin P.card}
    (h : P.SingleVertexDeformation s i) :
    (P.deform h).SingleVertexDeformation (P.vertex i) i := by
  refine
    { outside := ?_
      internal_left := h.internal_left
      internal_right := h.internal_right
      adj_iff := ?_ }
  · rintro ⟨q, hq⟩
    by_cases hqi : q = i
    · subst q
      have hsi : s = P.vertex i := by
        simpa using hq
      exact h.outside ⟨i, hsi.symm⟩
    · have hPi : P.vertex q = P.vertex i := by
        calc
          P.vertex q = (P.deform h).vertex q :=
            (deform_vertex_away P h hqi).symm
          _ = P.vertex i := hq
      exact hqi (P.injective hPi)
  · intro q
    by_cases hqi : q = i
    · subst q
      have hsi : G.Adj s (P.vertex i) :=
        (h.adj_iff i).2 (Or.inl rfl)
      have his : G.Adj (P.vertex i) s := hsi.symm
      simp [his]
    · have haway : (P.deform h).vertex q = P.vertex q :=
        deform_vertex_away P h hqi
      have hi : (P.deform h).vertex i = s :=
        deform_vertex_at P h
      rw [haway, hi]
      constructor
      · intro hiq
        exact Or.inr ((h.adj_iff q).2 (Or.inr hiq))
      · intro hq
        rcases hq with hqi' | hsq
        · exact (hqi hqi').elim
        · rcases (h.adj_iff q).1 hsq with hqi' | hiq
          · exact (hqi hqi').elim
          · exact hiq

/-- Applying the reverse deformation at the same index recovers the original
indexed path, including its ordering. -/
theorem SingleVertexDeformation.deform_reverse_eq
    (P : IndexedInducedPath G) {s : V} {i : Fin P.card}
    (h : P.SingleVertexDeformation s i) :
    (P.deform h).deform h.reverse = P := by
  cases P with
  | mk card nonempty vertex injective adj_iff =>
    simp only [deform]
    congr 1
    funext q
    by_cases hqi : q = i
    · subst q
      simp [replaceVertex]
    · simp [replaceVertex, hqi]

end IndexedInducedPath

/-- A generator step of the induced-path deformation closure can be traversed
in the opposite direction. -/
theorem InducedPathDeformationStep.symm
    {P Q : IndexedInducedPath G}
    (h : InducedPathDeformationStep G P Q) :
    InducedPathDeformationStep G Q P := by
  rcases h with ⟨s, i, hdef, rfl⟩
  exact
    ⟨P.vertex i, i, hdef.reverse,
      (hdef.deform_reverse_eq P).symm⟩

/-- Definition 12 deformation closure is symmetric because each of its
single-vertex generators is reversible. -/
theorem InInducedPathDeformationClosure.symm
    {P Q : IndexedInducedPath G}
    (h : InInducedPathDeformationClosure G P Q) :
    InInducedPathDeformationClosure G Q P := by
  induction h with
  | refl => exact InInducedPathDeformationClosure.refl P
  | tail hPQ hQR ih =>
      exact hQR.symm.inClosure.trans ih

end SimpleGraph
