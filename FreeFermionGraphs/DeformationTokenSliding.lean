import FreeFermionGraphs.TokenSlidingComponents

/-!
# Even-hole deformations as token slides

The paper observes that a single-vertex deformation is a token slide on one
coloring class of an even hole.  This file proves that statement for the
`a`-color class of an alternating labeling.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace EvenHoleLabeling

variable {G : SimpleGraph V}

/-- The `a` coloring class of an alternating even-hole labeling. -/
def aColorClass {k : Nat} (C : EvenHoleLabeling G k) : Set V :=
  Set.range C.a

/-- Replace `a i` by its clone `s` in the `a` coloring class. -/
def deformedAColorClass {k : Nat} (C : EvenHoleLabeling G k)
    (s : V) (i : Fin k) : Set V :=
  Set.insert s (C.aColorClass \ {C.a i})

/-- The `a` coloring class is independent. -/
theorem aColorClass_isIndepSet {k : Nat} (C : EvenHoleLabeling G k) :
    G.IsIndepSet C.aColorClass := by
  intro x hx y hy _
  rcases hx with ⟨p, rfl⟩
  rcases hy with ⟨q, rfl⟩
  exact C.adj_aa p q

/-- A clone lies outside the original `a` coloring class. -/
theorem CloneAt.not_mem_aColorClass {k : Nat} {C : EvenHoleLabeling G k}
    {s : V} {i : Fin k} (h : C.CloneAt s i) :
    s ∉ C.aColorClass := by
  rintro ⟨j, rfl⟩
  exact h.outside (C.a_mem_carrier j)

/-- A clone is not adjacent to any unreplaced vertex in its coloring class. -/
theorem CloneAt.not_adj_a_of_ne {k : Nat} {C : EvenHoleLabeling G k}
    {s : V} {i j : Fin k} (h : C.CloneAt s i)
    (hne : C.a j ≠ C.a i) :
    ¬G.Adj s (C.a j) := by
  intro hs
  rcases (h.adj_iff (C.a j) (C.a_mem_carrier j)).1 hs with heq | hai
  · exact hne heq
  · exact C.adj_aa i j hai

/-- Replacing `a i` by its clone preserves independence of the coloring
class. -/
theorem CloneAt.deformedAColorClass_isIndepSet {k : Nat}
    {C : EvenHoleLabeling G k} {s : V} {i : Fin k}
    (h : C.CloneAt s i) :
    G.IsIndepSet (C.deformedAColorClass s i) := by
  intro x hx y hy _
  simp only [deformedAColorClass, Set.mem_insert_iff, Set.mem_diff,
    Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | hx
  · rcases hy with rfl | hy
    · exact G.irrefl s
    · rcases hy.1 with ⟨j, rfl⟩
      exact h.not_adj_a_of_ne hy.2
  · rcases hy with rfl | hy
    · rcases hx.1 with ⟨j, rfl⟩
      exact fun hadj => h.not_adj_a_of_ne hx.2 hadj.symm
    · rcases hx.1 with ⟨p, rfl⟩
      rcases hy.1 with ⟨q, rfl⟩
      exact C.adj_aa p q

/-- A single-vertex deformation gives an oriented token slide on the
corresponding coloring class. -/
theorem CloneAt.forwardTokenSlide_aColorClass {k : Nat}
    {C : EvenHoleLabeling G k} {s : V} {i : Fin k}
    (h : C.CloneAt s i) :
    ForwardTokenSlide G C.aColorClass (C.deformedAColorClass s i) := by
  refine ⟨C.aColorClass_isIndepSet, h.deformedAColorClass_isIndepSet,
    C.a i, s, h.adj_original.symm, ?_, ?_, rfl⟩
  · constructor
    · exact ⟨i, rfl⟩
    · have hais : C.a i ≠ s := by
        intro his
        apply h.outside
        rw [← his]
        exact C.a_mem_carrier i
      simp [deformedAColorClass, hais]
  · exact ⟨by simp [deformedAColorClass], h.not_mem_aColorClass⟩

/-- Paper-facing form: a single-vertex even-hole deformation is a token
slide on its coloring class. -/
theorem CloneAt.tokenSlide_aColorClass {k : Nat}
    {C : EvenHoleLabeling G k} {s : V} {i : Fin k}
    (h : C.CloneAt s i) :
    G.TokenSlide C.aColorClass (C.deformedAColorClass s i) :=
  Or.inl h.forwardTokenSlide_aColorClass

end EvenHoleLabeling

end SimpleGraph
