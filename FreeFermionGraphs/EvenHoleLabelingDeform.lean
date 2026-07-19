import FreeFermionGraphs.Lemma11BAlternatingHoleCoordinates
import FreeFermionGraphs.NeighborhoodDeformation

/-!
# Transporting alternating labels through a deformation

Replacing an `a`-vertex of an alternating even hole by a clone preserves
the complete alternating labeling.  This is the labeled counterpart of
`IndexedInducedHole.deform` and is the step needed to propagate one initial
paper labeling through a concrete deformation sequence.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace EvenHoleLabeling

/-- Replace the `a`-vertex at index `i` by `s`. -/
def replaceA {k : Nat} (C : EvenHoleLabeling G k)
    (s : V) (i : Fin k) : Fin k → V :=
  fun q => if q = i then s else C.a q

@[simp]
theorem replaceA_at {k : Nat} (C : EvenHoleLabeling G k)
    (s : V) (i : Fin k) :
    C.replaceA s i i = s := by
  simp [replaceA]

@[simp]
theorem replaceA_away {k : Nat} (C : EvenHoleLabeling G k)
    (s : V) {i q : Fin k} (hqi : q ≠ i) :
    C.replaceA s i q = C.a q := by
  simp [replaceA, hqi]

/-- Replacing an `a`-vertex by a clone preserves the alternating
even-hole labeling, with the same cyclic index maps and all `b`-vertices
unchanged. -/
def deform {k : Nat} (C : EvenHoleLabeling G k)
    {s : V} {i : Fin k} (h : C.CloneAt s i) :
    EvenHoleLabeling G k := by
  have hs_not_adj :
      ∀ q : Fin k, q ≠ i → ¬G.Adj s (C.a q) := by
    intro q hqi hsq
    rcases
        (h.adj_iff (C.a q) (C.a_mem_carrier q)).1 hsq with
      hqi' | haiq
    · exact hqi (C.a_injective hqi')
    · exact C.adj_aa i q haiq
  refine
    { two_le := C.two_le
      a := C.replaceA s i
      b := C.b
      next := C.next
      prev := C.prev
      next_ne := C.next_ne
      next_next_ne := C.next_next_ne
      next_prev := C.next_prev
      prev_next := C.prev_next
      a_injective := ?_
      b_injective := C.b_injective
      color_disjoint := ?_
      adj_aa := ?_
      adj_bb := C.adj_bb
      adj_ab_iff := ?_ }
  · intro p q hpq
    by_cases hp : p = i
    · subst p
      by_cases hq : q = i
      · exact hq.symm
      · exfalso
        apply h.outside
        have hsqa : s = C.a q := by
          simpa [replaceA, hq] using hpq
        rw [hsqa]
        exact C.a_mem_carrier q
    · by_cases hq : q = i
      · subst q
        exfalso
        apply h.outside
        have hpas : C.a p = s := by
          simpa [replaceA, hp] using hpq
        rw [← hpas]
        exact C.a_mem_carrier p
      · apply C.a_injective
        simpa [replaceA, hp, hq] using hpq
  · intro p q
    by_cases hp : p = i
    · subst p
      simp only [replaceA_at]
      intro hsb
      apply h.outside
      rw [hsb]
      exact C.b_mem_carrier q
    · simpa [replaceA, hp] using C.color_disjoint p q
  · intro p q
    by_cases hp : p = i
    · subst p
      by_cases hq : q = i
      · subst q
        simp [replaceA]
      · simpa [replaceA, hq] using hs_not_adj q hq
    · by_cases hq : q = i
      · subst q
        have hnot : ¬G.Adj (C.a p) s :=
          fun hps => hs_not_adj p hp hps.symm
        simpa [replaceA, hp] using hnot
      · simpa [replaceA, hp, hq] using C.adj_aa p q
  · intro p q
    by_cases hp : p = i
    · subst p
      simp only [replaceA_at]
      rw [h.adj_iff (C.b q) (C.b_mem_carrier q)]
      rw [C.adj_ab_iff i q]
      simp [(C.color_disjoint i q).symm]
    · simpa [replaceA, hp] using C.adj_ab_iff p q

@[simp]
theorem deform_a_at {k : Nat} (C : EvenHoleLabeling G k)
    {s : V} {i : Fin k} (h : C.CloneAt s i) :
    (C.deform h).a i = s := by
  simp [deform]

@[simp]
theorem deform_a_away {k : Nat} (C : EvenHoleLabeling G k)
    {s : V} {i q : Fin k} (h : C.CloneAt s i)
    (hqi : q ≠ i) :
    (C.deform h).a q = C.a q := by
  simp [deform, hqi]

@[simp]
theorem deform_b {k : Nat} (C : EvenHoleLabeling G k)
    {s : V} {i : Fin k} (h : C.CloneAt s i)
    (q : Fin k) :
    (C.deform h).b q = C.b q :=
  rfl

@[simp]
theorem deform_next {k : Nat} (C : EvenHoleLabeling G k)
    {s : V} {i : Fin k} (h : C.CloneAt s i)
    (q : Fin k) :
    (C.deform h).next q = C.next q :=
  rfl

/-- The transported labeling has exactly the carrier obtained by replacing
`a i` by its clone. -/
theorem deform_carrier {k : Nat} (C : EvenHoleLabeling G k)
    {s : V} {i : Fin k} (h : C.CloneAt s i) :
    (C.deform h).carrier = C.deformedCarrier s i := by
  ext v
  change
    v ∈ Set.range (C.replaceA s i) ∪ Set.range C.b ↔
      v ∈ Set.insert s
        ((Set.range C.a ∪ Set.range C.b) \ {C.a i})
  simp only [Set.mem_union, Set.mem_range]
  constructor
  · rintro (⟨q, hq⟩ | ⟨q, hq⟩)
    · by_cases hqi : q = i
      · left
        subst q
        simpa [replaceA] using hq.symm
      · right
        have hqv : C.a q = v := by
          simpa [replaceA, hqi] using hq
        refine ⟨Or.inl ⟨q, hqv⟩, ?_⟩
        intro hvi
        exact hqi (C.a_injective (hqv.trans hvi))
    · right
      refine ⟨Or.inr ⟨q, hq⟩, ?_⟩
      intro hvi
      exact C.color_disjoint i q (hvi.symm.trans hq.symm)
  · rintro (rfl | ⟨hcarrier, hvne⟩)
    · left
      exact ⟨i, by simp [replaceA]⟩
    · rcases hcarrier with ⟨q, hq⟩ | ⟨q, hq⟩
      · have hqi : q ≠ i := by
          intro hqi
          subst q
          exact hvne hq.symm
        left
        exact ⟨q, by simpa [replaceA, hqi] using hq⟩
      · right
        exact ⟨q, hq⟩

end EvenHoleLabeling

end SimpleGraph
