import FreeFermionGraphs.EvenHoleLabelingDeform

/-!
# Bridging indexed and alternating hole deformations

A concrete deformation step is stored using `IndexedInducedHole`, whereas
the paper's cyclic color coordinates use `EvenHoleLabeling`.  When their
carriers agree and the indexed removed vertex is identified with `a r`,
the indexed deformation axioms produce the corresponding alternating
`CloneAt` certificate.  The two resulting deformed carriers then agree.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace IndexedInducedHole

/-- Set-level description of an indexed single-vertex deformation. -/
theorem deform_range_eq
    (C : IndexedInducedHole G)
    {s : V} {i : Fin C.card}
    (h : C.SingleVertexDeformation s i) :
    Set.range (C.deform h).vertex =
      Set.insert s (Set.range C.vertex \ {C.vertex i}) := by
  ext v
  change
    (∃ q, (C.deform h).vertex q = v) ↔
      v = s ∨ ((∃ q, C.vertex q = v) ∧ v ≠ C.vertex i)
  constructor
  · rintro ⟨q, hq⟩
    by_cases hqi : q = i
    · subst q
      left
      simpa using hq.symm
    · right
      have hqv : C.vertex q = v := by
        calc
          C.vertex q = (C.deform h).vertex q :=
            (C.deform_vertex_away h hqi).symm
          _ = v := hq
      refine ⟨⟨q, hqv⟩, ?_⟩
      intro hvi
      exact hqi (C.injective (hqv.trans hvi))
  · rintro (rfl | ⟨⟨q, hq⟩, hvne⟩)
    · exact ⟨i, by simp⟩
    · have hqi : q ≠ i := by
        intro hqi
        subst q
        exact hvne hq.symm
      refine ⟨q, ?_⟩
      calc
        (C.deform h).vertex q = C.vertex q :=
          C.deform_vertex_away h hqi
        _ = _ := hq

end IndexedInducedHole

namespace EvenHoleLabeling

/-- An indexed deformation is a clone deformation in alternating
coordinates once the two presentations of the hole and removed vertex are
identified. -/
theorem cloneAt_of_indexedDeformation
    {k : Nat}
    (C : EvenHoleLabeling G k)
    (H : IndexedInducedHole G)
    {s : V} {i : Fin H.card}
    (h : H.SingleVertexDeformation s i)
    (r : Fin k)
    (hcarrier : C.carrier = Set.range H.vertex)
    (hremoved : H.vertex i = C.a r) :
    C.CloneAt s r := by
  constructor
  · intro hs
    apply h.outside
    rw [← hcarrier]
    exact hs
  · intro v hv
    have hvH : v ∈ Set.range H.vertex := by
      rw [← hcarrier]
      exact hv
    obtain ⟨q, hq⟩ := hvH
    subst v
    rw [h.adj_iff q]
    constructor
    · rintro (rfl | hadj)
      · exact Or.inl hremoved
      · exact Or.inr (by simpa [hremoved] using hadj)
    · rintro (heq | hadj)
      · left
        apply H.injective
        exact heq.trans hremoved.symm
      · right
        simpa [hremoved] using hadj

/-- The alternating and indexed transports have the same post-deformation
carrier. -/
theorem deform_carrier_eq_indexedDeform_range
    {k : Nat}
    (C : EvenHoleLabeling G k)
    (H : IndexedInducedHole G)
    {s : V} {i : Fin H.card}
    (h : H.SingleVertexDeformation s i)
    (r : Fin k)
    (hcarrier : C.carrier = Set.range H.vertex)
    (hremoved : H.vertex i = C.a r)
    (hc : C.CloneAt s r) :
    (C.deform hc).carrier =
      Set.range (H.deform h).vertex := by
  rw [C.deform_carrier hc, H.deform_range_eq h]
  simp only [deformedCarrier]
  rw [hcarrier, ← hremoved]

/-- Combined one-step transport: the indexed step supplies both the
alternating clone proof and agreement of the transported carriers. -/
theorem transport_indexedDeformation
    {k : Nat}
    (C : EvenHoleLabeling G k)
    (H : IndexedInducedHole G)
    {s : V} {i : Fin H.card}
    (h : H.SingleVertexDeformation s i)
    (r : Fin k)
    (hcarrier : C.carrier = Set.range H.vertex)
    (hremoved : H.vertex i = C.a r) :
    ∃ hc : C.CloneAt s r,
      (C.deform hc).carrier =
        Set.range (H.deform h).vertex := by
  let hc : C.CloneAt s r :=
    C.cloneAt_of_indexedDeformation
      H h r hcarrier hremoved
  exact
    ⟨hc,
      C.deform_carrier_eq_indexedDeform_range
        H h r hcarrier hremoved hc⟩

end EvenHoleLabeling

end SimpleGraph
