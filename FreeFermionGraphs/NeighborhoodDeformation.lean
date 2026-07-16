import FreeFermionGraphs.Corollaries45

/-!
# Neighborhoods under a single deformation

The one-step invariant used in Lemma 9: replacing an even-hole vertex by a
clone does not change which external vertices neighbor the hole.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- The union of the open neighborhoods of the vertices in `S`. -/
def openNeighborhood (G : SimpleGraph V) (S : Set V) : Set V :=
  {t | ∃ v ∈ S, G.Adj t v}

@[simp]
theorem mem_openNeighborhood {S : Set V} {t : V} :
    t ∈ G.openNeighborhood S ↔ ∃ v ∈ S, G.Adj t v :=
  Iff.rfl

namespace EvenHoleLabeling

/-- The carrier obtained by replacing `a i` with its clone `s`. -/
def deformedCarrier {k : Nat} (C : EvenHoleLabeling G k)
    (s : V) (i : Fin k) : Set V :=
  Set.insert s (C.carrier \ {C.a i})

@[simp]
theorem clone_mem_deformedCarrier {k : Nat} (C : EvenHoleLabeling G k)
    (s : V) (i : Fin k) : s ∈ C.deformedCarrier s i := by
  simp [deformedCarrier]

theorem mem_deformedCarrier_of_mem {k : Nat}
    (C : EvenHoleLabeling G k) {s v : V} {i : Fin k}
    (hv : v ∈ C.carrier) (hvi : v ≠ C.a i) :
    v ∈ C.deformedCarrier s i := by
  simp [deformedCarrier, hv, hvi]

/-- The two cycle neighbors of the replaced `a`-vertex remain in the
deformed carrier. -/
theorem b_mem_deformedCarrier {k : Nat} (C : EvenHoleLabeling G k)
    (s : V) (i : Fin k) : C.b i ∈ C.deformedCarrier s i := by
  exact C.mem_deformedCarrier_of_mem (C.b_mem_carrier i)
    (C.color_disjoint i i).symm

theorem b_next_mem_deformedCarrier {k : Nat}
    (C : EvenHoleLabeling G k) (s : V) (i : Fin k) :
    C.b (C.next i) ∈ C.deformedCarrier s i := by
  exact C.mem_deformedCarrier_of_mem (C.b_mem_carrier (C.next i))
    (C.color_disjoint i (C.next i)).symm

/-- The external-vertex step in the proof of Lemma 9.  Lemma 8 supplies an
unchanged `b`-neighbor whenever `t` neighbors exactly one of the clone and
the replaced vertex. -/
theorem CloneAt.external_openNeighborhood_deformedCarrier_iff {k : Nat}
    {C : EvenHoleLabeling G k} {s t : V} {i : Fin k}
    (h : C.CloneAt s i) (hclaw : G.IsClawFree)
    (htC : t ∉ Set.insert s C.carrier) :
    t ∈ G.openNeighborhood (C.deformedCarrier s i) ↔
      t ∈ G.openNeighborhood C.carrier := by
  constructor
  · rintro ⟨v, hv, htv⟩
    rcases Set.mem_insert_iff.1 hv with hvs | hvrest
    · subst v
      by_cases htai : G.Adj t (C.a i)
      · exact ⟨C.a i, C.a_mem_carrier i, htai⟩
      · have hbase := h.dependent_forces_side hclaw htC
          (Or.inl ⟨htv, htai⟩)
        rcases hbase with ⟨htbi, _⟩ | ⟨htbn, _⟩
        · exact ⟨C.b i, C.b_mem_carrier i, htbi⟩
        · exact ⟨C.b (C.next i), C.b_mem_carrier (C.next i), htbn⟩
    · exact ⟨v, hvrest.1, htv⟩
  · rintro ⟨v, hv, htv⟩
    by_cases hvai : v = C.a i
    · subst v
      by_cases hts : G.Adj t s
      · exact ⟨s, C.clone_mem_deformedCarrier s i, hts⟩
      · have hbase := h.dependent_forces_side hclaw htC
          (Or.inr ⟨hts, htv⟩)
        rcases hbase with ⟨htbi, _⟩ | ⟨htbn, _⟩
        · exact ⟨C.b i, C.b_mem_deformedCarrier s i, htbi⟩
        · exact ⟨C.b (C.next i),
            C.b_next_mem_deformedCarrier s i, htbn⟩
    · exact ⟨v, C.mem_deformedCarrier_of_mem hv hvai, htv⟩

end EvenHoleLabeling

end SimpleGraph
