import FreeFermionGraphs.Lemma8

/-!
# Corollaries 4 and 5

The two immediate consequences of Lemma 8 for an even hole of length
`2k` with `k > 2`.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace EvenHoleLabeling

/-- Corollary 4 of the paper: outside the four-cycle case, a vertex dependent
on a deformation at `a i` neighbors exactly one of `b i` and `b (next i)`. -/
theorem CloneAt.corollary4 {k : Nat}
    {C : EvenHoleLabeling G k} {s t : V} {i : Fin k}
    (h : C.CloneAt s i) (hclaw : G.IsClawFree) (hk : 2 < k)
    (htC : t ∉ Set.insert s C.carrier)
    (hexact :
      (G.Adj t s ∧ ¬G.Adj t (C.a i)) ∨
      (¬G.Adj t s ∧ G.Adj t (C.a i))) :
    (G.Adj t (C.b i) ∧ ¬G.Adj t (C.b (C.next i))) ∨
    (¬G.Adj t (C.b i) ∧ G.Adj t (C.b (C.next i))) := by
  obtain ⟨u, hu, hcase⟩ := h.lemma8 hclaw htC hexact
  have hbi_ne_u : C.b i ≠ u := by
    rcases hu with rfl | rfl
    · intro hbis
      exact h.outside (hbis ▸ C.b_mem_carrier i)
    · exact (C.color_disjoint i i).symm
  have hbnext_ne_u : C.b (C.next i) ≠ u := by
    rcases hu with rfl | rfl
    · intro hbns
      exact h.outside (hbns ▸ C.b_mem_carrier (C.next i))
    · exact (C.color_disjoint i (C.next i)).symm
  have hbi_mem : C.b i ∈ Set.insert s C.carrier :=
    Set.mem_insert_iff.2 (Or.inr (C.b_mem_carrier i))
  have hbnext_mem : C.b (C.next i) ∈ Set.insert s C.carrier :=
    Set.mem_insert_iff.2 (Or.inr (C.b_mem_carrier (C.next i)))
  rcases hcase with hI | hII | hIII | hIV
  · refine Or.inl ⟨(hI (C.b i) hbi_mem).2 (Or.inr (Or.inl rfl)), ?_⟩
    intro hbn
    rcases (hI (C.b (C.next i)) hbnext_mem).1 hbn with
      hbna | hbni | hbnu
    · exact C.color_disjoint (C.prev i) (C.next i) hbna.symm
    · exact C.b_ne_next i hbni
    · exact hbnext_ne_u hbnu
  · refine Or.inl ⟨(hII (C.b i) hbi_mem).2
      (Or.inr (Or.inr (Or.inl rfl))), ?_⟩
    intro hbn
    rcases (hII (C.b (C.next i)) hbnext_mem).1 hbn with
      hbnp | hbna | hbni | hbnu
    · exact C.b_prev_ne_next hk i hbnp.symm
    · exact C.color_disjoint (C.prev i) (C.next i) hbna.symm
    · exact C.b_ne_next i hbni
    · exact hbnext_ne_u hbnu
  · refine Or.inr ⟨?_, (hIII (C.b (C.next i)) hbnext_mem).2
      (Or.inr (Or.inl rfl))⟩
    intro hbi
    rcases (hIII (C.b i) hbi_mem).1 hbi with hbiu | hbin | hbia
    · exact hbi_ne_u hbiu
    · exact C.b_ne_next i hbin.symm
    · exact C.color_disjoint (C.next i) i hbia.symm
  · refine Or.inr ⟨?_, (hIV (C.b (C.next i)) hbnext_mem).2
      (Or.inr (Or.inl rfl))⟩
    intro hbi
    rcases (hIV (C.b i) hbi_mem).1 hbi with
      hbiu | hbin | hbia | hbinn
    · exact hbi_ne_u hbiu
    · exact C.b_ne_next i hbin.symm
    · exact C.color_disjoint (C.next i) i hbia.symm
    · exact C.b_ne_next_next hk i hbinn

/-- Corollary 5 of the paper: for `k > 2`, if `t` neighbors at least one of
the clone/original pair and both adjacent `b`-vertices, then it neighbors
both the clone and the original. -/
theorem CloneAt.corollary5 {k : Nat}
    {C : EvenHoleLabeling G k} {s t : V} {i : Fin k}
    (h : C.CloneAt s i) (hclaw : G.IsClawFree) (hk : 2 < k)
    (htC : t ∉ Set.insert s C.carrier)
    (hatleast : G.Adj t s ∨ G.Adj t (C.a i))
    (hboth : G.Adj t (C.b i) ∧ G.Adj t (C.b (C.next i))) :
    G.Adj t s ∧ G.Adj t (C.a i) := by
  have hts : G.Adj t s := by
    by_contra hts
    have htai : G.Adj t (C.a i) := hatleast.resolve_left hts
    rcases h.corollary4 hclaw hk htC (Or.inr ⟨hts, htai⟩) with
      ⟨_, hnot⟩ | ⟨hnot, _⟩
    · exact hnot hboth.2
    · exact hnot hboth.1
  have htai : G.Adj t (C.a i) := by
    by_contra htai
    rcases h.corollary4 hclaw hk htC (Or.inl ⟨hts, htai⟩) with
      ⟨_, hnot⟩ | ⟨hnot, _⟩
    · exact hnot hboth.2
    · exact hnot hboth.1
  exact ⟨hts, htai⟩

end EvenHoleLabeling

end SimpleGraph
