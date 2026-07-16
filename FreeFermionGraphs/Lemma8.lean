import FreeFermionGraphs.EvenHoleLabeling

/-!
# Lemma 8: restriction of additional neighbors

This module adds the Corollary 3 step in the proof of Lemma 8.  Once one of
the two base arms is forced, every additional neighbor is restricted to one
of the two outer `b`-vertices.  The final Lemma 8 classification eliminates
the outer vertex on the opposite side (except in the four-cycle case).
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace EvenHoleLabeling

/-- Exact neighbors of an `a`-vertex within an alternating even-hole
carrier. -/
theorem adj_a_iff_of_mem {k : Nat} (C : EvenHoleLabeling G k)
    {i : Fin k} {v : V} (hv : v ∈ C.carrier) :
    G.Adj (C.a i) v ↔ v = C.b i ∨ v = C.b (C.next i) := by
  rcases hv with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · constructor
    · intro h
      exact (C.adj_aa i j h).elim
    · intro h
      rcases h with h | h
      · exact (C.color_disjoint j i h).elim
      · exact (C.color_disjoint j (C.next i) h).elim
  · constructor
    · intro h
      rcases (C.adj_ab_iff i j).1 h with hji | hji
      · exact Or.inl (congrArg C.b hji)
      · exact Or.inr (congrArg C.b hji)
    · intro h
      rcases h with h | h
      · exact (C.adj_ab_iff i j).2
          (Or.inl (C.b_injective h))
      · exact (C.adj_ab_iff i j).2
          (Or.inr (C.b_injective h))

/-- Exact neighbors of a clone within the original even-hole carrier. -/
theorem CloneAt.adj_iff_of_mem {k : Nat} {C : EvenHoleLabeling G k}
    {s : V} {i : Fin k} (h : C.CloneAt s i) {v : V}
    (hv : v ∈ C.carrier) :
    G.Adj s v ↔
      v = C.a i ∨ v = C.b i ∨ v = C.b (C.next i) := by
  rw [h.adj_iff v hv, C.adj_a_iff_of_mem hv]
  tauto

/-- Corollary 3 restricts an additional neighbor of the left-hand base arm
`a (prev i)-b i-u` to `b (prev i)` or `b (next i)`. -/
theorem CloneAt.left_additional_neighbor {k : Nat}
    {C : EvenHoleLabeling G k} {s t u v : V} {i : Fin k}
    (h : C.CloneAt s i) (hclaw : G.IsClawFree)
    (hchoice :
      (u = s ∧ ¬G.Adj t (C.a i)) ∨
      (u = C.a i ∧ ¬G.Adj t s))
    (htu : G.Adj t u)
    (htb : G.Adj t (C.b i))
    (hta : G.Adj t (C.a (C.prev i)))
    (hvC : v ∈ Set.insert s C.carrier)
    (htv : G.Adj t v)
    (hvu : v ≠ u) (hvb : v ≠ C.b i)
    (hva : v ≠ C.a (C.prev i)) :
    v = C.b (C.prev i) ∨ v = C.b (C.next i) := by
  have hbu : G.Adj (C.b i) u := by
    rcases hchoice with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact h.adj_b.symm
    · exact (C.adj_a_b i).symm
  have hau_nonadj : ¬G.Adj (C.a (C.prev i)) u := by
    rcases hchoice with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · intro has
      exact h.not_adj_a_prev has.symm
    · exact C.adj_aa (C.prev i) i
  have hau_ne : C.a (C.prev i) ≠ u := by
    rcases hchoice with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · intro has
      exact h.outside (has ▸ C.a_mem_carrier (C.prev i))
    · exact C.a_ne_prev i
  have hpath :
      G.IsInducedPathTriple (C.a (C.prev i)) (C.b i) u :=
    ⟨C.adj_a_prev_b i, hbu, hau_nonadj, hau_ne⟩
  rcases hclaw.corollary3 hpath hta htb htu htv hva hvu with
    hva' | hvu'
  · rcases Set.mem_insert_iff.1 hvC with rfl | hvCarrier
    · exact (h.not_adj_a_prev hva').elim
    · rcases (C.adj_a_iff_of_mem hvCarrier).1 hva'.symm with
        hvprev | hvi
      · exact Or.inl hvprev
      · rw [C.next_prev i] at hvi
        exact (hvb hvi).elim
  · rcases hchoice with ⟨rfl, htai⟩ | ⟨rfl, hts⟩
    · rcases Set.mem_insert_iff.1 hvC with hvs | hvCarrier
      · exact (hvu hvs).elim
      · rcases (h.adj_iff_of_mem hvCarrier).1 hvu' with
          hvai | hvi | hvnext
        · exact (htai (hvai ▸ htv)).elim
        · exact (hvb hvi).elim
        · exact Or.inr hvnext
    · rcases Set.mem_insert_iff.1 hvC with hvs | hvCarrier
      · exact (hts (hvs ▸ htv)).elim
      · rcases (C.adj_a_iff_of_mem hvCarrier).1 hvu' with
          hvi | hvnext
        · exact (hvb hvi).elim
        · exact Or.inr hvnext

/-- Corollary 3 restricts an additional neighbor of the right-hand base arm
`u-b (next i)-a (next i)` to `b i` or `b (next (next i))`. -/
theorem CloneAt.right_additional_neighbor {k : Nat}
    {C : EvenHoleLabeling G k} {s t u v : V} {i : Fin k}
    (h : C.CloneAt s i) (hclaw : G.IsClawFree)
    (hchoice :
      (u = s ∧ ¬G.Adj t (C.a i)) ∨
      (u = C.a i ∧ ¬G.Adj t s))
    (htu : G.Adj t u)
    (htb : G.Adj t (C.b (C.next i)))
    (hta : G.Adj t (C.a (C.next i)))
    (hvC : v ∈ Set.insert s C.carrier)
    (htv : G.Adj t v)
    (hvu : v ≠ u) (hvb : v ≠ C.b (C.next i))
    (hva : v ≠ C.a (C.next i)) :
    v = C.b i ∨ v = C.b (C.next (C.next i)) := by
  have hub : G.Adj u (C.b (C.next i)) := by
    rcases hchoice with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact h.adj_b_next
    · exact C.adj_a_b_next i
  have hua_nonadj : ¬G.Adj u (C.a (C.next i)) := by
    rcases hchoice with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact h.not_adj_a_next
    · exact C.adj_aa i (C.next i)
  have hua_ne : u ≠ C.a (C.next i) := by
    rcases hchoice with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · intro has
      exact h.outside (has.symm ▸ C.a_mem_carrier (C.next i))
    · exact (C.a_ne_next i).symm
  have hpath :
      G.IsInducedPathTriple u (C.b (C.next i))
        (C.a (C.next i)) :=
    ⟨hub, (C.adj_a_b (C.next i)).symm, hua_nonadj, hua_ne⟩
  rcases hclaw.corollary3 hpath htu htb hta htv hvu hva with
    hvu' | hva'
  · rcases hchoice with ⟨rfl, htai⟩ | ⟨rfl, hts⟩
    · rcases Set.mem_insert_iff.1 hvC with hvs | hvCarrier
      · exact (hvu hvs).elim
      · rcases (h.adj_iff_of_mem hvCarrier).1 hvu'.symm with
          hvai | hvi | hvnext
        · exact (htai (hvai ▸ htv)).elim
        · exact Or.inl hvi
        · exact (hvb hvnext).elim
    · rcases Set.mem_insert_iff.1 hvC with hvs | hvCarrier
      · exact (hts (hvs ▸ htv)).elim
      · rcases (C.adj_a_iff_of_mem hvCarrier).1 hvu'.symm with
          hvi | hvnext
        · exact Or.inl hvi
        · exact (hvb hvnext).elim
  · rcases Set.mem_insert_iff.1 hvC with rfl | hvCarrier
    · exact (h.not_adj_a_next hva').elim
    · rcases (C.adj_a_iff_of_mem hvCarrier).1 hva'.symm with
        hvnext | hvnextnext
      · exact (hvb hvnext).elim
      · exact Or.inr hvnextnext

/-- The neighbor-restriction form of Lemma 8.  It packages the forced base
arm together with the two possible locations of any additional neighbor. -/
theorem CloneAt.dependent_neighbor_restriction {k : Nat}
    {C : EvenHoleLabeling G k} {s t : V} {i : Fin k}
    (h : C.CloneAt s i) (hclaw : G.IsClawFree)
    (htC : t ∉ Set.insert s C.carrier)
    (hexact :
      (G.Adj t s ∧ ¬G.Adj t (C.a i)) ∨
      (¬G.Adj t s ∧ G.Adj t (C.a i))) :
    ∃ u : V,
      ((u = s ∧ ¬G.Adj t (C.a i)) ∨
        (u = C.a i ∧ ¬G.Adj t s)) ∧
      G.Adj t u ∧
      ((G.Adj t (C.b i) ∧ G.Adj t (C.a (C.prev i)) ∧
        ∀ v : V, v ∈ Set.insert s C.carrier → G.Adj t v →
          v ≠ u → v ≠ C.b i → v ≠ C.a (C.prev i) →
          v = C.b (C.prev i) ∨ v = C.b (C.next i)) ∨
       (G.Adj t (C.b (C.next i)) ∧
        G.Adj t (C.a (C.next i)) ∧
        ∀ v : V, v ∈ Set.insert s C.carrier → G.Adj t v →
          v ≠ u → v ≠ C.b (C.next i) →
          v ≠ C.a (C.next i) →
          v = C.b i ∨ v = C.b (C.next (C.next i)))) := by
  have hbase := h.dependent_forces_side hclaw htC hexact
  rcases hexact with ⟨hts, htai⟩ | ⟨hts, htai⟩
  · refine ⟨s, Or.inl ⟨rfl, htai⟩, hts, ?_⟩
    rcases hbase with ⟨htb, hta⟩ | ⟨htb, hta⟩
    · refine Or.inl ⟨htb, hta, ?_⟩
      intro v hvC htv hvu hvb hva
      exact h.left_additional_neighbor hclaw (Or.inl ⟨rfl, htai⟩)
        hts htb hta hvC htv hvu hvb hva
    · refine Or.inr ⟨htb, hta, ?_⟩
      intro v hvC htv hvu hvb hva
      exact h.right_additional_neighbor hclaw (Or.inl ⟨rfl, htai⟩)
        hts htb hta hvC htv hvu hvb hva
  · refine ⟨C.a i, Or.inr ⟨rfl, hts⟩, htai, ?_⟩
    rcases hbase with ⟨htb, hta⟩ | ⟨htb, hta⟩
    · refine Or.inl ⟨htb, hta, ?_⟩
      intro v hvC htv hvu hvb hva
      exact h.left_additional_neighbor hclaw (Or.inr ⟨rfl, hts⟩)
        htai htb hta hvC htv hvu hvb hva
    · refine Or.inr ⟨htb, hta, ?_⟩
      intro v hvC htv hvu hvb hva
      exact h.right_additional_neighbor hclaw (Or.inr ⟨rfl, hts⟩)
        htai htb hta hvC htv hvu hvb hva

end EvenHoleLabeling

end SimpleGraph
