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
      · rcases (h.adj_iff_of_mem hvCarrier).1 hvu'.symm with
          hvai | hvi | hvnext
        · exact (htai (hvai ▸ htv)).elim
        · exact (hvb hvi).elim
        · exact Or.inr hvnext
    · rcases Set.mem_insert_iff.1 hvC with hvs | hvCarrier
      · exact (hts (hvs ▸ htv)).elim
      · rcases (C.adj_a_iff_of_mem hvCarrier).1 hvu'.symm with
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

/-- In the left-hand arm, the candidate on the opposite side either
coincides with the permitted outer vertex (the four-cycle degeneracy) or is
not adjacent to `t`. -/
theorem CloneAt.left_opposite_outer_eq_or_not_adj {k : Nat}
    {C : EvenHoleLabeling G k} {s t u : V} {i : Fin k}
    (h : C.CloneAt s i) (hclaw : G.IsClawFree)
    (htC : t ∉ Set.insert s C.carrier)
    (hchoice :
      (u = s ∧ ¬G.Adj t (C.a i)) ∨
      (u = C.a i ∧ ¬G.Adj t s))
    (htu : G.Adj t u)
    (htb : G.Adj t (C.b i))
    (hta : G.Adj t (C.a (C.prev i))) :
    C.b (C.next i) = C.b (C.prev i) ∨
      ¬G.Adj t (C.b (C.next i)) := by
  by_cases heq : C.b (C.next i) = C.b (C.prev i)
  · exact Or.inl heq
  · refine Or.inr ?_
    have hidx : C.next i ≠ C.prev i := by
      intro hidx
      exact heq (congrArg C.b hidx)
    have ht_anext : ¬G.Adj t (C.a (C.next i)) := by
      intro htanext
      have hane_u : C.a (C.next i) ≠ u := by
        rcases hchoice with ⟨rfl, _⟩ | ⟨rfl, _⟩
        · intro has
          exact h.outside (has ▸ C.a_mem_carrier (C.next i))
        · exact C.a_ne_next i
      have hane_bi : C.a (C.next i) ≠ C.b i :=
        C.color_disjoint (C.next i) i
      have hane_aprev : C.a (C.next i) ≠ C.a (C.prev i) := by
        intro haa
        exact hidx (C.a_injective haa)
      rcases h.left_additional_neighbor hclaw hchoice htu htb hta
          (Set.mem_insert_iff.2
            (Or.inr (C.a_mem_carrier (C.next i))))
          htanext hane_u hane_bi hane_aprev with hbad | hbad
      · exact C.color_disjoint (C.next i) (C.prev i) hbad
      · exact C.color_disjoint (C.next i) (C.next i) hbad
    have ht_ai : t ≠ C.a i := by
      intro htai
      exact htC (Set.mem_insert_iff.2
        (Or.inr (htai.symm ▸ C.a_mem_carrier i)))
    have ht_anext_ne : t ≠ C.a (C.next i) := by
      intro htanext
      exact htC (Set.mem_insert_iff.2
        (Or.inr (htanext.symm ▸ C.a_mem_carrier (C.next i))))
    have ht_s : t ≠ s := by
      intro hts
      exact htC (Set.mem_insert_iff.2 (Or.inl hts))
    intro htwrong
    rcases hchoice with ⟨rfl, htai⟩ | ⟨rfl, hts⟩
    · rcases hclaw.adjacent_to_one_of_nonadjacent_neighbors
          htwrong (C.adj_a_b_next i).symm
          (C.adj_a_b (C.next i)).symm
          ht_ai ht_anext_ne (C.a_ne_next i).symm
          (C.adj_aa i (C.next i)) with htai' | htanext'
      · exact htai htai'
      · exact ht_anext htanext'
    · have hs_anext : s ≠ C.a (C.next i) := by
        intro hsa
        exact h.outside (hsa.symm ▸ C.a_mem_carrier (C.next i))
      rcases hclaw.adjacent_to_one_of_nonadjacent_neighbors
          htwrong h.adj_b_next.symm
          (C.adj_a_b (C.next i)).symm
          ht_s ht_anext_ne hs_anext h.not_adj_a_next with
        hts' | htanext'
      · exact hts hts'
      · exact ht_anext htanext'

/-- Symmetric opposite-side exclusion for the right-hand arm. -/
theorem CloneAt.right_opposite_outer_eq_or_not_adj {k : Nat}
    {C : EvenHoleLabeling G k} {s t u : V} {i : Fin k}
    (h : C.CloneAt s i) (hclaw : G.IsClawFree)
    (htC : t ∉ Set.insert s C.carrier)
    (hchoice :
      (u = s ∧ ¬G.Adj t (C.a i)) ∨
      (u = C.a i ∧ ¬G.Adj t s))
    (htu : G.Adj t u)
    (htb : G.Adj t (C.b (C.next i)))
    (hta : G.Adj t (C.a (C.next i))) :
    C.b i = C.b (C.next (C.next i)) ∨ ¬G.Adj t (C.b i) := by
  by_cases heq : C.b i = C.b (C.next (C.next i))
  · exact Or.inl heq
  · refine Or.inr ?_
    have hidx : C.prev i ≠ C.next i := by
      intro hidx
      have hn := congrArg C.next hidx
      rw [C.next_prev i] at hn
      exact heq (congrArg C.b hn)
    have ht_aprev : ¬G.Adj t (C.a (C.prev i)) := by
      intro htaprev
      have hape_u : C.a (C.prev i) ≠ u := by
        rcases hchoice with ⟨rfl, _⟩ | ⟨rfl, _⟩
        · intro has
          exact h.outside (has ▸ C.a_mem_carrier (C.prev i))
        · exact C.a_ne_prev i
      have hape_bnext : C.a (C.prev i) ≠ C.b (C.next i) :=
        C.color_disjoint (C.prev i) (C.next i)
      have hape_anext : C.a (C.prev i) ≠ C.a (C.next i) := by
        intro haa
        exact hidx (C.a_injective haa)
      rcases h.right_additional_neighbor hclaw hchoice htu htb hta
          (Set.mem_insert_iff.2
            (Or.inr (C.a_mem_carrier (C.prev i))))
          htaprev hape_u hape_bnext hape_anext with hbad | hbad
      · exact C.color_disjoint (C.prev i) i hbad
      · exact C.color_disjoint (C.prev i) (C.next (C.next i)) hbad
    have ht_ai : t ≠ C.a i := by
      intro htai
      exact htC (Set.mem_insert_iff.2
        (Or.inr (htai.symm ▸ C.a_mem_carrier i)))
    have ht_aprev_ne : t ≠ C.a (C.prev i) := by
      intro htaprev
      exact htC (Set.mem_insert_iff.2
        (Or.inr (htaprev.symm ▸ C.a_mem_carrier (C.prev i))))
    have ht_s : t ≠ s := by
      intro hts
      exact htC (Set.mem_insert_iff.2 (Or.inl hts))
    intro htwrong
    rcases hchoice with ⟨rfl, htai⟩ | ⟨rfl, hts⟩
    · rcases hclaw.adjacent_to_one_of_nonadjacent_neighbors
          htwrong (C.adj_a_b i).symm (C.adj_a_prev_b i).symm
          ht_ai ht_aprev_ne (C.a_ne_prev i).symm
          (C.adj_aa i (C.prev i)) with htai' | htaprev'
      · exact htai htai'
      · exact ht_aprev htaprev'
    · have hs_aprev : s ≠ C.a (C.prev i) := by
        intro hsa
        exact h.outside (hsa.symm ▸ C.a_mem_carrier (C.prev i))
      rcases hclaw.adjacent_to_one_of_nonadjacent_neighbors
          htwrong h.adj_b.symm (C.adj_a_prev_b i).symm
          ht_s ht_aprev_ne hs_aprev h.not_adj_a_prev with
        hts' | htaprev'
      · exact hts hts'
      · exact ht_aprev htaprev'

/-- The four exact neighborhood alternatives in Lemma 8, written in the
alternating labeling at an arbitrary index `i`. -/
def Lemma8Cases {k : Nat} (C : EvenHoleLabeling G k)
    (s t : V) (i : Fin k) : Prop :=
  ∃ u : V, (u = s ∨ u = C.a i) ∧
    ((∀ v : V, v ∈ Set.insert s C.carrier →
        (G.Adj t v ↔
          v = C.a (C.prev i) ∨ v = C.b i ∨ v = u)) ∨
     (∀ v : V, v ∈ Set.insert s C.carrier →
        (G.Adj t v ↔
          v = C.b (C.prev i) ∨ v = C.a (C.prev i) ∨
            v = C.b i ∨ v = u)) ∨
     (∀ v : V, v ∈ Set.insert s C.carrier →
        (G.Adj t v ↔
          v = u ∨ v = C.b (C.next i) ∨
            v = C.a (C.next i))) ∨
     (∀ v : V, v ∈ Set.insert s C.carrier →
        (G.Adj t v ↔
          v = u ∨ v = C.b (C.next i) ∨
            v = C.a (C.next i) ∨
            v = C.b (C.next (C.next i))))

/-- Lemma 8 of the paper. -/
theorem CloneAt.lemma8 {k : Nat}
    {C : EvenHoleLabeling G k} {s t : V} {i : Fin k}
    (h : C.CloneAt s i) (hclaw : G.IsClawFree)
    (htC : t ∉ Set.insert s C.carrier)
    (hexact :
      (G.Adj t s ∧ ¬G.Adj t (C.a i)) ∨
      (¬G.Adj t s ∧ G.Adj t (C.a i))) :
    C.Lemma8Cases s t i := by
  obtain ⟨u, hchoice, htu, hleft | hright⟩ :=
    h.dependent_neighbor_restriction hclaw htC hexact
  have hu : u = s ∨ u = C.a i := by
    rcases hchoice with ⟨hus, _⟩ | ⟨hua, _⟩
    · exact Or.inl hus
    · exact Or.inr hua
  refine ⟨u, hu, ?_⟩
  · rcases hleft with ⟨htb, hta, hrestrict⟩
    have hopen := h.left_opposite_outer_eq_or_not_adj
      hclaw htC hchoice htu htb hta
    have hall : ∀ v : V, v ∈ Set.insert s C.carrier → G.Adj t v →
        v = u ∨ v = C.b i ∨ v = C.a (C.prev i) ∨
          v = C.b (C.prev i) := by
      intro v hvC htv
      by_cases hvu : v = u
      · exact Or.inl hvu
      by_cases hvb : v = C.b i
      · exact Or.inr (Or.inl hvb)
      by_cases hva : v = C.a (C.prev i)
      · exact Or.inr (Or.inr (Or.inl hva))
      rcases hrestrict v hvC htv hvu hvb hva with hvprev | hvnext
      · exact Or.inr (Or.inr (Or.inr hvprev))
      · rcases hopen with heq | hnot
        · exact Or.inr (Or.inr (Or.inr (hvnext.trans heq)))
        · exact (hnot (hvnext ▸ htv)).elim
    by_cases htouter : G.Adj t (C.b (C.prev i))
    · refine Or.inr (Or.inl ?_)
      intro v hvC
      constructor
      · intro htv
        rcases hall v hvC htv with hvu | hvb | hva | hvouter
        · exact Or.inr (Or.inr (Or.inr hvu))
        · exact Or.inr (Or.inr (Or.inl hvb))
        · exact Or.inr (Or.inl hva)
        · exact Or.inl hvouter
      · intro hv
        rcases hv with hvouter | hva | hvb | hvu
        · exact hvouter.symm ▸ htouter
        · exact hva.symm ▸ hta
        · exact hvb.symm ▸ htb
        · exact hvu.symm ▸ htu
    · refine Or.inl ?_
      intro v hvC
      constructor
      · intro htv
        rcases hall v hvC htv with hvu | hvb | hva | hvouter
        · exact Or.inr (Or.inr hvu)
        · exact Or.inr (Or.inl hvb)
        · exact Or.inl hva
        · exact (htouter (hvouter ▸ htv)).elim
      · intro hv
        rcases hv with hva | hvb | hvu
        · exact hva.symm ▸ hta
        · exact hvb.symm ▸ htb
        · exact hvu.symm ▸ htu
  · rcases hright with ⟨htb, hta, hrestrict⟩
    have hopen := h.right_opposite_outer_eq_or_not_adj
      hclaw htC hchoice htu htb hta
    have hall : ∀ v : V, v ∈ Set.insert s C.carrier → G.Adj t v →
        v = u ∨ v = C.b (C.next i) ∨
          v = C.a (C.next i) ∨
          v = C.b (C.next (C.next i)) := by
      intro v hvC htv
      by_cases hvu : v = u
      · exact Or.inl hvu
      by_cases hvb : v = C.b (C.next i)
      · exact Or.inr (Or.inl hvb)
      by_cases hva : v = C.a (C.next i)
      · exact Or.inr (Or.inr (Or.inl hva))
      rcases hrestrict v hvC htv hvu hvb hva with hvi | hvouter
      · rcases hopen with heq | hnot
        · exact Or.inr (Or.inr (Or.inr (hvi.trans heq)))
        · exact (hnot (hvi ▸ htv)).elim
      · exact Or.inr (Or.inr (Or.inr hvouter))
    by_cases htouter : G.Adj t (C.b (C.next (C.next i)))
    · refine Or.inr (Or.inr (Or.inr ?_))
      intro v hvC
      constructor
      · exact hall v hvC
      · intro hv
        rcases hv with hvu | hvb | hva | hvouter
        · exact hvu.symm ▸ htu
        · exact hvb.symm ▸ htb
        · exact hva.symm ▸ hta
        · exact hvouter.symm ▸ htouter
    · refine Or.inr (Or.inr (Or.inl ?_))
      intro v hvC
      constructor
      · intro htv
        rcases hall v hvC htv with hvu | hvb | hva | hvouter
        · exact Or.inl hvu
        · exact Or.inr (Or.inl hvb)
        · exact Or.inr (Or.inr hva)
        · exact (htouter (hvouter ▸ htv)).elim
      · intro hv
        rcases hv with hvu | hvb | hva
        · exact hvu.symm ▸ htu
        · exact hvb.symm ▸ htb
        · exact hva.symm ▸ hta

end EvenHoleLabeling

end SimpleGraph
