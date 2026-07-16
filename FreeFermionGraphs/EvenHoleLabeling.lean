import FreeFermionGraphs.Deformation

/-!
# Alternating labels on even holes

An order-sensitive interface for the paper's labeling

`b₀-a₀-b₁-a₁-⋯-bₖ₋₁-aₖ₋₁-b₀`.

The local forced-neighbor theorem at the end is the first half of Lemma 8:
a vertex dependent on a single-vertex deformation must contain one of the
two displayed three-vertex arms in its neighborhood.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- Alternating `a`/`b` labels for an even induced cycle.  The maps `next`
and `prev` encode addition and subtraction modulo `k`.  The adjacency fields
say that the only cross-color edges are `a i-b i` and `a i-b (next i)`;
each color class is independent. -/
structure EvenHoleLabeling (G : SimpleGraph V) (k : Nat) where
  two_le : 2 ≤ k
  a : Fin k → V
  b : Fin k → V
  next : Fin k → Fin k
  prev : Fin k → Fin k
  next_ne : ∀ i, next i ≠ i
  next_next_ne : 2 < k → ∀ i, next (next i) ≠ i
  next_prev : ∀ i, next (prev i) = i
  prev_next : ∀ i, prev (next i) = i
  a_injective : Function.Injective a
  b_injective : Function.Injective b
  color_disjoint : ∀ i j, a i ≠ b j
  adj_aa : ∀ i j, ¬G.Adj (a i) (a j)
  adj_bb : ∀ i j, ¬G.Adj (b i) (b j)
  adj_ab_iff : ∀ i j,
    G.Adj (a i) (b j) ↔ j = i ∨ j = next i

namespace EvenHoleLabeling

/-- The vertex carrier of an alternating even-hole labeling. -/
def carrier {k : Nat} (C : EvenHoleLabeling G k) : Set V :=
  Set.range C.a ∪ Set.range C.b

@[simp]
theorem a_mem_carrier {k : Nat} (C : EvenHoleLabeling G k)
    (i : Fin k) : C.a i ∈ C.carrier := by
  exact Or.inl ⟨i, rfl⟩

@[simp]
theorem b_mem_carrier {k : Nat} (C : EvenHoleLabeling G k)
    (i : Fin k) : C.b i ∈ C.carrier := by
  exact Or.inr ⟨i, rfl⟩

theorem prev_ne {k : Nat} (C : EvenHoleLabeling G k) (i : Fin k) :
    C.prev i ≠ i := by
  intro h
  have hn := congrArg C.next h
  rw [C.next_prev i] at hn
  exact C.next_ne i hn.symm

theorem prev_ne_next {k : Nat} (C : EvenHoleLabeling G k)
    (hk : 2 < k) (i : Fin k) : C.prev i ≠ C.next i := by
  intro h
  have hn := congrArg C.next h
  rw [C.next_prev i] at hn
  exact C.next_next_ne hk i hn.symm

theorem a_ne_next {k : Nat} (C : EvenHoleLabeling G k) (i : Fin k) :
    C.a (C.next i) ≠ C.a i := by
  intro h
  exact C.next_ne i (C.a_injective h)

theorem a_ne_prev {k : Nat} (C : EvenHoleLabeling G k) (i : Fin k) :
    C.a (C.prev i) ≠ C.a i := by
  intro h
  exact C.prev_ne i (C.a_injective h)

theorem b_ne_next {k : Nat} (C : EvenHoleLabeling G k) (i : Fin k) :
    C.b (C.next i) ≠ C.b i := by
  intro h
  exact C.next_ne i (C.b_injective h)

theorem b_prev_ne_next {k : Nat} (C : EvenHoleLabeling G k)
    (hk : 2 < k) (i : Fin k) :
    C.b (C.prev i) ≠ C.b (C.next i) := by
  intro h
  exact C.prev_ne_next hk i (C.b_injective h)

theorem b_ne_next_next {k : Nat} (C : EvenHoleLabeling G k)
    (hk : 2 < k) (i : Fin k) :
    C.b i ≠ C.b (C.next (C.next i)) := by
  intro h
  exact C.next_next_ne hk i (C.b_injective h).symm

theorem adj_a_b {k : Nat} (C : EvenHoleLabeling G k) (i : Fin k) :
    G.Adj (C.a i) (C.b i) := by
  exact (C.adj_ab_iff i i).2 (Or.inl rfl)

theorem adj_a_b_next {k : Nat} (C : EvenHoleLabeling G k)
    (i : Fin k) : G.Adj (C.a i) (C.b (C.next i)) := by
  exact (C.adj_ab_iff i (C.next i)).2 (Or.inr rfl)

theorem adj_a_prev_b {k : Nat} (C : EvenHoleLabeling G k)
    (i : Fin k) : G.Adj (C.a (C.prev i)) (C.b i) := by
  apply (C.adj_ab_iff (C.prev i) i).2
  exact Or.inr (C.next_prev i).symm

/-- The alternating-label form of `s ≺_C a i`. -/
structure CloneAt {k : Nat} (C : EvenHoleLabeling G k)
    (s : V) (i : Fin k) : Prop where
  outside : s ∉ C.carrier
  adj_iff : ∀ v : V, v ∈ C.carrier →
    (G.Adj s v ↔ v = C.a i ∨ G.Adj (C.a i) v)

theorem CloneAt.adj_original {k : Nat} {C : EvenHoleLabeling G k}
    {s : V} {i : Fin k} (h : C.CloneAt s i) :
    G.Adj s (C.a i) := by
  exact (h.adj_iff (C.a i) (C.a_mem_carrier i)).2 (Or.inl rfl)

theorem CloneAt.adj_b {k : Nat} {C : EvenHoleLabeling G k}
    {s : V} {i : Fin k} (h : C.CloneAt s i) :
    G.Adj s (C.b i) := by
  exact (h.adj_iff (C.b i) (C.b_mem_carrier i)).2
    (Or.inr (C.adj_a_b i))

theorem CloneAt.adj_b_next {k : Nat} {C : EvenHoleLabeling G k}
    {s : V} {i : Fin k} (h : C.CloneAt s i) :
    G.Adj s (C.b (C.next i)) := by
  exact (h.adj_iff (C.b (C.next i))
    (C.b_mem_carrier (C.next i))).2
      (Or.inr (C.adj_a_b_next i))

theorem CloneAt.not_adj_a_next {k : Nat} {C : EvenHoleLabeling G k}
    {s : V} {i : Fin k} (h : C.CloneAt s i) :
    ¬G.Adj s (C.a (C.next i)) := by
  intro hs
  rcases (h.adj_iff (C.a (C.next i))
      (C.a_mem_carrier (C.next i))).1 hs with hai | hai
  · exact C.a_ne_next i hai
  · exact C.adj_aa i (C.next i) hai

theorem CloneAt.not_adj_a_prev {k : Nat} {C : EvenHoleLabeling G k}
    {s : V} {i : Fin k} (h : C.CloneAt s i) :
    ¬G.Adj s (C.a (C.prev i)) := by
  intro hs
  rcases (h.adj_iff (C.a (C.prev i))
      (C.a_mem_carrier (C.prev i))).1 hs with hai | hai
  · exact C.a_ne_prev i hai
  · exact C.adj_aa i (C.prev i) hai

/-- The two base arms of Lemma 8.  If `t` is adjacent to exactly one of a
clone `s` and its original `a i`, then `t` neighbors either
`a (prev i)-b i` or `b (next i)-a (next i)`.

For `i = 0`, these are the paper's cases (i) and (iii) before deciding
whether the optional fourth neighbor is present. -/
theorem CloneAt.dependent_forces_side {k : Nat}
    {C : EvenHoleLabeling G k} {s t : V} {i : Fin k}
    (h : C.CloneAt s i) (hclaw : G.IsClawFree)
    (htC : t ∉ Set.insert s C.carrier)
    (hexact :
      (G.Adj t s ∧ ¬G.Adj t (C.a i)) ∨
      (¬G.Adj t s ∧ G.Adj t (C.a i))) :
    (G.Adj t (C.b i) ∧ G.Adj t (C.a (C.prev i))) ∨
    (G.Adj t (C.b (C.next i)) ∧ G.Adj t (C.a (C.next i))) := by
  have ht_b : ∀ q : Fin k, t ≠ C.b q := by
    intro q htq
    exact htC (Set.mem_insert_iff.2
      (Or.inr (htq.symm ▸ C.b_mem_carrier q)))
  have ht_a : ∀ q : Fin k, t ≠ C.a q := by
    intro q htq
    exact htC (Set.mem_insert_iff.2
      (Or.inr (htq.symm ▸ C.a_mem_carrier q)))
  have ht_s : t ≠ s := by
    intro hts
    exact htC (Set.mem_insert_iff.2 (Or.inl hts))
  have hs_a_prev : s ≠ C.a (C.prev i) := by
    intro hs
    exact h.outside (hs.symm ▸ C.a_mem_carrier (C.prev i))
  have hs_a_next : s ≠ C.a (C.next i) := by
    intro hs
    exact h.outside (hs.symm ▸ C.a_mem_carrier (C.next i))
  have hforce_prev :
      G.Adj t (C.b i) →
      (¬G.Adj t (C.a i) ∨ ¬G.Adj t s) →
      G.Adj t (C.a (C.prev i)) := by
    intro htb hnot
    rcases hnot with htai | hts
    · rcases hclaw.adjacent_to_one_of_nonadjacent_neighbors
          htb (C.adj_a_b i).symm (C.adj_a_prev_b i).symm
          (ht_a i) (ht_a (C.prev i)) (C.a_ne_prev i).symm
          (C.adj_aa i (C.prev i)) with htai' | htprev
      · exact (htai htai').elim
      · exact htprev
    · rcases hclaw.adjacent_to_one_of_nonadjacent_neighbors
          htb h.adj_b.symm (C.adj_a_prev_b i).symm
          ht_s (ht_a (C.prev i)) hs_a_prev
          h.not_adj_a_prev with hts' | htprev
      · exact (hts hts').elim
      · exact htprev
  have hforce_next :
      G.Adj t (C.b (C.next i)) →
      (¬G.Adj t (C.a i) ∨ ¬G.Adj t s) →
      G.Adj t (C.a (C.next i)) := by
    intro htb hnot
    rcases hnot with htai | hts
    · rcases hclaw.adjacent_to_one_of_nonadjacent_neighbors
          htb (C.adj_a_b_next i).symm
          (C.adj_a_b (C.next i)).symm
          (ht_a i) (ht_a (C.next i)) (C.a_ne_next i).symm
          (C.adj_aa i (C.next i)) with htai' | htnext
      · exact (htai htai').elim
      · exact htnext
    · rcases hclaw.adjacent_to_one_of_nonadjacent_neighbors
          htb h.adj_b_next.symm (C.adj_a_b (C.next i)).symm
          ht_s (ht_a (C.next i)) hs_a_next
          h.not_adj_a_next with hts' | htnext
      · exact (hts hts').elim
      · exact htnext
  rcases hexact with ⟨hts, htai⟩ | ⟨hts, htai⟩
  · have hb : G.Adj t (C.b i) ∨ G.Adj t (C.b (C.next i)) :=
      hclaw.adjacent_to_one_of_nonadjacent_neighbors
        hts h.adj_b h.adj_b_next (ht_b i) (ht_b (C.next i))
        (C.b_ne_next i).symm (C.adj_bb i (C.next i))
    rcases hb with htb | htb
    · exact Or.inl ⟨htb, hforce_prev htb (Or.inl htai)⟩
    · exact Or.inr ⟨htb, hforce_next htb (Or.inl htai)⟩
  · have hb : G.Adj t (C.b i) ∨ G.Adj t (C.b (C.next i)) :=
      hclaw.adjacent_to_one_of_nonadjacent_neighbors
        htai (C.adj_a_b i) (C.adj_a_b_next i)
        (ht_b i) (ht_b (C.next i)) (C.b_ne_next i).symm
        (C.adj_bb i (C.next i))
    rcases hb with htb | htb
    · exact Or.inl ⟨htb, hforce_prev htb (Or.inr hts)⟩
    · exact Or.inr ⟨htb, hforce_next htb (Or.inr hts)⟩

end EvenHoleLabeling

end SimpleGraph
