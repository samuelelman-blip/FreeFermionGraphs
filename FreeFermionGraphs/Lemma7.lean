import FreeFermionGraphs.FiveNeighborExact
import Mathlib.Data.Set.Card

/-!
# Complete neighboring-relation classification

This module assembles the cardinality-specific results into unified path and
hole statements formalising Lemma 7 of the paper.
-/

universe u v

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- Explicitly enumerate a set of cardinality five. -/
theorem exists_five_of_ncard_eq_five
    {α : Type v} {S : Set α} (hS5 : S.ncard = 5) :
    ∃ a b c d e : α,
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧
      b ≠ c ∧ b ≠ d ∧ b ≠ e ∧
      c ≠ d ∧ c ≠ e ∧ d ≠ e ∧
      S = {a, b, c, d, e} := by
  have hsucc : S.ncard = 4 + 1 := by omega
  obtain ⟨e, T, heT, hinsert, hT4⟩ :=
    (Set.ncard_eq_succ (s := S) (n := 4)).1 hsucc
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hT⟩ :=
    Set.ncard_eq_four.mp hT4
  have hae : a ≠ e := by
    intro h
    apply heT
    rw [hT, ← h]
    simp
  have hbe : b ≠ e := by
    intro h
    apply heT
    rw [hT, ← h]
    simp
  have hce : c ≠ e := by
    intro h
    apply heT
    rw [hT, ← h]
    simp
  have hde : d ≠ e := by
    intro h
    apply heT
    rw [hT, ← h]
    simp
  have hset : S = {a, b, c, d, e} := by
    rw [← hinsert, hT]
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  exact ⟨a, b, c, d, e, hab, hac, had, hae, hbc, hbd, hbe,
    hcd, hce, hde, hset⟩

/-- Explicitly enumerate a set of cardinality six. -/
theorem exists_six_of_ncard_eq_six
    {α : Type v} {S : Set α} (hS6 : S.ncard = 6) :
    ∃ a b c d e f : α,
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ a ≠ f ∧
      b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ b ≠ f ∧
      c ≠ d ∧ c ≠ e ∧ c ≠ f ∧
      d ≠ e ∧ d ≠ f ∧ e ≠ f ∧
      S = {a, b, c, d, e, f} := by
  have hsucc : S.ncard = 5 + 1 := by omega
  obtain ⟨f, T, hfT, hinsert, hT5⟩ :=
    (Set.ncard_eq_succ (s := S) (n := 5)).1 hsucc
  obtain ⟨a, b, c, d, e, hab, hac, had, hae, hbc, hbd, hbe,
    hcd, hce, hde, hT⟩ := exists_five_of_ncard_eq_five hT5
  have haf : a ≠ f := by
    intro h
    apply hfT
    rw [hT, ← h]
    simp
  have hbf : b ≠ f := by
    intro h
    apply hfT
    rw [hT, ← h]
    simp
  have hcf : c ≠ f := by
    intro h
    apply hfT
    rw [hT, ← h]
    simp
  have hdf : d ≠ f := by
    intro h
    apply hfT
    rw [hT, ← h]
    simp
  have hef : e ≠ f := by
    intro h
    apply hfT
    rw [hT, ← h]
    simp
  have hset : S = {a, b, c, d, e, f} := by
    rw [← hinsert, hT]
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  exact ⟨a, b, c, d, e, f, hab, hac, had, hae, haf,
    hbc, hbd, hbe, hbf, hcd, hce, hcf, hde, hdf, hef, hset⟩

/-- The complete list of neighboring relations between an external vertex
and an indexed induced path. -/
def IndexedInducedPath.Lemma7Cases
    (P : IndexedInducedPath G) (j : V) : Prop :=
  (P.neighborIndexSet j).ncard = 0 ∨
  ((P.neighborIndexSet j).ncard = 1 ∧
    ∀ p : Fin P.card, G.Adj j (P.vertex p) → P.IsEndpointIndex p) ∨
  ((P.neighborIndexSet j).ncard = 2 ∧
    ∀ p q : Fin P.card, p ≠ q →
      G.Adj j (P.vertex p) → G.Adj j (P.vertex q) →
      (∀ k : Fin P.card, G.Adj j (P.vertex k) → k = p ∨ k = q) →
      (G.Adj (P.vertex p) (P.vertex q) ∨
        (p.val = 0 ∧ q.val + 1 = P.card) ∨
        (q.val = 0 ∧ p.val + 1 = P.card))) ∨
  ((P.neighborIndexSet j).ncard = 3 ∧
    ∀ p q r : Fin P.card, p ≠ q → p ≠ r → q ≠ r →
      G.Adj j (P.vertex p) → G.Adj j (P.vertex q) →
      G.Adj j (P.vertex r) →
      (∀ k : Fin P.card,
        G.Adj j (P.vertex k) → k = p ∨ k = q ∨ k = r) →
      (P.ThreeNeighborPathCase p q r ∨
        P.ThreeNeighborEndpointCase p q r)) ∨
  ((P.neighborIndexSet j).ncard = 4 ∧
    ∀ p q r s : Fin P.card,
      p ≠ q → p ≠ r → p ≠ s → q ≠ r → q ≠ s → r ≠ s →
      G.Adj j (P.vertex p) → G.Adj j (P.vertex q) →
      G.Adj j (P.vertex r) → G.Adj j (P.vertex s) →
      FourNeighborDegreeShape
        (G.Adj (P.vertex p) (P.vertex q))
        (G.Adj (P.vertex p) (P.vertex r))
        (G.Adj (P.vertex p) (P.vertex s))
        (G.Adj (P.vertex q) (P.vertex r))
        (G.Adj (P.vertex q) (P.vertex s))
        (G.Adj (P.vertex r) (P.vertex s)))

/-- The complete list of neighboring relations between an external vertex
and an indexed induced hole.  The cardinality-one case is absent. -/
def IndexedInducedHole.Lemma7Cases
    (C : IndexedInducedHole G) (j : V) : Prop :=
  (C.neighborIndexSet j).ncard = 0 ∨
  ((C.neighborIndexSet j).ncard = 2 ∧
    ∀ p q : Fin C.card, p ≠ q →
      G.Adj j (C.vertex p) → G.Adj j (C.vertex q) →
      (∀ k : Fin C.card, G.Adj j (C.vertex k) → k = p ∨ k = q) →
      G.Adj (C.vertex p) (C.vertex q)) ∨
  ((C.neighborIndexSet j).ncard = 3 ∧
    ∀ p q r : Fin C.card, p ≠ q → p ≠ r → q ≠ r →
      G.Adj j (C.vertex p) → G.Adj j (C.vertex q) →
      G.Adj j (C.vertex r) →
      (∀ k : Fin C.card,
        G.Adj j (C.vertex k) → k = p ∨ k = q ∨ k = r) →
      (G.IsInducedPathTriple (C.vertex q) (C.vertex p) (C.vertex r) ∨
        G.IsInducedPathTriple (C.vertex p) (C.vertex q) (C.vertex r) ∨
        G.IsInducedPathTriple (C.vertex p) (C.vertex r) (C.vertex q))) ∨
  ((C.neighborIndexSet j).ncard = 4 ∧
    ∀ p q r s : Fin C.card,
      p ≠ q → p ≠ r → p ≠ s → q ≠ r → q ≠ s → r ≠ s →
      G.Adj j (C.vertex p) → G.Adj j (C.vertex q) →
      G.Adj j (C.vertex r) → G.Adj j (C.vertex s) →
      FourNeighborDegreeShape
        (G.Adj (C.vertex p) (C.vertex q))
        (G.Adj (C.vertex p) (C.vertex r))
        (G.Adj (C.vertex p) (C.vertex s))
        (G.Adj (C.vertex q) (C.vertex r))
        (G.Adj (C.vertex q) (C.vertex s))
        (G.Adj (C.vertex r) (C.vertex s))) ∨
  ((C.neighborIndexSet j).ncard = 5 ∧
    C.card = 5)

/-- Lemma 7 for indexed induced paths. -/
theorem IndexedInducedPath.lemma7
    (P : IndexedInducedPath G) (hclaw : G.IsClawFree) {j : V}
    (hjP : j ∉ Set.range P.vertex) : P.Lemma7Cases j := by
  have hbound : (P.neighborIndexSet j).ncard ≤ 4 := by
    by_contra h
    have hfive : 5 ≤ (P.neighborIndexSet j).ncard := by omega
    obtain ⟨T, hTS, hT5⟩ := Set.exists_subset_card_eq hfive
    obtain ⟨p, q, r, s, t, hpq, hpr, hps, hpt, hqr, hqs, hqt,
      hrs, hrt, hst, hT⟩ := exists_five_of_ncard_eq_five hT5
    have hp : p ∈ P.neighborIndexSet j := hTS (by rw [hT]; simp)
    have hq : q ∈ P.neighborIndexSet j := hTS (by rw [hT]; simp)
    have hr : r ∈ P.neighborIndexSet j := hTS (by rw [hT]; simp)
    have hs : s ∈ P.neighborIndexSet j := hTS (by rw [hT]; simp)
    have ht : t ∈ P.neighborIndexSet j := hTS (by rw [hT]; simp)
    exact P.not_five_external_neighbors hclaw hjP
      hpq hpr hps hpt hqr hqs hqt hrs hrt hst hp hq hr hs ht
  have hcases :
      (P.neighborIndexSet j).ncard = 0 ∨
      (P.neighborIndexSet j).ncard = 1 ∨
      (P.neighborIndexSet j).ncard = 2 ∨
      (P.neighborIndexSet j).ncard = 3 ∨
      (P.neighborIndexSet j).ncard = 4 := by
    omega
  rcases hcases with hzero | hone | htwo | hthree | hfour
  · exact Or.inl hzero
  · refine Or.inr (Or.inl ⟨hone, ?_⟩)
    intro p hjp
    have hp : p ∈ P.neighborIndexSet j := by simpa using hjp
    have hle : (P.neighborIndexSet j).ncard ≤ 1 := by omega
    have hunique : ∀ k : Fin P.card,
        G.Adj j (P.vertex k) → k = p := by
      intro k hjk
      have hk : k ∈ P.neighborIndexSet j := by simpa using hjk
      exact (Set.ncard_le_one.mp hle) k hk p hp
    exact P.unique_external_neighbor_is_endpoint hclaw hjP hjp hunique
  · refine Or.inr (Or.inr (Or.inl ⟨htwo, ?_⟩))
    intro p q hpq hjp hjq hexact
    exact P.two_external_neighbors_classification
      hclaw hjP hpq hjp hjq hexact
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨hthree, ?_⟩)))
    intro p q r hpq hpr hqr hjp hjq hjr hexact
    exact P.three_external_neighbors_classification
      hclaw hjP hpq hpr hqr hjp hjq hjr hexact
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨hfour, ?_⟩)))
    intro p q r s hpq hpr hps hqr hqs hrs hjp hjq hjr hjs
    exact P.four_external_neighbors_degree_shape
      hclaw hjP hpq hpr hps hqr hqs hrs hjp hjq hjr hjs

/-- Lemma 7 for indexed induced holes. -/
theorem IndexedInducedHole.lemma7
    (C : IndexedInducedHole G) (hclaw : G.IsClawFree) {j : V}
    (hjC : j ∉ Set.range C.vertex) : C.Lemma7Cases j := by
  have hbound : (C.neighborIndexSet j).ncard ≤ 5 := by
    by_contra h
    have hsix : 6 ≤ (C.neighborIndexSet j).ncard := by omega
    obtain ⟨T, hTS, hT6⟩ := Set.exists_subset_card_eq hsix
    obtain ⟨p, q, r, s, t, u, hpq, hpr, hps, hpt, hpu,
      hqr, hqs, hqt, hqu, hrs, hrt, hru, hst, hsu, htu, hT⟩ :=
      exists_six_of_ncard_eq_six hT6
    have hp : p ∈ C.neighborIndexSet j := hTS (by rw [hT]; simp)
    have hq : q ∈ C.neighborIndexSet j := hTS (by rw [hT]; simp)
    have hr : r ∈ C.neighborIndexSet j := hTS (by rw [hT]; simp)
    have hs : s ∈ C.neighborIndexSet j := hTS (by rw [hT]; simp)
    have ht : t ∈ C.neighborIndexSet j := hTS (by rw [hT]; simp)
    have hu : u ∈ C.neighborIndexSet j := hTS (by rw [hT]; simp)
    exact C.not_six_external_neighbors hclaw hjC
      hpq hpr hps hpt hpu hqr hqs hqt hqu hrs hrt hru hst hsu htu
      hp hq hr hs ht hu
  have hcases :
      (C.neighborIndexSet j).ncard = 0 ∨
      (C.neighborIndexSet j).ncard = 1 ∨
      (C.neighborIndexSet j).ncard = 2 ∨
      (C.neighborIndexSet j).ncard = 3 ∨
      (C.neighborIndexSet j).ncard = 4 ∨
      (C.neighborIndexSet j).ncard = 5 := by
    omega
  rcases hcases with hzero | hone | htwo | hthree | hfour | hfive
  · exact Or.inl hzero
  · obtain ⟨p, hset⟩ := Set.ncard_eq_one.mp hone
    have hp : p ∈ C.neighborIndexSet j := by rw [hset]; simp
    have hle : (C.neighborIndexSet j).ncard ≤ 1 := by omega
    have hunique : ∀ k : Fin C.card,
        G.Adj j (C.vertex k) → k = p := by
      intro k hjk
      have hk : k ∈ C.neighborIndexSet j := by simpa using hjk
      exact (Set.ncard_le_one.mp hle) k hk p hp
    exact ((C.not_unique_external_neighbor hclaw hjC p hp) hunique).elim
  · refine Or.inr (Or.inl ⟨htwo, ?_⟩)
    intro p q hpq hjp hjq hexact
    exact C.two_external_neighbors_are_adjacent
      hclaw hjC hpq hjp hjq hexact
  · refine Or.inr (Or.inr (Or.inl ⟨hthree, ?_⟩))
    intro p q r hpq hpr hqr hjp hjq hjr hexact
    exact C.three_external_neighbors_induce_path
      hclaw hjC hpq hpr hqr hjp hjq hjr hexact
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨hfour, ?_⟩)))
    intro p q r s hpq hpr hps hqr hqs hrs hjp hjq hjr hjs
    exact C.four_external_neighbors_degree_shape
      hclaw hjC hpq hpr hps hqr hqs hrs hjp hjq hjr hjs
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨hfive, ?_⟩)))
    obtain ⟨p, q, r, s, t, hpq, hpr, hps, hpt, hqr, hqs, hqt,
      hrs, hrt, hst, hset⟩ := exists_five_of_ncard_eq_five hfive
    have hp : p ∈ C.neighborIndexSet j := by rw [hset]; simp
    have hq : q ∈ C.neighborIndexSet j := by rw [hset]; simp
    have hr : r ∈ C.neighborIndexSet j := by rw [hset]; simp
    have hs : s ∈ C.neighborIndexSet j := by rw [hset]; simp
    have ht : t ∈ C.neighborIndexSet j := by rw [hset]; simp
    exact C.five_external_neighbors_force_card_five hclaw hjC
      hpq hpr hps hpt hqr hqs hqt hrs hrt hst hp hq hr hs ht

end SimpleGraph
