import FreeFermionGraphs.TwoNeighbors

/-!
# Three external neighbors of induced paths and holes

The non-endpoint cardinality-three case in Lemma 7.  Three external
neighbors of a hole, or three interior external neighbors of a path, induce
a path of length two.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- Indexed induced paths contain no triangle. -/
theorem IndexedInducedPath.not_triangle
    (P : IndexedInducedPath G) (a b c : Fin P.card) :
    ¬(G.Adj (P.vertex a) (P.vertex b) ∧
      G.Adj (P.vertex b) (P.vertex c) ∧
      G.Adj (P.vertex a) (P.vertex c)) := by
  rintro ⟨hab, hbc, hac⟩
  rcases (P.adj_iff a b).1 hab with hab | hab <;>
    rcases (P.adj_iff b c).1 hbc with hbc | hbc <;>
    rcases (P.adj_iff a c).1 hac with hac | hac <;> omega

/-- Indexed holes of length at least four contain no triangle. -/
theorem IndexedInducedHole.not_triangle
    (C : IndexedInducedHole G) (a b c : Fin C.card) :
    ¬(G.Adj (C.vertex a) (C.vertex b) ∧
      G.Adj (C.vertex b) (C.vertex c) ∧
      G.Adj (C.vertex a) (C.vertex c)) := by
  rintro ⟨hab, hbc, hac⟩
  have hcard : 4 ≤ C.card := C.four_le_card
  have ha : a.val < C.card := a.isLt
  have hb : b.val < C.card := b.isLt
  have hc : c.val < C.card := c.isLt
  have hab' := (C.adj_iff a b).1 hab
  have hbc' := (C.adj_iff b c).1 hbc
  have hac' := (C.adj_iff a c).1 hac
  unfold CyclicAdjacent at hab' hbc' hac'
  rcases hab' with hab' | hab' | hab' | hab' <;>
    rcases hbc' with hbc' | hbc' | hbc' | hbc' <;>
    rcases hac' with hac' | hac' | hac' | hac' <;> omega

/-- An external neighbor of a hole vertex also neighbors an adjacent,
differently indexed hole vertex. -/
theorem IndexedInducedHole.external_neighbor_hits_adjacent_hole_neighbor
    (C : IndexedInducedHole G) (hclaw : G.IsClawFree) {j : V}
    (hjC : j ∉ Set.range C.vertex) (i : Fin C.card)
    (hji : G.Adj j (C.vertex i)) :
    ∃ k : Fin C.card, k ≠ i ∧
      G.Adj (C.vertex i) (C.vertex k) ∧ G.Adj j (C.vertex k) := by
  obtain ⟨p, q, _hpq, hip, hiq, _hpq_nonadj, hj⟩ :=
    C.external_neighbor_hits_cycle_neighbor hclaw hjC i hji
  rcases hj with hjp | hjq
  · refine ⟨p, ?_, hip, hjp⟩
    intro h
    exact hip.ne (congrArg C.vertex h.symm)
  · refine ⟨q, ?_, hiq, hjq⟩
    intro h
    exact hiq.ne (congrArg C.vertex h.symm)

/-- Three exact external neighbors of an indexed hole induce a path of
length two.  The three disjuncts identify its middle vertex. -/
theorem IndexedInducedHole.three_external_neighbors_induce_path
    (C : IndexedInducedHole G) (hclaw : G.IsClawFree) {j : V}
    (hjC : j ∉ Set.range C.vertex) {p q r : Fin C.card}
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hjp : G.Adj j (C.vertex p)) (hjq : G.Adj j (C.vertex q))
    (hjr : G.Adj j (C.vertex r))
    (hexact : ∀ k : Fin C.card,
      G.Adj j (C.vertex k) → k = p ∨ k = q ∨ k = r) :
    G.IsInducedPathTriple (C.vertex q) (C.vertex p) (C.vertex r) ∨
      G.IsInducedPathTriple (C.vertex p) (C.vertex q) (C.vertex r) ∨
      G.IsInducedPathTriple (C.vertex p) (C.vertex r) (C.vertex q) := by
  have hpq_vertices : C.vertex p ≠ C.vertex q := by
    intro h
    exact hpq (C.injective h)
  have hpr_vertices : C.vertex p ≠ C.vertex r := by
    intro h
    exact hpr (C.injective h)
  have hqr_vertices : C.vertex q ≠ C.vertex r := by
    intro h
    exact hqr (C.injective h)
  have center_p (hpq_adj : G.Adj (C.vertex p) (C.vertex q))
      (hpr_adj : G.Adj (C.vertex p) (C.vertex r)) :
      G.IsInducedPathTriple (C.vertex q) (C.vertex p) (C.vertex r) := by
    refine ⟨hpq_adj.symm, hpr_adj, ?_, hqr_vertices⟩
    intro hqr_adj
    exact C.not_triangle p q r ⟨hpq_adj, hqr_adj, hpr_adj⟩
  have center_q (hpq_adj : G.Adj (C.vertex p) (C.vertex q))
      (hqr_adj : G.Adj (C.vertex q) (C.vertex r)) :
      G.IsInducedPathTriple (C.vertex p) (C.vertex q) (C.vertex r) := by
    refine ⟨hpq_adj, hqr_adj, ?_, hpr_vertices⟩
    intro hpr_adj
    exact C.not_triangle p q r ⟨hpq_adj, hqr_adj, hpr_adj⟩
  have center_r (hpr_adj : G.Adj (C.vertex p) (C.vertex r))
      (hrq_adj : G.Adj (C.vertex r) (C.vertex q)) :
      G.IsInducedPathTriple (C.vertex p) (C.vertex r) (C.vertex q) := by
    refine ⟨hpr_adj, hrq_adj, ?_, hpq_vertices⟩
    intro hpq_adj
    exact C.not_triangle p q r ⟨hpq_adj, hrq_adj.symm, hpr_adj⟩
  obtain ⟨k, hkp, hpk, hjk⟩ :=
    C.external_neighbor_hits_adjacent_hole_neighbor hclaw hjC p hjp
  rcases hexact k hjk with hkp' | hkq | hkr
  · exact (hkp hkp').elim
  · subst k
    obtain ⟨k, hkr, hrk, hjk⟩ :=
      C.external_neighbor_hits_adjacent_hole_neighbor hclaw hjC r hjr
    rcases hexact k hjk with hkp | hkq | hkr'
    · subst k
      exact Or.inl (center_p hpk hrk.symm)
    · subst k
      exact Or.inr (Or.inl (center_q hpk hrk.symm))
    · exact (hkr hkr').elim
  · subst k
    obtain ⟨k, hkq, hqk, hjk⟩ :=
      C.external_neighbor_hits_adjacent_hole_neighbor hclaw hjC q hjq
    rcases hexact k hjk with hkp | hkq' | hkr
    · subst k
      exact Or.inl (center_p hqk.symm hpk)
    · exact (hkq hkq').elim
    · subst k
      exact Or.inr (Or.inr (center_r hpk hqk.symm))

/-- An index is interior to an indexed path when it is neither endpoint. -/
def IndexedInducedPath.IsInteriorIndex
    (P : IndexedInducedPath G) (i : Fin P.card) : Prop :=
  i.val ≠ 0 ∧ i.val + 1 ≠ P.card

/-- Three exact interior external neighbors of an indexed path induce a path
of length two. -/
theorem IndexedInducedPath.three_interior_external_neighbors_induce_path
    (P : IndexedInducedPath G) (hclaw : G.IsClawFree) {j : V}
    (hjP : j ∉ Set.range P.vertex) {p q r : Fin P.card}
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hp_int : P.IsInteriorIndex p) (hq_int : P.IsInteriorIndex q)
    (hr_int : P.IsInteriorIndex r)
    (hjp : G.Adj j (P.vertex p)) (hjq : G.Adj j (P.vertex q))
    (hjr : G.Adj j (P.vertex r))
    (hexact : ∀ k : Fin P.card,
      G.Adj j (P.vertex k) → k = p ∨ k = q ∨ k = r) :
    G.IsInducedPathTriple (P.vertex q) (P.vertex p) (P.vertex r) ∨
      G.IsInducedPathTriple (P.vertex p) (P.vertex q) (P.vertex r) ∨
      G.IsInducedPathTriple (P.vertex p) (P.vertex r) (P.vertex q) := by
  have hpq_vertices : P.vertex p ≠ P.vertex q := by
    intro h
    exact hpq (P.injective h)
  have hpr_vertices : P.vertex p ≠ P.vertex r := by
    intro h
    exact hpr (P.injective h)
  have hqr_vertices : P.vertex q ≠ P.vertex r := by
    intro h
    exact hqr (P.injective h)
  have center_p (hpq_adj : G.Adj (P.vertex p) (P.vertex q))
      (hpr_adj : G.Adj (P.vertex p) (P.vertex r)) :
      G.IsInducedPathTriple (P.vertex q) (P.vertex p) (P.vertex r) := by
    refine ⟨hpq_adj.symm, hpr_adj, ?_, hqr_vertices⟩
    intro hqr_adj
    exact P.not_triangle p q r ⟨hpq_adj, hqr_adj, hpr_adj⟩
  have center_q (hpq_adj : G.Adj (P.vertex p) (P.vertex q))
      (hqr_adj : G.Adj (P.vertex q) (P.vertex r)) :
      G.IsInducedPathTriple (P.vertex p) (P.vertex q) (P.vertex r) := by
    refine ⟨hpq_adj, hqr_adj, ?_, hpr_vertices⟩
    intro hpr_adj
    exact P.not_triangle p q r ⟨hpq_adj, hqr_adj, hpr_adj⟩
  have center_r (hpr_adj : G.Adj (P.vertex p) (P.vertex r))
      (hrq_adj : G.Adj (P.vertex r) (P.vertex q)) :
      G.IsInducedPathTriple (P.vertex p) (P.vertex r) (P.vertex q) := by
    refine ⟨hpr_adj, hrq_adj, ?_, hpq_vertices⟩
    intro hpq_adj
    exact P.not_triangle p q r ⟨hpq_adj, hrq_adj.symm, hpr_adj⟩
  obtain ⟨k, hkp, hpk, hjk⟩ :=
    P.interior_external_neighbor_hits_path_neighbor
      hclaw hjP p hjp hp_int.1 hp_int.2
  rcases hexact k hjk with hkp' | hkq | hkr
  · exact (hkp hkp').elim
  · subst k
    obtain ⟨k, hkr, hrk, hjk⟩ :=
      P.interior_external_neighbor_hits_path_neighbor
        hclaw hjP r hjr hr_int.1 hr_int.2
    rcases hexact k hjk with hkp | hkq | hkr'
    · subst k
      exact Or.inl (center_p hpk hrk.symm)
    · subst k
      exact Or.inr (Or.inl (center_q hpk hrk.symm))
    · exact (hkr hkr').elim
  · subst k
    obtain ⟨k, hkq, hqk, hjk⟩ :=
      P.interior_external_neighbor_hits_path_neighbor
        hclaw hjP q hjq hq_int.1 hq_int.2
    rcases hexact k hjk with hkp | hkq' | hkr
    · subst k
      exact Or.inl (center_p hqk.symm hpk)
    · exact (hkq hkq').elim
    · subst k
      exact Or.inr (Or.inr (center_r hpk hqk.symm))

end SimpleGraph
