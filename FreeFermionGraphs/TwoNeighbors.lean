import FreeFermionGraphs.ExternalNeighbors

/-!
# Two external neighbors of induced paths and holes

The cardinality-two cases in the neighboring-relation classification of
Lemma 7.  Two neighbors on a hole must be adjacent.  Two neighbors on a path
must be adjacent unless they are the two endpoints.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- If an external vertex neighbors an interior vertex of an induced path,
it also neighbors either the predecessor or the successor of that vertex. -/
theorem IndexedInducedPath.interior_external_neighbor_hits_path_neighbor
    (P : IndexedInducedPath G) (hclaw : G.IsClawFree) {j : V}
    (hjP : j ∉ Set.range P.vertex) (i : Fin P.card)
    (hji : G.Adj j (P.vertex i))
    (hfirst : i.val ≠ 0) (hlast : i.val + 1 ≠ P.card) :
    ∃ k : Fin P.card, k ≠ i ∧
      G.Adj (P.vertex i) (P.vertex k) ∧ G.Adj j (P.vertex k) := by
  have hi : i.val < P.card := i.isLt
  let p : Fin P.card := ⟨i.val - 1, by omega⟩
  let q : Fin P.card := ⟨i.val + 1, by omega⟩
  have hip : G.Adj (P.vertex i) (P.vertex p) := by
    apply (P.adj_iff i p).2
    right
    dsimp [p]
    omega
  have hiq : G.Adj (P.vertex i) (P.vertex q) := by
    apply (P.adj_iff i q).2
    left
    rfl
  have hpq : p ≠ q := by
    intro h
    have hval := congrArg Fin.val h
    dsimp [p, q] at hval
    omega
  have hpq_vertices : P.vertex p ≠ P.vertex q := by
    intro h
    exact hpq (P.injective h)
  have hpq_nonadj : ¬G.Adj (P.vertex p) (P.vertex q) := by
    intro h
    rcases (P.adj_iff p q).1 h with h | h
    · dsimp [p, q] at h
      omega
    · dsimp [p, q] at h
      omega
  have hjp : j ≠ P.vertex p := by
    intro h
    exact hjP ⟨p, h.symm⟩
  have hjq : j ≠ P.vertex q := by
    intro h
    exact hjP ⟨q, h.symm⟩
  have hj := hclaw.adjacent_to_one_of_nonadjacent_neighbors
    hji hip hiq hjp hjq hpq_vertices hpq_nonadj
  rcases hj with hjp_adj | hjq_adj
  · refine ⟨p, ?_, hip, hjp_adj⟩
    intro h
    have hval := congrArg Fin.val h
    dsimp [p] at hval
    omega
  · refine ⟨q, ?_, hiq, hjq_adj⟩
    intro h
    have hval := congrArg Fin.val h
    dsimp [q] at hval
    omega

/-- The two-neighbor hole case of Lemma 7: if `p` and `q` are exactly the
neighbors of an external vertex on a hole, then `p` and `q` are adjacent. -/
theorem IndexedInducedHole.two_external_neighbors_are_adjacent
    (C : IndexedInducedHole G) (hclaw : G.IsClawFree) {j : V}
    (hjC : j ∉ Set.range C.vertex) {p q : Fin C.card}
    (_hpq : p ≠ q) (hjp : G.Adj j (C.vertex p))
    (_hjq : G.Adj j (C.vertex q))
    (hexact : ∀ k : Fin C.card,
      G.Adj j (C.vertex k) → k = p ∨ k = q) :
    G.Adj (C.vertex p) (C.vertex q) := by
  obtain ⟨a, b, hab, hpa, hpb, hab_nonadj, hj⟩ :=
    C.external_neighbor_hits_cycle_neighbor hclaw hjC p hjp
  rcases hj with hja | hjb
  · rcases hexact a hja with hap | haq
    · subst a
      exact (hpa.ne rfl).elim
    · subst a
      exact hpa
  · rcases hexact b hjb with hbp | hbq
    · subst b
      exact (hpb.ne rfl).elim
    · subst b
      exact hpb

/-- The two-neighbor path case of Lemma 7: two exact external neighbors are
adjacent, unless they are the two endpoints of the path. -/
theorem IndexedInducedPath.two_external_neighbors_classification
    (P : IndexedInducedPath G) (hclaw : G.IsClawFree) {j : V}
    (hjP : j ∉ Set.range P.vertex) {p q : Fin P.card}
    (hpq : p ≠ q) (hjp : G.Adj j (P.vertex p))
    (hjq : G.Adj j (P.vertex q))
    (hexact : ∀ k : Fin P.card,
      G.Adj j (P.vertex k) → k = p ∨ k = q) :
    G.Adj (P.vertex p) (P.vertex q) ∨
      (p.val = 0 ∧ q.val + 1 = P.card) ∨
      (q.val = 0 ∧ p.val + 1 = P.card) := by
  by_cases hp_endpoint : p.val = 0 ∨ p.val + 1 = P.card
  · by_cases hq_endpoint : q.val = 0 ∨ q.val + 1 = P.card
    · rcases hp_endpoint with hp_first | hp_last
      · rcases hq_endpoint with hq_first | hq_last
        · have h : p = q := by
            apply Fin.ext
            omega
          exact (hpq h).elim
        · exact Or.inr (Or.inl ⟨hp_first, hq_last⟩)
      · rcases hq_endpoint with hq_first | hq_last
        · exact Or.inr (Or.inr ⟨hq_first, hp_last⟩)
        · have h : p = q := by
            apply Fin.ext
            omega
          exact (hpq h).elim
    · have hq_first : q.val ≠ 0 := by
        intro h
        exact hq_endpoint (Or.inl h)
      have hq_last : q.val + 1 ≠ P.card := by
        intro h
        exact hq_endpoint (Or.inr h)
      obtain ⟨k, hkq, hqk, hjk⟩ :=
        P.interior_external_neighbor_hits_path_neighbor
          hclaw hjP q hjq hq_first hq_last
      rcases hexact k hjk with hkp | hkq'
      · subst k
        exact Or.inl hqk.symm
      · exact (hkq hkq').elim
  · have hp_first : p.val ≠ 0 := by
      intro h
      exact hp_endpoint (Or.inl h)
    have hp_last : p.val + 1 ≠ P.card := by
      intro h
      exact hp_endpoint (Or.inr h)
    obtain ⟨k, hkp, hpk, hjk⟩ :=
      P.interior_external_neighbor_hits_path_neighbor
        hclaw hjP p hjp hp_first hp_last
    rcases hexact k hjk with hkp' | hkq
    · exact (hkp hkp').elim
    · subst k
      exact Or.inl hpk

end SimpleGraph
