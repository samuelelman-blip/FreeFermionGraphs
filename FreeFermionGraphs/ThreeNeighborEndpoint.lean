import FreeFermionGraphs.ThreeNeighbors

/-!
# Complete three-neighbor classification for induced paths

This module adds the endpoint exception in case (b.iv) of Lemma 7 and
combines it with the induced-three-vertex-path case (b.i).
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- An endpoint index of an indexed induced path. -/
def IndexedInducedPath.IsEndpointIndex
    (P : IndexedInducedPath G) (i : Fin P.card) : Prop :=
  i.val = 0 ∨ i.val + 1 = P.card

theorem IndexedInducedPath.isInteriorIndex_iff_not_isEndpointIndex
    (P : IndexedInducedPath G) (i : Fin P.card) :
    P.IsInteriorIndex i ↔ ¬P.IsEndpointIndex i := by
  simp only [IsInteriorIndex, IsEndpointIndex, not_or]

/-- The three external neighbors form an induced path of length two. -/
def IndexedInducedPath.ThreeNeighborPathCase
    (P : IndexedInducedPath G) (p q r : Fin P.card) : Prop :=
  G.IsInducedPathTriple (P.vertex q) (P.vertex p) (P.vertex r) ∨
    G.IsInducedPathTriple (P.vertex p) (P.vertex q) (P.vertex r) ∨
    G.IsInducedPathTriple (P.vertex p) (P.vertex r) (P.vertex q)

/-- One external neighbor is a path endpoint and the other two are
adjacent, the exceptional configuration in case (b.iv). -/
def IndexedInducedPath.ThreeNeighborEndpointCase
    (P : IndexedInducedPath G) (p q r : Fin P.card) : Prop :=
  (P.IsEndpointIndex p ∧ G.Adj (P.vertex q) (P.vertex r)) ∨
    (P.IsEndpointIndex q ∧ G.Adj (P.vertex p) (P.vertex r)) ∨
    (P.IsEndpointIndex r ∧ G.Adj (P.vertex p) (P.vertex q))

/-- Complete cardinality-three path case of Lemma 7.  Three exact external
neighbors either induce a path of length two or consist of an endpoint and
an adjacent pair. -/
theorem IndexedInducedPath.three_external_neighbors_classification
    (P : IndexedInducedPath G) (hclaw : G.IsClawFree) {j : V}
    (hjP : j ∉ Set.range P.vertex) {p q r : Fin P.card}
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hjp : G.Adj j (P.vertex p)) (hjq : G.Adj j (P.vertex q))
    (hjr : G.Adj j (P.vertex r))
    (hexact : ∀ k : Fin P.card,
      G.Adj j (P.vertex k) → k = p ∨ k = q ∨ k = r) :
    P.ThreeNeighborPathCase p q r ∨ P.ThreeNeighborEndpointCase p q r := by
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
  rcases hclaw hjp hjq hjr hpq_vertices hpr_vertices hqr_vertices with
    hpq_adj | hpr_adj | hqr_adj
  · by_cases hr_endpoint : P.IsEndpointIndex r
    · exact Or.inr (Or.inr (Or.inr ⟨hr_endpoint, hpq_adj⟩))
    · have hr_int : P.IsInteriorIndex r :=
        (P.isInteriorIndex_iff_not_isEndpointIndex r).2 hr_endpoint
      obtain ⟨k, hkr, hrk, hjk⟩ :=
        P.interior_external_neighbor_hits_path_neighbor
          hclaw hjP r hjr hr_int.1 hr_int.2
      rcases hexact k hjk with hkp | hkq | hkr'
      · subst k
        exact Or.inl (Or.inl (center_p hpq_adj hrk.symm))
      · subst k
        exact Or.inl (Or.inr (Or.inl (center_q hpq_adj hrk.symm)))
      · exact (hkr hkr').elim
  · by_cases hq_endpoint : P.IsEndpointIndex q
    · exact Or.inr (Or.inr (Or.inl ⟨hq_endpoint, hpr_adj⟩))
    · have hq_int : P.IsInteriorIndex q :=
        (P.isInteriorIndex_iff_not_isEndpointIndex q).2 hq_endpoint
      obtain ⟨k, hkq, hqk, hjk⟩ :=
        P.interior_external_neighbor_hits_path_neighbor
          hclaw hjP q hjq hq_int.1 hq_int.2
      rcases hexact k hjk with hkp | hkq' | hkr
      · subst k
        exact Or.inl (Or.inl (center_p hqk.symm hpr_adj))
      · exact (hkq hkq').elim
      · subst k
        exact Or.inl (Or.inr (Or.inr (center_r hpr_adj hqk.symm)))
  · by_cases hp_endpoint : P.IsEndpointIndex p
    · exact Or.inr (Or.inl ⟨hp_endpoint, hqr_adj⟩)
    · have hp_int : P.IsInteriorIndex p :=
        (P.isInteriorIndex_iff_not_isEndpointIndex p).2 hp_endpoint
      obtain ⟨k, hkp, hpk, hjk⟩ :=
        P.interior_external_neighbor_hits_path_neighbor
          hclaw hjP p hjp hp_int.1 hp_int.2
      rcases hexact k hjk with hkp' | hkq | hkr
      · exact (hkp hkp').elim
      · subst k
        exact Or.inl (Or.inr (Or.inl (center_q hpk hqr_adj)))
      · subst k
        exact Or.inl (Or.inr (Or.inr (center_r hpk hqr_adj.symm)))

end SimpleGraph
