import FreeFermionGraphs.ClawFree

/-!
# Neighboring relations in claw-free graphs

Local graph-theoretic facts underlying Lemma 7 and Corollaries 2-3 of the
paper.  They isolate the claw arguments from the later representations of
induced paths and holes.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- Three vertices form an induced path of length two in `G`.  The explicit
endpoint inequality rules out the degenerate closed walk. -/
def IsInducedPathTriple (G : SimpleGraph V) (k₀ k₁ k₂ : V) : Prop :=
  G.Adj k₀ k₁ ∧ G.Adj k₁ k₂ ∧ ¬G.Adj k₀ k₂ ∧ k₀ ≠ k₂

/-- The local claw argument used throughout the neighboring-relation
classification: if `j` is adjacent to `k`, and `u` and `v` are distinct
nonadjacent neighbors of `k`, then `j` must be adjacent to `u` or `v`.

In applications, `k`, `u`, and `v` lie on an induced path or hole and `j`
lies outside it. -/
theorem IsClawFree.adjacent_to_one_of_nonadjacent_neighbors
    (hclaw : G.IsClawFree) {j k u v : V}
    (hjk : G.Adj j k) (hku : G.Adj k u) (hkv : G.Adj k v)
    (hju : j ≠ u) (hjv : j ≠ v) (huv : u ≠ v)
    (huv_nonadj : ¬G.Adj u v) :
    G.Adj j u ∨ G.Adj j v := by
  rcases hclaw hjk.symm hku hkv hju hjv huv with hju' | hjv' | huv'
  · exact Or.inl hju'
  · exact Or.inr hjv'
  · exact (huv_nonadj huv').elim

/-- Corollary 2 of the paper, with the two cycle neighbors made explicit.
If `j` lies outside `C` and is adjacent to `k`, then it is adjacent to at
least one of two distinct nonadjacent neighbors of `k` in `C`.

For a hole, the predecessor and successor of `k` supply `u` and `v`. -/
theorem corollary2_hole_neighbor
    (hclaw : G.IsClawFree) {C : Set V} {j k u v : V}
    (hjC : j ∉ C) (hkC : k ∈ C) (huC : u ∈ C) (hvC : v ∈ C)
    (hjk : G.Adj j k) (hku : G.Adj k u) (hkv : G.Adj k v)
    (huv : u ≠ v) (huv_nonadj : ¬G.Adj u v) :
    G.Adj j u ∨ G.Adj j v := by
  have hju : j ≠ u := by
    intro h
    subst j
    exact hjC huC
  have hjv : j ≠ v := by
    intro h
    subst j
    exact hjC hvC
  exact hclaw.adjacent_to_one_of_nonadjacent_neighbors
    hjk hku hkv hju hjv huv huv_nonadj

/-- Corollary 3 of the paper.  If `j` is adjacent to all three vertices of
an induced path `k₀-k₁-k₂` and also to an additional vertex `u`, then `u`
must be adjacent to at least one endpoint of that path.

The inequalities say precisely that `u` is an additional neighbor rather
than one of the two endpoints. -/
theorem corollary3_additional_neighbor
    (hclaw : G.IsClawFree) {j k₀ k₁ k₂ u : V}
    (hpath : G.IsInducedPathTriple k₀ k₁ k₂)
    (hjk₀ : G.Adj j k₀) (_hjk₁ : G.Adj j k₁) (hjk₂ : G.Adj j k₂)
    (hju : G.Adj j u) (huk₀ : u ≠ k₀) (huk₂ : u ≠ k₂) :
    G.Adj u k₀ ∨ G.Adj u k₂ := by
  rcases hclaw hjk₀ hjk₂ hju hpath.2.2.2 huk₀.symm huk₂.symm with
    hk₀k₂ | hk₀u | hk₂u
  · exact (hpath.2.2.1 hk₀k₂).elim
  · exact Or.inl hk₀u.symm
  · exact Or.inr hk₂u.symm

end SimpleGraph
