import FreeFermionGraphs.Lemma7

/-!
# Corollaries 2 and 3

Paper-facing statements of the two local consequences following Lemma 7.
Both results hold without the parity assumption on the hole used in the
paper, and Corollary 3 only needs the displayed induced three-vertex path.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- Corollary 2 of the paper: if an external vertex `j` neighbors a vertex
`k` of an indexed hole, then `j` also neighbors a cycle neighbor of `k`.

The paper applies this to even holes; the proof only uses claw-freeness and
the fact that a hole vertex has two distinct nonadjacent cycle neighbors. -/
theorem IndexedInducedHole.corollary2
    (C : IndexedInducedHole G) (hclaw : G.IsClawFree) {j : V}
    (hjC : j ∉ Set.range C.vertex) {k : Fin C.card}
    (hjk : G.Adj j (C.vertex k)) :
    ∃ u : Fin C.card,
      G.Adj (C.vertex k) (C.vertex u) ∧ G.Adj j (C.vertex u) := by
  obtain ⟨u, v, _huv, hku, hkv, _huv_nonadj, hju | hjv⟩ :=
    C.external_neighbor_hits_cycle_neighbor hclaw hjC k hjk
  · exact ⟨u, hku, hju⟩
  · exact ⟨v, hkv, hjv⟩

/-- Corollary 3 of the paper: if `j` neighbors every vertex of the induced
path `k₀-k₁-k₂` and also neighbors `u`, then `u` neighbors at least one of
the two endpoints.

The conclusion only needs `u` to be distinct from the endpoints; membership
of all four displayed vertices in a larger induced path or hole is not used. -/
theorem IsClawFree.corollary3
    (hclaw : G.IsClawFree) {j k₀ k₁ k₂ u : V}
    (hpath : G.IsInducedPathTriple k₀ k₁ k₂)
    (hjk₀ : G.Adj j k₀) (hjk₁ : G.Adj j k₁) (hjk₂ : G.Adj j k₂)
    (hju : G.Adj j u) (huk₀ : u ≠ k₀) (huk₂ : u ≠ k₂) :
    G.Adj u k₀ ∨ G.Adj u k₂ :=
  corollary3_additional_neighbor
    hclaw hpath hjk₀ hjk₁ hjk₂ hju huk₀ huk₂

end SimpleGraph
