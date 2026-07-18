import FreeFermionGraphs.Lemma11BColoring

/-!
# Lemma 11(b): base step of the local descent

The recursive argument in Lemma 11(b) cannot stop at the first deformation
step with a commuting dependent vertex.  At that step the dependent vertex
is adjacent to the initial endpoint of the active path and to no other path
vertex.  Its path-adjacency count is therefore one, so the corresponding
term anticommutes with the path product.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace IndexedInducedPath

/-- The path begins at the displayed vertex. -/
def StartsAt (P : IndexedInducedPath G) (v : V) : Prop :=
  ∃ i : Fin P.card, i.val = 0 ∧ P.vertex i = v

/-- A vertex with exactly one neighbor on an indexed path anticommutes with
the path product. -/
theorem anticommutesWith_of_unique_neighbor
    (P : IndexedInducedPath G) {u : V} {i : Fin P.card}
    (hui : G.Adj u (P.vertex i))
    (hunique : ∀ q : Fin P.card,
      G.Adj u (P.vertex q) → q = i) :
    P.AnticommutesWith u := by
  have hset : P.neighborIndexSet u = ({i} : Set (Fin P.card)) := by
    ext q
    simp only [mem_neighborIndexSet, Set.mem_singleton_iff]
    constructor
    · exact hunique q
    · intro hqi
      subst q
      exact hui
  apply (P.anticommutesWith_iff_neighborIndexSet_mod_eq_one u).2
  rw [hset]
  simp

/-- A dependent vertex whose only path neighbor is the initial vertex
anticommutes with the path.  This is the base case used by the strict
descent in Lemma 11(b). -/
theorem dependent_at_start_anticommutes
    (P : IndexedInducedPath G)
    {Cprime : Set V} {introduced removed u : V}
    (hu : u ∈ G.dependentSubset Cprime introduced removed)
    (hstart : P.StartsAt introduced)
    (hunique : ∀ q : Fin P.card,
      G.Adj u (P.vertex q) → P.vertex q = introduced) :
    P.AnticommutesWith u := by
  obtain ⟨i, _hi0, hi⟩ := hstart
  have hui : G.Adj u (P.vertex i) := by
    simpa [hi] using hu.2.1
  have huniqueIndex : ∀ q : Fin P.card,
      G.Adj u (P.vertex q) → q = i := by
    intro q huq
    apply P.injective
    calc
      P.vertex q = introduced := hunique q huq
      _ = P.vertex i := hi.symm
  exact P.anticommutesWith_of_unique_neighbor hui huniqueIndex

/-- Equivalent commuting formulation of the base case: no such first-step
dependent vertex can commute with the active path. -/
theorem dependent_at_start_not_commutes
    (P : IndexedInducedPath G)
    {Cprime : Set V} {introduced removed u : V}
    (hu : u ∈ G.dependentSubset Cprime introduced removed)
    (hstart : P.StartsAt introduced)
    (hunique : ∀ q : Fin P.card,
      G.Adj u (P.vertex q) → P.vertex q = introduced) :
    ¬P.CommutesWith u := by
  exact (P.anticommutesWith_iff_not_commutesWith u).1
    (P.dependent_at_start_anticommutes hu hstart hunique)

end IndexedInducedPath

end SimpleGraph
