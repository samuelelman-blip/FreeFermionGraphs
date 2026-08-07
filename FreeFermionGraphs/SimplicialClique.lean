import FreeFermionGraphs.ClawFree
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Simplicial cliques

This module records the graph-theoretic part of the manuscript definition of a
simplicial clique and the clique `K_j` used in Lemma 17.

For a clique `Ks`, simpliciality means that for each `j ∈ Ks`, the neighbors of
`j` outside `Ks` form a clique.  The manuscript then sets

`K_j = Γ[j] \ (Ks \ {j})`,

where `Γ[j]` is the closed neighborhood.  For `j ∈ Ks`, this is exactly `j`
together with the neighbors of `j` outside `Ks`.
-/

open Set

universe u

variable {V : Type u}

namespace SimpleGraph

/-- Manuscript definition of a simplicial clique. -/
def IsSimplicialClique (G : SimpleGraph V) (Ks : Set V) : Prop :=
  G.IsClique Ks ∧
    ∀ ⦃j : V⦄, j ∈ Ks → G.IsClique (G.neighborSet j \ Ks)

namespace IsSimplicialClique

variable {G : SimpleGraph V} {Ks : Set V}

/-- A simplicial clique is, in particular, a clique. -/
theorem isClique (hKs : G.IsSimplicialClique Ks) : G.IsClique Ks :=
  hKs.1

/-- The neighbors of one simplicial-clique vertex outside the simplicial
clique form a clique. -/
theorem externalNeighbors_isClique
    (hKs : G.IsSimplicialClique Ks) {j : V} (hj : j ∈ Ks) :
    G.IsClique (G.neighborSet j \ Ks) :=
  hKs.2 hj

end IsSimplicialClique

/-- Closed neighborhood `Γ[j]` in the manuscript notation. -/
def closedNeighborhood (G : SimpleGraph V) (j : V) : Set V :=
  insert j (G.neighborSet j)

/-- The clique `K_j = Γ[j] \ (Ks \ {j})` from manuscript Lemma 17. -/
def lemma17CliqueAt (G : SimpleGraph V) (Ks : Set V) (j : V) : Set V :=
  G.closedNeighborhood j \ (Ks \ {j})

/-- For a vertex of `Ks`, the manuscript `K_j` is the vertex `j` together
with its neighbors outside `Ks`. -/
theorem lemma17CliqueAt_eq_insert_external
    {G : SimpleGraph V} {Ks : Set V} {j : V}
    (hj : j ∈ Ks) :
    G.lemma17CliqueAt Ks j = insert j (G.neighborSet j \ Ks) := by
  ext v
  by_cases hvj : v = j
  · subst v
    simp [lemma17CliqueAt, closedNeighborhood, hj]
  · simp [lemma17CliqueAt, closedNeighborhood, hvj]

/-- Simpliciality is exactly what makes each `K_j` in Lemma 17 a clique. -/
theorem lemma17CliqueAt_isClique
    {G : SimpleGraph V} {Ks : Set V}
    (hKs : G.IsSimplicialClique Ks) {j : V} (hj : j ∈ Ks) :
    G.IsClique (G.lemma17CliqueAt Ks j) := by
  rw [lemma17CliqueAt_eq_insert_external hj]
  refine (hKs.externalNeighbors_isClique hj).insert ?_
  intro v hv _hjv
  exact (G.mem_neighborSet j v).mp hv.1

/-- For `j ∈ Ks`, the paper identity `Γ[j] = Ks ∪ K_j`. -/
theorem closedNeighborhood_eq_union_lemma17CliqueAt
    {G : SimpleGraph V} {Ks : Set V}
    (hKs : G.IsSimplicialClique Ks) {j : V} (hj : j ∈ Ks) :
    G.closedNeighborhood j = Ks ∪ G.lemma17CliqueAt Ks j := by
  ext v
  constructor
  · intro hv
    by_cases hvKs : v ∈ Ks
    · exact Or.inl hvKs
    · exact Or.inr ⟨hv, by
        intro hvDiff
        exact hvKs hvDiff.1⟩
  · intro hv
    rcases hv with hvKs | hvKj
    · by_cases hvj : v = j
      · subst v
        simp [closedNeighborhood]
      · have hadj : G.Adj j v := hKs.isClique hj hvKs hvj.symm
        exact Set.mem_insert_iff.mpr (Or.inr ((G.mem_neighborSet j v).mpr hadj))
    · exact hvKj.1

end SimpleGraph
