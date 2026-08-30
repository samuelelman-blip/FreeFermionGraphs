import FreeFermionGraphs.PauliCliqueHamiltonianKrylovStep
import FreeFermionGraphs.Lemma11APathBlock
import FreeFermionGraphs.SimplicialClique

/-!
# Odd-neighbour classification for a Pauli Krylov step

Lemma 7 gives a complete finite classification of an external vertex relative
to an induced path.  Anticommutation forces odd path-neighbour parity, so only
the unique-endpoint case and the two cardinality-three cases remain.  For an
original vertex already on a clique-rooted path, anticommutation instead
forces that vertex to be the non-root terminal.

Together these alternatives partition every vertex in the exact support of
the physical-Hamiltonian commutator from `PauliCliqueHamiltonianKrylovStep`.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace IsSimplicialClique

variable {G : SimpleGraph V} {K : Set V}

/-- Adjoining the artificial root to a simplicial clique preserves
claw-freeness.  Simpliciality is essential here: at a clique vertex, the new
root and two external neighbours would otherwise be able to form a claw. -/
theorem isClawFree_adjoinRootAt
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree) :
    (G.adjoinRootAt K).IsClawFree := by
  have oneRoot
      {x y z : V} (hxK : x ∈ K)
      (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : y ≠ z) :
      y ∈ K ∨ z ∈ K ∨ G.Adj y z := by
    by_cases hyK : y ∈ K
    · exact Or.inl hyK
    by_cases hzK : z ∈ K
    · exact Or.inr (Or.inl hzK)
    · exact Or.inr (Or.inr
        (hK.externalNeighbors_isClique hxK
          ⟨(G.mem_neighborSet x y).2 hxy, hyK⟩
          ⟨(G.mem_neighborSet x z).2 hxz, hzK⟩ hyz))
  intro center a b c hca hcb hcc hab hac hbc
  cases center with
  | none =>
      cases a with
      | none => exact ((G.adjoinRootAt K).irrefl hca).elim
      | some a =>
          cases b with
          | none => exact ((G.adjoinRootAt K).irrefl hcb).elim
          | some b =>
              cases c with
              | none => exact ((G.adjoinRootAt K).irrefl hcc).elim
              | some c =>
                  left
                  exact hK.isClique hca hcb (by
                    intro h
                    exact hab (congrArg some h))
  | some x =>
      cases a with
      | none =>
          cases b with
          | none => exact (hab rfl).elim
          | some b =>
              cases c with
              | none => exact (hac rfl).elim
              | some c =>
                  rcases oneRoot hca hcb hcc (by
                    intro h
                    exact hbc (congrArg some h)) with hbK | hcK | hbc'
                  · exact Or.inl hbK
                  · exact Or.inr (Or.inl hcK)
                  · exact Or.inr (Or.inr hbc')
      | some a =>
          cases b with
          | none =>
              cases c with
              | none => exact (hbc rfl).elim
              | some c =>
                  rcases oneRoot hcb hca hcc (by
                    intro h
                    exact hac (congrArg some h)) with haK | hcK | hac'
                  · exact Or.inl haK
                  · exact Or.inr (Or.inr hcK)
                  · exact Or.inr (Or.inl hac')
          | some b =>
              cases c with
              | none =>
                  rcases oneRoot hcc hca hcb (by
                    intro h
                    exact hab (congrArg some h)) with haK | hbK | hab'
                  · exact Or.inr (Or.inl haK)
                  · exact Or.inr (Or.inr hbK)
                  · exact Or.inl hab'
              | some c =>
                  exact hclaw hca hcb hcc
                    (by intro h; exact hab (congrArg some h))
                    (by intro h; exact hac (congrArg some h))
                    (by intro h; exact hbc (congrArg some h))

end IsSimplicialClique

namespace IndexedInducedPath

variable {G : SimpleGraph V}

/-- The three useful forms of an external odd-neighbour configuration. -/
inductive ExternalOddNeighborCase
    (P : IndexedInducedPath G) (j : V) : Prop
  | endpoint
      (q : Fin P.card)
      (adjacent : G.Adj j (P.vertex q))
      (endpointIndex : P.IsEndpointIndex q)
      (exact : ∀ k : Fin P.card,
        G.Adj j (P.vertex k) → k = q) :
      ExternalOddNeighborCase P j
  | pathTriple
      (p q r : Fin P.card)
      (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
      (adjacentP : G.Adj j (P.vertex p))
      (adjacentQ : G.Adj j (P.vertex q))
      (adjacentR : G.Adj j (P.vertex r))
      (exact : ∀ k : Fin P.card,
        G.Adj j (P.vertex k) → k = p ∨ k = q ∨ k = r)
      (shape : P.ThreeNeighborPathCase p q r) :
      ExternalOddNeighborCase P j
  | endpointTriple
      (p q r : Fin P.card)
      (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
      (adjacentP : G.Adj j (P.vertex p))
      (adjacentQ : G.Adj j (P.vertex q))
      (adjacentR : G.Adj j (P.vertex r))
      (exact : ∀ k : Fin P.card,
        G.Adj j (P.vertex k) → k = p ∨ k = q ∨ k = r)
      (shape : P.ThreeNeighborEndpointCase p q r) :
      ExternalOddNeighborCase P j

/-- An external vertex anticommuting with an induced path lies in exactly one
of the odd cases retained from Lemma 7. -/
theorem externalOddNeighborCase_of_anticommutesWith
    (P : IndexedInducedPath G) (hclaw : G.IsClawFree) {j : V}
    (hjP : j ∉ Set.range P.vertex)
    (hanti : P.AnticommutesWith j) :
    P.ExternalOddNeighborCase j := by
  classical
  have hodd :=
    (P.anticommutesWith_iff_neighborIndexSet_mod_eq_one j).1 hanti
  rcases P.lemma7 hclaw hjP with hzero | hone | htwo | hthree | hfour
  · omega
  · obtain ⟨q, hset⟩ := Set.ncard_eq_one.mp hone.1
    have hq : G.Adj j (P.vertex q) := by
      change q ∈ P.neighborIndexSet j
      rw [hset]
      simp
    have hexact : ∀ k : Fin P.card,
        G.Adj j (P.vertex k) → k = q := by
      intro k hk
      change k ∈ P.neighborIndexSet j at hk
      rw [hset] at hk
      simpa using hk
    exact .endpoint q hq (hone.2 q hq) hexact
  · omega
  · obtain ⟨p, q, r, hpq, hpr, hqr, hset⟩ :=
      Set.ncard_eq_three.mp hthree.1
    have hp : G.Adj j (P.vertex p) := by
      change p ∈ P.neighborIndexSet j
      rw [hset]
      simp
    have hq : G.Adj j (P.vertex q) := by
      change q ∈ P.neighborIndexSet j
      rw [hset]
      simp
    have hr : G.Adj j (P.vertex r) := by
      change r ∈ P.neighborIndexSet j
      rw [hset]
      simp
    have hexact : ∀ k : Fin P.card,
        G.Adj j (P.vertex k) → k = p ∨ k = q ∨ k = r := by
      intro k hk
      change k ∈ P.neighborIndexSet j at hk
      rw [hset] at hk
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hk
    rcases hthree.2 p q r hpq hpr hqr hp hq hr hexact with
      hpath | hendpoint
    · exact .pathTriple p q r hpq hpr hqr hp hq hr hexact hpath
    · exact .endpointTriple p q r hpq hpr hqr hp hq hr hexact hendpoint
  · omega

end IndexedInducedPath

namespace RootedInducedPath

variable {G : SimpleGraph V} {K : Set V}

/-- Every anticommuting original vertex is either the terminal path vertex or
one of the external odd-neighbour configurations. -/
inductive OriginalAnticommutingCase
    (P : CliqueRootedInducedPath G K) (j : V) : Prop
  | terminal
      (terminalVertex : P.path.terminalVertex = some j) :
      OriginalAnticommutingCase P j
  | external
      (outside : some j ∉ Set.range P.path.vertex)
      (oddCase : P.path.ExternalOddNeighborCase (some j)) :
      OriginalAnticommutingCase P j

/-- A path-contained original vertex anticommuting with a clique-rooted path
is its non-root terminal. -/
theorem terminalVertex_eq_of_original_mem_of_anticommutesWith
    (P : CliqueRootedInducedPath G K) {j : V}
    (hjP : some j ∈ Set.range P.path.vertex)
    (hanti : P.path.AnticommutesWith (some j)) :
    P.path.terminalVertex = some j := by
  obtain ⟨q, hq, hendpoint⟩ :=
    P.path.endpoint_of_mem_range_of_anticommutesWith hjP hanti
  rcases hendpoint with hfirst | hlast
  · have hqzero : q = ⟨0, P.path.nonempty⟩ := by
      apply Fin.ext
      exact hfirst
    have hroot := P.root_eq
    rw [← hqzero, hq] at hroot
    simp at hroot
  · unfold IndexedInducedPath.terminalVertex
    rw [← hq]
    apply congrArg P.path.vertex
    apply Fin.ext
    change P.path.card - 1 = q.val
    omega

/-- Exhaustive classification of one vertex in the exact anticommuting support
of a clique-rooted physical-Hamiltonian Krylov step. -/
theorem originalAnticommutingCase
    (P : CliqueRootedInducedPath G K)
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree)
    {j : V} (hanti : P.path.AnticommutesWith (some j)) :
    P.OriginalAnticommutingCase j := by
  by_cases hjP : some j ∈ Set.range P.path.vertex
  · exact .terminal (P.terminalVertex_eq_of_original_mem_of_anticommutesWith
      hjP hanti)
  · exact .external hjP
      (P.path.externalOddNeighborCase_of_anticommutesWith
        (hK.isClawFree_adjoinRootAt hclaw) hjP hanti)

end RootedInducedPath

end SimpleGraph
