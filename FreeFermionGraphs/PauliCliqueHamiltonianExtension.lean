import FreeFermionGraphs.PauliCliqueHamiltonian

/-!
# Pauli extension contribution at a clique-rooted path

This module derives the unit-weight forward tree arc in Appendix E.  For a
literal one-vertex extension, the new terminal vertex is adjacent to exactly
the old terminal vertex and to no other vertex of the shorter induced path.
Consequently its Hamiltonian term anticommutes with the shorter path operator,
and its commutator contribution is exactly `-2 h_Q`.
-/

universe u v w

variable {V : Type u}

namespace SimpleGraph

namespace RootedInducedPath

variable {G : SimpleGraph V} {root : V}

/-- The vertex appended by a one-vertex extension has exactly one neighbour
on the shorter path, namely its terminal vertex. -/
theorem IsOneVertexExtension.shorter_anticommutesWith_terminal
    {P Q : RootedInducedPath G root}
    (h : P.IsOneVertexExtension Q) :
    P.path.AnticommutesWith Q.path.terminalVertex := by
  rcases h with ⟨hcard, hprefix⟩
  let lastP : Fin P.path.card :=
    ⟨P.path.card - 1, Nat.sub_lt P.path.nonempty (by decide)⟩
  let newQ : Fin Q.path.card := ⟨P.path.card, by omega⟩
  have hnew : Q.path.vertex newQ = Q.path.terminalVertex := by
    simp only [IndexedInducedPath.terminalVertex]
    apply congrArg Q.path.vertex
    apply Fin.ext
    dsimp [newQ]
    omega
  apply P.path.anticommutesWith_of_unique_neighbor
      (i := lastP)
  · rw [← hnew, ← hprefix lastP]
    apply (Q.path.adj_iff newQ
      ⟨lastP.val, by have := lastP.isLt; omega⟩).2
    right
    dsimp [newQ, lastP]
    have hpos := P.path.nonempty
    omega
  · intro q hq
    have hqQ :
        G.Adj (Q.path.vertex newQ)
          (Q.path.vertex ⟨q.val, by omega⟩) := by
      rw [hnew, hprefix q]
      exact hq
    rcases (Q.path.adj_iff newQ
      ⟨q.val, by omega⟩).1 hqQ with hforward | hbackward
    · dsimp [newQ] at hforward
      have hq_lt := q.isLt
      omega
    · apply Fin.ext
      dsimp [newQ, lastP] at hbackward ⊢
      have hpos := P.path.nonempty
      omega

end RootedInducedPath

namespace PauliCliqueHamiltonianRepresentation

variable {G : SimpleGraph V} {K : Set V}
variable {R : Type v} {A : Type w}
variable [CommRing R] [Ring A] [Algebra R A]

/-- Exact unit-weight forward-tree contribution from Eq. (E11).  If `Q`
extends `P` by the original vertex `j`, the `j` term in the physical
Hamiltonian contributes `-2 h_Q`. -/
theorem extension_commutator
    (H : G.PauliCliqueHamiltonianRepresentation K R A)
    {P Q : CliqueRootedInducedPath G K}
    (h : P.IsOneVertexExtension Q) {j : V}
    (hterminal : Q.path.terminalVertex = some j) :
    algebraCommutator (H.operator.term (some j)) (H.pathOperator P) =
      ((-1 : A) - 1) * H.pathOperator Q := by
  have hanti : P.path.AnticommutesWith (some j) := by
    simpa only [hterminal] using
      h.shorter_anticommutesWith_terminal
  change algebraCommutator (H.operator.term (some j))
      (H.operator.pathOperator P.path) =
    ((-1 : A) - 1) * H.operator.pathOperator Q.path
  rw [H.operator.commutator_term_pathOperator_of_anticommutesWith
    (some j) P.path hanti]
  rw [H.operator.pathOperator_extension h, hterminal]

end PauliCliqueHamiltonianRepresentation
end SimpleGraph
