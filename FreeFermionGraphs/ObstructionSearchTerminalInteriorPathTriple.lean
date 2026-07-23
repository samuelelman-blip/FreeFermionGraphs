import FreeFermionGraphs.ObstructionSearchTerminalInteriorTargetIndex

/-!
# Lemma 14(iv): the path neighbours around the interior target

After the manuscript writes the common obstruction target as the interior path
vertex `j_(p-1)`, it uses the consecutive path vertices `j_(p-2)` and `j_p`.
This module derives those two neighbours directly from the indexed terminal
path.  No terminal-hole or deformation certificate is introduced.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace IndexedInducedPath

/-- Every interior index has a predecessor and successor which form an induced
three-vertex path with the indexed vertex in the middle. -/
theorem exists_consecutiveTriple_around_interior
    (P : IndexedInducedPath G) {q : Fin P.card}
    (hq : P.IsInteriorIndex q) :
    ∃ qPrev qNext : Fin P.card,
      qPrev.val + 1 = q.val ∧
        q.val + 1 = qNext.val ∧
          G.IsInducedPathTriple
            (P.vertex qPrev) (P.vertex q) (P.vertex qNext) := by
  have hqLt := q.isLt
  have hqPos : 0 < q.val := by
    exact Nat.pos_of_ne_zero hq.1
  have hqNextLt : q.val + 1 < P.card := by
    omega
  let qPrev : Fin P.card := ⟨q.val - 1, by omega⟩
  let qNext : Fin P.card := ⟨q.val + 1, hqNextLt⟩
  have hprev : qPrev.val + 1 = q.val := by
    dsimp [qPrev]
    omega
  have hnext : q.val + 1 = qNext.val := by
    rfl
  refine ⟨qPrev, qNext, hprev, hnext, ?_⟩
  exact P.consecutiveTriple hprev hnext

end IndexedInducedPath

namespace FixedPairingPathFamily

variable {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ObstructionSearchInitialization

variable {I : ObstructionSearchInitialization families Cprime}

namespace InitializationTerminalCoreData

/-- Indexed form of the manuscript path segment
`j_(p-2) - j'' - j_p` in the two-incoming interior branch. -/
theorem exists_terminalPathTriple_around_target_of_twoIncoming
    (T : I.InitializationTerminalCoreData)
    (hclaw : G.IsClawFree)
    {source source' target : I.Node}
    (hne : source ≠ source')
    (incoming : I.graph.Arc source target)
    (incoming' : I.graph.Arc source' target)
    (hsource :
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source target) ≠ (target : V))
    (hsource' :
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source' target) ≠ (target : V)) :
    ∃ qPrev q qNext : Fin (T.terminalPath target).card,
      (T.terminalPath target).vertex q = (target : V) ∧
        qPrev.val + 1 = q.val ∧
          q.val + 1 = qNext.val ∧
            G.IsInducedPathTriple
              ((T.terminalPath target).vertex qPrev)
              (target : V)
              ((T.terminalPath target).vertex qNext) := by
  obtain ⟨q, htarget, hqInterior⟩ :=
    T.exists_interior_targetIndex_of_twoIncoming hclaw hne
      incoming incoming' hsource hsource'
  obtain ⟨qPrev, qNext, hprev, hnext, htriple⟩ :=
    (T.terminalPath target).exists_consecutiveTriple_around_interior hqInterior
  refine ⟨qPrev, q, qNext, htarget, hprev, hnext, ?_⟩
  simpa [htarget] using htriple

end InitializationTerminalCoreData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
