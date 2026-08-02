import FreeFermionGraphs.ObstructionSearchTerminalInteriorPathTriple
import FreeFermionGraphs.ObstructionSearchFiniteMixedTerminalCloneComparison

/-!
# Interior target index for finite mixed-side terminal executions

In the unresolved two-incoming branch of Lemma 14(iv), the common obstruction
target differs from both selected terminal endpoints.  Finite terminal-slot
injectivity identifies the two selected slots with the two endpoint
orientations, so the target is an interior vertex of the common terminal path.
Its predecessor and successor then form the exact induced path triple used in
the manuscript.

No final-hole clone or propagation conclusion is assumed here.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace FixedPairingPathFamily

variable {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ObstructionSearchInitialization

variable {I : ObstructionSearchInitialization families Cprime}

namespace InitializationFiniteMixedSideTerminalCoreData

/-- Distinct incoming finite searches occupy distinct terminal endpoint slots. -/
theorem currentSlot_ne_of_twoIncoming
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (hclaw : G.IsClawFree)
    {source source' target : I.Node}
    (hne : source ≠ source')
    (incoming : I.graph.Arc source target)
    (incoming' : I.graph.Arc source' target) :
    T.currentSlot source target ≠ T.currentSlot source' target := by
  intro hslots
  exact hne (T.currentSlot_source_injective hclaw incoming incoming' hslots)

/-- In the two-incoming interior branch, the target differs from both actual
endpoint orientations of the common terminal path. -/
theorem target_ne_both_terminalEndpoints_of_twoIncoming
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
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
    (T.terminalPath target).obstructionEndpoint .first ≠ (target : V) ∧
      (T.terminalPath target).obstructionEndpoint .last ≠ (target : V) := by
  have hslots := T.currentSlot_ne_of_twoIncoming hclaw hne incoming incoming'
  cases hs : T.currentSlot source target <;>
    cases hs' : T.currentSlot source' target
  · exact (hslots (hs.trans hs'.symm)).elim
  · exact ⟨by simpa [hs] using hsource, by simpa [hs'] using hsource'⟩
  · exact ⟨by simpa [hs'] using hsource', by simpa [hs] using hsource⟩
  · exact (hslots (hs.trans hs'.symm)).elim

/-- The common obstruction target has an interior index in the finite terminal
path. -/
theorem exists_interior_targetIndex_of_twoIncoming
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
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
    ∃ q : Fin (T.terminalPath target).card,
      (T.terminalPath target).vertex q = (target : V) ∧
        (T.terminalPath target).IsInteriorIndex q := by
  obtain ⟨q, htarget, _hnearest⟩ :=
    T.nearestTarget.obstruction_nearest incoming
  have hend :=
    T.target_ne_both_terminalEndpoints_of_twoIncoming hclaw hne
      incoming incoming' hsource hsource'
  refine ⟨q, htarget, ?_⟩
  apply (T.terminalPath target).isInteriorIndex_of_obstructionEndpoints_ne
  · intro heq
    exact hend.1 (heq.trans htarget)
  · intro heq
    exact hend.2 (heq.trans htarget)

/-- The interior finite terminal branch uses a path with at least three
vertices. -/
theorem three_le_terminalPath_card_of_twoIncoming
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
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
    3 ≤ (T.terminalPath target).card := by
  obtain ⟨q, _htarget, hqInterior⟩ :=
    T.exists_interior_targetIndex_of_twoIncoming hclaw hne
      incoming incoming' hsource hsource'
  have hq_pos : 1 ≤ q.val := Nat.one_le_iff_ne_zero.mpr hqInterior.1
  have hq_succ_le : q.val + 1 ≤ (T.terminalPath target).card := q.isLt
  have hq_not_last : q.val + 1 ≠ (T.terminalPath target).card := hqInterior.2
  have hq_succ_lt : q.val + 1 < (T.terminalPath target).card := by omega
  omega

/-- Exact finite indexed form of the manuscript segment
`j_(p-2) - j'' - j_p`. -/
theorem exists_terminalPathTriple_around_target_of_twoIncoming
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
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

end InitializationFiniteMixedSideTerminalCoreData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
