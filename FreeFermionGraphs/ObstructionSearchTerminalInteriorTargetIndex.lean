import FreeFermionGraphs.ObstructionSearchTerminalInteriorFinalClones
import FreeFermionGraphs.ThreeNeighbors

/-!
# Lemma 14(iv): the common target is interior to the terminal path

In the remaining two-incoming branch of Lemma 14(iv), the common obstruction
target differs from both returned singleton dependent vertices.  Those two
vertices occupy opposite endpoints of the same terminal path.  The manuscript
therefore writes the target as an interior vertex `j_(p-1)` with `1 < p`.

This module derives that order statement directly from the initialized terminal
data.  It adds no certificate: distinct incoming sources have distinct terminal
slots, the two-valued slot type therefore supplies both endpoint orientations,
and the two endpoint inequalities force the target's path index to be interior.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace IndexedInducedPath

/-- A path vertex distinct from both selected endpoint vertices has an interior
index. -/
theorem isInteriorIndex_of_obstructionEndpoints_ne
    (P : IndexedInducedPath G) {q : Fin P.card}
    (hfirst : P.obstructionEndpoint .first ≠ P.vertex q)
    (hlast : P.obstructionEndpoint .last ≠ P.vertex q) :
    P.IsInteriorIndex q := by
  constructor
  · intro hzero
    apply hfirst
    unfold obstructionEndpoint
    apply congrArg P.vertex
    apply Fin.ext
    simp [obstructionEndpointIndex, hzero]
  · intro hlastIndex
    apply hlast
    unfold obstructionEndpoint
    apply congrArg P.vertex
    apply Fin.ext
    simp only [obstructionEndpointIndex]
    have hqLt := q.isLt
    omega

end IndexedInducedPath

namespace FixedPairingPathFamily

variable {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ObstructionSearchInitialization

variable {I : ObstructionSearchInitialization families Cprime}

namespace InitializationTerminalCoreData

/-- Two distinct incoming searches occupy opposite terminal endpoint slots. -/
theorem currentSlot_ne_of_twoIncoming
    (T : I.InitializationTerminalCoreData)
    (hclaw : G.IsClawFree)
    {source source' target : I.Node}
    (hne : source ≠ source')
    (incoming : I.graph.Arc source target)
    (incoming' : I.graph.Arc source' target) :
    T.currentSlot source target ≠ T.currentSlot source' target := by
  intro hslots
  exact hne (T.currentSlot_source_injective hclaw incoming incoming' hslots)

/-- In the manuscript's remaining branch, the target differs from both endpoint
orientations of the common terminal path, not merely from the two endpoint
expressions before their orientations are identified. -/
theorem target_ne_both_terminalEndpoints_of_twoIncoming
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
    (T.terminalPath target).obstructionEndpoint .first ≠ (target : V) ∧
      (T.terminalPath target).obstructionEndpoint .last ≠ (target : V) := by
  have hslots :=
    T.currentSlot_ne_of_twoIncoming hclaw hne incoming incoming'
  cases hs : T.currentSlot source target <;>
    cases hs' : T.currentSlot source' target
  · exact (hslots (hs.trans hs'.symm)).elim
  · exact ⟨by simpa [hs] using hsource, by simpa [hs'] using hsource'⟩
  · exact ⟨by simpa [hs'] using hsource', by simpa [hs] using hsource⟩
  · exact (hslots (hs.trans hs'.symm)).elim

/-- Exact indexed form of the manuscript sentence that writes the common target
as `j_(p-1)` with `1 < p` in the two-incoming interior case. -/
theorem exists_interior_targetIndex_of_twoIncoming
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

/-- The interior branch necessarily uses a terminal path with at least three
vertices. -/
theorem three_le_terminalPath_card_of_twoIncoming
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
    3 ≤ (T.terminalPath target).card := by
  obtain ⟨q, _htarget, hqInterior⟩ :=
    T.exists_interior_targetIndex_of_twoIncoming hclaw hne
      incoming incoming' hsource hsource'
  have hq_pos : 1 ≤ q.val := by
    exact Nat.one_le_iff_ne_zero.mpr hqInterior.1
  have hq_succ_le : q.val + 1 ≤ (T.terminalPath target).card := by
    exact q.isLt
  have hq_succ_lt : q.val + 1 < (T.terminalPath target).card := by
    omega
  omega

end InitializationTerminalCoreData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
