import FreeFermionGraphs.ObstructionSearchFiniteMixedGeneratedDistinctPropagation

/-!
# Generated terminal component and stopping events

The manuscript writes the terminal component as

`j₀-k₀-⋯-k_(ℓ-1)-j_ℓ`.

This file uses that literal coordinate presentation as the terminal event.  The
odd path cardinality, even target coordinate, and endpoint side are derived
from the half-length and target position.  The incoming stopping event stores
only the step-balance invariant and the adjacent tether-link coordinate.  The
terminal degree-three and clone-to-flank conclusions are then theorems.
-/

universe u

variable {V : Type u}

namespace SimpleGraph
namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ObstructionSearchInitialization

variable {I : ObstructionSearchInitialization families Cprime}

/-- Literal coordinate presentation of the odd terminal path
`j₀-k₀-⋯-k_(ℓ-1)-j_ℓ`, with the obstruction target at `j_p`. -/
structure FiniteMixedSideTerminalPathExecution
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (target : I.Node) where
  halfLength : Nat
  card_eq : (T.terminalPath target).card = 2 * halfLength + 1
  targetPosition : Nat
  targetPosition_le : targetPosition ≤ halfLength
  target_eq :
    (T.terminalPath target).vertex
        ⟨2 * targetPosition, by omega⟩ = (target : V)

namespace FiniteMixedSideTerminalPathExecution

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}
  {target : I.Node}

/-- Canonical even index of the target in the literal alternating path. -/
def targetIndex
    (P : FiniteMixedSideTerminalPathExecution T target) :
    Fin (T.terminalPath target).card :=
  ⟨2 * P.targetPosition, by omega⟩

@[simp] theorem targetIndex_val
    (P : FiniteMixedSideTerminalPathExecution T target) :
    P.targetIndex.val = 2 * P.targetPosition := rfl

/-- Target index evaluates to the common obstruction target. -/
theorem targetIndex_target_eq
    (P : FiniteMixedSideTerminalPathExecution T target) :
    (T.terminalPath target).vertex P.targetIndex = (target : V) :=
  P.target_eq

/-- The endpoint colour side of the alternating path, defined directly by even
path coordinates. -/
def sameSide
    (P : FiniteMixedSideTerminalPathExecution T target) : Set V :=
  {v | ∃ q : Fin (T.terminalPath target).card,
    Even q.val ∧ (T.terminalPath target).vertex q = v}

/-- Membership in the endpoint side is equivalent to even path coordinate. -/
theorem index_even_iff_mem_sameSide
    (P : FiniteMixedSideTerminalPathExecution T target)
    (q : Fin (T.terminalPath target).card) :
    Even q.val ↔ (T.terminalPath target).vertex q ∈ P.sameSide := by
  constructor
  · intro hq
    exact ⟨q, hq, rfl⟩
  · rintro ⟨r, hrEven, hr⟩
    have hqr : q = r :=
      (T.terminalPath target).injective hr
    simpa [hqr] using hrEven

/-- The obstruction target lies on the endpoint side. -/
theorem target_mem_sameSide
    (P : FiniteMixedSideTerminalPathExecution T target) :
    (target : V) ∈ P.sameSide := by
  refine ⟨P.targetIndex, ?_, P.targetIndex_target_eq⟩
  exact ⟨P.targetPosition, by omega⟩

/-- The last endpoint has coordinate `2ℓ` and is on the same side. -/
theorem lastEndpoint_mem_sameSide
    (P : FiniteMixedSideTerminalPathExecution T target) :
    (T.terminalPath target).obstructionEndpoint .last ∈ P.sameSide := by
  let q := (T.terminalPath target).obstructionEndpointIndex .last
  refine ⟨q, ?_, rfl⟩
  refine ⟨P.halfLength, ?_⟩
  change q.val = P.halfLength + P.halfLength
  dsimp [q, IndexedInducedPath.obstructionEndpointIndex]
  omega

/-- Literal odd-path coordinates provide the alternating-label interface. -/
def toAlternatingLabelData
    (P : ∀ target : I.Node,
      FiniteMixedSideTerminalPathExecution T target) :
    FiniteMixedSideTerminalAlternatingLabelData T where
  sameSide := fun target => (P target).sameSide
  index_even_iff_mem_sameSide := by
    intro target q
    exact (P target).index_even_iff_mem_sameSide q
  target_mem_sameSide := by
    intro source target incoming
    exact (P target).target_mem_sameSide
  lastEndpoint_mem_sameSide := by
    intro source target incoming
    exact (P target).lastEndpoint_mem_sameSide

end FiniteMixedSideTerminalPathExecution

/-- Literal incoming terminal event.  Target degree is controlled by the
step-balance invariant.  The tether centre is the path vertex one coordinate
between the source-side flank and the target. -/
structure FiniteMixedSideIncomingGeneratedTerminalStop
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (P : FiniteMixedSideTerminalPathExecution T target)
    (source target : I.Node)
    (incoming : I.graph.Arc source target) where
  targetBalanced :
    (T.execution.toInitializationFiniteMixedSideOSExecutionData.execution
      source).TargetBalanced (target : V)
  linkIndex :
    ∀ X : FiniteMixedSideIncomingTerminalCloneWitness
        T source target incoming,
      Fin (T.terminalPath target).card
  link_center_eq :
    ∀ X : FiniteMixedSideIncomingTerminalCloneWitness
        T source target incoming,
      (T.terminalPath target).vertex (linkIndex X) = X.center
  link_toward_target :
    ∀ X : FiniteMixedSideIncomingTerminalCloneWitness
        T source target incoming,
      match T.currentSlot source target with
      | .first => (linkIndex X).val + 1 = P.targetIndex.val
      | .last => P.targetIndex.val + 1 = (linkIndex X).val

namespace FiniteMixedSideIncomingGeneratedTerminalStop

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}
  {target source : I.Node}
  {incoming : I.graph.Arc source target}
  {P : FiniteMixedSideTerminalPathExecution T target}

/-- Target balance transports the stopping-branch clone degree from the
original hole to the exact positive final hole. -/
theorem positive_finalDegree_three
    (E : FiniteMixedSideIncomingGeneratedTerminalStop
      T P source target incoming)
    (hclaw : G.IsClawFree)
    (hpos :
      0 <
        (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
          source).blockCount) :
    (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
      source).manuscriptFinalHole.externalDegree (target : V) = 3 := by
  let Y := T.execution.toInitializationFiniteMixedSideOSExecutionData
  have htransport :=
    (Y.execution source).manuscriptFinalHole_externalDegree_eq_original_of_targetBalanced
      (target : V) E.targetBalanced hpos
  obtain ⟨i, hclone⟩ := T.exists_target_clone_of_incoming hclaw incoming
  exact htransport.trans hclone.externalDegree_eq_three

/-- The target coordinate chosen by the terminal event is the canonical
nearest-target index. -/
theorem targetIndex_eq_canonical
    (E : FiniteMixedSideIncomingGeneratedTerminalStop
      T P source target incoming) :
    P.targetIndex = T.terminalTargetIndex incoming := by
  apply (T.terminalPath target).injective
  exact P.targetIndex_target_eq.trans
    (T.terminalTargetIndex_target_eq incoming).symm

/-- The tether-link coordinate forces adjacency of the staged clone centre to
the endpoint-side two-step flank. -/
theorem clone_adj_flank
    (E : FiniteMixedSideIncomingGeneratedTerminalStop
      T P source target incoming)
    (X : FiniteMixedSideIncomingTerminalCloneWitness
      T source target incoming)
    (q : Fin (T.terminalPath target).card) :
    match T.currentSlot source target with
    | .first =>
        q.val + 2 = (T.terminalTargetIndex incoming).val →
          G.Adj X.center ((T.terminalPath target).vertex q)
    | .last =>
        (T.terminalTargetIndex incoming).val + 2 = q.val →
          G.Adj X.center ((T.terminalPath target).vertex q) := by
  let r := E.linkIndex X
  have hcenter := E.link_center_eq X
  have htarget := E.targetIndex_eq_canonical
  cases hs : T.currentSlot source target with
  | first =>
      intro hq
      have hr := E.link_toward_target X
      have hr' : r.val + 1 = P.targetIndex.val := by
        simpa [hs, r] using hr
      rw [← hcenter]
      apply ((T.terminalPath target).adj_iff r q).2
      right
      rw [← htarget] at hq
      omega
  | last =>
      intro hq
      have hr := E.link_toward_target X
      have hr' : P.targetIndex.val + 1 = r.val := by
        simpa [hs, r] using hr
      rw [← hcenter]
      apply ((T.terminalPath target).adj_iff r q).2
      left
      rw [← htarget] at hq
      omega

/-- Convert the generated terminal stop to the operational tether interface. -/
def toOperationalTether
    (E : FiniteMixedSideIncomingGeneratedTerminalStop
      T P source target incoming)
    (hclaw : G.IsClawFree) :
    FiniteMixedSideIncomingOperationalTether T source target incoming where
  positive_finalDegree_three := E.positive_finalDegree_three hclaw
  clone_adj_flank := E.clone_adj_flank

end FiniteMixedSideIncomingGeneratedTerminalStop

/-- Terminal data emitted by literal odd path coordinates, balanced finite
executions, and adjacent tether links. -/
structure InitializationFiniteMixedSideGeneratedTerminalEvent
    (T : I.InitializationFiniteMixedSideTerminalCoreData) : Type (u + 1) where
  path : ∀ target : I.Node,
    FiniteMixedSideTerminalPathExecution T target
  stop : ∀ ⦃source target : I.Node⦄
    (incoming : I.graph.Arc source target),
      FiniteMixedSideIncomingGeneratedTerminalStop
        T (path target) source target incoming

namespace InitializationFiniteMixedSideGeneratedTerminalEvent

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}

/-- All terminal labels, degree-three facts, and flank adjacencies are derived
from the generated event. -/
def toLabelledOperationalTerminalData
    (E : InitializationFiniteMixedSideGeneratedTerminalEvent T)
    (hclaw : G.IsClawFree) :
    FiniteMixedSideInitializationLabelledOperationalTerminalData T where
  labels := E.path.toAlternatingLabelData
  tether := fun incoming => (E.stop incoming).toOperationalTether hclaw

end InitializationFiniteMixedSideGeneratedTerminalEvent

end ObstructionSearchInitialization
end FixedPairingPathFamily
end SimpleGraph
