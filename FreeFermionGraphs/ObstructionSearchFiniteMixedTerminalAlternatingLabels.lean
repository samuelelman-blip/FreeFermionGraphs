import FreeFermionGraphs.ObstructionSearchFiniteMixedTerminalAlternation

/-!
# Alternating labels for finite terminal paths

The terminal path alternates between the two colour classes of its selected
component.  The obstruction target and both terminal endpoints lie on the same
side.  This module derives the even target index and odd path cardinality from
that literal alternating labelling, rather than storing either arithmetic fact.
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

/-- Literal target-level alternating labelling of a terminal path.

`sameSide` is the colour side containing the two endpoints and the obstruction
target.  Membership in that side is equivalent to even path index. -/
structure FiniteMixedSideTerminalAlternatingLabelData
    (T : I.InitializationFiniteMixedSideTerminalCoreData) : Type (u + 1) where
  sameSide : I.Node → Set V
  index_even_iff_mem_sameSide :
    ∀ (target : I.Node) (q : Fin (T.terminalPath target).card),
      Even q.val ↔ (T.terminalPath target).vertex q ∈ sameSide target
  target_mem_sameSide :
    ∀ {source target : I.Node},
      I.graph.Arc source target → (target : V) ∈ sameSide target
  lastEndpoint_mem_sameSide :
    ∀ {source target : I.Node},
      I.graph.Arc source target →
        (T.terminalPath target).obstructionEndpoint .last ∈ sameSide target

namespace FiniteMixedSideTerminalAlternatingLabelData

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}

/-- The canonical nearest-target index is even because the target lies on the
same alternating side as the terminal endpoints. -/
theorem canonicalTargetIndex_even
    (A : FiniteMixedSideTerminalAlternatingLabelData T)
    {source target : I.Node}
    (incoming : I.graph.Arc source target) :
    Even (T.terminalTargetIndex incoming).val := by
  apply (A.index_even_iff_mem_sameSide target
    (T.terminalTargetIndex incoming)).2
  rw [T.terminalTargetIndex_target_eq incoming]
  exact A.target_mem_sameSide incoming

/-- If the last endpoint has even index, then the path cardinality is odd. -/
theorem pathCard_odd_of_incoming
    (A : FiniteMixedSideTerminalAlternatingLabelData T)
    {source target : I.Node}
    (incoming : I.graph.Arc source target) :
    Odd (T.terminalPath target).card := by
  let P := T.terminalPath target
  let last : Fin P.card := P.obstructionEndpointIndex .last
  have hlastMem : P.vertex last ∈ A.sameSide target := by
    simpa [P, last, IndexedInducedPath.obstructionEndpoint] using
      A.lastEndpoint_mem_sameSide incoming
  have hlastEven : Even last.val :=
    (A.index_even_iff_mem_sameSide target last).2 hlastMem
  obtain ⟨k, hk⟩ := hlastEven
  refine ⟨k, ?_⟩
  have hcardPos : 0 < P.card := P.nonempty
  have hlastVal : last.val = P.card - 1 := by
    rfl
  dsimp [P] at hcardPos ⊢
  rw [hlastVal] at hk
  omega

/-- Alternating labels construct the target-level arithmetic interface used by
the finite terminal proof. -/
def toTerminalAlternationData
    (A : FiniteMixedSideTerminalAlternatingLabelData T) :
    FiniteMixedSideTerminalAlternationData T where
  targetIndex_even := by
    intro target hincoming
    obtain ⟨source, incoming⟩ := hincoming
    exact ⟨T.terminalTargetIndex incoming,
      T.terminalTargetIndex_target_eq incoming,
      A.canonicalTargetIndex_even incoming⟩
  pathCard_odd := by
    intro target hincoming
    obtain ⟨source, incoming⟩ := hincoming
    exact A.pathCard_odd_of_incoming incoming

end FiniteMixedSideTerminalAlternatingLabelData

/-- Operational terminal input with arithmetic parity derived from literal
alternating labels. -/
structure FiniteMixedSideInitializationLabelledOperationalTerminalData
    (T : I.InitializationFiniteMixedSideTerminalCoreData) : Type (u + 1) where
  labels : FiniteMixedSideTerminalAlternatingLabelData T
  tether : ∀ ⦃source target : I.Node⦄
    (incoming : I.graph.Arc source target),
      FiniteMixedSideIncomingOperationalTether T source target incoming

namespace FiniteMixedSideInitializationLabelledOperationalTerminalData

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}

/-- Forget the explicit colouring after deriving the parity consequences. -/
def toOperationalTerminalData
    (D : FiniteMixedSideInitializationLabelledOperationalTerminalData T) :
    FiniteMixedSideInitializationOperationalTerminalData T where
  alternation := D.labels.toTerminalAlternationData
  tether := D.tether

end FiniteMixedSideInitializationLabelledOperationalTerminalData

/-- Complete finite terminal data with arithmetic parity eliminated from the
input boundary. -/
structure InitializationFiniteMixedSideLabelledOperationalTerminalData
    (T : I.InitializationFiniteMixedSideTerminalCoreData) : Type (u + 1) where
  terminal : FiniteMixedSideInitializationLabelledOperationalTerminalData T
  distinctPropagation : ∀ hclaw : G.IsClawFree,
    FiniteMixedSideDistinctCenterPropagationTraceData T
      terminal.toOperationalTerminalData.toTerminalTetherData hclaw

namespace InitializationFiniteMixedSideLabelledOperationalTerminalData

/-- Exact manuscript Lemma 14 from alternating terminal labels, the literal
one-sided stopping tether, and bounded unequal-centre propagation. -/
theorem paperLemma14
    {T : I.InitializationFiniteMixedSideTerminalCoreData}
    (L : InitializationFiniteMixedSideLabelledOperationalTerminalData T)
    (hclaw : G.IsClawFree) :
    PaperLemma14Conclusion I := by
  let D := L.terminal.toOperationalTerminalData.toTerminalTetherData
  exact D.paperLemma14_of_distinctCenterConsequences hclaw
    (L.distinctPropagation hclaw).toDistinctCenterConsequences

end InitializationFiniteMixedSideLabelledOperationalTerminalData

end ObstructionSearchInitialization
end FixedPairingPathFamily
end SimpleGraph
