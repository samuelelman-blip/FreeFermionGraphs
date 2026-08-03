import FreeFermionGraphs.ObstructionSearchFiniteMixedTerminalTargetIndex

/-!
# Target-level alternation data for terminal paths

The parity of the common target index and the odd cardinality of its terminal
path depend only on the target path, not on a particular incoming search.  This
module factors those facts out of the one-sided tether data.  The remaining
per-incoming fields are the positive final-hole degree and the one-sided clone
adjacency produced by the actual stopping history.
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

/-- Alternating terminal-path information indexed only by the common target.
The displayed target index may be any occurrence of the target on the induced
path; injectivity identifies it with the canonical nearest-target index. -/
structure FiniteMixedSideTerminalAlternationData
    (T : I.InitializationFiniteMixedSideTerminalCoreData) : Prop where
  targetIndex_even :
    ∀ (target : I.Node),
      (∃ source : I.Node, I.graph.Arc source target) →
        ∃ q : Fin (T.terminalPath target).card,
          (T.terminalPath target).vertex q = (target : V) ∧ Even q.val
  pathCard_odd :
    ∀ (target : I.Node),
      (∃ source : I.Node, I.graph.Arc source target) →
        Odd (T.terminalPath target).card

namespace FiniteMixedSideTerminalAlternationData

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}

/-- Target-level parity transfers to the canonical index selected by the
nearest-target rule. -/
theorem canonicalTargetIndex_even
    (A : FiniteMixedSideTerminalAlternationData T)
    {source target : I.Node}
    (incoming : I.graph.Arc source target) :
    Even (T.terminalTargetIndex incoming).val := by
  obtain ⟨q, hqTarget, hqEven⟩ :=
    A.targetIndex_even target ⟨source, incoming⟩
  have hq : q = T.terminalTargetIndex incoming := by
    apply (T.terminalPath target).injective
    exact hqTarget.trans (T.terminalTargetIndex_target_eq incoming).symm
  simpa [hq] using hqEven

/-- The shared terminal path has odd cardinality for every actual incoming
obstruction arc. -/
theorem pathCard_odd_of_incoming
    (A : FiniteMixedSideTerminalAlternationData T)
    {source target : I.Node}
    (incoming : I.graph.Arc source target) :
    Odd (T.terminalPath target).card :=
  A.pathCard_odd target ⟨source, incoming⟩

end FiniteMixedSideTerminalAlternationData

/-- The genuinely one-sided part of a terminal tether after target index and
path parity have been factored out. -/
structure FiniteMixedSideIncomingOperationalTether
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (source target : I.Node)
    (incoming : I.graph.Arc source target) : Type where
  positive_finalDegree_three :
    ∀ hpos :
      0 <
        (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
          source).blockCount,
      (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
        source).manuscriptFinalHole.externalDegree (target : V) = 3
  clone_adj_flank :
    ∀ X : FiniteMixedSideIncomingTerminalCloneWitness
        T source target incoming,
      ∀ q : Fin (T.terminalPath target).card,
        match T.currentSlot source target with
        | .first =>
            q.val + 2 = (T.terminalTargetIndex incoming).val →
              G.Adj X.center ((T.terminalPath target).vertex q)
        | .last =>
            (T.terminalTargetIndex incoming).val + 2 = q.val →
              G.Adj X.center ((T.terminalPath target).vertex q)

/-- Target-level alternation together with the operational tether for every
actual incoming search. -/
structure FiniteMixedSideInitializationOperationalTerminalData
    (T : I.InitializationFiniteMixedSideTerminalCoreData) : Type (u + 1) where
  alternation : FiniteMixedSideTerminalAlternationData T
  tether : ∀ ⦃source target : I.Node⦄
    (incoming : I.graph.Arc source target),
      FiniteMixedSideIncomingOperationalTether T source target incoming

namespace FiniteMixedSideInitializationOperationalTerminalData

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}

/-- Reconstruct the reduced per-incoming tether interface.  The parity fields
are supplied once at target level and transported to the canonical target
index. -/
noncomputable def toTerminalTetherWithoutTargetIndexData
    (D : FiniteMixedSideInitializationOperationalTerminalData T) :
    FiniteMixedSideInitializationTerminalTetherWithoutTargetIndexData T where
  tether := fun incoming =>
    { targetIndex_even := D.alternation.canonicalTargetIndex_even incoming
      pathCard_odd := D.alternation.pathCard_odd_of_incoming incoming
      positive_finalDegree_three :=
        (D.tether incoming).positive_finalDegree_three
      clone_adj_flank := (D.tether incoming).clone_adj_flank }

/-- Reconstruct the established terminal tether analysis. -/
noncomputable def toTerminalTetherData
    (D : FiniteMixedSideInitializationOperationalTerminalData T) :
    FiniteMixedSideInitializationTerminalTetherData T :=
  D.toTerminalTetherWithoutTargetIndexData.toTerminalTetherData

end FiniteMixedSideInitializationOperationalTerminalData

/-- Complete finite terminal input after factoring common path alternation out
of the incoming search data. -/
structure InitializationFiniteMixedSideOperationalTerminalData
    (T : I.InitializationFiniteMixedSideTerminalCoreData) : Type (u + 1) where
  terminal : FiniteMixedSideInitializationOperationalTerminalData T
  distinctPropagation : ∀ hclaw : G.IsClawFree,
    FiniteMixedSideDistinctCenterPropagationTraceData T
      terminal.toTerminalTetherData hclaw

namespace InitializationFiniteMixedSideOperationalTerminalData

/-- Exact manuscript Lemma 14 from target-level alternation, literal one-sided
tethers, and bounded unequal-centre propagation. -/
theorem paperLemma14
    {T : I.InitializationFiniteMixedSideTerminalCoreData}
    (L : InitializationFiniteMixedSideOperationalTerminalData T)
    (hclaw : G.IsClawFree) :
    PaperLemma14Conclusion I := by
  let D := L.terminal.toTerminalTetherData
  exact D.paperLemma14_of_distinctCenterConsequences hclaw
    (L.distinctPropagation hclaw).toDistinctCenterConsequences

end InitializationFiniteMixedSideOperationalTerminalData

end ObstructionSearchInitialization
end FixedPairingPathFamily
end SimpleGraph
