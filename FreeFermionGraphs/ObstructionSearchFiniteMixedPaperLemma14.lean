import FreeFermionGraphs.ObstructionSearchFiniteMixedDistinctPropagationTrace

/-!
# Paper Lemma 14 from literal finite obstruction-search data

The equal-centre branch is already a consequence of the one-sided terminal
tethers.  In the unequal-centre branch, a bounded propagation trace on either
actual incoming execution constructs the final distinct-clone contradiction.

This module packages only those literal search outputs and exports the exact
four-part statement of manuscript Lemma 14.  There is no terminal-claw,
endpoint-alternative, clone-comparison, or Lemma 14 conclusion in the input
data.
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

structure FiniteMixedSideDistinctCenterPropagationTraceData
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (D : FiniteMixedSideInitializationTerminalTetherData T)
    (hclaw : G.IsClawFree) : Prop where
  trace :
    ∀ ⦃source source' target : I.Node⦄
      (hne : source ≠ source')
      (incoming : I.graph.Arc source target)
      (incoming' : I.graph.Arc source' target)
      (hsource :
        (T.terminalPath target).obstructionEndpoint
            (T.currentSlot source target) ≠ (target : V))
      (hsource' :
        (T.terminalPath target).obstructionEndpoint
            (T.currentSlot source' target) ≠ (target : V)),
      let C := D.toInteriorTerminalCloneData hclaw
      let left := C.witnessOfInterior incoming hsource
      let right := C.witnessOfInterior incoming' hsource'
      ∀ hcenter : left.center ≠ right.center,
        ∃ F : FiniteMixedSideTerminalTwoStepFlanks T target,
          (Nonempty
              (FiniteMixedSideDistinctPropagationTrace
                T hclaw F source incoming) ∨
            Nonempty
              (FiniteMixedSideDistinctPropagationTrace
                T hclaw F source' incoming'))

namespace FiniteMixedSideDistinctCenterPropagationTraceData

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}
  {D : FiniteMixedSideInitializationTerminalTetherData T}
  {hclaw : G.IsClawFree}

noncomputable def toDistinctCenterConsequences
    (A : FiniteMixedSideDistinctCenterPropagationTraceData T D hclaw) :
    D.DistinctCenterConsequences hclaw where
  propagate := by
    classical
    intro source source' target hne incoming incoming' hsource hsource'
    dsimp
    intro hcenter
    have htraceAll :=
      A.trace hne incoming incoming' hsource hsource'
    dsimp at htraceAll
    obtain ⟨F, hleft | hright⟩ := htraceAll hcenter
    · obtain ⟨X⟩ := hleft
      let Y := X.toPropagationFromFlankOccurrence
      exact Or.inl ⟨Y.toPropagationFromDegreeOccurrence⟩
    · obtain ⟨X⟩ := hright
      let Y := X.toPropagationFromFlankOccurrence
      exact Or.inr ⟨Y.toPropagationFromDegreeOccurrence⟩

end FiniteMixedSideDistinctCenterPropagationTraceData

structure InitializationFiniteMixedSideLiteralTerminalData
    (T : I.InitializationFiniteMixedSideTerminalCoreData) : Type (u + 1) where
  tether : FiniteMixedSideInitializationTerminalTetherData T
  distinctPropagation : ∀ hclaw : G.IsClawFree,
    FiniteMixedSideDistinctCenterPropagationTraceData T tether hclaw

namespace InitializationFiniteMixedSideLiteralTerminalData

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}

theorem paperLemma14
    (L : InitializationFiniteMixedSideLiteralTerminalData T)
    (hclaw : G.IsClawFree) :
    PaperLemma14Conclusion I :=
  L.tether.paperLemma14_of_distinctCenterConsequences hclaw
    (L.distinctPropagation hclaw).toDistinctCenterConsequences

end InitializationFiniteMixedSideLiteralTerminalData
end ObstructionSearchInitialization
end FixedPairingPathFamily
end SimpleGraph
