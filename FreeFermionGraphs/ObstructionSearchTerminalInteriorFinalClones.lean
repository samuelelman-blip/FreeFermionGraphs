import FreeFermionGraphs.ObstructionSearchTerminalCanonicalFinalClones

/-!
# Lemma 14(iv): final-hole clones only in the interior obstruction case

The final-hole clone relations in the manuscript are introduced only after two
incoming searches have been fixed and the common obstruction target is assumed
to equal neither returned singleton dependent vertex.  Since each returned
vertex is represented by the selected terminal-path endpoint, the relevant
per-arc premise is exactly that the target differs from that endpoint.

This module corrects the quantifier scope of the final-hole clone boundary.  It
requires a clone witness for an incoming arc only under the corresponding
interior-target premise.  The two centres are then selected under the two
premises already present in the pairwise Lemma 14(iv) argument.
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

/-- Final-hole clone existence for exactly the manuscript's interior case.

For an arc `source → target`, the witness is required only when the obstruction
target is not the terminal endpoint returned as the singleton dependent set of
`source`.  No clone statement is imposed on the endpoint alternative. -/
structure InitializationInteriorTerminalCloneData
    (T : I.InitializationTerminalCoreData) : Prop where
  exists_witness :
    ∀ ⦃source target : I.Node⦄
      (incoming : I.graph.Arc source target),
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source target) ≠ (target : V) →
        Nonempty (IncomingTerminalCloneWitness T source target incoming)

namespace InitializationInteriorTerminalCloneData

variable {T : I.InitializationTerminalCoreData}

/-- Select the target's final-hole clone witness under the interior premise. -/
noncomputable def witnessOfInterior
    (C : InitializationInteriorTerminalCloneData T)
    {source target : I.Node}
    (incoming : I.graph.Arc source target)
    (hinterior :
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source target) ≠ (target : V)) :
    IncomingTerminalCloneWitness T source target incoming :=
  Classical.choice (C.exists_witness incoming hinterior)

/-- The displayed final-hole clone centre under the interior premise. -/
noncomputable def centerOfInterior
    (C : InitializationInteriorTerminalCloneData T)
    {source target : I.Node}
    (incoming : I.graph.Arc source target)
    (hinterior :
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source target) ≠ (target : V)) : V :=
  (C.witnessOfInterior incoming hinterior).center

/-- Every supplied witness agrees with the selected interior clone centre. -/
theorem center_eq_centerOfInterior
    (C : InitializationInteriorTerminalCloneData T)
    {source target : I.Node}
    {incoming : I.graph.Arc source target}
    (hinterior :
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source target) ≠ (target : V))
    (X : IncomingTerminalCloneWitness T source target incoming) :
    X.center = C.centerOfInterior incoming hinterior :=
  X.center_eq (C.witnessOfInterior incoming hinterior)

/-- The selected centre is independent of the proof term used for the same
interior proposition. -/
theorem centerOfInterior_proof_irrel
    (C : InitializationInteriorTerminalCloneData T)
    {source target : I.Node}
    (incoming : I.graph.Arc source target)
    (h h' :
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source target) ≠ (target : V)) :
    C.centerOfInterior incoming h = C.centerOfInterior incoming h' := by
  have hh : h = h' := Subsingleton.elim _ _
  subst h'
  rfl

end InitializationInteriorTerminalCloneData

/-- The equal-centre and distinct-centre continuations with the two clone
centres selected only after the two interior premises have been supplied. -/
structure TwoIncomingTerminalInteriorCloneConsequences
    (T : I.InitializationTerminalCoreData)
    (hclaw : G.IsClawFree)
    (C : InitializationInteriorTerminalCloneData T) : Prop where
  terminalGeometry :
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
        (C.centerOfInterior incoming hsource =
            C.centerOfInterior incoming' hsource' →
          Nonempty
            ((T.terminalPath target).SameCloneTerminalNeighborhood
              (target : V))) ∧
        (C.centerOfInterior incoming hsource ≠
            C.centerOfInterior incoming' hsource' →
          (Nonempty
              (DistinctClonePropagationFromDegreeOccurrence
                T hclaw source target incoming) ∨
            Nonempty
              (DistinctClonePropagationFromDegreeOccurrence
                T hclaw source' target incoming')))

namespace InitializationInteriorTerminalCloneData

variable {T : I.InitializationTerminalCoreData}
  {hclaw : G.IsClawFree}

/-- Recover the preceding comparison interface without imposing final-hole
clone existence on the endpoint alternatives. -/
theorem toTerminalCloneComparisonAnalysis
    (C : InitializationInteriorTerminalCloneData T)
    (A : TwoIncomingTerminalInteriorCloneConsequences T hclaw C) :
    TwoIncomingTerminalCloneComparisonAnalysis T hclaw := by
  classical
  refine { terminalGeometry := ?_ }
  intro source source' target hne incoming incoming' hsource hsource'
  let left := C.witnessOfInterior incoming hsource
  let right := C.witnessOfInterior incoming' hsource'
  obtain ⟨hsame, hdistinct⟩ :=
    A.terminalGeometry hne incoming incoming' hsource hsource'
  refine ⟨left, right, ?_, ?_⟩
  · intro hcenter
    apply hsame
    simpa [left, right, centerOfInterior] using hcenter
  · intro hcenter
    apply hdistinct
    simpa [left, right, centerOfInterior] using hcenter

end InitializationInteriorTerminalCloneData

namespace InitializationTerminalCoreData

/-- Conditional paper-facing Lemma 14 bridge with final-hole clone witnesses
scoped exactly to the two-incoming interior case used in the manuscript. -/
theorem paperLemma14_of_interiorTerminalCloneData_and_consequences
    (T : I.InitializationTerminalCoreData)
    (hclaw : G.IsClawFree)
    (C : InitializationInteriorTerminalCloneData T)
    (A : TwoIncomingTerminalInteriorCloneConsequences T hclaw C) :
    PaperLemma14Conclusion I := by
  exact T.paperLemma14_of_terminalCloneComparisonAnalysis hclaw
    (C.toTerminalCloneComparisonAnalysis A)

end InitializationTerminalCoreData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
