import FreeFermionGraphs.ObstructionSearchTerminalCloneComparison

/-!
# Lemma 14(iv): canonical final-hole clone centres

The manuscript first obtains a clone of the common obstruction target in each
incoming search's final hole in the two-incoming interior case.  Only after
those scoped per-search facts are fixed does it compare the two displayed
centre vertices.

This module supplies a stronger convenience interface in which final-hole clone
existence is available for every incoming arc.  Existence and pairwise branch
consequences are still separated, and uniqueness makes the selected centre
independent of the chosen witness.  The manuscript-scoped interface, which
requires witnesses only under the interior-target premise, is provided in
`ObstructionSearchTerminalInteriorFinalClones` and is the preferred fidelity
boundary.
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

namespace IncomingTerminalCloneWitness

variable {T : I.InitializationTerminalCoreData}
  {source target : I.Node}
  {incoming : I.graph.Arc source target}

/-- Two clone witnesses for one incoming search select the same index in that
search's final hole. -/
theorem cloneIndex_eq
    (X Y : IncomingTerminalCloneWitness T source target incoming) :
    X.cloneIndex = Y.cloneIndex :=
  X.target_clone.center_eq Y.target_clone

/-- Consequently, the displayed centre vertex is independent of the chosen
final-hole clone witness. -/
theorem center_eq
    (X Y : IncomingTerminalCloneWitness T source target incoming) :
    X.center = Y.center := by
  unfold center
  rw [X.cloneIndex_eq Y]

end IncomingTerminalCloneWitness

/-- Unrestricted per-arc existence of the target clone in the final execution
hole.

This is stronger than the exact Lemma 14(iv) branch, which needs such a witness
only when the target differs from the returned singleton endpoint.  It remains
a useful convenience interface, but paper-facing fidelity should use
`InitializationInteriorTerminalCloneData`. -/
structure InitializationIncomingTerminalCloneData
    (T : I.InitializationTerminalCoreData) : Prop where
  exists_witness :
    ∀ ⦃source target : I.Node⦄
      (incoming : I.graph.Arc source target),
      Nonempty (IncomingTerminalCloneWitness T source target incoming)

namespace InitializationIncomingTerminalCloneData

variable {T : I.InitializationTerminalCoreData}

/-- Select one final-hole clone witness for an incoming arc.  The selected
centre is canonical by `IncomingTerminalCloneWitness.center_eq`. -/
noncomputable def witnessOfIncoming
    (C : InitializationIncomingTerminalCloneData T)
    {source target : I.Node}
    (incoming : I.graph.Arc source target) :
    IncomingTerminalCloneWitness T source target incoming :=
  Classical.choice (C.exists_witness incoming)

/-- The canonical displayed centre for one incoming initialized search. -/
noncomputable def centerOfIncoming
    (C : InitializationIncomingTerminalCloneData T)
    {source target : I.Node}
    (incoming : I.graph.Arc source target) : V :=
  (C.witnessOfIncoming incoming).center

/-- Every supplied witness has the canonical selected centre. -/
theorem center_eq_centerOfIncoming
    (C : InitializationIncomingTerminalCloneData T)
    {source target : I.Node}
    {incoming : I.graph.Arc source target}
    (X : IncomingTerminalCloneWitness T source target incoming) :
    X.center = C.centerOfIncoming incoming :=
  X.center_eq (C.witnessOfIncoming incoming)

end InitializationIncomingTerminalCloneData

/-- The two manuscript continuations after the per-arc clone centres have been
fixed canonically.

The equal-centre implication contains the short same-clone terminal argument.
The unequal-centre implication contains the longer propagation argument.  No
existence or arbitrary choice of clone witnesses is hidden in this pairwise
interface. -/
structure TwoIncomingTerminalCanonicalCloneConsequences
    (T : I.InitializationTerminalCoreData)
    (hclaw : G.IsClawFree)
    (C : InitializationIncomingTerminalCloneData T) : Prop where
  terminalGeometry :
    ∀ ⦃source source' target : I.Node⦄
      (hne : source ≠ source')
      (incoming : I.graph.Arc source target)
      (incoming' : I.graph.Arc source' target),
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source target) ≠ (target : V) →
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source' target) ≠ (target : V) →
        (C.centerOfIncoming incoming = C.centerOfIncoming incoming' →
          Nonempty
            ((T.terminalPath target).SameCloneTerminalNeighborhood
              (target : V))) ∧
        (C.centerOfIncoming incoming ≠ C.centerOfIncoming incoming' →
          (Nonempty
              (DistinctClonePropagationFromDegreeOccurrence
                T hclaw source target incoming) ∨
            Nonempty
              (DistinctClonePropagationFromDegreeOccurrence
                T hclaw source' target incoming')))

namespace InitializationIncomingTerminalCloneData

variable {T : I.InitializationTerminalCoreData}
  {hclaw : G.IsClawFree}

/-- Combine per-arc clone existence with the two canonical branch consequences
to recover the preceding comparison interface. -/
theorem toTerminalCloneComparisonAnalysis
    (C : InitializationIncomingTerminalCloneData T)
    (A : TwoIncomingTerminalCanonicalCloneConsequences T hclaw C) :
    TwoIncomingTerminalCloneComparisonAnalysis T hclaw := by
  classical
  refine { terminalGeometry := ?_ }
  intro source source' target hne incoming incoming' hsource hsource'
  let left := C.witnessOfIncoming incoming
  let right := C.witnessOfIncoming incoming'
  obtain ⟨hsame, hdistinct⟩ :=
    A.terminalGeometry hne incoming incoming' hsource hsource'
  refine ⟨left, right, ?_, ?_⟩
  · intro hcenter
    apply hsame
    simpa [left, right, centerOfIncoming] using hcenter
  · intro hcenter
    apply hdistinct
    simpa [left, right, centerOfIncoming] using hcenter

end InitializationIncomingTerminalCloneData

namespace InitializationTerminalCoreData

/-- Conditional Lemma 14 bridge for the stronger unrestricted per-arc clone
interface.  The manuscript-scoped bridge is supplied by
`paperLemma14_of_interiorTerminalCloneData_and_consequences`. -/
theorem paperLemma14_of_incomingTerminalCloneData_and_canonicalConsequences
    (T : I.InitializationTerminalCoreData)
    (hclaw : G.IsClawFree)
    (C : InitializationIncomingTerminalCloneData T)
    (A : TwoIncomingTerminalCanonicalCloneConsequences T hclaw C) :
    PaperLemma14Conclusion I := by
  exact T.paperLemma14_of_terminalCloneComparisonAnalysis hclaw
    (C.toTerminalCloneComparisonAnalysis A)

end InitializationTerminalCoreData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
