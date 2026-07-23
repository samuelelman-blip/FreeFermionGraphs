import FreeFermionGraphs.ObstructionSearchTerminalCloneComparison

/-!
# Lemma 14(iv): canonical final-hole clone centres

The manuscript first obtains, for each incoming initialized search, a clone of
the common obstruction target in that search's final hole.  Only after those
per-search facts are fixed does it compare the two displayed centre vertices.

This module separates those quantifiers.  Existence of a final-hole clone is a
per-arc property, while the consequences of equal or distinct centres remain
pairwise properties.  Uniqueness of a clone centre in one induced hole makes
the selected centre independent of the witness chosen from the per-arc
existence proof.

The actual construction of the per-arc witnesses and the two branch
consequences from the terminal search histories remains explicit.
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

/-- Per-arc existence of the target clone in the correctly staged final
execution hole.

This is the direct formal counterpart of the two manuscript statements
`j'' ≺_(C_j^(m)) v` and `j'' ≺_(C_j'^(m')) v'`.  It is intentionally separate
from the later pairwise comparison of `v` and `v'`. -/
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

/-- Conditional paper-facing Lemma 14 bridge with the manuscript quantifier
order made explicit: first one clone witness per incoming arc, then pairwise
consequences of comparing the canonical centres. -/
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
