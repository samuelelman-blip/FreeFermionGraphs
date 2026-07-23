import FreeFermionGraphs.ObstructionSearchTerminalPredecessorAnticommutation

/-!
# Paper-facing fidelity gates

This module states the manuscript-facing content separately from the internal
certificate structures used while constructing the proofs.

The purpose is not to duplicate proofs.  It fixes the mathematical target at
an integration boundary so that later refactors cannot silently change the
hole stage, weaken a conclusion, or hide part of a manuscript lemma in an
unqualified theorem name.

At present Lemma 11(b) is exported from its literal Definition 19/20 data.
Lemma 14 is exported only conditionally, because the long two-search terminal
argument has not yet been constructed from the initialized executions.  There
is deliberately no unconditional theorem named `paperLemma14` in this module.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace FixedPairingPathFamily

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- The paper-facing conclusion of Lemma 11(b) for one dependent vertex.

The degree is stated directly on `D.finalHole`, corresponding to the
manuscript hole `C^(r)`.  This avoids routing the public statement through the
step-insensitive implementation abbreviation `finalDegree`.
-/
def PaperLemma11BConclusion
    (D : ConcretePathDeformation O Cprime) (s : Nat) (u : V) : Prop :=
  D.finalHole.externalDegree u = 4 ∧
    O.EarlierAnticommutingWitnessInUniqueBDPath
      D.dependentAt D.path.AnticommutesWith s u

/-- Paper Lemma 11(b), with the final-hole stage made explicit.

For `u ∈ U^(r,s)` commuting with the path operator, the manuscript concludes
that `Delta_(C^(r))(u) = 4` and that an earlier dependent anticommuting vertex
lies in the same fixed-pairing path component.
-/
theorem paperLemma11b
    (D : ConcretePathDeformation O Cprime)
    (X : D.Lemma11AHistoryContext)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (huPrime : u ∈ Cprime)
    (hu : u ∈ D.dependentAt s)
    (hcomm : ¬D.path.AnticommutesWith u) :
    PaperLemma11BConclusion D s u := by
  unfold PaperLemma11BConclusion
  rcases (D.lemma11 X hclaw huPrime).2 s hu hcomm with
    ⟨hdegree, hwitness⟩
  refine ⟨?_, hwitness⟩
  simpa [ConcretePathDeformation.finalDegree] using hdegree

end ConcretePathDeformation

variable {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ObstructionSearchInitialization

variable {I : ObstructionSearchInitialization families Cprime}

/-- Exact four-part conclusion of manuscript Lemma 14 at initialization.

This proposition contains no terminal-claw or propagation certificate.  Such
certificates may appear only as premises of explicitly conditional bridge
theorems proving this proposition.
-/
def PaperLemma14Conclusion
    (I : ObstructionSearchInitialization families Cprime) : Prop :=
  (∀ source : I.Node,
      (I.output source).run = none ∨
        ∃ F : FullDefinition19Deformation
            (families (I.pairing source)) Cprime,
          (I.output source).run = some F) ∧
    I.graph.IsBipartiteByPairing I.pairing ∧
    (∀ ⦃source source' : I.Node⦄,
      source ≠ source' →
      I.pairing source = I.pairing source' →
        Disjoint (I.output source).paths
          (I.output source').paths) ∧
    ((∀ target : I.Node, I.graph.AtMostTwoIncoming target) ∧
      ∀ ⦃source source' target : I.Node⦄,
        source ≠ source' →
        I.graph.Arc source target →
        I.graph.Arc source' target →
          ((I.dependentSet source = {(target : V)} ∧
              I.dependentSet source' ≠ {(target : V)}) ∨
            (I.dependentSet source ≠ {(target : V)} ∧
              I.dependentSet source' = {(target : V)})))

namespace FirstBlockPredecessorDegreeOccurrence

variable {T : I.InitializationTerminalCoreData}
  {source : I.Node} {previous : V}

/-- Stage check used by the reviewed Lemma 14 distinct-clone reduction.

Both the supplied degree-three fact and the degree-four contradiction from
Lemma 11(b) refer to the final hole of the same concrete path block.  The
anticommutation conclusion is therefore not obtained by comparing degrees on
different deformation stages.
-/
theorem paperStageCheck
    (W : FirstBlockPredecessorDegreeOccurrence T source previous)
    (hclaw : G.IsClawFree) :
    ((T.executionTrace.execution source).concreteBlock
        W.blockIndex).path.AnticommutesWith previous ∧
      ((T.executionTrace.execution source).concreteBlock
        W.blockIndex).finalHole.externalDegree previous = 3 := by
  exact ⟨W.anticommutes hclaw, W.finalDegree_three⟩

end FirstBlockPredecessorDegreeOccurrence

namespace InitializationTerminalCoreData

/-- Conditional bridge to the exact paper statement.

The theorem name records the remaining non-paper premise.  It must not be
renamed to an unconditional `paperLemma14` until
`TwoIncomingTerminalPredecessorDegreeAnalysis` has itself been constructed
from the literal initialized obstruction-search executions.
-/
theorem paperLemma14_of_terminalPredecessorDegreeAnalysis
    (T : I.InitializationTerminalCoreData)
    (hclaw : G.IsClawFree)
    (A : TwoIncomingTerminalPredecessorDegreeAnalysis T hclaw) :
    PaperLemma14Conclusion I := by
  simpa only [PaperLemma14Conclusion] using
    T.lemma14_of_terminalPredecessorDegreeAnalysis hclaw A

end InitializationTerminalCoreData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
