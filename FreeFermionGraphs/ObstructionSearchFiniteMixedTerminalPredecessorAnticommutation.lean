import FreeFermionGraphs.Lemma11Complete
import FreeFermionGraphs.ObstructionSearchFiniteMixedTerminalPredecessorOccurrence

/-!
# Deriving finite predecessor anticommutation

The finite predecessor occurrence still stored anticommutation with its active
path as an independent field.  This is forced by dependent-set membership and
final degree three.  If the predecessor commuted with the path, the complete
Lemma 11(b) theorem for the block's recorded side would give final degree four.

This module removes anticommutation from the primitive terminal propagation
data and derives it from the local finite Definition 19 block.
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

/-- A finite first-block predecessor occurrence without a separately supplied
anticommutation certificate. -/
structure FiniteMixedSideFirstBlockPredecessorDegreeOccurrence
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (source : I.Node)
    (previous : V) where
  blockIndex : Fin
    (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
      source).blockCount
  block_initial_eq_original :
    Set.range
        ((T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
          source).block blockIndex).initialHole.vertex =
      Set.range
        T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
  step : Nat
  mem_dependent :
    previous ∈
      ((T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
        source).block blockIndex).dependentAt step
  finalDegree_three :
    ((T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
      source).block blockIndex).finalHole.externalDegree previous = 3

namespace FiniteMixedSideFirstBlockPredecessorDegreeOccurrence

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}
  {source : I.Node} {previous : V}

/-- Dependent-set membership supplies membership in the prime carrier. -/
theorem mem_prime
    (W : FiniteMixedSideFirstBlockPredecessorDegreeOccurrence
      T source previous) :
    previous ∈ Cprime :=
  ConcretePathDeformation.mem_prime_of_mem_dependentAt
    ((T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
      source).block W.blockIndex)
    W.mem_dependent

/-- Final degree three rules out the commuting branch of Lemma 11(b), which
would force final degree four. -/
theorem anticommutes
    (W : FiniteMixedSideFirstBlockPredecessorDegreeOccurrence
      T source previous)
    (hclaw : G.IsClawFree) :
    ((T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
      source).block W.blockIndex).path.AnticommutesWith previous := by
  let X := T.execution.toInitializationFiniteMixedSideOSExecutionData
  let D := (X.ordered source).block W.blockIndex
  let side := (X.ordered source).side W.blockIndex
  let A := D.reorient side
  by_contra hcomm
  have hData : A.FullDefinition19Lemma11AData := by
    simpa [A, D, side, X] using
      (X.ordered source).localData W.blockIndex
  have huA : previous ∈ A.dependentAt W.step := by
    change previous ∈ (D.reorient side).dependentAt W.step
    rw [D.reorient_dependentAt side W.step]
    exact W.mem_dependent
  have hcommA : ¬A.path.AnticommutesWith previous := by
    intro hantiA
    apply hcomm
    simpa [A, D, ConcretePathDeformation.reorient_path] using hantiA
  have hfourA :=
    (A.lemma11b_of_fullDefinition19NeighborhoodData
      hData.neighborhood hclaw huA hcommA).1
  have hfour : D.finalHole.externalDegree previous = 4 := by
    simpa [A, D, side, ConcretePathDeformation.finalDegree] using hfourA
  have hthree : D.finalHole.externalDegree previous = 3 := by
    simpa [D, X] using W.finalDegree_three
  omega

/-- Recover the prior finite predecessor occurrence, with anticommutation
proved from Lemma 11(b). -/
def toPredecessorOccurrence
    (W : FiniteMixedSideFirstBlockPredecessorDegreeOccurrence
      T source previous)
    (hclaw : G.IsClawFree) :
    FiniteMixedSideFirstBlockPredecessorOccurrence T source previous where
  blockIndex := W.blockIndex
  block_initial_eq_original := W.block_initial_eq_original
  step := W.step
  mem_dependent := W.mem_dependent
  anticommutes := W.anticommutes hclaw
  finalDegree_three := W.finalDegree_three

end FiniteMixedSideFirstBlockPredecessorDegreeOccurrence

/-- Finite distinct-clone propagation after removing predecessor
anticommutation from the certificate boundary. -/
structure FiniteMixedSideDistinctClonePropagationFromDegreeOccurrence
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (source target : I.Node)
    (incoming : I.graph.Arc source target) where
  previous : V
  predecessorOccurrence :
    Nonempty
      (FiniteMixedSideFirstBlockPredecessorDegreeOccurrence T source previous)
  center : V
  propagatedNeighbor : V
  adj_previous : G.Adj center previous
  adj_propagatedNeighbor : G.Adj center propagatedNeighbor
  previous_ne_propagatedNeighbor : previous ≠ propagatedNeighbor
  propagatedNeighbor_ne_previousNeighbor :
    ∀ q : Fin
        T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.card,
      G.Adj previous
          (T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex q) →
        propagatedNeighbor ≠
          T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex q
  propagatedNeighbor_mem_originalHole :
    propagatedNeighbor ∈ Set.range
      T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
  cloneGeometry :
    FiniteMixedSideDistinctCloneGeometryWithoutPreviousPair
      T target center previous propagatedNeighbor

namespace FiniteMixedSideDistinctClonePropagationFromDegreeOccurrence

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}
  {source target : I.Node}
  {incoming : I.graph.Arc source target}

/-- Choose a concrete predecessor occurrence only when converting to the prior
interface; its anticommutation is derived from Lemma 11(b). -/
noncomputable def toPropagationFromOccurrence
    (X : FiniteMixedSideDistinctClonePropagationFromDegreeOccurrence
      T source target incoming)
    (hclaw : G.IsClawFree) :
    FiniteMixedSideDistinctClonePropagationFromOccurrence
      T source target incoming := by
  let W : FiniteMixedSideFirstBlockPredecessorDegreeOccurrence
      T source X.previous :=
    Classical.choice X.predecessorOccurrence
  exact
    { previous := X.previous
      predecessorOccurrence := ⟨W.toPredecessorOccurrence hclaw⟩
      center := X.center
      propagatedNeighbor := X.propagatedNeighbor
      adj_previous := X.adj_previous
      adj_propagatedNeighbor := X.adj_propagatedNeighbor
      previous_ne_propagatedNeighbor := X.previous_ne_propagatedNeighbor
      propagatedNeighbor_ne_previousNeighbor :=
        X.propagatedNeighbor_ne_previousNeighbor
      propagatedNeighbor_mem_originalHole :=
        X.propagatedNeighbor_mem_originalHole
      cloneGeometry := X.cloneGeometry }

/-- The degree-only occurrence package still yields the final distinct-clone
contradiction. -/
theorem false_of_clawFree
    (X : FiniteMixedSideDistinctClonePropagationFromDegreeOccurrence
      T source target incoming)
    (hclaw : G.IsClawFree) : False :=
  (X.toPropagationFromOccurrence hclaw).false_of_clawFree hclaw

end FiniteMixedSideDistinctClonePropagationFromDegreeOccurrence

/-- Same-clone geometry or finite distinct-clone propagation whose predecessor
anticommutation is derived from dependent membership and degree. -/
inductive FiniteMixedSideTwoIncomingInteriorGeometryFromDegreeOccurrences
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (source source' target : I.Node)
    (incoming : I.graph.Arc source target)
    (incoming' : I.graph.Arc source' target) : Prop where
  | sameClone :
      Nonempty
        ((T.terminalPath target).SameCloneTerminalNeighborhood (target : V)) →
      FiniteMixedSideTwoIncomingInteriorGeometryFromDegreeOccurrences
        T source source' target incoming incoming'
  | distinctClone :
      (Nonempty
          (FiniteMixedSideDistinctClonePropagationFromDegreeOccurrence
            T source target incoming) ∨
        Nonempty
          (FiniteMixedSideDistinctClonePropagationFromDegreeOccurrence
            T source' target incoming')) →
      FiniteMixedSideTwoIncomingInteriorGeometryFromDegreeOccurrences
        T source source' target incoming incoming'

/-- Pairwise finite terminal analysis with predecessor anticommutation removed
from the primitive distinct-clone data. -/
structure FiniteMixedSideTwoIncomingTerminalPredecessorDegreeAnalysis
    (T : I.InitializationFiniteMixedSideTerminalCoreData) : Prop where
  interiorGeometry :
    ∀ ⦃source source' target : I.Node⦄
      (hne : source ≠ source')
      (incoming : I.graph.Arc source target)
      (incoming' : I.graph.Arc source' target),
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source target) ≠ (target : V) →
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source' target) ≠ (target : V) →
        FiniteMixedSideTwoIncomingInteriorGeometryFromDegreeOccurrences
          T source source' target incoming incoming'

namespace FiniteMixedSideTwoIncomingTerminalPredecessorDegreeAnalysis

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}

/-- Convert the degree-only predecessor analysis to the prior existential
occurrence interface. -/
noncomputable def toTerminalOccurrenceAnalysis
    (A : FiniteMixedSideTwoIncomingTerminalPredecessorDegreeAnalysis T)
    (hclaw : G.IsClawFree) :
    FiniteMixedSideTwoIncomingTerminalOccurrenceAnalysis T where
  interiorGeometry := by
    intro source source' target hne incoming incoming' hsource hsource'
    rcases A.interiorGeometry
        hne incoming incoming' hsource hsource' with hsame | hdistinct
    · exact
        FiniteMixedSideTwoIncomingInteriorGeometryFromOccurrences.sameClone
          hsame
    · apply
        FiniteMixedSideTwoIncomingInteriorGeometryFromOccurrences.distinctClone
      rcases hdistinct with hleft | hright
      · obtain ⟨X⟩ := hleft
        exact Or.inl ⟨X.toPropagationFromOccurrence hclaw⟩
      · obtain ⟨X⟩ := hright
        exact Or.inr ⟨X.toPropagationFromOccurrence hclaw⟩

end FiniteMixedSideTwoIncomingTerminalPredecessorDegreeAnalysis

namespace InitializationFiniteMixedSideTerminalCoreData

/-- Lemma 14 from a finite terminal analysis in which predecessor
anticommutation is a consequence of Lemma 11(b), not an independent
propagation certificate. -/
theorem lemma14_of_terminalPredecessorDegreeAnalysis
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (A : FiniteMixedSideTwoIncomingTerminalPredecessorDegreeAnalysis T)
    (hclaw : G.IsClawFree) :
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
              I.dependentSet source' = {(target : V)}))) :=
  T.lemma14_of_terminalOccurrenceAnalysis
    (A.toTerminalOccurrenceAnalysis hclaw) hclaw

end InitializationFiniteMixedSideTerminalCoreData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
