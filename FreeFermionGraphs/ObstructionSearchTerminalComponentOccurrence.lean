import FreeFermionGraphs.ObstructionSearchTerminalComponentAvoidance

/-!
# Lemma 14(iv): a missing terminal-component vertex identifies an executed path

In the proof of Lemma 14(i), reused in Lemma 14(iv), the manuscript argues that
if a vertex of `P ∩ C_b` were absent from the current hole, then it must have
been removed by one of the preceding Definition 19 path blocks.  Since path
components of one fixed-pairing family are disjoint, that executed path must be
`P` itself.

The carrier-persistence and component-avoidance results already formalized give
this implication directly.  This module packages the conclusion at the finite
history-context level and then states it on the exact positive manuscript
terminal hole.  It also derives the literal stopping-rule fact that the
terminal obstruction path is not among the paths appended by the search.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace FixedPairingPathFamily

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}
  {D : ConcretePathDeformation O Cprime}

namespace Lemma11AHistoryContext

/-- A component occurs as the current path, or as one of the represented prior
paths in the positive-history case. -/
def ContainsComponent
    (X : D.Lemma11AHistoryContext) (P : Set V) : Prop :=
  match X with
  | .first _ => Set.range D.path.vertex = P
  | .later H =>
      (∃ r : Nat, r < H.priorCount ∧
        Set.range (H.history.block r).path.vertex = P) ∨
      Set.range D.path.vertex = P

/-- Component avoidance is exactly non-occurrence among the paths represented
by the finite history context. -/
theorem avoidsComponent_iff_not_containsComponent
    (X : D.Lemma11AHistoryContext) (P : Set V) :
    X.AvoidsComponent P ↔ ¬X.ContainsComponent P := by
  cases X with
  | first _ =>
      simp [AvoidsComponent, ContainsComponent]
  | later H =>
      change
        ((∀ r : Nat, r < H.priorCount →
            Set.range (H.history.block r).path.vertex ≠ P) ∧
          Set.range D.path.vertex ≠ P) ↔
        ¬((∃ r : Nat, r < H.priorCount ∧
            Set.range (H.history.block r).path.vertex = P) ∨
          Set.range D.path.vertex = P)
      constructor
      · rintro ⟨hprior, hcurrent⟩ hcontains
        rcases hcontains with ⟨r, hr, hEq⟩ | hEq
        · exact hprior r hr hEq
        · exact hcurrent hEq
      · intro hnot
        constructor
        · intro r hr hEq
          exact hnot (Or.inl ⟨r, hr, hEq⟩)
        · intro hEq
          exact hnot (Or.inr hEq)

/-- If an original-hole `C_b` vertex of a `bd` component is absent from the
current final hole, that component must occur among the represented executed
paths.

This is the carrier-level form of the manuscript sentence that such a vertex
would be a removed `k_(p-1)^(q)` for some preceding block `q`. -/
theorem containsComponent_of_mem_bdComponent_of_not_mem_currentFinalHole
    (X : D.Lemma11AHistoryContext)
    {P : Set V} {x : V}
    (hP : P ∈ O.bdPaths)
    (hxP : x ∈ P)
    (hxCb : x ∈ O.Cb)
    (hxExact : ExactlyOneOfFour x O.Ca O.Cb O.Cc O.Cd)
    (hxOriginal : x ∈ Set.range X.originalHole.vertex)
    (hxNotFinal : x ∉ Set.range D.finalHole.vertex) :
    X.ContainsComponent P := by
  by_contra hnot
  have havoidComponent : X.AvoidsComponent P :=
    (X.avoidsComponent_iff_not_containsComponent P).2 hnot
  have havoidAll : X.AvoidsAllPaths x :=
    X.avoidsAllPaths_of_mem_bdComponent
      hP hxP hxCb hxExact havoidComponent
  exact hxNotFinal
    (X.mem_currentFinalHole_of_mem_originalHole_of_avoids
      hxOriginal havoidAll)

end Lemma11AHistoryContext

end ConcretePathDeformation

namespace SearchPathHistoryWitness

variable {O : FixedPairingPathFamily G} {Cprime : Set V}
  {S : SearchDeformation O Cprime}
  {originalHole : IndexedInducedHole G} {P : Set V}

/-- Every component represented by an actual search-history witness is itself
an output path of that search.  The current path uses `output_mem`; prior paths
use the literal provenance field `prior_output_mem`. -/
theorem output_mem_of_context_containsComponent
    (A : SearchPathHistoryWitness S originalHole P)
    {Q : Set V}
    (hQ : A.context.ContainsComponent Q) :
    Q ∈ S.paths := by
  generalize hctx : A.context = X at hQ
  cases X with
  | first _ =>
      change Set.range A.block.path.vertex = Q at hQ
      rw [A.path_eq] at hQ
      rw [← hQ]
      exact A.output_mem
  | later H =>
      change
        (∃ r : Nat, r < H.priorCount ∧
          Set.range (H.history.block r).path.vertex = Q) ∨
        Set.range A.block.path.vertex = Q at hQ
      rcases hQ with ⟨r, hr, hEq⟩ | hEq
      · rw [← hEq]
        exact A.prior_output_mem H hctx r hr
      · rw [A.path_eq] at hEq
        rw [← hEq]
        exact A.output_mem

end SearchPathHistoryWitness

variable {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ObstructionSearchInitialization

variable {I : ObstructionSearchInitialization families Cprime}

namespace OrderedOSExecution

/-- Positive-execution specialization on the manuscript terminal hole
`C_j^(m)`: a missing original-hole `C_b` vertex forces its terminal `bd`
component to occur in the finite history of the last concrete block. -/
theorem containsComponent_of_mem_bdComponent_of_not_mem_manuscriptFinalHole
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : OrderedOSExecution I source originalHole)
    (hpos : 0 < X.blockCount)
    {P : Set V} {x : V}
    (hP : P ∈ (families (I.pairing source)).bdPaths)
    (hxP : x ∈ P)
    (hxCb : x ∈ (families (I.pairing source)).Cb)
    (hxExact : ExactlyOneOfFour x
      (families (I.pairing source)).Ca
      (families (I.pairing source)).Cb
      (families (I.pairing source)).Cc
      (families (I.pairing source)).Cd)
    (hxOriginal : x ∈ Set.range originalHole.vertex)
    (hxNotFinal : x ∉ Set.range X.manuscriptFinalHole.vertex) :
    (X.blockContext (X.lastBlockIndex hpos)).ContainsComponent P := by
  have hxContext :
      x ∈ Set.range
        (X.blockContext (X.lastBlockIndex hpos)).originalHole.vertex := by
    rw [X.blockContext_originalHole (X.lastBlockIndex hpos)]
    exact hxOriginal
  have hxNotLastFinal :
      x ∉ Set.range
        (X.concreteBlock (X.lastBlockIndex hpos)).finalHole.vertex := by
    intro hxLast
    apply hxNotFinal
    rw [X.manuscriptFinalHole_eq_lastBlockFinalHole hpos]
    exact hxLast
  exact
    ConcretePathDeformation.Lemma11AHistoryContext.containsComponent_of_mem_bdComponent_of_not_mem_currentFinalHole
      (X.blockContext (X.lastBlockIndex hpos))
      hP hxP hxCb hxExact hxContext hxNotLastFinal

/-- A component represented in the history of an indexed execution block is an
actual output path of that same initialized search. -/
theorem output_mem_of_blockContext_containsComponent
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : OrderedOSExecution I source originalHole)
    (i : Fin X.blockCount) {P : Set V}
    (hP : (X.blockContext i).ContainsComponent P) :
    P ∈ (I.output source).paths := by
  exact
    (X.history.witness (X.path_mem i)).output_mem_of_context_containsComponent hP

end OrderedOSExecution

namespace InitializationTerminalCoreData

/-- Nearest-target selection places the obstruction target on the terminal
path. -/
theorem target_mem_terminalPath
    (T : I.InitializationTerminalCoreData)
    {source target : I.Node}
    (incoming : I.graph.Arc source target) :
    (target : V) ∈ Set.range (T.terminalPath target).vertex := by
  obtain ⟨q, htarget, _hnearest⟩ :=
    T.nearestTarget.obstruction_nearest incoming
  exact ⟨q, htarget⟩

/-- The stopping rule excludes the obstruction target from every path actually
appended by its incoming search. -/
theorem target_not_mem_executionPath
    (T : I.InitializationTerminalCoreData)
    {source target : I.Node}
    (incoming : I.graph.Arc source target)
    (i : Fin (T.executionTrace.execution source).blockCount) :
    (target : V) ∉ (T.executionTrace.execution source).path i := by
  exact (T.executionTrace.execution source).otherSource_not_mem_path
    i target (T.nearestTarget.target_ne_source incoming)

/-- The terminal obstruction path cannot equal any path actually appended by
the initialized search. -/
theorem terminalPath_ne_executionPath
    (T : I.InitializationTerminalCoreData)
    {source target : I.Node}
    (incoming : I.graph.Arc source target)
    (i : Fin (T.executionTrace.execution source).blockCount) :
    Set.range (T.terminalPath target).vertex ≠
      (T.executionTrace.execution source).path i := by
  intro hEq
  apply T.target_not_mem_executionPath incoming i
  rw [← hEq]
  exact T.target_mem_terminalPath incoming

/-- The terminal obstruction path is not one of the output paths of the search
which stopped on it. -/
theorem terminalPath_not_mem_outputPaths
    (T : I.InitializationTerminalCoreData)
    {source target : I.Node}
    (incoming : I.graph.Arc source target) :
    Set.range (T.terminalPath target).vertex ∉
      (I.output source).paths := by
  intro hmem
  obtain ⟨i, hi⟩ :=
    (T.executionTrace.execution source).output_path hmem
  exact T.terminalPath_ne_executionPath incoming i hi.symm

/-- The terminal path cannot occur in the finite history context of the last
positive execution block, because every represented component is an output
path while the stopping rule proves that the terminal path was not appended. -/
theorem terminalPath_not_containsComponent_lastBlock
    (T : I.InitializationTerminalCoreData)
    {source target : I.Node}
    (incoming : I.graph.Arc source target)
    (hpos : 0 < (T.executionTrace.execution source).blockCount) :
    ¬((T.executionTrace.execution source).blockContext
        ((T.executionTrace.execution source).lastBlockIndex hpos)).ContainsComponent
      (Set.range (T.terminalPath target).vertex) := by
  intro hcontains
  apply T.terminalPath_not_mem_outputPaths incoming
  exact OrderedOSExecution.output_mem_of_blockContext_containsComponent
    (T.executionTrace.execution source)
    ((T.executionTrace.execution source).lastBlockIndex hpos) hcontains

/-- Conditional form of the manuscript inclusion
`P ∩ C_b ⊆ C_j^(m)`.  Once the terminal path is identified as the relevant
`bd` component and the selected `C_b` vertex is placed on the initialized
original hole, the history/output linkage and stopping rule force it to persist
to the exact manuscript terminal hole. -/
theorem terminalCb_mem_manuscriptFinalHole
    (T : I.InitializationTerminalCoreData)
    {source target : I.Node}
    (incoming : I.graph.Arc source target)
    (hpos : 0 < (T.executionTrace.execution source).blockCount)
    {x : V}
    (hcomponent : Set.range (T.terminalPath target).vertex ∈
      (families (I.pairing source)).bdPaths)
    (hxPath : x ∈ Set.range (T.terminalPath target).vertex)
    (hxCb : x ∈ (families (I.pairing source)).Cb)
    (hxExact : ExactlyOneOfFour x
      (families (I.pairing source)).Ca
      (families (I.pairing source)).Cb
      (families (I.pairing source)).Cc
      (families (I.pairing source)).Cd)
    (hxOriginal : x ∈ Set.range T.executionTrace.originalHole.vertex) :
    x ∈ Set.range
      (T.executionTrace.execution source).manuscriptFinalHole.vertex := by
  by_contra hxNotFinal
  have hcontains :=
    OrderedOSExecution.containsComponent_of_mem_bdComponent_of_not_mem_manuscriptFinalHole
      (T.executionTrace.execution source) hpos hcomponent hxPath hxCb hxExact
        hxOriginal hxNotFinal
  exact T.terminalPath_not_containsComponent_lastBlock
    incoming hpos hcontains

end InitializationTerminalCoreData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
