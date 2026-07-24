import FreeFermionGraphs.ObstructionSearchTerminalComponentAvoidance

/-!
# Lemma 14(iv): faithful occurrence information from a missing carrier vertex

The manuscript allows a vertex to belong to one original-hole colour class and
one prime-hole colour class simultaneously.  Corollary 9 therefore allows such
a vertex to occur on one `ac` path and one `bd` path.  From the fact that a
terminal `C_b` vertex is absent from the current hole, carrier persistence only
shows that some represented path contains that vertex.  It does not yet show
that the represented path is the terminal `bd` component.

This module records exactly that weaker, faithful conclusion.  It also retains
the literal stopping-rule theorem that the terminal obstruction path itself was
not appended to the search.  The missing manuscript step is directional: a
missing `C_b` vertex was removed as a `k`-vertex of a `bd` block, rather than
merely occurring as an introduced vertex of an `ac` block.
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

/-- Component avoidance is exactly non-occurrence among the represented paths. -/
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

/-- A vertex occurs on the current path, or on one of the represented prior
paths in the positive-history case. -/
def ContainsVertex
    (X : D.Lemma11AHistoryContext) (x : V) : Prop :=
  match X with
  | .first _ => x ∈ Set.range D.path.vertex
  | .later H =>
      (∃ r : Nat, r < H.priorCount ∧
        x ∈ Set.range (H.history.block r).path.vertex) ∨
      x ∈ Set.range D.path.vertex

/-- Avoidance of every represented path is exactly non-occurrence of the
vertex in the finite history. -/
theorem avoidsAllPaths_iff_not_containsVertex
    (X : D.Lemma11AHistoryContext) (x : V) :
    X.AvoidsAllPaths x ↔ ¬X.ContainsVertex x := by
  cases X with
  | first _ =>
      simp [AvoidsAllPaths, ContainsVertex]
  | later H =>
      change
        ((∀ r : Nat, r < H.priorCount →
            x ∉ Set.range (H.history.block r).path.vertex) ∧
          x ∉ Set.range D.path.vertex) ↔
        ¬((∃ r : Nat, r < H.priorCount ∧
            x ∈ Set.range (H.history.block r).path.vertex) ∨
          x ∈ Set.range D.path.vertex)
      constructor
      · rintro ⟨hprior, hcurrent⟩ hcontains
        rcases hcontains with ⟨r, hr, hmem⟩ | hmem
        · exact hprior r hr hmem
        · exact hcurrent hmem
      · intro hnot
        constructor
        · intro r hr hmem
          exact hnot (Or.inl ⟨r, hr, hmem⟩)
        · intro hmem
          exact hnot (Or.inr hmem)

/-- If an original-hole vertex is absent from the current final hole, then it
occurs on at least one represented path.

This theorem deliberately does not identify whether the occurrence is as an
introduced or removed vertex, nor whether the path belongs to the `ac` or `bd`
component family. -/
theorem containsVertex_of_mem_originalHole_of_not_mem_currentFinalHole
    (X : D.Lemma11AHistoryContext)
    {x : V}
    (hxOriginal : x ∈ Set.range X.originalHole.vertex)
    (hxNotFinal : x ∉ Set.range D.finalHole.vertex) :
    X.ContainsVertex x := by
  by_contra hnot
  have havoid : X.AvoidsAllPaths x :=
    (X.avoidsAllPaths_iff_not_containsVertex x).2 hnot
  exact hxNotFinal
    (X.mem_currentFinalHole_of_mem_originalHole_of_avoids
      hxOriginal havoid)

end Lemma11AHistoryContext

end ConcretePathDeformation

namespace SearchPathHistoryWitness

variable {O : FixedPairingPathFamily G} {Cprime : Set V}
  {S : SearchDeformation O Cprime}
  {originalHole : IndexedInducedHole G} {P : Set V}

/-- Every component represented by an actual search-history witness is itself
an output path of that search. -/
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

/-- A vertex occurrence in an actual history context yields an output path of
that search containing the vertex. -/
theorem exists_output_path_of_context_containsVertex
    (A : SearchPathHistoryWitness S originalHole P)
    {x : V}
    (hx : A.context.ContainsVertex x) :
    ∃ Q : Set V, Q ∈ S.paths ∧ x ∈ Q := by
  generalize hctx : A.context = X at hx
  cases X with
  | first _ =>
      change x ∈ Set.range A.block.path.vertex at hx
      refine ⟨P, A.output_mem, ?_⟩
      rw [← A.path_eq]
      exact hx
  | later H =>
      change
        (∃ r : Nat, r < H.priorCount ∧
          x ∈ Set.range (H.history.block r).path.vertex) ∨
        x ∈ Set.range A.block.path.vertex at hx
      rcases hx with ⟨r, hr, hmem⟩ | hmem
      · refine ⟨Set.range (H.history.block r).path.vertex, ?_, hmem⟩
        exact A.prior_output_mem H hctx r hr
      · refine ⟨P, A.output_mem, ?_⟩
        rw [← A.path_eq]
        exact hmem

end SearchPathHistoryWitness

variable {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ObstructionSearchInitialization

variable {I : ObstructionSearchInitialization families Cprime}

namespace OrderedOSExecution

/-- Positive-execution specialization: an initialized original-hole vertex
missing from the manuscript terminal hole occurs in the finite history context
of the last concrete block. -/
theorem containsVertex_of_mem_originalHole_of_not_mem_manuscriptFinalHole
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : OrderedOSExecution I source originalHole)
    (hpos : 0 < X.blockCount)
    {x : V}
    (hxOriginal : x ∈ Set.range originalHole.vertex)
    (hxNotFinal : x ∉ Set.range X.manuscriptFinalHole.vertex) :
    (X.blockContext (X.lastBlockIndex hpos)).ContainsVertex x := by
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
    ConcretePathDeformation.Lemma11AHistoryContext.containsVertex_of_mem_originalHole_of_not_mem_currentFinalHole
      (X.blockContext (X.lastBlockIndex hpos)) hxContext hxNotLastFinal

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

/-- A represented vertex occurrence in an indexed execution block yields an
actual output path containing that vertex. -/
theorem exists_output_path_of_blockContext_containsVertex
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : OrderedOSExecution I source originalHole)
    (i : Fin X.blockCount) {x : V}
    (hx : (X.blockContext i).ContainsVertex x) :
    ∃ Q : Set V, Q ∈ (I.output source).paths ∧ x ∈ Q := by
  exact
    (X.history.witness (X.path_mem i)).exists_output_path_of_context_containsVertex hx

/-- Consequently a missing initialized carrier vertex lies on some actual
output path.  No component-family or introduced/removed orientation is inferred. -/
theorem exists_output_path_of_mem_originalHole_of_not_mem_manuscriptFinalHole
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : OrderedOSExecution I source originalHole)
    (hpos : 0 < X.blockCount)
    {x : V}
    (hxOriginal : x ∈ Set.range originalHole.vertex)
    (hxNotFinal : x ∉ Set.range X.manuscriptFinalHole.vertex) :
    ∃ Q : Set V, Q ∈ (I.output source).paths ∧ x ∈ Q := by
  exact X.exists_output_path_of_blockContext_containsVertex
    (X.lastBlockIndex hpos)
    (X.containsVertex_of_mem_originalHole_of_not_mem_manuscriptFinalHole
      hpos hxOriginal hxNotFinal)

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

/-- The terminal path cannot occur as a represented component in the last
positive execution block.  This does not exclude its vertices from occurring
on opposite-family paths. -/
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

end InitializationTerminalCoreData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
