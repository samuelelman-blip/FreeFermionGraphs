import FreeFermionGraphs.ObstructionSearchTerminalComponentOccurrence

/-!
# Lemma 14(iv): the terminal obstruction path was not appended

For an obstruction arc `source → target`, the nearest-target rule places
`target` on the terminal path.  The initialized search stopping rule says that
every path actually appended by the search for `source` avoids every other
initializer, including `target`.  Hence the terminal path is distinct from
every executed path and is not a member of the output path family.

This is the literal stopping-rule fact needed to contradict occurrence of the
terminal component in the execution history.  No terminal-hole, clone, degree,
or Lemma 14 conclusion is assumed.
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

namespace InitializationTerminalCoreData

/-- The obstruction target lies on its terminal path by nearest-target
selection. -/
theorem target_mem_terminalPath
    (T : I.InitializationTerminalCoreData)
    {source target : I.Node}
    (incoming : I.graph.Arc source target) :
    (target : V) ∈ Set.range (T.terminalPath target).vertex := by
  obtain ⟨q, htarget, _hnearest⟩ :=
    T.nearestTarget.obstruction_nearest incoming
  exact ⟨q, htarget⟩

/-- The target is absent from every path actually appended by its incoming
search. -/
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

/-- The terminal obstruction component is not one of the output paths of the
search which stopped on it. -/
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

end InitializationTerminalCoreData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
