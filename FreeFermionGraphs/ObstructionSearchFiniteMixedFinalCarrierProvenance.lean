import FreeFermionGraphs.ObstructionSearchFiniteMixedTerminalContainment

/-!
# Carrier provenance for finite mixed-side final holes

A single replacement adds only its introduced vertex.  Therefore every vertex
of the final hole of one path block either belonged to the block's initial hole
or lies on that block's active path.  Iterating over the literal finite block
trace shows that every vertex of the manuscript terminal hole either came from
the initialized original hole or lies on an appended execution path.

For an obstruction target, both alternatives are impossible: the initializer
clone certificate puts it outside the original hole, and the stopping rule
excludes it from every appended path.  Hence the target is outside each
positive final execution hole.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace IndexedInducedHole

/-- Every vertex of a deformed hole is either an old carrier vertex or the
single introduced vertex. -/
theorem mem_range_or_eq_introduced_of_mem_range_deform
    (C : IndexedInducedHole G)
    {introduced x : V} {i : Fin C.card}
    (h : C.SingleVertexDeformation introduced i)
    (hx : x ∈ Set.range (C.deform h).vertex) :
    x ∈ Set.range C.vertex ∨ x = introduced := by
  obtain ⟨q, hq⟩ := hx
  by_cases hqi : q = i
  · right
    subst q
    simpa using hq.symm
  · left
    refine ⟨q, ?_⟩
    have haway := C.deform_vertex_away h hqi
    exact haway.symm.trans hq

end IndexedInducedHole

namespace FixedPairingPathFamily

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

namespace ConcreteDeformationStep

/-- Step-level carrier provenance. -/
theorem mem_before_or_eq_introduced_of_mem_after
    (S : ConcreteDeformationStep O Cprime)
    {x : V}
    (hx : x ∈ Set.range S.after.vertex) :
    x ∈ Set.range S.before.vertex ∨ x = S.introduced := by
  simpa [ConcreteDeformationStep.after] using
    S.before.mem_range_or_eq_introduced_of_mem_range_deform
      S.deformation hx

end ConcreteDeformationStep

namespace ConcretePathDeformation

/-- Every vertex surviving through the first `n+1` steps of one path block
came from the block's initial hole or lies on the common active path. -/
theorem mem_initialHole_or_mem_path_of_mem_stepAfter
    (D : ConcretePathDeformation O Cprime)
    {x : V} (n : Nat) (hn : n < D.deformation.stepCount)
    (hx : x ∈ Set.range (D.deformation.step ⟨n, hn⟩).after.vertex) :
    x ∈ Set.range D.initialHole.vertex ∨
      x ∈ Set.range D.path.vertex := by
  induction n with
  | zero =>
      rcases
        ConcreteDeformationStep.mem_before_or_eq_introduced_of_mem_after
          (D.deformation.step ⟨0, hn⟩) hx with
        hbefore | hintroduced
      · exact Or.inl (by
          simpa [ConcretePathDeformation.initialHole,
            ConcretePathDeformation.firstIndex] using hbefore)
      · right
        rw [hintroduced]
        rw [← D.activePath_eq ⟨0, hn⟩]
        exact (D.deformation.step ⟨0, hn⟩).introduced_mem_activePath
  | succ n ih =>
      let current : Fin D.deformation.stepCount := ⟨n + 1, hn⟩
      rcases
        ConcreteDeformationStep.mem_before_or_eq_introduced_of_mem_after
          (D.deformation.step current) (by simpa [current] using hx) with
        hbefore | hintroduced
      · have hnPrev : n < D.deformation.stepCount := by omega
        let previous : Fin D.deformation.stepCount := ⟨n, hnPrev⟩
        have hchain :
            Set.range (D.deformation.step previous).after.vertex =
              Set.range (D.deformation.step current).before.vertex :=
          D.deformation.carrier_chain (by simp [previous, current])
        have hxPrevious :
            x ∈ Set.range (D.deformation.step previous).after.vertex := by
          rw [hchain]
          exact hbefore
        exact ih hnPrev hxPrevious
      · right
        rw [hintroduced]
        rw [← D.activePath_eq current]
        exact (D.deformation.step current).introduced_mem_activePath

/-- Every vertex in the final hole of one complete path block came from its
initial hole or lies on the block path. -/
theorem mem_initialHole_or_mem_path_of_mem_finalHole
    (D : ConcretePathDeformation O Cprime)
    {x : V}
    (hx : x ∈ Set.range D.finalHole.vertex) :
    x ∈ Set.range D.initialHole.vertex ∨
      x ∈ Set.range D.path.vertex := by
  simpa [ConcretePathDeformation.finalHole,
    ConcretePathDeformation.lastIndex] using
    D.mem_initialHole_or_mem_path_of_mem_stepAfter
      (D.deformation.stepCount - 1) (by omega) hx

namespace FiniteMixedSideSearchTrace

variable {S : SearchDeformation O Cprime}
  {originalHole : IndexedInducedHole G}

/-- Carrier provenance through the first `n+1` actual finite path blocks. -/
theorem mem_originalHole_or_mem_path_through
    (X : FiniteMixedSideSearchTrace S originalHole)
    {x : V} (n : Nat) (hn : n < X.blockCount)
    (hx : x ∈ Set.range (X.block ⟨n, hn⟩).finalHole.vertex) :
    x ∈ Set.range originalHole.vertex ∨
      ∃ q : Fin X.blockCount,
        q.val ≤ n ∧ x ∈ Set.range (X.block q).path.vertex := by
  induction n with
  | zero =>
      rcases (X.block ⟨0, hn⟩).mem_initialHole_or_mem_path_of_mem_finalHole hx with
        hinitial | hpath
      · left
        rw [← X.originalHole_eq]
        exact hinitial
      · exact Or.inr ⟨⟨0, hn⟩, by omega, hpath⟩
  | succ n ih =>
      let current : Fin X.blockCount := ⟨n + 1, hn⟩
      rcases
        (X.block current).mem_initialHole_or_mem_path_of_mem_finalHole
          (by simpa [current] using hx) with
        hinitial | hpath
      · have hnPrev : n < X.blockCount := by omega
        let previous : Fin X.blockCount := ⟨n, hnPrev⟩
        have hchain :
            Set.range (X.block previous).finalHole.vertex =
              Set.range (X.block current).initialHole.vertex :=
          X.chain (by simp [previous, current])
        have hxPrevious :
            x ∈ Set.range (X.block previous).finalHole.vertex := by
          rw [hchain]
          exact hinitial
        rcases ih hnPrev hxPrevious with horiginal | ⟨q, hqle, hxq⟩
        · exact Or.inl horiginal
        · exact Or.inr ⟨q, by omega, hxq⟩
      · exact Or.inr ⟨current, by omega, hpath⟩

end FiniteMixedSideSearchTrace
end ConcretePathDeformation

namespace ObstructionSearchInitialization

variable {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}
  {I : ObstructionSearchInitialization families Cprime}

namespace FiniteMixedSideOSExecution

/-- Lift final-carrier provenance through the literal empty/nonempty execution
split.  The empty branch has no positive block index. -/
theorem mem_originalHole_or_mem_orderedPath_through
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : FiniteMixedSideOSExecution I source originalHole)
    {x : V} (n : Nat) (hn : n < X.toOrdered.blockCount)
    (hx : x ∈ Set.range (X.toOrdered.block ⟨n, hn⟩).finalHole.vertex) :
    x ∈ Set.range originalHole.vertex ∨
      ∃ q : Fin X.toOrdered.blockCount,
        q.val ≤ n ∧ x ∈ X.toOrdered.path q := by
  cases X with
  | empty hrun =>
      omega
  | nonempty data =>
      exact data.literal.trace.mem_originalHole_or_mem_path_through
        n hn hx

end FiniteMixedSideOSExecution

namespace InitializationFiniteMixedSideTerminalCoreData

/-- Every initialized vertex, including an obstruction target, lies outside the
initialized original hole by its literal clone certificate. -/
theorem target_not_mem_originalHole
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (target : I.Node) :
    (target : V) ∉ Set.range
      T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex := by
  rcases T.pairingLabels.initializer_typedClone target with
    ⟨i, hclone, _hpair⟩
  exact hclone.outside

/-- A common obstruction target is outside the exact positive final execution
hole. -/
theorem target_not_mem_manuscriptFinalHole_of_pos
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    {source target : I.Node}
    (incoming : I.graph.Arc source target)
    (hpos :
      0 <
        (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
          source).blockCount) :
    (target : V) ∉ Set.range
      (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
        source).manuscriptFinalHole.vertex := by
  intro htargetFinal
  let Y := T.execution.toInitializationFiniteMixedSideOSExecutionData
  let X := Y.ordered source
  let last := X.lastBlockIndex hpos
  have htargetLast :
      (target : V) ∈ Set.range (X.block last).finalHole.vertex := by
    rw [← X.manuscriptFinalHole_eq_lastBlockFinalHole hpos]
    exact htargetFinal
  rcases (Y.execution source).mem_originalHole_or_mem_orderedPath_through
      last.val last.isLt htargetLast with horiginal | ⟨q, _hqle, hpath⟩
  · exact T.target_not_mem_originalHole target horiginal
  · exact T.target_not_mem_executionPath incoming q hpath

end InitializationFiniteMixedSideTerminalCoreData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
