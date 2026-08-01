import FreeFermionGraphs.ObstructionSearchFiniteMixedSamePairing

/-!
# Final selection for literal finite mixed-side executions

The empty branch of an initialized obstruction search has no returned
dependent vertex.  The nonempty branch already stores the manuscript's final
selection rule: a returned dependent vertex occurs in a dependent set of an
actual output block and anticommutes with that block.

This module records the missing empty-branch compatibility and derives
same-pairing disjointness of the final dependent sets from the literal finite
executions.  No total `Nat` history or terminal-path conclusion is assumed.
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

namespace FiniteMixedSideOSExecution

/-- Final selection for one possibly empty literal execution.  In the empty
case the compatibility hypothesis rules out a returned dependent vertex. -/
theorem finalSelection
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : FiniteMixedSideOSExecution I source originalHole)
    (dependent_none_of_empty :
      (I.output source).run = none → I.dependent source = none)
    {u : V} (hu : I.dependent source = some u) :
    ∃ (q : Fin X.toOrdered.blockCount) (s : Nat),
      u ∈ (X.toOrdered.block q).dependentAt s ∧
        (X.toOrdered.block q).path.AnticommutesWith u := by
  cases X with
  | empty hRun =>
      have hnone := dependent_none_of_empty hRun
      rw [hnone] at hu
      contradiction
  | nonempty data =>
      exact data.finalSelection hu

end FiniteMixedSideOSExecution

/-- Literal finite executions together with the intrinsic fact that an empty
search output has no final dependent vertex. -/
structure InitializationFiniteMixedSideFinalSelectionData
    (I : ObstructionSearchInitialization families Cprime)
    extends I.InitializationFiniteMixedSideOSExecutionData where
  dependent_none_of_empty : ∀ source : I.Node,
    (I.output source).run = none → I.dependent source = none

namespace InitializationFiniteMixedSideFinalSelectionData

/-- Final selection expressed through the uniform ordered interface. -/
theorem finalSelection
    (X : I.InitializationFiniteMixedSideFinalSelectionData)
    (source : I.Node)
    {u : V} (hu : I.dependent source = some u) :
    ∃ (q : Fin (X.toInitializationFiniteMixedSideOSExecutionData.ordered source).blockCount)
      (s : Nat),
      u ∈ (X.toInitializationFiniteMixedSideOSExecutionData.ordered source).block q
          |>.dependentAt s ∧
        ((X.toInitializationFiniteMixedSideOSExecutionData.ordered source).block q).path
          |>.AnticommutesWith u := by
  exact
    (X.execution source).finalSelection
      (X.dependent_none_of_empty source) hu

/-- Distinct initialized searches of one pairing type have disjoint final
dependent sets.  A common returned vertex would give a shared dependent
anticommuting witness on two output blocks, while finite same-pairing path
disjointness makes those blocks distinct. -/
theorem samePairing_dependentSets_disjoint
    (X : I.InitializationFiniteMixedSideFinalSelectionData)
    (hclaw : G.IsClawFree)
    {source source' : I.Node}
    (hne : source ≠ source')
    (hpair : I.pairing source = I.pairing source') :
    Disjoint (I.dependentSet source) (I.dependentSet source') := by
  let Y := X.toInitializationFiniteMixedSideOSExecutionData
  apply Set.disjoint_left.mpr
  intro u hu hu'
  obtain ⟨q, s, huDep, huAnti⟩ := X.finalSelection source hu
  obtain ⟨r, t, huDep', huAnti'⟩ := X.finalSelection source' hu'
  let Q := (Y.ordered source).path q
  let R := (Y.ordered source').path r
  have hQ : Q ∈ (I.output source).paths :=
    (Y.ordered source).path_mem' q
  have hR : R ∈ (I.output source').paths :=
    (Y.ordered source').path_mem' r
  have hpaths :
      Disjoint (I.output source).paths (I.output source').paths :=
    Y.samePairing_paths_disjoint hclaw hne hpair
  have hQR : Q ≠ R := by
    intro hEq
    exact (Set.disjoint_left.mp hpaths) hQ (hEq ▸ hR)
  have hforbidden :=
    ConcretePathDeformation.FiniteMixedSideLemma11AContext.
      noSharedDependentAnticommutingWitness_of_pairing_eq
        (Y.orderedContextAt source q)
        (Y.orderedContextAt source' r)
        hpair hclaw (by
          simpa [Q, R, FiniteMixedSideOrderedOSExecution.path] using hQR)
  apply hforbidden
  exact ⟨u, s, t, huDep, huDep', huAnti, huAnti'⟩

end InitializationFiniteMixedSideFinalSelectionData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
