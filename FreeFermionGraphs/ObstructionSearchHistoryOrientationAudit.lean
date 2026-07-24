import FreeFermionGraphs.ObstructionSearchHistory

/-!
# Fidelity audit: orientation of obstruction-search history blocks

The manuscript's fixed-pairing deformation may contain path components from
both `C_a ⊕ C'_c` and `C_b ⊕ C'_d`.  The current `SearchPathHistoryWitness`,
however, represents every output path by a `ConcretePathDeformation` whose
stored Definition 19 geometry is specifically `ACHoleStepGeometry`.

This module makes the resulting strengthening explicit: every path covered by
`SearchHistoryData` is forced into `acPaths`.  The theorem is an audit guard,
not a manuscript conclusion.  It identifies the exact interface that must be
generalized before the two-sided obstruction-search proof can be claimed.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace FixedPairingPathFamily

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

namespace SearchPathHistoryWitness

/-- The current witness type forces its represented output path to be an
`acPaths` component, because its local Definition 19 data stores
`ACHoleStepGeometry` at every concrete step. -/
theorem output_mem_acPaths
    {S : SearchDeformation O Cprime}
    {originalHole : IndexedInducedHole G}
    {P : Set V}
    (A : SearchPathHistoryWitness S originalHole P) :
    P ∈ O.acPaths := by
  have hactive :
      Set.range
          (A.block.deformation.step A.block.firstIndex).activePath.vertex ∈
        O.acPaths :=
    (A.context.currentData.neighborhood.mechanical.stepGeometry
      A.block.firstIndex).base.activePath_ac
  rw [A.block.activePath_eq A.block.firstIndex] at hactive
  rw [A.path_eq] at hactive
  exact hactive

end SearchPathHistoryWitness

namespace SearchHistoryData

/-- Consequently the current search-history interface can only be inhabited
when every output path lies in the `acPaths` half of the fixed-pairing family.
This is stronger than the manuscript's two-sided Definition 19 deformation. -/
theorem paths_subset_acPaths
    {S : SearchDeformation O Cprime}
    {originalHole : IndexedInducedHole G}
    (H : SearchHistoryData S originalHole) :
    S.paths ⊆ O.acPaths := by
  intro P hP
  exact (H.witness hP).output_mem_acPaths

end SearchHistoryData

end FixedPairingPathFamily

end SimpleGraph
