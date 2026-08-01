import FreeFermionGraphs.ObstructionSearchFiniteMixedCanonicalEntry

/-!
# First common paths in finite mixed-side obstruction-search executions

This module carries out the manuscript's least-common-path argument on the
literal finite ordered executions.  A common output path has a least index in
the first execution.  Since distinct initializers occur only in their own
first paths, that common path is noninitial in both executions.  The two
earlier-selection rules then produce distinct earlier blocks with a shared
dependent anticommuting witness at the canonical entry of the common path.

No path-disjointness conclusion or Corollary 11 exclusion is assumed here.
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

namespace InitializationFiniteMixedSideOSExecutionData

/-- The least common output path of two distinct initialized finite executions
produces distinct earlier blocks with the shared dependent anticommuting
witness used by the manuscript's Corollary 11 contradiction. -/
theorem firstCommonWitness
    (X : I.InitializationFiniteMixedSideOSExecutionData)
    {source source' : I.Node} {P : Set V}
    (hne : source ≠ source')
    (_hpair : I.pairing source = I.pairing source')
    (hP : P ∈ (I.output source).paths)
    (hP' : P ∈ (I.output source').paths) :
    ∃ (q : Fin (X.ordered source).blockCount)
      (r : Fin (X.ordered source').blockCount),
      (X.ordered source).path q ≠ (X.ordered source').path r ∧
        SharedDependentAnticommutingWitness
          ((X.ordered source).block q).path
          ((X.ordered source').block r).path
          ((X.ordered source).block q).dependentAt
          ((X.ordered source').block r).dependentAt := by
  classical
  let A := X.ordered source
  let B := X.ordered source'
  obtain ⟨iP, hiP⟩ := A.output_path' hP
  let common : Finset (Fin A.blockCount) :=
    Finset.univ.filter fun i =>
      A.path i ∈ (I.output source').paths
  have hcommon : common.Nonempty := by
    refine ⟨iP, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rw [hiP]
    exact hP'
  let i : Fin A.blockCount := common.min' hcommon
  have hiCommon : i ∈ common := Finset.min'_mem common hcommon
  have hiOther : A.path i ∈ (I.output source').paths :=
    (Finset.mem_filter.mp hiCommon).2
  obtain ⟨j, hji⟩ := B.output_path' hiOther
  have hiPos : 0 < i.val := by
    by_contra hnot
    have hiZero : i.val = 0 := by omega
    have hsourceMem : (source : V) ∈ A.path i :=
      (A.initializer_mem_path_iff' i source).2 ⟨rfl, hiZero⟩
    have hsourceOther : (source : V) ∈ B.path j := by
      rw [hji]
      exact hsourceMem
    have hsourceEq :=
      (B.initializer_mem_path_iff' j source).1 hsourceOther
    exact hne hsourceEq.1
  have hjPos : 0 < j.val := by
    by_contra hnot
    have hjZero : j.val = 0 := by omega
    have hsource'Mem : (source' : V) ∈ B.path j :=
      (B.initializer_mem_path_iff' j source').2 ⟨rfl, hjZero⟩
    have hsource'Other : (source' : V) ∈ A.path i := by
      rw [← hji]
      exact hsource'Mem
    have hsource'Eq :=
      (A.initializer_mem_path_iff' i source').1 hsource'Other
    exact hne hsource'Eq.1.symm
  obtain ⟨q, s, hqi, hsDep, hsAnti⟩ := A.earlierSelection' i hiPos
  obtain ⟨r, t, hrj, htDep, htAnti⟩ := B.earlierSelection' j hjPos
  refine ⟨q, r, ?_, ?_⟩
  · intro hEq
    have hqOther : A.path q ∈ (I.output source').paths := by
      rw [hEq]
      exact B.path_mem' r
    have hqCommon : q ∈ common :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ q, hqOther⟩
    have hle : i ≤ q := Finset.min'_le common q hqCommon
    exact (not_lt_of_ge hle) hqi
  · have hentry : A.entry i = B.entry j :=
      X.commonPath_entry_eq i j hji.symm
    refine ⟨A.entry i, s, t, hsDep, ?_, hsAnti, ?_⟩
    · simpa [hentry] using htDep
    · simpa [hentry] using htAnti

end InitializationFiniteMixedSideOSExecutionData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
