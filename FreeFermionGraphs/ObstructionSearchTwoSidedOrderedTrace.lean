import FreeFermionGraphs.ObstructionSearchTwoSidedFirstCommon
import FreeFermionGraphs.ObstructionSearchTwoSidedEarlierSelection

/-!
# Two-sided ordered obstruction-search traces

This module transports the manuscript's least-common-path argument to the
side-correct obstruction-search execution.  The only cross-trace datum retained
is the canonical orientation statement: if two same-pairing searches contain
the same Definition 19 path component, their first introduced endpoint
`j_0^(r)` is the same vertex.

From that statement and the literal ordered-search invariants, the least common
path produces two distinct earlier blocks with a shared dependent
anticommuting witness.  No path disjointness, owner function, terminal geometry,
or Lemma 14 conclusion is stored in the trace data.
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

/-- Side-correct ordered traces for every initializer.

`commonPath_entry_eq` is the canonical path-orientation fact used in the paper:
for equal pairing types, equal path carriers have the same first introduced
endpoint.  It is not a path-disjointness or ownership assumption. -/
structure InitializationTwoSidedOrderedTraceData
    (I : ObstructionSearchInitialization families Cprime) where
  originalHole : IndexedInducedHole G
  trace : ∀ source : I.Node,
    TwoSidedOrderedOSExecution I source originalHole
  commonPath_entry_eq :
    ∀ ⦃source source' : I.Node⦄
      (i : Fin (trace source).blockCount)
      (j : Fin (trace source').blockCount),
      I.pairing source = I.pairing source' →
      (trace source).path i = (trace source').path j →
        (trace source).entry i = (trace source').entry j

namespace InitializationTwoSidedOrderedTraceData

/-- The least-common-path argument constructs the exact side-correct witness
consumed by Corollary 11. -/
theorem firstCommonWitness
    (X : I.InitializationTwoSidedOrderedTraceData)
    {source source' : I.Node} {P : Set V}
    (hne : source ≠ source')
    (hpair : I.pairing source = I.pairing source')
    (hP : P ∈ (I.output source).paths)
    (hP' : P ∈ (I.output source').paths) :
    ∃ (Q R : Set V)
      (hQ : Q ∈ (I.output source).paths)
      (hR : R ∈ (I.output source').paths),
      Q ≠ R ∧
        SharedDependentAnticommutingWitness
          ((((X.trace source).ordered.history).witness hQ).block.path)
          ((((X.trace source').ordered.history).witness hR).block.path)
          ((((X.trace source).ordered.history).witness hQ).block.dependentAt)
          ((((X.trace source').ordered.history).witness hR).block.dependentAt) := by
  classical
  let A := X.trace source
  let B := X.trace source'
  obtain ⟨iP, hiP⟩ := A.output_path hP
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
  obtain ⟨j, hji⟩ := B.output_path hiOther
  have hiPos : 0 < i.val := by
    by_contra hnot
    have hiZero : i.val = 0 := by omega
    have hsourceMem : (source : V) ∈ A.path i :=
      (A.initializer_mem_path_iff i source).2 ⟨rfl, hiZero⟩
    have hsourceOther : (source : V) ∈ B.path j := by
      rw [hji]
      exact hsourceMem
    have hsourceEq :=
      (B.initializer_mem_path_iff j source).1 hsourceOther
    exact hne hsourceEq.1
  have hjPos : 0 < j.val := by
    by_contra hnot
    have hjZero : j.val = 0 := by omega
    have hsource'Mem : (source' : V) ∈ B.path j :=
      (B.initializer_mem_path_iff j source').2 ⟨rfl, hjZero⟩
    have hsource'Other : (source' : V) ∈ A.path i := by
      rw [← hji]
      exact hsource'Mem
    have hsource'Eq :=
      (A.initializer_mem_path_iff i source').1 hsource'Other
    exact hne hsource'Eq.1.symm
  obtain ⟨q, s, hqi, hsDep, hsAnti⟩ := A.earlierSelection i hiPos
  obtain ⟨r, t, hrj, htDep, htAnti⟩ := B.earlierSelection j hjPos
  let hQ : A.path q ∈ (I.output source).paths := A.path_mem q
  let hR : B.path r ∈ (I.output source').paths := B.path_mem r
  refine ⟨A.path q, B.path r, hQ, hR, ?_, ?_⟩
  · intro hEq
    have hqOther : A.path q ∈ (I.output source').paths := by
      rw [hEq]
      exact hR
    have hqCommon : q ∈ common :=
      Finset.mem_filter.mpr
        ⟨Finset.mem_univ q, hqOther⟩
    have hle : i ≤ q := Finset.min'_le common q hqCommon
    exact (not_lt_of_ge hle) hqi
  · have hentry : A.entry i = B.entry j :=
      X.commonPath_entry_eq i j hpair hji.symm
    refine ⟨A.entry i, s, t, ?_, ?_, ?_, ?_⟩
    · simpa [A, hQ, TwoSidedOrderedPathExecution.blockWitness] using hsDep
    · simpa [B, hR, hentry,
        TwoSidedOrderedPathExecution.blockWitness] using htDep
    · simpa [A, hQ, TwoSidedOrderedPathExecution.blockWitness] using hsAnti
    · simpa [B, hR, hentry,
        TwoSidedOrderedPathExecution.blockWitness] using htAnti

/-- Replace the side-correct first-common-path boundary by the theorem derived
from the finite ordered traces. -/
noncomputable def toInitializationTwoSidedFirstCommonPathData
    (X : I.InitializationTwoSidedOrderedTraceData) :
    I.InitializationTwoSidedFirstCommonPathData where
  originalHole := X.originalHole
  history source := (X.trace source).ordered.history
  firstCommonWitness := by
    intro source source' P hne hpair hP hP'
    exact X.firstCommonWitness hne hpair hP hP'

end InitializationTwoSidedOrderedTraceData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
