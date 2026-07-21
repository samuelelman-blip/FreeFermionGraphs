import FreeFermionGraphs.ObstructionSearchFirstCommon

/-!
# Ordered obstruction-search traces

The first-common-path certificate used for Lemma 14(iii) is not primitive.
An initialized call to `OS` produces an ordered list of path blocks.  The
first block is the only block containing its initializing vertex, while no
block contains another initializer because the search stops before appending
a path meeting `W \ {source}`.  Every later block starts at a dependent
anticommuting vertex selected from an earlier block by the maximal-step rule.

If two same-pairing searches share a path, choose its least occurrence in
the first trace.  The common path cannot be the first block of either trace.
Its common oriented entry vertex therefore lies in dependent sets of two
earlier blocks and anticommutes with both.  Those earlier blocks are distinct,
since equality would give an earlier common path.  This constructs
the exact witness consumed by Corollary 11.
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

/-- One concrete initialized `OS` trace, in path-block order.

`initializer_mem_path_iff` combines the stopping rule
`P ∩ (W \ {source}) = ∅` with Corollary 10's persistence of the initializing
vertex on the first path only.  `earlierWitness` records the literal update
rule for `u_t`: the first introduced vertex of every later block belongs to a
dependent set of some strictly earlier block and anticommutes with that path.
The algorithm obtains this block from the eligible pair with maximal global
step value `L_{r,s}`; it need not be the immediately preceding block. -/
structure OrderedSearchTrace
    (I : ObstructionSearchInitialization families Cprime)
    (source : I.Node)
    (originalHole : IndexedInducedHole G) where
  history : SearchHistoryData (I.output source) originalHole
  blockCount : Nat
  path : Fin blockCount → Set V
  path_mem : ∀ i : Fin blockCount,
    path i ∈ (I.output source).paths
  output_path : ∀ ⦃P : Set V⦄,
    P ∈ (I.output source).paths →
      ∃ i : Fin blockCount, path i = P
  entry : Fin blockCount → V
  entry_is_firstIntroduced : ∀ i : Fin blockCount,
    entry i =
      (((history.witness (path_mem i)).block.deformation.step
        (history.witness (path_mem i)).block.firstIndex).introduced)
  initializer_mem_path_iff :
    ∀ (i : Fin blockCount) (v : I.Node),
      (v : V) ∈ path i ↔ v = source ∧ i.val = 0
  earlierWitness :
    ∀ (i : Fin blockCount) (hi : 0 < i.val),
      ∃ (q : Fin blockCount) (s : Nat),
        q.val < i.val ∧
          entry i ∈
              ((history.witness (path_mem q)).block.dependentAt s) ∧
            ((history.witness (path_mem q)).block.path).AnticommutesWith
              (entry i)

/-- Ordered traces for every initializer, together with the canonical
orientation of a path component.  For equal pairing types, equal path
carriers have the same first introduced endpoint. -/
structure InitializationOrderedTraceData
    (I : ObstructionSearchInitialization families Cprime) where
  originalHole : IndexedInducedHole G
  trace : ∀ source : I.Node,
    OrderedSearchTrace I source originalHole
  commonPath_entry_eq :
    ∀ ⦃source source' : I.Node⦄
      (i : Fin (trace source).blockCount)
      (j : Fin (trace source').blockCount),
      I.pairing source = I.pairing source' →
      (trace source).path i = (trace source').path j →
        (trace source).entry i = (trace source').entry j

namespace InitializationOrderedTraceData

/-- The least-common-path argument constructs the Corollary 11 witness from
the ordered `OS` traces. -/
theorem firstCommonWitness
    (X : I.InitializationOrderedTraceData)
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
          (((X.trace source).history.witness hQ).block.path)
          (((X.trace source').history.witness hR).block.path)
          (((X.trace source).history.witness hQ).block.dependentAt)
          (((X.trace source').history.witness hR).block.dependentAt) := by
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
  obtain ⟨q, s, hqi, hsDep, hsAnti⟩ := A.earlierWitness i hiPos
  obtain ⟨r, t, hrj, htDep, htAnti⟩ := B.earlierWitness j hjPos
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
  ·
    have hentry : A.entry i = B.entry j :=
      X.commonPath_entry_eq i j hpair hji.symm
    refine ⟨A.entry i, s, t, hsDep, ?_, hsAnti, ?_⟩
    · simpa [hentry] using htDep
    · simpa [hentry] using htAnti

/-- Replace the former primitive first-common-path certificate by the
theorem derived from the ordered trace. -/
noncomputable def toInitializationFirstCommonPathData
    (X : I.InitializationOrderedTraceData) :
    I.InitializationFirstCommonPathData where
  originalHole := X.originalHole
  history source := (X.trace source).history
  firstCommonWitness := by
    intro source source' P hne hpair hP hP'
    exact X.firstCommonWitness hne hpair hP hP'

end InitializationOrderedTraceData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
