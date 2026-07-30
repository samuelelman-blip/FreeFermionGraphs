import FreeFermionGraphs.ObstructionSearchTwoSidedMixedContext

/-!
# Endpoint persistence through mixed-side Definition 19 histories

Corollary 10 makes the first introduced vertex of an earlier path unique to
that path. Since the later carrier paths are distinct, none removes that
vertex. The literal carrier chain therefore transports it to the initial hole
of the current block.

This argument uses the full fixed-pairing path family and is independent of the
`ac` or `bd` presentation of each local block. No obstruction-search execution
is constructed, and no conclusion of Lemma 14 is assumed.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation

/-- The first introduced endpoint of any earlier block in a positive mixed-side
history belongs to the current block's initial hole. -/
theorem earlierFirstIntroduced_mem_currentInitial_of_mixedSideHistory
    (D : ConcretePathDeformation O Cprime)
    (X : D.MixedSideFullDefinition19Lemma11AHistoryData)
    {r : Nat} (hr : r < X.priorCount) :
    ((X.history.carrier.block r).deformation.step
      (X.history.carrier.block r).firstIndex).introduced ∈
      Set.range D.initialHole.vertex := by
  let A := X.history.carrier.block r
  let v : V :=
    (A.deformation.step A.firstIndex).introduced
  let last : Nat := X.priorCount - 1
  have hrLast : r ≤ last := by
    dsimp [last]
    have hpos := X.priorCount_pos
    omega
  have hvFinal : v ∈ Set.range A.finalHole.vertex := by
    exact A.introduced_mem_finalHole
      (X.history.carrier.pathOrder r) A.firstIndex
  have hnotLater : ∀ q : Nat, r < q → q ≤ last →
      v ∉ Set.range (X.history.carrier.block q).path.vertex := by
    intro q hrq hqLast hvq
    have hEq :
        Set.range (X.history.carrier.block q).path.vertex =
          Set.range A.path.vertex :=
      (X.earlierFirstIntroduced_uniquePath r hr).2.2
        (X.prior_path_mem_family q) hvq
    exact (X.priorPath_pairwise r q hr
      (by omega) (by omega)) hEq.symm
  have hvLast :
      v ∈ Set.range (X.history.carrier.block last).finalHole.vertex :=
    X.history.carrier.mem_finalHole_of_mem_finalHole_through
      hrLast (by simpa [A] using hvFinal) (by
        intro q hrq hqLast
        simpa [A, v] using hnotLater q hrq hqLast)
  rw [X.final_before_current] at hvLast
  simpa [A, v] using hvLast

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
