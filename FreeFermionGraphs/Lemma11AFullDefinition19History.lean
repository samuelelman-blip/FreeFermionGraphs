import FreeFermionGraphs.Lemma11AEndpointPersistence

/-!
# Lemma 11(a.ii): full Definition 19 history

Lemma 11(a.ii) compares the current path block with the original hole.  The
local block data alone cannot represent that comparison, so this module
records the finite prefix of earlier Definition 19 blocks and the
Corollary-10 persistence of earlier path endpoints.  Corollary 11 is proved
from this geometry in a later module rather than stored as a field.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- Every concrete path block is one of the path components recorded by its
fixed-pairing family. -/
theorem path_range_mem
    (D : ConcretePathDeformation O Cprime) :
    Set.range D.path.vertex ∈ O.paths := by
  rw [← D.activePath_eq D.firstIndex]
  exact D.deformation.activePath_mem D.firstIndex

/-- The cross-path Definition 19 data used in Lemma 11(a.ii).  It records
the finite carrier-linked block history, distinct path components, and the
paper's Corollary 10 uniqueness of earlier path endpoints.  Corollary 11 is
proved from this geometry rather than stored as a field. -/
structure FullDefinition19Lemma11AHistoryData
    (D : ConcretePathDeformation O Cprime) where
  current : D.FullDefinition19Lemma11AData
  history : PathBlockHistory (O := O) (Cprime := Cprime)
  priorCount : Nat
  priorCount_pos : 0 < priorCount
  prior : ∀ r : Nat, (history.block r).FullDefinition19Lemma11AData
  final_before_current :
    Set.range (history.block (priorCount - 1)).finalHole.vertex =
      Set.range D.initialHole.vertex
  priorPath_ne_current : ∀ r : Nat, r < priorCount →
    Set.range (history.block r).path.vertex ≠ Set.range D.path.vertex
  priorPath_pairwise : ∀ r q : Nat,
    r < priorCount → q < priorCount → r ≠ q →
      Set.range (history.block r).path.vertex ≠
        Set.range (history.block q).path.vertex
  earlierFirstIntroduced_uniquePath : ∀ r : Nat, r < priorCount →
    O.IsUniqueContainingPath
      ((history.block r).deformation.step
        (history.block r).firstIndex).introduced
      (Set.range (history.block r).path.vertex)

/-- Corollary 10 makes the first introduced vertex of an earlier path unique
to that path.  Since all later paths in the finite Definition 19 history are
distinct, it is never removed by them; carrier transport then puts it on the
initial hole of the current block. -/
theorem earlierFirstIntroduced_mem_currentInitial
    (D : ConcretePathDeformation O Cprime)
    (X : D.FullDefinition19Lemma11AHistoryData)
    {r : Nat} (hr : r < X.priorCount) :
    ((X.history.block r).deformation.step
      (X.history.block r).firstIndex).introduced ∈
      Set.range D.initialHole.vertex := by
  let A := X.history.block r
  let v : V := (A.deformation.step A.firstIndex).introduced
  let last : Nat := X.priorCount - 1
  have hlastLt : last < X.priorCount := by
    dsimp [last]
    have hpos := X.priorCount_pos
    omega
  have hrLast : r ≤ last := by
    dsimp [last]
    have hpos := X.priorCount_pos
    omega
  have hvPath : v ∈ Set.range A.path.vertex := by
    rw [← A.activePath_eq A.firstIndex]
    exact (A.deformation.step A.firstIndex).introduced_mem_activePath
  have hvFinal : v ∈ Set.range A.finalHole.vertex := by
    exact A.introduced_mem_finalHole
      (X.prior r).neighborhood.pathOrder A.firstIndex
  have hnotLater : ∀ q : Nat, r < q → q ≤ last →
      v ∉ Set.range (X.history.block q).path.vertex := by
    intro q hrq hqLast hvq
    have hEq :
        Set.range (X.history.block q).path.vertex =
          Set.range A.path.vertex :=
      (X.earlierFirstIntroduced_uniquePath r hr).2.2
        ((X.history.block q).path_range_mem) hvq
    exact (X.priorPath_pairwise r q hr
      (by omega) (by omega)) hEq.symm
  have hvLast : v ∈ Set.range (X.history.block last).finalHole.vertex :=
    X.history.mem_finalHole_of_mem_finalHole_through
      hrLast (by simpa [A] using hvFinal) (by
        intro q hrq hqLast
        simpa [A, v] using hnotLater q hrq hqLast)
  rw [X.final_before_current] at hvLast
  simpa [A, v] using hvLast

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
