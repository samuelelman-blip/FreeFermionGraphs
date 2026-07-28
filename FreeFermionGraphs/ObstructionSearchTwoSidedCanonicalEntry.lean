import FreeFermionGraphs.ObstructionSearchTwoSidedOrderedTrace

/-!
# Canonical entries of two-sided Definition 19 paths

Definition 19 orients every path component as
`j₀-k₀-⋯-j_(ℓ-1)-k_(ℓ-1)`: the first endpoint is introduced from the fixed
prime hole, while the final endpoint is an original-hole vertex and is not in
the prime carrier.  Consequently the carrier of a represented path determines
its first introduced endpoint.

This module proves that fact from the concrete Definition 19 data and removes
the last cross-trace premise from the two-sided least-common-path construction.
No path disjointness, ownership, terminal obstruction geometry, or Lemma 14
conclusion is assumed.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace IndexedInducedPath

/-- Under equality of path carriers, a vertex occupying index zero in one
indexed induced path occupies either index zero or the final index in the other
path.

The proof is intrinsic to the induced path.  An interior occurrence would have
two distinct path neighbours, whereas index zero in the first path has at most
one. -/
theorem firstVertex_eq_first_or_last_of_range_eq
    (P Q : IndexedInducedPath G)
    (p : Fin P.card) (q₀ : Fin Q.card)
    (hp₀ : p.val = 0) (hq₀ : q₀.val = 0)
    (hRange : Set.range P.vertex = Set.range Q.vertex) :
    P.vertex p = Q.vertex q₀ ∨
      ∃ q : Fin Q.card,
        q.val + 1 = Q.card ∧ P.vertex p = Q.vertex q := by
  have hpMemQ : P.vertex p ∈ Set.range Q.vertex := by
    rw [← hRange]
    exact ⟨p, rfl⟩
  obtain ⟨q, hq⟩ := hpMemQ
  by_cases hqFirst : q.val = 0
  · left
    have hqq₀ : q = q₀ := Fin.ext (by omega)
    calc
      P.vertex p = Q.vertex q := hq.symm
      _ = Q.vertex q₀ := by rw [hqq₀]
  by_cases hqLast : q.val + 1 = Q.card
  · exact Or.inr ⟨q, hqLast, hq.symm⟩
  · exfalso
    have hqPos : 0 < q.val := by omega
    have hqNext : q.val + 1 < Q.card := by omega
    let qPrev : Fin Q.card := ⟨q.val - 1, by omega⟩
    let qNext : Fin Q.card := ⟨q.val + 1, hqNext⟩
    have hqPrev : G.Adj (Q.vertex q) (Q.vertex qPrev) :=
      (Q.adj_iff q qPrev).2 (Or.inr (by
        dsimp [qPrev]
        omega))
    have hqNextAdj : G.Adj (Q.vertex q) (Q.vertex qNext) :=
      (Q.adj_iff q qNext).2 (Or.inl rfl)
    have hPrevMemP : Q.vertex qPrev ∈ Set.range P.vertex := by
      rw [hRange]
      exact ⟨qPrev, rfl⟩
    have hNextMemP : Q.vertex qNext ∈ Set.range P.vertex := by
      rw [hRange]
      exact ⟨qNext, rfl⟩
    obtain ⟨iPrev, hiPrev⟩ := hPrevMemP
    obtain ⟨iNext, hiNext⟩ := hNextMemP
    have hpPrev : G.Adj (P.vertex p) (P.vertex iPrev) := by
      rw [← hq, hiPrev]
      exact hqPrev
    have hpNext : G.Adj (P.vertex p) (P.vertex iNext) := by
      rw [← hq, hiNext]
      exact hqNextAdj
    have hiPrevVal : iPrev.val = 1 := by
      rcases (P.adj_iff p iPrev).1 hpPrev with h | h <;> omega
    have hiNextVal : iNext.val = 1 := by
      rcases (P.adj_iff p iNext).1 hpNext with h | h <;> omega
    have hi : iPrev = iNext := Fin.ext (by omega)
    have hvertices : Q.vertex qPrev = Q.vertex qNext := by
      calc
        Q.vertex qPrev = P.vertex iPrev := hiPrev.symm
        _ = P.vertex iNext := by rw [hi]
        _ = Q.vertex qNext := hiNext
    have hindices : qPrev = qNext := Q.injective hvertices
    have hvals := congrArg Fin.val hindices
    dsimp [qPrev, qNext] at hvals
    omega

end IndexedInducedPath

namespace FixedPairingPathFamily

variable {O O' : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation

namespace Lemma11AHistoryContext

/-- Equal Definition 19 path carriers have the same first introduced vertex.

The carrier equality first identifies the first endpoint of `D` with either the
first or final endpoint of `E`.  The final alternative is impossible because
the former is introduced from `Cprime`, while the latter is the terminal removed
vertex and is explicitly outside `Cprime`. -/
theorem firstIntroduced_eq_of_path_range_eq
    {D : ConcretePathDeformation O Cprime}
    {E : ConcretePathDeformation O' Cprime}
    (A : D.Lemma11AHistoryContext)
    (B : E.Lemma11AHistoryContext)
    (hRange : Set.range D.path.vertex = Set.range E.path.vertex) :
    (D.deformation.step D.firstIndex).introduced =
      (E.deformation.step E.firstIndex).introduced := by
  let p : Fin D.path.card :=
    A.currentData.neighborhood.pathOrder.introducedPathIndex D.firstIndex
  let q₀ : Fin E.path.card :=
    B.currentData.neighborhood.pathOrder.introducedPathIndex E.firstIndex
  have hp₀ : p.val = 0 := by
    dsimp [p]
    rw [A.currentData.neighborhood.pathOrder.introduced_index_val]
    rfl
  have hq₀ : q₀.val = 0 := by
    dsimp [q₀]
    rw [B.currentData.neighborhood.pathOrder.introduced_index_val]
    rfl
  have hpVertex :
      D.path.vertex p =
        (D.deformation.step D.firstIndex).introduced := by
    exact A.currentData.neighborhood.pathOrder.introduced_eq D.firstIndex
  have hqVertex :
      E.path.vertex q₀ =
        (E.deformation.step E.firstIndex).introduced := by
    exact B.currentData.neighborhood.pathOrder.introduced_eq E.firstIndex
  rcases D.path.firstVertex_eq_first_or_last_of_range_eq
      E.path p q₀ hp₀ hq₀ hRange with hfirst | hlast
  · calc
      (D.deformation.step D.firstIndex).introduced = D.path.vertex p :=
        hpVertex.symm
      _ = E.path.vertex q₀ := hfirst
      _ = (E.deformation.step E.firstIndex).introduced := hqVertex
  · obtain ⟨q, hqLast, hpLast⟩ := hlast
    have hlastVertex :=
      B.currentData.lastPathVertex_eq_terminalRemoved q hqLast
    have hpPrime :
        (D.deformation.step D.firstIndex).introduced ∈ Cprime :=
      A.currentData.neighborhood.primeHole.introduced_mem D.firstIndex
    exfalso
    apply B.currentData.terminalRemoved_not_mem_prime
    rw [← hlastVertex, ← hpLast, hpVertex]
    exact hpPrime

end Lemma11AHistoryContext

end ConcretePathDeformation

variable {O O' : FixedPairingPathFamily G}

namespace TwoSidedSearchPathHistoryWitness

/-- The first introduced endpoint is independent of which two-sided history
witness presents a fixed Definition 19 path carrier. -/
theorem firstIntroduced_eq_of_path_eq
    {S : SearchDeformation O Cprime}
    {T : SearchDeformation O' Cprime}
    {originalHole : IndexedInducedHole G}
    {P Q : Set V}
    (A : TwoSidedSearchPathHistoryWitness S originalHole P)
    (B : TwoSidedSearchPathHistoryWitness T originalHole Q)
    (hPQ : P = Q) :
    (A.block.deformation.step A.block.firstIndex).introduced =
      (B.block.deformation.step B.block.firstIndex).introduced := by
  apply A.context.firstIntroduced_eq_of_path_range_eq B.context
  calc
    Set.range A.block.path.vertex = P := A.path_eq
    _ = Q := hPQ
    _ = Set.range B.block.path.vertex := B.path_eq.symm

end TwoSidedSearchPathHistoryWitness

variable {families : PairingType → FixedPairingPathFamily G}

namespace ObstructionSearchInitialization

variable {I : ObstructionSearchInitialization families Cprime}

/-- Two-sided ordered executions for all initializers, with no cross-trace
premise.  Canonical common-path entries are now derived from Definition 19. -/
structure InitializationTwoSidedOrderedExecutionData
    (I : ObstructionSearchInitialization families Cprime) where
  originalHole : IndexedInducedHole G
  trace : ∀ source : I.Node,
    TwoSidedOrderedOSExecution I source originalHole

namespace InitializationTwoSidedOrderedExecutionData

/-- Construct the ordered-trace interface by deriving its common-path entry
field from the concrete prime-to-original orientation of Definition 19. -/
def toInitializationTwoSidedOrderedTraceData
    (X : I.InitializationTwoSidedOrderedExecutionData) :
    I.InitializationTwoSidedOrderedTraceData where
  originalHole := X.originalHole
  trace := X.trace
  commonPath_entry_eq := by
    intro source source' i j _hpair hpath
    let A := (X.trace source).ordered.blockWitness i
    let B := (X.trace source').ordered.blockWitness j
    change (X.trace source).ordered.path i =
      (X.trace source').ordered.path j at hpath
    calc
      (X.trace source).entry i =
          (A.block.deformation.step A.block.firstIndex).introduced := by
        simpa [A] using (X.trace source).entry_is_firstIntroduced i
      _ = (B.block.deformation.step B.block.firstIndex).introduced := by
        apply A.context.firstIntroduced_eq_of_path_range_eq B.context
        calc
          Set.range A.block.path.vertex =
              (X.trace source).ordered.path i := A.path_eq
          _ = (X.trace source').ordered.path j := hpath
          _ = Set.range B.block.path.vertex := B.path_eq.symm
      _ = (X.trace source').entry j := by
        simpa [B] using
          ((X.trace source').entry_is_firstIntroduced j).symm

/-- Hence the side-correct first-common-path data, same-pairing path
disjointness, and canonical ownership all follow without a cross-trace
certificate. -/
noncomputable def toInitializationTwoSidedFirstCommonPathData
    (X : I.InitializationTwoSidedOrderedExecutionData) :
    I.InitializationTwoSidedFirstCommonPathData :=
  X.toInitializationTwoSidedOrderedTraceData
    |>.toInitializationTwoSidedFirstCommonPathData

end InitializationTwoSidedOrderedExecutionData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
