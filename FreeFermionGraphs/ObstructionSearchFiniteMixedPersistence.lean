import FreeFermionGraphs.ObstructionSearchFiniteMixedParity

/-!
# Endpoint persistence on bounded mixed-side histories

Corollary 10 makes the first introduced endpoint of an earlier path unique to
that path.  Since all later blocks in the finite Definition 19 prefix have
distinct paths, none of them removes the endpoint.  The carrier chain
therefore transports it into the initial hole of the current block.

This module proves that argument directly on `Fin priorCount`.  It does not
construct an infinite history and does not assume a conclusion of Lemma 11 or
Lemma 14.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation

private theorem firstIntroduced_mem_finalHole_of_reorient
    (A : ConcretePathDeformation O Cprime)
    (side : DeformationSide)
    (F : (A.reorient side).FullDefinition19Lemma11AData) :
    (A.deformation.step A.firstIndex).introduced ∈
      Set.range A.finalHole.vertex := by
  have h :=
    (A.reorient side).introduced_mem_finalHole
      F.neighborhood.pathOrder (A.reorient side).firstIndex
  cases side <;> exact h

namespace FiniteMixedSideLemma11AHistoryData

variable {D : ConcretePathDeformation O Cprime}
  {originalHole : IndexedInducedHole G}

/-- Every prior path belongs to the full fixed-pairing family, independently
of its local `ac` or `bd` presentation. -/
theorem prior_path_mem_family
    (H : FiniteMixedSideLemma11AHistoryData D originalHole)
    (r : Fin H.priorCount) :
    Set.range (H.priorBlock r).path.vertex ∈ O.paths := by
  have hactive :
      Set.range
          (((H.priorBlock r).reorient (H.priorSide r)).path.vertex) ∈
        ((H.priorSide r).family O).acPaths := by
    rw [← ((H.priorBlock r).reorient (H.priorSide r)).activePath_eq
      ((H.priorBlock r).reorient (H.priorSide r)).firstIndex]
    exact
      ((H.priorData r).neighborhood.mechanical.stepGeometry
        ((H.priorBlock r).reorient
          (H.priorSide r)).firstIndex).base.activePath_ac
  change Set.range (H.priorBlock r).path.vertex ∈
    O.acPaths ∪ O.bdPaths
  cases hside : H.priorSide r with
  | ac =>
      left
      simpa [hside, DeformationSide.family] using hactive
  | bd =>
      right
      simpa [hside, DeformationSide.family, swapSides] using hactive

/-- A vertex at the final hole of block `r` persists to the final hole of
block `n` whenever it lies on none of the intervening finite-prefix paths. -/
theorem mem_finalHole_of_mem_finalHole_through
    (H : FiniteMixedSideLemma11AHistoryData D originalHole)
    {x : V} {r n : Nat}
    (hr : r < H.priorCount)
    (hn : n < H.priorCount)
    (hrn : r ≤ n)
    (hx : x ∈ Set.range
      (H.priorBlock ⟨r, hr⟩).finalHole.vertex)
    (hxPath : ∀ (q : Nat) (hq : q < H.priorCount),
      r < q → q ≤ n →
        x ∉ Set.range (H.priorBlock ⟨q, hq⟩).path.vertex) :
    x ∈ Set.range (H.priorBlock ⟨n, hn⟩).finalHole.vertex := by
  revert hn hxPath
  induction n, hrn using Nat.le_induction with
  | base =>
      intro hn _
      simpa using hx
  | succ n hrn ih =>
      intro hn hxPath
      have hnPrevious : n < H.priorCount := by omega
      let previous : Fin H.priorCount := ⟨n, hnPrevious⟩
      let current : Fin H.priorCount := ⟨n + 1, hn⟩
      have hprevious :
          x ∈ Set.range (H.priorBlock previous).finalHole.vertex := by
        apply ih hnPrevious
        intro q hq hrq hqn
        exact hxPath q hq hrq (by omega)
      have hchain :
          Set.range (H.priorBlock previous).finalHole.vertex =
            Set.range (H.priorBlock current).initialHole.vertex :=
        H.priorChain (r := previous) (q := current) (by
          simp [previous, current])
      have hbefore :
          x ∈ Set.range (H.priorBlock current).initialHole.vertex := by
        rw [← hchain]
        exact hprevious
      have hnotCurrent :
          x ∉ Set.range (H.priorBlock current).path.vertex := by
        simpa [current] using
          hxPath (n + 1) hn (by omega) (by omega)
      exact (H.priorBlock current).mem_finalHole_of_mem_initialHole_of_not_mem_path
        hbefore hnotCurrent

/-- The first introduced endpoint of every earlier block belongs to the
current block's initial hole.  This is the bounded Corollary 10 persistence
statement required by Lemma 11(a.ii). -/
theorem earlierFirstIntroduced_mem_currentInitial
    (H : FiniteMixedSideLemma11AHistoryData D originalHole)
    (r : Fin H.priorCount) :
    ((H.priorBlock r).deformation.step
      (H.priorBlock r).firstIndex).introduced ∈
      Set.range D.initialHole.vertex := by
  let A := H.priorBlock r
  let v : V :=
    (A.deformation.step A.firstIndex).introduced
  have hrLast : r.val ≤ H.lastIndex.val := by
    change r.val ≤ H.priorCount - 1
    omega
  have hvFinal : v ∈ Set.range A.finalHole.vertex := by
    exact firstIntroduced_mem_finalHole_of_reorient
      A (H.priorSide r) (H.priorData r)
  have hnotLater : ∀ q : Fin H.priorCount,
      r.val < q.val → q.val ≤ H.lastIndex.val →
        v ∉ Set.range (H.priorBlock q).path.vertex := by
    intro q hrq _ hvq
    have hpathEq :
        Set.range (H.priorBlock q).path.vertex =
          Set.range A.path.vertex :=
      (H.earlierFirstIntroduced_uniquePath r).2.2
        (H.prior_path_mem_family q) (by simpa [v, A] using hvq)
    have hrqNe : r ≠ q := by
      intro hEq
      have hval := congrArg Fin.val hEq
      omega
    exact (H.priorPath_pairwise (r := r) (q := q) hrqNe)
      hpathEq.symm
  have hvLast :
      v ∈ Set.range (H.priorBlock H.lastIndex).finalHole.vertex := by
    have h := H.mem_finalHole_of_mem_finalHole_through
      (r := r.val) (n := H.lastIndex.val)
      r.isLt H.lastIndex.isLt hrLast (by simpa [A, v] using hvFinal)
      (by
        intro q hq hrq hqLast
        let qFin : Fin H.priorCount := ⟨q, hq⟩
        simpa [qFin] using hnotLater qFin hrq hqLast)
    simpa using h
  rw [H.lastFinal_eq_current'] at hvLast
  simpa [A, v] using hvLast

end FiniteMixedSideLemma11AHistoryData

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
