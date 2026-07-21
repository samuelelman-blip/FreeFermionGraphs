import FreeFermionGraphs.Lemma11AHistory
import FreeFermionGraphs.Corollary7

/-!
# Lemma 11(a.ii): endpoint persistence through path blocks

An endpoint of an earlier Definition 19 path persists through every later
path block that does not contain it.  This is the carrier-level form of the
Corollary 10 argument used after Corollary 12.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- A vertex on the initial hole which is not on the active path is never
removed by the block, and therefore remains on its final hole. -/
theorem mem_finalHole_of_mem_initialHole_of_not_mem_path
    (D : ConcretePathDeformation O Cprime)
    {x : V}
    (hx : x ∈ Set.range D.initialHole.vertex)
    (hxPath : x ∉ Set.range D.path.vertex) :
    x ∈ Set.range D.finalHole.vertex := by
  have hafter : ∀ (n : Nat) (hn : n < D.deformation.stepCount),
      x ∈ Set.range (D.deformation.step ⟨n, hn⟩).after.vertex := by
    intro n
    induction n with
    | zero =>
        intro hn
        let current : Fin D.deformation.stepCount := ⟨0, hn⟩
        have hbefore :
            x ∈ Set.range (D.deformation.step current).before.vertex := by
          simpa [current, initialHole, firstIndex] using hx
        have hremovedActive :
            (D.deformation.step current).before.vertex
                (D.deformation.step current).removedIndex ∈
              Set.range (D.deformation.step current).activePath.vertex :=
          (D.deformation.step current).removed_mem_activePath
        have hremovedPath :
            (D.deformation.step current).before.vertex
                (D.deformation.step current).removedIndex ∈
              Set.range D.path.vertex := by
          rw [← D.activePath_eq current]
          exact hremovedActive
        have hneRemoved : x ≠
            (D.deformation.step current).before.vertex
              (D.deformation.step current).removedIndex := by
          intro hEq
          apply hxPath
          simpa [hEq] using hremovedPath
        simpa [current] using
          (D.deformation.step current).mem_after_of_mem_before_of_ne_removed
            hbefore hneRemoved
    | succ n ih =>
        intro hn
        have hnPrevious : n < D.deformation.stepCount := by omega
        let previous : Fin D.deformation.stepCount := ⟨n, hnPrevious⟩
        let current : Fin D.deformation.stepCount := ⟨n + 1, hn⟩
        have hprevious :
            x ∈ Set.range (D.deformation.step previous).after.vertex := by
          simpa [previous] using ih hnPrevious
        have hchain :
            Set.range (D.deformation.step previous).after.vertex =
              Set.range (D.deformation.step current).before.vertex :=
          D.deformation.carrier_chain (i := previous) (j := current) (by
            simp [previous, current])
        have hbefore :
            x ∈ Set.range (D.deformation.step current).before.vertex := by
          rw [← hchain]
          exact hprevious
        have hremovedActive :
            (D.deformation.step current).before.vertex
                (D.deformation.step current).removedIndex ∈
              Set.range (D.deformation.step current).activePath.vertex :=
          (D.deformation.step current).removed_mem_activePath
        have hremovedPath :
            (D.deformation.step current).before.vertex
                (D.deformation.step current).removedIndex ∈
              Set.range D.path.vertex := by
          rw [← D.activePath_eq current]
          exact hremovedActive
        have hneRemoved : x ≠
            (D.deformation.step current).before.vertex
              (D.deformation.step current).removedIndex := by
          intro hEq
          apply hxPath
          simpa [hEq] using hremovedPath
        simpa [current] using
          (D.deformation.step current).mem_after_of_mem_before_of_ne_removed
            hbefore hneRemoved
  have hlast : D.deformation.stepCount - 1 < D.deformation.stepCount := by
    have hpos := D.nonempty
    omega
  have hfinal := hafter (D.deformation.stepCount - 1) hlast
  simpa [finalHole, lastIndex] using hfinal

end ConcretePathDeformation

namespace ConcretePathDeformation.PathBlockHistory

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- A vertex at the final hole of block `r` persists to the final hole of
block `n` whenever it lies on none of the intervening active paths. -/
theorem mem_finalHole_of_mem_finalHole_through
    (H : PathBlockHistory (O := O) (Cprime := Cprime))
    {x : V} {r n : Nat}
    (hrn : r ≤ n)
    (hx : x ∈ Set.range (H.block r).finalHole.vertex)
    (hxPath : ∀ q : Nat, r < q → q ≤ n →
      x ∉ Set.range (H.block q).path.vertex) :
    x ∈ Set.range (H.block n).finalHole.vertex := by
  revert hxPath
  induction n, hrn using Nat.le_induction with
  | base =>
      intro _
      exact hx
  | succ n hrn ih =>
      intro hxPath
      have hprevious :
          x ∈ Set.range (H.block n).finalHole.vertex :=
        ih (fun q hrq hqn => hxPath q hrq (by omega))
      have hbefore :
          x ∈ Set.range (H.block (n + 1)).initialHole.vertex := by
        rw [← H.chain n]
        exact hprevious
      exact (H.block (n + 1)).mem_finalHole_of_mem_initialHole_of_not_mem_path
        hbefore (hxPath (n + 1) (by omega) (by omega))

end ConcretePathDeformation.PathBlockHistory

end FixedPairingPathFamily

end SimpleGraph
