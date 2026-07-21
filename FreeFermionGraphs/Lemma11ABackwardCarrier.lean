import FreeFermionGraphs.Lemma11AHistory

/-!
# Lemma 11(a): backward carrier transport

The proof of Lemma 11(a) repeatedly observes that an original-hole vertex
which is not one of the introduced vertices can be followed backwards
through the Definition 19 deformation.  The existing carrier lemmas run in
the forward direction; this file supplies the converse transport needed to
identify the paper's original hole `C`.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace FixedPairingPathFamily

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

namespace ConcreteDeformationStep

/-- A vertex on the after-hole which is not the introduced vertex was
already on the before-hole. -/
theorem mem_before_of_mem_after_of_ne_introduced
    (S : ConcreteDeformationStep O Cprime)
    {x : V}
    (hxAfter : x ∈ Set.range S.after.vertex)
    (hxIntroduced : x ≠ S.introduced) :
    x ∈ Set.range S.before.vertex := by
  obtain ⟨q, hqx⟩ := hxAfter
  by_cases hqi : q = S.removedIndex
  · subst q
    have hEq : S.introduced = x := by
      simpa [ConcreteDeformationStep.after] using hqx
    exact (hxIntroduced hEq.symm).elim
  · refine ⟨q, ?_⟩
    calc
      S.before.vertex q = S.after.vertex q := by
        simpa [ConcreteDeformationStep.after] using
          (S.before.deform_vertex_away S.deformation hqi).symm
      _ = x := hqx

end ConcreteDeformationStep

namespace ConcretePathDeformation

/-- Backward transport from the before-hole of step `n` to the initial
hole, provided the vertex is not introduced at an earlier step. -/
theorem mem_initialHole_of_mem_before_at
    (D : ConcretePathDeformation O Cprime)
    {x : V} :
    ∀ (n : Nat) (hn : n < D.deformation.stepCount),
      (∀ j : Fin D.deformation.stepCount, j.val < n →
        x ≠ (D.deformation.step j).introduced) →
      x ∈ Set.range (D.deformation.step ⟨n, hn⟩).before.vertex →
      x ∈ Set.range D.initialHole.vertex := by
  intro n
  induction n with
  | zero =>
      intro hn _hne hx
      simpa [ConcretePathDeformation.initialHole,
        ConcretePathDeformation.firstIndex] using hx
  | succ n ih =>
      intro hn hne hx
      have hnPrevious : n < D.deformation.stepCount := by omega
      let previous : Fin D.deformation.stepCount := ⟨n, hnPrevious⟩
      let current : Fin D.deformation.stepCount := ⟨n + 1, hn⟩
      have hchain :
          Set.range (D.deformation.step previous).after.vertex =
            Set.range (D.deformation.step current).before.vertex :=
        D.deformation.carrier_chain (i := previous) (j := current) (by
          simp [previous, current])
      have hxPreviousAfter :
          x ∈ Set.range (D.deformation.step previous).after.vertex := by
        rw [hchain]
        simpa [current] using hx
      have hxPreviousIntroduced :
          x ≠ (D.deformation.step previous).introduced :=
        hne previous (by simp [previous])
      have hxPreviousBefore :
          x ∈ Set.range (D.deformation.step previous).before.vertex :=
        (D.deformation.step previous).mem_before_of_mem_after_of_ne_introduced
          hxPreviousAfter hxPreviousIntroduced
      exact ih hnPrevious
        (fun j hj => hne j (by omega))
        (by simpa [previous] using hxPreviousBefore)

/-- A final-hole vertex which is never introduced by the path block was
already present on its initial hole. -/
theorem mem_initialHole_of_mem_finalHole_of_ne_introduced
    (D : ConcretePathDeformation O Cprime)
    {x : V}
    (hxFinal : x ∈ Set.range D.finalHole.vertex)
    (hne : ∀ j : Fin D.deformation.stepCount,
      x ≠ (D.deformation.step j).introduced) :
    x ∈ Set.range D.initialHole.vertex := by
  have hlast : D.deformation.stepCount - 1 < D.deformation.stepCount := by
    have hpos := D.nonempty
    omega
  let last : Fin D.deformation.stepCount :=
    ⟨D.deformation.stepCount - 1, hlast⟩
  have hxLastAfter :
      x ∈ Set.range (D.deformation.step last).after.vertex := by
    simpa [ConcretePathDeformation.finalHole,
      ConcretePathDeformation.lastIndex, last] using hxFinal
  have hxLastBefore :
      x ∈ Set.range (D.deformation.step last).before.vertex :=
    (D.deformation.step last).mem_before_of_mem_after_of_ne_introduced
      hxLastAfter (hne last)
  exact D.mem_initialHole_of_mem_before_at last.val last.isLt
    (fun j _hj => hne j) hxLastBefore

end ConcretePathDeformation

namespace ConcretePathDeformation.PathBlockHistory

/-- Backward transport through the first `n+1` path blocks. -/
theorem mem_firstInitial_of_mem_final_through
    (H : PathBlockHistory (O := O) (Cprime := Cprime))
    {x : V} (n : Nat)
    (hxFinal : x ∈ Set.range (H.block n).finalHole.vertex)
    (hne : ∀ r : Nat, r ≤ n →
      ∀ j : Fin (H.block r).deformation.stepCount,
        x ≠ ((H.block r).deformation.step j).introduced) :
    x ∈ Set.range (H.block 0).initialHole.vertex := by
  induction n with
  | zero =>
      exact (H.block 0).mem_initialHole_of_mem_finalHole_of_ne_introduced
        hxFinal (hne 0 (by omega))
  | succ n ih =>
      have hxCurrentInitial :
          x ∈ Set.range (H.block (n + 1)).initialHole.vertex :=
        (H.block (n + 1)).mem_initialHole_of_mem_finalHole_of_ne_introduced
          hxFinal (hne (n + 1) (by omega))
      have hxPreviousFinal :
          x ∈ Set.range (H.block n).finalHole.vertex := by
        rw [H.chain n]
        exact hxCurrentInitial
      exact ih hxPreviousFinal
        (fun r hr => hne r (by omega))

end ConcretePathDeformation.PathBlockHistory

end FixedPairingPathFamily

end SimpleGraph
