import FreeFermionGraphs.Lemma12ReverseClone

/-!
# Lemma 12: the sufficient criterion for a palindromic deformation

The reverse run starts at the prime hole and traverses the original concrete
steps in descending order.  At original step `i`, it removes the forward
introduced vertex and introduces the forward removed vertex.  The latter is
an original-hole vertex by the complete Definition 19 data.

The proof is decreasing induction.  Its invariant is equation (C27): the
symmetric difference of the reverse auxiliary carrier and the corresponding
forward after-carrier is the fixed set `C' ∆ C^(m)`.  Lemma 13 proves the
boundary exclusion needed by every local reverse clone.  Path endpoints use
component maximality; interior steps use the five-neighbour contradiction
proved in `Lemma12ReverseClone`.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

open scoped symmDiff

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace FullDefinition19Deformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- A certificate that the suffix beginning at `n` has been traversed in
reverse from `primeHole`.  The resulting hole is the auxiliary reverse hole
at boundary `n`. -/
inductive ReverseRun
    (F : FullDefinition19Deformation O Cprime)
    (primeHole : IndexedInducedHole G) :
    Nat → IndexedInducedHole G → Prop where
  | terminal : ReverseRun F primeHole F.deformation.stepCount primeHole
  | step {n : Nat} (hn : n < F.deformation.stepCount)
      {R : IndexedInducedHole G}
      (tail : ReverseRun F primeHole (n + 1) R)
      (q : Fin R.card)
      (removedVertex :
        R.vertex q = (F.deformation.step ⟨n, hn⟩).introduced)
      (deformation : R.SingleVertexDeformation
        ((F.deformation.step ⟨n, hn⟩).before.vertex
          (F.deformation.step ⟨n, hn⟩).removedIndex) q)
      (introduced_mem_original :
        (F.deformation.step ⟨n, hn⟩).before.vertex
            (F.deformation.step ⟨n, hn⟩).removedIndex ∈
          Set.range F.initialHole.vertex) :
      ReverseRun F primeHole n (R.deform deformation)

/-- A nonterminal reverse run exposes the next reverse deformation. -/
theorem ReverseRun.exists_head_of_lt
    {F : FullDefinition19Deformation O Cprime}
    {primeHole R : IndexedInducedHole G}
    {n : Nat}
    (run : ReverseRun F primeHole n R)
    (hn : n < F.deformation.stepCount) :
    ∃ Rtail : IndexedInducedHole G,
      ∃ q : Fin Rtail.card,
        Rtail.vertex q = (F.deformation.step ⟨n, hn⟩).introduced ∧
        ∃ hdeform : Rtail.SingleVertexDeformation
            ((F.deformation.step ⟨n, hn⟩).before.vertex
              (F.deformation.step ⟨n, hn⟩).removedIndex) q,
          R = Rtail.deform hdeform ∧
          ReverseRun F primeHole (n + 1) Rtail := by
  cases run with
  | terminal => omega
  | @step m hm Rtail tail q hq hdeform horiginal =>
      refine ⟨Rtail, q, ?_, hdeform, rfl, tail⟩
      simpa using hq

/-- Lemma 12.  If every Definition 20 dependent vertex belongs to the
terminal hole, the complete fixed-pairing deformation admits its reverse run
from `C'` by vertices of the original hole. -/
theorem lemma12
    (F : FullDefinition19Deformation O Cprime)
    (L : Lemma12Definition19Data F)
    (hclaw : G.IsClawFree)
    (hcriterion :
      F.dependentUnion ⊆ Set.range F.terminalHole.vertex) :
    ∃ finalHole : IndexedInducedHole G,
      ReverseRun F L.primeHole 0 finalHole := by
  have build : ∀ (n : Nat) (hn : n ≤ F.deformation.stepCount),
      ∃ R : IndexedInducedHole G,
        ReverseRun F L.primeHole n R ∧
        Even R.card ∧
        (n = 0 ∨
          ∃ i : Fin F.deformation.stepCount,
            i.val + 1 = n ∧
            Set.range R.vertex ∆
                Set.range (F.deformation.step i).after.vertex =
              Cprime ∆ Set.range F.terminalHole.vertex) := by
    intro n hn
    induction hn using Nat.decreasingInduction with
    | self =>
        refine ⟨L.primeHole, ReverseRun.terminal, L.primeHole_even, ?_⟩
        right
        refine ⟨F.lastIndex, ?_, ?_⟩
        · simp [lastIndex]
          have hpos := F.nonempty
          omega
        · rw [L.primeHole_carrier]
          rfl
    | of_succ k hk ih =>
        obtain ⟨Rnext, hrun, hEven, hstage⟩ := ih
        let i : Fin F.deformation.stepCount := ⟨k, hk⟩
        have hsymm :
            Set.range Rnext.vertex ∆
                Set.range (F.deformation.step i).after.vertex =
              Cprime ∆ Set.range F.terminalHole.vertex := by
          rcases hstage with hkZero | ⟨previous, hprevious, hpreviousSymm⟩
          · omega
          · have hEq : previous = i := by
              apply Fin.ext
              change previous.val = k
              omega
            rw [hEq] at hpreviousSymm
            exact hpreviousSymm
        have hreverse : ∃ q : Fin Rnext.card,
            Rnext.vertex q = (F.deformation.step i).introduced ∧
            Rnext.SingleVertexDeformation
              ((F.deformation.step i).before.vertex
                (F.deformation.step i).removedIndex) q := by
          rcases L.endpoint_or_continuation i with hendpoint | hcontinuation
          · exact F.exists_reverse_deformation_of_endpoint
              L hcriterion i Rnext hsymm hendpoint
          · let K : Lemma12Continuation F i :=
              Classical.choice hcontinuation
            have hconsecutive : k + 1 = K.next.val := by
              simpa [i] using K.consecutive
            have hkNext : k + 1 < F.deformation.stepCount := by
              have hnextLt := K.next.isLt
              omega
            obtain ⟨Rtail, qnext, hqnext, hnext, hRnext, tail⟩ :=
              hrun.exists_head_of_lt hkNext
            subst Rnext
            let nextIndex : Fin F.deformation.stepCount :=
              ⟨k + 1, hkNext⟩
            have hnextEq : nextIndex = K.next := by
              apply Fin.ext
              simpa [nextIndex] using hconsecutive
            exact F.exists_reverse_deformation_of_continuation
              hclaw hcriterion i K nextIndex hnextEq Rtail qnext
              (by simpa [nextIndex] using hqnext)
              (by simpa [nextIndex] using hnext)
              (by simpa using hEven)
              (by simpa [nextIndex] using hsymm)
        obtain ⟨q, hq, hdeform⟩ := hreverse
        let Rcurrent : IndexedInducedHole G := Rnext.deform hdeform
        have hrunCurrent : ReverseRun F L.primeHole k Rcurrent := by
          exact ReverseRun.step hk hrun q hq hdeform
            (L.removed_mem_original i)
        have hEvenCurrent : Even Rcurrent.card := by
          simpa [Rcurrent] using hEven
        have hnewBefore :
            Set.range Rcurrent.vertex ∆
                Set.range (F.deformation.step i).before.vertex =
              Cprime ∆ Set.range F.terminalHole.vertex := by
          let S := F.deformation.step i
          let j : V := S.introduced
          let removed : V := S.before.vertex S.removedIndex
          have hforwardReverse :
              S.after.SingleVertexDeformation removed S.removedIndex :=
            S.deformation.reverse
          have hcenter : S.after.vertex S.removedIndex = j := by
            simp [ConcreteDeformationStep.after, j]
          have hbeforeSwap :
              Set.range S.before.vertex =
                Set.insert removed
                  (Set.range S.after.vertex \ {j}) := by
            calc
              Set.range S.before.vertex =
                  Set.range (S.after.deform hforwardReverse).vertex :=
                S.deformation.reverse_deform_range_eq.symm
              _ = Set.insert removed
                    (Set.range S.after.vertex \
                      {S.after.vertex S.removedIndex}) :=
                S.after.deform_range_eq hforwardReverse
              _ = Set.insert removed
                    (Set.range S.after.vertex \ {j}) := by rw [hcenter]
          calc
            Set.range Rcurrent.vertex ∆ Set.range S.before.vertex =
                Set.insert removed (Set.range Rnext.vertex \ {j}) ∆
                  Set.insert removed (Set.range S.after.vertex \ {j}) := by
              rw [Rnext.deform_range_eq hdeform, hq, hbeforeSwap]
            _ = Set.range Rnext.vertex ∆ Set.range S.after.vertex :=
              symmDiff_same_swap
                (by exact ⟨q, hq⟩)
                hdeform.outside
                S.introduced_mem_after
                S.removed_not_mem_after
            _ = Cprime ∆ Set.range F.terminalHole.vertex := by
              simpa [S] using hsymm
        refine ⟨Rcurrent, hrunCurrent, hEvenCurrent, ?_⟩
        by_cases hkZero : k = 0
        · exact Or.inl hkZero
        · right
          let previous : Fin F.deformation.stepCount :=
            ⟨k - 1, by omega⟩
          refine ⟨previous, by simp [previous]; omega, ?_⟩
          have hchain :
              Set.range (F.deformation.step previous).after.vertex =
                Set.range (F.deformation.step i).before.vertex :=
            F.deformation.carrier_chain (i := previous) (j := i) (by
              simp [previous, i]
              omega)
          rw [hchain]
          exact hnewBefore
  obtain ⟨R, hrun, _hEven, _hstage⟩ := build 0 (Nat.zero_le _)
  exact ⟨R, hrun⟩

end FullDefinition19Deformation

end FixedPairingPathFamily

end SimpleGraph
