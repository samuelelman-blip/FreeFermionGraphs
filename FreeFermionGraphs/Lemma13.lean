import FreeFermionGraphs.Lemma11Complete

/-!
# Lemma 13: the terminal symmetric difference misses the deformation boundary

This module introduces the finite, flattened form of a complete Definition 19
deformation.  Flattening only forgets the division into path blocks: it retains
every concrete single-vertex deformation in order, the unchanged prime hole
`C'`, and the local successor fact supplied by the alternating order on each
Definition 19 path.

The successor fact is the only path-specific ingredient needed here.  If a
removed vertex also belongs to `C'`, it cannot be the terminal vertex of its
path.  The following introduced path vertex is adjacent to it, whereas the
following removed vertex is not.  Thus the removed vertex belongs to the next
Definition 20 dependent subset.

The proof of Lemma 13 is then a carrier argument.  A removed non-prime vertex
can return to the terminal hole only by being introduced later, which would put
it in `C'`.  Conversely, an introduced prime vertex can disappear only by being
removed later, and every removed prime vertex lies in the dependent union.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

open scoped symmDiff

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

/-- A complete finite Definition 19 deformation, with its path blocks
flattened into one ordered sequence of single-vertex replacements.

`removedPrime_hasSuccessor` is the direct local consequence of the alternating
path order used in the paper: a removed vertex which is also in the prime hole
is followed in the same path by an introduced vertex, and it satisfies the
four defining conditions of the next dependent subset. -/
structure FullDefinition19Deformation
    (O : FixedPairingPathFamily G) (Cprime : Set V) where
  deformation : ConcreteDeformation O Cprime
  nonempty : 0 < deformation.stepCount
  introduced_mem_prime :
    ∀ i : Fin deformation.stepCount,
      (deformation.step i).introduced ∈ Cprime
  removedPrime_hasSuccessor :
    ∀ (i : Fin deformation.stepCount),
      (deformation.step i).before.vertex
          (deformation.step i).removedIndex ∈ Cprime →
        ∃ j : Fin deformation.stepCount,
          i.val + 1 = j.val ∧
          G.Adj
            ((deformation.step i).before.vertex
              (deformation.step i).removedIndex)
            (deformation.step j).introduced ∧
          (deformation.step i).before.vertex
              (deformation.step i).removedIndex ≠
            (deformation.step j).before.vertex
              (deformation.step j).removedIndex ∧
          ¬G.Adj
            ((deformation.step i).before.vertex
              (deformation.step i).removedIndex)
            ((deformation.step j).before.vertex
              (deformation.step j).removedIndex)

namespace FullDefinition19Deformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- The first hole in the complete deformation. -/
def initialHole (F : FullDefinition19Deformation O Cprime) :
    IndexedInducedHole G :=
  (F.deformation.step ⟨0, F.nonempty⟩).before

/-- Index of the last concrete replacement. -/
def lastIndex (F : FullDefinition19Deformation O Cprime) :
    Fin F.deformation.stepCount :=
  ⟨F.deformation.stepCount - 1, by
    have hpos := F.nonempty
    omega⟩

/-- The terminal hole `C^(m)` of the complete deformation. -/
def terminalHole (F : FullDefinition19Deformation O Cprime) :
    IndexedInducedHole G :=
  (F.deformation.step F.lastIndex).after

/-- The paper's boundary `∂O`: all vertices introduced or removed by a
single-vertex replacement.  For a Definition 19 path block these are exactly
its alternating path vertices. -/
def boundary (F : FullDefinition19Deformation O Cprime) : Set V :=
  {u | ∃ i : Fin F.deformation.stepCount,
    u = (F.deformation.step i).introduced ∨
    u = (F.deformation.step i).before.vertex
      (F.deformation.step i).removedIndex}

/-- Definition 20's union of all dependent subsets. -/
def dependentUnion (F : FullDefinition19Deformation O Cprime) : Set V :=
  {u | ∃ i : Fin F.deformation.stepCount,
    u ∈ (F.deformation.step i).dependentSet}

@[simp]
theorem mem_boundary_iff
    (F : FullDefinition19Deformation O Cprime) {u : V} :
    u ∈ F.boundary ↔
      ∃ i : Fin F.deformation.stepCount,
        u = (F.deformation.step i).introduced ∨
        u = (F.deformation.step i).before.vertex
          (F.deformation.step i).removedIndex :=
  Iff.rfl

@[simp]
theorem mem_dependentUnion_iff
    (F : FullDefinition19Deformation O Cprime) {u : V} :
    u ∈ F.dependentUnion ↔
      ∃ i : Fin F.deformation.stepCount,
        u ∈ (F.deformation.step i).dependentSet :=
  Iff.rfl

/-- A prime-hole vertex removed by the deformation belongs to the next
Definition 20 dependent subset. -/
theorem removed_mem_dependentUnion
    (F : FullDefinition19Deformation O Cprime)
    (i : Fin F.deformation.stepCount)
    (hprime :
      (F.deformation.step i).before.vertex
          (F.deformation.step i).removedIndex ∈ Cprime) :
    (F.deformation.step i).before.vertex
        (F.deformation.step i).removedIndex ∈ F.dependentUnion := by
  obtain ⟨j, _hij, hadj, hne, hnonadj⟩ :=
    F.removedPrime_hasSuccessor i hprime
  refine ⟨j, ?_⟩
  exact ⟨hprime, hadj, hne, hnonadj⟩

/-- If a vertex is removed at step `i` but belongs to the terminal hole,
some later step must introduce that same vertex. -/
theorem exists_later_introduced_of_removed_mem_terminal
    (F : FullDefinition19Deformation O Cprime)
    (i : Fin F.deformation.stepCount)
    (hterminal :
      (F.deformation.step i).before.vertex
          (F.deformation.step i).removedIndex ∈
        Set.range F.terminalHole.vertex) :
    ∃ j : Fin F.deformation.stepCount,
      i.val < j.val ∧
      (F.deformation.step i).before.vertex
          (F.deformation.step i).removedIndex =
        (F.deformation.step j).introduced := by
  let x : V :=
    (F.deformation.step i).before.vertex
      (F.deformation.step i).removedIndex
  by_contra hnone
  push Not at hnone
  have habsent : ∀ (n : Nat) (hn : n < F.deformation.stepCount),
      i.val ≤ n →
      x ∉ Set.range
        (F.deformation.step ⟨n, hn⟩).after.vertex := by
    intro n hn hin
    induction n, hin using Nat.le_induction with
    | base =>
        simpa [x] using
          (F.deformation.step i).removed_not_mem_after
    | succ n hin ih =>
        have hnPrev : n < F.deformation.stepCount := by omega
        let previous : Fin F.deformation.stepCount := ⟨n, hnPrev⟩
        let current : Fin F.deformation.stepCount := ⟨n + 1, hn⟩
        intro hxAfter
        have hxNeIntroduced :
            x ≠ (F.deformation.step current).introduced := by
          exact hnone current (by
            dsimp [current]
            omega)
        have hxBefore :
            x ∈ Set.range
              (F.deformation.step current).before.vertex :=
          (F.deformation.step current).mem_before_of_mem_after_of_ne_introduced
              (by simpa [current] using hxAfter) hxNeIntroduced
        have hchain :
            Set.range (F.deformation.step previous).after.vertex =
              Set.range (F.deformation.step current).before.vertex :=
          F.deformation.carrier_chain (i := previous) (j := current) (by
            simp [previous, current])
        have hxPrevious :
            x ∈ Set.range
              (F.deformation.step previous).after.vertex := by
          rw [hchain]
          exact hxBefore
        exact ih hnPrev (by simpa [previous] using hxPrevious)
  have hlast :
      F.deformation.stepCount - 1 < F.deformation.stepCount := by
    have hpos := F.nonempty
    omega
  have hiLast : i.val ≤ F.deformation.stepCount - 1 := by
    have hi := i.isLt
    omega
  have hnotTerminal :=
    habsent (F.deformation.stepCount - 1) hlast hiLast
  exact hnotTerminal (by
    simpa [terminalHole, lastIndex] using hterminal)

/-- If a vertex introduced at step `i` is absent from the terminal hole,
some later step must remove it. -/
theorem exists_later_removed_of_introduced_not_mem_terminal
    (F : FullDefinition19Deformation O Cprime)
    (i : Fin F.deformation.stepCount)
    (hterminal :
      (F.deformation.step i).introduced ∉
        Set.range F.terminalHole.vertex) :
    ∃ j : Fin F.deformation.stepCount,
      i.val < j.val ∧
      (F.deformation.step i).introduced =
        (F.deformation.step j).before.vertex
          (F.deformation.step j).removedIndex := by
  let x : V := (F.deformation.step i).introduced
  by_contra hnone
  push Not at hnone
  have hpresent : ∀ (n : Nat) (hn : n < F.deformation.stepCount),
      i.val ≤ n →
      x ∈ Set.range
        (F.deformation.step ⟨n, hn⟩).after.vertex := by
    intro n hn hin
    induction n, hin using Nat.le_induction with
    | base =>
        simpa [x] using
          (F.deformation.step i).introduced_mem_after
    | succ n hin ih =>
        have hnPrev : n < F.deformation.stepCount := by omega
        let previous : Fin F.deformation.stepCount := ⟨n, hnPrev⟩
        let current : Fin F.deformation.stepCount := ⟨n + 1, hn⟩
        have hxPrevious :
            x ∈ Set.range
              (F.deformation.step previous).after.vertex := by
          simpa [previous] using ih hnPrev
        have hchain :
            Set.range (F.deformation.step previous).after.vertex =
              Set.range (F.deformation.step current).before.vertex :=
          F.deformation.carrier_chain (i := previous) (j := current) (by
            simp [previous, current])
        have hxBefore :
            x ∈ Set.range
              (F.deformation.step current).before.vertex := by
          rw [← hchain]
          exact hxPrevious
        have hxNeRemoved :
            x ≠ (F.deformation.step current).before.vertex
              (F.deformation.step current).removedIndex := by
          exact hnone current (by
            dsimp [current]
            omega)
        have hxAfter :=
          (F.deformation.step current).mem_after_of_mem_before_of_ne_removed
            hxBefore hxNeRemoved
        simpa [current] using hxAfter
  have hlast :
      F.deformation.stepCount - 1 < F.deformation.stepCount := by
    have hpos := F.nonempty
    omega
  have hiLast : i.val ≤ F.deformation.stepCount - 1 := by
    have hi := i.isLt
    omega
  apply hterminal
  simpa [terminalHole, lastIndex] using
    hpresent (F.deformation.stepCount - 1) hlast hiLast

/-- A terminal-hole vertex which is outside the deformation boundary was
already present immediately after every earlier step.  This is the carrier
transport used in Lemma 12: away from `∂O`, no later replacement can be
the first one to introduce the vertex. -/
theorem mem_after_of_mem_terminal_of_not_mem_boundary
    (F : FullDefinition19Deformation O Cprime)
    (i : Fin F.deformation.stepCount)
    {x : V}
    (hxTerminal : x ∈ Set.range F.terminalHole.vertex)
    (hxBoundary : x ∉ F.boundary) :
    x ∈ Set.range (F.deformation.step i).after.vertex := by
  have hxNeIntroduced : ∀ j : Fin F.deformation.stepCount,
      x ≠ (F.deformation.step j).introduced := by
    intro j hEq
    apply hxBoundary
    exact F.mem_boundary_iff.mpr ⟨j, Or.inl hEq⟩
  have hbackward : ∀ (n : Nat) (hn : n < F.deformation.stepCount),
      i.val ≤ n →
      x ∈ Set.range
        (F.deformation.step ⟨n, hn⟩).after.vertex →
      x ∈ Set.range (F.deformation.step i).after.vertex := by
    intro n hn hin
    induction n, hin using Nat.le_induction with
    | base =>
        intro hx
        simpa using hx
    | succ n hin ih =>
        intro hxCurrentAfter
        have hnPrevious : n < F.deformation.stepCount := by omega
        let previous : Fin F.deformation.stepCount := ⟨n, hnPrevious⟩
        let current : Fin F.deformation.stepCount := ⟨n + 1, hn⟩
        have hxCurrentBefore :
            x ∈ Set.range
              (F.deformation.step current).before.vertex :=
          (F.deformation.step current).mem_before_of_mem_after_of_ne_introduced
            (by simpa [current] using hxCurrentAfter)
            (hxNeIntroduced current)
        have hchain :
            Set.range (F.deformation.step previous).after.vertex =
              Set.range (F.deformation.step current).before.vertex :=
          F.deformation.carrier_chain (i := previous) (j := current) (by
            simp [previous, current])
        have hxPreviousAfter :
            x ∈ Set.range
              (F.deformation.step previous).after.vertex := by
          rw [hchain]
          exact hxCurrentBefore
        exact ih hnPrevious (by simpa [previous] using hxPreviousAfter)
  have hlast :
      F.deformation.stepCount - 1 < F.deformation.stepCount := by
    have hpos := F.nonempty
    omega
  have hiLast : i.val ≤ F.deformation.stepCount - 1 := by
    have hi := i.isLt
    omega
  apply hbackward (F.deformation.stepCount - 1) hlast hiLast
  simpa [terminalHole, lastIndex] using hxTerminal

/-- Contrapositive form of terminal-to-earlier carrier transport. -/
theorem not_mem_terminal_of_not_mem_after_of_not_mem_boundary
    (F : FullDefinition19Deformation O Cprime)
    (i : Fin F.deformation.stepCount)
    {x : V}
    (hxAfter : x ∉ Set.range (F.deformation.step i).after.vertex)
    (hxBoundary : x ∉ F.boundary) :
    x ∉ Set.range F.terminalHole.vertex := by
  intro hxTerminal
  exact hxAfter
    (F.mem_after_of_mem_terminal_of_not_mem_boundary
      i hxTerminal hxBoundary)

/-- Lemma 13.  Under the Lemma 12 criterion `U ⊆ C^(m)`, every vertex
in exactly one of the prime hole `C'` and terminal hole `C^(m)` is absent
from the deformation boundary. -/
theorem lemma13
    (F : FullDefinition19Deformation O Cprime)
    (hcriterion :
      F.dependentUnion ⊆ Set.range F.terminalHole.vertex)
    {u : V}
    (hu : u ∈ Cprime ∆ Set.range F.terminalHole.vertex) :
    u ∉ F.boundary := by
  intro huBoundary
  obtain ⟨i, hintroduced | hremoved⟩ :=
    F.mem_boundary_iff.mp huBoundary
  · rcases Set.mem_symmDiff.mp hu with
      ⟨huPrime, huNotTerminal⟩ | ⟨huTerminal, huNotPrime⟩
    · have hnotTerminal :
          (F.deformation.step i).introduced ∉
            Set.range F.terminalHole.vertex := by
        simpa [hintroduced] using huNotTerminal
      obtain ⟨j, _hij, hremovedLater⟩ :=
        F.exists_later_removed_of_introduced_not_mem_terminal
          i hnotTerminal
      have hprimeLater :
          (F.deformation.step j).before.vertex
              (F.deformation.step j).removedIndex ∈ Cprime := by
        simpa [← hintroduced, ← hremovedLater] using huPrime
      have hdep := F.removed_mem_dependentUnion j hprimeLater
      exact huNotTerminal (by
        rw [hintroduced, hremovedLater]
        exact hcriterion hdep)
    · apply huNotPrime
      rw [hintroduced]
      exact F.introduced_mem_prime i
  · rcases Set.mem_symmDiff.mp hu with
      ⟨huPrime, huNotTerminal⟩ | ⟨huTerminal, huNotPrime⟩
    · have hprimeRemoved :
          (F.deformation.step i).before.vertex
              (F.deformation.step i).removedIndex ∈ Cprime := by
        simpa [hremoved] using huPrime
      have hdep := F.removed_mem_dependentUnion i hprimeRemoved
      exact huNotTerminal (by
        rw [hremoved]
        exact hcriterion hdep)
    · have hterminalRemoved :
          (F.deformation.step i).before.vertex
              (F.deformation.step i).removedIndex ∈
            Set.range F.terminalHole.vertex := by
        simpa [hremoved] using huTerminal
      obtain ⟨j, _hij, hintroducedLater⟩ :=
        F.exists_later_introduced_of_removed_mem_terminal
          i hterminalRemoved
      apply huNotPrime
      rw [hremoved, hintroducedLater]
      exact F.introduced_mem_prime j

end FullDefinition19Deformation

end FixedPairingPathFamily

end SimpleGraph
