import FreeFermionGraphs.Lemma11BHalfLengthTwo

/-!
# Full cyclic order for alternating hole labels

The basic `EvenHoleLabeling` interface records that `next` has no fixed
points or two-cycles.  The paper uses the stronger intended meaning:
`next` walks once around a single cycle, so no positive iterate shorter
than the half-length returns to its starting index.

This module records that full cyclic-order condition, proves that it is
unchanged by clone deformation, and derives the cross-color nonedges needed
for Lemma 11(b)'s half-length-greater-than-three obstruction.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace EvenHoleLabeling

/-- Iterate the cyclic successor map. -/
def nextIterate {k : Nat} (C : EvenHoleLabeling G k) :
    Nat → Fin k → Fin k
  | 0, i => i
  | n + 1, i => C.next (C.nextIterate n i)

@[simp]
theorem nextIterate_zero {k : Nat}
    (C : EvenHoleLabeling G k) (i : Fin k) :
    C.nextIterate 0 i = i :=
  rfl

@[simp]
theorem nextIterate_succ {k : Nat}
    (C : EvenHoleLabeling G k) (n : Nat) (i : Fin k) :
    C.nextIterate (n + 1) i =
      C.next (C.nextIterate n i) :=
  rfl

/-- The paper-faithful assertion that `next` traverses one full
half-cycle before returning to its starting index. -/
def HasFullCyclicOrder {k : Nat}
    (C : EvenHoleLabeling G k) : Prop :=
  ∀ (i : Fin k) (n : Nat),
    0 < n → n < k →
      C.nextIterate n i ≠ i

/-- Full cyclic order rules out a three-step return when the half-length is
greater than three. -/
theorem next_next_next_ne
    {k : Nat} (C : EvenHoleLabeling G k)
    (hcycle : C.HasFullCyclicOrder)
    (hk : 3 < k) (i : Fin k) :
    C.next (C.next (C.next i)) ≠ i := by
  have h := hcycle i 3 (by omega) hk
  simpa [nextIterate] using h

/-- Iteration of `next` is unchanged by a clone deformation. -/
theorem nextIterate_deform
    {k : Nat} (C : EvenHoleLabeling G k)
    {s : V} {i : Fin k} (h : C.CloneAt s i)
    (n : Nat) (q : Fin k) :
    (C.deform h).nextIterate n q =
      C.nextIterate n q := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp only [nextIterate_succ]
      exact congrArg C.next ih

/-- Consequently full cyclic order is preserved by deformation. -/
theorem hasFullCyclicOrder_deform
    {k : Nat} (C : EvenHoleLabeling G k)
    {s : V} {i : Fin k} (h : C.CloneAt s i)
    (hcycle : C.HasFullCyclicOrder) :
    (C.deform h).HasFullCyclicOrder := by
  intro q n hn hk
  rw [C.nextIterate_deform h n q]
  exact hcycle q n hn hk

/-- For half-length greater than two, `a (next i)` is not adjacent to
`b i`. -/
theorem not_adj_a_next_b
    {k : Nat} (C : EvenHoleLabeling G k)
    (hk : 2 < k) (i : Fin k) :
    ¬G.Adj (C.a (C.next i)) (C.b i) := by
  rw [C.adj_ab_iff]
  rintro (hi | hi)
  · exact C.next_ne i hi.symm
  · exact C.next_next_ne hk i hi.symm

/-- For half-length greater than three, `a (next (next i))` is also not
adjacent to `b i`.  The second possible cross-color edge would be exactly
a forbidden three-step return. -/
theorem not_adj_a_next_next_b
    {k : Nat} (C : EvenHoleLabeling G k)
    (hcycle : C.HasFullCyclicOrder)
    (hk : 3 < k) (i : Fin k) :
    ¬G.Adj (C.a (C.next (C.next i))) (C.b i) := by
  rw [C.adj_ab_iff]
  rintro (hi | hi)
  · exact C.next_next_ne (by omega) i hi.symm
  · exact C.next_next_next_ne hcycle hk i hi.symm

end EvenHoleLabeling

end SimpleGraph
