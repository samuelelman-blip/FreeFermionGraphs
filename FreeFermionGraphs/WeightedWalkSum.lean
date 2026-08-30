import Mathlib.Data.Matrix.Mul
import FreeFermionGraphs.InducedPathFintype

/-!
# Weighted finite walks and matrix powers

The recursively defined sum below is the weighted sum of all fixed-length
walks between two matrix indices: a zero-step walk has weight one precisely
at equal endpoints, and a successor walk chooses its penultimate vertex.  The
main theorem identifies this sum with the corresponding matrix-power entry.
-/

universe u w

/-- The weighted sum of all `n`-step walks from `x` to `y` for a square
matrix `A`. -/
noncomputable def weightedWalkSum
    {X : Type u} {R : Type w} [Fintype X] [DecidableEq X] [Semiring R]
    (A : Matrix X X R) : Nat → X → X → R
  | 0, x, y => if x = y then 1 else 0
  | n + 1, x, y => ∑ z : X, weightedWalkSum A n x z * A z y

@[simp]
theorem weightedWalkSum_zero
    {X : Type u} {R : Type w} [Fintype X] [DecidableEq X] [Semiring R]
    (A : Matrix X X R) (x y : X) :
    weightedWalkSum A 0 x y = if x = y then 1 else 0 :=
  rfl

@[simp]
theorem weightedWalkSum_succ
    {X : Type u} {R : Type w} [Fintype X] [DecidableEq X] [Semiring R]
    (A : Matrix X X R) (n : Nat) (x y : X) :
    weightedWalkSum A (n + 1) x y =
      ∑ z : X, weightedWalkSum A n x z * A z y :=
  rfl

/-- The recursive weighted-walk sum is exactly the corresponding matrix-power
entry. -/
theorem weightedWalkSum_eq_matrixPow
    {X : Type u} {R : Type w} [Fintype X] [DecidableEq X] [Semiring R]
    (A : Matrix X X R) (n : Nat) (x y : X) :
    weightedWalkSum A n x y = (A ^ n) x y := by
  induction n generalizing x y with
  | zero =>
      rw [weightedWalkSum_zero, pow_zero, Matrix.one_apply]
  | succ n ih =>
      rw [weightedWalkSum_succ, pow_succ, Matrix.mul_apply]
      simp_rw [ih]

/-- A weight-preserving permutation of the matrix indices transports every
weighted-walk sum.  This packages the reindexing argument needed once the
Lemma 18 walk correspondence is constructed. -/
theorem weightedWalkSum_equiv
    {X : Type u} {R : Type w} [Fintype X] [DecidableEq X] [Semiring R]
    (A : Matrix X X R) (e : X ≃ X)
    (hA : ∀ x y, A (e x) (e y) = A x y)
    (n : Nat) (x y : X) :
    weightedWalkSum A n (e x) (e y) = weightedWalkSum A n x y := by
  induction n generalizing x y with
  | zero =>
      rw [weightedWalkSum_zero, weightedWalkSum_zero]
      simp only [e.injective.eq_iff]
  | succ n ih =>
      rw [weightedWalkSum_succ, weightedWalkSum_succ]
      calc
        (∑ z : X, weightedWalkSum A n (e x) z * A z (e y)) =
            ∑ z : X, weightedWalkSum A n (e x) (e z) * A (e z) (e y) := by
              symm
              exact e.sum_comp
                (fun z => weightedWalkSum A n (e x) z * A z (e y))
        _ = ∑ z : X, weightedWalkSum A n x z * A z y := by
          apply Finset.sum_congr rfl
          intro z _
          rw [ih, hA]

/-- Consequently, a weight-preserving permutation fixing the source gives
equal matrix-power amplitudes at paired targets. -/
theorem matrixPow_apply_equiv
    {X : Type u} {R : Type w} [Fintype X] [DecidableEq X] [Semiring R]
    (A : Matrix X X R) (e : X ≃ X)
    (hA : ∀ x y, A (e x) (e y) = A x y)
    {source : X} (hsource : e source = source)
    (n : Nat) (target : X) :
    (A ^ n) source (e target) = (A ^ n) source target := by
  rw [← weightedWalkSum_eq_matrixPow, ← weightedWalkSum_eq_matrixPow]
  calc
    weightedWalkSum A n source (e target) =
        weightedWalkSum A n (e source) (e target) := by rw [hsource]
    _ = weightedWalkSum A n source target :=
      weightedWalkSum_equiv A e hA n source target
