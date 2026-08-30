import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.BigOperators

/-!
# Matrix realizations of operator Krylov recursions

Theorem 3 of the manuscript asserts that nested commutators with the
Hamiltonian are coefficients of powers of a finite path-indexed matrix.  The
graph-specific work is the one-step commutator classification.  This file
separates out the purely algebraic induction: once the commutator of every
basis operator is represented by one matrix row, every nested commutator is
represented by the corresponding matrix power.

The coefficient ring is commutative, while the operator algebra may be
noncommutative.  Scalar coefficients act through the algebra structure and
therefore commute with every operator.
-/

open scoped BigOperators

universe u v

/-- The ordinary ring commutator with a fixed left argument. -/
def algebraCommutator
    {A : Type v} [Ring A]
    (H x : A) : A :=
  H * x - x * H

/-- Commutation with a fixed operator is linear over the central coefficient
ring. -/
def commutatorLinearMap
    {R : Type u} {A : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (H : A) : A →ₗ[R] A where
  toFun := algebraCommutator H
  map_add' := by
    intro x y
    simp only [algebraCommutator, mul_add, add_mul]
    exact (sub_add_sub_comm (H * x) (x * H) (H * y) (y * H)).symm
  map_smul' := by
    intro r x
    simp only [algebraCommutator, Algebra.smul_def, RingHom.id_apply]
    calc
      H * ((algebraMap R A) r * x) -
          ((algebraMap R A) r * x) * H =
          (algebraMap R A) r * (H * x) -
            (algebraMap R A) r * (x * H) := by
            rw [← mul_assoc H, ← Algebra.commutes r H,
              mul_assoc, mul_assoc]
      _ = (algebraMap R A) r * (H * x - x * H) := by
            rw [mul_sub]

@[simp]
theorem commutatorLinearMap_apply
    {R : Type u} {A : Type v}
    [CommRing R] [Ring A] [Algebra R A]
    (H x : A) :
    commutatorLinearMap (R := R) H x = algebraCommutator H x :=
  rfl

/-- Repeated commutation with `H`, with depth zero equal to the input. -/
def iteratedCommutator
    {A : Type v} [Ring A]
    (H : A) : Nat → A → A
  | 0, x => x
  | n + 1, x => algebraCommutator H (iteratedCommutator H n x)

@[simp]
theorem iteratedCommutator_zero
    {A : Type v} [Ring A]
    (H x : A) :
    iteratedCommutator H 0 x = x :=
  rfl

@[simp]
theorem iteratedCommutator_succ
    {A : Type v} [Ring A]
    (H : A) (n : Nat) (x : A) :
    iteratedCommutator H (n + 1) x =
      algebraCommutator H (iteratedCommutator H n x) :=
  rfl

/-- A one-step basis transition determines all nested commutators by matrix
powers.

This is the abstract matrix-realization statement used by manuscript Theorem
3.  Its sole substantive premise is the graph-specific one-step formula; no
matrix-power or higher-commutator equality is accepted as data. -/
theorem iteratedCommutator_eq_matrixPow_sum
    {X : Type u} {R : Type u} {A : Type v}
    [Fintype X] [DecidableEq X]
    [CommRing R] [Ring A] [Algebra R A]
    (H : A) (basis : X → A) (T : Matrix X X R)
    (hstep : ∀ x : X,
      algebraCommutator H (basis x) =
        ∑ y : X, T x y • basis y)
    (n : Nat) (source : X) :
    iteratedCommutator H n (basis source) =
      ∑ y : X, (T ^ n) source y • basis y := by
  induction n with
  | zero =>
      simp [Matrix.one_apply]
  | succ n ih =>
      rw [iteratedCommutator_succ, ih]
      change commutatorLinearMap (R := R) H
          (∑ y : X, (T ^ n) source y • basis y) = _
      rw [map_sum]
      simp_rw [LinearMap.map_smul, commutatorLinearMap_apply, hstep]
      rw [pow_succ]
      simp only [Matrix.mul_apply]
      simp_rw [Finset.smul_sum, smul_smul, Finset.sum_smul]
      rw [Finset.sum_comm]
