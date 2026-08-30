import Mathlib.Data.Matrix.Mul

/-!
# Lifting a deformation-quotient transition matrix

The printed proof of manuscript Lemma 18 attempts to replace the suffix of
each individual walk after its last crossing of the deformation index.  That
replacement is not defined for walks which leave the displayed prefix chain.

This file records a different, global route.  If the transition matrix is
constructed on deformation classes and then lifted to paths, its columns
depend only on the target class.  Every positive matrix power therefore has
the same property.  The zeroth power has it as well when the source belongs
to a singleton class, as the adjoined root path does.

The theorem below is purely linear algebra.  It does not claim that the
specific Eq. (E1) matrix is such a lift; proving the operator transition
factors through deformation classes is the remaining graph/operator
obligation.
-/

universe u v w

/-- Lift a matrix on quotient classes to the underlying finite index type.

No choice of representative is involved.  The lifted entry depends only on
the source and target classes. -/
def quotientLiftMatrix
    {X : Type u} {C : Type v} {R : Type w}
    (classOf : X → C) (B : Matrix C C R) : Matrix X X R :=
  fun x y => B (classOf x) (classOf y)

@[simp]
theorem quotientLiftMatrix_apply
    {X : Type u} {C : Type v} {R : Type w}
    (classOf : X → C) (B : Matrix C C R) (x y : X) :
    quotientLiftMatrix classOf B x y = B (classOf x) (classOf y) :=
  rfl

/-- Equal target classes give equal columns of the lifted matrix. -/
theorem quotientLiftMatrix_column_eq
    {X : Type u} {C : Type v} {R : Type w}
    (classOf : X → C) (B : Matrix C C R)
    {y z : X} (hyz : classOf y = classOf z) (x : X) :
    quotientLiftMatrix classOf B x y =
      quotientLiftMatrix classOf B x z := by
  simp [quotientLiftMatrix, hyz]

/-- If two columns of a square matrix agree, then the corresponding entries
of every positive power agree, for every source. -/
theorem matrixPow_apply_eq_of_column_eq
    {X : Type u} {R : Type w}
    [Fintype X] [DecidableEq X] [Semiring R]
    (A : Matrix X X R) {y z : X}
    (hcol : ∀ x, A x y = A x z)
    (n : Nat) (source : X) :
    (A ^ (n + 1)) source y = (A ^ (n + 1)) source z := by
  rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro x _
  rw [hcol x]

/-- Matrix-power amplitudes of a quotient lift are constant on every target
class.  The singleton-source condition is needed only for the zeroth power. -/
theorem quotientLiftMatrix_pow_apply_eq
    {X : Type u} {C : Type v} {R : Type w}
    [Fintype X] [DecidableEq X] [Semiring R]
    (classOf : X → C) (B : Matrix C C R)
    {source y z : X}
    (hsource : ∀ x, classOf x = classOf source → x = source)
    (hyz : classOf y = classOf z)
    (n : Nat) :
    (quotientLiftMatrix classOf B ^ n) source y =
      (quotientLiftMatrix classOf B ^ n) source z := by
  cases n with
  | zero =>
      rw [pow_zero, pow_zero, Matrix.one_apply, Matrix.one_apply]
      by_cases hsy : source = y
      · have hsz : source = z := by
          apply hsource z
          rw [← hyz, ← hsy]
        simp [hsy, hsz]
      · have hsz : source ≠ z := by
          intro h
          apply hsy
          apply hsource y
          rw [hyz, ← h]
        simp [hsy, hsz]
  | succ n =>
      exact matrixPow_apply_eq_of_column_eq
        (quotientLiftMatrix classOf B)
        (fun x => quotientLiftMatrix_column_eq classOf B hyz x)
        n source
