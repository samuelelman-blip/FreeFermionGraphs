import Mathlib.Data.Matrix.Mul

/-!
# Deformation-class invariant transition matrices

The printed proof of manuscript Lemma 18 attempts to replace the suffix of
each individual walk after its last crossing of the deformation index.  That
replacement is not defined for walks which leave the displayed prefix chain.

This file records a different, global route.  It is enough that right
multiplication by the transition matrix preserve row functions which are
constant on deformation classes.  Induction then gives the amplitude identity
at every matrix power.  A literal matrix lifted from the quotient is one
sufficient special case, but the general preservation criterion also allows
different raw columns whose contributions agree only after class aggregation.

The theorems below are purely linear algebra.  They do not claim that the
specific Eq. (E1) matrix satisfies the preservation criterion.  In fact, the
literal partition by internal path deformations need not be preserved: the
prefix ending at the changed vertex is not itself related by an internal
deformation.  Applying this criterion therefore requires a richer spectral
class relation or a transition constructed directly on an operator quotient.
-/

universe u v w

/-- A row-valued function is constant on the fibres of `classOf`. -/
def ClassConstant
    {X : Type u} {C : Type v} {R : Type w}
    (classOf : X → C) (f : X → R) : Prop :=
  ∀ ⦃x y : X⦄, classOf x = classOf y → f x = f y

/-- The right action of a square matrix on a row-valued function. -/
noncomputable def matrixRightAction
    {X : Type u} {R : Type w}
    [Fintype X] [Semiring R]
    (A : Matrix X X R) (f : X → R) : X → R :=
  fun y ⇒ ∑ x : X, f x * A x y

/-- A global sufficient condition for a corrected Lemma 18 argument: one
transition sends every row which is constant on deformation classes to
another row which is constant on those classes.

This condition is strictly weaker than equality of individual matrix
columns.  It allows contributions from different paths in one deformation
class to cancel or combine before the class comparison is made. -/
def MatrixPreservesClassConstant
    {X : Type u} {C : Type v} {R : Type w}
    [Fintype X] [Semiring R]
    (classOf : X → C) (A : Matrix X X R) : Prop :=
  ∀ f : X → R, ClassConstant classOf f →
    ClassConstant classOf (matrixRightAction A f)

/-- If the source fibre is a singleton, the zeroth-power row at that source
is constant on classes. -/
theorem matrixOneRow_classConstant
    {X : Type u} {C : Type v} {R : Type w}
    [DecidableEq X] [Semiring R]
    (classOf : X → C) (source : X)
    (hsource : ∀ x, classOf x = classOf source → x = source) :
    ClassConstant classOf (fun y ⇒ (1 : Matrix X X R) source y) := by
  intro y z hyz
  rw [Matrix.one_apply, Matrix.one_apply]
  by_cases hsy : source = y
  · have hsz : source = z := by
      exact (hsource z (by rw [← hyz, ← hsy])).symm
    simp [hsy, hsz]
  · have hsz : source ≠ z := by
      intro h
      apply hsy
      exact (hsource y (by rw [hyz, ← h])).symm
    simp [hsy, hsz]

/-- A class-preserving transition makes every matrix-power row from a
singleton source constant on classes.  This is the abstract induction for a
possible replacement of the manuscript's non-total last-crossing walk
substitution. -/
theorem matrixPow_row_classConstant
    {X : Type u} {C : Type v} {R : Type w}
    [Fintype X] [DecidableEq X] [Semiring R]
    (classOf : X → C) (A : Matrix X X R)
    (hA : MatrixPreservesClassConstant classOf A)
    (source : X)
    (hsource : ∀ x, classOf x = classOf source → x = source)
    (n : Nat) :
    ClassConstant classOf (fun y ⇒ (A ^ n) source y) := by
  induction n with
  | zero =>
      simpa only [pow_zero] using
        matrixOneRow_classConstant classOf source hsource
  | succ n ih =>
      have hstep := hA (fun y ⇒ (A ^ n) source y) ih
      intro y z hyz
      simpa only [matrixRightAction, pow_succ, Matrix.mul_apply] using
        hstep hyz

/-- Paper-shaped consequence of the global transition criterion: targets in
the same class have equal amplitudes at every nonnegative power. -/
theorem matrixPow_apply_eq_of_preservesClassConstant
    {X : Type u} {C : Type v} {R : Type w}
    [Fintype X] [DecidableEq X] [Semiring R]
    (classOf : X → C) (A : Matrix X X R)
    (hA : MatrixPreservesClassConstant classOf A)
    {source y z : X}
    (hsource : ∀ x, classOf x = classOf source → x = source)
    (hyz : classOf y = classOf z)
    (n : Nat) :
    (A ^ n) source y = (A ^ n) source z :=
  matrixPow_row_classConstant classOf A hA source hsource n hyz

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

/-- A literal quotient lift satisfies the global class-preservation
criterion.  The criterion above also applies to less rigid matrices whose
individual columns are not equal. -/
theorem quotientLiftMatrix_preservesClassConstant
    {X : Type u} {C : Type v} {R : Type w}
    [Fintype X] [Semiring R]
    (classOf : X → C) (B : Matrix C C R) :
    MatrixPreservesClassConstant classOf
      (quotientLiftMatrix classOf B) := by
  intro f _ y z hyz
  simp only [matrixRightAction, quotientLiftMatrix]
  apply Finset.sum_congr rfl
  intro x _
  rw [hyz]

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
          exact (hsource z (by rw [← hyz, ← hsy])).symm
        simp [hsy, hsz]
      · have hsz : source ≠ z := by
          intro h
          apply hsy
          exact (hsource y (by rw [hyz, ← h])).symm
        simp [hsy, hsz]
  | succ n =>
      exact matrixPow_apply_eq_of_column_eq
        (quotientLiftMatrix classOf B)
        (fun x => quotientLiftMatrix_column_eq classOf B hyz x)
        n source
