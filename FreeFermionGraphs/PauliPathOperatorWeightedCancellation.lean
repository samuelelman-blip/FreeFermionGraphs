import FreeFermionGraphs.PauliPathOperatorCancellation
import FreeFermionGraphs.DeformationQuotientLift

/-!
# Coefficient-weighted Pauli deformation cancellation

The raw ordered-product identity for a Definition 10 path deformation cancels
the two exchanged Hamiltonian terms.  This file incorporates scalar Krylov
coefficients.  Equal coefficients factor through the raw zero sum, and the
global class-preservation criterion supplies that equality for matrix-power
rows.

The result isolates the exact missing premise in the printed Lemma 18 proof:
the concrete Eq. (E1) transition still has to be shown to preserve the chosen
spectral classes.  No equality of amplitudes is accepted as an independent
certificate here.
-/

universe u v w z

variable {V : Type u}

namespace SimpleGraph

namespace PauliFrustrationRepresentation

variable {G : SimpleGraph V}
variable {R : Type v} {A : Type w}
variable [CommRing R] [Ring A] [Algebra R A]

/-- Scalar-weighted form of the literal deformation-pair cancellation. -/
theorem pathOperator_deformation_smul_add_eq_zero
    (H : G.PauliFrustrationRepresentation A)
    (P : IndexedInducedPath G) {s : V} {i : Fin P.card}
    (h : P.SingleVertexDeformation s i)
    {a b : R} (hab : a = b) :
    a • (H.pathOperator P * H.term s) +
      b • (H.pathOperator (P.deform h) * H.term (P.vertex i)) = 0 := by
  rw [hab, ← smul_add]
  rw [H.pathOperator_deformation_add_eq_zero P h]
  simp

/-- Corrected Eq. (E12) interface.  A transition preserving spectral-class
constant rows gives equal coefficients to a literal deformation pair at
every matrix power, and those two weighted operator contributions cancel.

The hypothesis `hT` is the global linear-algebra property that replaces the
non-total last-crossing walk substitution in the manuscript. -/
theorem pathOperator_deformation_matrixPow_add_eq_zero
    {X : Type z} {C : Type u}
    [Fintype X] [DecidableEq X]
    (H : G.PauliFrustrationRepresentation A)
    (classOf : X → C) (T : Matrix X X R)
    (hT : MatrixPreservesClassConstant classOf T)
    {source x y : X}
    (hsource : ∀ q, classOf q = classOf source → q = source)
    (hxy : classOf x = classOf y)
    (n : Nat)
    (P : IndexedInducedPath G) {s : V} {i : Fin P.card}
    (h : P.SingleVertexDeformation s i) :
    (T ^ n) source x • (H.pathOperator P * H.term s) +
      (T ^ n) source y •
        (H.pathOperator (P.deform h) * H.term (P.vertex i)) = 0 := by
  apply H.pathOperator_deformation_smul_add_eq_zero P h
  exact matrixPow_apply_eq_of_preservesClassConstant
    classOf T hT hsource hxy n

end PauliFrustrationRepresentation

end SimpleGraph
