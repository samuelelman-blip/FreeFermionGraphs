import FreeFermionGraphs.PauliFrustrationRepresentation
import Mathlib.Algebra.Algebra.Basic

/-!
# Pauli Hamiltonian terms squaring to central scalars

Part (iii) of Theorem 1 (arXiv 2305.15625 v1, proof at L1203-1241) cancels the
terms `h_C h_{C'}` and `h_{C~} h_{C~'}` using the normalisation `h_j^2 = b_j^2 I`
(v1 L232, for Pauli terms `h_j = b_j σ^j` with coupling `b_j`, L93) and the
invertibility of `B^2`, where `B^{-2}` is written explicitly at L1238.

`PauliFrustrationRepresentation` records only the commutation structure of the
terms.  This module adds exactly the extra data used there: a coupling
`b_j` for every vertex, assumed invertible, such that `h_j * h_j` is the
central scalar `b_j ^ 2`.  It mirrors the pattern of
`PauliCliqueHamiltonianRepresentation` (`operator`, `coupling`,
`original_term_sq`), but on the plain frustration graph.  The field
`coupling_isUnit` is the setup assumption `b_j ∈ ℝ∖{0}` of v1 L93, stated as
`IsUnit` because the coefficient ring is a general commutative ring (over `ℝ`
this is equivalent to `b_j ≠ 0`).  It is what makes `B^2` invertible at
v1 L1236-1238.

Theorem 1(i) and (ii) do not use this structure.

## Main declarations

* `SimpleGraph.ScaledPauliFrustrationRepresentation`: a Pauli frustration
  representation together with invertible couplings `b_j` and `h_j ^ 2 = b_j ^ 2`.
* `ScaledPauliFrustrationRepresentation.independentProduct_mul_self`: for an
  independent set `S`, `h_S * h_S = ∏_{j ∈ S} b_j ^ 2` (as a central scalar).
* `ScaledPauliFrustrationRepresentation.independentProduct_isUnit`: for an
  independent set `S`, the operator `h_S` is invertible, so products of such
  factors, like `h_O` in v1 L1203-1238, are invertible.  The scalar `B^2`
  itself is a unit directly by `coupling_isUnit`.
-/

open scoped BigOperators

universe u v w

variable {V : Type u}

namespace SimpleGraph

/-- Pauli Hamiltonian terms on the frustration graph `G` whose squares are the
central scalars `b_j ^ 2` with every coupling `b_j` invertible.

`coupling_isUnit` is the setup assumption `b_j ∈ ℝ∖{0}` of v1 L93
(`h_j = b_j σ^j`), stated as `IsUnit` because the coefficient ring is a general
commutative ring (over `ℝ` this is equivalent to `b_j ≠ 0`).  It is what makes
`B^2` invertible at v1 L1236-1238.  `term_sq` is the Pauli normalisation
`h_j^2 = b_j^2 I` of v1 L232. -/
structure ScaledPauliFrustrationRepresentation
    (G : SimpleGraph V) (R : Type v) (A : Type w)
    [CommRing R] [Ring A] [Algebra R A] where
  operator : G.PauliFrustrationRepresentation A
  coupling : V → R
  coupling_isUnit : ∀ j, IsUnit (coupling j)
  term_sq : ∀ j,
    operator.term j * operator.term j = algebraMap R A (coupling j ^ 2)

namespace ScaledPauliFrustrationRepresentation

variable {G : SimpleGraph V} {R : Type v} {A : Type w}
variable [CommRing R] [Ring A] [Algebra R A]

/-- Each term is invertible, because its square is an invertible central
scalar. -/
theorem term_isUnit (H : G.ScaledPauliFrustrationRepresentation R A) (j : V) :
    IsUnit (H.operator.term j) := by
  have hsq : IsUnit (H.operator.term j * H.operator.term j) := by
    rw [H.term_sq j]
    exact ((H.coupling_isUnit j).pow 2).map (algebraMap R A)
  exact ((Commute.refl (H.operator.term j)).isUnit_mul_iff.mp hsq).1

/-- The manuscript identity `h_S ^ 2 = ∏_{j ∈ S} b_j ^ 2` for an independent
set `S`.  The factors of `h_S` commute pairwise, so duplicated factors can be
brought together, and the scalars `b_j ^ 2` are central. -/
theorem independentProduct_mul_self [DecidableEq V]
    (H : G.ScaledPauliFrustrationRepresentation R A) {S : Finset V}
    (hS : G.IsIndepSet (S : Set V)) :
    H.operator.independentProduct S * H.operator.independentProduct S =
      algebraMap R A (∏ j ∈ S, H.coupling j ^ 2) := by
  induction S using Finset.induction_on with
  | empty =>
    simp [H.operator.independentProduct_empty]
  | insert j T hjT ih =>
    have hT : G.IsIndepSet (T : Set V) := hS.mono (by simp)
    have hNonadj : ∀ v ∈ T, ¬G.Adj j v := by
      intro v hvT hadj
      have hj : j ∈ ((insert j T : Finset V) : Set V) := by simp
      have hv : v ∈ ((insert j T : Finset V) : Set V) := by simp [hvT]
      exact hS hj hv (fun h => hjT (h ▸ hvT)) hadj
    have hleft := H.operator.independentProduct_insert_left hjT hT hNonadj
    have hright := H.operator.independentProduct_insert_right hjT hT hNonadj
    have ihT := ih hT
    rw [Finset.prod_insert hjT]
    calc H.operator.independentProduct (insert j T) *
          H.operator.independentProduct (insert j T)
        = (H.operator.term j * H.operator.independentProduct T) *
            (H.operator.independentProduct T * H.operator.term j) := by
          rw [← hleft, ← hright]
      _ = H.operator.term j *
            (H.operator.independentProduct T * H.operator.independentProduct T) *
            H.operator.term j := by
          simp only [mul_assoc]
      _ = H.operator.term j *
            algebraMap R A (∏ i ∈ T, H.coupling i ^ 2) * H.operator.term j := by
          rw [ihT]
      _ = algebraMap R A (∏ i ∈ T, H.coupling i ^ 2) *
            (H.operator.term j * H.operator.term j) := by
          rw [← Algebra.commutes (∏ i ∈ T, H.coupling i ^ 2) (H.operator.term j)]
          simp only [mul_assoc]
      _ = algebraMap R A (H.coupling j ^ 2 * ∏ i ∈ T, H.coupling i ^ 2) := by
          rw [H.term_sq j, ← map_mul, mul_comm]

/-- The canonical product `h_S` over an independent set is invertible, because
its square is the unit scalar `∏_{j ∈ S} b_j ^ 2`.  Hence products of such
factors, like `h_O` in v1 L1203-1238, are invertible.  The scalar `B^2` itself
(v1 L1236: `h_O h_O^† = B^2 I`) is a unit directly by `coupling_isUnit`. -/
theorem independentProduct_isUnit [DecidableEq V]
    (H : G.ScaledPauliFrustrationRepresentation R A) {S : Finset V}
    (hS : G.IsIndepSet (S : Set V)) :
    IsUnit (H.operator.independentProduct S) := by
  have hprod : IsUnit (∏ j ∈ S, H.coupling j ^ 2) :=
    IsUnit.prod_iff.mpr (fun j _ => (H.coupling_isUnit j).pow 2)
  have hsq : IsUnit (H.operator.independentProduct S *
      H.operator.independentProduct S) := by
    rw [H.independentProduct_mul_self hS]
    exact hprod.map (algebraMap R A)
  exact ((Commute.refl (H.operator.independentProduct S)).isUnit_mul_iff.mp hsq).1

end ScaledPauliFrustrationRepresentation

end SimpleGraph
