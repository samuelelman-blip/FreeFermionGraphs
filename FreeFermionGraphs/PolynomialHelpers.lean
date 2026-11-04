import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Real.Basic

/-!
# Polynomial and Lagrange helpers for operator-valued polynomial identities

Auxiliary results used to replace the informal limit and interpolation steps in the
proofs of v1 Lemma 14 (the limit `u -> u_j`, v1 `main.tex` L2077-2084) and v1 Lemma 15
(the limit at L2114-2116 and the "Lagrange interpolation formula" at L2127-2139) of
Chapman--Elman--Mann, arXiv:2305.15625v1, by exact algebra.

There is no statement in the manuscript to match; these are purely algebraic lemmas.

* `eq_zero_of_infinite_sum_smul_pow`: if `∑_{k<n} x^k • a_k = 0` for infinitely many real
  `x`, with the `a_k` in a real vector space, then every `a_k` vanishes.  This turns identities
  proved pointwise in the spectral parameter into coefficient identities.
* `Polynomial.eq_zero_of_infinite_eval_algebraMap`: the same statement for a polynomial with
  coefficients in a (possibly noncommutative) `ℝ`-algebra `A`, evaluated at the central real
  points `algebraMap ℝ A x`.
* `Polynomial.eval_eq_neg_derivative_of_mul_eq`: if `(C v - X) * F = G` in `A[X]`, with `v` a
  central real scalar, then `F(v) = -G'(v)`.  This is the exact form of the limit `u -> u_j`.
* `lagrange_weights_at_zero`: for pairwise distinct reals `x_1, ..., x_r` and `k < r`,
  `∑_j x_j^k ∏_{i ≠ j} x_i / (x_i - x_j) = δ_{k0}` (Lagrange weights at `0`).  No nonvanishing
  hypothesis on the nodes is needed.
-/

open Polynomial
open scoped BigOperators

/-- If `∑_{k<n} x^k • a_k = 0` for infinitely many real `x`, then all `a_k` (`k < n`) vanish. -/
theorem eq_zero_of_infinite_sum_smul_pow {M : Type*} [AddCommGroup M] [Module ℝ M]
    (a : ℕ → M) (n : ℕ)
    (h : {x : ℝ | ∑ k ∈ Finset.range n, x ^ k • a k = 0}.Infinite) :
    ∀ k < n, a k = 0 := by
  intro k hk
  rw [← Module.forall_dual_apply_eq_zero_iff ℝ (a k)]
  intro φ
  -- the scalar polynomial `∑ φ(a_k) X^k` has infinitely many roots, hence vanishes
  set p : ℝ[X] := ∑ j ∈ Finset.range n, C (φ (a j)) * X ^ j with hp
  have hroot : {x : ℝ | ∑ j ∈ Finset.range n, x ^ j • a j = 0} ⊆ {x : ℝ | IsRoot p x} := by
    intro x hx
    have hx' : ∑ j ∈ Finset.range n, x ^ j • a j = 0 := hx
    have := congrArg φ hx'
    rw [map_sum, map_zero] at this
    simp only [map_smul, smul_eq_mul] at this
    show p.eval x = 0
    rw [hp, eval_finsetSum]
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hp0 : p = 0 := eq_zero_of_infinite_isRoot p (h.mono hroot)
  have hc : p.coeff k = φ (a k) := by
    rw [hp, finsetSum_coeff]
    simp [coeff_C_mul, coeff_X_pow, hk]
  rw [← hc, hp0, coeff_zero]

namespace Polynomial

/-- A polynomial over an `ℝ`-algebra that vanishes at infinitely many central real points is zero. -/
theorem eq_zero_of_infinite_eval_algebraMap {A : Type*} [Ring A] [Algebra ℝ A] (p : Polynomial A)
    (h : {x : ℝ | p.eval (algebraMap ℝ A x) = 0}.Infinite) : p = 0 := by
  have hset : {x : ℝ | p.eval (algebraMap ℝ A x) = 0} ⊆
      {x : ℝ | ∑ k ∈ Finset.range (p.natDegree + 1), x ^ k • p.coeff k = 0} := by
    intro x hx
    have hx' : p.eval (algebraMap ℝ A x) = 0 := hx
    show ∑ k ∈ Finset.range (p.natDegree + 1), x ^ k • p.coeff k = 0
    rw [eval_eq_sum_range] at hx'
    rw [← hx']
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← map_pow, ← Algebra.commutes, ← Algebra.smul_def]
  have key := eq_zero_of_infinite_sum_smul_pow (fun k => p.coeff k) (p.natDegree + 1) (h.mono hset)
  ext k
  rw [coeff_zero]
  by_cases hk : k < p.natDegree + 1
  · exact key k hk
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

/-- If `(C v - X) * F = G` in `A[X]`, with `v` a central real scalar, then
`F(v) = -G'(v)`. -/
theorem eval_eq_neg_derivative_of_mul_eq {A : Type*} [Ring A] [Algebra ℝ A] (v : ℝ)
    (F G : Polynomial A)
    (h : (Polynomial.C (algebraMap ℝ A v) - Polynomial.X) * F = G) :
    F.eval (algebraMap ℝ A v) = -(Polynomial.derivative G).eval (algebraMap ℝ A v) := by
  subst h
  have hcomm : ∀ q : A[X], ((C (algebraMap ℝ A v) - X) * q).eval (algebraMap ℝ A v) = 0 := by
    intro q
    rw [sub_mul, eval_sub, eval_C_mul, X_mul, eval_mul_X, ← Algebra.commutes, sub_self]
  rw [derivative_mul, eval_add, hcomm, derivative_sub, derivative_C, derivative_X, zero_sub,
    neg_mul, one_mul, eval_neg]
  simp

end Polynomial

/-- Lagrange weights at `0`: for pairwise distinct real nodes `x_1, ..., x_r` and `k < r`,
`∑_j x_j^k ∏_{i ≠ j} x_i / (x_i - x_j) = δ_{k0}`.

No nonvanishing hypothesis on the nodes is needed.  This is the exact form of the "Lagrange
interpolation formula" used at the end of the proof of v1 Lemma 15 (v1 `main.tex` L2127-2139). -/
theorem lagrange_weights_at_zero {r : ℕ} (x : Fin r → ℝ) (hx : Function.Injective x) {k : ℕ}
    (hk : k < r) :
    ∑ j, x j ^ k * ∏ i ∈ Finset.univ.erase j, x i / (x i - x j) = if k = 0 then 1 else 0 := by
  have hvs : Set.InjOn x (Finset.univ : Finset (Fin r)) := fun a _ b _ h => hx h
  have hdeg : ((X : ℝ[X]) ^ k).degree < (Finset.univ : Finset (Fin r)).card := by
    rw [degree_X_pow, Finset.card_univ, Fintype.card_fin]
    exact_mod_cast hk
  have h0 := congrArg (eval 0) (Lagrange.eq_interpolate hvs hdeg)
  simp only [Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C, Lagrange.basis,
    Lagrange.basisDivisor, eval_prod, eval_pow, eval_X, eval_sub] at h0
  have h1 : (0 : ℝ) ^ k = if k = 0 then 1 else 0 := by
    split_ifs with hk0
    · simp [hk0]
    · exact zero_pow hk0
  rw [← h1, h0]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  have hij : x i ≠ x j := hx.ne (Finset.ne_of_mem_erase hi)
  have h2 : x i - x j ≠ 0 := sub_ne_zero.mpr hij
  have h3 : x j - x i ≠ 0 := sub_ne_zero.mpr hij.symm
  field_simp
  ring
