import FreeFermionGraphs.LadderAnticommutation

/-!
# The commutator `[ψ_j^+, ψ_j^-]` in terms of `T` and `T'`

Manuscript (arXiv 2305.15625 v1), proof of Lemma 15 (`DiagonalRelation`, statement L1315,
proof L2106-2139), first half: the commutator displays at L2113-2121.  In the numbering of the
revised manuscript used by the repository, v1 Lemma 15 is "Lemma 5".

## Setting

As in `LadderAnticommutation`: `H` is a `SimplicialModeHamiltonian`, `S : H.ModeSector` a mode
sector with sector polynomials `z_G = S.zG`, `z_K = S.zK`, `T(u) = T_G(u)` the transfer operator,
and `ψ_j^+ = A_{u_j}/N_j`, `ψ_j^- = A_{-u_j}/N_j` the normalised incognito modes of a
`Nondegenerate` sector.  `T'(u) = Σ_k k (-1)^k u^{k-1} Q_G^(k)` is the derivative of
`T(u) = Σ_k (-u)^k Q_G^(k)` with respect to `u` (`transferDeriv`); v1 writes
`∂T_G(u_j)/∂u_j` for `T'(u_j)` and `∂T_G(-u_j)/∂u_j` for `-T'(-u_j)`.

## Main declarations

* `PauliFrustrationRepresentation.transferDeriv` : `T'_{G∖W}(u) = Σ_k k (-1)^k u^{k-1} Q_{G∖W}^(k)`;
* `ModeSector.mode_commutator_mode_neg` : for a root `v ≠ 0` of `z_G(-v²)`,
  `[A_v, A_{-v}] = -8 v z_K(-v²) Π (T(-v) T'(v) + T(v) T'(-v))`;
* `ModeSector.Nondegenerate.commutator_plus_minus` :
  `[ψ_j^+, ψ_j^-] = -(2 u_j z_G'(-u_j²))⁻¹ Π (T(-u_j) T'(u_j) + T(u_j) T'(-u_j))`
  (v1 L2120-2121, with `∂_u[T(-u)] = -T'(-u)` made explicit).

## Deviations from v1

* v1 passes to the limit `u → u_j` of `((u_j + u)/(u_j - u)) T(u) [ψ_+, χ] T(-u)` informally
  (L2114-2115).  Here the limit is the exact derivative identity of an operator-valued
  polynomial in `u` (`Polynomial.eval_algebraMap_eq_neg_derivative_of_forall`, built on
  `Polynomial.eval_eq_neg_derivative_of_mul_eq` of `PolynomialHelpers`): the pointwise identity
  `(v - w) [A_v, A_{-w}] = (v + w) T(w) [A_v, χ] T(-w)` holds for all real `w`
  (`ModeSector.mode_commutator_mode_neg_arg`) and differentiation at `w = v` gives the result.
* v1 uses `T(u_j) ψ_+ = 0 = ψ_+ T(-u_j)` (to drop the term in which the derivative falls on the
  prefactor `(u_j + u)`, and to simplify `[ψ_+, χ] T(-u_j)`) without stating it; here it is
  `transfer_mul_mode_eq_zero` of `IncognitoModes`.
* v1's display L2120 has the prefactor `-8u/N²` and omits the factor `z_K(-u_j²)` coming from
  `{ψ_+, χ} = 4 Π z_K(-u_j²)/N` (L2093-2097; `mode_anticomm_root`); with that factor L2120 and
  L2121 agree.  Here `[A_v, A_{-v}] = -8 v z_K(-v²) Π (⋯)` keeps `z_K` explicit and the
  normalisation `N_j² = 16 u_j² z_K(-u_j²) z_G'(-u_j²)` produces `-(2 u_j z_G'(-u_j²))⁻¹`
  (v1 L2121).
* The commutation of `T(-u_j)` with `T'(u_j)` (used to bring v1's `T'(u_j) T(-u_j)` into the
  form `T(-u_j) T'(u_j)`) is Theorem 1(i) (`deletedCharge_commute`) and needs `hclaw`.
* The premises beyond the manuscript setup are those of `ModeSector.Nondegenerate`
  (real, positive, distinct roots; positive radicands), which v1 uses silently (see
  `LadderRelations`), together with `hclaw : G.IsClawFree` and `hKs : G.IsSimplicialClique Ks`.
  The unnormalised statement `mode_commutator_mode_neg` needs only `hclaw`, `hKs`, `v ≠ 0` and
  `z_G(-v²) = 0`.
-/

open scoped BigOperators

namespace Polynomial

variable {B : Type*} [Ring B] [Algebra ℝ B]

/-- **Exact form of the limit `u → v`, operator-valued version.**  If `F`, `G` are polynomials
with coefficients in an `ℝ`-algebra `B` and `(v - w) F(w) = G(w)` for all real `w` (evaluation at
the central points `algebraMap ℝ B w`), then `F(v) = -G'(v)`. -/
theorem eval_algebraMap_eq_neg_derivative_of_forall {F G : B[X]} (v : ℝ)
    (h : ∀ w : ℝ, (v - w) • F.eval (algebraMap ℝ B w) = G.eval (algebraMap ℝ B w)) :
    F.eval (algebraMap ℝ B v) = -(derivative G).eval (algebraMap ℝ B v) := by
  have hmain : (C (algebraMap ℝ B v) - X) * F = G := by
    rw [← sub_eq_zero]
    refine eq_zero_of_infinite_eval_algebraMap _ ?_
    have hall : {x : ℝ | ((C (algebraMap ℝ B v) - X) * F - G).eval (algebraMap ℝ B x) = 0} =
        Set.univ := by
      refine Set.eq_univ_of_forall (fun w => ?_)
      show ((C (algebraMap ℝ B v) - X) * F - G).eval (algebraMap ℝ B w) = 0
      have h1 := map_sub (evalCentralHom B w) ((C (algebraMap ℝ B v) - X) * F) G
      have h2 := map_mul (evalCentralHom B w) (C (algebraMap ℝ B v) - X) F
      have h3 := map_sub (evalCentralHom B w) (C (algebraMap ℝ B v)) X
      simp only [evalCentralHom_apply, eval_C, eval_X] at h1 h2 h3
      rw [h1, h2, h3, ← h w, ← map_sub, Algebra.smul_def, sub_self]
    rw [hall]
    exact Set.infinite_univ
  exact eval_eq_neg_derivative_of_mul_eq v F G hmain

/-- Evaluation at a central real point is multiplicative, also for noncommutative coefficients. -/
theorem evalCentral_mul (p q : B[X]) (w : ℝ) :
    (p * q).eval (algebraMap ℝ B w) = p.eval (algebraMap ℝ B w) * q.eval (algebraMap ℝ B w) :=
  map_mul (evalCentralHom B w) p q

/-- The limit `w → v` for a polynomial map: if `F : ℝ → B` is a polynomial map and
`(v - w) F(w) = G(w)` for all real `w`, with `G ∈ B[X]`, then `F(v) = -G'(v)`. -/
theorem IsPolyMap.apply_eq_neg_derivative_poly {F : ℝ → B} (hF : IsPolyMap F) (v : ℝ) (G : B[X])
    (h : ∀ w : ℝ, (v - w) • F w = G.eval (algebraMap ℝ B w)) :
    F v = -(derivative G).eval (algebraMap ℝ B v) := by
  obtain ⟨p, hp⟩ := hF
  rw [hp]
  exact eval_algebraMap_eq_neg_derivative_of_forall v (fun w => by rw [← hp w]; exact h w)

end Polynomial

universe u w

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V} {Ks : Set V} {A : Type w}

namespace PauliFrustrationRepresentation

variable [Ring A] [Algebra ℝ A] [Fintype V] [DecidableEq V]

/-- The derivative of the transfer operator, `T'_{G∖W}(u) = Σ_k k (-1)^k u^{k-1} Q_{G∖W}^(k)`
(`d/du` of `T_{G∖W}(u) = Σ_k (-u)^k Q_{G∖W}^(k)`).  v1 writes `∂T_G(u)/∂u` (Lemma 15, L2114-2121).
The `k = 0` term vanishes because of the factor `k`. -/
noncomputable def transferDeriv (H : G.PauliFrustrationRepresentation A) (W : Set V) (u : ℝ) :
    A :=
  ∑ k ∈ Finset.range (Fintype.card V + 1), ((k : ℝ) * (-1) ^ k * u ^ (k - 1)) •
    H.deletedCharge W k

/-- The polynomial `Σ_k (-1)^k Q^(k) X^k` with coefficients in `A`; its value at `w` is `T(w)`. -/
noncomputable def transferPoly (H : G.PauliFrustrationRepresentation A) (W : Set V) :
    Polynomial A :=
  ∑ k ∈ Finset.range (Fintype.card V + 1),
    Polynomial.monomial k (((-1 : ℝ) ^ k) • H.deletedCharge W k)

/-- The polynomial `Σ_k Q^(k) X^k` with coefficients in `A`; its value at `w` is `T(-w)`. -/
noncomputable def transferNegPoly (H : G.PauliFrustrationRepresentation A) (W : Set V) :
    Polynomial A :=
  ∑ k ∈ Finset.range (Fintype.card V + 1), Polynomial.monomial k (H.deletedCharge W k)

theorem eval_transferPoly (H : G.PauliFrustrationRepresentation A) (W : Set V) (w : ℝ) :
    (H.transferPoly W).eval (algebraMap ℝ A w) = H.transfer W w := by
  unfold transferPoly transfer
  rw [Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Polynomial.eval_monomial, ← map_pow, ← Algebra.commutes, ← Algebra.smul_def, smul_smul,
    ← mul_pow]
  congr 2
  ring

theorem eval_transferNegPoly (H : G.PauliFrustrationRepresentation A) (W : Set V) (w : ℝ) :
    (H.transferNegPoly W).eval (algebraMap ℝ A w) = H.transfer W (-w) := by
  unfold transferNegPoly transfer
  rw [Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Polynomial.eval_monomial, ← map_pow, ← Algebra.commutes, ← Algebra.smul_def, neg_neg]

theorem eval_derivative_transferPoly (H : G.PauliFrustrationRepresentation A) (W : Set V)
    (w : ℝ) :
    (Polynomial.derivative (H.transferPoly W)).eval (algebraMap ℝ A w) = H.transferDeriv W w := by
  unfold transferPoly transferDeriv
  rw [map_sum, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Polynomial.derivative_monomial, Polynomial.eval_monomial, ← map_pow, ← Algebra.commutes,
    ← Algebra.smul_def, ← nsmul_eq_mul', ← Nat.cast_smul_eq_nsmul ℝ]
  simp only [smul_smul]
  congr 1
  ring

theorem eval_derivative_transferNegPoly (H : G.PauliFrustrationRepresentation A) (W : Set V)
    (w : ℝ) :
    (Polynomial.derivative (H.transferNegPoly W)).eval (algebraMap ℝ A w) =
      -H.transferDeriv W (-w) := by
  unfold transferNegPoly transferDeriv
  rw [map_sum, Polynomial.eval_finsetSum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Polynomial.derivative_monomial, Polynomial.eval_monomial, ← map_pow, ← Algebra.commutes,
    ← Algebra.smul_def, ← nsmul_eq_mul', ← Nat.cast_smul_eq_nsmul ℝ, ← neg_smul]
  simp only [smul_smul]
  congr 1
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    simp only [Nat.succ_sub_one, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
    rcases Nat.even_or_odd m with he | ho
    · rw [he.neg_pow, he.add_one.neg_pow, one_pow]
      ring
    · rw [ho.neg_pow, ho.add_one.neg_pow, one_pow]
      ring

/-- An operator commuting with every deleted charge `Q_{G∖W}^(k)` commutes with `T'_{G∖W}(u)`. -/
theorem commute_transferDeriv_of_commute_deletedCharge (H : G.PauliFrustrationRepresentation A)
    (W : Set V) {x : A} (hx : ∀ k, Commute x (H.deletedCharge W k)) (u : ℝ) :
    Commute x (H.transferDeriv W u) := by
  unfold transferDeriv
  exact Commute.sum_right _ _ _ (fun k _ => (hx k).smul_right _)

/-- If the deleted charges `Q_{G∖W}^(k)` pairwise commute (Theorem 1(i); for a claw-free `G` this
is `deletedCharge_commute`), then `T'_{G∖W}(u)` commutes with `T_{G∖W}(u')`. -/
theorem transferDeriv_commute_transfer (H : G.PauliFrustrationRepresentation A) (W : Set V)
    (hc : ∀ s t, Commute (H.deletedCharge W s) (H.deletedCharge W t)) (u u' : ℝ) :
    Commute (H.transferDeriv W u) (H.transfer W u') := by
  unfold transferDeriv
  refine Commute.sum_left _ _ _ (fun k _ => ?_)
  exact (H.commute_transfer_of_commute_deletedCharge W (fun t => hc k t) u').smul_left _

end PauliFrustrationRepresentation

namespace SimplicialModeHamiltonian

variable [Ring A] [StarRing A] [Algebra ℝ A] [StarModule ℝ A]
variable [Fintype V] [DecidableEq V]

namespace ModeSector

variable {H : G.SimplicialModeHamiltonian Ks A}

/-- `Π` commutes with `T'(u)`: it commutes with every charge `Q_G^(k)`. -/
theorem Pi_comm_transferDeriv (S : H.ModeSector) (u : ℝ) :
    Commute S.Pi (H.frustration.transferDeriv ∅ u) :=
  H.frustration.commute_transferDeriv_of_commute_deletedCharge ∅
    (fun k => S.Pi_comm_charge k) u

/-- Pure algebra of the commutator of a mode with a second sandwich (the commutator analogue of
`anticomm_sandwich_algebra`).  Here `a = A_v`, `Tm = T(-w)`, `Tp = T(w)`, `P = Π`, and the
intertwining relations `(v - w) T(-w) a = (v + w) a T(-w)` and `(v + w) T(w) a = (v - w) a T(w)`
hold; the second sandwich is `Π T(w) χ T(-w) = A_{-w}`. -/
theorem commutator_sandwich_algebra {B : Type*} [Ring B] [Algebra ℝ B]
    (P Tm Tp χ a : B) (v w : ℝ)
    (hPp : P * Tp = Tp * P) (hPχ : P * χ = χ * P)
    (hPa : P * a = a) (haP : a * P = a)
    (h1 : (v - w) • (Tm * a) = (v + w) • (a * Tm))
    (h2 : (v + w) • (Tp * a) = (v - w) • (a * Tp)) :
    (v - w) • (a * (P * Tp * χ * Tm) - (P * Tp * χ * Tm) * a) =
      (v + w) • (Tp * (a * χ - χ * a) * Tm) := by
  have e1 : (v - w) • (a * (P * Tp * χ * Tm)) = (v + w) • (Tp * (a * χ) * Tm) := by
    have : a * (P * Tp * χ * Tm) = (a * Tp) * χ * Tm := by
      calc a * (P * Tp * χ * Tm) = (a * P) * Tp * χ * Tm := by simp only [mul_assoc]
        _ = (a * Tp) * χ * Tm := by rw [haP]
    rw [this, ← smul_mul_assoc, ← smul_mul_assoc, ← h2, smul_mul_assoc, smul_mul_assoc]
    simp only [mul_assoc]
  have e2 : (v - w) • ((P * Tp * χ * Tm) * a) = (v + w) • (Tp * (χ * a) * Tm) := by
    have : (P * Tp * χ * Tm) * a = (P * Tp * χ) * (Tm * a) := by simp only [mul_assoc]
    rw [this, ← mul_smul_comm, h1, mul_smul_comm]
    have : P * Tp * χ * (a * Tm) = Tp * (χ * a) * Tm := by
      calc P * Tp * χ * (a * Tm) = (P * Tp) * χ * a * Tm := by simp only [mul_assoc]
        _ = Tp * (P * χ) * a * Tm := by rw [hPp]; simp only [mul_assoc]
        _ = Tp * (χ * P) * a * Tm := by rw [hPχ]
        _ = Tp * χ * (P * a) * Tm := by simp only [mul_assoc]
        _ = Tp * (χ * a) * Tm := by rw [hPa]; simp only [mul_assoc]
    rw [this]
  rw [smul_sub, e1, e2, ← smul_sub]
  congr 1
  simp only [mul_sub, sub_mul]

/-- **Pointwise commutator identity** (v1 L2079-2083 and L2114, with the commutator in place of
the anticommutator): if `v ≠ 0` and `z_G(-v²) = 0`, then for every real `w`

`(v - w) [A_v, A_{-w}] = (v + w) T(w) [A_v, χ] T(-w)`,

where `A_{-w} = Π T(w) χ T(-w)` (`mode_neg_eq`).  It holds for all real `w`, including `w = ±v`,
and needs no inversion of `Z_G(-w²)`. -/
theorem mode_commutator_mode_neg_arg (S : H.ModeSector) (hclaw : G.IsClawFree)
    (hKs : G.IsSimplicialClique Ks) {v : ℝ} (hv : v ≠ 0)
    (hroot : S.zG.eval (-v ^ 2) = 0) (w : ℝ) :
    (v - w) • (S.mode v * S.mode (-w) - S.mode (-w) * S.mode v) =
      (v + w) • (H.frustration.transfer ∅ w * (S.mode v * H.root - H.root * S.mode v) *
        H.frustration.transfer ∅ (-w)) := by
  have h1 : (v - w) • (H.frustration.transfer ∅ (-w) * S.mode v) =
      (v + w) • (S.mode v * H.frustration.transfer ∅ (-w)) := by
    have h := S.intertwine hclaw hKs hv hroot (-w)
    rwa [← sub_eq_add_neg, sub_neg_eq_add] at h
  have h2 := S.intertwine hclaw hKs hv hroot w
  rw [S.mode_neg_eq w]
  exact commutator_sandwich_algebra S.Pi (H.frustration.transfer ∅ (-w))
    (H.frustration.transfer ∅ w) H.root (S.mode v) v w
    (S.Pi_comm_transfer w).eq S.Pi_comm_root.eq (S.Pi_mul_mode v).1 (S.Pi_mul_mode v).2 h1 h2

/-- Pure algebra of the derivative step.  Here `a = A_v`, `P = Π`, `Tp = T(v)`, `Tm = T(-v)`,
`Dp = T'(v)`, `Dm = T'(-v)`, `c = [a, χ]`, with `Tp a = 0`, `a Tm = 0` and
`{a, χ} = z Π`.  Then `Tp c Tm = 0`, `Dp c Tm = z Π Tm Dp` (`Π`, `Tm`, `Dp` commuting) and
`Tp c Dm = -z Π Tp Dm`. -/
theorem commutator_derivative_algebra {B : Type*} [Ring B] [Algebra ℝ B]
    (P Tm Tp Dp Dm χ a : B) (v z : ℝ)
    (hTa : Tp * a = 0) (haT : a * Tm = 0) (hanti : a * χ + χ * a = z • P)
    (hPDp : P * Dp = Dp * P) (hPTp : P * Tp = Tp * P) (hDT : Dp * Tm = Tm * Dp) :
    -(1 * (Tp * ((a * χ - χ * a) * Tm)) +
        (algebraMap ℝ B v + algebraMap ℝ B v) * (Dp * ((a * χ - χ * a) * Tm) +
          Tp * ((a * χ - χ * a) * -Dm))) =
      (-(2 * v * z)) • (P * (Tm * Dp + Tp * Dm)) := by
  have hc : a * χ = z • P - χ * a := eq_sub_of_add_eq hanti
  have c1 : Tp * ((a * χ - χ * a) * Tm) = 0 := by
    have : Tp * ((a * χ - χ * a) * Tm) = Tp * a * (χ * Tm) - Tp * χ * (a * Tm) := by
      simp only [mul_sub, sub_mul, mul_assoc]
    rw [this, hTa, haT, zero_mul, mul_zero, sub_zero]
  have c2 : Dp * ((a * χ - χ * a) * Tm) = z • (P * (Tm * Dp)) := by
    have : Dp * ((a * χ - χ * a) * Tm) = Dp * (a * χ) * Tm - Dp * χ * (a * Tm) := by
      simp only [mul_sub, sub_mul, mul_assoc]
    rw [this, haT, mul_zero, sub_zero, hc, mul_sub, sub_mul]
    have e : Dp * (χ * a) * Tm = Dp * χ * (a * Tm) := by simp only [mul_assoc]
    rw [e, haT, mul_zero, sub_zero, mul_smul_comm, smul_mul_assoc, ← hPDp, mul_assoc, hDT]
  have c3 : Tp * ((a * χ - χ * a) * Dm) = -(z • (P * (Tp * Dm))) := by
    have : Tp * ((a * χ - χ * a) * Dm) = Tp * a * (χ * Dm) - Tp * (χ * a) * Dm := by
      simp only [mul_sub, sub_mul, mul_assoc]
    have e : Tp * (χ * a) = z • (Tp * P) := by
      have h2 : χ * a = z • P - a * χ := eq_sub_of_add_eq' hanti
      rw [h2, mul_sub, mul_smul_comm]
      have : Tp * (a * χ) = Tp * a * χ := by simp only [mul_assoc]
      rw [this, hTa, zero_mul, sub_zero]
    rw [this, hTa, zero_mul, zero_sub, e, smul_mul_assoc, ← hPTp, mul_assoc]
  rw [c1, c2, mul_neg (a * χ - χ * a) Dm, mul_neg Tp, c3, neg_neg, mul_zero, zero_add,
    ← map_add, ← Algebra.smul_def, ← smul_add, ← mul_add, neg_smul, smul_smul]
  rw [show (v + v) * z = 2 * v * z by ring]

/-- `w ↦ [A_v, A_{-w}]` is a polynomial map. -/
theorem isPolyMap_commutator_mode_neg (S : H.ModeSector) (v : ℝ) :
    Polynomial.IsPolyMap (fun w : ℝ => S.mode v * S.mode (-w) - S.mode (-w) * S.mode v) := by
  obtain ⟨p, hp⟩ := S.isPolyMap_mode_neg
  refine ⟨Polynomial.C (S.mode v) * p - p * Polynomial.C (S.mode v), fun w => ?_⟩
  have h1 := map_sub (Polynomial.evalCentralHom A w) (Polynomial.C (S.mode v) * p)
    (p * Polynomial.C (S.mode v))
  have h2 := map_mul (Polynomial.evalCentralHom A w) (Polynomial.C (S.mode v)) p
  have h3 := map_mul (Polynomial.evalCentralHom A w) p (Polynomial.C (S.mode v))
  simp only [Polynomial.evalCentralHom_apply, Polynomial.eval_C] at h1 h2 h3
  rw [h1, h2, h3, ← hp]

/-- **Commutator of `A_v` and `A_{-v}`** (v1 Lemma 15, proof, L2112-2120, before the
normalisation of the modes): if `v ≠ 0` and `z_G(-v²) = 0` then

`[A_v, A_{-v}] = -8 v z_K(-v²) Π (T(-v) T'(v) + T(v) T'(-v))`,

with `T'(u) = Σ_k k (-1)^k u^{k-1} Q^(k)` (`transferDeriv`).

Proof.  `mode_commutator_mode_neg_arg` says `(v - w) F(w) = G(w)`, where
`F(w) = [A_v, A_{-w}]` and `G(w) = (v + w) T(w) [A_v, χ] T(-w)` are polynomials in `w` with
coefficients in the algebra; `Polynomial.eval_algebraMap_eq_neg_derivative_of_forall` (the exact
form of v1's limit `u → u_j`) gives `F(v) = -G'(v)`.  Differentiating,
`G'(v) = T(v) c T(-v) + 2v (T'(v) c T(-v) - T(v) c T'(-v))` with `c = [A_v, χ]`
(`∂_w T(-w) = -T'(-w)`).  The first term vanishes because `T(v) A_v = 0 = A_v T(-v)`
(`transfer_mul_mode_eq_zero`); with `{A_v, χ} = 4 z_K Π` (`mode_anticomm_root`) one finds
`T'(v) c T(-v) = 4 z_K Π T'(v) T(-v)` and `T(v) c T'(-v) = -4 z_K Π T(v) T'(-v)`, and finally
`T'(v) T(-v) = T(-v) T'(v)` by Theorem 1(i) (`deletedCharge_commute`). -/
theorem mode_commutator_mode_neg (S : H.ModeSector) (hclaw : G.IsClawFree)
    (hKs : G.IsSimplicialClique Ks) {v : ℝ} (hv : v ≠ 0)
    (hroot : S.zG.eval (-v ^ 2) = 0) :
    S.mode v * S.mode (-v) - S.mode (-v) * S.mode v =
      (-(8 * v * S.zK.eval (-v ^ 2))) • (S.Pi * (H.frustration.transfer ∅ (-v) *
        H.frustration.transferDeriv ∅ v +
        H.frustration.transfer ∅ v * H.frustration.transferDeriv ∅ (-v))) := by
  set c : A := S.mode v * H.root - H.root * S.mode v with hc
  set Gp : Polynomial A := (Polynomial.C (algebraMap ℝ A v) + Polynomial.X) *
    (H.frustration.transferPoly ∅ * (Polynomial.C c * H.frustration.transferNegPoly ∅)) with hGp
  have hGeval : ∀ w : ℝ, Gp.eval (algebraMap ℝ A w) =
      (v + w) • (H.frustration.transfer ∅ w * c * H.frustration.transfer ∅ (-w)) := by
    intro w
    simp only [hGp, Polynomial.evalCentral_mul, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_X, H.frustration.eval_transferPoly, H.frustration.eval_transferNegPoly]
    rw [← map_add, ← Algebra.smul_def, mul_assoc]
  have h := (S.isPolyMap_commutator_mode_neg v).apply_eq_neg_derivative_poly v Gp (fun w => by
    rw [hGeval]
    exact S.mode_commutator_mode_neg_arg hclaw hKs hv hroot w)
  rw [h]
  have hd : (Polynomial.derivative Gp).eval (algebraMap ℝ A v) =
      1 * (H.frustration.transfer ∅ v * (c * H.frustration.transfer ∅ (-v))) +
        (algebraMap ℝ A v + algebraMap ℝ A v) *
          (H.frustration.transferDeriv ∅ v * (c * H.frustration.transfer ∅ (-v)) +
            H.frustration.transfer ∅ v * (c * -H.frustration.transferDeriv ∅ (-v))) := by
    simp only [hGp, Polynomial.derivative_mul, Polynomial.derivative_add, Polynomial.derivative_C,
      Polynomial.derivative_X, zero_add, Polynomial.eval_add, Polynomial.evalCentral_mul,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, zero_mul,
      H.frustration.eval_transferPoly, H.frustration.eval_transferNegPoly,
      H.frustration.eval_derivative_transferPoly, H.frustration.eval_derivative_transferNegPoly]
  have key := commutator_derivative_algebra S.Pi (H.frustration.transfer ∅ (-v))
    (H.frustration.transfer ∅ v) (H.frustration.transferDeriv ∅ v)
    (H.frustration.transferDeriv ∅ (-v)) H.root (S.mode v) v (4 * S.zK.eval (-v ^ 2))
    (S.transfer_mul_mode_eq_zero hclaw hKs hv hroot).1
    (S.transfer_mul_mode_eq_zero hclaw hKs hv hroot).2
    (S.mode_anticomm_root hclaw hKs hroot) (S.Pi_comm_transferDeriv v).eq
    (S.Pi_comm_transfer v).eq
    (H.frustration.transferDeriv_commute_transfer ∅
      (fun s t => H.frustration.deletedCharge_commute hclaw ∅ s t) v (-v)).eq
  rw [hd, key]
  congr 2
  ring

namespace Nondegenerate

variable {S : H.ModeSector}

/-- **`[ψ_j^+, ψ_j^-] = -(2 u_j z_G'(-u_j²))⁻¹ Π (T(-u_j) T'(u_j) + T(u_j) T'(-u_j))`**
(v1 Lemma 15, `DiagonalRelation`, proof L2112-2121), within one sector.  In v1's notation
`T'(u_j) = ∂T_G(u_j)/∂u_j` and `T'(-u_j) = -∂T_G(-u_j)/∂u_j`, so the right-hand side is
`-(1/(2 u_j)) Π (∂Z_G/∂x|_{x=-u_j²})⁻¹ (T(-u_j) ∂T(u_j)/∂u_j - T(u_j) ∂T(-u_j)/∂u_j)` (L2121).

The proof is `mode_commutator_mode_neg`, `[A_v, A_{-v}] = -8 v z_K(-v²) Π (⋯)` (the exact
derivative form of v1's limit `u → u_j`), divided by `N_j² = 16 u_j² z_K(-u_j²) z_G'(-u_j²)`;
the radicand is positive, so `z_K(-u_j²) ≠ 0 ≠ z_G'(-u_j²)`.

The premises beyond the manuscript setup are the non-degeneracy data `D` (which v1 uses silently;
see `ModeSector.Nondegenerate`), `hclaw` and `hKs`. -/
theorem commutator_plus_minus (D : S.Nondegenerate) (hclaw : G.IsClawFree)
    (hKs : G.IsSimplicialClique Ks) (j : Fin D.r) :
    D.psiPlus j * D.psiMinus j - D.psiMinus j * D.psiPlus j =
      (-(2 * D.u j * (Polynomial.derivative S.zG).eval (-(D.u j) ^ 2))⁻¹) •
        (S.Pi * (H.frustration.transfer ∅ (-(D.u j)) * H.frustration.transferDeriv ∅ (D.u j) +
                 H.frustration.transfer ∅ (D.u j) *
                   H.frustration.transferDeriv ∅ (-(D.u j)))) := by
  unfold psiPlus psiMinus
  rw [smul_mul_smul_comm, smul_mul_smul_comm, ← smul_sub,
    S.mode_commutator_mode_neg hclaw hKs (D.u_pos j).ne' (D.zG_eval_root j), smul_smul]
  congr 1
  have hr := D.radicand_pos j
  have hK : S.zK.eval (-(D.u j) ^ 2) ≠ 0 := left_ne_zero_of_mul hr.ne'
  have hZ : (Polynomial.derivative S.zG).eval (-(D.u j) ^ 2) ≠ 0 := right_ne_zero_of_mul hr.ne'
  have hu := (D.u_pos j).ne'
  have hN := D.N_sq j
  have hN0 := D.N_ne_zero j
  have e : (D.N j)⁻¹ * (D.N j)⁻¹ = (16 * D.u j ^ 2 * (S.zK.eval (-(D.u j) ^ 2) *
      (Polynomial.derivative S.zG).eval (-(D.u j) ^ 2)))⁻¹ := by
    rw [← mul_inv, ← sq, hN]
  rw [e]
  field_simp
  ring

end Nondegenerate

end ModeSector

end SimplicialModeHamiltonian

end SimpleGraph
