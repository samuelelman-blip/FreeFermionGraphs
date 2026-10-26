import FreeFermionGraphs.LadderAnticommutation
import FreeFermionGraphs.JointSpectralProjections

/-!
# Matrix-algebra consequences of "no common root"

Manuscript (arXiv 2305.15625 v1), proof of Lemma 14 (`LadderAnticommutationRelations`,
L2085-2098, the normalisation `N_{J,j}` at L2097) and proof of Lemma 15 (`DiagonalRelation`,
L2123-2139): v1 uses without proof that the roots `u_{J,j}` of `Z_{G,J}(-u²)` are real, that
`Z_{G∖Ks,J}(-u²) Z_{G,J}'(-u²) > 0` (so that `N_{J,j}` is a positive real), and that `Z_{G,J}` has
`α(G)` distinct roots; cf. L604-608 for the literature on the `J`-free case.  In the numbering of
the revised manuscript used by the repository, v1 Lemmas 14 and 15 are "Lemma 4" and "Lemma 5".
None of these facts is proved in v1; this module proves them for matrix algebras from the single
hypothesis that `z_G` and `z_K` have no common root.

## Setting

`A = Matrix (Fin d) (Fin d) ℂ`, `H : G.SimplicialModeHamiltonian Ks A` and `S : H.ModeSector` with
sector polynomials `z_G = S.zG`, `z_K = S.zK` (v1's `Z_{G,J}` and `Z_{G∖Ks,J}`), `Π = S.Pi`.  The
frustration graph `G` is claw-free and `Ks` is a simplicial clique, as in v1's "SCF" setting.

## Main declarations

* `ModeSector.root_real_neg` : if `Π ≠ 0`, `x ∈ ℂ`, `z_G(x) = 0` and `z_K(x) ≠ 0`, then `x` is real
  and negative;
* `ModeSector.radicand_pos` : for a real such root, `z_K(x) z_G'(x) > 0`;
  `ModeSector.derivative_eval_ne_zero` and `ModeSector.aeval_derivative_ne_zero` record that such a
  root is simple (real and complex form);
* `ModeSector.charge_mul_Pi_eq_zero` : `Q_G^(k) Π = 0` for every `k > deg z_G`;
* `ModeSector.exists_nondegenerate_of_isCoprime` : if `z_G` and `z_K` are coprime in `ℝ[X]`
  (equivalently, by the Fundamental Theorem of Algebra, they have no common complex root), there
  is `Nondegenerate` data with `r = deg z_G`; `ModeSector.exists_nondegenerate_of_fta` is the same
  with the hypothesis "no common complex root" and the Fundamental Theorem of Algebra for `ℂ` as a
  hypothesis (see "Deviations");
* the supporting steps: `ModeSector.natDegree_eq_one_of_irreducible_dvd` (every irreducible
  factor of `z_G(-Y²)` is linear), `ModeSector.exists_real_root_of_dvd` and
  `ModeSector.card_roots_zG_eq_natDegree` (`z_G` splits over `ℝ`), and
  `ModeSector.exists_nondegenerate_of_splits` (assembly of the data from the splitting);
* the complex-parameter layer used for `root_real_neg`: `ModeSector.Z_scalar_complex`,
  `ModeSector.ZK_scalar_complex` (the fields `Z_scalar`, `ZK_scalar` extended from real to complex
  parameter), `ModeSector.modeC` (the mode `A_w = Π T(-w) χ T(w)` at complex `w`),
  `ModeSector.comm_modeC` (`[H, A_w] = (2/w) A_w`), `ModeSector.modeC_anticomm_root`
  (`{A_w, χ} = 4 z_K(-w²) Π`);
* the polynomial layer used for the splitting: `ModeSector.modePolynomial` (the mode as a polynomial
  in the spectral parameter with coefficients in `A`), `ModeSector.modePolynomial_comm`,
  `ModeSector.modePolynomial_anticomm`.

## Proof ideas

* *Reality (i).*  `z_G(0) = 1`, so a root is `x = -w²` with `w ≠ 0`.  The complex mode `A_w`
  satisfies `[H, A_w] = (2/w) A_w` and is nonzero because `{A_w, χ} = 4 z_K(x) Π ≠ 0`.  `H` is
  Hermitian, so `ad_H` is self-adjoint for the Hilbert-Schmidt form `tr (X† Y)` and its
  eigenvalue `2/w` is real.
* *Positivity (ii).*  For a real root `x = -v²` take the trace of
  `{A_v, A_{-v}} = 16 v² z_K z_G' Π` (`mode_anticomm_mode_neg`), using `A_{-v} = A_v†`: the left
  side is `2 ‖A_v‖²_HS > 0`, and `tr Π > 0`.  Simplicity follows from positivity.
* *Top charges (iii).*  Downward induction on `k`, from the coefficient of `u^{2k}` in
  `Π T(u) T(-u) = z_G(-u²) Π`, and `X† X = 0 ⟹ X = 0`.
* *Non-degeneracy data (iv).*  The real roots are simple, negative, and `z_G(0) = 1` gives the
  product form `z_G = ∏_j (1 + x/u_j²)`, `u_j = √(-x_j)`, once `z_G` is known to split over `ℝ`.
  The splitting is proved *without* the Fundamental Theorem of Algebra: the real identity
  `u [H, A_u] = 2 A_u - 2 z_G(-u²) Π (1 + uΣ) χ` is a polynomial identity in `u` with coefficients
  in `A`; projecting onto the spectral components `e_μ · e_ν` of the Hermitian matrix `H` it says
  `(2 - (μ - ν) u) 𝒜_{μν} = 2 ĝ ℬ_{μν}`, so an irreducible factor `P` of `z_G(-u²)` of degree at
  least `2` is coprime to the linear factor and divides every component of `A_u`.  Then
  `{A_u, χ} = (4 z_K - 2 z_G)(-u²) Π` makes `P` divide `4 z_K(-u²) Π`, and coprimality of `P` with
  `z_K(-u²)` makes `P` divide the nonzero constant `Π`, which is absurd.

## Deviations from the work package

* `charge_mul_Pi_eq_zero` holds without the hypotheses `hclaw` and `hPi` of the package statement:
  the commutation of `Π` with the charges and the scalar action `Z_scalar` are fields of
  `ModeSector`, and `Π = 0` makes the claim trivial.  It is stated without them (a stronger
  theorem).
* An extra hypothesis that the roots are simple is not needed: simplicity follows from
  `radicand_pos`, and no such hypothesis appears anywhere.
* `exists_nondegenerate` is stated with the hypothesis `IsCoprime S.zG S.zK`
  (`exists_nondegenerate_of_isCoprime`) instead of the package's "no common complex root".  For real
  polynomials the two are equivalent, but passing from "no common complex root" to coprimality needs
  the Fundamental Theorem of Algebra for `ℂ`: a nonconstant common factor must have a complex root.
  Mathlib proves it (`Complex.exists_root`), but that module lies in `Mathlib.Analysis`, whose
  import closure is not built here, so this module cannot import it.  The direction
  coprime ⟹ no common complex root is proved here (`aeval_ne_zero_of_isCoprime`); the other
  direction is `isCoprime_of_forall_aeval_ne_zero`, which takes the Fundamental Theorem of
  Algebra in Mathlib's own form `∀ f : ℂ[X], 0 < f.degree → ∃ z, f.IsRoot z` as a hypothesis,
  and `exists_nondegenerate_of_fta` is the package statement with that hypothesis.  A caller
  with `Mathlib.Analysis.Complex.Polynomial.Basic` imported passes
  `fun f hf => Complex.exists_root hf`.  The splitting of `z_G` over `ℝ` itself uses no
  algebraic closure.  Neither hypothesis is a claim from the manuscript; everything else in this
  module is unconditional.
* `Z_scalar` and `ZK_scalar` are real-parameter fields; the complex-parameter versions needed for
  `root_real_neg` are derived from them by the polynomial extension argument
  (`IsPolyMapC.eq_of_real`, from `Polynomial.eq_zero_of_infinite_eval_algebraMap`).
* This module is for matrix algebras `Matrix (Fin d) (Fin d) ℂ` only; it needs the trace form, and
  Mathlib's `Matrix.conjTranspose_mul_self_eq_zero` (module
  `Mathlib.LinearAlgebra.Matrix.DotProduct`) is not built here, so the Hilbert-Schmidt norm is
  developed locally (`hsNormSq`).
-/

open scoped BigOperators
open Matrix Polynomial

namespace ModeSectorPositivity

/-! ### Square roots in `ℂ` -/

/-- Every complex number is a square.  (Explicit formula; the Fundamental Theorem of Algebra is
not needed.) -/
theorem exists_sq_eq (z : ℂ) : ∃ w : ℂ, w ^ 2 = z := by
  have hr : 0 ≤ z.re ^ 2 + z.im ^ 2 := by positivity
  set r := Real.sqrt (z.re ^ 2 + z.im ^ 2) with hr_def
  have hr2 : r ^ 2 = z.re ^ 2 + z.im ^ 2 := Real.sq_sqrt hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hab : |z.re| ≤ r := Real.abs_le_sqrt (by nlinarith [sq_nonneg z.im])
  have hp : 0 ≤ (r + z.re) / 2 := by
    have := (abs_le.mp hab).1
    linarith
  have hm : 0 ≤ (r - z.re) / 2 := by
    have := (abs_le.mp hab).2
    linarith
  set x := Real.sqrt ((r + z.re) / 2) with hx
  set y := Real.sqrt ((r - z.re) / 2) with hy
  have hx2 : x ^ 2 = (r + z.re) / 2 := Real.sq_sqrt hp
  have hy2 : y ^ 2 = (r - z.re) / 2 := Real.sq_sqrt hm
  have hxy : x * y = |z.im| / 2 := by
    have h1 : x * y = Real.sqrt (((r + z.re) / 2) * ((r - z.re) / 2)) := (Real.sqrt_mul hp _).symm
    have h2 : ((r + z.re) / 2) * ((r - z.re) / 2) = (|z.im| / 2) ^ 2 := by
      have : (r + z.re) * (r - z.re) = z.im ^ 2 := by nlinarith
      rw [div_pow, sq_abs]
      nlinarith
    rw [h1, h2]
    exact Real.sqrt_sq (by positivity)
  refine ⟨⟨x, (if 0 ≤ z.im then 1 else -1) * y⟩, ?_⟩
  apply Complex.ext
  · simp only [pow_two, Complex.mul_re]
    have : ((if 0 ≤ z.im then (1:ℝ) else -1) * y) *
        ((if 0 ≤ z.im then (1:ℝ) else -1) * y) = y ^ 2 := by
      split_ifs <;> ring
    rw [this]
    nlinarith
  · simp only [pow_two, Complex.mul_im]
    split_ifs with h
    · rw [abs_of_nonneg h] at hxy
      nlinarith
    · have h := not_le.mp h
      rw [abs_of_neg h] at hxy
      nlinarith


/-! ### Real polynomials with real complex roots -/

section RealRoots

open Polynomial

/-- A real polynomial evaluated at a real point, viewed in `ℂ`. -/
theorem aeval_ofReal (p : Polynomial ℝ) (x : ℝ) :
    Polynomial.aeval (x : ℂ) p = ((p.eval x : ℝ) : ℂ) := by
  have : (x : ℂ) = algebraMap ℝ ℂ x := rfl
  rw [this, Polynomial.aeval_algebraMap_apply, Polynomial.coe_aeval_eq_eval]
  rfl

/-- A nonzero real polynomial all of whose nonconstant divisors have a real root has as many real
roots, counted with multiplicity, as its degree. -/
theorem card_roots_eq_natDegree_of_dvd_real_root :
    ∀ (n : ℕ) (p : Polynomial ℝ), p.natDegree = n → p ≠ 0 →
      (∀ q : Polynomial ℝ, q ∣ p → 0 < q.natDegree → ∃ a : ℝ, q.IsRoot a) →
      Multiset.card p.roots = p.natDegree := by
  intro n
  induction n with
  | zero =>
    intro p hn hp _
    obtain ⟨c, rfl⟩ := Polynomial.natDegree_eq_zero.mp hn
    simp
  | succ n ih =>
    intro p hn hp hreal
    obtain ⟨a, ha⟩ := hreal p (dvd_refl p) (by omega)
    have hfac : (X - C a) * (p /ₘ (X - C a)) = p := Polynomial.mul_divByMonic_eq_iff_isRoot.mpr ha
    set q := p /ₘ (X - C a) with hq
    have hq0 : q ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hfac
      exact hp hfac.symm
    have hXa : (X - C a : Polynomial ℝ) ≠ 0 := Polynomial.X_sub_C_ne_zero a
    have hqdeg : q.natDegree = n := by
      have := Polynomial.natDegree_mul hXa hq0
      rw [hfac, Polynomial.natDegree_X_sub_C] at this
      omega
    have hqp : q ∣ p := ⟨X - C a, by rw [← hfac, mul_comm]⟩
    have hih := ih q hqdeg hq0 (fun r hr hrdeg => hreal r (hr.trans hqp) hrdeg)
    have hroots : p.roots = {a} + q.roots := by
      conv_lhs => rw [← hfac]
      rw [Polynomial.roots_mul (by rw [hfac]; exact hp), Polynomial.roots_X_sub_C]
    rw [hroots, Multiset.card_add, hih, hn, hqdeg]
    simp
    omega


/-- Coprime real polynomials have no common complex root. -/
theorem aeval_ne_zero_of_isCoprime {p q : Polynomial ℝ} (h : IsCoprime p q) (x : ℂ)
    (hx : Polynomial.aeval x p = 0) : Polynomial.aeval x q ≠ 0 := by
  obtain ⟨a, b, hab⟩ := h
  have h1 := congrArg (Polynomial.aeval x) hab
  rw [map_add, map_mul, map_mul, hx, mul_zero, zero_add, map_one] at h1
  intro hq
  rw [hq, mul_zero] at h1
  exact zero_ne_one h1

/-- **Absence of common complex roots implies coprimality, given the Fundamental Theorem of
Algebra for `ℂ`** (in the form of Mathlib's `Complex.exists_root`).  Real polynomials without a
common complex root are coprime: a common prime factor is nonconstant, so has a complex root. -/
theorem isCoprime_of_forall_aeval_ne_zero
    (hFTA : ∀ f : Polynomial ℂ, 0 < f.degree → ∃ z : ℂ, f.IsRoot z) {p q : Polynomial ℝ}
    (hp : p ≠ 0) (h : ∀ x : ℂ, Polynomial.aeval x p = 0 → Polynomial.aeval x q ≠ 0) :
    IsCoprime p q := by
  refine isCoprime_of_prime_dvd (fun ⟨h1, _⟩ => hp h1) (fun z hz hzp hzq => ?_)
  have hzdeg : 0 < (z.map (algebraMap ℝ ℂ)).degree := by
    rw [Polynomial.degree_map]
    exact Polynomial.degree_pos_of_ne_zero_of_nonunit hz.ne_zero hz.not_unit
  obtain ⟨w, hw⟩ := hFTA _ hzdeg
  have hw' : Polynomial.aeval w z = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    exact hw
  exact h w (Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hzp hw')
    (Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hzq hw')

end RealRoots

/-! ### The Hilbert-Schmidt form on matrices -/

section HilbertSchmidt

variable {d : ℕ}

/-- The squared Hilbert-Schmidt norm `∑_{i,j} |X_{ij}|²` of a complex square matrix. -/
noncomputable def hsNormSq (X : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (X i j)

theorem hsNormSq_nonneg (X : Matrix (Fin d) (Fin d) ℂ) : 0 ≤ hsNormSq X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem hsNormSq_eq_zero_iff (X : Matrix (Fin d) (Fin d) ℂ) : hsNormSq X = 0 ↔ X = 0 := by
  constructor
  · intro h
    unfold hsNormSq at h
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (X i j))).1 h
    ext i j
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => Complex.normSq_nonneg (X i j))).1 (h1 i (Finset.mem_univ i)) j (Finset.mem_univ j)
    simpa using h2
  · rintro rfl
    simp [hsNormSq]

theorem hsNormSq_pos {X : Matrix (Fin d) (Fin d) ℂ} (hX : X ≠ 0) : 0 < hsNormSq X :=
  lt_of_le_of_ne (hsNormSq_nonneg X) fun h => hX ((hsNormSq_eq_zero_iff X).1 h.symm)

/-- `tr (X† X) = ∑_{i,j} |X_{ij}|²`. -/
theorem trace_conjTranspose_mul_self (X : Matrix (Fin d) (Fin d) ℂ) :
    (Xᴴ * X).trace = ((hsNormSq X : ℝ) : ℂ) := by
  unfold hsNormSq
  push_cast
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]
  rfl

/-- `X† X = 0` forces `X = 0`. -/
theorem eq_zero_of_conjTranspose_mul_self_eq_zero {X : Matrix (Fin d) (Fin d) ℂ}
    (h : Xᴴ * X = 0) : X = 0 := by
  have ht := trace_conjTranspose_mul_self X
  rw [h, Matrix.trace_zero] at ht
  exact (hsNormSq_eq_zero_iff X).1 (by exact_mod_cast ht.symm)

/-- If `H` is Hermitian and `[H, X] = λ X` for a nonzero matrix `X`, then `λ` is real.
(`ad_H` is self-adjoint for the Hilbert-Schmidt form `tr (X† Y)`.) -/
theorem im_eq_zero_of_commutator_eq_smul {Hm X : Matrix (Fin d) (Fin d) ℂ} (hH : Hm.IsHermitian)
    (hX : X ≠ 0) {lam : ℂ} (h : Hm * X - X * Hm = lam • X) : lam.im = 0 := by
  have ht : (Xᴴ * X).trace = ((hsNormSq X : ℝ) : ℂ) := trace_conjTranspose_mul_self X
  have hn : ((hsNormSq X : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (hsNormSq_pos hX).ne'
  have e1 : (Xᴴ * (Hm * X - X * Hm)).trace = lam * ((hsNormSq X : ℝ) : ℂ) := by
    rw [h, Matrix.mul_smul, Matrix.trace_smul, ht, smul_eq_mul]
  have e2 : ((Hm * X - X * Hm)ᴴ * X).trace = star lam * ((hsNormSq X : ℝ) : ℂ) := by
    rw [h, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.trace_smul, ht, smul_eq_mul]
  have e3 : ((Hm * X - X * Hm)ᴴ * X).trace = (Xᴴ * (Hm * X - X * Hm)).trace := by
    have hHc : Hmᴴ = Hm := hH
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hHc]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub, Matrix.mul_assoc]
    congr 1
    rw [Matrix.trace_mul_comm Hm (Xᴴ * X), Matrix.mul_assoc]
  have e4 : star lam * ((hsNormSq X : ℝ) : ℂ) = lam * ((hsNormSq X : ℝ) : ℂ) := by
    rw [← e2, e3, e1]
  have e5 : star lam = lam := mul_right_cancel₀ hn e4
  have := congrArg Complex.im e5
  simp at this
  linarith

end HilbertSchmidt

/-! ### Polynomial maps `ℂ → B` -/

section PolyMap

open Polynomial

variable {B : Type*} [Ring B] [Algebra ℂ B]

/-- Evaluation of a polynomial over a (possibly noncommutative) `ℂ`-algebra `B` at the central
complex point `algebraMap ℂ B w`, as a ring homomorphism. -/
noncomputable def evalCentralHomC (B : Type*) [Ring B] [Algebra ℂ B] (w : ℂ) : B[X] →+* B :=
  eval₂RingHom' (RingHom.id B) (algebraMap ℂ B w) (fun a => (Algebra.commutes w a).symm)

theorem evalCentralHomC_apply (w : ℂ) (p : B[X]) :
    evalCentralHomC B w p = p.eval (algebraMap ℂ B w) := rfl

/-- A map `F : ℂ → B` is a *polynomial map* if it is `w ↦ p(w)` for a polynomial `p` with
coefficients in `B`, evaluated at the central complex points `algebraMap ℂ B w`. -/
def IsPolyMapC (F : ℂ → B) : Prop :=
  ∃ p : B[X], ∀ w, F w = p.eval (algebraMap ℂ B w)

theorem IsPolyMapC.const (b : B) : IsPolyMapC (fun _ : ℂ => b) :=
  ⟨C b, fun _ => (eval_C).symm⟩

theorem IsPolyMapC.add {F G : ℂ → B} (hF : IsPolyMapC F) (hG : IsPolyMapC G) :
    IsPolyMapC (fun w => F w + G w) := by
  obtain ⟨p, hp⟩ := hF
  obtain ⟨q, hq⟩ := hG
  exact ⟨p + q, fun w => by simp only [eval_add, hp, hq]⟩

theorem IsPolyMapC.mul {F G : ℂ → B} (hF : IsPolyMapC F) (hG : IsPolyMapC G) :
    IsPolyMapC (fun w => F w * G w) := by
  obtain ⟨p, hp⟩ := hF
  obtain ⟨q, hq⟩ := hG
  refine ⟨p * q, fun w => ?_⟩
  have := map_mul (evalCentralHomC B w) p q
  simp only [evalCentralHomC_apply] at this
  simp only [this, hp, hq]

/-- `w ↦ f(w) • b` is a polynomial map for a complex polynomial `f` and `b ∈ B`. -/
theorem IsPolyMapC.smul_const (f : ℂ[X]) (b : B) :
    IsPolyMapC (fun w : ℂ => f.eval w • b) := by
  refine ⟨C b * f.map (algebraMap ℂ B), fun w => ?_⟩
  show f.eval w • b = _
  rw [eval_C_mul, eval_map, ← aeval_def, aeval_algebraMap_apply_eq_algebraMap_eval,
    Algebra.smul_def, ← Algebra.commutes]

/-- `w ↦ ∑_{k<n} w^k • a_k` is a polynomial map. -/
theorem isPolyMapC_sum_smul_pow (a : ℕ → B) (n : ℕ) :
    IsPolyMapC (fun w : ℂ => ∑ k ∈ Finset.range n, w ^ k • a k) := by
  refine ⟨∑ k ∈ Finset.range n, C (a k) * X ^ k, fun w => ?_⟩
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have := map_mul (evalCentralHomC B w) (C (a k)) (X ^ k)
  simp only [evalCentralHomC_apply] at this
  rw [this, eval_C]
  have h2 := map_pow (evalCentralHomC B w) X k
  simp only [evalCentralHomC_apply, eval_X] at h2
  rw [h2, ← map_pow, ← Algebra.commutes, ← Algebra.smul_def]

/-- Two polynomial maps `ℂ → B` that agree at all real points agree everywhere (a polynomial with
coefficients in an `ℝ`-algebra that vanishes at all real central points is zero). -/
theorem IsPolyMapC.eq_of_real [Algebra ℝ B] [IsScalarTower ℝ ℂ B] {F G : ℂ → B}
    (hF : IsPolyMapC F) (hG : IsPolyMapC G) (h : ∀ x : ℝ, F x = G x) (w : ℂ) : F w = G w := by
  obtain ⟨p, hp⟩ := hF
  obtain ⟨q, hq⟩ := hG
  have hpq : p - q = 0 := by
    refine Polynomial.eq_zero_of_infinite_eval_algebraMap _ ?_
    have hall : {x : ℝ | (p - q).eval (algebraMap ℝ B x) = 0} = Set.univ := by
      refine Set.eq_univ_of_forall (fun x => ?_)
      show (p - q).eval (algebraMap ℝ B x) = 0
      have e : algebraMap ℝ B x = algebraMap ℂ B (x : ℂ) := by
        rw [IsScalarTower.algebraMap_apply ℝ ℂ B x]
        rfl
      have h1 := map_sub (evalCentralHomC B (x : ℂ)) p q
      simp only [evalCentralHomC_apply] at h1
      rw [e, h1, ← hp, ← hq, h x, sub_self]
    rw [hall]
    exact Set.infinite_univ
  have h1 := map_sub (evalCentralHomC B w) p q
  simp only [evalCentralHomC_apply] at h1
  rw [hpq, eval_zero] at h1
  rw [hp, hq]
  exact (sub_eq_zero.mp h1.symm)

end PolyMap

/-! ### Real polynomials acting on `B[X]`: Bezout and degree arguments -/

section RealPolyScalars

open Polynomial

variable {B : Type*} [Ring B] [Algebra ℝ B]

/-- A constant polynomial with scalar coefficient `algebraMap ℝ B r` is central in `B[X]`. -/
theorem commute_C_algebraMap (r : ℝ) (𝒳 : B[X]) : Commute (C (algebraMap ℝ B r)) 𝒳 := by
  have h := Algebra.commutes r 𝒳
  rw [Polynomial.algebraMap_apply] at h
  exact h

/-- The image of a real polynomial in `B[X]` is central. -/
theorem commute_map_algebraMap (f : ℝ[X]) (𝒳 : B[X]) :
    Commute (f.map (algebraMap ℝ B)) 𝒳 := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.map_add]; exact hp.add_left hq
  | monomial n r =>
    rw [Polynomial.map_monomial, ← Polynomial.C_mul_X_pow_eq_monomial]
    exact Commute.mul_left (commute_C_algebraMap r 𝒳) ((Polynomial.commute_X 𝒳).pow_left n)

theorem eval_mul_real (p q : B[X]) (u : ℝ) :
    (p * q).eval (algebraMap ℝ B u) = p.eval (algebraMap ℝ B u) * q.eval (algebraMap ℝ B u) := by
  have := map_mul (Polynomial.evalCentralHom B u) p q
  simpa [Polynomial.evalCentralHom_apply] using this

theorem eval_map_real (f : ℝ[X]) (u : ℝ) :
    (f.map (algebraMap ℝ B)).eval (algebraMap ℝ B u) = algebraMap ℝ B (f.eval u) := by
  rw [Polynomial.eval_map_algebraMap, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]

/-- **Bezout step.**  If `P` is coprime to `L` and divides `g`, and `L 𝒳 = g 𝒞` in `B[X]` (the real
polynomials acting by multiplication through `algebraMap ℝ B`), then `P` divides `𝒳`. -/
theorem exists_eq_map_mul_of_isCoprime {P L g : ℝ[X]} (hPL : IsCoprime P L) (hPg : P ∣ g)
    {𝒳 𝒞 : B[X]}
    (h : L.map (algebraMap ℝ B) * 𝒳 = g.map (algebraMap ℝ B) * 𝒞) :
    ∃ 𝒳' : B[X], 𝒳 = P.map (algebraMap ℝ B) * 𝒳' := by
  obtain ⟨a, b, hab⟩ := hPL
  obtain ⟨g', rfl⟩ := hPg
  refine ⟨a.map (algebraMap ℝ B) * 𝒳 + b.map (algebraMap ℝ B) * (g'.map (algebraMap ℝ B) * 𝒞), ?_⟩
  have h1 : (a * P + b * L).map (algebraMap ℝ B) = 1 := by rw [hab, Polynomial.map_one]
  rw [Polynomial.map_mul] at h
  calc 𝒳 = (a * P + b * L).map (algebraMap ℝ B) * 𝒳 := by rw [h1, one_mul]
    _ = a.map (algebraMap ℝ B) * (P.map (algebraMap ℝ B) * 𝒳) +
        b.map (algebraMap ℝ B) * (L.map (algebraMap ℝ B) * 𝒳) := by
      rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, add_mul, mul_assoc,
        mul_assoc]
    _ = a.map (algebraMap ℝ B) * (P.map (algebraMap ℝ B) * 𝒳) +
        b.map (algebraMap ℝ B) * (P.map (algebraMap ℝ B) *
          (g'.map (algebraMap ℝ B) * 𝒞)) := by rw [h, mul_assoc]
    _ = P.map (algebraMap ℝ B) * (a.map (algebraMap ℝ B) * 𝒳 +
        b.map (algebraMap ℝ B) * (g'.map (algebraMap ℝ B) * 𝒞)) := by
      rw [mul_add, ← mul_assoc, ← mul_assoc, (commute_map_algebraMap a (P.map (algebraMap ℝ B))).eq,
        ← mul_assoc (P.map (algebraMap ℝ B)), ← mul_assoc (P.map (algebraMap ℝ B)),
        ← (commute_map_algebraMap b (P.map (algebraMap ℝ B))).eq]


/-- **Degree step.**  A nonzero constant polynomial `C c` is not divisible by a nonconstant real
polynomial `P` (acting through `algebraMap ℝ B`) in `B[X]`, when `B` has no `ℝ`-torsion. -/
theorem not_exists_C_eq_map_mul [NoZeroSMulDivisors ℝ B] {P : ℝ[X]} (hP : 0 < P.natDegree) {c : B}
    (hc : c ≠ 0) : ¬ ∃ 𝒵 : B[X], C c = P.map (algebraMap ℝ B) * 𝒵 := by
  rintro ⟨𝒵, h⟩
  haveI : Nontrivial B := ⟨⟨c, 0, hc⟩⟩
  have hP0 : P ≠ 0 := by rintro rfl; simp at hP
  have hlc : algebraMap ℝ B P.leadingCoeff ≠ 0 := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact smul_ne_zero (leadingCoeff_ne_zero.mpr hP0) one_ne_zero
  have hZ0 : 𝒵 ≠ 0 := by
    rintro rfl
    rw [mul_zero] at h
    exact hc (C_eq_zero.mp h)
  have hdeg : (P.map (algebraMap ℝ B)).natDegree = P.natDegree :=
    natDegree_map_of_leadingCoeff_ne_zero _ hlc
  have key := coeff_mul_degree_add_degree (P.map (algebraMap ℝ B)) 𝒵
  rw [← h, hdeg, leadingCoeff_map_of_leadingCoeff_ne_zero _ hlc, coeff_C] at key
  rw [if_neg (by omega)] at key
  have : algebraMap ℝ B P.leadingCoeff * 𝒵.leadingCoeff ≠ 0 := by
    rw [← Algebra.smul_def]
    exact smul_ne_zero (leadingCoeff_ne_zero.mpr hP0) (leadingCoeff_ne_zero.mpr hZ0)
  exact this key.symm

/-- **Projection of a commutator identity onto a pair of spectral components.**  In a ring `R`,
let `x, γ, mμ, mν` be central, and suppose `x [Ĥ, 𝒜] = 2 𝒜 - 2 γ ℬ`, `eμ Ĥ = mμ eμ` and
`Ĥ eν = mν eν`.  Then `(2 - (mμ - mν) x) (eμ 𝒜 eν) = 2 γ (eμ ℬ eν)`. -/
theorem project_commutator_identity {R : Type*} [Ring R] {x γ mμ mν Ĥ eμ eν 𝒜 ℬ : R}
    (hx : ∀ r : R, Commute x r) (hγ : ∀ r : R, Commute γ r) (hμ : ∀ r : R, Commute mμ r)
    (hν : ∀ r : R, Commute mν r)
    (h : x * (Ĥ * 𝒜 - 𝒜 * Ĥ) = 2 * 𝒜 - 2 * (γ * ℬ))
    (heμ : eμ * Ĥ = mμ * eμ) (heν : Ĥ * eν = mν * eν) :
    (2 - (mμ - mν) * x) * (eμ * 𝒜 * eν) = 2 * (γ * (eμ * ℬ * eν)) := by
  have h2 : (2 : R) = ((2 : ℕ) : R) := by norm_num
  have c2 : ∀ r : R, (2 : R) * r = r * 2 := fun r => by
    rw [h2]; exact (Nat.cast_commute 2 r).eq
  have cx : ∀ r : R, x * r = r * x := fun r => (hx r).eq
  have cγ : ∀ r : R, γ * r = r * γ := fun r => (hγ r).eq
  have cμ : ∀ r : R, mμ * r = r * mμ := fun r => (hμ r).eq
  have cν : ∀ r : R, mν * r = r * mν := fun r => (hν r).eq
  have h3 := congrArg (fun y => eμ * y * eν) h
  have l1 : eμ * (x * (Ĥ * 𝒜 - 𝒜 * Ĥ)) * eν = x * (mμ * (eμ * 𝒜 * eν) - mν * (eμ * 𝒜 * eν)) := by
    have a1 : eμ * (x * (Ĥ * 𝒜 - 𝒜 * Ĥ)) * eν = x * (eμ * (Ĥ * 𝒜 - 𝒜 * Ĥ) * eν) := by
      rw [← mul_assoc eμ, ← cx eμ, mul_assoc x, mul_assoc x]
    have a2 : eμ * (Ĥ * 𝒜 - 𝒜 * Ĥ) * eν = mμ * (eμ * 𝒜 * eν) - mν * (eμ * 𝒜 * eν) := by
      rw [mul_sub, sub_mul]
      have b1 : eμ * (Ĥ * 𝒜) * eν = mμ * (eμ * 𝒜 * eν) := by
        rw [← mul_assoc eμ, heμ, mul_assoc mμ, mul_assoc mμ]
      have b2 : eμ * (𝒜 * Ĥ) * eν = mν * (eμ * 𝒜 * eν) := by
        calc eμ * (𝒜 * Ĥ) * eν = eμ * 𝒜 * (Ĥ * eν) := by simp only [mul_assoc]
          _ = eμ * 𝒜 * (mν * eν) := by rw [heν]
          _ = mν * (eμ * 𝒜 * eν) := by rw [← mul_assoc, ← cν (eμ * 𝒜), mul_assoc]
      rw [b1, b2]
    rw [a1, a2]
  have r1 : eμ * (2 * 𝒜 - 2 * (γ * ℬ)) * eν = 2 * (eμ * 𝒜 * eν) - 2 * (γ * (eμ * ℬ * eν)) := by
    have d1 : eμ * (2 * 𝒜) * eν = 2 * (eμ * 𝒜 * eν) := by
      calc eμ * (2 * 𝒜) * eν = (eμ * 2) * 𝒜 * eν := by simp only [mul_assoc]
        _ = (2 * eμ) * 𝒜 * eν := by rw [← c2 eμ]
        _ = 2 * (eμ * 𝒜 * eν) := by simp only [mul_assoc]
    have d2 : eμ * (2 * (γ * ℬ)) * eν = 2 * (γ * (eμ * ℬ * eν)) := by
      calc eμ * (2 * (γ * ℬ)) * eν = (eμ * 2) * γ * ℬ * eν := by simp only [mul_assoc]
        _ = (2 * eμ) * γ * ℬ * eν := by rw [← c2 eμ]
        _ = 2 * ((eμ * γ) * ℬ * eν) := by simp only [mul_assoc]
        _ = 2 * ((γ * eμ) * ℬ * eν) := by rw [← cγ eμ]
        _ = 2 * (γ * (eμ * ℬ * eν)) := by simp only [mul_assoc]
    rw [mul_sub, sub_mul, d1, d2]
  have key : x * (mμ * (eμ * 𝒜 * eν) - mν * (eμ * 𝒜 * eν)) =
      2 * (eμ * 𝒜 * eν) - 2 * (γ * (eμ * ℬ * eν)) := by
    rw [← l1, h3, r1]
  have e1 : (mμ - mν) * x * (eμ * 𝒜 * eν) = x * (mμ * (eμ * 𝒜 * eν) - mν * (eμ * 𝒜 * eν)) := by
    rw [← sub_mul, ← cx (mμ - mν), mul_assoc]
  rw [sub_mul, e1, key]
  abel


end RealPolyScalars

/-! ### Coefficients and values of `∑ C (a k) X^k` -/

section SumHelpers

open Polynomial
variable {B : Type*} [Ring B]

theorem coeff_sum_C_mul_X_pow (a : ℕ → B) (n i : ℕ) :
    (∑ k ∈ Finset.range n, C (a k) * X ^ k).coeff i = if i < n then a i else 0 := by
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

theorem eval_sum_C_mul_X_pow [Algebra ℝ B] (a : ℕ → B) (n : ℕ) (u : ℝ) :
    (∑ k ∈ Finset.range n, C (a k) * X ^ k).eval (algebraMap ℝ B u) =
      ∑ k ∈ Finset.range n, u ^ k • a k := by
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have := map_mul (Polynomial.evalCentralHom B u) (C (a k)) (X ^ k)
  simp only [Polynomial.evalCentralHom_apply] at this
  rw [this, eval_C]
  have h2 := map_pow (Polynomial.evalCentralHom B u) X k
  simp only [Polynomial.evalCentralHom_apply, eval_X] at h2
  rw [h2, ← map_pow, ← Algebra.commutes, ← Algebra.smul_def]

end SumHelpers

end ModeSectorPositivity

universe u w
variable {V : Type u}

namespace SimpleGraph

namespace PauliFrustrationRepresentation

variable {G : SimpleGraph V} {A : Type w} [Ring A] [Algebra ℂ A]
variable [Fintype V] [DecidableEq V]

open ModeSectorPositivity

/-- `w ↦ T(w)` is a polynomial map `ℂ → A` (`T(w) = ∑_{k ≤ |V|} (-w)^k Q^(k)`). -/
theorem isPolyMapC_transfer (H : G.PauliFrustrationRepresentation A) (W : Set V) :
    IsPolyMapC (fun w : ℂ => H.transfer W w) := by
  have h := isPolyMapC_sum_smul_pow (fun k => ((-1 : ℂ) ^ k) • H.deletedCharge W k)
    (Fintype.card V + 1)
  have e : (fun w : ℂ => H.transfer W w) = fun w : ℂ => ∑ k ∈ Finset.range (Fintype.card V + 1),
      w ^ k • (((-1 : ℂ) ^ k) • H.deletedCharge W k) := by
    funext w
    unfold transfer
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [smul_smul, neg_pow, mul_comm]
  rw [e]
  exact h

/-- `w ↦ T(-w)` is a polynomial map `ℂ → A`. -/
theorem isPolyMapC_transfer_neg (H : G.PauliFrustrationRepresentation A) (W : Set V) :
    IsPolyMapC (fun w : ℂ => H.transfer W (-w)) := by
  have h := isPolyMapC_sum_smul_pow (fun k => H.deletedCharge W k) (Fintype.card V + 1)
  have e : (fun w : ℂ => H.transfer W (-w)) = fun w : ℂ => ∑ k ∈ Finset.range (Fintype.card V + 1),
      w ^ k • H.deletedCharge W k := by
    funext w
    unfold transfer
    simp only [neg_neg]
  rw [e]
  exact h

/-- For real `x`, the transfer operator with complex parameter `(x : ℂ)` is the transfer operator
with real parameter `x`. -/
theorem transfer_ofReal [Algebra ℝ A] [IsScalarTower ℝ ℂ A] (H : G.PauliFrustrationRepresentation A)
    (W : Set V) (x : ℝ) :
    H.transfer W (x : ℂ) = H.transfer W x := by
  unfold transfer
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have : (-(x : ℂ)) ^ k = algebraMap ℝ ℂ ((-x) ^ k) := by simp
  rw [this]
  exact IsScalarTower.algebraMap_smul ℂ _ _

/-- **A scalar action of `T_{G∖W}(w) T_{G∖W}(-w)` on `P` extends from real to complex `w`.**
If `P · T(x) T(-x) = z(-x²) · P` for all real `x` (`z` a real polynomial), then
`P · T(w) T(-w) = z(-w²) · P` for all complex `w`: both sides are polynomials in `w` with
coefficients in `A`, so equality at all real points forces equality everywhere. -/
theorem mul_transfer_mul_transfer_neg_complex [Algebra ℝ A] [IsScalarTower ℝ ℂ A]
    (H : G.PauliFrustrationRepresentation A) (W : Set V) (P : A) (z : Polynomial ℝ)
    (hreal : ∀ x : ℝ, P * (H.transfer W x * H.transfer W (-x)) = z.eval (-x ^ 2) • P) (w : ℂ) :
    P * (H.transfer W w * H.transfer W (-w)) = Polynomial.aeval (-w ^ 2) z • P := by
  have hF : IsPolyMapC (fun w : ℂ => P * (H.transfer W w * H.transfer W (-w))) :=
    (IsPolyMapC.const P).mul ((H.isPolyMapC_transfer W).mul (H.isPolyMapC_transfer_neg W))
  have hG : IsPolyMapC (fun w : ℂ => Polynomial.aeval (-w ^ 2) z • P) := by
    have h := IsPolyMapC.smul_const ((z.map (algebraMap ℝ ℂ)).comp (-(Polynomial.X ^ 2))) P
    refine (funext fun w => ?_ : (fun w : ℂ => Polynomial.aeval (-w ^ 2) z • P) =
      fun w : ℂ => ((z.map (algebraMap ℝ ℂ)).comp (-(Polynomial.X ^ 2))).eval w • P) ▸ h
    simp only [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_map, Polynomial.aeval_def]
  refine hF.eq_of_real hG (fun x => ?_) w
  show P * (H.transfer W (x : ℂ) * H.transfer W (-(x : ℂ))) =
    Polynomial.aeval (-(x : ℂ) ^ 2) z • P
  have e1 : H.transfer W (x : ℂ) = H.transfer W x := H.transfer_ofReal W x
  have e2 : H.transfer W (-(x : ℂ)) = H.transfer W (-x) := by
    rw [← Complex.ofReal_neg]
    exact H.transfer_ofReal W (-x)
  have e3 : Polynomial.aeval (-(x : ℂ) ^ 2) z = ((z.eval (-x ^ 2) : ℝ) : ℂ) := by
    have : (-(x : ℂ) ^ 2) = algebraMap ℝ ℂ (-x ^ 2) := by simp
    rw [this, Polynomial.aeval_algebraMap_apply, Polynomial.coe_aeval_eq_eval]
    rfl
  rw [e1, e2, e3]
  have e4 : (((z.eval (-x ^ 2) : ℝ) : ℂ)) • P = z.eval (-x ^ 2) • P :=
    IsScalarTower.algebraMap_smul (M := A) ℂ (z.eval (-x ^ 2)) P
  rw [e4]
  exact hreal x

end PauliFrustrationRepresentation

namespace SimplicialModeHamiltonian

variable {G : SimpleGraph V} {Ks : Set V} {A : Type w}
variable [Ring A] [StarRing A] [Algebra ℝ A] [StarModule ℝ A] [Algebra ℂ A]
variable [Fintype V] [DecidableEq V]

/-- The Hamiltonian commutes with the transfer operator at any complex parameter. -/
theorem hamiltonian_commute_transferC (H : G.SimplicialModeHamiltonian Ks A)
    (hclaw : G.IsClawFree) (w : ℂ) :
    Commute H.frustration.hamiltonian (H.frustration.transfer ∅ w) :=
  H.frustration.commute_transfer_of_commute_deletedCharge ∅
    (fun k => H.frustration.hamiltonian_commute_charge hclaw k) w

/-- The reduced Fundamental Identity at a complex parameter:
`(1 - wΣ) χ T(w) = T(w) (1 + wΣ) χ`. -/
theorem fundamentalIdentity_reduced_negC (H : G.SimplicialModeHamiltonian Ks A)
    (hKs : G.IsSimplicialClique Ks) (w : ℂ) :
    (1 - w • ∑ j ∈ verticesOfSet Ks, H.frustration.term j) * H.root *
        H.frustration.transfer ∅ w =
      H.frustration.transfer ∅ w *
        ((1 + w • ∑ j ∈ verticesOfSet Ks, H.frustration.term j) * H.root) := by
  have h := H.operator.fundamentalIdentity_reduced hKs (-w)
  simp only [neg_neg, neg_smul, ← sub_eq_add_neg, sub_neg_eq_add] at h
  exact h


namespace ModeSector

variable {H : G.SimplicialModeHamiltonian Ks A}

/-- `Π` commutes with the transfer operator at any parameter in any commutative ring. -/
theorem Pi_comm_transferC (S : H.ModeSector) (w : ℂ) :
    Commute S.Pi (H.frustration.transfer ∅ w) :=
  H.frustration.commute_transfer_of_commute_deletedCharge ∅ (fun k => S.Pi_comm_charge k) w


end ModeSector

end SimplicialModeHamiltonian

namespace SimplicialModeHamiltonian

variable {G : SimpleGraph V} {Ks : Set V} {A : Type w}
variable [Ring A] [StarRing A] [Algebra ℝ A] [StarModule ℝ A] [Algebra ℂ A] [IsScalarTower ℝ ℂ A]
variable [Fintype V] [DecidableEq V]

namespace ModeSector

variable {H : G.SimplicialModeHamiltonian Ks A}

/-- **`Z_scalar` for complex `w`.**  `Π T(w) T(-w) = z_G(-w²) Π` for every complex `w`, where
`z_G` is evaluated at the complex point `-w²`.  The defining field `Z_scalar` is stated for real
arguments only; both sides are polynomials in `w` with coefficients in `A`, so the identity
extends to all complex `w`. -/
theorem Z_scalar_complex (S : H.ModeSector) (w : ℂ) :
    S.Pi * (H.frustration.transfer ∅ w * H.frustration.transfer ∅ (-w)) =
      Polynomial.aeval (-w ^ 2) S.zG • S.Pi :=
  H.frustration.mul_transfer_mul_transfer_neg_complex ∅ S.Pi S.zG S.Z_scalar w

/-- **`ZK_scalar` for complex `w`.**  `Π T_{G∖Ks}(w) T_{G∖Ks}(-w) = z_K(-w²) Π` for every complex
`w`. -/
theorem ZK_scalar_complex (S : H.ModeSector) (w : ℂ) :
    S.Pi * (H.frustration.transfer Ks w * H.frustration.transfer Ks (-w)) =
      Polynomial.aeval (-w ^ 2) S.zK • S.Pi :=
  H.frustration.mul_transfer_mul_transfer_neg_complex Ks S.Pi S.zK S.ZK_scalar w

/-! ### Modes at complex parameter -/

/-- The unnormalised incognito mode `A_w = Π T(-w) χ T(w)` at a complex parameter `w`
(for real `w` this is `ModeSector.mode`). -/
noncomputable def modeC (S : H.ModeSector) (w : ℂ) : A :=
  S.Pi * H.frustration.transfer ∅ (-w) * H.root * H.frustration.transfer ∅ w

/-- Pure algebra of `mode_eq_smul` over an arbitrary commutative scalar ring. -/
theorem mode_algebra_gen {B : Type*} [Ring B] {R : Type*} [CommRing R] [Algebra R B]
    (P Tv Sg χ : B) (v : R) (hz : P * Tv = 0)
    (hFI : (1 - v • Sg) * χ * Tv = Tv * ((1 + v • Sg) * χ)) :
    P * χ * Tv = v • (P * (Sg * χ) * Tv) := by
  have h := congrArg (fun x => P * x) hFI
  have hR : P * (Tv * ((1 + v • Sg) * χ)) = 0 := by
    rw [← mul_assoc, hz, zero_mul]
  have hL : P * ((1 - v • Sg) * χ * Tv) = P * χ * Tv - v • (P * (Sg * χ) * Tv) := by
    simp only [mul_sub, sub_mul, one_mul, smul_mul_assoc, mul_smul_comm, mul_assoc]
  simp only [hL, hR] at h
  exact sub_eq_zero.mp h

/-- `A_w = w Π T(-w) (Σ χ) T(w)` at a complex root `w`. -/
theorem modeC_eq_smul (S : H.ModeSector) (hKs : G.IsSimplicialClique Ks) {w : ℂ}
    (hroot : Polynomial.aeval (-w ^ 2) S.zG = 0) :
    S.modeC w = w • (S.Pi * H.frustration.transfer ∅ (-w) *
        ((∑ j ∈ verticesOfSet Ks, H.frustration.term j) * H.root) *
        H.frustration.transfer ∅ w) := by
  have hz : S.Pi * (H.frustration.transfer ∅ (-w) * H.frustration.transfer ∅ w) = 0 := by
    have h := S.Z_scalar_complex (-w)
    rw [neg_neg, neg_sq, hroot, zero_smul] at h
    exact h
  exact mode_algebra_gen (S.Pi * H.frustration.transfer ∅ (-w)) (H.frustration.transfer ∅ w) _ _ w
    (by rw [mul_assoc]; exact hz) (H.fundamentalIdentity_reduced_negC hKs w)

/-- **Eigenmode lemma at a complex root** (the complex-parameter form of `ModeSector.eigenmode`):
if `w ≠ 0` and `z_G(-w²) = 0` then `[H, A_w] = (2/w) A_w`. -/
theorem comm_modeC (S : H.ModeSector) (hclaw : G.IsClawFree)
    (hKs : G.IsSimplicialClique Ks) {w : ℂ} (hw : w ≠ 0)
    (hroot : Polynomial.aeval (-w ^ 2) S.zG = 0) :
    algebraCommutator H.frustration.hamiltonian (S.modeC w) = (2 / w) • S.modeC w := by
  have ha : Commute H.frustration.hamiltonian (S.Pi * H.frustration.transfer ∅ (-w)) :=
    S.Pi_comm_hamiltonian.symm.mul_right (H.hamiltonian_commute_transferC hclaw (-w))
  have hc : Commute H.frustration.hamiltonian (H.frustration.transfer ∅ w) :=
    H.hamiltonian_commute_transferC hclaw w
  have h1 : algebraCommutator H.frustration.hamiltonian (S.modeC w) =
      S.Pi * H.frustration.transfer ∅ (-w) *
        algebraCommutator H.frustration.hamiltonian H.root * H.frustration.transfer ∅ w :=
    algebraCommutator_mul_mul ha hc
  have h2 : algebraCommutator H.frustration.hamiltonian H.root =
      (2 : ℂ) • ((∑ j ∈ verticesOfSet Ks, H.frustration.term j) * H.root) := by
    rw [H.operator.commutator_hamiltonian_root, two_smul, two_mul]
    rfl
  rw [h1, h2, S.modeC_eq_smul hKs hroot, smul_smul, div_mul_cancel₀ _ hw]
  simp only [mul_smul_comm, smul_mul_assoc]

/-- **`{A_w, χ} = 4 z_K(-w²) Π` at a complex root `w`** (the complex-parameter form of
`ModeSector.mode_anticomm_root`). -/
theorem modeC_anticomm_root (S : H.ModeSector) (hclaw : G.IsClawFree)
    (hKs : G.IsSimplicialClique Ks) {w : ℂ}
    (hroot : Polynomial.aeval (-w ^ 2) S.zG = 0) :
    S.modeC w * H.root + H.root * S.modeC w =
      (4 * Polynomial.aeval (-w ^ 2) S.zK) • S.Pi := by
  have key : H.frustration.transfer ∅ (-w) * H.root * H.frustration.transfer ∅ w * H.root +
      H.root * H.frustration.transfer ∅ (-w) * H.root * H.frustration.transfer ∅ w =
      (4 : ℂ) • (H.frustration.transfer Ks w * H.frustration.transfer Ks (-w)) -
        (2 : ℂ) • (H.frustration.transfer ∅ w * H.frustration.transfer ∅ (-w)) :=
    H.operator.root_sandwich_anticomm hclaw hKs H.root_sq w
  have hPχ : S.Pi * H.root = H.root * S.Pi := S.Pi_comm_root.eq
  have h1 : S.modeC w * H.root + H.root * S.modeC w =
      S.Pi * (H.frustration.transfer ∅ (-w) * H.root * H.frustration.transfer ∅ w * H.root +
        H.root * H.frustration.transfer ∅ (-w) * H.root * H.frustration.transfer ∅ w) := by
    unfold modeC
    have e : H.root * (S.Pi * H.frustration.transfer ∅ (-w) * H.root *
        H.frustration.transfer ∅ w) =
        S.Pi * (H.root * H.frustration.transfer ∅ (-w) * H.root *
          H.frustration.transfer ∅ w) := by
      rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc,
        ← hPχ]
    rw [e, mul_add]
    simp only [mul_assoc]
  rw [h1, key, mul_sub, mul_smul_comm, mul_smul_comm, S.ZK_scalar_complex w, S.Z_scalar_complex w,
    hroot, zero_smul, smul_zero, sub_zero, smul_smul]

end ModeSector
end SimplicialModeHamiltonian
end SimpleGraph

/-! ### Real-parameter identities for modes, and their polynomial lifts -/

namespace SimpleGraph
namespace SimplicialModeHamiltonian
namespace ModeSector

open ModeSectorPositivity

variable {G : SimpleGraph V} {Ks : Set V} {A : Type w}
variable [Ring A] [StarRing A] [Algebra ℝ A] [StarModule ℝ A]
variable [Fintype V] [DecidableEq V]
variable {H : G.SimplicialModeHamiltonian Ks A}

/-- **Mode identity at arbitrary real `u`, without a root hypothesis.**
`u [H, A_u] = 2 A_u - 2 z_G(-u²) Π (1 + uΣ) χ`. -/
theorem smul_comm_mode (S : H.ModeSector) (hclaw : G.IsClawFree)
    (hKs : G.IsSimplicialClique Ks) (u : ℝ) :
    u • algebraCommutator H.frustration.hamiltonian (S.mode u) =
      (2 : ℝ) • S.mode u - (2 * S.zG.eval (-u ^ 2)) •
        (S.Pi * ((1 + u • ∑ j ∈ verticesOfSet Ks, H.frustration.term j) * H.root)) := by
  have ha : Commute H.frustration.hamiltonian (S.Pi * H.frustration.transfer ∅ (-u)) :=
    S.Pi_comm_hamiltonian.symm.mul_right (H.hamiltonian_commute_transfer hclaw (-u))
  have hc : Commute H.frustration.hamiltonian (H.frustration.transfer ∅ u) :=
    H.hamiltonian_commute_transfer hclaw u
  have h1 : algebraCommutator H.frustration.hamiltonian (S.mode u) =
      S.Pi * H.frustration.transfer ∅ (-u) *
        algebraCommutator H.frustration.hamiltonian H.root * H.frustration.transfer ∅ u :=
    algebraCommutator_mul_mul ha hc
  have h2 : algebraCommutator H.frustration.hamiltonian H.root =
      (2 : ℝ) • ((∑ j ∈ verticesOfSet Ks, H.frustration.term j) * H.root) := by
    rw [H.operator.commutator_hamiltonian_root, two_smul, two_mul]
    rfl
  -- the reduced Fundamental Identity sandwiched between `Π T(-u)` and `1`
  set Sg := ∑ j ∈ verticesOfSet Ks, H.frustration.term j with hSg
  have hFI := H.fundamentalIdentity_reduced_neg hKs u
  have hz : S.Pi * (H.frustration.transfer ∅ (-u) * H.frustration.transfer ∅ u) =
      S.zG.eval (-u ^ 2) • S.Pi := by
    have h := S.Z_scalar (-u)
    rw [neg_neg, neg_sq] at h
    exact h
  have hsand : S.mode u - u • (S.Pi * H.frustration.transfer ∅ (-u) * (Sg * H.root) *
      H.frustration.transfer ∅ u) = S.zG.eval (-u ^ 2) • (S.Pi * ((1 + u • Sg) * H.root)) := by
    have h := congrArg (fun x => S.Pi * H.frustration.transfer ∅ (-u) * x) hFI
    have hL : S.Pi * H.frustration.transfer ∅ (-u) * ((1 - u • Sg) * H.root *
        H.frustration.transfer ∅ u) = S.mode u - u • (S.Pi * H.frustration.transfer ∅ (-u) *
          (Sg * H.root) * H.frustration.transfer ∅ u) := by
      unfold mode
      simp only [mul_sub, sub_mul, one_mul, smul_mul_assoc, mul_smul_comm, mul_assoc]
    have hR : S.Pi * H.frustration.transfer ∅ (-u) * (H.frustration.transfer ∅ u *
        ((1 + u • Sg) * H.root)) = S.zG.eval (-u ^ 2) • (S.Pi * ((1 + u • Sg) * H.root)) := by
      rw [← mul_assoc, mul_assoc S.Pi, hz, smul_mul_assoc]
    rw [← hL, ← hR, h]
  rw [h1, h2]
  have e : u • (S.Pi * H.frustration.transfer ∅ (-u) * ((2 : ℝ) • (Sg * H.root)) *
      H.frustration.transfer ∅ u) = (2 : ℝ) • (u • (S.Pi * H.frustration.transfer ∅ (-u) *
        (Sg * H.root) * H.frustration.transfer ∅ u)) := by
    rw [mul_smul_comm, smul_mul_assoc, smul_comm]
  rw [e]
  have e2 : u • (S.Pi * H.frustration.transfer ∅ (-u) * (Sg * H.root) *
      H.frustration.transfer ∅ u) = S.mode u - S.zG.eval (-u ^ 2) •
        (S.Pi * ((1 + u • Sg) * H.root)) := by
    rw [← hsand]; abel
  rw [e2, smul_sub, smul_smul]

/-- **`{A_u, χ} = (4 z_K - 2 z_G)(-u²) Π` at arbitrary real `u`** (`mode_anticomm_root` before
imposing the root hypothesis). -/
theorem mode_anticomm_real (S : H.ModeSector) (hclaw : G.IsClawFree)
    (hKs : G.IsSimplicialClique Ks) (u : ℝ) :
    S.mode u * H.root + H.root * S.mode u =
      (4 * S.zK.eval (-u ^ 2) - 2 * S.zG.eval (-u ^ 2)) • S.Pi := by
  have key : H.frustration.transfer ∅ (-u) * H.root * H.frustration.transfer ∅ u * H.root +
      H.root * H.frustration.transfer ∅ (-u) * H.root * H.frustration.transfer ∅ u =
      (4 : ℝ) • (H.frustration.transfer Ks u * H.frustration.transfer Ks (-u)) -
        (2 : ℝ) • (H.frustration.transfer ∅ u * H.frustration.transfer ∅ (-u)) :=
    H.operator.root_sandwich_anticomm hclaw hKs H.root_sq u
  have hPχ : S.Pi * H.root = H.root * S.Pi := S.Pi_comm_root.eq
  have h1 : S.mode u * H.root + H.root * S.mode u =
      S.Pi * (H.frustration.transfer ∅ (-u) * H.root * H.frustration.transfer ∅ u * H.root +
        H.root * H.frustration.transfer ∅ (-u) * H.root * H.frustration.transfer ∅ u) := by
    unfold mode
    have e : H.root * (S.Pi * H.frustration.transfer ∅ (-u) * H.root *
        H.frustration.transfer ∅ u) =
        S.Pi * (H.root * H.frustration.transfer ∅ (-u) * H.root *
          H.frustration.transfer ∅ u) := by
      rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc,
        ← hPχ]
    rw [e, mul_add]
    simp only [mul_assoc]
  rw [h1, key, mul_sub, mul_smul_comm, mul_smul_comm, S.ZK_scalar u, S.Z_scalar u, smul_smul,
    smul_smul, sub_smul]

end ModeSector
end SimplicialModeHamiltonian

namespace PauliFrustrationRepresentation

variable {G : SimpleGraph V} {A : Type w} [Ring A] [Algebra ℝ A] [Fintype V] [DecidableEq V]

/-- `T_{G∖W}(Y)` as a polynomial in `Y` with coefficients in `A`: its value at the central real
point `algebraMap ℝ A u` is `T_{G∖W}(u)` (`eval_transferPolynomial`). -/
noncomputable def transferPolynomial (F : G.PauliFrustrationRepresentation A) (W : Set V) :
    A[X] :=
  ∑ k ∈ Finset.range (Fintype.card V + 1), C (((-1 : ℝ) ^ k) • F.deletedCharge W k) * X ^ k

/-- `T_{G∖W}(-Y)` as a polynomial in `Y` with coefficients in `A`. -/
noncomputable def transferNegPolynomial (F : G.PauliFrustrationRepresentation A) (W : Set V) :
    A[X] :=
  ∑ k ∈ Finset.range (Fintype.card V + 1), C (F.deletedCharge W k) * X ^ k

theorem eval_transferPolynomial (F : G.PauliFrustrationRepresentation A) (W : Set V) (u : ℝ) :
    (F.transferPolynomial W).eval (algebraMap ℝ A u) = F.transfer W u := by
  unfold transferPolynomial
  rw [ModeSectorPositivity.eval_sum_C_mul_X_pow]
  unfold transfer
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have e : u ^ j * (-1 : ℝ) ^ j = (-u) ^ j := by rw [← mul_pow]; ring
  rw [smul_smul, e]

theorem eval_transferNegPolynomial (F : G.PauliFrustrationRepresentation A) (W : Set V) (u : ℝ) :
    (F.transferNegPolynomial W).eval (algebraMap ℝ A u) = F.transfer W (-u) := by
  unfold transferNegPolynomial
  rw [ModeSectorPositivity.eval_sum_C_mul_X_pow]
  unfold transfer
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [neg_neg]

theorem coeff_transferPolynomial (F : G.PauliFrustrationRepresentation A) (W : Set V) (i : ℕ) :
    (F.transferPolynomial W).coeff i = ((-1 : ℝ) ^ i) • F.deletedCharge W i := by
  unfold transferPolynomial
  rw [ModeSectorPositivity.coeff_sum_C_mul_X_pow]
  split_ifs with h
  · rfl
  · rw [F.deletedCharge_eq_zero_of_card_lt W (by omega), smul_zero]

omit [Algebra ℝ A] in
theorem coeff_transferNegPolynomial (F : G.PauliFrustrationRepresentation A) (W : Set V) (i : ℕ) :
    (F.transferNegPolynomial W).coeff i = F.deletedCharge W i := by
  unfold transferNegPolynomial
  rw [ModeSectorPositivity.coeff_sum_C_mul_X_pow]
  split_ifs with h
  · rfl
  · exact (F.deletedCharge_eq_zero_of_card_lt W (by omega)).symm

end PauliFrustrationRepresentation

end SimpleGraph

namespace SimpleGraph
namespace SimplicialModeHamiltonian
namespace ModeSector

open ModeSectorPositivity

variable {G : SimpleGraph V} {Ks : Set V} {A : Type w}
variable [Ring A] [StarRing A] [Algebra ℝ A] [StarModule ℝ A]
variable [Fintype V] [DecidableEq V]
variable {H : G.SimplicialModeHamiltonian Ks A}

/-- The mode `A_Y = Π T(-Y) χ T(Y)` as a polynomial in `Y` with coefficients in `A`. -/
noncomputable def modePolynomial (S : H.ModeSector) : A[X] :=
  C S.Pi * H.frustration.transferNegPolynomial ∅ * C H.root * H.frustration.transferPolynomial ∅

theorem eval_modePolynomial (S : H.ModeSector) (u : ℝ) :
    S.modePolynomial.eval (algebraMap ℝ A u) = S.mode u := by
  unfold modePolynomial mode
  rw [eval_mul_real, eval_mul_real, eval_mul_real, eval_C, eval_C,
    H.frustration.eval_transferNegPolynomial, H.frustration.eval_transferPolynomial]

/-- The polynomial `Π (1 + Y Σ) χ`, i.e. `Π χ + Y Π Σ χ`. -/
noncomputable def sourcePolynomial (S : H.ModeSector) : A[X] :=
  C (S.Pi * H.root) + X * C (S.Pi * ((∑ j ∈ verticesOfSet Ks, H.frustration.term j) * H.root))

/-- **Polynomial form of `smul_comm_mode`.**  In `A[X]`,
`Y [H, 𝒜] = 2 𝒜 - 2 ĝ ℬ`, where `𝒜 = modePolynomial`, `ĝ = z_G(-Y²)` and `ℬ = Π (1 + Y Σ) χ`. -/
theorem modePolynomial_comm (S : H.ModeSector) (hclaw : G.IsClawFree)
    (hKs : G.IsSimplicialClique Ks) :
    X * (C H.frustration.hamiltonian * S.modePolynomial -
        S.modePolynomial * C H.frustration.hamiltonian) =
      2 * S.modePolynomial - 2 * ((S.zG.comp (-(X ^ 2))).map (algebraMap ℝ A) *
        S.sourcePolynomial) := by
  rw [← sub_eq_zero]
  refine Polynomial.eq_zero_of_infinite_eval_algebraMap _ ?_
  have hall : {x : ℝ | (X * (C H.frustration.hamiltonian * S.modePolynomial -
        S.modePolynomial * C H.frustration.hamiltonian) -
      (2 * S.modePolynomial - 2 * ((S.zG.comp (-(X ^ 2))).map (algebraMap ℝ A) *
        S.sourcePolynomial))).eval (algebraMap ℝ A x) = 0} = Set.univ := by
    refine Set.eq_univ_of_forall (fun u => ?_)
    show (X * (C H.frustration.hamiltonian * S.modePolynomial -
        S.modePolynomial * C H.frustration.hamiltonian) -
      (2 * S.modePolynomial - 2 * ((S.zG.comp (-(X ^ 2))).map (algebraMap ℝ A) *
        S.sourcePolynomial))).eval (algebraMap ℝ A u) = 0
    have h := S.smul_comm_mode hclaw hKs u
    unfold algebraCommutator at h
    simp only [eval_sub, eval_mul_real, eval_X, eval_C, eval_ofNat, eval_modePolynomial,
      eval_map_real, sourcePolynomial, eval_add, eval_comp, eval_neg, eval_pow]
    have hB : S.Pi * ((1 + u • ∑ j ∈ verticesOfSet Ks, H.frustration.term j) * H.root) =
        S.Pi * H.root + u • (S.Pi * ((∑ j ∈ verticesOfSet Ks, H.frustration.term j) * H.root)) := by
      simp only [add_mul, one_mul, mul_add, smul_mul_assoc, mul_smul_comm]
    rw [hB] at h
    simp only [← Algebra.smul_def]
    have e2 : ∀ x : A, (2 : A) * x = (2 : ℝ) • x := fun x => by rw [two_mul, two_smul]
    simp only [e2]
    rw [← sub_eq_zero] at h
    rw [← h]
    module
  rw [hall]
  exact Set.infinite_univ

/-- **Polynomial form of `mode_anticomm_real`.**  In `A[X]`,
`𝒜 χ + χ 𝒜 = 4 k̂ Π - 2 ĝ Π` where `k̂ = z_K(-Y²)` and `ĝ = z_G(-Y²)`. -/
theorem modePolynomial_anticomm (S : H.ModeSector) (hclaw : G.IsClawFree)
    (hKs : G.IsSimplicialClique Ks) :
    S.modePolynomial * C H.root + C H.root * S.modePolynomial =
      4 * ((S.zK.comp (-(X ^ 2))).map (algebraMap ℝ A) * C S.Pi) -
        2 * ((S.zG.comp (-(X ^ 2))).map (algebraMap ℝ A) * C S.Pi) := by
  rw [← sub_eq_zero]
  refine Polynomial.eq_zero_of_infinite_eval_algebraMap _ ?_
  have hall : {x : ℝ | (S.modePolynomial * C H.root + C H.root * S.modePolynomial -
      (4 * ((S.zK.comp (-(X ^ 2))).map (algebraMap ℝ A) * C S.Pi) -
        2 * ((S.zG.comp (-(X ^ 2))).map (algebraMap ℝ A) * C S.Pi))).eval
          (algebraMap ℝ A x) = 0} = Set.univ := by
    refine Set.eq_univ_of_forall (fun u => ?_)
    show (S.modePolynomial * C H.root + C H.root * S.modePolynomial -
      (4 * ((S.zK.comp (-(X ^ 2))).map (algebraMap ℝ A) * C S.Pi) -
        2 * ((S.zG.comp (-(X ^ 2))).map (algebraMap ℝ A) * C S.Pi))).eval
          (algebraMap ℝ A u) = 0
    have h := S.mode_anticomm_real hclaw hKs u
    simp only [eval_sub, eval_add, eval_mul_real, eval_C, eval_ofNat, eval_modePolynomial,
      eval_map_real, eval_comp, eval_neg, eval_pow, eval_X]
    simp only [← Algebra.smul_def]
    have e2 : ∀ x : A, (2 : A) * x = (2 : ℝ) • x := fun x => by rw [two_mul, two_smul]
    have e4 : ∀ x : A, (4 : A) * x = (4 : ℝ) • x := fun x => by
      have := (Algebra.smul_def (4 : ℝ) x).symm
      rwa [map_ofNat] at this
    simp only [e2, e4]
    rw [← sub_eq_zero] at h
    rw [← h]
    module
  rw [hall]
  exact Set.infinite_univ

end ModeSector
end SimplicialModeHamiltonian
end SimpleGraph

namespace SimpleGraph
namespace SimplicialModeHamiltonian
namespace ModeSector

open ModeSectorPositivity

variable {d : ℕ} {G : SimpleGraph V} {Ks : Set V} [Fintype V] [DecidableEq V]
variable {H : G.SimplicialModeHamiltonian Ks (Matrix (Fin d) (Fin d) ℂ)}

/-- `z_G(0) = 1` on a nonzero sector: `Π T(0) T(0) = Π`. -/
theorem zG_eval_zero (S : H.ModeSector) (hPi : S.Pi ≠ 0) : S.zG.eval 0 = 1 := by
  have h := S.Z_scalar 0
  have h0 : (-(0 : ℝ) ^ 2) = 0 := by norm_num
  rw [neg_zero, H.frustration.transfer_zero, mul_one, mul_one, h0] at h
  have h2 : (1 - S.zG.eval 0) • S.Pi = 0 := by
    rw [sub_smul, one_smul, ← h, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · linarith
  · exact absurd h3 hPi

/-- The complex mode is nonzero at a root where `z_K` does not vanish: `{A_w, χ} = 4 z_K(-w²) Π`
and `Π ≠ 0`. -/
theorem modeC_ne_zero (S : H.ModeSector) (hclaw : G.IsClawFree) (hKs : G.IsSimplicialClique Ks)
    (hPi : S.Pi ≠ 0) {w : ℂ} (hroot : Polynomial.aeval (-w ^ 2) S.zG = 0)
    (hK : Polynomial.aeval (-w ^ 2) S.zK ≠ 0) : S.modeC w ≠ 0 := by
  intro h0
  have h := S.modeC_anticomm_root hclaw hKs hroot
  rw [h0, zero_mul, mul_zero, add_zero] at h
  rcases smul_eq_zero.mp h.symm with h1 | h1
  · exact hK (by simpa using h1)
  · exact hPi h1

omit [DecidableEq V] in
/-- The Hamiltonian of a simplicial-mode model over `Matrix (Fin d) (Fin d) ℂ` is Hermitian. -/
theorem isHermitian_hamiltonian (H : G.SimplicialModeHamiltonian Ks (Matrix (Fin d) (Fin d) ℂ)) :
    H.frustration.hamiltonian.IsHermitian := by
  have h := H.isSelfAdjoint_hamiltonian.star_eq
  rw [Matrix.star_eq_conjTranspose] at h
  exact h

/-- **Roots of `z_G` are real and negative** (matrix algebras, no common root with `z_K`).

Let `S` be a mode sector with `Π ≠ 0` over `Matrix (Fin d) (Fin d) ℂ`, with `G` claw-free and `Ks`
a simplicial clique.  If `x ∈ ℂ` is a root of `z_G` at which `z_K` does not vanish, then `x` is real
and negative.

Proof.  `z_G(0) = 1`, so `x ≠ 0`; write `x = -w²` with `w ≠ 0`.  The complex mode
`A_w = Π T(-w) χ T(w)` satisfies `[H, A_w] = (2/w) A_w` (`comm_modeC`) and is nonzero because
`{A_w, χ} = 4 z_K(x) Π ≠ 0` (`modeC_ne_zero`).  As `H` is Hermitian, `ad_H` is self-adjoint for the
Hilbert-Schmidt form `tr (X† Y)`, so its eigenvalue `2/w` is real; hence `w` is real and
`x = -w² ≤ 0`, with `x ≠ 0`.

This is not proved in v1, which uses it silently (reality of `N_{J,j}`, `ψ_{J,-j} = ψ_{J,j}†`;
L2097, L2123-2139; cf. L604-608 for the literature on the `J`-free case). -/
theorem root_real_neg (S : H.ModeSector) (hclaw : G.IsClawFree) (hKs : G.IsSimplicialClique Ks)
    (hPi : S.Pi ≠ 0) {x : ℂ} (hroot : Polynomial.aeval x S.zG = 0)
    (hK : Polynomial.aeval x S.zK ≠ 0) : x.im = 0 ∧ x.re < 0 := by
  obtain ⟨w, hw2⟩ := exists_sq_eq (-x)
  have hx : -w ^ 2 = x := by rw [hw2]; ring
  have hx0 : x ≠ 0 := by
    rintro rfl
    have h1 : Polynomial.aeval (0 : ℂ) S.zG = 1 := by
      have h := aeval_ofReal S.zG 0
      rw [Complex.ofReal_zero, S.zG_eval_zero hPi] at h
      simpa using h
    rw [h1] at hroot
    exact one_ne_zero hroot
  have hw : w ≠ 0 := by
    rintro rfl
    apply hx0
    rw [← hx]
    ring
  have hroot' : Polynomial.aeval (-w ^ 2) S.zG = 0 := by rwa [hx]
  have hK' : Polynomial.aeval (-w ^ 2) S.zK ≠ 0 := by rwa [hx]
  have hX := S.modeC_ne_zero hclaw hKs hPi hroot' hK'
  have hc := S.comm_modeC hclaw hKs hw hroot'
  have him : (2 / w).im = 0 :=
    im_eq_zero_of_commutator_eq_smul (isHermitian_hamiltonian H) hX hc
  have hwim : w.im = 0 := by
    rw [Complex.div_im] at him
    simp at him
    rcases him with h | h
    · exact h
    · exact absurd h hw
  have hxim : x.im = 0 := by
    rw [← hx]
    simp [pow_two, hwim]
  refine ⟨hxim, ?_⟩
  have hre : x.re = -(w.re ^ 2) := by
    rw [← hx]
    simp [pow_two, hwim]
  have hne : x.re ≠ 0 := by
    intro h0
    exact hx0 (Complex.ext h0 hxim)
  have : 0 < w.re ^ 2 := by
    rcases (sq_nonneg w.re).lt_or_eq with h | h
    · exact h
    · exact absurd (by rw [hre, ← h]; ring) hne
  rw [hre]
  linarith

/-- A real root of `z_G` at which `z_K` does not vanish is negative (the real case of
`root_real_neg`). -/
theorem real_root_neg (S : H.ModeSector) (hclaw : G.IsClawFree) (hKs : G.IsSimplicialClique Ks)
    (hPi : S.Pi ≠ 0) {x : ℝ} (hroot : S.zG.eval x = 0) (hK : S.zK.eval x ≠ 0) : x < 0 := by
  have h := S.root_real_neg hclaw hKs hPi (x := (x : ℂ))
    (by rw [aeval_ofReal, hroot]; simp)
    (by rw [aeval_ofReal]; exact_mod_cast hK)
  simpa using h.2

/-- **The radicand `z_K(x) z_G'(x)` is positive at every real root of `z_G`** (v1 uses this silently
for `N_{J,j}` at L2097).

Let `x` be a real root of `z_G` with `z_K(x) ≠ 0`.  By `real_root_neg` `x = -v²` with `v > 0`.
Taking the trace of `{A_v, A_{-v}} = 16 v² z_K(x) z_G'(x) Π` (`mode_anticomm_mode_neg`) and using
`A_{-v} = A_v†` (`star_mode`) gives `2 ‖A_v‖²_HS = 16 v² z_K(x) z_G'(x) tr Π`, where `A_v ≠ 0`
(`{A_v, χ} = 4 z_K(x) Π ≠ 0`) and `tr Π = ‖Π‖²_HS > 0`. -/
theorem radicand_pos (S : H.ModeSector) (hclaw : G.IsClawFree) (hKs : G.IsSimplicialClique Ks)
    (hPi : S.Pi ≠ 0) {x : ℝ} (hroot : S.zG.eval x = 0) (hK : S.zK.eval x ≠ 0) :
    0 < S.zK.eval x * (Polynomial.derivative S.zG).eval x := by
  have hxneg : x < 0 := S.real_root_neg hclaw hKs hPi hroot hK
  set v := Real.sqrt (-x) with hv_def
  have hv : 0 < v := Real.sqrt_pos.mpr (by linarith)
  have hvx : -v ^ 2 = x := by
    rw [hv_def, Real.sq_sqrt (by linarith)]; ring
  have hrootv : S.zG.eval (-v ^ 2) = 0 := by rw [hvx]; exact hroot
  have hKv : S.zK.eval (-v ^ 2) ≠ 0 := by rw [hvx]; exact hK
  have hAA := S.mode_anticomm_mode_neg hclaw hKs hv.ne' hrootv
  have hAne : S.mode v ≠ 0 := by
    intro h0
    have h := S.mode_anticomm_root hclaw hKs hrootv
    rw [h0, zero_mul, mul_zero, add_zero] at h
    rcases smul_eq_zero.mp h.symm with h1 | h1
    · exact hKv (by linarith)
    · exact hPi h1
  have hstar : S.mode (-v) = (S.mode v)ᴴ := by
    rw [← S.star_mode v, Matrix.star_eq_conjTranspose]
  rw [hstar] at hAA
  set c : ℝ := 16 * v ^ 2 * S.zK.eval (-v ^ 2) * (Polynomial.derivative S.zG).eval (-v ^ 2)
    with hc_def
  have htr := congrArg Matrix.trace hAA
  rw [Matrix.trace_add, Matrix.trace_mul_comm (S.mode v) (S.mode v)ᴴ,
    trace_conjTranspose_mul_self, Matrix.trace_smul, Complex.real_smul] at htr
  have hPiH : S.Piᴴ = S.Pi := by
    have := S.Pi_selfAdjoint.star_eq
    rwa [Matrix.star_eq_conjTranspose] at this
  have hPitr : S.Pi.trace = ((hsNormSq S.Pi : ℝ) : ℂ) := by
    rw [← trace_conjTranspose_mul_self, hPiH, S.Pi_idem]
  rw [hPitr] at htr
  have hreal : hsNormSq (S.mode v) + hsNormSq (S.mode v) = c * hsNormSq S.Pi := by
    exact_mod_cast htr
  have h1 := hsNormSq_pos hAne
  have h2 := hsNormSq_pos hPi
  have hcpos : 0 < c := by
    by_contra hneg
    push Not at hneg
    nlinarith [mul_le_mul_of_nonneg_right hneg h2.le]
  have hcx : c = 16 * v ^ 2 * (S.zK.eval x * (Polynomial.derivative S.zG).eval x) := by
    rw [hc_def, hvx]; ring
  rw [hcx] at hcpos
  have hv2 : 0 < 16 * v ^ 2 := by positivity
  exact pos_of_mul_pos_right hcpos hv2.le


/-! ### Vanishing of the top charges on the sector -/

section Charges

open Polynomial

variable {d : ℕ} {H : G.SimplicialModeHamiltonian Ks (Matrix (Fin d) (Fin d) ℂ)}

/-- The `u^{2k}` coefficient of `Π T(u) T(-u) = z_G(-u²) Π`.  If `k > deg z_G` and `Π Q^(t) = 0`
for all `t > k`, then `Π (Q^(k))² = 0`. -/
theorem Pi_mul_charge_sq_eq_zero (S : H.ModeSector) {k : ℕ} (hk : S.zG.natDegree < k)
    (hhigh : ∀ t, k < t → H.frustration.charge t * S.Pi = 0) :
    S.Pi * (H.frustration.charge k * H.frustration.charge k) = 0 := by
  classical
  set Q : ℕ → Matrix (Fin d) (Fin d) ℂ := fun j => H.frustration.charge j with hQ
  set TP : (Matrix (Fin d) (Fin d) ℂ)[X] := H.frustration.transferPolynomial ∅ with hTP
  set TPm : (Matrix (Fin d) (Fin d) ℂ)[X] := H.frustration.transferNegPolynomial ∅ with hTPm
  set g : ℝ[X] := S.zG.comp (-(X ^ 2)) with hg
  set Z : (Matrix (Fin d) (Fin d) ℂ)[X] := C S.Pi * g.map (algebraMap ℝ _) with hZdef
  have hT : ∀ u : ℝ, TP.eval (algebraMap ℝ _ u) = H.frustration.transfer ∅ u :=
    fun u => H.frustration.eval_transferPolynomial ∅ u
  have hTm : ∀ u : ℝ, TPm.eval (algebraMap ℝ _ u) = H.frustration.transfer ∅ (-u) :=
    fun u => H.frustration.eval_transferNegPolynomial ∅ u
  have hZ : ∀ u : ℝ, Z.eval (algebraMap ℝ _ u) = S.zG.eval (-u ^ 2) • S.Pi := by
    intro u
    rw [hZdef, eval_C_mul, eval_map, ← aeval_def, aeval_algebraMap_apply_eq_algebraMap_eval,
      Algebra.smul_def, ← Algebra.commutes, hg]
    simp only [eval_comp, eval_neg, eval_pow, eval_X]
  have hF : C S.Pi * TP * TPm - Z = 0 := by
    refine Polynomial.eq_zero_of_infinite_eval_algebraMap _ ?_
    have hall : {x : ℝ | (C S.Pi * TP * TPm - Z).eval (algebraMap ℝ _ x) = 0} = Set.univ := by
      refine Set.eq_univ_of_forall (fun u => ?_)
      show (C S.Pi * TP * TPm - Z).eval (algebraMap ℝ _ u) = 0
      have h1 := map_sub (Polynomial.evalCentralHom (Matrix (Fin d) (Fin d) ℂ) u)
        (C S.Pi * TP * TPm) Z
      have h2 := map_mul (Polynomial.evalCentralHom (Matrix (Fin d) (Fin d) ℂ) u)
        (C S.Pi * TP) TPm
      have h3 := map_mul (Polynomial.evalCentralHom (Matrix (Fin d) (Fin d) ℂ) u) (C S.Pi) TP
      simp only [Polynomial.evalCentralHom_apply, eval_C] at h1 h2 h3
      rw [h1, h2, h3, hT, hTm, hZ, mul_assoc, S.Z_scalar u, sub_self]
    rw [hall]
    exact Set.infinite_univ
  have hcoef : (C S.Pi * TP * TPm).coeff (2 * k) = Z.coeff (2 * k) := by
    have := congrArg (fun p => Polynomial.coeff p (2 * k)) (sub_eq_zero.mp hF)
    exact this
  have hZcoef : Z.coeff (2 * k) = 0 := by
    rw [hZdef, coeff_C_mul, coeff_map]
    have hdeg : g.natDegree < 2 * k := by
      rw [hg, natDegree_comp, natDegree_neg, natDegree_X_pow]
      omega
    rw [coeff_eq_zero_of_natDegree_lt hdeg, map_zero, mul_zero]
  have hcTP : ∀ i, TP.coeff i = ((-1 : ℝ) ^ i) • Q i :=
    fun i => H.frustration.coeff_transferPolynomial ∅ i
  have hcTPm : ∀ i, TPm.coeff i = Q i := fun i => H.frustration.coeff_transferNegPolynomial ∅ i
  rw [hZcoef, mul_assoc, coeff_C_mul, coeff_mul, Finset.mul_sum] at hcoef
  have hcomm : ∀ j, S.Pi * Q j = Q j * S.Pi := fun j => (S.Pi_comm_charge j).eq
  rw [Finset.sum_eq_single (k, k)] at hcoef
  · simp only [hcTP, hcTPm] at hcoef
    have h1 : (-1 : ℝ) ^ k • (S.Pi * (Q k * Q k)) = 0 := by
      rw [← hcoef]
      simp only [mul_smul_comm, smul_mul_assoc]
    rcases smul_eq_zero.mp h1 with h | h
    · exact absurd h (pow_ne_zero _ (by norm_num))
    · exact h
  · intro x hx hne
    rw [Finset.mem_antidiagonal] at hx
    rw [hcTP, hcTPm]
    have hx1 : x.1 ≠ k := by
      intro h1
      apply hne
      ext
      · exact h1
      · simp only; omega
    rcases lt_or_gt_of_ne hx1 with hlt | hgt
    · -- `x.2 > k`
      have hx2 : k < x.2 := by omega
      have h0 : Q x.2 * S.Pi = 0 := hhigh x.2 hx2
      calc S.Pi * (((-1 : ℝ) ^ x.1 • Q x.1) * Q x.2)
          = ((-1 : ℝ) ^ x.1) • (Q x.1 * (S.Pi * Q x.2)) := by
            rw [smul_mul_assoc, mul_smul_comm, ← mul_assoc, ← mul_assoc, hcomm, mul_assoc]
        _ = 0 := by rw [hcomm, h0, mul_zero, smul_zero]
    · have h0 : Q x.1 * S.Pi = 0 := hhigh x.1 hgt
      calc S.Pi * (((-1 : ℝ) ^ x.1 • Q x.1) * Q x.2)
          = ((-1 : ℝ) ^ x.1) • ((S.Pi * Q x.1) * Q x.2) := by
            rw [smul_mul_assoc, mul_smul_comm, mul_assoc]
        _ = 0 := by rw [hcomm, h0, zero_mul, smul_zero]
  · intro h
    exfalso
    apply h
    rw [Finset.mem_antidiagonal]
    ring

/-- **Vanishing of the top charges on the sector.**  `Q_G^(k) Π = 0` for every `k > deg z_G`,
i.e. the charges above the degree of the sector polynomial act as zero on the sector (not proved
in v1).

Downward induction on `k`.  The coefficient of `u^{2k}` in `Π T(u) T(-u) = z_G(-u²) Π` is, for
`k > deg z_G`, zero; on the left it is `(-1)^k Π (Q^(k))²` plus terms containing some `Q^(t)` with
`t > k`, which vanish by the induction hypothesis because `Π` commutes with the charges.  So
`Π (Q^(k))² = 0`, and then `(Q^(k) Π)† (Q^(k) Π) = Π (Q^(k))² Π = 0` gives `Q^(k) Π = 0`.

Neither claw-freeness, a simplicial clique, nor `Π ≠ 0` is used (the commutation of `Π` with the
charges and the scalar action `Z_scalar` are fields of the sector). -/
theorem charge_mul_Pi_eq_zero (S : H.ModeSector) {k : ℕ} (hk : S.zG.natDegree < k) :
    H.frustration.charge k * S.Pi = 0 := by
  have key : ∀ m : ℕ, ∀ k : ℕ, Fintype.card V + 1 - k = m → S.zG.natDegree < k →
      H.frustration.charge k * S.Pi = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro k hm hk
      by_cases hbig : Fintype.card V < k
      · show H.frustration.deletedCharge ∅ k * S.Pi = 0
        rw [H.frustration.deletedCharge_eq_zero_of_card_lt ∅ hbig, zero_mul]
      · have hhigh : ∀ t, k < t → H.frustration.charge t * S.Pi = 0 := fun t ht =>
          ih (Fintype.card V + 1 - t) (by omega) t rfl (by omega)
        have hsq := S.Pi_mul_charge_sq_eq_zero hk hhigh
        have hQH : (H.frustration.charge k)ᴴ = H.frustration.charge k := by
          have := (H.isSelfAdjoint_deletedCharge ∅ k).star_eq
          rwa [Matrix.star_eq_conjTranspose] at this
        have hPH : S.Piᴴ = S.Pi := by
          have := S.Pi_selfAdjoint.star_eq
          rwa [Matrix.star_eq_conjTranspose] at this
        apply eq_zero_of_conjTranspose_mul_self_eq_zero
        rw [Matrix.conjTranspose_mul, hQH, hPH]
        calc S.Pi * H.frustration.charge k * (H.frustration.charge k * S.Pi)
            = (S.Pi * (H.frustration.charge k * H.frustration.charge k)) * S.Pi := by
              simp only [mul_assoc]
          _ = 0 := by rw [hsq, zero_mul]
  exact key _ k rfl hk

end Charges


/-! ### Non-degeneracy data from the absence of common roots -/

section Nondegeneracy

open Polynomial

variable {d : ℕ} {H : G.SimplicialModeHamiltonian Ks (Matrix (Fin d) (Fin d) ℂ)}

/-- `z_G ≠ 0` on a nonzero sector (`z_G(0) = 1`). -/
theorem zG_ne_zero (S : H.ModeSector) (hPi : S.Pi ≠ 0) : S.zG ≠ 0 := by
  intro h
  have := S.zG_eval_zero hPi
  rw [h, eval_zero] at this
  exact zero_ne_one this

/-- **Simplicity of real roots**: `z_G'(x) ≠ 0` at every real root `x` of `z_G` with `z_K(x) ≠ 0`
(from `radicand_pos`; an extra hypothesis that the root is simple is not needed). -/
theorem derivative_eval_ne_zero (S : H.ModeSector) (hclaw : G.IsClawFree)
    (hKs : G.IsSimplicialClique Ks) (hPi : S.Pi ≠ 0) {x : ℝ} (hroot : S.zG.eval x = 0)
    (hK : S.zK.eval x ≠ 0) : (derivative S.zG).eval x ≠ 0 := by
  intro h
  have := S.radicand_pos hclaw hKs hPi hroot hK
  rw [h, mul_zero] at this
  exact lt_irrefl _ this

/-- **Simplicity of complex roots** (v1 silently assumes `α(G)` distinct roots, L2129):
if `x ∈ ℂ` is a root of `z_G` at which `z_K` does not vanish, then `z_G'(x) ≠ 0`
(and `x` is real and negative, `root_real_neg`). -/
theorem aeval_derivative_ne_zero (S : H.ModeSector) (hclaw : G.IsClawFree)
    (hKs : G.IsSimplicialClique Ks) (hPi : S.Pi ≠ 0) {x : ℂ}
    (hroot : Polynomial.aeval x S.zG = 0) (hK : Polynomial.aeval x S.zK ≠ 0) :
    Polynomial.aeval x (derivative S.zG) ≠ 0 := by
  obtain ⟨him, -⟩ := S.root_real_neg hclaw hKs hPi hroot hK
  have hx : x = ((x.re : ℝ) : ℂ) := Complex.ext (by simp) (by simpa using him)
  rw [hx, aeval_ofReal] at hroot hK ⊢
  have hroot' : S.zG.eval x.re = 0 := by exact_mod_cast hroot
  have hK' : S.zK.eval x.re ≠ 0 := by exact_mod_cast hK
  have := S.derivative_eval_ne_zero hclaw hKs hPi hroot' hK'
  exact_mod_cast this

/-- Under the no-common-root hypothesis, the roots of `z_G` form a duplicate-free multiset. -/
theorem nodup_roots_zG (S : H.ModeSector) (hclaw : G.IsClawFree) (hKs : G.IsSimplicialClique Ks)
    (hPi : S.Pi ≠ 0) (hND : ∀ x : ℂ, Polynomial.aeval x S.zG = 0 → Polynomial.aeval x S.zK ≠ 0) :
    S.zG.roots.Nodup := by
  classical
  rw [Multiset.nodup_iff_count_le_one]
  intro a
  rw [Polynomial.count_roots]
  by_contra hlt
  have hlt' : 1 < rootMultiplicity a S.zG := not_le.mp hlt
  obtain ⟨h1, h2⟩ := (one_lt_rootMultiplicity_iff_isRoot (S.zG_ne_zero hPi)).mp hlt'
  have h1' : S.zG.eval a = 0 := h1
  have hK : S.zK.eval a ≠ 0 := by
    have := hND (a : ℂ) (by rw [aeval_ofReal, h1']; simp)
    rw [aeval_ofReal] at this
    exact_mod_cast this
  exact S.derivative_eval_ne_zero hclaw hKs hPi h1' hK h2

/-- **Non-degeneracy data from the absence of a common root, given that `z_G` splits over `ℝ`.**

Let `S` be a mode sector with `Π ≠ 0` over `Matrix (Fin d) (Fin d) ℂ`, `G` claw-free and `Ks` a
simplicial clique, and assume that `z_G` and `z_K` have no common complex root (`hND`).  If moreover
`z_G` splits over `ℝ`, i.e. `deg z_G` roots counted with multiplicity (`hsplit`), then there is
`Nondegenerate` data with `r = deg z_G`.

The roots of `z_G` are real and negative (`root_real_neg`), simple (`derivative_eval_ne_zero`), and
the radicands are positive (`radicand_pos`); with `z_G(0) = 1` this gives
`z_G = ∏_j (1 + x/u_j²)` with `u_j = √(-x_j)`.

The splitting hypothesis `hsplit` is discharged by `card_roots_zG_eq_natDegree` under coprimality of
`z_G` and `z_K` (`exists_nondegenerate_of_isCoprime`); it is kept separate here so that this
assembly step is independent of how the splitting is obtained. -/
theorem exists_nondegenerate_of_splits (S : H.ModeSector) (hclaw : G.IsClawFree)
    (hKs : G.IsSimplicialClique Ks) (hPi : S.Pi ≠ 0)
    (hND : ∀ x : ℂ, Polynomial.aeval x S.zG = 0 → Polynomial.aeval x S.zK ≠ 0)
    (hsplit : Multiset.card S.zG.roots = S.zG.natDegree) :
    ∃ D : S.Nondegenerate, D.r = S.zG.natDegree := by
  classical
  have hz0 := S.zG_ne_zero hPi
  have hnd := S.nodup_roots_zG hclaw hKs hPi hND
  set R : Finset ℝ := S.zG.roots.toFinset with hR
  have hcard : R.card = S.zG.natDegree := by
    rw [hR, Multiset.toFinset_card_of_nodup hnd]; exact hsplit
  have hmemR : ∀ a ∈ R, S.zG.eval a = 0 := fun a ha =>
    ((mem_roots hz0).mp (Multiset.mem_toFinset.mp ha)).eq_zero
  have hKR : ∀ a ∈ R, S.zK.eval a ≠ 0 := by
    intro a ha
    have := hND (a : ℂ) (by rw [aeval_ofReal, hmemR a ha]; simp)
    rw [aeval_ofReal] at this
    exact_mod_cast this
  have hneg : ∀ a ∈ R, a < 0 := fun a ha =>
    S.real_root_neg hclaw hKs hPi (hmemR a ha) (hKR a ha)
  let e : Fin S.zG.natDegree ≃ R := (Finset.equivFinOfCardEq hcard).symm
  let u : Fin S.zG.natDegree → ℝ := fun j => Real.sqrt (-(e j : ℝ))
  have hneg' : ∀ j, (e j : ℝ) < 0 := fun j => hneg _ (e j).2
  have hu2 : ∀ j, (u j) ^ 2 = -(e j : ℝ) := fun j => Real.sq_sqrt (by linarith [hneg' j])
  have huroot : ∀ j, -(u j) ^ 2 = (e j : ℝ) := fun j => by rw [hu2]; ring
  have hupos : ∀ j, 0 < u j := fun j => Real.sqrt_pos.mpr (by linarith [hneg' j])
  -- the product formula
  set f : ℝ → ℝ[X] := fun a => 1 + C ((-a)⁻¹) * X with hf
  have hprod : S.zG = C S.zG.leadingCoeff * ∏ a ∈ R, (X - C a) := by
    have h := C_leadingCoeff_mul_prod_multiset_X_sub_C hsplit
    rw [Finset.prod_eq_multiset_prod, hR, Multiset.toFinset_val,
      Multiset.dedup_eq_self.mpr hnd]
    exact h.symm
  have hlin : ∀ a ∈ R, (X - C a : ℝ[X]) = C (-a) * f a := by
    intro a ha
    have ha0 : -a ≠ 0 := neg_ne_zero.mpr (hneg a ha).ne
    rw [hf]
    simp only
    rw [mul_add, mul_one, ← mul_assoc, ← C_mul, mul_inv_cancel₀ ha0, C_1, one_mul, C_neg]
    ring
  have hprod2 : ∏ a ∈ R, (X - C a : ℝ[X]) = C (∏ a ∈ R, (-a)) * ∏ a ∈ R, f a := by
    rw [Finset.prod_congr rfl hlin, Finset.prod_mul_distrib, map_prod]
  have hconst : S.zG.leadingCoeff * ∏ a ∈ R, (-a) = 1 := by
    have h0 := S.zG_eval_zero hPi
    rw [hprod, hprod2] at h0
    have hev : (∏ a ∈ R, f a).eval 0 = 1 := by
      rw [eval_prod]
      refine Finset.prod_eq_one (fun a _ => ?_)
      simp [hf]
    rw [eval_mul, eval_mul, eval_C, eval_C, hev, mul_one] at h0
    exact h0
  have hzG : S.zG = ∏ a ∈ R, f a := by
    rw [hprod, hprod2, ← mul_assoc, ← C_mul, hconst, C_1, one_mul]
  refine ⟨{ r := S.zG.natDegree
            u := u
            u_pos := hupos
            u_injective := ?_
            zG_eq := ?_
            radicand_pos := ?_ }, rfl⟩
  · intro j k hjk
    have h2 : (u j) ^ 2 = (u k) ^ 2 := by rw [hjk]
    rw [hu2, hu2] at h2
    exact e.injective (Subtype.ext (by linarith))
  · show S.zG = ∏ j : Fin S.zG.natDegree, (1 + C ((u j)⁻¹ ^ 2) * X)
    have hx : ∀ j, (u j)⁻¹ ^ 2 = (-(e j : ℝ))⁻¹ := fun j => by rw [inv_pow, hu2]
    calc S.zG = ∏ a ∈ R, f a := hzG
      _ = ∏ a : R, f a := (Finset.prod_coe_sort R f).symm
      _ = ∏ j, f (e j) := (Equiv.prod_comp e (fun a : R => f a)).symm
      _ = ∏ j : Fin S.zG.natDegree, (1 + C ((u j)⁻¹ ^ 2) * X) := by
        refine Finset.prod_congr rfl (fun j _ => ?_)
        rw [hx j]
  · intro j
    show 0 < S.zK.eval (-(u j) ^ 2) * (derivative S.zG).eval (-(u j) ^ 2)
    rw [huroot j]
    exact S.radicand_pos hclaw hKs hPi (hmemR _ (e j).2) (hKR _ (e j).2)

end Nondegeneracy

/-! ### Splitting of `z_G` without the Fundamental Theorem of Algebra

If `z_G` and `z_K` are coprime, `z_G` splits over `ℝ`: every nonconstant divisor `q` of `z_G` has a
real root.  The proof studies the irreducible factors of `q(-Y²)` in `ℝ[Y]` through the polynomial
identities `modePolynomial_comm` and `modePolynomial_anticomm`; see
`natDegree_eq_one_of_irreducible_dvd`. -/

section Splitting

open Polynomial ModeSectorPositivity JointSpectralProjections

variable {d : ℕ} {H : G.SimplicialModeHamiltonian Ks (Matrix (Fin d) (Fin d) ℂ)}

/-- **No nonlinear irreducible factor.**  Let `S` be a mode sector over `Matrix (Fin d) (Fin d) ℂ`
with `Π ≠ 0`, `G` claw-free, `Ks` a simplicial clique, and `z_G`, `z_K` coprime in `ℝ[X]`.  Every
irreducible factor `P` of `z_G(-Y²)` in `ℝ[Y]` is linear.

Proof.  Let `e_μ` be the spectral idempotents of the Hermitian matrix `H` (`μ` in the finite
spectrum `Sh`).  In `A[Y]` the identity `Y [H, 𝒜] = 2 𝒜 - 2 ĝ ℬ` (`modePolynomial_comm`),
projected to the component `e_μ · e_ν`, reads `(2 - (μ - ν) Y) 𝒜_{μν} = 2 ĝ ℬ_{μν}`.  If `P`
had degree at least `2`, it would be coprime to each linear factor `2 - (μ - ν) Y`, and Bezout
(`P ∣ ĝ`) would give `P ∣ 𝒜_{μν}` for all `μ, ν`, hence `P ∣ 𝒜`.  Then
`{𝒜, χ} = (4 k̂ - 2 ĝ) Π` (`modePolynomial_anticomm`) gives `P ∣ 4 k̂ Π`, and coprimality of `P`
and `k̂` gives `P ∣ Π`, which is impossible for the nonzero constant `Π`
(`not_exists_C_eq_map_mul`).  No algebraic closure is needed. -/
theorem natDegree_eq_one_of_irreducible_dvd (S : H.ModeSector) (hclaw : G.IsClawFree)
    (hKs : G.IsSimplicialClique Ks) (hPi : S.Pi ≠ 0) (hcop : IsCoprime S.zG S.zK) {P : ℝ[X]}
    (hP : Irreducible P) (hdvd : P ∣ S.zG.comp (-(X ^ 2))) : P.natDegree = 1 := by
  by_contra hne
  have hPpos : 0 < P.natDegree := natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hP)
  have hP2 : 2 ≤ P.natDegree := by omega
  -- spectral decomposition of the Hamiltonian
  obtain ⟨Sh, hSh⟩ := exists_nodal_annihilator (isHermitian_hamiltonian H)
  set Ham := H.frustration.hamiltonian with hHam
  set e : ℝ → Matrix (Fin d) (Fin d) ℂ := fun μ => aeval Ham (basisPoly Sh μ) with he
  have hsum : ∑ μ ∈ Sh, e μ = 1 := aeval_basisPoly_sum hSh
  have hHe : ∀ μ ∈ Sh, Ham * e μ = algebraMap ℝ _ μ * e μ := fun μ hμ => by
    rw [← Algebra.smul_def]; exact mul_aeval_basisPoly hSh hμ
  have heH : ∀ μ ∈ Sh, e μ * Ham = algebraMap ℝ _ μ * e μ := fun μ hμ => by
    have hcomm : e μ * Ham = Ham * e μ := by
      have := aeval_commute_aeval Ham (basisPoly Sh μ) X
      simpa [he] using this
    rw [hcomm, hHe μ hμ]
  -- polynomial-level data in `A[X]`
  set 𝒜 := S.modePolynomial with h𝒜
  set ℬ := S.sourcePolynomial with hℬ
  set g : ℝ[X] := S.zG.comp (-(X ^ 2)) with hg
  set k : ℝ[X] := S.zK.comp (-(X ^ 2)) with hk
  have hid := S.modePolynomial_comm hclaw hKs
  have hid2 := S.modePolynomial_anticomm hclaw hKs
  have hX : ∀ r : (Matrix (Fin d) (Fin d) ℂ)[X], Commute X r := fun r => Polynomial.commute_X r
  have hγ : ∀ r : (Matrix (Fin d) (Fin d) ℂ)[X], Commute (g.map (algebraMap ℝ _)) r :=
    fun r => commute_map_algebraMap g r
  have hmap2 : ∀ r : (Matrix (Fin d) (Fin d) ℂ)[X],
      (2 : (Matrix (Fin d) (Fin d) ℂ)[X]) * r = r * 2 :=
    fun r => by
      have h2 : (2 : (Matrix (Fin d) (Fin d) ℂ)[X]) =
          ((2 : ℕ) : (Matrix (Fin d) (Fin d) ℂ)[X]) := by
        norm_num
      rw [h2]; exact (Nat.cast_commute 2 r).eq
  -- the components `𝒜_{μν} = e_μ 𝒜 e_ν` are divisible by `P`
  have hcomp : ∀ μ ∈ Sh, ∀ ν ∈ Sh, ∃ 𝒳' : (Matrix (Fin d) (Fin d) ℂ)[X],
      C (e μ) * 𝒜 * C (e ν) = P.map (algebraMap ℝ _) * 𝒳' := by
    intro μ hμ ν hν
    have hp := project_commutator_identity (x := X) (γ := g.map (algebraMap ℝ _))
      (mμ := C (algebraMap ℝ _ μ)) (mν := C (algebraMap ℝ _ ν)) (Ĥ := C Ham)
      (eμ := C (e μ)) (eν := C (e ν)) (𝒜 := 𝒜) (ℬ := ℬ) hX hγ
      (fun r => commute_C_algebraMap μ r) (fun r => commute_C_algebraMap ν r) hid
      (by rw [← C_mul, heH μ hμ, C_mul]) (by rw [← C_mul, hHe ν hν, C_mul])
    set L : ℝ[X] := 2 - C (μ - ν) * X with hL
    have hLmap : L.map (algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ)) =
        2 - (C (algebraMap ℝ _ μ) - C (algebraMap ℝ _ ν)) * X := by
      simp only [hL, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat,
        Polynomial.map_C, Polynomial.map_X, map_sub]
    have hL0 : L ≠ 0 := by
      intro h0
      have := congrArg (Polynomial.eval 0) h0
      simp [hL] at this
    have hLdeg : L.natDegree ≤ 1 := by
      rw [hL]; compute_degree
    have hcop : IsCoprime P L := by
      refine (Irreducible.coprime_iff_not_dvd hP).mpr (fun hdv => ?_)
      have := natDegree_le_of_dvd hdv hL0
      omega
    refine exists_eq_map_mul_of_isCoprime hcop hdvd (𝒞 := 2 * (C (e μ) * ℬ * C (e ν))) ?_
    rw [hLmap, hp, ← mul_assoc, hmap2 (g.map (algebraMap ℝ _)), mul_assoc]
  -- hence `P ∣ 𝒜`
  have hsumC : ∑ μ ∈ Sh, C (e μ) = (1 : (Matrix (Fin d) (Fin d) ℂ)[X]) := by
    rw [← map_sum, hsum, C_1]
  have hdecomp : 𝒜 = ∑ μ ∈ Sh, ∑ ν ∈ Sh, C (e μ) * 𝒜 * C (e ν) := by
    calc 𝒜 = (∑ μ ∈ Sh, C (e μ)) * 𝒜 * (∑ ν ∈ Sh, C (e ν)) := by rw [hsumC, one_mul, mul_one]
      _ = _ := by rw [Finset.sum_mul, Finset.sum_mul]; simp only [Finset.mul_sum]
  have hDv : ∃ 𝒜' : (Matrix (Fin d) (Fin d) ℂ)[X], 𝒜 = P.map (algebraMap ℝ _) * 𝒜' := by
    have hadd : ∀ a b : (Matrix (Fin d) (Fin d) ℂ)[X],
        (∃ a', a = P.map (algebraMap ℝ _) * a') → (∃ b', b = P.map (algebraMap ℝ _) * b') →
        ∃ c', a + b = P.map (algebraMap ℝ _) * c' := by
      rintro a b ⟨a', rfl⟩ ⟨b', rfl⟩
      exact ⟨a' + b', by rw [mul_add]⟩
    have h0 : ∃ c' : (Matrix (Fin d) (Fin d) ℂ)[X], (0 : (Matrix (Fin d) (Fin d) ℂ)[X]) =
        P.map (algebraMap ℝ _) * c' := ⟨0, by rw [mul_zero]⟩
    rw [hdecomp]
    exact Finset.sum_induction _ (fun 𝒳 : (Matrix (Fin d) (Fin d) ℂ)[X] =>
      ∃ 𝒳', 𝒳 = P.map (algebraMap ℝ _) * 𝒳') hadd h0
      (fun μ hμ => Finset.sum_induction _ (fun 𝒳 : (Matrix (Fin d) (Fin d) ℂ)[X] =>
        ∃ 𝒳', 𝒳 = P.map (algebraMap ℝ _) * 𝒳') hadd h0 (fun ν hν => hcomp μ hμ ν hν))
  obtain ⟨𝒜', h𝒜'⟩ := hDv
  obtain ⟨g', hg'⟩ := hdvd
  set Pm : (Matrix (Fin d) (Fin d) ℂ)[X] := P.map (algebraMap ℝ _) with hPm
  have hPc : ∀ r : (Matrix (Fin d) (Fin d) ℂ)[X], Pm * r = r * Pm := fun r =>
    (commute_map_algebraMap P r).eq
  -- the anticommutator with `χ`
  have hgmap : g.map (algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ)) =
      Pm * g'.map (algebraMap ℝ _) := by rw [hg', Polynomial.map_mul]
  have hW : (4 : (Matrix (Fin d) (Fin d) ℂ)[X]) * (k.map (algebraMap ℝ _) * C S.Pi) =
      Pm * (𝒜' * C H.root + C H.root * 𝒜' + 2 * (g'.map (algebraMap ℝ _) * C S.Pi)) := by
    have h4 : (4 : (Matrix (Fin d) (Fin d) ℂ)[X]) * (k.map (algebraMap ℝ _) * C S.Pi) =
        (𝒜 * C H.root + C H.root * 𝒜) + 2 * (g.map (algebraMap ℝ _) * C S.Pi) := by
      rw [hid2]; abel
    rw [h4, h𝒜', hgmap]
    have t1 : Pm * 𝒜' * C H.root = Pm * (𝒜' * C H.root) := mul_assoc _ _ _
    have t2 : C H.root * (Pm * 𝒜') = Pm * (C H.root * 𝒜') := by
      rw [← mul_assoc, ← hPc (C H.root), mul_assoc]
    have t3 : 2 * (Pm * g'.map (algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ)) * C S.Pi) =
        Pm * (2 * (g'.map (algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ)) * C S.Pi)) := by
      calc 2 * (Pm * g'.map (algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ)) * C S.Pi)
          = (2 * Pm) * (g'.map (algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ)) * C S.Pi) := by
            simp only [mul_assoc]
        _ = (Pm * 2) * (g'.map (algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ)) * C S.Pi) := by
            rw [hmap2 Pm]
        _ = _ := by rw [mul_assoc]
    rw [t1, t2, t3, mul_add, mul_add]
  -- coprimality of `P` with `4 k`
  have hPk : IsCoprime P k := by
    have h1 := hcop.map (Polynomial.compRingHom (-(X ^ 2) : ℝ[X]))
    simp only [Polynomial.coe_compRingHom_apply] at h1
    exact h1.of_isCoprime_of_dvd_left ⟨g', hg'⟩
  have hP4 : IsCoprime P (4 : ℝ[X]) := by
    refine ⟨0, C (1 / 4), ?_⟩
    rw [zero_mul, zero_add, ← map_ofNat C 4, ← C_mul]
    norm_num
  have hPL : IsCoprime P (4 * k) := hP4.mul_right hPk
  obtain ⟨𝒳', h𝒳'⟩ := exists_eq_map_mul_of_isCoprime (B := Matrix (Fin d) (Fin d) ℂ) (L := 4 * k)
    (g := P) hPL (dvd_refl P) (𝒳 := C S.Pi)
    (𝒞 := 𝒜' * C H.root + C H.root * 𝒜' + 2 * (g'.map (algebraMap ℝ _) * C S.Pi))
    (by rw [Polynomial.map_mul, Polynomial.map_ofNat, mul_assoc, hW])
  exact not_exists_C_eq_map_mul hPpos hPi ⟨𝒳', h𝒳'⟩

/-- **Every nonconstant divisor of `z_G` has a real root** (no algebraic closure used).  If
`q ∣ z_G` is nonconstant, an irreducible factor `P` of `q(-Y²)` divides `z_G(-Y²)` and is linear
(`natDegree_eq_one_of_irreducible_dvd`), so it has a real root `r`, and `-r²` is a real root of
`q`. -/
theorem exists_real_root_of_dvd (S : H.ModeSector) (hclaw : G.IsClawFree)
    (hKs : G.IsSimplicialClique Ks) (hPi : S.Pi ≠ 0) (hcop : IsCoprime S.zG S.zK) {q : ℝ[X]}
    (hq : q ∣ S.zG) (hqdeg : 0 < q.natDegree) : ∃ a : ℝ, q.IsRoot a := by
  set q' : ℝ[X] := q.comp (-(X ^ 2)) with hq'
  have hq'deg : q'.natDegree = q.natDegree * 2 := by
    rw [hq', natDegree_comp, natDegree_neg, natDegree_X_pow]
  have hq'0 : q' ≠ 0 := by
    intro h0
    rw [h0] at hq'deg
    simp at hq'deg
    omega
  have hq'u : ¬IsUnit q' := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, degree_eq_natDegree hq'0]
    intro h
    have : q'.natDegree = 0 := by exact_mod_cast h
    omega
  obtain ⟨P, hP, hPq⟩ := WfDvdMonoid.exists_irreducible_factor hq'u hq'0
  have hPg : P ∣ S.zG.comp (-(X ^ 2)) := by
    obtain ⟨c, hc⟩ := hq
    exact hPq.trans ⟨c.comp (-(X ^ 2)), by rw [hq', ← mul_comp, ← hc]⟩
  have hP1 := S.natDegree_eq_one_of_irreducible_dvd hclaw hKs hPi hcop hP hPg
  have hdeg1 : P.degree = 1 := by
    rw [degree_eq_natDegree hP.ne_zero, hP1]; rfl
  obtain ⟨r, hr⟩ := exists_root_of_degree_eq_one hdeg1
  refine ⟨-r ^ 2, ?_⟩
  have h1 : q'.eval r = 0 := by
    obtain ⟨c, hc⟩ := hPq
    rw [hc, eval_mul, hr.eq_zero, zero_mul]
  rw [hq', eval_comp] at h1
  simpa using h1

/-- The roots of a sector polynomial `z_G` coprime to `z_K`: `z_G` splits over `ℝ`. -/
theorem card_roots_zG_eq_natDegree (S : H.ModeSector) (hclaw : G.IsClawFree)
    (hKs : G.IsSimplicialClique Ks) (hPi : S.Pi ≠ 0) (hcop : IsCoprime S.zG S.zK) :
    Multiset.card S.zG.roots = S.zG.natDegree :=
  card_roots_eq_natDegree_of_dvd_real_root _ S.zG rfl (S.zG_ne_zero hPi)
    (fun _ hq hqdeg => S.exists_real_root_of_dvd hclaw hKs hPi hcop hq hqdeg)

end Splitting

/-! ### Non-degeneracy data from coprimality of `z_G` and `z_K` -/

section Final

variable {d : ℕ} {H : G.SimplicialModeHamiltonian Ks (Matrix (Fin d) (Fin d) ℂ)}

/-- **Non-degeneracy data from the absence of a common root** (v1 silently assumes all of this at
L2097 and L2123-2139), in its algebraic form: `z_G` and `z_K` are coprime in `ℝ[X]`.

Let `S` be a mode sector with `Π ≠ 0` over `Matrix (Fin d) (Fin d) ℂ`, `G` claw-free and `Ks` a
simplicial clique.  If `z_G` and `z_K` are coprime, then there is `Nondegenerate` data with
`r = deg z_G`: the roots of `z_G` are real, negative, simple and `r = deg z_G` in number
(`card_roots_zG_eq_natDegree`), and the radicands are positive (`radicand_pos`).

Coprimality of real polynomials is equivalent to the absence of a common complex root
(`aeval_ne_zero_of_isCoprime` one way; `isCoprime_of_forall_aeval_ne_zero` the other way, which uses
the Fundamental Theorem of Algebra), but this theorem does not use the Fundamental Theorem of
Algebra, and does not pass through the complex roots of `z_G`: the splitting of `z_G` over `ℝ` is
proved from the sector structure (`natDegree_eq_one_of_irreducible_dvd`). -/
theorem exists_nondegenerate_of_isCoprime (S : H.ModeSector) (hclaw : G.IsClawFree)
    (hKs : G.IsSimplicialClique Ks) (hPi : S.Pi ≠ 0) (hcop : IsCoprime S.zG S.zK) :
    ∃ D : S.Nondegenerate, D.r = S.zG.natDegree :=
  S.exists_nondegenerate_of_splits hclaw hKs hPi
    (fun x hx => ModeSectorPositivity.aeval_ne_zero_of_isCoprime hcop x hx)
    (S.card_roots_zG_eq_natDegree hclaw hKs hPi hcop)

/-- **Non-degeneracy data from the absence of a common complex root** (in the
form of the manuscript's "no common root" hypothesis), given the Fundamental Theorem of Algebra for
`ℂ` in the form of Mathlib's `Complex.exists_root` (`hFTA`).

`hFTA` is a Mathlib theorem, but its module `Mathlib.Analysis.Complex.Polynomial.Basic` lies in
the analysis hierarchy, which is not built here; a caller with that module imported passes
`fun f hf => Complex.exists_root hf`.  It is used only to turn `hND` into coprimality of `z_G` and
`z_K` (`isCoprime_of_forall_aeval_ne_zero`); see `exists_nondegenerate_of_isCoprime`, which needs no
such hypothesis. -/
theorem exists_nondegenerate_of_fta (S : H.ModeSector) (hclaw : G.IsClawFree)
    (hKs : G.IsSimplicialClique Ks) (hPi : S.Pi ≠ 0)
    (hND : ∀ x : ℂ, Polynomial.aeval x S.zG = 0 → Polynomial.aeval x S.zK ≠ 0)
    (hFTA : ∀ f : Polynomial ℂ, 0 < f.degree → ∃ z : ℂ, f.IsRoot z) :
    ∃ D : S.Nondegenerate, D.r = S.zG.natDegree :=
  S.exists_nondegenerate_of_isCoprime hclaw hKs hPi
    (ModeSectorPositivity.isCoprime_of_forall_aeval_ne_zero hFTA (S.zG_ne_zero hPi) hND)

end Final

end ModeSector
end SimplicialModeHamiltonian
end SimpleGraph
