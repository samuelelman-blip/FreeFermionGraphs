import FreeFermionGraphs.LadderRelations
import FreeFermionGraphs.PolynomialHelpers

/-!
# Canonical anticommutation relations of the incognito modes

Manuscript (arXiv 2305.15625 v1), Lemma 14 (`LadderAnticommutationRelations`, L1306-1313),
proved in the appendix at L2058-2104.  In the numbering of the revised manuscript used by the
repository, v1 Lemma 14 is "Lemma 4".

## Setting

`H` is a `SimplicialModeHamiltonian` and `S : H.ModeSector` a mode sector (see
`IncognitoModes`), with sector polynomials `z_G = S.zG` and `z_K = S.zK` (v1's `Z_{G,J}` and
`Z_{G∖Ks,J}`).  `A_v = S.mode v = Π T(-v) χ T(v)` is the unnormalised incognito mode, and
`T(u) = T_G(u)`.  `Nondegenerate` (see `LadderRelations`) provides the `r` positive distinct
roots `u_j` of `z_G(-u²)` and the normalisations `N_j`; `ψ_j^+ = A_{u_j}/N_j`,
`ψ_j^- = A_{-u_j}/N_j`.

## Main declarations

* `ModeSector.mode_anticomm_mode` : for a root `v ≠ 0` of `z_G(-v²)` and every real `w`,
  `(v + w) {A_v, A_w} = (v - w) 4 z_K(-v²) z_G(-w²) Π`  (v1 L2077-2098);
  `ModeSector.mode_anticomm_mode_neg_arg` is the same with `w ↦ -w`, i.e.
  `(v - w) {A_v, Π T(w) χ T(-w)} = (v + w) 4 z_K(-v²) z_G(-w²) Π`
  (`ModeSector.mode_neg_eq` identifies `Π T(w) χ T(-w) = A_{-w}`);
* `ModeSector.mode_anticomm_mode_eq_zero` : `{A_v, A_w} = 0` for two roots with `v + w ≠ 0`;
* `ModeSector.mode_anticomm_mode_neg` : for a root `v ≠ 0` (not assumed simple),
  `{A_v, A_{-v}} = 16 v² z_K(-v²) z_G'(-v²) Π`  (v1 L2097-2104);
* `Nondegenerate.ladder_plus_minus` : `{ψ_j^+, ψ_k^-} = δ_{jk} Π`  (v1 Lemma 14, within one
  sector; the cross-sector `δ_{J,J'}` is immediate from `Π_J Π_{J'} = 0`);
* `Nondegenerate.ladder_plus_plus`, `Nondegenerate.ladder_minus_minus` :
  `{ψ_j^+, ψ_k^+} = 0 = {ψ_j^-, ψ_k^-}`.

## Deviations from v1

* v1 states only `{ψ_{J,+j}, ψ_{J',-k}} = δ_{JJ'} δ_{jk} Π_J`.  The relations
  `{ψ_+, ψ_+} = 0` and `{ψ_-, ψ_-} = 0`, which are needed for genuine canonical
  anticommutation relations, are never stated in v1; they follow from the same intertwining
  relation at `u = -u_k` and are proved here (`ladder_plus_plus`, `ladder_minus_minus`).
* v1 passes to the limit `u → u_j` informally (L2077-2084).  Here the limit is the exact
  derivative identity of a polynomial in `w` with coefficients in the algebra
  (`Polynomial.IsPolyMap.apply_eq_neg_derivative`, built on
  `Polynomial.eval_eq_neg_derivative_of_mul_eq` of `PolynomialHelpers`).  The pointwise identity
  `(v - w) {A_v, A_{-w}} = (v + w) 4 z_K(-v²) z_G(-w²) Π` holds for *all* real `w` (including
  `w = ±v`) without inverting `Z_G(-w²)`, because the intertwining relation of `IncognitoModes`
  is derived without inversion.  In particular `mode_anticomm_mode_neg` does not assume that the
  root `v` is simple (for a multiple root the right-hand side is `0`).
* The premises beyond the manuscript setup are those of `ModeSector.Nondegenerate`
  (real, positive, distinct roots, `z_G = ∏_j (1 + x/u_j²)`, positive radicands), which v1
  uses silently (see `LadderRelations`), together with `hclaw : G.IsClawFree` and
  `hKs : G.IsSimplicialClique Ks`.  The statements `mode_anticomm_mode*` only need `hclaw`, `hKs`,
  `v ≠ 0` and `z_G(-v²) = 0`.
-/

open scoped BigOperators

namespace Polynomial

variable {B : Type*} [Ring B] [Algebra ℝ B]

/-- Evaluation of a polynomial over a (possibly noncommutative) `ℝ`-algebra `B` at the central
real point `algebraMap ℝ B w`, as a ring homomorphism. -/
noncomputable def evalCentralHom (B : Type*) [Ring B] [Algebra ℝ B] (w : ℝ) : B[X] →+* B :=
  eval₂RingHom' (RingHom.id B) (algebraMap ℝ B w) (fun a => (Algebra.commutes w a).symm)

theorem evalCentralHom_apply (w : ℝ) (p : B[X]) :
    evalCentralHom B w p = p.eval (algebraMap ℝ B w) := rfl

/-- A map `F : ℝ → B` is a *polynomial map* if it is `w ↦ p(w)` for a polynomial `p` with
coefficients in `B`, evaluated at the central real points `algebraMap ℝ B w`. -/
def IsPolyMap (F : ℝ → B) : Prop :=
  ∃ p : B[X], ∀ w, F w = p.eval (algebraMap ℝ B w)

theorem IsPolyMap.const (b : B) : IsPolyMap (fun _ : ℝ => b) :=
  ⟨C b, fun _ => (eval_C).symm⟩

theorem IsPolyMap.add {F G : ℝ → B} (hF : IsPolyMap F) (hG : IsPolyMap G) :
    IsPolyMap (fun w => F w + G w) := by
  obtain ⟨p, hp⟩ := hF
  obtain ⟨q, hq⟩ := hG
  exact ⟨p + q, fun w => by simp only [eval_add, hp, hq]⟩

theorem IsPolyMap.mul {F G : ℝ → B} (hF : IsPolyMap F) (hG : IsPolyMap G) :
    IsPolyMap (fun w => F w * G w) := by
  obtain ⟨p, hp⟩ := hF
  obtain ⟨q, hq⟩ := hG
  refine ⟨p * q, fun w => ?_⟩
  have := map_mul (evalCentralHom B w) p q
  simp only [evalCentralHom_apply] at this
  simp only [this, hp, hq]

/-- `w ↦ ∑_{k<n} w^k • a_k` is a polynomial map. -/
theorem isPolyMap_sum_smul_pow (a : ℕ → B) (n : ℕ) :
    IsPolyMap (fun w : ℝ => ∑ k ∈ Finset.range n, w ^ k • a k) := by
  refine ⟨∑ k ∈ Finset.range n, C (a k) * X ^ k, fun w => ?_⟩
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have := map_mul (evalCentralHom B w) (C (a k)) (X ^ k)
  simp only [evalCentralHom_apply] at this
  rw [this, eval_C]
  have h2 := map_pow (evalCentralHom B w) X k
  simp only [evalCentralHom_apply, eval_X] at h2
  rw [h2, ← map_pow, ← Algebra.commutes, ← Algebra.smul_def]

/-- **Exact form of the limit `u → v`.**  If `F : ℝ → B` is a polynomial map and
`(v - w) • F w = g(w) • b` for all real `w` (`g` a real polynomial, `b ∈ B`), then
`F v = -g'(v) • b`. -/
theorem IsPolyMap.apply_eq_neg_derivative {F : ℝ → B} (hF : IsPolyMap F) (v : ℝ) (g : ℝ[X])
    (b : B) (h : ∀ w, (v - w) • F w = g.eval w • b) :
    F v = -((derivative g).eval v • b) := by
  obtain ⟨p, hp⟩ := hF
  set Gp : B[X] := C b * g.map (algebraMap ℝ B) with hGp
  have hGeval : ∀ w, Gp.eval (algebraMap ℝ B w) = g.eval w • b := by
    intro w
    rw [hGp, eval_C_mul, eval_map, ← aeval_def, aeval_algebraMap_apply_eq_algebraMap_eval, Algebra.smul_def,
      ← Algebra.commutes]
  have hmain : (C (algebraMap ℝ B v) - X) * p = Gp := by
    rw [← sub_eq_zero]
    refine eq_zero_of_infinite_eval_algebraMap _ ?_
    have hall : {x : ℝ | ((C (algebraMap ℝ B v) - X) * p - Gp).eval (algebraMap ℝ B x) = 0} =
        Set.univ := by
      refine Set.eq_univ_of_forall (fun w => ?_)
      show ((C (algebraMap ℝ B v) - X) * p - Gp).eval (algebraMap ℝ B w) = 0
      have h1 := map_sub (evalCentralHom B w) ((C (algebraMap ℝ B v) - X) * p) Gp
      have h2 := map_mul (evalCentralHom B w) (C (algebraMap ℝ B v) - X) p
      have h3 := map_sub (evalCentralHom B w) (C (algebraMap ℝ B v)) X
      simp only [evalCentralHom_apply, eval_C, eval_X] at h1 h2 h3
      rw [h1, h2, h3, hGeval, ← map_sub, ← hp, ← h w, Algebra.smul_def, sub_self]
    rw [hall]
    exact Set.infinite_univ
  have := Polynomial.eval_eq_neg_derivative_of_mul_eq v p Gp hmain
  rw [hp, this, hGp, derivative_C_mul, eval_C_mul, derivative_map, eval_map, ← aeval_def,
    aeval_algebraMap_apply_eq_algebraMap_eval, Algebra.smul_def, ← Algebra.commutes]

end Polynomial

universe u w

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V} {Ks : Set V} {A : Type w}

namespace PauliFrustrationRepresentation

variable [Ring A] [Algebra ℝ A] [Fintype V] [DecidableEq V]

/-- `w ↦ T(w)` is a polynomial map (`T(w) = ∑_{k ≤ |V|} (-w)^k Q^(k)`). -/
theorem isPolyMap_transfer (H : G.PauliFrustrationRepresentation A) (W : Set V) :
    Polynomial.IsPolyMap (fun w : ℝ => H.transfer W w) := by
  have h := Polynomial.isPolyMap_sum_smul_pow
    (fun k => ((-1 : ℝ) ^ k) • H.deletedCharge W k) (Fintype.card V + 1)
  have e : (fun w : ℝ => H.transfer W w) = fun w : ℝ => ∑ k ∈ Finset.range (Fintype.card V + 1),
      w ^ k • (((-1 : ℝ) ^ k) • H.deletedCharge W k) := by
    funext w
    unfold transfer
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [smul_smul, neg_pow, mul_comm]
  rw [e]
  exact h

/-- `w ↦ T(-w)` is a polynomial map. -/
theorem isPolyMap_transfer_neg (H : G.PauliFrustrationRepresentation A) (W : Set V) :
    Polynomial.IsPolyMap (fun w : ℝ => H.transfer W (-w)) := by
  have h := Polynomial.isPolyMap_sum_smul_pow (fun k => H.deletedCharge W k)
    (Fintype.card V + 1)
  have e : (fun w : ℝ => H.transfer W (-w)) = fun w : ℝ => ∑ k ∈ Finset.range (Fintype.card V + 1),
      w ^ k • H.deletedCharge W k := by
    funext w
    unfold transfer
    simp only [neg_neg]
  rw [e]
  exact h

end PauliFrustrationRepresentation

namespace SimplicialModeHamiltonian

variable [Ring A] [StarRing A] [Algebra ℝ A] [StarModule ℝ A]
variable [Fintype V] [DecidableEq V]

namespace ModeSector

variable {H : G.SimplicialModeHamiltonian Ks A}

/-- Scaling identity for anticommutators of scalar multiples. -/
theorem smul_anticomm_smul {B : Type*} [Ring B] [Algebra ℝ B] (a b : ℝ) (x y : B) :
    (a • x) * (b • y) + (b • y) * (a • x) = (a * b) • (x * y + y * x) := by
  rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm b a, smul_add]

/-- Pure algebra of the anticommutator of a mode with a second sandwich.  Here
`a = A_v`, `Tm = T(-w)`, `Tp = T(w)`, `A = Π T(-w) χ T(w) = A_w`, and the intertwining
relations `(v - w) T(-w) a = (v + w) a T(-w)` and `(v + w) T(w) a = (v - w) a T(w)` hold. -/
theorem anticomm_sandwich_algebra {B : Type*} [Ring B] [Algebra ℝ B]
    (P Tm Tp χ a : B) (v w : ℝ)
    (hPm : P * Tm = Tm * P) (hPχ : P * χ = χ * P)
    (hPa : P * a = a) (haP : a * P = a)
    (h1 : (v - w) • (Tm * a) = (v + w) • (a * Tm))
    (h2 : (v + w) • (Tp * a) = (v - w) • (a * Tp)) :
    (v + w) • (a * (P * Tm * χ * Tp) + (P * Tm * χ * Tp) * a) =
      (v - w) • (Tm * (a * χ + χ * a) * Tp) := by
  have e1 : (v + w) • (a * (P * Tm * χ * Tp)) = (v - w) • (Tm * (a * χ) * Tp) := by
    have : a * (P * Tm * χ * Tp) = (a * Tm) * χ * Tp := by
      calc a * (P * Tm * χ * Tp) = (a * P) * Tm * χ * Tp := by simp only [mul_assoc]
        _ = (a * Tm) * χ * Tp := by rw [haP]
    rw [this, ← smul_mul_assoc, ← smul_mul_assoc, ← h1, smul_mul_assoc, smul_mul_assoc]
    simp only [mul_assoc]
  have e2 : (v + w) • ((P * Tm * χ * Tp) * a) = (v - w) • (Tm * (χ * a) * Tp) := by
    have : (P * Tm * χ * Tp) * a = (P * Tm * χ) * (Tp * a) := by simp only [mul_assoc]
    rw [this, ← mul_smul_comm, h2, mul_smul_comm]
    have : P * Tm * χ * (a * Tp) = Tm * (χ * a) * Tp := by
      calc P * Tm * χ * (a * Tp) = (P * Tm) * χ * a * Tp := by simp only [mul_assoc]
        _ = Tm * (P * χ) * a * Tp := by rw [hPm]; simp only [mul_assoc]
        _ = Tm * (χ * P) * a * Tp := by rw [hPχ]
        _ = Tm * χ * (P * a) * Tp := by simp only [mul_assoc]
        _ = Tm * (χ * a) * Tp := by rw [hPa]; simp only [mul_assoc]
    rw [this]
  rw [smul_add, e1, e2, ← smul_add]
  congr 1
  simp only [mul_add, add_mul]

/-- **Unnormalised key identity** (v1 L2085-2098; this is the intertwining relation applied to
`{ψ_{+j}, T(u) χ T(-u)}`): if `v ≠ 0` and `z_G(-v²) = 0`, then for every real `w`

`(v + w) {A_v, A_w} = (v - w) · 4 z_K(-v²) z_G(-w²) Π`.

It holds for all real `w`, including `w = ±v`, and needs no simplicity of the root `v`.
Proof: by `intertwine` at `-w` and at `w` the factor `T(∓w)` moves across `A_v`, producing the
factor `(v - w)/(v + w)`, and `{A_v, χ} = 4 z_K(-v²) Π` (`mode_anticomm_root`) is inserted;
finally `Π T(-w) T(w) = z_G(-w²) Π`. -/
theorem mode_anticomm_mode (S : H.ModeSector) (hclaw : G.IsClawFree)
    (hKs : G.IsSimplicialClique Ks) {v : ℝ} (hv : v ≠ 0)
    (hroot : S.zG.eval (-v ^ 2) = 0) (w : ℝ) :
    (v + w) • (S.mode v * S.mode w + S.mode w * S.mode v) =
      ((v - w) * (4 * S.zK.eval (-v ^ 2) * S.zG.eval (-w ^ 2))) • S.Pi := by
  have h1 : (v - w) • (H.frustration.transfer ∅ (-w) * S.mode v) =
      (v + w) • (S.mode v * H.frustration.transfer ∅ (-w)) := by
    have h := S.intertwine hclaw hKs hv hroot (-w)
    rwa [← sub_eq_add_neg, sub_neg_eq_add] at h
  have h2 := S.intertwine hclaw hKs hv hroot w
  have key := anticomm_sandwich_algebra S.Pi (H.frustration.transfer ∅ (-w))
    (H.frustration.transfer ∅ w) H.root (S.mode v) v w
    (S.Pi_comm_transfer (-w)).eq S.Pi_comm_root.eq (S.Pi_mul_mode v).1 (S.Pi_mul_mode v).2 h1 h2
  have hmode : S.mode w = S.Pi * H.frustration.transfer ∅ (-w) * H.root *
      H.frustration.transfer ∅ w := rfl
  have hZs := S.Z_scalar (-w)
  rw [neg_neg, neg_sq] at hZs
  have hZ : H.frustration.transfer ∅ (-w) * (4 * S.zK.eval (-v ^ 2)) • S.Pi *
      H.frustration.transfer ∅ w = (4 * S.zK.eval (-v ^ 2) * S.zG.eval (-w ^ 2)) • S.Pi := by
    rw [mul_smul_comm, smul_mul_assoc, ← (S.Pi_comm_transfer (-w)).eq, mul_assoc, hZs, smul_smul]
  rw [hmode, key, S.mode_anticomm_root hclaw hKs hroot, hZ, smul_smul]

/-- `A_{-w} = Π T(w) χ T(-w)`: the mode at `-w` is the sandwich `Π T(w) χ T(-w)` that appears
in v1's `{ψ_{+j}, T(u) χ T(-u)}` (L2077). -/
theorem mode_neg_eq (S : H.ModeSector) (w : ℝ) :
    S.mode (-w) = S.Pi * H.frustration.transfer ∅ w * H.root *
      H.frustration.transfer ∅ (-w) := by
  unfold mode
  rw [neg_neg]

/-- **Unnormalised key identity, second form** (v1 L2077-2079 and L2085-2098): if `v ≠ 0` and
`z_G(-v²) = 0`, then for every real `w`

`(v - w) {A_v, Π T(w) χ T(-w)} = (v + w) · 4 z_K(-v²) z_G(-w²) Π`,

where `Π T(w) χ T(-w) = A_{-w}` (`mode_neg_eq`).  This is `mode_anticomm_mode` at `-w`. -/
theorem mode_anticomm_mode_neg_arg (S : H.ModeSector) (hclaw : G.IsClawFree)
    (hKs : G.IsSimplicialClique Ks) {v : ℝ} (hv : v ≠ 0)
    (hroot : S.zG.eval (-v ^ 2) = 0) (w : ℝ) :
    (v - w) • (S.mode v * S.mode (-w) + S.mode (-w) * S.mode v) =
      ((v + w) * (4 * S.zK.eval (-v ^ 2) * S.zG.eval (-w ^ 2))) • S.Pi := by
  have h := S.mode_anticomm_mode hclaw hKs hv hroot (-w)
  rwa [← sub_eq_add_neg, sub_neg_eq_add, neg_sq] at h

/-- `w ↦ A_{-w}` is a polynomial map: `A_{-w} = Π T(w) χ T(-w)`. -/
theorem isPolyMap_mode_neg (S : H.ModeSector) :
    Polynomial.IsPolyMap (fun w : ℝ => S.mode (-w)) := by
  have e : (fun w : ℝ => S.mode (-w)) = fun w : ℝ => S.Pi * H.frustration.transfer ∅ w * H.root *
      H.frustration.transfer ∅ (-w) := funext (fun w => S.mode_neg_eq w)
  rw [e]
  exact (((Polynomial.IsPolyMap.const S.Pi).mul (H.frustration.isPolyMap_transfer ∅)).mul
    (Polynomial.IsPolyMap.const H.root)).mul (H.frustration.isPolyMap_transfer_neg ∅)

/-- **Anticommutator of `A_v` and `A_{-v}`** (v1 Lemma 14 at `j = k`, L2085-2104, with
the limit `u → u_j` of v1 L2084 replaced by an exact derivative identity): if `v ≠ 0` and
`z_G(-v²) = 0` then

`{A_v, A_{-v}} = 16 v² z_K(-v²) z_G'(-v²) Π`.

No simplicity of the root `v` is assumed (if it is a multiple root then `z_G'(-v²) = 0` and
the anticommutator vanishes).  Proof: `mode_anticomm_mode_neg_arg` says
`(v - w) F(w) = (v + w) 4 z_K(-v²) z_G(-w²) Π` with `F(w) = {A_v, A_{-w}}` a polynomial in `w`
with coefficients in `A`; `Polynomial.IsPolyMap.apply_eq_neg_derivative` gives
`F(v) = -∂_w[(v + w) 4 z_K(-v²) z_G(-w²)]_{w = v} Π`, and `z_G(-v²) = 0` leaves
`16 v² z_K(-v²) z_G'(-v²) Π`. -/
theorem mode_anticomm_mode_neg (S : H.ModeSector) (hclaw : G.IsClawFree)
    (hKs : G.IsSimplicialClique Ks) {v : ℝ} (hv : v ≠ 0)
    (hroot : S.zG.eval (-v ^ 2) = 0) :
    S.mode v * S.mode (-v) + S.mode (-v) * S.mode v =
      (16 * v ^ 2 * S.zK.eval (-v ^ 2) * (Polynomial.derivative S.zG).eval (-v ^ 2)) • S.Pi := by
  have hF : Polynomial.IsPolyMap (fun w : ℝ => S.mode v * S.mode (-w) + S.mode (-w) * S.mode v) :=
    ((Polynomial.IsPolyMap.const (S.mode v)).mul S.isPolyMap_mode_neg).add
      (S.isPolyMap_mode_neg.mul (Polynomial.IsPolyMap.const (S.mode v)))
  set g : Polynomial ℝ := Polynomial.C (4 * S.zK.eval (-v ^ 2)) *
    ((Polynomial.C v + Polynomial.X) * S.zG.comp (-(Polynomial.X ^ 2))) with hg
  have hgeval : ∀ w : ℝ, g.eval w = (v + w) * (4 * S.zK.eval (-v ^ 2) * S.zG.eval (-w ^ 2)) := by
    intro w
    simp only [hg, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_pow]
    ring
  have h := hF.apply_eq_neg_derivative v g S.Pi (fun w => by
    rw [hgeval]
    exact S.mode_anticomm_mode_neg_arg hclaw hKs hv hroot w)
  have hd : (Polynomial.derivative g).eval v =
      -(16 * v ^ 2 * S.zK.eval (-v ^ 2) * (Polynomial.derivative S.zG).eval (-v ^ 2)) := by
    simp only [hg, Polynomial.derivative_mul, Polynomial.derivative_C, Polynomial.derivative_add,
      Polynomial.derivative_X, Polynomial.derivative_comp, Polynomial.derivative_neg,
      Polynomial.derivative_X_pow, zero_mul, zero_add, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_comp, Polynomial.eval_neg,
      Polynomial.eval_pow, Polynomial.eval_one]
    rw [hroot]
    norm_num
    ring
  rw [h, hd, neg_smul, neg_neg]

/-- **Two distinct roots anticommute**: if `z_G(-v²) = 0 = z_G(-w²)`, `v ≠ 0` and `v + w ≠ 0`,
then `{A_v, A_w} = 0`.  This is `mode_anticomm_mode` with the right-hand side killed by
`z_G(-w²) = 0`; it covers `{ψ_j^+, ψ_k^-}` for `j ≠ k` (`w = -u_k`) and `{ψ_j^+, ψ_k^+}`
(`w = u_k`). -/
theorem mode_anticomm_mode_eq_zero (S : H.ModeSector) (hclaw : G.IsClawFree)
    (hKs : G.IsSimplicialClique Ks) {v w : ℝ} (hv : v ≠ 0)
    (hroot : S.zG.eval (-v ^ 2) = 0) (hw : S.zG.eval (-w ^ 2) = 0) (hvw : v + w ≠ 0) :
    S.mode v * S.mode w + S.mode w * S.mode v = 0 := by
  have h := S.mode_anticomm_mode hclaw hKs hv hroot w
  rw [hw, mul_zero, mul_zero, zero_smul] at h
  exact (smul_eq_zero.mp h).resolve_left hvw

/-! ### Canonical anticommutation relations of the normalised modes -/

namespace Nondegenerate

variable {S : H.ModeSector}

/-- `N_j² = 16 u_j² z_K(-u_j²) z_G'(-u_j²)` (the radicand is positive). -/
theorem N_sq (D : S.Nondegenerate) (j : Fin D.r) :
    D.N j ^ 2 = 16 * D.u j ^ 2 *
      (S.zK.eval (-(D.u j) ^ 2) * (Polynomial.derivative S.zG).eval (-(D.u j) ^ 2)) := by
  unfold N
  rw [mul_pow, mul_pow, Real.sq_sqrt (D.radicand_pos j).le]
  ring

/-- **`{ψ_j^+, ψ_k^-} = δ_{jk} Π`** (v1 Lemma 14, `LadderAnticommutationRelations`, L1306-1313;
proof L2058-2104), within one sector.  The cross-sector factor `δ_{J,J'}` is immediate from
`Π_J Π_{J'} = 0` and is not part of this statement.

For `j ≠ k` the anticommutator is `0` by `mode_anticomm_mode_eq_zero` (`u_j ≠ u_k`); for `j = k`
it is `16 u_j² z_K z_G' Π / N_j² = Π` by `mode_anticomm_mode_neg` (the exact form of v1's limit
`u → u_j`) and the normalisation `N_j² = 16 u_j² z_K(-u_j²) z_G'(-u_j²)`.

The premises beyond the manuscript setup are the non-degeneracy data `D` (which v1 uses
silently; see `ModeSector.Nondegenerate`), `hclaw` and `hKs`. -/
theorem ladder_plus_minus (D : S.Nondegenerate) (hclaw : G.IsClawFree)
    (hKs : G.IsSimplicialClique Ks) (j k : Fin D.r) :
    D.psiPlus j * D.psiMinus k + D.psiMinus k * D.psiPlus j = if j = k then S.Pi else 0 := by
  unfold psiPlus psiMinus
  rw [smul_anticomm_smul]
  by_cases hjk : j = k
  · subst hjk
    rw [if_pos rfl, S.mode_anticomm_mode_neg hclaw hKs (D.u_pos j).ne' (D.zG_eval_root j),
      smul_smul]
    have hN := D.N_sq j
    have hN0 := D.N_ne_zero j
    have hu := (D.u_pos j).ne'
    have : (D.N j)⁻¹ * (D.N j)⁻¹ * (16 * D.u j ^ 2 * S.zK.eval (-(D.u j) ^ 2) *
        (Polynomial.derivative S.zG).eval (-(D.u j) ^ 2)) = 1 := by
      rw [mul_assoc (16 * D.u j ^ 2), ← hN]
      field_simp
    rw [this, one_smul]
  · rw [if_neg hjk, S.mode_anticomm_mode_eq_zero hclaw hKs (D.u_pos j).ne' (D.zG_eval_root j)
      (by rw [neg_sq]; exact D.zG_eval_root k)
      (by
        intro h
        apply hjk
        apply D.u_injective
        linarith),
      smul_zero]

/-- **`{ψ_j^+, ψ_k^+} = 0`** (not stated in v1 but needed for the canonical anticommutation
relations).  It is `mode_anticomm_mode_eq_zero` at `v = u_j`, `w = u_k`, where `u_j + u_k > 0`. -/
theorem ladder_plus_plus (D : S.Nondegenerate) (hclaw : G.IsClawFree)
    (hKs : G.IsSimplicialClique Ks) (j k : Fin D.r) :
    D.psiPlus j * D.psiPlus k + D.psiPlus k * D.psiPlus j = 0 := by
  unfold psiPlus
  rw [smul_anticomm_smul, S.mode_anticomm_mode_eq_zero hclaw hKs (D.u_pos j).ne'
    (D.zG_eval_root j) (D.zG_eval_root k) (by have := D.u_pos j; have := D.u_pos k; positivity),
    smul_zero]

/-- **`{ψ_j^-, ψ_k^-} = 0`**, the adjoint of `ladder_plus_plus` (`(ψ_j^+)† = ψ_j^-`). -/
theorem ladder_minus_minus (D : S.Nondegenerate) (hclaw : G.IsClawFree)
    (hKs : G.IsSimplicialClique Ks) (j k : Fin D.r) :
    D.psiMinus j * D.psiMinus k + D.psiMinus k * D.psiMinus j = 0 := by
  have h := congrArg star (D.ladder_plus_plus hclaw hKs j k)
  rw [star_add, star_mul, star_mul, D.star_psiPlus, D.star_psiPlus, star_zero] at h
  rw [← h, add_comm]

end Nondegenerate

end ModeSector
end SimplicialModeHamiltonian
end SimpleGraph
