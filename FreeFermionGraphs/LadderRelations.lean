import FreeFermionGraphs.CliqueDeletionIdentity
import FreeFermionGraphs.IncognitoModes
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.Real.Sqrt

/-!
# Normalised incognito modes: the anticommutator with `χ` and the adjoint relation

Manuscript (arXiv 2305.15625 v1), proof of Lemma 14 (`LadderAnticommutationRelations`,
L2085-2098, with the normalisation `N_{J,j}` at L2097) and the passage from the
commutator `[ψ_{J,+j}, ψ_{J,-j}]` of Lemma 15 (L1315) to the form `[ψ_j, ψ_j^†]` of
Theorem 2 (L1254).  In the numbering of the revised manuscript used by the repository,
v1 Lemma 14 is "Lemma 4" and v1 Lemma 15 is "Lemma 5".

## Setting

`H` is a `SimplicialModeHamiltonian` and `S : H.ModeSector` a mode sector (see
`IncognitoModes`), with sector polynomials `z_G = S.zG` and `z_K = S.zK`
(v1's `Z_{G,J}` and `Z_{G∖Ks,J}`).  `S.mode v = A_v = Π T(-v) χ T(v)` is the unnormalised
incognito mode.

## Main declarations

* `ModeSector.mode_anticomm_root` : if `z_G(-v²) = 0` then
  `A_v χ + χ A_v = 4 z_K(-v²) Π`  (v1 L2093, `{ψ_{+j}, χ} = 4 Π Z_{G∖Ks}(-u²)/N`);
* `ModeSector.star_mode` : `A_v† = A_{-v}` for real `v`;
* `ModeSector.Nondegenerate` : non-degeneracy data of a sector, namely `r` distinct
  positive reals `u_j` with `z_G = ∏_j (1 + x/u_j²)` and
  `z_K(-u_j²) z_G'(-u_j²) > 0`;
* `Nondegenerate.N`, `Nondegenerate.psiPlus`, `Nondegenerate.psiMinus` : the
  normalisation `N_j = 4 u_j √(z_K(-u_j²) z_G'(-u_j²))` of v1 L2097 and the normalised
  modes `ψ_j^± = A_{±u_j}/N_j` (v1 Definition 9's `ψ_{J,j}` and the undefined `ψ_{J,-j}`);
* `Nondegenerate.star_psiPlus` : `(ψ_j^+)† = ψ_j^-`, which supplies v1's unproved passage from
  `[ψ_+, ψ_-]` (Lemma 15) to `[ψ, ψ†]` (Theorem 2);
* `Nondegenerate.psiPlus_anticomm_root` : `ψ_j^+ χ + χ ψ_j^+ = (4 z_K(-u_j²)/N_j) Π`.

## Deviations from v1

* v1 proves `{A_v, χ}` by "applying Eq. (`transfermatrixrecursion`) again" (L2088-2093);
  that step needs the cross identity `A(-u) B(u) = B(-u) A(u)`, which v1 does not prove.  It is
  supplied by `root_sandwich_anticomm` of `CliqueDeletionIdentity`
  (`T(-v) χ T(v) χ + χ T(-v) χ T(v) = 4 Z_{G∖Ks}(-v²) - 2 Z_G(-v²)`), and `Π Z_G(-v²) = 0`
  kills the second term.
* v1 never proves that the roots `u_{J,j}` are real, positive and simple nor that
  `Z_{G∖Ks}(-u²) Z_G'(-u²) > 0`; all of these are needed for `N_{J,j}` to be a positive real and for
  `ψ_{J,-j} = ψ_{J,j}^†`.  At this abstract level they are explicit hypotheses collected
  in `ModeSector.Nondegenerate`, not provable in a generic ring; they are hypotheses
  on the sector, not claims about the modes, so no field of `Nondegenerate` assumes a conclusion
  of this module.  In the final solution they are derived from the single no-common-root hypothesis
  on `Z_{G,J}` and `Z_{G∖Ks,J}`.
* v1 writes the generating polynomial as `z_G(x) = ∏_j (1 + x/u_j²)` implicitly (L2129); here this is the field
  `zG_eq`, with `(u_j⁻¹)²` for `1/u_j²`.
* `N_j` uses `Real.sqrt`, so this module imports `Mathlib.Analysis.Real.Sqrt`.
* `mode_anticomm_root` and `star_mode` hold for every real `v` (not only positive roots);
  `star_mode` needs neither a root hypothesis nor claw-freeness.
* Beyond the stated target, the module records `N_j > 0`, that `-u_j²` is a root of `z_G`
  (`zG_eval_root`), `(ψ_j^-)† = ψ_j^+`, `Π ψ_j^± = ψ_j^± = ψ_j^± Π`, and the normalised form
  `ψ_j^+ χ + χ ψ_j^+ = (4 z_K(-u_j²)/N_j) Π`; the normalisation `{ψ_j^+, ψ_j^-} = Π` itself is
  the next step (it needs the intertwining relation and the derivative identity for `z_G`).
-/

open Set Finset
open scoped BigOperators

universe u w
variable {V : Type u}

namespace SimpleGraph
namespace SimplicialModeHamiltonian

variable {G : SimpleGraph V} {Ks : Set V} {A : Type w}
variable [Ring A] [StarRing A] [Algebra ℝ A] [StarModule ℝ A]
variable [Fintype V] [DecidableEq V]

/-- The transfer operator `T_{G∖W}(u)` is Hermitian for real `u`: it is a real combination of
the Hermitian charges `Q_{G∖W}^(k)`. -/
theorem isSelfAdjoint_transfer (H : G.SimplicialModeHamiltonian Ks A) (W : Set V) (u : ℝ) :
    IsSelfAdjoint (H.frustration.transfer W u) := by
  unfold IsSelfAdjoint PauliFrustrationRepresentation.transfer
  rw [star_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [star_smul, star_trivial, (H.isSelfAdjoint_deletedCharge W k).star_eq]

namespace ModeSector

variable {H : G.SimplicialModeHamiltonian Ks A}

/-- **Anticommutator of a mode with the simplicial mode** (v1 L2088-2093, the display
`{ψ_{J,+j}, χ} = 4 Π_J Z_{G∖Ks}(-u²)/N`): if `z_G(-v²) = 0` then
`A_v χ + χ A_v = 4 z_K(-v²) Π`.

`Π` commutes with `χ`, so `A_v χ + χ A_v = Π (T(-v) χ T(v) χ + χ T(-v) χ T(v))`.  By
`root_sandwich_anticomm` (the step v1 calls "applying Eq. (`transfermatrixrecursion`)
again", whose cross identity v1 does not prove) the bracket is
`4 Z_{G∖Ks}(-v²) - 2 Z_G(-v²)`, hence the product with `Π` is
`4 z_K(-v²) Π - 2 z_G(-v²) Π`, and the second term vanishes at a root. -/
theorem mode_anticomm_root (S : H.ModeSector) (hclaw : G.IsClawFree)
    (hKs : G.IsSimplicialClique Ks) {v : ℝ} (hroot : S.zG.eval (-v ^ 2) = 0) :
    S.mode v * H.root + H.root * S.mode v = (4 * S.zK.eval (-v ^ 2)) • S.Pi := by
  have key : H.frustration.transfer ∅ (-v) * H.root * H.frustration.transfer ∅ v * H.root +
      H.root * H.frustration.transfer ∅ (-v) * H.root * H.frustration.transfer ∅ v =
      (4 : ℝ) • (H.frustration.transfer Ks v * H.frustration.transfer Ks (-v)) -
        (2 : ℝ) • (H.frustration.transfer ∅ v * H.frustration.transfer ∅ (-v)) :=
    H.operator.root_sandwich_anticomm hclaw hKs H.root_sq v
  have hPχ : S.Pi * H.root = H.root * S.Pi := S.Pi_comm_root.eq
  have h1 : S.mode v * H.root + H.root * S.mode v =
      S.Pi * (H.frustration.transfer ∅ (-v) * H.root * H.frustration.transfer ∅ v * H.root +
        H.root * H.frustration.transfer ∅ (-v) * H.root * H.frustration.transfer ∅ v) := by
    unfold mode
    have e : H.root * (S.Pi * H.frustration.transfer ∅ (-v) * H.root *
        H.frustration.transfer ∅ v) =
        S.Pi * (H.root * H.frustration.transfer ∅ (-v) * H.root *
          H.frustration.transfer ∅ v) := by
      rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc,
        ← hPχ]
    rw [e, mul_add]
    simp only [mul_assoc]
  rw [h1, key, mul_sub, mul_smul_comm, mul_smul_comm, S.ZK_scalar v, S.Z_scalar v, hroot,
    zero_smul, smul_zero, sub_zero, smul_smul]

/-- **The adjoint of a mode** (v1 Theorem 2 form `[ψ, ψ†]`, L1254): for real `v`,
`A_v† = A_{-v}`.  Indeed `T(u)` is Hermitian for real `u`, `χ` and `Π` are Hermitian, and `Π`
commutes with `T` and `χ`, so
`(Π T(-v) χ T(v))† = T(v) χ T(-v) Π = Π T(v) χ T(-v) = A_{-v}`.
Neither claw-freeness nor a root hypothesis is needed. -/
theorem star_mode (S : H.ModeSector) (v : ℝ) : star (S.mode v) = S.mode (-v) := by
  unfold mode
  have hT : ∀ u : ℝ, star (H.frustration.transfer ∅ u) = H.frustration.transfer ∅ u :=
    fun u => (H.isSelfAdjoint_transfer ∅ u).star_eq
  have hχ : star H.root = H.root := (H.term_selfAdjoint none).star_eq
  rw [star_mul, star_mul, star_mul, hT, hT, hχ, S.Pi_selfAdjoint.star_eq, neg_neg]
  have e1 : H.frustration.transfer ∅ v * H.root * H.frustration.transfer ∅ (-v) * S.Pi =
      S.Pi * H.frustration.transfer ∅ v * H.root * H.frustration.transfer ∅ (-v) := by
    have c1 : H.frustration.transfer ∅ (-v) * S.Pi = S.Pi * H.frustration.transfer ∅ (-v) :=
      (S.Pi_comm_transfer (-v)).eq.symm
    have c2 : H.root * S.Pi = S.Pi * H.root := S.Pi_comm_root.eq.symm
    have c3 : H.frustration.transfer ∅ v * S.Pi = S.Pi * H.frustration.transfer ∅ v :=
      (S.Pi_comm_transfer v).eq.symm
    calc H.frustration.transfer ∅ v * H.root * H.frustration.transfer ∅ (-v) * S.Pi
        = H.frustration.transfer ∅ v * H.root * (H.frustration.transfer ∅ (-v) * S.Pi) := by
          simp only [mul_assoc]
      _ = H.frustration.transfer ∅ v * (H.root * S.Pi) * H.frustration.transfer ∅ (-v) := by
          rw [c1]; simp only [mul_assoc]
      _ = (H.frustration.transfer ∅ v * S.Pi) * H.root * H.frustration.transfer ∅ (-v) := by
          rw [c2]; simp only [mul_assoc]
      _ = S.Pi * H.frustration.transfer ∅ v * H.root * H.frustration.transfer ∅ (-v) := by
          rw [c3]
  simpa only [mul_assoc] using e1

/-! ### Non-degeneracy data and the normalised modes -/

/-- **Non-degeneracy data** of a mode sector `S` (v1 L2085-2098 and L2129): the sector
polynomial `z_G = Z_{G,J}` has `r` distinct positive real roots, `z_G(x) = ∏_j (1 + x/u_j²)`
(so the roots in `x` are `-u_j²`), and the radicands `z_K(-u_j²) z_G'(-u_j²)` of the
normalisations `N_j` are positive.

These are explicit hypotheses about the sector at this abstract level (they are not provable
in a generic ring); v1 uses them silently.  No field mentions an incognito mode.  For matrix
models they are derived from the single hypothesis that `Z_{G,J}` and `Z_{G∖Ks,J}` have no
common root.  `r` stands in for `α(G)`; it equals `deg z_G`. -/
structure Nondegenerate (S : H.ModeSector) where
  /-- The number `r` of modes. -/
  r : ℕ
  /-- The mode energies `u_j`. -/
  u : Fin r → ℝ
  /-- Each `u_j` is positive. -/
  u_pos : ∀ j, 0 < u j
  /-- The `u_j` are pairwise distinct. -/
  u_injective : Function.Injective u
  /-- `z_G(x) = ∏_j (1 + x/u_j²)`. -/
  zG_eq : S.zG = ∏ j, (1 + Polynomial.C ((u j)⁻¹ ^ 2) * Polynomial.X)
  /-- The radicand of `N_j` is positive: `z_K(-u_j²) z_G'(-u_j²) > 0`. -/
  radicand_pos : ∀ j, 0 < S.zK.eval (-(u j) ^ 2) *
    (Polynomial.derivative S.zG).eval (-(u j) ^ 2)

namespace Nondegenerate

variable {S : H.ModeSector}

/-- The normalisation `N_j = 4 u_j √(z_K(-u_j²) z_G'(-u_j²))` (v1 L2097, first defined inside
the proof of Lemma 14, after its use in Definition 9 and Theorem 2). -/
noncomputable def N (D : S.Nondegenerate) (j : Fin D.r) : ℝ :=
  4 * D.u j * Real.sqrt (S.zK.eval (-(D.u j) ^ 2) *
    (Polynomial.derivative S.zG).eval (-(D.u j) ^ 2))

/-- The normalised raising mode `ψ_j^+ = A_{u_j}/N_j = N_j⁻¹ Π T(-u_j) χ T(u_j)`
(v1 Definition 9's `ψ_{J,j}`). -/
noncomputable def psiPlus (D : S.Nondegenerate) (j : Fin D.r) : A :=
  (D.N j)⁻¹ • S.mode (D.u j)

/-- The normalised lowering mode `ψ_j^- = A_{-u_j}/N_j = N_j⁻¹ Π T(u_j) χ T(-u_j)`: the
`ψ_{J,-j}` that v1 uses (L1289, L1310) without defining it. -/
noncomputable def psiMinus (D : S.Nondegenerate) (j : Fin D.r) : A :=
  (D.N j)⁻¹ • S.mode (-(D.u j))

/-- `N_j > 0`: `u_j > 0` and the radicand is positive. -/
theorem N_pos (D : S.Nondegenerate) (j : Fin D.r) : 0 < D.N j := by
  unfold N
  have h1 := D.u_pos j
  have h2 := Real.sqrt_pos.mpr (D.radicand_pos j)
  positivity

/-- `N_j ≠ 0`. -/
theorem N_ne_zero (D : S.Nondegenerate) (j : Fin D.r) : D.N j ≠ 0 :=
  (D.N_pos j).ne'

/-- Each `-u_j²` is a root of `z_G` (from `z_G = ∏_j (1 + x/u_j²)`). -/
theorem zG_eval_root (D : S.Nondegenerate) (j : Fin D.r) :
    S.zG.eval (-(D.u j) ^ 2) = 0 := by
  rw [D.zG_eq, Polynomial.eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
  have hne : D.u j ≠ 0 := (D.u_pos j).ne'
  simp only [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  field_simp
  ring

/-- **`ψ_j^- = (ψ_j^+)†`** (v1: `ψ_{J,-j} = ψ_{J,j}^†`, which v1 uses to pass from the
commutator `[ψ_+, ψ_-]` of Lemma 15 to the `[ψ, ψ†]` of Theorem 2).  It follows from
`star_mode` and the reality of `N_j`. -/
theorem star_psiPlus (D : S.Nondegenerate) (j : Fin D.r) :
    star (D.psiPlus j) = D.psiMinus j := by
  unfold psiPlus psiMinus
  rw [star_smul, star_trivial, S.star_mode]

/-- `(ψ_j^-)† = ψ_j^+`. -/
theorem star_psiMinus (D : S.Nondegenerate) (j : Fin D.r) :
    star (D.psiMinus j) = D.psiPlus j := by
  rw [← D.star_psiPlus j, star_star]

/-- `ψ_j^± ∈ Π A Π`: `Π ψ_j^± = ψ_j^± = ψ_j^± Π`. -/
theorem Pi_mul_psiPlus (D : S.Nondegenerate) (j : Fin D.r) :
    S.Pi * D.psiPlus j = D.psiPlus j ∧ D.psiPlus j * S.Pi = D.psiPlus j := by
  unfold psiPlus
  rw [mul_smul_comm, smul_mul_assoc, (S.Pi_mul_mode _).1, (S.Pi_mul_mode _).2]
  exact ⟨rfl, rfl⟩

/-- `Π ψ_j^- = ψ_j^- = ψ_j^- Π`. -/
theorem Pi_mul_psiMinus (D : S.Nondegenerate) (j : Fin D.r) :
    S.Pi * D.psiMinus j = D.psiMinus j ∧ D.psiMinus j * S.Pi = D.psiMinus j := by
  unfold psiMinus
  rw [mul_smul_comm, smul_mul_assoc, (S.Pi_mul_mode _).1, (S.Pi_mul_mode _).2]
  exact ⟨rfl, rfl⟩

/-- **`{ψ_j^+, χ} = (4 z_K(-u_j²)/N_j) Π`** (v1 L2093-2097, the display before the choice of
`N_{J,j}`), the normalised form of `mode_anticomm_root` at the root `u_j`. -/
theorem psiPlus_anticomm_root (D : S.Nondegenerate) (hclaw : G.IsClawFree)
    (hKs : G.IsSimplicialClique Ks) (j : Fin D.r) :
    D.psiPlus j * H.root + H.root * D.psiPlus j =
      (4 * S.zK.eval (-(D.u j) ^ 2) / D.N j) • S.Pi := by
  unfold psiPlus
  rw [smul_mul_assoc, mul_smul_comm, ← smul_add,
    S.mode_anticomm_root hclaw hKs (D.zG_eval_root j), smul_smul, div_eq_inv_mul]

end Nondegenerate

end ModeSector

end SimplicialModeHamiltonian
end SimpleGraph
