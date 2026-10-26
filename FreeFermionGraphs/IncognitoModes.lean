import FreeFermionGraphs.FundamentalIdentity
import FreeFermionGraphs.ConservedChargesIndependentSets
import FreeFermionGraphs.KrylovMatrixRealization
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Mode sectors, unnormalised incognito modes, and the eigenmode lemma

Manuscript (arXiv 2305.15625 v1) Definition 9 (incognito modes, L596-603),
Lemma 13 (`lemma:commutationrelation`, L1285-1304) and the intertwining relation
`(u_j + u) T(u) ψ_j = (u_j - u) ψ_j T(u)` that v1 derives inside the proof of
Lemma 14 (L2063-2079).  In the numbering of the revised manuscript used by the
repository, v1 Lemma 13 is "Lemma 3".

## Setting

Let `H` be a `SimplicialModeHamiltonian` (the root-adjoined Pauli model of
v1 Definition 8): terms `h_j`, `j ∈ V`, with frustration graph `G`, and the
simplicial mode `χ` attached to the simplicial clique `Ks`.  Write
`T(u) = T_G(u)` for the transfer operator (v1 Definition 5), `Σ = ∑_{j ∈ Ks} h_j`,
and `Z_G(-u²) = T(u) T(-u)` (v1 Definition 7, as in `fundamentalIdentity`).

v1 defines the incognito mode `ψ_{J,j} = N_{J,j}^{-1} Π_J T(-u_{J,j}) χ T(u_{J,j})`
on the mutual eigenspace `Π_J` of the generalised cycle symmetries, for a root
`u_{J,j}` of `Z_{G,J}(-u²)`, and uses `ψ_{J,-j}` (L1289, L1310) without ever
defining it.  Here `ModeSector.mode S v` is the *unnormalised* incognito mode
`A_v := Π T(-v) χ T(v)` for an arbitrary real `v`; the normalisation `N_{J,j}`
of v1 (first defined inside the proof of Lemma 14, L2097, after its use in
Definition 9) is not needed for the results of this module, and
`mode S (-v)` is the missing `ψ_{J,-j}` before normalisation.

## What a sector has to provide

A `ModeSector` bundles exactly what v1 uses about a joint eigenprojection `Π_J`
of the generalised cycle symmetries, and nothing else:

* `Pi` is a self-adjoint idempotent (an orthogonal projection);
* `Pi` commutes with every charge `Q_G^(k)` (Theorem 1(ii)), hence with the
  Hamiltonian `H = Q_G^(1)` and with every transfer operator `T_G(u)`, and with
  `χ`;
* `Pi Z_G(-u²) = z_G(-u²) Pi` and `Pi Z_{G∖Ks}(-u²) = z_K(-u²) Pi` for real `u`,
  for real polynomials `z_G`, `z_K` (the sector polynomials of v1, which v1
  writes `Z_{G,J}` and `Z_{G∖Ks,J}`).

`Pi` is deliberately **not** assumed to commute with the individual terms `h_j`
(it does not, in general), nor with the deleted charges `Q_{G∖Ks}^(k)`.  v1's proof
of Lemma 13 does not use such commutations, and neither do the proofs below.
The fields are properties of the projections `Π_J` that the exact solution
establishes elsewhere (Theorem 1(ii), the commutation of `χ`, and the scalar
action of `Z_G`, `Z_{G∖Ks}` on a sector); none of them is a claim proved in this
module.  No field mentions an incognito mode or a root of `z_G`: the roots enter
only through the hypotheses `hroot` of the theorems.

## Main declarations

* `ModeSector` : the data above;
* `ModeSector.mode` : `A_v = Π T(-v) χ T(v)`;
* `ModeSector.eigenmode` : v1 Lemma 13 for `+v`: if `v ≠ 0` and `z_G(-v²) = 0`
  then `[H, A_v] = (2/v) A_v`; `ModeSector.eigenmode_neg` is the case `-v`,
  `[H, A_{-v}] = -(2/v) A_{-v}`.  With the single-particle energy `ε = 1/v`
  these are `[H, ψ_{±j}] = ± 2 ε ψ_{±j}`.
* `ModeSector.intertwine` : `(v + u) T(u) A_v = (v - u) A_v T(u)` for all `u`;
* `ModeSector.transfer_mul_mode_eq_zero` : `T(v) A_v = 0 = A_v T(-v)`;
* `ModeSector.Pi_mul_mode` : `Π A_v = A_v = A_v Π`;
* `ModeSector.mode_eq_smul` : `A_v = v Π T(-v) (Σ χ) T(v)` when `z_G(-v²) = 0` (the
  Fundamental Identity multiplied by `Π`);
* `SimplicialModeHamiltonian.transfer_commute_transfer`,
  `SimplicialModeHamiltonian.hamiltonian_commute_transfer` : `[T(u), T(v)] = 0` and
  `[H, T(u)] = 0` for claw-free `G`, from `deletedCharge_commute`.

## Deviations from v1

* v1 states Lemma 13 for an "SCF Hamiltonian"; both hypotheses are used here
  (`hclaw` : the frustration graph is claw-free, for the commutation of the
  charges, Theorem 1(i); `hKs` : `Ks` is a simplicial clique, for the Fundamental
  Identity), and are explicit hypotheses of the theorems, not fields.
* v1's proof applies the Fundamental Identity and "the definition of `u_{J,j}`
  that `Π_J Z_G(-u_{J,j}²) = 0`".  The scalar action `Π Z_G(-v²) = z_G(-v²) Π` is
  the field `Z_scalar`, and the hypothesis is `hroot : z_G(-v²) = 0`.
* The intertwining relation is derived in v1 (L2063-2079) by multiplying with
  `Z_G(-u²)^{-1}`, which needs `Z_G ψ = ψ Z_G` on the sector and fails at
  `u = ± u_j`.  The proof here uses the reduced Fundamental Identity directly
  and needs no inversion: it holds for all real `u`, including `u = ± v`.
* The spectral parameter `v` need not be positive: the statements hold for every
  real `v ≠ 0` (v1's `ε = 1/u` tacitly takes `u > 0`).
* The commutation `[T(u), T(v)] = 0` and `[H, T(u)] = 0` (v1 Theorem 1(i), in the form of
  `deletedCharge_commute`) is passed from the charges to the transfer operators by the
  elementary lemmas `commute_transfer_of_commute_deletedCharge` and
  `transfer_commute_transfer_of_deletedCharge_commute`, which are proved here because the
  corollary for transfer operators is not yet in the repository.
* The relation `intertwine` has the hypothesis `v ≠ 0` in its signature, but does not use
  it (see its docstring).
-/

open Set Finset
open scoped BigOperators

universe u w
variable {V : Type u}

namespace SimpleGraph
namespace PauliFrustrationRepresentation

variable {G : SimpleGraph V} {A : Type w} [Ring A]
variable [Fintype V] [DecidableEq V] {R : Type*} [CommRing R] [Algebra R A]

/-- An operator commuting with every deleted charge `Q_{G∖W}^(k)` commutes with the
transfer operator `T_{G∖W}(u) = ∑_k (-u)^k Q_{G∖W}^(k)` (v1 Definition 5, L532-540). -/
theorem commute_transfer_of_commute_deletedCharge
    (H : G.PauliFrustrationRepresentation A) (W : Set V) {x : A}
    (hx : ∀ k, Commute x (H.deletedCharge W k)) (u : R) :
    Commute x (H.transfer W u) := by
  unfold transfer
  exact Commute.sum_right _ _ _ (fun k _ => (hx k).smul_right _)

/-- If the deleted charges `Q_{G∖W}^(k)` pairwise commute (Theorem 1(i), v1 L864-873;
for a claw-free `G` this is `deletedCharge_commute`), the transfer operators
`T_{G∖W}(u)` and `T_{G∖W}(v)` commute. -/
theorem transfer_commute_transfer_of_deletedCharge_commute
    (H : G.PauliFrustrationRepresentation A) (W : Set V)
    (hc : ∀ s t, Commute (H.deletedCharge W s) (H.deletedCharge W t)) (u v : R) :
    Commute (H.transfer W u) (H.transfer W v) := by
  unfold transfer
  refine Commute.sum_left _ _ _ (fun k _ => ?_)
  exact (H.commute_transfer_of_commute_deletedCharge W (fun t => hc k t) v).smul_left _

end PauliFrustrationRepresentation

namespace SimplicialModeHamiltonian

variable {G : SimpleGraph V} {Ks : Set V} {A : Type w}
variable [Ring A] [StarRing A] [Algebra ℝ A] [StarModule ℝ A]
variable [Fintype V] [DecidableEq V]

/-- The reduced Fundamental Identity (v1 Lemma 12, L2021-2023) at `-u`, in the form used by
the intertwining relation: `(1 - uΣ) χ T(u) = T(u) (1 + uΣ) χ`. -/
theorem fundamentalIdentity_reduced_neg (H : G.SimplicialModeHamiltonian Ks A)
    (hKs : G.IsSimplicialClique Ks) (u : ℝ) :
    (1 - u • ∑ j ∈ verticesOfSet Ks, H.frustration.term j) * H.root *
        H.frustration.transfer ∅ u =
      H.frustration.transfer ∅ u *
        ((1 + u • ∑ j ∈ verticesOfSet Ks, H.frustration.term j) * H.root) := by
  have h := H.operator.fundamentalIdentity_reduced hKs (-u)
  simp only [neg_neg, neg_smul, ← sub_eq_add_neg, sub_neg_eq_add] at h
  exact h

/-- The transfer operators `T_G(u)` and `T_G(v)` commute for a claw-free frustration graph
(v1 Theorem 1(i), L864-873, via `deletedCharge_commute`). -/
theorem transfer_commute_transfer (H : G.SimplicialModeHamiltonian Ks A)
    (hclaw : G.IsClawFree) (u v : ℝ) :
    Commute (H.frustration.transfer ∅ u) (H.frustration.transfer ∅ v) :=
  H.frustration.transfer_commute_transfer_of_deletedCharge_commute ∅
    (fun s t => H.frustration.deletedCharge_commute hclaw ∅ s t) u v

/-- The Hamiltonian commutes with the transfer operators `T_G(u)` for a claw-free
frustration graph (`H = Q_G^(1)` and v1 Theorem 1(i)). -/
theorem hamiltonian_commute_transfer (H : G.SimplicialModeHamiltonian Ks A)
    (hclaw : G.IsClawFree) (u : ℝ) :
    Commute H.frustration.hamiltonian (H.frustration.transfer ∅ u) :=
  H.frustration.commute_transfer_of_commute_deletedCharge ∅
    (fun k => H.frustration.hamiltonian_commute_charge hclaw k) u

/-- A *mode sector* of the simplicial-mode Hamiltonian `H`: a self-adjoint idempotent
`Π` standing for the joint eigenprojection `Π_J` of the generalised cycle symmetries
(v1 Section 2, L577-606), together with the real polynomials `z_G`, `z_K` by which
`Z_G(-u²) = T_G(u) T_G(-u)` and `Z_{G∖Ks}(-u²) = T_{G∖Ks}(u) T_{G∖Ks}(-u)` act on
the sector (v1 writes `Z_{G,J}` and `Z_{G∖Ks,J}`).

`Π` commutes with every charge `Q_G^(k)` (v1 Theorem 1(ii)) and with the simplicial
mode `χ`.  It is *not* assumed to commute with the individual terms `h_j` or with the
deleted charges `Q_{G∖Ks}^(k)`.  These fields are the properties of `Π_J` that the
exact solution establishes separately; no field concerns incognito modes. -/
structure ModeSector (H : G.SimplicialModeHamiltonian Ks A) where
  /-- The sector projection `Π`. -/
  Pi : A
  /-- `Π² = Π`. -/
  Pi_idem : Pi * Pi = Pi
  /-- `Π† = Π`. -/
  Pi_selfAdjoint : IsSelfAdjoint Pi
  /-- `Π` commutes with every charge `Q_G^(k)` (Theorem 1(ii)). -/
  Pi_comm_charge : ∀ k : ℕ, Commute Pi (H.frustration.charge k)
  /-- `Π` commutes with the simplicial mode `χ`. -/
  Pi_comm_root : Commute Pi H.root
  /-- The polynomial `z_G` with `Π Z_G(-u²) = z_G(-u²) Π`. -/
  zG : Polynomial ℝ
  /-- The polynomial `z_K` with `Π Z_{G∖Ks}(-u²) = z_K(-u²) Π`. -/
  zK : Polynomial ℝ
  /-- `Π Z_G(-u²) = z_G(-u²) Π` for all real `u`, where `Z_G(-u²) = T_G(u) T_G(-u)`. -/
  Z_scalar : ∀ u : ℝ,
    Pi * (H.frustration.transfer ∅ u * H.frustration.transfer ∅ (-u)) =
      zG.eval (-u ^ 2) • Pi
  /-- `Π Z_{G∖Ks}(-u²) = z_K(-u²) Π` for all real `u`, where
  `Z_{G∖Ks}(-u²) = T_{G∖Ks}(u) T_{G∖Ks}(-u)`. -/
  ZK_scalar : ∀ u : ℝ,
    Pi * (H.frustration.transfer Ks u * H.frustration.transfer Ks (-u)) =
      zK.eval (-u ^ 2) • Pi

namespace ModeSector

variable {H : G.SimplicialModeHamiltonian Ks A}

/-- The unnormalised incognito mode `A_v = Π T_G(-v) χ T_G(v)` (v1 Definition 9, L596-603,
before dividing by `N_{J,j}`; for `-v` it is the undefined `ψ_{J,-j}` of v1 L1289,
before normalisation). -/
noncomputable def mode (S : H.ModeSector) (v : ℝ) : A :=
  S.Pi * H.frustration.transfer ∅ (-v) * H.root * H.frustration.transfer ∅ v

/-! ### Commutation lemmas -/

/-- `Π` commutes with every transfer operator `T_G(u)`: it commutes with the charges. -/
theorem Pi_comm_transfer (S : H.ModeSector) (u : ℝ) :
    Commute S.Pi (H.frustration.transfer ∅ u) :=
  H.frustration.commute_transfer_of_commute_deletedCharge ∅ (fun k => S.Pi_comm_charge k) u

/-- `Π` commutes with the Hamiltonian `H = Q_G^(1)` (v1 L522). -/
theorem Pi_comm_hamiltonian (S : H.ModeSector) :
    Commute S.Pi H.frustration.hamiltonian := by
  rw [← H.frustration.charge_one]
  exact S.Pi_comm_charge 1

/-! ### Pure algebra of the sandwich -/

/-- The noncommutative algebra behind the intertwining relation.  Here `P = Π T(-v)`,
`a = P χ T(v) = A_v` and `e = P (Σ χ) T(v)`, with `a = v e` (from the Fundamental
Identity and `Π Z_G(-v²) = 0`).  The reduced Fundamental Identity at `-u`,
`(1 - uΣ) χ T(u) = T(u) (1 + uΣ) χ`, sandwiched between `P` and `T(v)`, gives
`a T(u) - u e T(u) = T(u) a + u T(u) e`, hence `(v - u) a T(u) = (v + u) T(u) a`. -/
theorem intertwine_algebra {B : Type*} [Ring B] [Algebra ℝ B]
    (P Tu Tv Sg χ : B) (v u : ℝ)
    (hPT : Commute P Tu) (hTT : Commute Tu Tv)
    (R : (1 - u • Sg) * χ * Tu = Tu * ((1 + u • Sg) * χ))
    (hE : v • (P * (Sg * χ) * Tv) = P * χ * Tv) :
    (v + u) • (Tu * (P * χ * Tv)) = (v - u) • (P * χ * Tv * Tu) := by
  have hL : P * ((1 - u • Sg) * χ * Tu) * Tv =
      P * χ * Tv * Tu - u • (P * (Sg * χ) * Tv * Tu) := by
    have h1 : P * ((1 - u • Sg) * χ * Tu) * Tv =
        P * (1 - u • Sg) * χ * (Tu * Tv) := by simp only [mul_assoc]
    rw [h1, hTT.eq]
    simp only [mul_sub, mul_one, sub_mul, smul_mul_assoc, mul_smul_comm, mul_assoc]
  have hRr : P * (Tu * ((1 + u • Sg) * χ)) * Tv =
      Tu * (P * χ * Tv) + u • (Tu * (P * (Sg * χ) * Tv)) := by
    have h1 : P * (Tu * ((1 + u • Sg) * χ)) * Tv =
        (P * Tu) * ((1 + u • Sg) * χ) * Tv := by simp only [mul_assoc]
    rw [h1, hPT.eq]
    simp only [mul_add, one_mul, add_mul, smul_mul_assoc, mul_smul_comm, mul_assoc]
  have hmain : P * χ * Tv * Tu - u • (P * (Sg * χ) * Tv * Tu) =
      Tu * (P * χ * Tv) + u • (Tu * (P * (Sg * χ) * Tv)) := by
    rw [← hL, ← hRr, R]
  have hv := congrArg (fun x => v • x) hmain
  simp only [smul_sub, smul_add] at hv
  have e1 : v • (u • (P * (Sg * χ) * Tv * Tu)) = u • (P * χ * Tv * Tu) := by
    rw [smul_comm v u, ← smul_mul_assoc, hE]
  have e2 : v • (u • (Tu * (P * (Sg * χ) * Tv))) = u • (Tu * (P * χ * Tv)) := by
    rw [smul_comm v u, ← mul_smul_comm, hE]
  rw [e1, e2] at hv
  rw [add_smul, sub_smul]
  rw [sub_eq_iff_eq_add] at hv
  rw [hv]
  abel

/-- The noncommutative algebra behind `mode_eq_smul`.  With `P = Π T(-v)`: if
`P T(v) = 0` (this is `Π Z_G(-v²) = 0`) and the reduced Fundamental Identity
`(1 - vΣ) χ T(v) = T(v) (1 + vΣ) χ` holds, then `P χ T(v) = v P (Σ χ) T(v)`. -/
theorem mode_algebra {B : Type*} [Ring B] [Algebra ℝ B]
    (P Tv Sg χ : B) (v : ℝ) (hz : P * Tv = 0)
    (hFI : (1 - v • Sg) * χ * Tv = Tv * ((1 + v • Sg) * χ)) :
    P * χ * Tv = v • (P * (Sg * χ) * Tv) := by
  have h := congrArg (fun x => P * x) hFI
  have hR : P * (Tv * ((1 + v • Sg) * χ)) = 0 := by
    rw [← mul_assoc, hz, zero_mul]
  have hL : P * ((1 - v • Sg) * χ * Tv) = P * χ * Tv - v • (P * (Sg * χ) * Tv) := by
    simp only [mul_sub, sub_mul, one_mul, smul_mul_assoc, mul_smul_comm, mul_assoc]
  simp only [hL, hR] at h
  exact sub_eq_zero.mp h

/-! ### The Fundamental Identity on a sector -/

/-- On the sector, the Fundamental Identity and `z_G(-v²) = 0` give
`A_v = v Π T(-v) (Σ χ) T(v)` (v1 L1295-1300: "applying Lemma 12 together with
`Π Z_G(-u_j²) = 0`"). -/
theorem mode_eq_smul (S : H.ModeSector) (hKs : G.IsSimplicialClique Ks) {v : ℝ}
    (hroot : S.zG.eval (-v ^ 2) = 0) :
    S.mode v = v • (S.Pi * H.frustration.transfer ∅ (-v) *
        ((∑ j ∈ verticesOfSet Ks, H.frustration.term j) * H.root) *
        H.frustration.transfer ∅ v) := by
  have hz : S.Pi * (H.frustration.transfer ∅ (-v) * H.frustration.transfer ∅ v) = 0 := by
    have h := S.Z_scalar (-v)
    rw [neg_neg, neg_sq, hroot, zero_smul] at h
    exact h
  exact mode_algebra (S.Pi * H.frustration.transfer ∅ (-v)) (H.frustration.transfer ∅ v) _ _ v
    (by rw [mul_assoc]; exact hz) (H.fundamentalIdentity_reduced_neg hKs v)

/-- Conjugating by operators that commute with `Ham` commutes through the commutator:
`[Ham, a x c] = a [Ham, x] c` when `Ham` commutes with `a` and `c`. -/
theorem algebraCommutator_mul_mul {B : Type*} [Ring B] {Ham a x c : B}
    (ha : Commute Ham a) (hc : Commute Ham c) :
    algebraCommutator Ham (a * x * c) = a * algebraCommutator Ham x * c := by
  unfold algebraCommutator
  have e1 : Ham * (a * x * c) = a * (Ham * x) * c := by
    have : Ham * (a * x * c) = (Ham * a) * x * c := by simp only [mul_assoc]
    rw [this, ha.eq]
    simp only [mul_assoc]
  have e2 : a * x * c * Ham = a * (x * Ham) * c := by
    have : a * x * c * Ham = a * x * (c * Ham) := by simp only [mul_assoc]
    rw [this, ← hc.eq]
    simp only [mul_assoc]
  rw [e1, e2, mul_sub, sub_mul]

/-! ### The eigenmode lemma (v1 Lemma 13) -/

/-- **Eigenmode lemma** (v1 Lemma 13, `lemma:commutationrelation`, L1285-1304; repo
"Lemma 3"), for `+v`.

Let `S` be a mode sector, `Ks` a simplicial clique of the claw-free frustration graph
`G`, and `v ≠ 0` with `z_G(-v²) = 0` (`v` is a root `u_{J,j}`, so `Π Z_G(-v²) = 0`).
Then the unnormalised incognito mode `A_v = Π T(-v) χ T(v)` satisfies
`[H, A_v] = (2/v) A_v`.  With the single-particle energy `ε = 1/v` this is
`[H, ψ_{J,j}] = 2 ε ψ_{J,j}` (the normalisation `N_{J,j}` is a scalar and drops out).

The proof is v1's: `[H, A_v] = Π T(-v) [H, χ] T(v) = 2 Π T(-v) Σ χ T(v)` (`H` commutes
with `Π` and with `T`; `[H, χ] = 2 Σ χ`), and `Π T(-v) Σ χ T(v) = A_v / v` by the
Fundamental Identity and `Π Z_G(-v²) = 0` (`mode_eq_smul`).  Claw-freeness enters
through the commutation `[H, T(u)] = 0` (v1 Theorem 1(i)); the simplicial clique
through the Fundamental Identity.  `Π` is not assumed to commute with any `h_j`. -/
theorem eigenmode (S : H.ModeSector) (hclaw : G.IsClawFree)
    (hKs : G.IsSimplicialClique Ks) {v : ℝ} (hv : v ≠ 0)
    (hroot : S.zG.eval (-v ^ 2) = 0) :
    algebraCommutator H.frustration.hamiltonian (S.mode v) = (2 / v) • S.mode v := by
  have ha : Commute H.frustration.hamiltonian (S.Pi * H.frustration.transfer ∅ (-v)) :=
    S.Pi_comm_hamiltonian.symm.mul_right (H.hamiltonian_commute_transfer hclaw (-v))
  have hc : Commute H.frustration.hamiltonian (H.frustration.transfer ∅ v) :=
    H.hamiltonian_commute_transfer hclaw v
  have h1 : algebraCommutator H.frustration.hamiltonian (S.mode v) =
      S.Pi * H.frustration.transfer ∅ (-v) *
        algebraCommutator H.frustration.hamiltonian H.root * H.frustration.transfer ∅ v :=
    algebraCommutator_mul_mul ha hc
  have h2 : algebraCommutator H.frustration.hamiltonian H.root =
      (2 : ℝ) • ((∑ j ∈ verticesOfSet Ks, H.frustration.term j) * H.root) := by
    rw [H.operator.commutator_hamiltonian_root, two_smul, two_mul]
    rfl
  rw [h1, h2, mode_eq_smul S hKs hroot, smul_smul, div_mul_cancel₀ _ hv]
  simp only [mul_smul_comm, smul_mul_assoc]

/-- **Eigenmode lemma** (v1 Lemma 13, L1285-1304), for `-v`: `[H, A_{-v}] = -(2/v) A_{-v}`,
i.e. `[H, ψ_{J,-j}] = -2 ε ψ_{J,-j}` for the mode `ψ_{J,-j}` that v1 never defines
(L1289, L1310), here `mode S (-v)` before normalisation.  It is `eigenmode` at `-v`
(note `z_G(-(-v)²) = z_G(-v²)`). -/
theorem eigenmode_neg (S : H.ModeSector) (hclaw : G.IsClawFree)
    (hKs : G.IsSimplicialClique Ks) {v : ℝ} (hv : v ≠ 0)
    (hroot : S.zG.eval (-v ^ 2) = 0) :
    algebraCommutator H.frustration.hamiltonian (S.mode (-v)) = -(2 / v) • S.mode (-v) := by
  rw [S.eigenmode hclaw hKs (neg_ne_zero.mpr hv) (by rwa [neg_sq]), div_neg]

/-! ### The intertwining relation -/

/-- **Intertwining relation** (v1 L2063-2079, inside the proof of Lemma 14): for a real `v`
that is a root of `z_G(-v²)` and every real `u`,

`(v + u) T(u) A_v = (v - u) A_v T(u)`

(v1: `(u_{J,j} + u) T(u) ψ_{J,j} = (u_{J,j} - u) ψ_{J,j} T(u)`).

v1 derives it by multiplying with `Z_G(-u²)^{-1}`, hence only for `u ≠ ± u_j` and using
`Z_G ψ = ψ Z_G`.  The proof here has no inversion and no restriction on `u`: the reduced
Fundamental Identity at `-u`, `(1 - uΣ) χ T(u) = T(u) (1 + uΣ) χ`, is sandwiched between
`Π T(-v)` and `T(v)`; `T(u)` slides through `Π`, `T(-v)` and `T(v)` (Theorem 1(i) and
`Π` commuting with the charges), and `Π T(-v) Σ χ T(v) = A_v / v`.

The hypothesis `_hv : v ≠ 0` is not used (for `v = 0` the hypothesis `hroot` forces
`Π = Π Z_G(0) = z_G(0) Π = 0`); it is kept so that the signature agrees with the other
statements about `A_v`, whose divisions by `v` do need it. -/
theorem intertwine (S : H.ModeSector) (hclaw : G.IsClawFree)
    (hKs : G.IsSimplicialClique Ks) {v : ℝ} (_hv : v ≠ 0)
    (hroot : S.zG.eval (-v ^ 2) = 0) (u : ℝ) :
    (v + u) • (H.frustration.transfer ∅ u * S.mode v) =
      (v - u) • (S.mode v * H.frustration.transfer ∅ u) :=
  intertwine_algebra (S.Pi * H.frustration.transfer ∅ (-v)) (H.frustration.transfer ∅ u)
    (H.frustration.transfer ∅ v) (∑ j ∈ verticesOfSet Ks, H.frustration.term j) H.root v u
    ((S.Pi_comm_transfer u).mul_left (H.transfer_commute_transfer hclaw (-v) u))
    (H.transfer_commute_transfer hclaw u v) (H.fundamentalIdentity_reduced_neg hKs u)
    (S.mode_eq_smul hKs hroot).symm

/-- `T(v) A_v = 0 = A_v T(-v)` (the zeros of the intertwining relation, at `u = v` and
`u = -v`, using `v ≠ 0`).  v1 uses these when passing to the limit `u → u_j`
(L2084, L2114) without stating them; note that `A_v T(-v) = 0` does not follow directly
from `Π Z_G(-v²) = 0`, since `χ` sits between `Π` and `Z_G`. -/
theorem transfer_mul_mode_eq_zero (S : H.ModeSector) (hclaw : G.IsClawFree)
    (hKs : G.IsSimplicialClique Ks) {v : ℝ} (hv : v ≠ 0)
    (hroot : S.zG.eval (-v ^ 2) = 0) :
    H.frustration.transfer ∅ v * S.mode v = 0 ∧
      S.mode v * H.frustration.transfer ∅ (-v) = 0 := by
  constructor
  · have h := S.intertwine hclaw hKs hv hroot v
    rw [sub_self, zero_smul] at h
    exact (smul_eq_zero.mp h).resolve_left (by intro h0; apply hv; linarith)
  · have h := S.intertwine hclaw hKs hv hroot (-v)
    rw [add_neg_cancel, zero_smul, sub_neg_eq_add] at h
    exact (smul_eq_zero.mp h.symm).resolve_left (by intro h0; apply hv; linarith)

/-- `Π A_v = A_v = A_v Π`: the mode lives in the sector.  This needs only that `Π` is an
idempotent commuting with `χ` and with the charges (hence with `T(±v)`); it uses neither
claw-freeness nor the root hypothesis. -/
theorem Pi_mul_mode (S : H.ModeSector) (v : ℝ) :
    S.Pi * S.mode v = S.mode v ∧ S.mode v * S.Pi = S.mode v := by
  have hPi : S.Pi * S.Pi = S.Pi := S.Pi_idem
  constructor
  · unfold mode
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, hPi]
  · unfold mode
    have e : H.frustration.transfer ∅ v * S.Pi = S.Pi * H.frustration.transfer ∅ v :=
      (S.Pi_comm_transfer v).eq.symm
    have e' : H.root * S.Pi = S.Pi * H.root := S.Pi_comm_root.eq.symm
    have e'' : H.frustration.transfer ∅ (-v) * S.Pi = S.Pi * H.frustration.transfer ∅ (-v) :=
      (S.Pi_comm_transfer (-v)).eq.symm
    calc S.Pi * H.frustration.transfer ∅ (-v) * H.root * H.frustration.transfer ∅ v * S.Pi
        = S.Pi * H.frustration.transfer ∅ (-v) * H.root *
            (H.frustration.transfer ∅ v * S.Pi) := by simp only [mul_assoc]
      _ = S.Pi * (H.frustration.transfer ∅ (-v) * (H.root * S.Pi)) *
            H.frustration.transfer ∅ v := by rw [e]; simp only [mul_assoc]
      _ = S.Pi * (H.frustration.transfer ∅ (-v) * (S.Pi * H.root)) *
            H.frustration.transfer ∅ v := by rw [e']
      _ = S.Pi * (S.Pi * H.frustration.transfer ∅ (-v)) * H.root *
            H.frustration.transfer ∅ v := by rw [← mul_assoc (H.frustration.transfer ∅ (-v)), e'']; simp only [mul_assoc]
      _ = S.Pi * H.frustration.transfer ∅ (-v) * H.root * H.frustration.transfer ∅ v := by
        rw [← mul_assoc S.Pi S.Pi, hPi]

end ModeSector

end SimplicialModeHamiltonian

end SimpleGraph
