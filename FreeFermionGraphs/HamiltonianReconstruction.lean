import FreeFermionGraphs.DiagonalRelation
import FreeFermionGraphs.ModeSectorPositivity
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Reconstruction of the Hamiltonian on a sector: `H Π = Σ_j ε_j [ψ_j^+, ψ_j^-]`

Manuscript (arXiv 2305.15625 v1), Lemma 15 (`DiagonalRelation`, statement L1315-1321),
proof L2123-2139 (the Lagrange interpolation step).  In the numbering of the revised manuscript
used by the repository, v1 Lemma 15 is "Lemma 5".  The commutator displays at L2112-2121 are
`ModeSector.Nondegenerate.commutator_plus_minus` of `DiagonalRelation`; this module is the second
half of the proof, from L2123 onwards.

## Setting

As in `DiagonalRelation`: `H` is a `SimplicialModeHamiltonian`, `S : H.ModeSector` a mode sector
with sector polynomial `z_G = S.zG`, `T(u) = T_G(u)` the transfer operator, `T'(u)` its derivative
(`transferDeriv`), and `D : S.Nondegenerate` the non-degeneracy data (`r` distinct positive reals
`u_j` with `z_G = ∏_j (1 + x/u_j²)`), whose normalised modes are `ψ_j^± = A_{±u_j}/N_j`.  The
single-particle energy of v1 is `ε_j = 1/u_j`.

## Main declarations

* `ModeSector.Nondegenerate.hamiltonian_mul_Pi` (v1 Lemma 15, within one sector): if the charges
  of order above `r` vanish on the sector, `Q_G^(k) Π = 0` for `k > r`, then
  `H Π = Σ_{j=1}^r u_j⁻¹ [ψ_j^+, ψ_j^-]`;
* `ModeSector.Nondegenerate.hamiltonian_mul_Pi_matrix`: the same statement for matrix algebras
  with no hypothesis on the charges: the condition is supplied by
  `ModeSector.charge_mul_Pi_eq_zero` (`ModeSectorPositivity`), because `r = deg z_G`
  (`Nondegenerate.natDegree_zG`);
* `PauliFrustrationRepresentation.transferDerivSymm` : `T(-u) T'(u) + T(u) T'(-u)`, the operator
  that appears in `commutator_plus_minus`, and
  `PauliFrustrationRepresentation.sum_weight_smul_transferDerivSymm_mul`: its Lagrange
  interpolation at `x = 0`, `Σ_j w_j D(u_j) Π = D(0) Π = -2 Q_G^(1) Π`, where `w_j` is the
  Lagrange weight at `0` of the node `x_j = -u_j²` (`HamiltonianReconstruction.weight`);
* `Nondegenerate.weight_eq_inv` : `w_j = (u_j² z_G'(-u_j²))⁻¹` (v1 L2129, `∂Z_G/∂x`).

## Deviations from v1

* **Sign slip at L2137.**  v1's last display reads `(T_G(u) ∂_u T_G(u))|_{u=0} = H`.  But
  `T(0) = 1` and `T'(0) = -Q_G^(1) = -H`, so this product is `-H`.  The line before it (L2133) is
  correct: with `∂T_G(-u_j)/∂u_j = -T'(-u_j)` it is `-½ Σ_j w_j D(u_j)`, where
  `D(u) = T(-u) T'(u) + T(u) T'(-u)` and `w_j = ∏_{i≠j} x_i/(x_i - x_j)` (`x_i = -u_i²`).
  Lagrange interpolation turns this into `-½ D(0) = -T'(0) = Q_G^(1) = H`.  The statement is
  therefore right but the displayed expression is not; here `D(0) = -2 Q_G^(1)` is computed
  explicitly (`transferDerivSymm_zero`).
* **Upper summation index.**  v1 sums over `j = 1, ..., α(G)`.  Here the sum runs over the `r`
  modes of the sector, `j : Fin D.r`; `r = deg z_G`, and `r < α(G)` can occur: for `C₄` with
  uniform couplings the sector `J = -1` has `z = 1 + 4x`, `r = 1 < α(G) = 2` (so the sum over
  `α(G)` modes is ill-defined there).  When `r = α(G)` one has `Q_G^(k) = 0` for `k > r`, so the
  hypothesis `htop` below holds automatically.
* **The degree condition.**  v1 applies the Lagrange formula (L2135) without saying why the
  operator polynomial `D(u) Π = Σ_m x^m D_m Π` (`x = -u²`) has degree `< r` in `x`.  Here this is
  the explicit hypothesis `htop : ∀ k > r, Q_G^(k) Π = 0`; it is a hypothesis on the sector, not a
  claim about the modes.  In matrix algebras it is a theorem (`hamiltonian_mul_Pi_matrix`).
  The formula for `Z_G'` at L2129 also presumes the product form `z_G = ∏_j (1 + x/u_j²)`; this is
  the field `zG_eq` of `Nondegenerate`, and `weight_eq_inv` derives L2129 from it.
* v1 states `H = Σ_J (Σ_j ε_{J,j} [ψ_{J,+j}, ψ_{J,-j}]) Π_J`; this module proves the single-sector
  identity `H Π_J = Σ_j ε_{J,j} [ψ_{J,+j}, ψ_{J,-j}]`.  The sum over sectors needs `Σ_J Π_J = 1`
  (a joint spectral decomposition), which is not part of this module.
* The premises beyond the manuscript setup are those of `ModeSector.Nondegenerate` (which v1 uses
  silently), `hclaw : G.IsClawFree`, `hKs : G.IsSimplicialClique Ks`, and `htop`.  The statement is
  therefore not named `paperLemma15`.
-/

open scoped BigOperators

namespace HamiltonianReconstruction

/-- The Lagrange weight at `0` of the node `x_j = -u_j²` among the nodes `x_i = -u_i²`:
`w_j = ∏_{i ≠ j} x_i / (x_i - x_j)`.  By `Nondegenerate.weight_eq_inv` it equals
`(u_j² z_G'(-u_j²))⁻¹`. -/
noncomputable def weight {r : ℕ} (u : Fin r → ℝ) (j : Fin r) : ℝ :=
  ∏ i ∈ Finset.univ.erase j, (-(u i) ^ 2) / (-(u i) ^ 2 - -(u j) ^ 2)

/-- The coefficient of `Q^(k) Q^(l)` in `T(-v) T'(v) + T(v) T'(-v)`:
`T(-v) = Σ_k (-(-v))^k Q^(k)`, `T'(v) = Σ_l l (-1)^l v^{l-1} Q^(l)`, and the same at `-v`. -/
def dCoeff (k l : ℕ) (v : ℝ) : ℝ :=
  (-(-v)) ^ k * ((l : ℝ) * (-1) ^ l * v ^ (l - 1)) +
    (-v) ^ k * ((l : ℝ) * (-1) ^ l * (-v) ^ (l - 1))

/-- Closed form of `dCoeff`: it vanishes unless `k + l` is odd, in which case it equals
`2 l (-1)^l v^{k+l-1}` (the operator `T(-v) T'(v) + T(v) T'(-v)` is even in `v`). -/
theorem dCoeff_eq (k l : ℕ) (v : ℝ) :
    dCoeff k l v = if Odd (k + l) then 2 * (l : ℝ) * (-1) ^ l * v ^ (k + l - 1) else 0 := by
  unfold dCoeff
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · simp
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl.ne'
    simp only [Nat.succ_sub_one, Nat.succ_eq_add_one, neg_neg]
    have e : k + (m + 1) - 1 = k + m := by omega
    rw [e]
    have h1 : v ^ k * (((m + 1 : ℕ) : ℝ) * (-1) ^ (m + 1) * v ^ m) =
        ((m + 1 : ℕ) : ℝ) * (-1) ^ (m + 1) * v ^ (k + m) := by rw [pow_add]; ring
    have h2 : (-v) ^ k * (((m + 1 : ℕ) : ℝ) * (-1) ^ (m + 1) * (-v) ^ m) =
        ((m + 1 : ℕ) : ℝ) * (-1) ^ (m + 1) * (-v) ^ (k + m) := by rw [pow_add]; ring
    rw [h1, h2]
    have hodd : Odd (k + (m + 1)) ↔ Even (k + m) := by
      rw [← add_assoc, Nat.odd_add_one, Nat.not_odd_iff_even]
    rcases Nat.even_or_odd (k + m) with he | ho
    · rw [if_pos (hodd.mpr he), he.neg_pow]
      ring
    · have hn : ¬ Odd (k + (m + 1)) := fun h => (Nat.not_even_iff_odd.mpr ho) (hodd.mp h)
      rw [if_neg hn, ho.neg_pow]
      ring

/-- **Lagrange interpolation at `0` for even powers**: for pairwise distinct positive `u_j`,
`Σ_j w_j u_j^{2m} = δ_{m0}` for `m < r` (`x_j = -u_j²`, `u_j^{2m} = (-1)^m x_j^m`,
`lagrange_weights_at_zero`). -/
theorem sum_weight_mul_pow_two_mul {r : ℕ} (u : Fin r → ℝ) (hpos : ∀ j, 0 < u j)
    (hinj : Function.Injective u) {m : ℕ} (hm : m < r) :
    ∑ j, weight u j * u j ^ (2 * m) = if m = 0 then 1 else 0 := by
  have hx : Function.Injective (fun j => -(u j) ^ 2) := by
    intro a b h
    have h' : u a ^ 2 = u b ^ 2 := by simpa using h
    exact hinj ((sq_eq_sq₀ (hpos a).le (hpos b).le).mp h')
  have key := lagrange_weights_at_zero (fun j => -(u j) ^ 2) hx hm
  have hterm : ∀ j, weight u j * u j ^ (2 * m) =
      (-1 : ℝ) ^ m * ((-(u j) ^ 2) ^ m * weight u j) := by
    intro j
    have : u j ^ (2 * m) = (-1 : ℝ) ^ m * (-(u j) ^ 2) ^ m := by
      rw [pow_mul, neg_pow ((u j) ^ 2) m, ← mul_assoc, ← mul_pow]
      simp
    rw [this]
    unfold weight
    ring
  simp only [hterm]
  rw [← Finset.mul_sum]
  have key' : ∑ j, (-(u j) ^ 2) ^ m * weight u j = if m = 0 then 1 else 0 := key
  rw [key']
  split_ifs with h
  · subst h; simp
  · simp

/-- **Lagrange interpolation of the coefficients of `T(-v) T'(v) + T(v) T'(-v)`**: if `k, l ≤ r`
then `Σ_j w_j c_{kl}(u_j) = c_{kl}(0)`.  Only `k + l` odd contributes; then `k + l - 1 = 2m` with
`m < r`. -/
theorem sum_weight_mul_dCoeff {r : ℕ} (u : Fin r → ℝ) (hpos : ∀ j, 0 < u j)
    (hinj : Function.Injective u) {k l : ℕ} (hk : k ≤ r) (hl : l ≤ r) :
    ∑ j, weight u j * dCoeff k l (u j) = dCoeff k l 0 := by
  simp only [dCoeff_eq]
  by_cases ho : Odd (k + l)
  · obtain ⟨m, hm⟩ := ho
    have hm' : m < r := by omega
    have e : k + l - 1 = 2 * m := by omega
    simp only [if_pos (show Odd (k + l) from ⟨m, hm⟩), e]
    have h1 : ∀ j, weight u j * (2 * (l : ℝ) * (-1) ^ l * u j ^ (2 * m)) =
        (2 * (l : ℝ) * (-1) ^ l) * (weight u j * u j ^ (2 * m)) := fun j => by ring
    simp only [h1]
    rw [← Finset.mul_sum, sum_weight_mul_pow_two_mul u hpos hinj hm']
    rcases Nat.eq_zero_or_pos m with rfl | hmpos
    · simp
    · simp [zero_pow (show 2 * m ≠ 0 by omega), hmpos.ne']
  · simp [ho]

end HamiltonianReconstruction

universe u w

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V} {Ks : Set V} {A : Type w}

namespace PauliFrustrationRepresentation

variable [Ring A] [Algebra ℝ A] [Fintype V] [DecidableEq V]

/-- Since the charges vanish above `|V|`, the sum defining `T'_{G∖W}(u)` may be extended to any
range `0 ≤ k < n` with `|V| < n` (the analogue of `transfer_eq_sum_range_of_card_lt`). -/
theorem transferDeriv_eq_sum_range_of_card_lt (H : G.PauliFrustrationRepresentation A)
    (W : Set V) (u : ℝ) {n : ℕ} (hn : Fintype.card V < n) :
    H.transferDeriv W u =
      ∑ k ∈ Finset.range n, ((k : ℝ) * (-1) ^ k * u ^ (k - 1)) • H.deletedCharge W k := by
  unfold transferDeriv
  refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) (fun k hk hk' => ?_)
  rw [Finset.mem_range] at hk hk'
  rw [H.deletedCharge_eq_zero_of_card_lt W (by omega), smul_zero]

/-- `T'_{G∖W}(0) = -Q_{G∖W}^(1)`: only the term `k = 1` of `Σ_k k (-1)^k u^{k-1} Q^(k)`
survives at `u = 0`. -/
theorem transferDeriv_zero (H : G.PauliFrustrationRepresentation A) (W : Set V) :
    H.transferDeriv W 0 = -H.deletedCharge W 1 := by
  rw [H.transferDeriv_eq_sum_range_of_card_lt W 0
    (show Fintype.card V < Fintype.card V + 2 by omega)]
  rw [Finset.sum_eq_single 1]
  · simp
  · intro k _ hk1
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · simp
    · have : k - 1 ≠ 0 := by omega
      simp [zero_pow this]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-- The operator `D(u) = T_G(-u) T'_G(u) + T_G(u) T'_G(-u)` that occurs in the commutator
`[ψ_j^+, ψ_j^-]` (`ModeSector.Nondegenerate.commutator_plus_minus`, v1 Lemma 15, L2120-2121, where
`T'(-u) = -∂_u[T(-u)]`).  For commuting charges it is even in `u`. -/
noncomputable def transferDerivSymm (H : G.PauliFrustrationRepresentation A) (u : ℝ) : A :=
  H.transfer ∅ (-u) * H.transferDeriv ∅ u + H.transfer ∅ u * H.transferDeriv ∅ (-u)

/-- `D(0) = 2 T'(0) = -2 Q_G^(1)`: with `T(0) = 1` and `T'(0) = -Q_G^(1)`.  (v1 L2137 writes
`T(0) T'(0) = H`; the correct value is `T(0) T'(0) = -H`, see the module docstring.) -/
theorem transferDerivSymm_zero (H : G.PauliFrustrationRepresentation A) :
    H.transferDerivSymm 0 = -((2 : ℝ) • H.charge 1) := by
  unfold transferDerivSymm
  rw [neg_zero, H.transfer_zero, H.transferDeriv_zero, H.deletedCharge_empty, one_mul]
  rw [two_smul, neg_add]

/-- Product of two charge expansions, sandwiched with `P` on the right. -/
theorem sum_smul_mul_sum_smul_mul {n : ℕ} (a b : ℕ → ℝ) (Q : ℕ → A) (P : A) :
    (∑ k ∈ Finset.range n, a k • Q k) * (∑ l ∈ Finset.range n, b l • Q l) * P =
      ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, (a k * b l) • (Q k * Q l * P) := by
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [smul_mul_smul_comm, smul_mul_assoc]

/-- Expansion of `D(u) P` in the charges, over any range `n > |V|`:
`D(u) P = Σ_{k,l<n} c_{kl}(u) Q^(k) Q^(l) P`. -/
theorem transferDerivSymm_mul_eq_sum (H : G.PauliFrustrationRepresentation A) (P : A) (u : ℝ)
    {n : ℕ} (hn : Fintype.card V < n) :
    H.transferDerivSymm u * P = ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
      HamiltonianReconstruction.dCoeff k l u • (H.charge k * H.charge l * P) := by
  unfold transferDerivSymm
  rw [H.transfer_eq_sum_range_of_card_lt ∅ (-u) hn, H.transfer_eq_sum_range_of_card_lt ∅ u hn,
    H.transferDeriv_eq_sum_range_of_card_lt ∅ u hn,
    H.transferDeriv_eq_sum_range_of_card_lt ∅ (-u) hn, add_mul]
  simp only [H.deletedCharge_empty]
  rw [sum_smul_mul_sum_smul_mul, sum_smul_mul_sum_smul_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [HamiltonianReconstruction.dCoeff, add_smul]

/-- **Lagrange interpolation of `D(u) Π` at `x = 0`** (v1 L2138, "by the Lagrange interpolation
formula"): if `Q^(k) P = 0` for `k > r`, the charges pairwise commute (Theorem 1(i)), and `u_1,
..., u_r` are distinct positive reals, then
`Σ_j w_j D(u_j) P = D(0) P`, where `w_j` is the Lagrange weight at `0` of `x_j = -u_j²`.

Proof.  Expand `D(u) P = Σ_{k,l} c_{kl}(u) Q^(k) Q^(l) P` (`transferDerivSymm_mul_eq_sum`).  A term
with `k > r` or `l > r` vanishes (the charges commute and `Q^(t) P = 0` for `t > r`); in the
others `k, l ≤ r` so `c_{kl}(u) ∝ u^{k+l-1}` has an even exponent `< 2r`, and
`HamiltonianReconstruction.sum_weight_mul_dCoeff` gives `Σ_j w_j c_{kl}(u_j) = c_{kl}(0)`. -/
theorem sum_weight_smul_transferDerivSymm_mul (H : G.PauliFrustrationRepresentation A)
    (hc : ∀ s t, Commute (H.charge s) (H.charge t)) {P : A} {r : ℕ}
    (htop : ∀ k, r < k → H.charge k * P = 0) (u : Fin r → ℝ) (hpos : ∀ j, 0 < u j)
    (hinj : Function.Injective u) :
    ∑ j, HamiltonianReconstruction.weight u j • (H.transferDerivSymm (u j) * P) =
      H.transferDerivSymm 0 * P := by
  set n : ℕ := Fintype.card V + r + 1 with hn
  have hn' : Fintype.card V < n := by omega
  have hX : ∀ k l, (r < k ∨ r < l) → H.charge k * H.charge l * P = 0 := by
    rintro k l (hk | hl)
    · rw [(hc k l).eq, mul_assoc, htop k hk, mul_zero]
    · rw [mul_assoc, htop l hl, mul_zero]
  simp only [H.transferDerivSymm_mul_eq_sum P _ hn', Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Finset.sum_smul]
  by_cases hkl : r < k ∨ r < l
  · rw [hX k l hkl, smul_zero, smul_zero]
  · rw [HamiltonianReconstruction.sum_weight_mul_dCoeff u hpos hinj
      (not_lt.mp (not_or.mp hkl).1) (not_lt.mp (not_or.mp hkl).2)]

end PauliFrustrationRepresentation

namespace SimplicialModeHamiltonian

namespace ModeSector

variable [Ring A] [StarRing A] [Algebra ℝ A] [StarModule ℝ A] [Fintype V] [DecidableEq V]
variable {H : G.SimplicialModeHamiltonian Ks A}

namespace Nondegenerate

variable {S : H.ModeSector}

/-- The degree of the sector polynomial is the number of modes: `z_G = ∏_j (1 + x/u_j²)` has `r`
linear factors, each with nonzero leading coefficient `u_j⁻²`. -/
theorem natDegree_zG (D : S.Nondegenerate) : S.zG.natDegree = D.r := by
  have hlin : ∀ j : Fin D.r,
      (1 + Polynomial.C ((D.u j)⁻¹ ^ 2) * Polynomial.X).natDegree = 1 := by
    intro j
    have hne : (D.u j)⁻¹ ^ 2 ≠ 0 := pow_ne_zero 2 (inv_ne_zero (D.u_pos j).ne')
    have h := Polynomial.natDegree_linear (a := (D.u j)⁻¹ ^ 2) (b := (1 : ℝ)) hne
    rwa [Polynomial.C_1, add_comm] at h
  rw [D.zG_eq, Polynomial.natDegree_prod]
  · rw [Finset.sum_congr rfl (fun j _ => hlin j)]
    simp
  · intro j _ h0
    have := hlin j
    rw [h0, Polynomial.natDegree_zero] at this
    exact zero_ne_one this

/-- **The Lagrange weight is the inverse of `u_j² z_G'(-u_j²)`** (v1 L2129, where
`∂Z_G/∂x|_{x=-u_j²} = u_j⁻² ∏_{k≠j} (u_k² - u_j²)/u_k²`):
`∏_{i≠j} x_i/(x_i - x_j) = (u_j² z_G'(x_j))⁻¹` with `x_i = -u_i²`.  Only the derivative of the
`j`-th factor of `z_G = ∏_i (1 + x/u_i²)` survives at the root `x_j`. -/
theorem weight_eq_inv (D : S.Nondegenerate) (j : Fin D.r) :
    HamiltonianReconstruction.weight D.u j =
      (D.u j ^ 2 * (Polynomial.derivative S.zG).eval (-(D.u j) ^ 2))⁻¹ := by
  have hu : ∀ i, D.u i ≠ 0 := fun i => (D.u_pos i).ne'
  set x : ℝ := -(D.u j) ^ 2 with hx
  -- the derivative of `z_G` at the root `x_j`
  have hder : (Polynomial.derivative S.zG).eval x =
      (∏ i ∈ Finset.univ.erase j, (1 + (D.u i)⁻¹ ^ 2 * x)) * (D.u j)⁻¹ ^ 2 := by
    rw [D.zG_eq, Polynomial.derivative_prod_finset, Polynomial.eval_finsetSum]
    rw [Finset.sum_eq_single j]
    · simp only [Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_add,
        Polynomial.eval_one, Polynomial.eval_C, Polynomial.eval_X, Polynomial.derivative_add,
        Polynomial.derivative_one, zero_add, Polynomial.derivative_C_mul_X, Polynomial.eval_C]
    · intro i _ hij
      have : ∏ b ∈ Finset.univ.erase i, (1 + (D.u b)⁻¹ ^ 2 * x) = 0 := by
        refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩) ?_
        rw [hx]
        field_simp [hu j]
        ring
      simp only [Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_add,
        Polynomial.eval_one, Polynomial.eval_C, Polynomial.eval_X]
      rw [this, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hprod : D.u j ^ 2 * (Polynomial.derivative S.zG).eval x =
      ∏ i ∈ Finset.univ.erase j, (1 + (D.u i)⁻¹ ^ 2 * x) := by
    rw [hder]
    field_simp [hu j]
  rw [hprod]
  unfold HamiltonianReconstruction.weight
  rw [← Finset.prod_inv_distrib]
  refine (Finset.prod_congr rfl fun i _ => ?_).symm
  have hi : D.u i ≠ 0 := hu i
  have hxi : -(D.u i) ^ 2 ≠ 0 := neg_ne_zero.mpr (pow_ne_zero 2 hi)
  have hrw : 1 + (D.u i)⁻¹ ^ 2 * x = (-(D.u i) ^ 2 - -(D.u j) ^ 2) / (-(D.u i) ^ 2) := by
    rw [hx]
    field_simp
    ring
  rw [hrw, inv_div]

/-- **Reconstruction of the Hamiltonian on a sector** (v1 Lemma 15, `DiagonalRelation`,
L1315-1321, proof L2123-2139; repo "Lemma 5"), within one sector `Π = Π_J`:

`H Π = Σ_{j=1}^r u_j⁻¹ [ψ_j^+, ψ_j^-]`,

i.e. `H Π = Σ_j ε_j [ψ_{J,+j}, ψ_{J,-j}]` with the single-particle energies `ε_j = 1/u_j`.

Proof (v1's, with the sign slip of L2137 corrected).  By `commutator_plus_minus`,
`[ψ_j^+, ψ_j^-] = -(2 u_j z_G'(-u_j²))⁻¹ Π D(u_j)` with `D(u) = T(-u) T'(u) + T(u) T'(-u)`.  Hence
`u_j⁻¹ [ψ_j^+, ψ_j^-] = -½ w_j D(u_j) Π`, where
`w_j = (u_j² z_G'(-u_j²))⁻¹ = ∏_{i≠j} x_i/(x_i - x_j)` is the Lagrange weight at `0` of the node
`x_j = -u_j²` (`weight_eq_inv`, from `z_G = ∏_j (1 + x/u_j²)`).  Since `D(u) Π` is an operator
polynomial of degree `< r` in `x = -u²` (here `htop` is used), Lagrange interpolation
(`sum_weight_smul_transferDerivSymm_mul`) gives `Σ_j w_j D(u_j) Π = D(0) Π = -2 Q_G^(1) Π`, so the
sum is `Q_G^(1) Π = H Π` (`charge_one`).

Corrections to v1:

* The last display of v1, `(T_G(u) ∂_u T_G(u))|_{u=0} = H` (L2137), has a sign slip:
  `T(0) T'(0) = -Q_G^(1) = -H`.  The correct bookkeeping is `-½ D(0) = -T'(0) = Q_G^(1) = H`.
* The sum is over the `r` modes of the sector (`r = deg z_G`), not over `α(G)` modes; for `C₄` with
  uniform couplings the sector `J = -1` has `r = 1 < α(G) = 2`.
* `htop : Q_G^(k) Π = 0` for `k > r` is the hypothesis that makes the Lagrange formula
  applicable; v1 does not state it.  It is automatic when `r = α(G)` (the charges vanish above
  `α(G)`) and in matrix algebras (`hamiltonian_mul_Pi_matrix`).

The premises beyond the manuscript setup are the non-degeneracy data `D`, `hclaw`, `hKs` and
`htop`. -/
theorem hamiltonian_mul_Pi (D : S.Nondegenerate) (hclaw : G.IsClawFree)
    (hKs : G.IsSimplicialClique Ks)
    (htop : ∀ k, D.r < k → H.frustration.charge k * S.Pi = 0) :
    H.frustration.hamiltonian * S.Pi =
      ∑ j, (D.u j)⁻¹ • (D.psiPlus j * D.psiMinus j - D.psiMinus j * D.psiPlus j) := by
  have hterm : ∀ j, (D.u j)⁻¹ • (D.psiPlus j * D.psiMinus j - D.psiMinus j * D.psiPlus j) =
      (-(1 / 2 : ℝ) * HamiltonianReconstruction.weight D.u j) •
        (H.frustration.transferDerivSymm (D.u j) * S.Pi) := by
    intro j
    have hPD : S.Pi * H.frustration.transferDerivSymm (D.u j) =
        H.frustration.transferDerivSymm (D.u j) * S.Pi :=
      (((S.Pi_comm_transfer (-(D.u j))).mul_right (S.Pi_comm_transferDeriv (D.u j))).add_right
        ((S.Pi_comm_transfer (D.u j)).mul_right (S.Pi_comm_transferDeriv (-(D.u j))))).eq
    rw [D.commutator_plus_minus hclaw hKs j]
    change (D.u j)⁻¹ • ((-(2 * D.u j *
      (Polynomial.derivative S.zG).eval (-(D.u j) ^ 2))⁻¹) •
        (S.Pi * H.frustration.transferDerivSymm (D.u j))) = _
    rw [hPD, smul_smul, D.weight_eq_inv j]
    congr 1
    have hr := D.radicand_pos j
    have hZ : (Polynomial.derivative S.zG).eval (-(D.u j) ^ 2) ≠ 0 := right_ne_zero_of_mul hr.ne'
    have hu := (D.u_pos j).ne'
    field_simp
  simp only [hterm, mul_smul, ← Finset.smul_sum]
  have hlag := H.frustration.sum_weight_smul_transferDerivSymm_mul
    (fun s t => H.frustration.deletedCharge_commute hclaw ∅ s t) htop D.u D.u_pos D.u_injective
  rw [hlag, H.frustration.transferDerivSymm_zero, ← H.frustration.charge_one, neg_mul,
    smul_mul_assoc, neg_smul, smul_neg, neg_neg, smul_smul]
  norm_num

/-- **Lemma 15 in matrix algebras, with no hypothesis on the charges**: in
`Matrix (Fin d) (Fin d) ℂ` the vanishing `Q_G^(k) Π = 0` for `k > r` (`htop` of
`hamiltonian_mul_Pi`) holds automatically, because `r = deg z_G` (`Nondegenerate.natDegree_zG`) and
`ModeSector.charge_mul_Pi_eq_zero` (`ModeSectorPositivity`) shows that the charges of order above
`deg z_G` vanish on the sector. -/
theorem hamiltonian_mul_Pi_matrix {d : ℕ}
    {H : G.SimplicialModeHamiltonian Ks (Matrix (Fin d) (Fin d) ℂ)} {S : H.ModeSector}
    (D : S.Nondegenerate) (hclaw : G.IsClawFree) (hKs : G.IsSimplicialClique Ks) :
    H.frustration.hamiltonian * S.Pi =
      ∑ j, (D.u j)⁻¹ • (D.psiPlus j * D.psiMinus j - D.psiMinus j * D.psiPlus j) :=
  D.hamiltonian_mul_Pi hclaw hKs
    (fun _ hk => S.charge_mul_Pi_eq_zero (by rw [D.natDegree_zG]; exact hk))

end Nondegenerate

end ModeSector

end SimplicialModeHamiltonian

end SimpleGraph
