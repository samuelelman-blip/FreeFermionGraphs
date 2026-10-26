import FreeFermionGraphs.FreeFermionSolution
import FreeFermionGraphs.CrossSectorRelationsExample

/-!
# Non-vacuity of `FreeFermionSolution`: the one-qubit model solved explicitly

`freeFermionSolution_of_cycleSymmetry_commute` has the premises `hJ` (`[J, J'] = 0`, v1
Theorem 1(iii)) and `hND` (per-sector coprimality).  This module checks, on the smallest
simplicial-mode Hamiltonian of `CrossSectorRelationsExample`
(`G` one vertex, `Ks = {0}`, `H = h₀ = Z`, `χ = X`, coupling `1`), that all hypotheses are jointly
satisfiable and that the explicit formulas of the theorem produce the textbook answer:

* there is a single sector (`Λ = {0}`, `Π = 1`: there is no even hole, so all cycle symmetries
  are `0`), with one mode, `r = deg(1 + x) = 1`;
* the root is `u = 1` (`z_∅(-u²) = 1 - u² = 0`), so `ε = 1/u = 1`, and
  `N = 4 u √(z_{Ks}(-u²) z_∅'(-u²)) = 4 √(1 · 1) = 4`;
* the explicit mode is `ψ = ¼ T(-1) χ T(1) = ¼ (1 + Z) X (1 - Z) = σ⁺ = [[0, 1], [0, 0]]`;
* `H = Z = ε [ψ, ψ†]`, and `[H, ψ] = 2 ε ψ`.

This confirms the normalisations (`N`, `ε`, the factor `2` in `[H, ψ] = 2εψ`) of the theorem
statement on an example where all of them are non-trivial.

## Main declarations

* `FreeFermionSolutionExample.transfer_ham1` : `T(u) = 1 - u Z` in the model;
* `FreeFermionSolutionExample.freeFermionSolution_ham1` : the conclusion of the theorem for the
  model, with the sectors, roots and modes computed.
-/

namespace SimpleGraph

namespace FreeFermionSolutionExample

open CrossSectorRelationsExample

/-- The Hamiltonian of the model is `H = Z`. -/
theorem hamiltonian_ham1 : ham1.frustration.hamiltonian = zM := by
  simp [PauliFrustrationRepresentation.hamiltonian, ham1, rep1, term1,
    SimplicialModeHamiltonian.frustration, PauliFrustrationRepresentation.restrictSome]

/-- The charges of the model: `Q^(0) = 1`, `Q^(1) = Z`, `Q^(k) = 0` for `k ≥ 2`; the transfer
operator is `T(u) = 1 - u Z`. -/
theorem transfer_ham1 (u : ℝ) : ham1.frustration.transfer ∅ u = 1 - u • zM := by
  unfold PauliFrustrationRepresentation.transfer
  have hcard : Fintype.card (Fin 1) = 1 := Fintype.card_fin 1
  rw [hcard, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    PauliFrustrationRepresentation.deletedCharge_empty,
    PauliFrustrationRepresentation.deletedCharge_empty,
    PauliFrustrationRepresentation.charge_zero, PauliFrustrationRepresentation.charge_one,
    hamiltonian_ham1]
  simp [sub_eq_add_neg]

/-- The raising operator `σ⁺ = [[0, 1], [0, 0]]`. -/
def sp : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

/-- The normalised mode of the model: `¼ (1 + Z) X (1 - Z) = σ⁺`. -/
theorem mode_ham1 : ((4 : ℝ)⁻¹) • ((1 + (-(-1 : ℝ)) • zM) * xM * (1 + (-(1 : ℝ)) • zM)) = sp := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [zM, xM, sp, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals norm_num

/-- `[σ⁺, (σ⁺)†] = Z`. -/
theorem comm_sp : sp * star sp - star sp * sp = zM := by
  have hstar : star sp = !![0, 0; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sp, Matrix.star_apply]
  rw [hstar]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [zM, sp]

/-- `(1 - uZ)(1 + uZ) = (1 - u²) 1`: `T(u) T(-u) = 1 - u²` in the model. -/
theorem transfer_mul_transfer_ham1 (u : ℝ) :
    ham1.frustration.transfer ∅ u * ham1.frustration.transfer ∅ (-u) =
      ((1 - u ^ 2 : ℝ) : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [transfer_ham1, transfer_ham1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [zM, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf

open scoped Classical in
/-- **Non-vacuity of `freeFermionSolution_of_cycleSymmetry_commute`, with all data computed.**
All hypotheses of the theorem hold for the model `ham1` (`g1_isClawFree`,
`g1_isSimplicialClique`, `g1_cycleSymmetriesCommute`, `ham1_hND`), and its conclusion gives:
a single sector `Λ = {0}` with one mode `r = 1`, root `u = 1`, the mode `ψ = σ⁺`, the
Hamiltonian `H = Z = [ψ, ψ†]` (with `ε = 1/u = 1`), and `[H, ψ] = 2 ε ψ = 2 ψ`. -/
theorem freeFermionSolution_ham1 :
    ∃ (Λ : Finset (g1.EvenHoleDeformationClass → ℝ))
      (r : (g1.EvenHoleDeformationClass → ℝ) → ℕ) (u : ∀ l, Fin (r l) → ℝ)
      (ψ : ∀ l, Fin (r l) → Matrix (Fin 2) (Fin 2) ℂ),
      Λ = {0} ∧ r 0 = 1 ∧ (∀ j, u 0 j = 1) ∧ (∀ j, ψ 0 j = sp) ∧
      zM = ∑ j, (ψ 0 j * star (ψ 0 j) - star (ψ 0 j) * ψ 0 j) ∧
      (∀ j, algebraCommutator zM (ψ 0 j) = (2 : ℝ) • ψ 0 j) := by
  obtain ⟨Λ, Pi, r, u, N, ε, ψ, h1, h2, h3, h4, h5, h6, h7, h8, hroots, hN, hNpos, hε, hψ,
    hcomm, hmul, hCAR1, hCAR2, hCAR3, hev, hevstar, hH⟩ :=
    ham1.freeFermionSolution_of_cycleSymmetry_commute g1_isClawFree g1_isSimplicialClique
      g1_cycleSymmetriesCommute (fun l _ => ham1_hND l)
  -- the only sector is `l = 0`
  have hzero : ∀ l ∈ Λ, l = 0 := by
    intro l hl
    funext κ
    refine h5 l hl κ ?_
    rintro ⟨C₀, hC₀, -⟩
    exact not_isEvenHoleCarrier_g1 C₀ hC₀
  have hne : Λ.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.sum_empty] at h3
    exact zero_ne_one h3
  obtain ⟨l₀, hl₀⟩ := hne
  have h0 : (0 : g1.EvenHoleDeformationClass → ℝ) ∈ Λ := by
    rw [← hzero l₀ hl₀]; exact hl₀
  have hΛ : Λ = {0} := Finset.eq_singleton_iff_unique_mem.2 ⟨h0, hzero⟩
  have hPi : Pi 0 = 1 := by
    rw [hΛ, Finset.sum_singleton] at h3
    exact h3
  obtain ⟨hr, -, hpos, -, -, hroot⟩ := hroots 0 h0
  rw [sectorPolynomial_empty1] at hr
  have hr1 : r 0 = 1 := by
    rw [hr, add_comm]; exact Polynomial.natDegree_X_add_C 1
  -- the root `u = 1`
  have hu : ∀ j, u 0 j = 1 := by
    intro j
    have h := hroot j
    rw [hPi, mul_one, transfer_mul_transfer_ham1] at h
    have h' := congrFun (congrFun h 0) 0
    simp at h'
    have h'' : ((1 - u 0 j ^ 2 : ℝ) : ℂ) = 0 := by push_cast; exact h'
    have hsq : u 0 j ^ 2 = 1 := by
      have := Complex.ofReal_eq_zero.1 h''
      linarith
    have := hpos j
    nlinarith
  -- the normalisation `N = 4`
  have hN4 : ∀ j, N 0 j = 4 := by
    intro j
    rw [hN, hu j, sectorPolynomial_Ks1, sectorPolynomial_empty1]
    simp
  have hψsp : ∀ j, ψ 0 j = sp := by
    intro j
    rw [hψ, hN4 j, hPi, hu j, one_mul, transfer_ham1, transfer_ham1]
    have hroot' : ham1.root = xM := rfl
    rw [hroot']
    rw [← mode_ham1]
    simp [sub_eq_add_neg]
  refine ⟨Λ, r, u, ψ, hΛ, hr1, hu, hψsp, ?_, ?_⟩
  · have h := hH
    rw [hΛ, Finset.sum_singleton, hPi, mul_one, hamiltonian_ham1] at h
    rw [h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hε, hu j]
    simp
  · intro j
    have h := hev 0 h0 j
    rw [hamiltonian_ham1, hε, hu j] at h
    simpa using h

end FreeFermionSolutionExample

end SimpleGraph
