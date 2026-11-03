import FreeFermionGraphs.TheoremOneIIIConsequences
import FreeFermionGraphs.CycleSymmetrySectorsExample

/-!
# Non-vacuity of `paperTheorem2_of_sectorCoprime`: a multi-sector model with an even hole

v1 Theorem 2 (the free-fermion solution, L1248-1264) is stated in this repository as
`SimplicialModeHamiltonian.paperTheorem2_of_sectorCoprime`, with the per-sector coprimality
hypothesis `hND` that v1 leaves tacit but needs (`docs/V1_ERRATA.md`).  This module is a
non-vacuity witness for that theorem on a graph that has an even hole and several sectors.

The other witnesses do not cover this case.  `FreeFermionSolutionExample` is the one-vertex graph,
which has no even hole and a single sector.  The three-qubit `C₄` model of
`CycleSymmetrySectorsExample` has uniform couplings, and there `hND` fails in the sector `J = +1`
(the double root `x = -1/2` of `z_{∅,+1} = (1 + 2x)²` is also a root of `z_{Ks,+1} = 1 + 2x`, so
the normalisation `N` of the modes vanishes).

## The model

The same three-qubit representation of `G⁺ = c4.adjoinRootAt Ks` (`G = c4` the 4-cycle, `Ks = {0, 1}`
the simplicial clique) is used, but with the couplings `b = (1, 1, 1, 2)`: the term at vertex `3`
is `h₃ = 2 X₀ Z₂`, so `h₃² = 4` and `b₃ = 2`.  Then

* the cycle symmetry of the unique even hole `{0, 1, 2, 3}` is `J = h₀ h₂ h₁ h₃ = 2 Z₂`
  (`cycleSymmetry2_eq`), with `J² = 4`, so the sectors are `J = ±2`;
* the sector polynomials are
  `z_{∅,+2} = 1 + 7x + 9x²`, `z_{∅,-2} = 1 + 7x + x²`, `z_{Ks} = 1 + 5x`
  (`z_empty`, `z_Ks`); in general `z_{∅,l} = I_G(x) + 2 l(⟨C⟩) x²` with the independence polynomial
  `I_G(x) = 1 + 7x + 5x²` of the weighted 4-cycle;
* these are coprime to `z_{Ks}` in both sectors (`coprime_plus`, `coprime_minus`), hence `hND`
  holds (`ham2_hND`).

## Main declarations

* `FreeFermionSolutionMultiSectorExample.ham2`: the `SimplicialModeHamiltonian` of the model.
* `FreeFermionSolutionMultiSectorExample.ham2_hND`: the hypothesis `hND` of
  `paperTheorem2_of_sectorCoprime` for `ham2`.
* `FreeFermionSolutionMultiSectorExample.theorem2_two_sectors`: the conclusion of
  `paperTheorem2_of_sectorCoprime` for `ham2` with at least two sectors: `r_l = 2` modes per
  sector; `Π_l` Hermitian, idempotent, nonzero, orthogonal and summing to `1`; `J Π_l = l(κ₀) Π_l`
  with `l(κ₀) ∈ {2, -2}` and both signs occurring; `u, N > 0` and `T(u) T(-u) Π_l = 0`; the
  explicit modes `ψ_{l,j} = N⁻¹ Π_l T(-u) χ T(u)` with `ε = 1/u`; the canonical anticommutation
  relations `{ψ_{l,j}, ψ_{l',k}^†} = δ Π_l`; and `H = ∑_l (∑_j ε_{l,j} [ψ_{l,j}, ψ_{l,j}^†]) Π_l`.

All matrix identities are decided on integer matrices (by kernel evaluation, `decide +kernel`) and
transported to `ℂ` by the ring homomorphism `φ` of `CycleSymmetrySectorsExample`.
-/

namespace SimpleGraph

namespace FreeFermionSolutionMultiSectorExample

open CycleSymmetrySectorsExample

/-! ### The model with couplings (1, 1, 1, 2) -/

/-- The integer matrices of the model `CycleSymmetrySectorsExample.M`, with the term at vertex `3`
doubled: `h₃ = 2 X₀ Z₂`. -/
def M2 : Option (Fin 4) → Matrix (Fin 8) (Fin 8) ℤ
  | some 3 => (2 : ℤ) • M (some 3)
  | v => M v

theorem M2_some012 : M2 (some 0) = M (some 0) ∧ M2 (some 1) = M (some 1) ∧
    M2 (some 2) = M (some 2) ∧ M2 none = M none := ⟨rfl, rfl, rfl, rfl⟩

theorem M2_transpose : ∀ v, Matrix.transpose (M2 v) = M2 v := by decide +kernel

theorem M2_anticomm : ∀ j k, adjB j k = true → M2 j * M2 k = -(M2 k * M2 j) := by
  decide +kernel

theorem M2_comm : ∀ j k, adjB j k = false → M2 j * M2 k = M2 k * M2 j := by decide +kernel

theorem M2_not_anticomm : ∀ j k, adjB j k = false → M2 j * M2 k ≠ -(M2 k * M2 j) := by
  decide +kernel

theorem M2_sq1 : ∀ j : Fin 4, j ≠ 3 → M2 (some j) * M2 (some j) = 1 := by decide +kernel

theorem M2_sq3 : M2 (some 3) * M2 (some 3) = (4 : ℤ) • 1 := by decide +kernel

theorem M2_root : M2 none * M2 none = 1 := by decide +kernel

theorem M2_cycle : M2 (some 0) * M2 (some 2) * (M2 (some 1) * M2 (some 3)) = (2 : ℤ) • zOp 2 := by
  decide +kernel

/-- The Pauli frustration representation of `G⁺ = c4.adjoinRootAt Ks` by the matrices `M2`.  The
relations (adjacent vertices anticommute, non-adjacent ones commute) are unchanged by the scaling
of `h₃`. -/
def rep2 : (c4.adjoinRootAt Ks).PauliFrustrationRepresentation (Matrix (Fin 8) (Fin 8) ℂ) where
  term v := φ (M2 v)
  adj_iff_anticommute := by
    intro j k
    rw [← map_mul, ← map_mul, ← map_neg, φ_injective.eq_iff, adjB_iff]
    constructor
    · exact M2_anticomm j k
    · intro h
      by_contra hb
      exact M2_not_anticomm j k (by simpa using hb) h
  commute_of_not_adj := by
    intro j k h
    have hb : adjB j k = false := by simpa [adjB_iff] using h
    rw [← map_mul, ← map_mul, M2_comm j k hb]

/-- The couplings `b = (1, 1, 1, 2)`. -/
def b : Fin 4 → ℝ := fun j => if j = 3 then 2 else 1

theorem b0 : b 0 = 1 := by simp [b]
theorem b1 : b 1 = 1 := by simp [b]
theorem b2 : b 2 = 1 := by simp [b]
theorem b3 : b 3 = 2 := by simp [b]

/-- The simplicial-mode Hamiltonian of the model: three qubits, frustration graph the 4-cycle,
simplicial clique `Ks = {0, 1}`, couplings `b = (1, 1, 1, 2)`
(`h₀ = Z₀ Z₁`, `h₁ = X₀ Z₁`, `h₂ = Z₀`, `h₃ = 2 X₀ Z₂`, `χ = X₁`). -/
def ham2 : c4.SimplicialModeHamiltonian Ks (Matrix (Fin 8) (Fin 8) ℂ) where
  operator := rep2
  coupling := b
  original_term_sq := by
    intro j
    show φ (M2 (some j)) * φ (M2 (some j)) = _
    rw [← map_mul]
    by_cases hj : j = 3
    · subst hj
      rw [M2_sq3, map_zsmul, map_one, Algebra.algebraMap_eq_smul_one]
      ext i k
      simp only [Matrix.smul_apply, Matrix.one_apply, b3]
      split_ifs <;> norm_num
    · rw [M2_sq1 j hj, map_one]
      fin_cases j <;> simp [b0, b1, b2] at hj ⊢
  term_selfAdjoint := fun v => isSelfAdjoint_φ (M2_transpose v)
  root_sq := by
    show φ (M2 none) * φ (M2 none) = 1
    rw [← map_mul, M2_root]
    exact map_one φ

theorem ham2_coupling : ham2.coupling = b := rfl

/-! ### The cycle symmetry `J = 2 Z₂` -/

theorem independentProduct_pair2 {a c : Fin 4} (hac : a ≠ c) (h : ¬ c4.Adj a c) :
    ham2.frustration.independentProduct {a, c} =
      ham2.frustration.term a * ham2.frustration.term c := by
  have hc : ham2.frustration.independentProduct {c} = ham2.frustration.term c := by
    rw [ham2.frustration.independentProduct_eq_noncommProd (by simp)]
    exact Finset.noncommProd_singleton c ham2.frustration.term
  rw [ham2.frustration.independentProduct_insert_left (by simpa using hac) (by simp)
    (by simpa using h), hc]

/-- The cycle symmetry of the model is `J = h₀ h₂ h₁ h₃ = 2 Z₂`. -/
theorem cycleSymmetry2_eq :
    ham2.frustration.generalizedCycleSymmetryOp Set.univ = φ ((2 : ℤ) • zOp 2) := by
  unfold PauliFrustrationRepresentation.generalizedCycleSymmetryOp generalizedCycleSymmetry
  rw [deformationClosureFinset_univ, Finset.sum_singleton]
  have hcov : (((({0, 2} : Finset (Fin 4)) : Set (Fin 4))) ∪
      (({1, 3} : Finset (Fin 4)) : Set (Fin 4))) = Set.univ := by
    ext x
    fin_cases x <;> simp
  have hd : Disjoint ({0, 2} : Finset (Fin 4)) {1, 3} := by decide
  have ha : c4.IsIndepSet ((({0, 2} : Finset (Fin 4)) : Set (Fin 4))) := by
    have h : ∀ x y : Fin 4, x ∈ ({0, 2} : Finset (Fin 4)) → y ∈ ({0, 2} : Finset (Fin 4)) →
        x ≠ y → ¬ c4.Adj x y := by decide
    exact fun x hx y hy hxy => h x y hx hy hxy
  have hb : c4.IsIndepSet ((({1, 3} : Finset (Fin 4)) : Set (Fin 4))) := by
    have h : ∀ x y : Fin 4, x ∈ ({1, 3} : Finset (Fin 4)) → y ∈ ({1, 3} : Finset (Fin 4)) →
        x ≠ y → ¬ c4.Adj x y := by decide
    exact fun x hx y hy hxy => h x y hx hy hxy
  rw [(ham2.frustration.evenHoleOperator_eq_of_colouring isEvenHoleCarrier_univ hcov hd ha hb).1,
    independentProduct_pair2 (by decide) (by decide),
    independentProduct_pair2 (by decide) (by decide)]
  show φ (M2 (some 0)) * φ (M2 (some 2)) * (φ (M2 (some 1)) * φ (M2 (some 3))) = _
  rw [← map_mul, ← map_mul, ← map_mul, M2_cycle]

/-- `J² = 4`, so the eigenvalues of `J` are `±2`. -/
theorem J2_sq : φ ((2 : ℤ) • zOp 2) * φ ((2 : ℤ) • zOp 2) = (4 : ℂ) • 1 := by
  rw [← map_mul]
  have : ((2 : ℤ) • zOp 2) * ((2 : ℤ) • zOp 2) = (4 : ℤ) • 1 := by decide +kernel
  rw [this, map_zsmul, map_one]
  ext i k
  simp only [Matrix.smul_apply, Matrix.one_apply]
  split_ifs <;> norm_num

/-! ### Sector polynomials -/

/-- The class of the 4-hole. -/
noncomputable abbrev κ₀ : c4.EvenHoleDeformationClass := c4.evenHoleDeformationClassOf Set.univ

theorem κ₀_out : κ₀.out = Set.univ := by
  have h : InEvenHoleDeformationClosure c4 κ₀.out Set.univ :=
    inEvenHoleDeformationClosure_classOf_out Set.univ
  exact eq_univ_of_inClosure_univ h.symm

theorem eq_κ₀_of_carrier {κ : c4.EvenHoleDeformationClass} (h : c4.IsEvenHoleCarrier κ.out) :
    κ = κ₀ := by
  have := eq_univ_of_isEvenHoleCarrier h
  rw [← evenHoleDeformationClassOf_out κ, this]

open scoped Classical in
theorem sectorClassFamilies_empty : c4.sectorClassFamilies ∅ = {∅, {κ₀}} := by
  ext K
  rw [mem_sectorClassFamilies, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨h, -⟩
    have hsub : K ⊆ {κ₀} := by
      intro κ hκ
      rw [Finset.mem_singleton]
      exact eq_κ₀_of_carrier (h κ hκ).1
    rcases Finset.subset_singleton_iff.1 hsub with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rintro (rfl | rfl)
    · simp
    · refine ⟨?_, by simp⟩
      intro κ hκ
      rw [Finset.mem_singleton] at hκ
      subst hκ
      rw [κ₀_out]
      exact ⟨isEvenHoleCarrier_univ, Set.disjoint_empty _⟩

theorem sectorClassFamilies_Ks : c4.sectorClassFamilies Ks = {∅} := by
  ext K
  rw [mem_sectorClassFamilies, Finset.mem_singleton]
  constructor
  · rintro ⟨h, -⟩
    rw [Finset.eq_empty_iff_forall_notMem]
    intro κ hκ
    obtain ⟨hc, hd⟩ := h κ hκ
    rw [eq_κ₀_of_carrier hc, κ₀_out] at hd
    have : (0 : Fin 4) ∈ Ks := by simp [Ks]
    exact Set.disjoint_left.1 hd (Set.mem_univ 0) this
  · rintro rfl
    simp

theorem indep_iff (S : Finset (Fin 4)) :
    c4.IsIndepSet (S : Set (Fin 4)) ↔ ∀ x ∈ S, ∀ y ∈ S, ¬ c4.Adj x y := by
  constructor
  · intro h x hx y hy hxy
    by_cases e : x = y
    · subst e
      exact c4.irrefl hxy
    · exact h hx hy e hxy
  · intro h x hx y hy _
    exact h x hx y hy

theorem indepAvoid_empty :
    c4.independentFinsetsAvoid (∅ : Set (Fin 4)) = {∅, {0}, {1}, {2}, {3}, {0, 2}, {1, 3}} := by
  ext S
  rw [mem_independentFinsetsAvoid, indep_iff]
  simp only [Set.mem_empty_iff_false, not_false_eq_true, implies_true, and_true]
  revert S
  decide

theorem indepAvoid_Ks :
    c4.independentFinsetsAvoid Ks = {∅, {2}, {3}} := by
  ext S
  rw [mem_independentFinsetsAvoid, indep_iff]
  have hKs : ∀ v : Fin 4, v ∈ Ks ↔ v.val < 2 := fun v => Iff.rfl
  simp only [hKs]
  revert S
  decide

theorem indepAvoid_univ (W : Set (Fin 4)) (hW : Set.univ ⊆ W) :
    c4.independentFinsetsAvoid W = {∅} := by
  ext S
  rw [mem_independentFinsetsAvoid, Finset.mem_singleton]
  constructor
  · rintro ⟨-, h⟩
    rw [Finset.eq_empty_iff_forall_notMem]
    intro v hv
    exact h v hv (hW (Set.mem_univ v))
  · rintro rfl
    exact ⟨by simp [SimpleGraph.IsIndepSet], by simp⟩

open Polynomial in
theorem I_G : c4.weightedIndependencePolynomial b ∅ = 1 + 7 * X + 5 * X ^ 2 := by
  rw [weightedIndependencePolynomial_eq_sum, indepAvoid_empty]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide)]
  simp only [Finset.prod_empty, Finset.prod_singleton, Finset.card_empty, Finset.card_singleton,
    Finset.card_insert_of_notMem (show (0 : Fin 4) ∉ ({2} : Finset (Fin 4)) by decide),
    Finset.card_insert_of_notMem (show (1 : Fin 4) ∉ ({3} : Finset (Fin 4)) by decide),
    b0, b1, b2, b3]
  norm_num
  simp only [show (C (4:ℝ)) = 4 from map_ofNat C 4]
  ring

open Polynomial in
theorem I_Ks : c4.weightedIndependencePolynomial b Ks = 1 + 5 * X := by
  rw [weightedIndependencePolynomial_eq_sum, indepAvoid_Ks]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [Finset.prod_empty, Finset.prod_singleton, Finset.card_empty, Finset.card_singleton,
    b2, b3]
  norm_num
  simp only [show (C (4:ℝ)) = 4 from map_ofNat C 4]
  ring

theorem familyBoundary_empty :
    c4.familyBoundary ((∅ : Finset c4.EvenHoleDeformationClass).image Quotient.out) = ∅ := by
  simp [SimpleGraph.familyBoundary]

theorem familyBoundary_κ₀ :
    c4.familyBoundary (({κ₀} : Finset c4.EvenHoleDeformationClass).image Quotient.out) =
      Set.univ := by
  simp [SimpleGraph.familyBoundary, κ₀_out]

open scoped Classical in
open Polynomial in
theorem z_empty (l : c4.EvenHoleDeformationClass → ℝ) :
    c4.sectorPolynomial ham2.coupling ∅ l = 1 + 7 * X + (5 + 2 * C (l κ₀)) * X ^ 2 := by
  unfold SimpleGraph.sectorPolynomial
  rw [sectorClassFamilies_empty, Finset.sum_insert (by simp), Finset.sum_singleton,
    familyBoundary_empty, familyBoundary_κ₀, ham2_coupling]
  have h1 : (∅ : Set (Fin 4)) ∪ ∅ ∪ c4.openNeighborhood ∅ = ∅ := by
    simp [SimpleGraph.openNeighborhood]
  have h2 : c4.weightedIndependencePolynomial b (∅ ∪ Set.univ ∪ c4.openNeighborhood Set.univ) =
      1 := by
    rw [weightedIndependencePolynomial_eq_sum,
      indepAvoid_univ (∅ ∪ Set.univ ∪ c4.openNeighborhood Set.univ) (by intro x _; simp)]
    simp
  rw [h1, h2, I_G]
  have h4 : (Set.univ : Set (Fin 4)).ncard = 4 := by simp
  rw [h4]
  simp
  simp only [show (C (2:ℝ)) = 2 from map_ofNat C 2]
  ring

open Polynomial in
theorem z_Ks (l : c4.EvenHoleDeformationClass → ℝ) :
    c4.sectorPolynomial ham2.coupling Ks l = 1 + 5 * X := by
  unfold SimpleGraph.sectorPolynomial
  rw [sectorClassFamilies_Ks, Finset.sum_singleton, familyBoundary_empty, ham2_coupling]
  have h1 : Ks ∪ ∅ ∪ c4.openNeighborhood ∅ = Ks := by
    simp [SimpleGraph.openNeighborhood]
  rw [h1, I_Ks]
  simp

/-! ### `hND` holds -/

open Polynomial in
theorem coprime_plus :
    IsCoprime (1 + 7 * X + (5 + 2 * C (2 : ℝ)) * X ^ 2 : ℝ[X]) (1 + 5 * X) := by
  refine ⟨-25, 45 * X + 26, ?_⟩
  rw [show (C (2 : ℝ)) = 2 from map_ofNat C 2]
  ring

open Polynomial in
theorem coprime_minus :
    IsCoprime (1 + 7 * X + (5 + 2 * C (-2 : ℝ)) * X ^ 2 : ℝ[X]) (1 + 5 * X) := by
  refine ⟨C (1 / 9) * (-25), C (1 / 9) * (5 * X + 34), ?_⟩
  rw [show (C (-2 : ℝ)) = -2 by rw [map_neg, map_ofNat C 2]]
  have e : C (1 / 9 : ℝ) * (-25) * (1 + 7 * X + (5 + 2 * -2) * X ^ 2) +
      C (1 / 9) * (5 * X + 34) * (1 + 5 * X) = C (1 / 9 : ℝ) * 9 := by ring
  rw [e, show (9 : ℝ[X]) = C 9 from (map_ofNat C 9).symm, ← C_mul]
  norm_num

/-- A joint eigenvalue `l(⟨C⟩)` of the cycle symmetry is `±2`. -/
theorem eigen_pm (l : c4.EvenHoleDeformationClass → ℝ)
    (h : ∃ v : Fin 8 → ℂ, v ≠ 0 ∧ ∀ C₀, c4.IsEvenHoleCarrier C₀ →
      (ham2.frustration.generalizedCycleSymmetryOp C₀).mulVec v =
        ((l (c4.evenHoleDeformationClassOf C₀) : ℝ) : ℂ) • v) :
    l κ₀ = 2 ∨ l κ₀ = -2 := by
  obtain ⟨v, hv, hJ⟩ := h
  have e := hJ Set.univ isEvenHoleCarrier_univ
  rw [cycleSymmetry2_eq] at e
  have e2 : (φ ((2 : ℤ) • zOp 2) * φ ((2 : ℤ) • zOp 2)).mulVec v =
      (((l κ₀ : ℝ) : ℂ) * ((l κ₀ : ℝ) : ℂ)) • v := by
    rw [← Matrix.mulVec_mulVec, e, Matrix.mulVec_smul, e, smul_smul]
  rw [J2_sq, Matrix.smul_mulVec, Matrix.one_mulVec] at e2
  have e3 : ((4 : ℂ) - ((l κ₀ : ℝ) : ℂ) * ((l κ₀ : ℝ) : ℂ)) • v = 0 := by
    rw [sub_smul, e2, sub_self]
  have e4 : (4 : ℂ) - ((l κ₀ : ℝ) : ℂ) * ((l κ₀ : ℝ) : ℂ) = 0 :=
    (smul_eq_zero.1 e3).resolve_right hv
  have e5 : (l κ₀) * (l κ₀) = 4 := by
    have : (((l κ₀ * l κ₀ : ℝ)) : ℂ) = ((4 : ℝ) : ℂ) := by
      push_cast
      linear_combination -e4
    exact_mod_cast this
  have : (l κ₀ - 2) * (l κ₀ + 2) = 0 := by linear_combination e5
  rcases mul_eq_zero.1 this with h | h
  · left; linarith
  · right; linarith

/-- **The coprimality hypothesis `hND` of `paperTheorem2_of_sectorCoprime` holds for `ham2`**, in
both sectors `J = ±2`: `z_{∅,±2}` is coprime to `z_{Ks} = 1 + 5x`. -/
theorem ham2_hND : ∀ l : c4.EvenHoleDeformationClass → ℝ,
      ((∃ v : Fin 8 → ℂ, v ≠ 0 ∧ ∀ C₀, c4.IsEvenHoleCarrier C₀ →
          (ham2.frustration.generalizedCycleSymmetryOp C₀).mulVec v =
            ((l (c4.evenHoleDeformationClassOf C₀) : ℝ) : ℂ) • v) ∧
        ∀ κ, ¬ c4.IsEvenHoleClass κ → l κ = 0) →
      IsCoprime (c4.sectorPolynomial ham2.coupling ∅ l)
        (c4.sectorPolynomial ham2.coupling Ks l) := by
  rintro l ⟨hv, -⟩
  rw [z_empty, z_Ks]
  rcases eigen_pm l hv with h | h
  · rw [h]; exact coprime_plus
  · rw [h]; exact coprime_minus

/-! ### Theorem 2 on the model: two sectors, two modes each -/

/-- The cycle symmetry `J = 2 Z₂` is not a scalar matrix, so it has at least two eigenvalues. -/
theorem J2_not_scalar (c : ℂ) :
    ham2.frustration.generalizedCycleSymmetryOp Set.univ ≠ c • (1 : Matrix (Fin 8) (Fin 8) ℂ) := by
  intro h
  rw [cycleSymmetry2_eq] at h
  have h0 := congrFun (congrFun h 0) 0
  have h4 := congrFun (congrFun h 4) 4
  have e0 : ((2 : ℤ) • zOp 2) 0 0 = 2 := by decide
  have e4 : ((2 : ℤ) • zOp 2) 4 4 = -2 := by decide
  simp only [φ, RingHom.mapMatrix_apply, Matrix.map_apply, e0, e4, Matrix.smul_apply,
    Matrix.one_apply_eq, smul_eq_mul, mul_one] at h0 h4
  rw [← h0] at h4
  norm_num at h4

open scoped Classical in
/-- **Non-vacuity of `paperTheorem2_of_sectorCoprime` with several sectors.**  For the three-qubit
`C₄` model `ham2` with couplings `(1, 1, 1, 2)`, the hypotheses `hclaw`, `hKs` and `hND` hold
(`c4_isClawFree`, `c4_isSimplicialClique`, `ham2_hND`), and the conclusion of
`paperTheorem2_of_sectorCoprime` holds with at least two sectors.  The statement lists, conjunct
for conjunct, the data of v1 Theorem 2 (L1248-1264) that tie the sectors to the Hamiltonian:

* `Λ` has at least two elements and `r_l = 2` modes in every sector;
* `Π_l` (`l ∈ Λ`) are Hermitian, idempotent, nonzero, pairwise orthogonal and sum to `1`;
* `J Π_l = l(κ₀) Π_l` for the cycle symmetry `J = 2 Z₂` of the 4-hole, `l(κ₀) ∈ {2, -2}`, and both
  signs occur (the cycle symmetry is not a scalar, `J2_not_scalar`);
* `u_{l,j} > 0`, `N_{l,j} > 0`, `Z_G(-u²) Π_l = 0` in the form
  `T(u) T(-u) Π_l = 0`, the explicit modes `ψ_{l,j} = N⁻¹ Π_l T(-u) χ T(u)`, and `ε = 1/u`;
* the canonical anticommutation relations `{ψ_{l,j}, ψ_{l',k}^†} = δ Π_l`;
* `H = ∑_{l ∈ Λ} (∑_j ε_{l,j} [ψ_{l,j}, ψ_{l,j}^†]) Π_l`.

In each sector `r_l = deg z_{∅,l} = 2 = α(G)` (`z_{∅,+2} = 1 + 7x + 9x²`,
`z_{∅,-2} = 1 + 7x + x²`). -/
theorem theorem2_two_sectors :
    ∃ (Λ : Finset (c4.EvenHoleDeformationClass → ℝ))
      (Pi : (c4.EvenHoleDeformationClass → ℝ) → Matrix (Fin 8) (Fin 8) ℂ)
      (r : (c4.EvenHoleDeformationClass → ℝ) → ℕ) (u : ∀ l, Fin (r l) → ℝ)
      (N : ∀ l, Fin (r l) → ℝ) (ε : ∀ l, Fin (r l) → ℝ)
      (ψ : ∀ l, Fin (r l) → Matrix (Fin 8) (Fin 8) ℂ),
      2 ≤ Λ.card ∧ (∀ l ∈ Λ, r l = 2) ∧
      (∀ l ∈ Λ, (Pi l).IsHermitian ∧ Pi l * Pi l = Pi l ∧ Pi l ≠ 0) ∧
      (∀ l ∈ Λ, ∀ m ∈ Λ, l ≠ m → Pi l * Pi m = 0) ∧ ∑ l ∈ Λ, Pi l = 1 ∧
      (∀ l ∈ Λ, ham2.frustration.generalizedCycleSymmetryOp Set.univ * Pi l =
        ((l κ₀ : ℝ) : ℂ) • Pi l) ∧
      (∀ l ∈ Λ, l κ₀ = 2 ∨ l κ₀ = -2) ∧
      (∃ l ∈ Λ, l κ₀ = 2) ∧ (∃ l ∈ Λ, l κ₀ = -2) ∧
      (∀ l ∈ Λ, ∀ j, 0 < u l j ∧ 0 < N l j ∧
        ham2.frustration.transfer ∅ (u l j) * ham2.frustration.transfer ∅ (-(u l j)) * Pi l = 0) ∧
      (∀ l j, ψ l j = (N l j)⁻¹ •
        (Pi l * ham2.frustration.transfer ∅ (-(u l j)) * ham2.root *
          ham2.frustration.transfer ∅ (u l j))) ∧
      (∀ l j, ε l j = (u l j)⁻¹) ∧
      (∀ l ∈ Λ, ∀ l' ∈ Λ, ∀ (j : Fin (r l)) (k : Fin (r l')),
        ψ l j * star (ψ l' k) + star (ψ l' k) * ψ l j = if l = l' ∧ HEq j k then Pi l else 0) ∧
      ham2.frustration.hamiltonian = ∑ l ∈ Λ,
        (∑ j, ε l j • (ψ l j * star (ψ l j) - star (ψ l j) * ψ l j)) * Pi l := by
  obtain ⟨Λ, Pi, r, u, N, ε, ψ, h1, h2, h3, h4, h5, h6, h7, h8, hroots, hN, hNpos, hε, hψ,
    hcomm, hmul, hCAR1, hCAR2, hCAR3, hev, hevstar, hH⟩ :=
    ham2.paperTheorem2_of_sectorCoprime c4_isClawFree c4_isSimplicialClique ham2_hND
  have h4' : ∀ l ∈ Λ, ham2.frustration.generalizedCycleSymmetryOp Set.univ * Pi l =
      ((l κ₀ : ℝ) : ℂ) • Pi l := fun l hl => h4 l hl Set.univ isEvenHoleCarrier_univ
  -- two sectors: `J` is not a scalar
  have hcard : 1 < Λ.card := by
    rw [Finset.one_lt_card]
    by_contra hcon
    push Not at hcon
    have hne : Λ.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      rw [hempty, Finset.sum_empty] at h3
      exact zero_ne_one h3
    obtain ⟨l₀, hl₀⟩ := hne
    have hsing : Λ = {l₀} :=
      Finset.eq_singleton_iff_unique_mem.2 ⟨hl₀, fun x hx => hcon x hx l₀ hl₀⟩
    rw [hsing, Finset.sum_singleton] at h3
    have h := h4' l₀ hl₀
    rw [h3, mul_one] at h
    exact J2_not_scalar _ h
  -- every occurring eigenvalue is `±2`, so `deg z_{∅,l} = 2`
  have hr : ∀ l ∈ Λ, r l = 2 := by
    intro l hl
    have hmem := (h7 l).1 hl
    rw [(hroots l hl).1, z_empty]
    rcases eigen_pm l hmem.1 with h | h <;> rw [h]
    · have e : (1 + 7 * Polynomial.X + (5 + 2 * Polynomial.C (2 : ℝ)) * Polynomial.X ^ 2 :
          Polynomial ℝ) = Polynomial.C 9 * Polynomial.X ^ 2 + Polynomial.C 7 * Polynomial.X +
            Polynomial.C 1 := by
        rw [show (Polynomial.C (2 : ℝ)) = 2 from map_ofNat Polynomial.C 2,
          show (Polynomial.C (9 : ℝ)) = 9 from map_ofNat Polynomial.C 9,
          show (Polynomial.C (7 : ℝ)) = 7 from map_ofNat Polynomial.C 7, map_one]
        ring
      rw [e]; exact Polynomial.natDegree_quadratic (by norm_num)
    · have e : (1 + 7 * Polynomial.X + (5 + 2 * Polynomial.C (-2 : ℝ)) * Polynomial.X ^ 2 :
          Polynomial ℝ) = Polynomial.C 1 * Polynomial.X ^ 2 + Polynomial.C 7 * Polynomial.X +
            Polynomial.C 1 := by
        rw [show (Polynomial.C (-2 : ℝ)) = -2 by rw [map_neg, map_ofNat Polynomial.C 2],
          show (Polynomial.C (7 : ℝ)) = 7 from map_ofNat Polynomial.C 7, map_one]
        ring
      rw [e]; exact Polynomial.natDegree_quadratic (by norm_num)
  have hoff : ∀ l ∈ Λ, ∀ κ, κ ≠ κ₀ → l κ = 0 := by
    intro l hl κ hκ
    exact h5 l hl κ (by
      rintro ⟨C, hC, rfl⟩
      exact hκ (by rw [eq_univ_of_isEvenHoleCarrier hC]))
  have hpm : ∀ l ∈ Λ, l κ₀ = 2 ∨ l κ₀ = -2 := fun l hl => eigen_pm l ((h7 l).1 hl).1
  have hext : ∀ l ∈ Λ, ∀ m ∈ Λ, l κ₀ = m κ₀ → l = m := by
    intro l hl m hm h
    funext κ
    by_cases hκ : κ = κ₀
    · subst hκ; exact h
    · rw [hoff l hl κ hκ, hoff m hm κ hκ]
  obtain ⟨l, hl, m, hm, hlm⟩ := Finset.one_lt_card.1 hcard
  have hne : l κ₀ ≠ m κ₀ := fun h => hlm (hext l hl m hm h)
  have hsigns : (∃ l ∈ Λ, l κ₀ = 2) ∧ (∃ l ∈ Λ, l κ₀ = -2) := by
    rcases hpm l hl with a | a <;> rcases hpm m hm with b | b
    · exact absurd (a.trans b.symm) hne
    · exact ⟨⟨l, hl, a⟩, ⟨m, hm, b⟩⟩
    · exact ⟨⟨m, hm, b⟩, ⟨l, hl, a⟩⟩
    · exact absurd (a.trans b.symm) hne
  exact ⟨Λ, Pi, r, u, N, ε, ψ, hcard, hr, h1, h2, h3, h4', hpm, hsigns.1, hsigns.2,
    fun l hl j => ⟨(hroots l hl).2.2.1 j, hNpos l hl j, (hroots l hl).2.2.2.2.2 j⟩,
    hψ, fun l j => hε l j, hCAR1, hH⟩

end FreeFermionSolutionMultiSectorExample

end SimpleGraph
