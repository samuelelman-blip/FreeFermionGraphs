import FreeFermionGraphs.CrossSectorRelations

/-!
# Non-vacuity of `CrossSectorRelations`: one qubit-mode model

`exists_crossSectorModes_of_cycleSymmetry_commute` has the two premises `hJ`
(`[J_{⟨C₀⟩}, J_{⟨C₁⟩}] = 0`, v1 Theorem 1(iii)) and `hND` (per-sector coprimality of
`z_{∅,l}`, `z_{Ks,l}`).  This module checks that all hypotheses are jointly satisfiable, on the
smallest simplicial-mode Hamiltonian:

* `G` is the graph on one vertex `0` (no edges), `Ks = {0}`;
* two-dimensional complex matrices, `h₀ = Z`, `χ = X` (anticommuting, as `0 ∈ Ks`), coupling
  `b₀ = 1`, i.e. `H = Z`.

`G` has no even hole (an even hole has at least four vertices), so there are no cycle
symmetries, `hJ` is vacuous, and the family `{J_κ}` is the family of junk classes, all `0`; there
is a single sector `Π = 1` (`hND` holds because `z_{Ks,l} = I_{G∖Ks} = 1`, `sectorPolynomial_Ks1`).
The assembled theorem then yields a nonempty `Λ` with `r_l = deg z_{∅,l} = 1` mode in each sector
(`z_{∅,l} = 1 + x`, `sectorPolynomial_empty1`).

The 4-cycle model of `CycleSymmetrySectorsExample` with uniform couplings does *not* satisfy
`hND`: in its sector `J = +1` the polynomials `z_{∅,l} = (1+2x)²`, `z_{Ks,l} = 1+2x` have a common
root (the `C₄` counterexample to v1's Theorem 2).

## Main declarations

* `CrossSectorRelationsExample.ham1` : the model;
* `g1_isClawFree`, `g1_isSimplicialClique`, `g1_cycleSymmetriesCommute`, `ham1_hND`:
  the hypotheses of the assembled theorem;
* `exists_crossSectorModes_ham1` : the conclusion with a nonempty set of sectors, one mode in
  each, and the canonical anticommutation relations.
-/

namespace SimpleGraph

namespace CrossSectorRelationsExample

/-- The graph on one vertex. -/
def g1 : SimpleGraph (Fin 1) := ⊥

/-- The simplicial clique `Ks = {0}`. -/
def Ks1 : Set (Fin 1) := Set.univ

/-- Pauli `Z`. -/
def zM : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- Pauli `X`. -/
def xM : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

theorem zM_mul_self : zM * zM = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [zM, Matrix.mul_apply, Fin.sum_univ_two]

theorem xM_mul_self : xM * xM = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [xM, Matrix.mul_apply, Fin.sum_univ_two]

theorem zM_mul_xM : zM * xM = -(xM * zM) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [zM, xM, Matrix.mul_apply, Fin.sum_univ_two]

theorem zM_isHermitian : zM.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [zM, Matrix.conjTranspose_apply]

theorem xM_isHermitian : xM.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [xM, Matrix.conjTranspose_apply]

/-- The terms: `h₀ = Z`, `χ = X`. -/
def term1 : Option (Fin 1) → Matrix (Fin 2) (Fin 2) ℂ
  | some _ => zM
  | none => xM

theorem xM_mul_zM : xM * zM = -(zM * xM) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [zM, xM, Matrix.mul_apply, Fin.sum_univ_two]

theorem one_ne_neg_one : (1 : Matrix (Fin 2) (Fin 2) ℂ) ≠ -1 := by
  intro h
  have := congrFun (congrFun h 0) 0
  norm_num at this

/-- The Pauli frustration representation of `G⁺`. -/
def rep1 : (g1.adjoinRootAt Ks1).PauliFrustrationRepresentation (Matrix (Fin 2) (Fin 2) ℂ) where
  term := term1
  adj_iff_anticommute := by
    intro j k
    cases j with
    | none =>
      cases k with
      | none =>
        simp only [term1, xM_mul_self]
        exact ⟨fun h => absurd h ((g1.adjoinRootAt Ks1).loopless.irrefl none),
          fun h => absurd h one_ne_neg_one⟩
      | some k =>
        simp only [term1]
        exact ⟨fun _ => xM_mul_zM, fun _ => Set.mem_univ _⟩
    | some j =>
      cases k with
      | none =>
        simp only [term1]
        exact ⟨fun _ => zM_mul_xM, fun _ => Set.mem_univ _⟩
      | some k =>
        simp only [term1, zM_mul_self]
        exact ⟨fun h => absurd h (by simp [g1]), fun h => absurd h one_ne_neg_one⟩
  commute_of_not_adj := by
    intro j k h
    cases j with
    | none =>
      cases k with
      | none => rfl
      | some k => exact absurd (Set.mem_univ k) h
    | some j =>
      cases k with
      | none => exact absurd (Set.mem_univ j) h
      | some k => rfl

/-- **The model**: one vertex, `H = Z`, simplicial mode `χ = X`, coupling `b₀ = 1`. -/
def ham1 : g1.SimplicialModeHamiltonian Ks1 (Matrix (Fin 2) (Fin 2) ℂ) where
  operator := rep1
  coupling := fun _ => 1
  original_term_sq := by
    intro j
    show zM * zM = _
    rw [zM_mul_self]
    simp
  term_selfAdjoint := by
    intro v
    cases v with
    | none => exact xM_isHermitian
    | some j => exact zM_isHermitian
  root_sq := xM_mul_self

/-! ### The hypotheses -/

theorem g1_isClawFree : g1.IsClawFree :=
  fun _ a b _ _ _ _ hab _ _ => absurd (Subsingleton.elim a b) hab

theorem g1_isSimplicialClique : g1.IsSimplicialClique Ks1 :=
  ⟨fun x _ y _ hxy => absurd (Subsingleton.elim x y) hxy,
    fun _ _ x hx => absurd (Set.mem_univ x) hx.2⟩

/-- The graph on one vertex has no even-hole carrier: an even hole has at least four vertices. -/
theorem not_isEvenHoleCarrier_g1 (C : Set (Fin 1)) : ¬ g1.IsEvenHoleCarrier C := by
  rintro ⟨H, -, -⟩
  have h := Fintype.card_le_of_injective H.vertex H.injective
  simp only [Fintype.card_fin] at h
  have h4 := H.four_le_card
  omega

theorem g1_cycleSymmetriesCommute : ham1.frustration.CycleSymmetriesCommute :=
  fun C₀ _ h₀ _ => absurd h₀ (not_isEvenHoleCarrier_g1 C₀)

theorem sectorClassFamilies_g1 (W : Set (Fin 1)) : g1.sectorClassFamilies W = {∅} := by
  ext K
  rw [mem_sectorClassFamilies, Finset.mem_singleton]
  constructor
  · rintro ⟨h, -⟩
    rw [Finset.eq_empty_iff_forall_notMem]
    intro κ hκ
    exact not_isEvenHoleCarrier_g1 _ (h κ hκ).1
  · rintro rfl
    simp

/-- `z_{Ks,l} = 1`: there is no hole family and `G ∖ Ks` is empty. -/
theorem sectorPolynomial_Ks1 (l : g1.EvenHoleDeformationClass → ℝ) :
    g1.sectorPolynomial ham1.coupling Ks1 l = 1 := by
  unfold SimpleGraph.sectorPolynomial
  rw [sectorClassFamilies_g1, Finset.sum_singleton]
  have hind : g1.independentFinsetsAvoid
      (Ks1 ∪ g1.familyBoundary ((∅ : Finset g1.EvenHoleDeformationClass).image Quotient.out) ∪
        g1.openNeighborhood
          (g1.familyBoundary ((∅ : Finset g1.EvenHoleDeformationClass).image Quotient.out))) =
      {∅} := by
    ext S
    simp only [mem_independentFinsetsAvoid, Finset.mem_singleton]
    constructor
    · rintro ⟨-, h⟩
      rw [Finset.eq_empty_iff_forall_notMem]
      intro v hv
      exact h v hv (Or.inl (Or.inl (Set.mem_univ v)))
    · rintro rfl
      exact ⟨by simp [SimpleGraph.IsIndepSet], by simp⟩
  rw [weightedIndependencePolynomial_eq_sum, hind]
  simp [SimpleGraph.familyBoundary]

/-- **`hND` holds in the model**: `z_{Ks,l} = 1` is coprime to everything. -/
theorem ham1_hND (l : g1.EvenHoleDeformationClass → ℝ) :
    IsCoprime (g1.sectorPolynomial ham1.coupling ∅ l)
      (g1.sectorPolynomial ham1.coupling Ks1 l) := by
  rw [sectorPolynomial_Ks1]
  exact isCoprime_one_right

/-- `z_{∅,l} = 1 + x`: the independent sets of the one-vertex graph are `∅` and `{0}`. -/
theorem sectorPolynomial_empty1 (l : g1.EvenHoleDeformationClass → ℝ) :
    g1.sectorPolynomial ham1.coupling ∅ l = 1 + Polynomial.X := by
  unfold SimpleGraph.sectorPolynomial
  rw [sectorClassFamilies_g1, Finset.sum_singleton]
  have hind : g1.independentFinsetsAvoid
      (∅ ∪ g1.familyBoundary ((∅ : Finset g1.EvenHoleDeformationClass).image Quotient.out) ∪
        g1.openNeighborhood
          (g1.familyBoundary ((∅ : Finset g1.EvenHoleDeformationClass).image Quotient.out))) =
      {∅, {0}} := by
    ext S
    simp only [mem_independentFinsetsAvoid, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro -
      rcases S.eq_empty_or_nonempty with h | ⟨v, hv⟩
      · exact Or.inl h
      · right
        ext x
        rw [Finset.mem_singleton, Subsingleton.elim x 0]
        simpa [Subsingleton.elim v 0] using hv
    · intro h
      refine ⟨fun x _ y _ hxy => absurd (Subsingleton.elim x y) hxy, fun v _ hv => ?_⟩
      simp [SimpleGraph.familyBoundary, SimpleGraph.openNeighborhood] at hv
  rw [weightedIndependencePolynomial_eq_sum, hind]
  simp [SimpleGraph.familyBoundary, ham1]

open scoped Classical in
/-- **Non-vacuity of `exists_crossSectorModes_of_cycleSymmetry_commute`.**  All hypotheses of the
assembled theorem hold for the model `ham1` (`g1_isClawFree`, `g1_isSimplicialClique`,
`g1_cycleSymmetriesCommute`, `ham1_hND`), and its conclusion holds with a nonempty set of sectors,
`∑ Π_l = 1`, exactly `deg z_{∅,l} = 1` mode in each sector, and the canonical anticommutation
relations of the explicit modes. -/
theorem exists_crossSectorModes_ham1 :
    ∃ (Λ : Finset (g1.EvenHoleDeformationClass → ℝ))
      (Pi : (g1.EvenHoleDeformationClass → ℝ) → Matrix (Fin 2) (Fin 2) ℂ)
      (r : (g1.EvenHoleDeformationClass → ℝ) → ℕ)
      (ψ : ∀ l, Fin (r l) → Matrix (Fin 2) (Fin 2) ℂ),
      Λ.Nonempty ∧ ∑ l ∈ Λ, Pi l = 1 ∧ (∀ l ∈ Λ, r l = 1) ∧
      (∀ l ∈ Λ, ∀ l' ∈ Λ, ∀ (j : Fin (r l)) (k : Fin (r l')),
        ψ l j * star (ψ l' k) + star (ψ l' k) * ψ l j = if l = l' ∧ HEq j k then Pi l else 0) := by
  obtain ⟨Λ, Pi, r, _u, ψ, -, -, h3, -, -, -, -, -, h9, -, -, -, h13, -, -⟩ :=
    ham1.exists_crossSectorModes_of_cycleSymmetry_commute g1_isClawFree g1_isSimplicialClique
      g1_cycleSymmetriesCommute (fun l _ => ham1_hND l)
  refine ⟨Λ, Pi, r, ψ, ?_, h3, fun l hl => ?_, h13⟩
  · by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.sum_empty] at h3
    exact zero_ne_one h3
  · rw [(h9 l hl).1, sectorPolynomial_empty1]
    rw [add_comm]
    exact Polynomial.natDegree_X_add_C 1

end CrossSectorRelationsExample

end SimpleGraph
