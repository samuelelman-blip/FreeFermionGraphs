import FreeFermionGraphs.Corollary1Unconditional
import FreeFermionGraphs.Corollary1Sector
import FreeFermionGraphs.CrossSectorRelationsExample
import FreeFermionGraphs.Theorem3SectorsExample

/-!
# Non-vacuity of Corollary 1 (the anticommutator matrix)

Manuscript reference: arXiv 2305.15625 v1, Corollary 12 (`corollary:modifiedanticommutationrelation`,
L1341-1392; repository/revised manuscript Corollary 1), `Π_𝒥 {ad^j χ, ad^k χ} = 2 M_{jk} Π_𝒥`.

`Corollary1Sector.lean` proves the identity on a symmetry sector (`paperCorollary1_of_commute`,
`paperCorollary1_of_cycleAlgebra`) and for graphs without even holes
(`paperCorollary1_of_evenHoleFree`); `Corollary1Unconditional.lean` proves it for the joint
eigenprojectors `Π_l` of the cycle symmetries (`paperCorollary1`).  This module checks, on the two
smallest models of the repository, that the hypotheses of these theorems are satisfiable with
`Π ≠ 0` and that their conclusions are informative.

## The models

* The three-qubit `C₄` model `CycleSymmetrySectorsExample.ham` (frustration graph the 4-cycle,
  claw-free, simplicial clique `{0, 1}`, one even hole `{0, 1, 2, 3}` with `J = Z₂`; `J = ±1` are
  the two sectors).  With `Y₂ = [H, [H, χ]]` (integer matrices, `Theorem3SectorsExample`), direct
  matrix computation gives `{Y₂, Y₂} (1 + J) = 128 (1 + J)` and `{Y₂, Y₂} (1 - J) = 256 (1 - J)`
  (`plus_id`, `minus_id`).  Corollary 1 at `j = k = 2` then forces
  `(A_{+1}^4)_{{j*},{j*}} = 4` and `(A_{-1}^4)_{{j*},{j*}} = 8`, i.e. `6 - 2λ`: the tree walks give
  `6` and the two arcs around the hole give `-2λ`.  So the even-hole arcs of the corrected sector
  matrix `cliqueHoppingMatrix` are present and the sector dependence of Theorem 3 and Corollary 1
  is not vacuous.
* The one-vertex model `CrossSectorRelationsExample.ham1` (`H = Z`, `χ = X`), which has no even
  hole: Corollary 1 at `j = k = 1` forces `(T²)_{{j*},{j*}} = 1` for the tree matrix `T`.

## Main declarations

* `Corollary1Example.hopping_plus`, `hopping_minus`: `(A_λ^4)_{{j*},{j*}} = 4` for `λ = +1` and
  `= 8` for `λ = -1`, derived from `paperCorollary1_of_cycleAlgebra` with `Pr = 1 ± J`
  (`J ∈ Algebra.adjoin` of the cycle operators, so `[H, Pr] = 0 = [χ, Pr]` are *derived*).
* `Corollary1Example.hopping_sector_dependent`: the two values differ.
* `Corollary1Example.paperCorollary1_two_sectors`: **non-vacuity of the unconditional
  `paperCorollary1`.**  All its hypotheses hold for the model, and its conclusion holds with
  nonzero projections `Π_l` summing to `1`, both eigenvalues `J = ±1` occurring, and for every
  sector `(A_l^4)_{{j*},{j*}} = 6 - 2 l(⟨C⟩)`, which takes two different values.
* `Corollary1Example.tree_entry`: `(T²)_{{j*},{j*}} = 1` for the one-vertex model, from
  `paperCorollary1_of_evenHoleFree`.
-/

universe u

namespace SimpleGraph

namespace Corollary1Example

/-! ### The three-qubit `C₄` model -/

section FourCycle

open CycleSymmetrySectorsExample Theorem3SectorsExample

/-- The model `ham` as a Pauli clique Hamiltonian representation. -/
abbrev HP : c4.PauliCliqueHamiltonianRepresentation Ks ℝ (Matrix (Fin 8) (Fin 8) ℂ) :=
  ham.toPauliCliqueHamiltonianRepresentation

/-- `[H, [H, χ]]` of the model, with integer entries. -/
def Y2 : Matrix (Fin 8) (Fin 8) ℤ := Hm * Y - Y * Hm

/-- `ad_H² χ = Y₂` in the model. -/
theorem ad2 : iteratedCommutator HP.physicalHamiltonian 2 HP.rootOperator = φ Y2 := by
  rw [iteratedCommutator_succ, iteratedCommutator_succ, iteratedCommutator_zero]
  have h1 : HP.physicalHamiltonian = φ Hm := physicalHamiltonian_eq
  have h2 : HP.rootOperator = φ (M none) := rfl
  rw [h1, h2]
  unfold algebraCommutator Y2 Y
  simp only [map_sub, map_mul]

/-- `{Y₂, Y₂} (1 + Z₂) = 128 (1 + Z₂)`: the anticommutator in the sector `J = +1`. -/
theorem plus_id : (Y2 * Y2 + Y2 * Y2) * (1 + zOp 2) = (128 : ℤ) • (1 + zOp 2) := by
  decide +kernel

/-- `{Y₂, Y₂} (1 - Z₂) = 256 (1 - Z₂)`: the anticommutator in the sector `J = -1`. -/
theorem minus_id : (Y2 * Y2 + Y2 * Y2) * (1 - zOp 2) = (256 : ℤ) • (1 - zOp 2) := by
  decide +kernel

theorem Z_plus : zOp 2 * (1 + zOp 2) = 1 + zOp 2 := by decide +kernel

theorem Z_minus : zOp 2 * (1 - zOp 2) = -(1 - zOp 2) := by decide +kernel

theorem plus_ne : (1 + zOp 2 : Matrix (Fin 8) (Fin 8) ℤ) ≠ 0 := by decide +kernel

theorem minus_ne : (1 - zOp 2 : Matrix (Fin 8) (Fin 8) ℤ) ≠ 0 := by decide +kernel

/-- The cycle operator of the class of the (unique) even hole is `Z₂`. -/
theorem J_eq : HP.generalizedCycleOperator (c4.evenHoleDeformationClassOf Set.univ) = φ (zOp 2) := by
  rw [PauliCliqueHamiltonianRepresentation.generalizedCycleOperator_mk]
  exact cycleSymmetry_eq

/-- Every labelling with full cyclic order has carrier `univ`, so its cycle operator is `Z₂`. -/
theorem J_eq' {k : ℕ} (E : c4.EvenHoleLabeling k) (hE : E.HasFullCyclicOrder) :
    HP.generalizedCycleOperator (c4.evenHoleDeformationClassOf E.carrier) = φ (zOp 2) := by
  rw [eq_univ_of_isEvenHoleCarrier (E.isEvenHoleCarrier_of_hasFullCyclicOrder hE)]
  exact J_eq

/-- `Z₂` lies in the algebra generated by the cycle operators. -/
theorem mem_adjoin_J :
    φ (zOp 2) ∈ Algebra.adjoin ℝ {J : Matrix (Fin 8) (Fin 8) ℂ | ∃ C : Set (Fin 4),
      c4.IsEvenHoleCarrier C ∧ J = HP.generalizedCycleOperator (c4.evenHoleDeformationClassOf C)} :=
  Algebra.subset_adjoin ⟨Set.univ, isEvenHoleCarrier_univ, J_eq.symm⟩

/-- The value of the hopping matrix in a sector, from `paperCorollary1_of_cycleAlgebra`: if
`Z' ≠ 0` lies in the algebra generated by the cycle operators, `Z₂ Z' = ±Z'` and
`{Y₂, Y₂} Z' = c Z'`, then `c = 2 (-1)² (-2)^4 (A_λ^4)_{{j*},{j*}}` for the sector label `λ = ±1`. -/
theorem sector_value [DecidableEq (c4.CliqueRootedInducedPath Ks)] (s : ℝ) (Z' : Matrix (Fin 8) (Fin 8) ℤ) (c : ℤ)
    (hZ'mem : φ Z' ∈ Algebra.adjoin ℝ {J : Matrix (Fin 8) (Fin 8) ℂ | ∃ C : Set (Fin 4),
      c4.IsEvenHoleCarrier C ∧ J = HP.generalizedCycleOperator (c4.evenHoleDeformationClassOf C)})
    (hZ' : zOp 2 * Z' = (if s = 1 then Z' else -Z')) (hs : s = 1 ∨ s = -1)
    (hne : Z' ≠ 0) (hval : (Y2 * Y2 + Y2 * Y2) * Z' = c • Z') :
    (c : ℝ) = 2 * (-1) ^ 2 * (-2) ^ (2 + 2) *
      (cliqueHoppingMatrix c4 Ks HP.coupling (fun _ => s) ^ (2 + 2)) (cliqueRootPath c4 Ks)
        (cliqueRootPath c4 Ks) := by
  have hJ : ∀ (k : ℕ) (E : c4.EvenHoleLabeling k), E.HasFullCyclicOrder →
      HP.generalizedCycleOperator (c4.evenHoleDeformationClassOf E.carrier) * φ Z' =
        (fun _ => s) (c4.evenHoleDeformationClassOf E.carrier) • φ Z' := by
    intro k E hE
    rw [J_eq' E hE, ← map_mul, hZ']
    rcases hs with rfl | rfl
    · simp
    · rw [if_neg (by norm_num), map_neg]
      simp
  have hχ : HP.rootOperator * HP.rootOperator = 1 := ham.root_sq
  have hc := PauliCliqueHamiltonianRepresentation.paperCorollary1_of_cycleAlgebra
    c4_isSimplicialClique c4_isClawFree HP (φ Z') hZ'mem hχ (fun _ => s) hJ 2 2
  rw [ad2, ← map_mul, ← map_add, ← map_mul, hval, map_zsmul,
    ← Int.cast_smul_eq_zsmul ℝ] at hc
  have hne' : φ Z' ≠ 0 := fun h => hne (φ_injective (h.trans (map_zero φ).symm))
  have h0 := sub_eq_zero.2 hc
  rw [← sub_smul] at h0
  exact sub_eq_zero.1 ((smul_eq_zero.1 h0).resolve_right hne')

/-- **The sector `λ = +1`**: `(A_{+1}^4)_{{j*},{j*}} = 4` (tree walks `6`, hole arcs `-2`),
forced by Corollary 1 at `j = k = 2` with `Pr = 1 + J`. -/
theorem hopping_plus [DecidableEq (c4.CliqueRootedInducedPath Ks)] :
    (cliqueHoppingMatrix c4 Ks HP.coupling (fun _ => 1) ^ 4) (cliqueRootPath c4 Ks)
      (cliqueRootPath c4 Ks) = 4 := by
  have hmem : φ (1 + zOp 2) ∈ Algebra.adjoin ℝ {J : Matrix (Fin 8) (Fin 8) ℂ | ∃ C : Set (Fin 4),
      c4.IsEvenHoleCarrier C ∧ J = HP.generalizedCycleOperator (c4.evenHoleDeformationClassOf C)} := by
    rw [map_add, map_one]
    exact Subalgebra.add_mem _ (Subalgebra.one_mem _) mem_adjoin_J
  have h := sector_value 1 (1 + zOp 2) 128 hmem (by rw [if_pos rfl]; exact Z_plus) (Or.inl rfl)
    plus_ne plus_id
  norm_num at h
  linarith

/-- **The sector `λ = -1`**: `(A_{-1}^4)_{{j*},{j*}} = 8` (tree walks `6`, hole arcs `+2`),
forced by Corollary 1 at `j = k = 2` with `Pr = 1 - J`. -/
theorem hopping_minus [DecidableEq (c4.CliqueRootedInducedPath Ks)] :
    (cliqueHoppingMatrix c4 Ks HP.coupling (fun _ => -1) ^ 4) (cliqueRootPath c4 Ks)
      (cliqueRootPath c4 Ks) = 8 := by
  have hmem : φ (1 - zOp 2) ∈ Algebra.adjoin ℝ {J : Matrix (Fin 8) (Fin 8) ℂ | ∃ C : Set (Fin 4),
      c4.IsEvenHoleCarrier C ∧ J = HP.generalizedCycleOperator (c4.evenHoleDeformationClassOf C)} := by
    rw [map_sub, map_one]
    exact Subalgebra.sub_mem _ (Subalgebra.one_mem _) mem_adjoin_J
  have h := sector_value (-1) (1 - zOp 2) 256 hmem (by rw [if_neg (by norm_num)]; exact Z_minus)
    (Or.inr rfl) minus_ne minus_id
  norm_num at h
  linarith

/-- The sector dependence is real: the corrected hopping matrix differs between the sectors. -/
theorem hopping_sector_dependent [DecidableEq (c4.CliqueRootedInducedPath Ks)] :
    (cliqueHoppingMatrix c4 Ks HP.coupling (fun _ => 1) ^ 4) (cliqueRootPath c4 Ks)
      (cliqueRootPath c4 Ks) ≠
    (cliqueHoppingMatrix c4 Ks HP.coupling (fun _ => -1) ^ 4) (cliqueRootPath c4 Ks)
      (cliqueRootPath c4 Ks) := by
  rw [hopping_plus, hopping_minus]
  norm_num

/-! #### The unconditional `paperCorollary1` on the model -/

/-- If `S (1 + u Z) = c (1 + u Z)`, `Z Π = ε Π` and `u ε = 1`, then `S Π = c Π`: on the range of
`Π` the operator `1 + u Z` acts as `2`. -/
theorem mul_sector_of_mul_eq {S Z Pi : Matrix (Fin 8) (Fin 8) ℂ} {u ε c : ℂ}
    (hS : S * (1 + u • Z) = c • (1 + u • Z)) (hZ : Z * Pi = ε • Pi) (hue : u * ε = 1) :
    S * Pi = c • Pi := by
  have h1 : (1 + u • Z) * Pi = (2 : ℂ) • Pi := by
    rw [add_mul, one_mul, smul_mul_assoc, hZ, smul_smul, hue, one_smul, two_smul]
  have h2 : (2 : ℂ) • (S * Pi) = (2 : ℂ) • (c • Pi) :=
    calc (2 : ℂ) • (S * Pi) = S * ((1 + u • Z) * Pi) := by rw [h1, Matrix.mul_smul]
      _ = (S * (1 + u • Z)) * Pi := by rw [mul_assoc]
      _ = c • ((1 + u • Z) * Pi) := by rw [hS, smul_mul_assoc]
      _ = (2 : ℂ) • (c • Pi) := by rw [h1, smul_comm]
  exact smul_right_injective _ (two_ne_zero : (2 : ℂ) ≠ 0) h2

/-- `{Y₂, Y₂} Π = 128 Π` if `J Π = Π`. -/
theorem anticommutator_mul_plus {Pi : Matrix (Fin 8) (Fin 8) ℂ}
    (hJ : φ (zOp 2) * Pi = (1 : ℂ) • Pi) :
    φ (Y2 * Y2 + Y2 * Y2) * Pi = (128 : ℂ) • Pi := by
  refine mul_sector_of_mul_eq (u := 1) (ε := 1) ?_ hJ (one_mul 1)
  have h := congrArg φ plus_id
  rw [map_mul φ (Y2 * Y2 + Y2 * Y2) (1 + zOp 2), map_zsmul, map_add φ 1 (zOp 2), map_one φ,
    ← Int.cast_smul_eq_zsmul ℂ] at h
  rw [one_smul]
  simpa using h

/-- `{Y₂, Y₂} Π = 256 Π` if `J Π = -Π`. -/
theorem anticommutator_mul_minus {Pi : Matrix (Fin 8) (Fin 8) ℂ}
    (hJ : φ (zOp 2) * Pi = (-1 : ℂ) • Pi) :
    φ (Y2 * Y2 + Y2 * Y2) * Pi = (256 : ℂ) • Pi := by
  refine mul_sector_of_mul_eq (u := -1) (ε := -1) ?_ hJ (by norm_num)
  have h := congrArg φ minus_id
  rw [map_mul φ (Y2 * Y2 + Y2 * Y2) (1 - zOp 2), map_zsmul, map_sub φ 1 (zOp 2), map_one φ,
    ← Int.cast_smul_eq_zsmul ℂ] at h
  rw [neg_one_smul, ← sub_eq_add_neg]
  simpa using h

/-- `{ad_{iH}² χ, ad_{iH}² χ} = {Y₂, Y₂}` in the model (`(iH)² = -H²`, and the sign cancels in the
anticommutator). -/
theorem anticommutator_ad_iH_two :
    iteratedCommutator (Complex.I • HP.physicalHamiltonian) 2 HP.rootOperator *
          iteratedCommutator (Complex.I • HP.physicalHamiltonian) 2 HP.rootOperator +
        iteratedCommutator (Complex.I • HP.physicalHamiltonian) 2 HP.rootOperator *
          iteratedCommutator (Complex.I • HP.physicalHamiltonian) 2 HP.rootOperator =
      φ (Y2 * Y2 + Y2 * Y2) := by
  rw [PauliCliqueHamiltonianRepresentation.iteratedCommutator_smul_left, ad2, Complex.I_sq, map_add, map_mul]
  simp only [neg_smul, one_smul, neg_mul_neg]

/-- **Non-vacuity of the unconditional `paperCorollary1`.**  For the model `ham` (a
simplicial-mode Hamiltonian on three qubits with frustration graph the 4-cycle, claw-free, with
simplicial clique `{0, 1}`, whose cycle symmetry `J = Z₂` genuinely acts), regarded as a Pauli
clique Hamiltonian representation, the hypotheses of `paperCorollary1` hold (`c4_isSimplicialClique`,
`c4_isClawFree`, the field `term_selfAdjoint`, the field `root_sq`), and the conclusion is
informative: there are nonzero projections `Π_l` (`l ∈ Λ`) with `∑ Π_l = 1` and
`J Π_l = l(⟨C⟩) Π_l`, the eigenvalues `l(⟨C⟩)` are `±1` and both occur, and for every sector
`(A_l^4)_{{j*},{j*}} = 6 - 2 l(⟨C⟩)` (the value forced by the identity of Corollary 1 at
`j = k = 2`), so that the corrected hopping matrix takes different values in the two sectors.
No commutation hypothesis on the cycle symmetries is supplied. -/
theorem paperCorollary1_two_sectors [DecidableEq (c4.CliqueRootedInducedPath Ks)] :
    ∃ (Λ : Finset (c4.EvenHoleDeformationClass → ℝ))
      (Pi : (c4.EvenHoleDeformationClass → ℝ) → Matrix (Fin 8) (Fin 8) ℂ),
      ∑ l ∈ Λ, Pi l = 1 ∧ (∀ l ∈ Λ, Pi l ≠ 0) ∧
      (∀ l ∈ Λ, ham.frustration.generalizedCycleSymmetryOp Set.univ * Pi l =
          ((l (c4.evenHoleDeformationClassOf Set.univ) : ℝ) : ℂ) • Pi l) ∧
      (∀ l ∈ Λ, l (c4.evenHoleDeformationClassOf Set.univ) = 1 ∨
        l (c4.evenHoleDeformationClassOf Set.univ) = -1) ∧
      (∃ l ∈ Λ, l (c4.evenHoleDeformationClassOf Set.univ) = 1) ∧
      (∃ l ∈ Λ, l (c4.evenHoleDeformationClassOf Set.univ) = -1) ∧
      (∀ l ∈ Λ, (cliqueHoppingMatrix c4 Ks ham.coupling l ^ 4) (cliqueRootPath c4 Ks)
          (cliqueRootPath c4 Ks) = 6 - 2 * l (c4.evenHoleDeformationClassOf Set.univ)) ∧
      (∃ l ∈ Λ, ∃ m ∈ Λ, (cliqueHoppingMatrix c4 Ks ham.coupling l ^ 4) (cliqueRootPath c4 Ks)
          (cliqueRootPath c4 Ks) ≠
        (cliqueHoppingMatrix c4 Ks ham.coupling m ^ 4) (cliqueRootPath c4 Ks)
          (cliqueRootPath c4 Ks)) := by
  obtain ⟨Λ, Pi, h1, -, h3, h4, -, -, -, h8⟩ :=
    PauliCliqueHamiltonianRepresentation.paperCorollary1 c4_isSimplicialClique c4_isClawFree
      HP (fun j => ham.term_selfAdjoint (some j)) ham.root_sq
  have h4' : ∀ l ∈ Λ, ham.frustration.generalizedCycleSymmetryOp Set.univ * Pi l =
      ((l (c4.evenHoleDeformationClassOf Set.univ) : ℝ) : ℂ) • Pi l :=
    fun l hl => h4 l hl Set.univ isEvenHoleCarrier_univ
  -- the eigenvalues are `±1` since `J² = 1`
  have hpm : ∀ l ∈ Λ, l (c4.evenHoleDeformationClassOf Set.univ) = 1 ∨
      l (c4.evenHoleDeformationClassOf Set.univ) = -1 := by
    intro l hl
    have e : Pi l = (((l (c4.evenHoleDeformationClassOf Set.univ) : ℝ) : ℂ) *
        ((l (c4.evenHoleDeformationClassOf Set.univ) : ℝ) : ℂ)) • Pi l := by
      calc Pi l = (ham.frustration.generalizedCycleSymmetryOp Set.univ *
            ham.frustration.generalizedCycleSymmetryOp Set.univ) * Pi l := by
              rw [cycleSymmetry_mul_self, one_mul]
        _ = ham.frustration.generalizedCycleSymmetryOp Set.univ *
            (ham.frustration.generalizedCycleSymmetryOp Set.univ * Pi l) := mul_assoc _ _ _
        _ = _ := by
              rw [h4' l hl, Matrix.mul_smul, h4' l hl, smul_smul]
    have e' : (((l (c4.evenHoleDeformationClassOf Set.univ) : ℝ) : ℂ) *
        ((l (c4.evenHoleDeformationClassOf Set.univ) : ℝ) : ℂ) - 1) • Pi l = 0 := by
      rw [sub_smul, one_smul, ← e, sub_self]
    have hcc := sub_eq_zero.1 ((smul_eq_zero.1 e').resolve_right (h1 l hl).2.2)
    have hcc' : l (c4.evenHoleDeformationClassOf Set.univ) *
        l (c4.evenHoleDeformationClassOf Set.univ) = 1 := by exact_mod_cast hcc
    exact mul_self_eq_one_iff.1 hcc'
  -- both eigenvalues occur, since `J = ∑ l(⟨C⟩) Π_l` is not a scalar
  have hboth : ∀ s : ℝ, (∀ l ∈ Λ, l (c4.evenHoleDeformationClassOf Set.univ) = s) →
      ham.frustration.generalizedCycleSymmetryOp Set.univ = (s : ℂ) • (1 : Matrix (Fin 8) (Fin 8) ℂ) := by
    intro s hs
    calc ham.frustration.generalizedCycleSymmetryOp Set.univ
        = ham.frustration.generalizedCycleSymmetryOp Set.univ * ∑ l ∈ Λ, Pi l := by
          rw [h3, mul_one]
      _ = ∑ l ∈ Λ, ham.frustration.generalizedCycleSymmetryOp Set.univ * Pi l :=
          Finset.mul_sum _ _ _
      _ = ∑ l ∈ Λ, (s : ℂ) • Pi l :=
          Finset.sum_congr rfl fun l hl => by rw [h4' l hl, hs l hl]
      _ = (s : ℂ) • (1 : Matrix (Fin 8) (Fin 8) ℂ) := by rw [← Finset.smul_sum, h3]
  have hplus : ∃ l ∈ Λ, l (c4.evenHoleDeformationClassOf Set.univ) = 1 := by
    by_contra hno
    push Not at hno
    refine cycleSymmetry_not_scalar (((-1 : ℝ)) : ℂ) (hboth (-1) fun l hl => ?_)
    exact (hpm l hl).resolve_left (hno l hl)
  have hminus : ∃ l ∈ Λ, l (c4.evenHoleDeformationClassOf Set.univ) = -1 := by
    by_contra hno
    push Not at hno
    refine cycleSymmetry_not_scalar (((1 : ℝ)) : ℂ) (hboth 1 fun l hl => ?_)
    exact (hpm l hl).resolve_right (hno l hl)
  -- the value of the hopping matrix in each sector
  have hval : ∀ l ∈ Λ, (cliqueHoppingMatrix c4 Ks ham.coupling l ^ 4) (cliqueRootPath c4 Ks)
      (cliqueRootPath c4 Ks) = 6 - 2 * l (c4.evenHoleDeformationClassOf Set.univ) := by
    intro l hl
    obtain ⟨M, -, hent, -, hright⟩ := h8 l hl
    have hPi : Pi l ≠ 0 := (h1 l hl).2.2
    have hJl : φ (zOp 2) * Pi l = ((l (c4.evenHoleDeformationClassOf Set.univ) : ℝ) : ℂ) • Pi l := by
      rw [← cycleSymmetry_eq]
      exact h4' l hl
    have hr := hright 2 2
    rw [anticommutator_ad_iH_two] at hr
    -- `M 2 2` and the hopping entry
    have hMc : (2 : ℂ) * (M 2 2 : ℂ) =
        if l (c4.evenHoleDeformationClassOf Set.univ) = 1 then 128 else 256 := by
      rcases hpm l hl with h | h
      · have hJ1 : φ (zOp 2) * Pi l = (1 : ℂ) • Pi l := by rw [hJl, h]; simp
        rw [anticommutator_mul_plus hJ1] at hr
        have := sub_eq_zero.2 hr
        rw [← sub_smul] at this
        rw [if_pos h]
        exact (sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_right hPi)).symm
      · have hJ1 : φ (zOp 2) * Pi l = (-1 : ℂ) • Pi l := by rw [hJl, h]; simp
        rw [anticommutator_mul_minus hJ1] at hr
        have := sub_eq_zero.2 hr
        rw [← sub_smul] at this
        rw [if_neg (by rw [h]; norm_num)]
        exact (sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_right hPi)).symm
    have he := hent 2 2
    have hsq : (-2 * Complex.I) ^ 2 = -4 := by
      rw [mul_pow, Complex.I_sq]
      norm_num
    have hpow : (-2 * Complex.I) ^ (2 + 2) = 16 := by
      rw [show 2 + 2 = 2 * 2 from rfl, pow_mul, hsq]
      norm_num
    rw [hpow] at he
    have hA : ((16 : ℂ) * (((cliqueHoppingMatrix c4 Ks ham.coupling l ^ (2 + 2)) (cliqueRootPath c4 Ks)
        (cliqueRootPath c4 Ks) : ℝ) : ℂ)) =
        (if l (c4.evenHoleDeformationClassOf Set.univ) = 1 then 64 else 128) := by
      have : (16 : ℂ) * (((cliqueHoppingMatrix c4 Ks ham.coupling l ^ (2 + 2)) (cliqueRootPath c4 Ks)
          (cliqueRootPath c4 Ks) : ℝ) : ℂ) = (M 2 2 : ℂ) := by
        rw [he]; ring
      rw [this]
      split_ifs at hMc ⊢ <;> linear_combination hMc / 2
    rcases hpm l hl with h | h
    · rw [if_pos h] at hA
      rw [h]
      have : (((cliqueHoppingMatrix c4 Ks ham.coupling l ^ (2 + 2)) (cliqueRootPath c4 Ks)
          (cliqueRootPath c4 Ks) : ℝ) : ℂ) = ((4 : ℝ) : ℂ) := by
        push_cast
        linear_combination hA / 16
      have h4r := Complex.ofReal_injective this
      norm_num at h4r ⊢
      linarith
    · rw [if_neg (by rw [h]; norm_num)] at hA
      rw [h]
      have : (((cliqueHoppingMatrix c4 Ks ham.coupling l ^ (2 + 2)) (cliqueRootPath c4 Ks)
          (cliqueRootPath c4 Ks) : ℝ) : ℂ) = ((8 : ℝ) : ℂ) := by
        push_cast
        linear_combination hA / 16
      have h8r := Complex.ofReal_injective this
      norm_num at h8r ⊢
      linarith
  refine ⟨Λ, Pi, h3, fun l hl => (h1 l hl).2.2, h4', hpm, hplus, hminus, hval, ?_⟩
  obtain ⟨l, hl, hl1⟩ := hplus
  obtain ⟨m, hm, hm1⟩ := hminus
  refine ⟨l, hl, m, hm, ?_⟩
  rw [hval l hl, hval m hm, hl1, hm1]
  norm_num

end FourCycle

/-! ### The one-vertex model (no even hole) -/

section OneVertex

open CrossSectorRelationsExample

/-- The one-vertex model as a Pauli clique Hamiltonian representation. -/
abbrev HP1 : g1.PauliCliqueHamiltonianRepresentation Ks1 ℝ (Matrix (Fin 2) (Fin 2) ℂ) :=
  ham1.toPauliCliqueHamiltonianRepresentation

/-- `g1` has no even hole: a hole has at least four vertices and `g1` has one. -/
theorem hfree1 : ∀ C : g1.IndexedInducedHole, ¬ Even C.card := by
  intro C _
  have h := Fintype.card_le_of_injective C.vertex C.injective
  simp only [Fintype.card_fin] at h
  have h4 := C.four_le_card
  omega

theorem phys1 : HP1.physicalHamiltonian = zM := by
  unfold PauliCliqueHamiltonianRepresentation.physicalHamiltonian
  rw [Fin.sum_univ_one]
  rfl

theorem ad1 :
    iteratedCommutator HP1.physicalHamiltonian 1 HP1.rootOperator = zM * xM - xM * zM := by
  rw [iteratedCommutator_succ, iteratedCommutator_zero, phys1]
  rfl

theorem anti11 : (zM * xM - xM * zM) * (zM * xM - xM * zM) +
    (zM * xM - xM * zM) * (zM * xM - xM * zM) = (-8 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zM, xM] <;> norm_num

/-- **Corollary 1 without even holes, on the one-vertex model**: the hypotheses of
`paperCorollary1_of_evenHoleFree` hold and `{ad_H χ, ad_H χ} = -8` forces
`(T²)_{{j*},{j*}} = 1` for the tree matrix `T` (the rooted induced paths are `{j*}` and
`{j*, 0}`, and `T` has weight `b₀² = 1` on the single arc between them). -/
theorem tree_entry [DecidableEq (g1.CliqueRootedInducedPath Ks1)] :
    (cliqueTreeMatrix g1 Ks1 HP1.coupling ^ (1 + 1)) (cliqueRootPath g1 Ks1)
      (cliqueRootPath g1 Ks1) = 1 := by
  have hc := PauliCliqueHamiltonianRepresentation.paperCorollary1_of_evenHoleFree
    g1_isSimplicialClique g1_isClawFree hfree1 HP1 ham1.root_sq 1 1
  rw [ad1, anti11, Algebra.algebraMap_eq_smul_one] at hc
  have h00 := congrFun (congrFun hc 0) 0
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h00
  have h' : ((-8 : ℝ) : ℂ) = ((2 * (-1) ^ 1 * (-2) ^ (1 + 1) *
      (cliqueTreeMatrix g1 Ks1 HP1.coupling ^ (1 + 1)) (cliqueRootPath g1 Ks1)
        (cliqueRootPath g1 Ks1) : ℝ) : ℂ) := by
    rw [← Complex.coe_smul] at h00
    push_cast at h00 ⊢
    simpa using h00
  have h'' := Complex.ofReal_injective h'
  norm_num at h''
  linarith

end OneVertex

end Corollary1Example

end SimpleGraph
