import FreeFermionGraphs.Theorem3Sectors
import FreeFermionGraphs.CycleSymmetrySectorsExample

/-!
# Non-vacuity of `Theorem3Sectors`: the 4-cycle with a simplicial mode

`Theorem3Sectors` proves v1 Theorem 3 over the joint spectral projectors `Π_l` of the cycle
symmetries `J_{⟨C₀⟩}`, conditional on `[J, J'] = 0`.  This module instantiates it on the model of
`CycleSymmetrySectorsExample` (the 4-cycle `G = c4` with the simplicial clique `Ks = {0, 1}` on
three qubits, with the unique even hole `{0, 1, 2, 3}` and `J = Z₂`, which splits the 8-dimensional
space into two sectors `J = ±1`), to check that the hypotheses are satisfiable and that the
conclusion is not empty:

* the hypotheses `hclaw`, `hKs`, `hJ` of `paperTheorem3_modeSectors_of_cycleSymmetry_commute`
  hold (`CycleSymmetrySectorsExample.c4_isClawFree`, `c4_isSimplicialClique`,
  `ham_cycleSymmetriesCommute`);
* the conclusion holds with at least two sectors, each `Π_l` a proper nonzero projection, with the
  eigenvalues `J = +1` and `J = -1` both occurring, and with the Theorem 3 identity for every
  `l ∈ Λ` and every `k`;
* the left side of the Theorem 3 identity is not zero: `ad_{iH} χ = 2i (h₀ + h₁) χ` is invertible
  (`(ad_{iH} χ)² = 8`, `ad_one_sq`), so `ad_{iH} χ · Π_l ≠ 0` in every sector.  (The Theorem 3
  identity at `k = 1` therefore equates a nonzero operator with the Krylov expansion
  `-2i ∑_P (A_l)_{{j*},P} h_P Π_l`, not `0` with `0`.)

## Main declarations

* `Theorem3SectorsExample.ad_one_sq`: `(ad_{iH} χ)² = 8` in the model.
* `Theorem3SectorsExample.theorem3_two_sectors`: the instantiation.
-/

universe u

namespace SimpleGraph

namespace Theorem3SectorsExample

open CycleSymmetrySectorsExample

/-! ### `ad_{iH} χ` is invertible -/

/-- `H = h₀ + h₁ + h₂ + h₃` of the model, with integer entries. -/
def Hm : Matrix (Fin 8) (Fin 8) ℤ := M (some 0) + M (some 1) + M (some 2) + M (some 3)

/-- `[H, χ]` of the model, with integer entries. -/
def Y : Matrix (Fin 8) (Fin 8) ℤ := Hm * M none - M none * Hm

/-- `[H, χ]² = -8` in the model: `[H, χ] = 2 (h₀ + h₁) χ`, `(h₀ + h₁)² = 2` (anticommuting
Pauli terms) and `χ` anticommutes with `h₀ + h₁`. -/
theorem Y_sq : Y * Y = (-8 : ℤ) • (1 : Matrix (Fin 8) (Fin 8) ℤ) := by decide +kernel

theorem physicalHamiltonian_eq : ham.physicalHamiltonian = φ Hm := by
  unfold PauliCliqueHamiltonianRepresentation.physicalHamiltonian Hm
  rw [Fin.sum_univ_four]
  simp only [map_add]
  rfl

theorem rootOperator_eq : ham.rootOperator = φ (M none) := rfl

/-- `ad_{iH} χ = i [H, χ]` in the model. -/
theorem ad_one :
    iteratedCommutator (Complex.I • ham.physicalHamiltonian) 1 ham.rootOperator =
      Complex.I • φ Y := by
  rw [iteratedCommutator_succ, iteratedCommutator_zero, physicalHamiltonian_eq, rootOperator_eq]
  unfold algebraCommutator Y
  rw [map_sub, map_mul, map_mul, smul_mul_assoc, Matrix.mul_smul, smul_sub]

/-- `(ad_{iH} χ)² = 8` in the model (`(i [H, χ])² = -[H, χ]² = 8`). -/
theorem ad_one_sq :
    iteratedCommutator (Complex.I • ham.physicalHamiltonian) 1 ham.rootOperator *
      iteratedCommutator (Complex.I • ham.physicalHamiltonian) 1 ham.rootOperator =
        (8 : ℂ) • (1 : Matrix (Fin 8) (Fin 8) ℂ) := by
  rw [ad_one, smul_mul_smul_comm, ← map_mul, Y_sq, map_zsmul, map_one,
    ← Int.cast_smul_eq_zsmul ℂ, Complex.I_mul_I, smul_smul]
  norm_num

/-- `ad_{iH} χ · P = 0` forces `P = 0` in the model: `ad_{iH} χ` is invertible. -/
theorem eq_zero_of_ad_one_mul_eq_zero {P : Matrix (Fin 8) (Fin 8) ℂ}
    (h : iteratedCommutator (Complex.I • ham.physicalHamiltonian) 1 ham.rootOperator * P = 0) :
    P = 0 := by
  have h2 : ((8 : ℂ) • (1 : Matrix (Fin 8) (Fin 8) ℂ)) * P = 0 := by
    rw [← ad_one_sq, mul_assoc, h, mul_zero]
  rw [smul_mul_assoc, one_mul] at h2
  exact (smul_eq_zero.1 h2).resolve_left (by norm_num)

/-! ### The instantiation -/

/-- **Non-vacuity of `paperTheorem3_modeSectors_of_cycleSymmetry_commute`.**  For the model `ham`
(a simplicial-mode Hamiltonian on three qubits with frustration graph the 4-cycle, claw-free, with
simplicial clique `{0, 1}`, whose cycle symmetry `J = Z₂` genuinely acts), the hypotheses of the
theorem hold, and the conclusion holds with two sectors: there are projections `Π_l` (`l ∈ Λ`),
none of them `0` or `1`, with `∑ Π_l = 1` and `J Π_l = l(⟨C⟩) Π_l`, the eigenvalues `l(⟨C⟩)` are
`±1` and both occur, and for every `l ∈ Λ`: the matrix `A_l` is bipartite, `Π_l` commutes with
every `ad_{iH}^k χ`, `Π_l ad_{iH}^k χ = ad_{iH}^k χ Π_l = (-2i)^k ∑_P (A_l^k)_{{j*},P} h_P Π_l`,
and the left side at `k = 1` is not zero.  Every `Π_l` is the projection of a `ModeSector`. -/
theorem theorem3_two_sectors [DecidableEq (c4.CliqueRootedInducedPath Ks)] :
    ∃ (Λ : Finset (c4.EvenHoleDeformationClass → ℝ))
      (Pi : (c4.EvenHoleDeformationClass → ℝ) → Matrix (Fin 8) (Fin 8) ℂ),
      2 ≤ Λ.card ∧
      (∀ l ∈ Λ, (Pi l).IsHermitian ∧ Pi l * Pi l = Pi l ∧ Pi l ≠ 0 ∧ Pi l ≠ 1) ∧
      ∑ l ∈ Λ, Pi l = 1 ∧
      (∀ l ∈ Λ, ham.frustration.generalizedCycleSymmetryOp Set.univ * Pi l =
          ((l (c4.evenHoleDeformationClassOf Set.univ) : ℝ) : ℂ) • Pi l) ∧
      (∀ l ∈ Λ, l (c4.evenHoleDeformationClassOf Set.univ) = 1 ∨
        l (c4.evenHoleDeformationClassOf Set.univ) = -1) ∧
      (∃ l ∈ Λ, l (c4.evenHoleDeformationClassOf Set.univ) = 1) ∧
      (∃ l ∈ Λ, l (c4.evenHoleDeformationClassOf Set.univ) = -1) ∧
      (∀ l ∈ Λ, ∃ S : ham.ModeSector, S.Pi = Pi l ∧
        S.zG = c4.sectorPolynomial ham.coupling ∅ l ∧
        S.zK = c4.sectorPolynomial ham.coupling Ks l) ∧
      (∀ l ∈ Λ,
        (∀ P Q : c4.CliqueRootedInducedPath Ks,
          cliqueHoppingMatrix c4 Ks ham.coupling l P Q ≠ 0 →
            Odd (P.path.card + Q.path.card)) ∧
        (∀ k : ℕ,
          Commute (Pi l)
              (iteratedCommutator (Complex.I • ham.physicalHamiltonian) k ham.rootOperator) ∧
          Pi l * iteratedCommutator (Complex.I • ham.physicalHamiltonian) k ham.rootOperator =
            ∑ P : c4.CliqueRootedInducedPath Ks,
              ((-2 * Complex.I) ^ k *
                  ((cliqueHoppingMatrix c4 Ks ham.coupling l ^ k) (cliqueRootPath c4 Ks) P :
                    ℂ)) •
                (ham.pathOperator P * Pi l) ∧
          iteratedCommutator (Complex.I • ham.physicalHamiltonian) k ham.rootOperator * Pi l =
            ∑ P : c4.CliqueRootedInducedPath Ks,
              ((-2 * Complex.I) ^ k *
                  ((cliqueHoppingMatrix c4 Ks ham.coupling l ^ k) (cliqueRootPath c4 Ks) P :
                    ℂ)) •
                (ham.pathOperator P * Pi l)) ∧
        iteratedCommutator (Complex.I • ham.physicalHamiltonian) 1 ham.rootOperator * Pi l ≠ 0) := by
  obtain ⟨Λ, Pi, h1, h2, h3, h4, h5, -, -, h8, h9⟩ :=
    ham.paperTheorem3_modeSectors_of_cycleSymmetry_commute c4_isClawFree c4_isSimplicialClique
      ham_cycleSymmetriesCommute
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
  -- there are two distinct sectors, because `J` is not a scalar
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
    exact cycleSymmetry_not_scalar _ h
  obtain ⟨l, hl, m, hm, hlm⟩ := Finset.one_lt_card.1 hcard
  -- distinct sectors have distinct eigenvalues: the junk coordinates vanish
  have hval : l (c4.evenHoleDeformationClassOf Set.univ) ≠
      m (c4.evenHoleDeformationClassOf Set.univ) := by
    intro heq
    apply hlm
    funext κ
    by_cases hκ : c4.IsEvenHoleClass κ
    · rw [eq_classOf_univ_of_isEvenHoleClass hκ]
      exact heq
    · rw [h5 l hl κ hκ, h5 m hm κ hκ]
  refine ⟨Λ, Pi, hcard, fun l hl => ⟨(h1 l hl).1, (h1 l hl).2.1, (h1 l hl).2.2, ?_⟩, h3, h4', hpm,
    ?_, ?_, h8, fun l hl => ⟨(h9 l hl).1, (h9 l hl).2, fun h => (h1 l hl).2.2 ?_⟩⟩
  · intro hone
    obtain ⟨m', hm', hlm'⟩ := Finset.exists_mem_ne hcard l
    have := h2 l hl m' hm' (Ne.symm hlm')
    rw [hone, one_mul] at this
    exact (h1 m' hm').2.2 this
  · rcases hpm l hl with h | h
    · exact ⟨l, hl, h⟩
    · rcases hpm m hm with h' | h'
      · exact ⟨m, hm, h'⟩
      · exact absurd (h.trans h'.symm) hval
  · rcases hpm l hl with h | h
    · rcases hpm m hm with h' | h'
      · exact absurd (h.trans h'.symm) hval
      · exact ⟨m, hm, h'⟩
    · exact ⟨l, hl, h⟩
  · exact eq_zero_of_ad_one_mul_eq_zero h

end Theorem3SectorsExample

end SimpleGraph
