import FreeFermionGraphs.TheoremOneIIIConsequences
import FreeFermionGraphs.Theorem3SectorsExample

/-!
# Non-vacuity of `TheoremOneIIIConsequences`: the 4-cycle with a simplicial mode

`TheoremOneIIIConsequences` discharges the commutation premise `hJ` (v1 Theorem 1 (iii)) from the
sector theory of v1 Theorems 2 and 3.  This module instantiates the unconditional
`PauliCliqueHamiltonianRepresentation.paperTheorem3` on the model of `CycleSymmetrySectorsExample`
and `Theorem3SectorsExample` (the 4-cycle `G = c4` with the simplicial clique `Ks = {0, 1}` on three
qubits, whose unique even hole `{0, 1, 2, 3}` has the cycle symmetry `J = Z₂`, which splits the
8-dimensional space into the two sectors `J = ±1`), to check that its remaining hypotheses
(`hK`, `hclaw`, `hstar`) are satisfiable and that the conclusion is not empty.

The hypotheses are supplied by `c4_isSimplicialClique`, `c4_isClawFree` and the field
`term_selfAdjoint` of the model.  The commutation `ham_cycleSymmetriesCommute` of
`CycleSymmetrySectorsExample`, which `Theorem3SectorsExample.theorem3_two_sectors` still feeds to
`paperTheorem3_modeSectors_of_cycleSymmetry_commute`, is not used: here it comes from Theorem 1
(iii) inside `paperTheorem3`.  As in `theorem3_two_sectors`, the conclusion holds with two sectors,
each `Π_l` a proper nonzero projection, with the eigenvalues `J = +1` and `J = -1` both occurring,
with the Theorem 3 identity for every `l ∈ Λ` and every `k`, and with a nonzero left side at
`k = 1`.

## Main declarations

* `TheoremOneIIIConsequencesExample.paperTheorem3_two_sectors`: the instantiation of
  `paperTheorem3`.
* `TheoremOneIIIConsequencesExample.exists_modeSectors_ham`: the instantiation of
  `exists_modeSectors`, without `ham_cycleSymmetriesCommute`.
-/

universe u

namespace SimpleGraph

namespace TheoremOneIIIConsequencesExample

open CycleSymmetrySectorsExample Theorem3SectorsExample

/-- **Non-vacuity of `paperTheorem3`.**  For the model `ham` (a simplicial-mode Hamiltonian on three
qubits with frustration graph the 4-cycle, claw-free, with simplicial clique `{0, 1}`, whose cycle
symmetry `J = Z₂` genuinely acts), regarded as a Pauli clique Hamiltonian representation, the
hypotheses of `paperTheorem3` hold, and the conclusion holds with two sectors: there are projections
`Π_l` (`l ∈ Λ`), none of them `0` or `1`, with `∑ Π_l = 1` and `J Π_l = l(⟨C⟩) Π_l`, the eigenvalues
`l(⟨C⟩)` are `±1` and both occur, and for every `l ∈ Λ`: the matrix `A_l` is bipartite, `Π_l`
commutes with every `ad_{iH}^k χ`,
`Π_l ad_{iH}^k χ = ad_{iH}^k χ Π_l = (-2i)^k ∑_P (A_l^k)_{{j*},P} h_P Π_l`, and the left side at
`k = 1` is not zero.  No commutation hypothesis `hJ` is supplied. -/
theorem paperTheorem3_two_sectors [DecidableEq (c4.CliqueRootedInducedPath Ks)] :
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
        iteratedCommutator (Complex.I • ham.physicalHamiltonian) 1 ham.rootOperator * Pi l ≠
          0) := by
  obtain ⟨Λ, Pi, h1, h2, h3, h4, h5, -, -, h9⟩ :=
    PauliCliqueHamiltonianRepresentation.paperTheorem3 c4_isSimplicialClique c4_isClawFree
      ham.toPauliCliqueHamiltonianRepresentation (fun j => ham.term_selfAdjoint (some j))
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
    ?_, ?_, fun l hl => ⟨(h9 l hl).1, (h9 l hl).2, fun h => (h1 l hl).2.2 ?_⟩⟩
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

/-- **Non-vacuity of `exists_modeSectors`**: its hypotheses `hclaw`, `hKs` hold for the model `ham`,
and the commutation `ham_cycleSymmetriesCommute` is not needed.  (The sector structure itself is
`CycleSymmetrySectorsExample.exists_two_sectors`.) -/
theorem exists_modeSectors_ham :
    ∃ (Λ : Finset (c4.EvenHoleDeformationClass → ℝ))
      (Pi : (c4.EvenHoleDeformationClass → ℝ) → Matrix (Fin 8) (Fin 8) ℂ),
      ∑ l ∈ Λ, Pi l = 1 ∧
      (∀ l ∈ Λ, ∃ S : ham.ModeSector, S.Pi = Pi l ∧
        S.zG = c4.sectorPolynomial ham.coupling ∅ l ∧
        S.zK = c4.sectorPolynomial ham.coupling Ks l) := by
  obtain ⟨Λ, Pi, -, -, h3, -, -, -, -, h8⟩ :=
    ham.exists_modeSectors c4_isClawFree c4_isSimplicialClique
  exact ⟨Λ, Pi, h3, h8⟩

end TheoremOneIIIConsequencesExample

end SimpleGraph
