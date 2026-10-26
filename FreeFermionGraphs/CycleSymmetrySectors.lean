import FreeFermionGraphs.JointSpectralProjections
import FreeFermionGraphs.IncognitoModes
import FreeFermionGraphs.HoleSimplicialClique
import FreeFermionGraphs.SectorCharacteristicPolynomial
import FreeFermionGraphs.TheoremOneII
import FreeFermionGraphs.LadderRelations
import FreeFermionGraphs.EvenHoleDeformationQuotient

/-!
# Mode sectors from the joint eigenprojections of the cycle symmetries `J_{⟨C₀⟩}`

Manuscript (arXiv 2305.15625 v1): Theorem 2 (`main.tex` L1248-1264), where `{Π_J}_J` is "a
complete set of projectors onto the mutual eigenspaces of `{J_{⟨C₀⟩}}`" (L1258-1262), together
with Definition 15 (`J_{⟨C₀⟩} = ∑_{C ∈ ⟨C₀⟩} h_C`, L799-803), the sector restriction of
`Z_G`, `Z_{G∖Ks}` (L563-585, L577-606), the commutation of `χ` with the `J`'s (Result 2, L110)
and the commutation of the `J`'s with the conserved charges (Theorem 1(ii), L864-871).  In the
numbering of the revised manuscript used by the repository, v1 Theorem 1 keeps its number.

This module is the first of the three pieces of the final assembly of Theorem 2 (the others are
the non-degeneracy bookkeeping and the per-sector conclusions).  It turns the *actual* operators
`J_κ = J_{⟨C₀⟩}` of a simplicial-mode Hamiltonian into the data `(Λ, Π_l)` and into a
`ModeSector` for every occurring joint eigenvalue tuple `l ∈ Λ`.

## The family of cycle symmetries

`SimpleGraph.PauliFrustrationRepresentation.cycleSymmetryOnClass H κ` is `J_κ` as a function of
the deformation class `κ : G.EvenHoleDeformationClass` (the representative-free form of
Definition 15; `cycleSymmetryOnClass_classOf` says that on `⟨C₀⟩` it is
`generalizedCycleSymmetryOp C₀`; the repository has no declaration called `cycleSymmetry`).  The
quotient `EvenHoleDeformationClass` also contains junk classes, the singleton classes of sets
that are not even-hole carriers; `IsEvenHoleClass` singles out the genuine classes.  For a junk
class `J_κ = 0` (`cycleSymmetryOnClass_eq_zero_of_not_isEvenHoleClass`: every set in the
closure of a non-hole is a non-hole, and `h_C = 0` for those), so the junk coordinates carry no
information, and every joint eigenvalue tuple has `l κ = 0` there.

## The commutation hypothesis

v1 Theorem 1(iii) (`[J_{⟨C₀⟩}, J_{⟨C₀'⟩}] = 0`) is **not** formalised in the repository yet.  It
is the explicit hypothesis `hJ : H.CycleSymmetriesCommute` of the theorems below, which therefore
carry the suffix `_of_cycleSymmetry_commute` (docs/PAPER_FIDELITY.md).  When `Theorem 1(iii)` is
proved it will discharge this hypothesis.  No other result of this module has a premise beyond
the manuscript setup (`hclaw`: `G` claw-free; `hKs`: `Ks` a simplicial clique; Hermiticity of the
Pauli terms, a field of `SimplicialModeHamiltonian`).

## Main declarations

* `IsEvenHoleClass`, `isEvenHoleClass_classOf_iff`: genuine hole classes.
* `PauliFrustrationRepresentation.cycleSymmetryOnClass` and its basic properties: `J_κ` is
  Hermitian (`isSelfAdjoint_cycleSymmetryOnClass`), vanishes on junk classes, commutes with every
  charge `Q_G^(k)` of a claw-free graph (`charge_commute_cycleSymmetryOnClass`, v1 Theorem 1(ii)
  summed over the token-sliding components, `sum_tokenSlidingChargeOp`).
* `PauliFrustrationRepresentation.CycleSymmetriesCommute`: the hypothesis `[J, J'] = 0` for
  even-hole carriers.
* `PauliFrustrationRepresentation.exists_jointSpectralProjections_of_cycleSymmetry_commute`:
  the joint spectral decomposition of `{J_κ}` in `Matrix (Fin d) (Fin d) ℂ`: a finite set `Λ`
  of tuples `l : EvenHoleDeformationClass → ℝ` and Hermitian idempotents `Π_l ≠ 0`, pairwise
  orthogonal, with `∑ Π_l = 1`, `J_{⟨C₀⟩} Π_l = l(⟨C₀⟩) Π_l`, `Π_l` in the bicommutant of the
  family, and `Λ` = exactly the joint eigenvalue tuples that occur (with junk coordinates `0`).
* `SimplicialModeHamiltonian.jointModeSector`: the `ModeSector` of a projection with the above
  properties, with `zG := sectorPolynomial H.coupling ∅ l` and `zK := sectorPolynomial H.coupling
  Ks l`.  Here `Π` commutes with every `Q_G^(k)` and `χ` because it lies in the bicommutant of the
  `J`'s, and `Π Z_G(-u²) = z_{∅,l}(-u²) Π`, `Π Z_{G∖Ks}(-u²) = z_{Ks,l}(-u²) Π` come from
  `transfer_mul_transfer_neg_mul_sector`, in the order with `Π` on the left either by `Π`
  commuting with `T_G(u)` (for `Z_G`) or by taking adjoints (for `Z_{G∖Ks}`, where `Π` is not
  known to commute with the deleted charges: both `Z_{G∖Ks}(-u²)` and `Π` are Hermitian).
* `SimplicialModeHamiltonian.exists_modeSectors_of_cycleSymmetry_commute`: the assembled
  statement.

## Deviations from v1

* v1 uses the sectors `Π_J` without constructing them, and does not prove that the `J`'s are
  Hermitian and commute (Theorem 1(iii), here the hypothesis), that `Π_J` commutes with `T`
  (Theorem 1(ii)) and with `χ` (an unstated lemma of v1, proved in `HoleSimplicialClique`), or that
  `Z_G Π_J` is an ordinary polynomial times `Π_J` (proved in `SectorCharacteristicPolynomial`).
* The sector labels are tuples on the quotient of *all* subsets (`EvenHoleDeformationClass`); the
  junk coordinates are forced to `0` (clause `∀ κ, ¬ IsEvenHoleClass κ → l κ = 0`), and the sector
  polynomials only see genuine hole classes (`sectorClassFamilies`).
* `zG`, `zK` are the real polynomials `z_{∅,l}`, `z_{Ks,l}`; the non-degeneracy hypothesis of the
  solution (no common root of `z_{∅,l}`, `z_{Ks,l}`, in the form `IsCoprime` per sector) is not
  used here.
-/

open scoped BigOperators

universe u w

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-! ### Genuine hole classes -/

/-- A deformation class `κ` is a *hole class* if it contains an even-hole carrier.  The
quotient `EvenHoleDeformationClass` also contains the singleton classes of arbitrary non-hole
sets (junk); the sector labels of v1 Theorem 2 are indexed by hole classes only. -/
def IsEvenHoleClass (G : SimpleGraph V) (κ : G.EvenHoleDeformationClass) : Prop :=
  ∃ C₀, G.IsEvenHoleCarrier C₀ ∧ G.evenHoleDeformationClassOf C₀ = κ

/-- The class of a set `C` is a hole class iff `C` is an even-hole carrier: the deformation
closure of an even-hole carrier consists of even-hole carriers. -/
theorem isEvenHoleClass_classOf_iff {C : Set V} :
    G.IsEvenHoleClass (G.evenHoleDeformationClassOf C) ↔ G.IsEvenHoleCarrier C := by
  constructor
  · rintro ⟨C₀, hC₀, h⟩
    exact (evenHoleDeformationClassOf_eq_iff.1 h).isEvenHoleCarrier hC₀
  · intro hC
    exact ⟨C, hC, rfl⟩

/-- Every class is either a hole class or the class of a set that is not an even-hole carrier. -/
theorem isEvenHoleClass_or_exists_not (κ : G.EvenHoleDeformationClass) :
    G.IsEvenHoleClass κ ∨ ∃ C, ¬ G.IsEvenHoleCarrier C ∧ G.evenHoleDeformationClassOf C = κ := by
  induction κ using Quotient.inductionOn with
  | _ C =>
    by_cases hC : G.IsEvenHoleCarrier C
    · exact Or.inl ⟨C, hC, rfl⟩
    · exact Or.inr ⟨C, hC, rfl⟩

namespace PauliFrustrationRepresentation

variable {A : Type w} [Ring A] [Fintype V] [DecidableEq V]

/-! ### `J_κ` as a function of the deformation class -/

/-- The generalized cycle symmetry `J_κ = J_{⟨C₀⟩} = ∑_{C ∈ ⟨C₀⟩} h_C` (v1 Definition 15,
L799-803) as a function of the deformation class `κ = ⟨C₀⟩`, not of a representative. -/
noncomputable def cycleSymmetryOnClass (H : G.PauliFrustrationRepresentation A) :
    G.EvenHoleDeformationClass → A :=
  G.generalizedCycleSymmetryOnClass H.evenHoleOperator

/-- On the class of `C₀`, `J_κ` is `generalizedCycleSymmetryOp C₀`. -/
@[simp]
theorem cycleSymmetryOnClass_classOf (H : G.PauliFrustrationRepresentation A) (C₀ : Set V) :
    H.cycleSymmetryOnClass (G.evenHoleDeformationClassOf C₀) =
      H.generalizedCycleSymmetryOp C₀ :=
  rfl

/-- `J_{C₀} = 0` when `C₀` is not an even-hole carrier: every set in its deformation closure is
again not an even-hole carrier (the closure of a hole consists of holes and the relation is
symmetric), and `h_C = 0` for those. -/
theorem generalizedCycleSymmetryOp_eq_zero_of_not_isEvenHoleCarrier
    (H : G.PauliFrustrationRepresentation A) {C₀ : Set V} (h : ¬ G.IsEvenHoleCarrier C₀) :
    H.generalizedCycleSymmetryOp C₀ = 0 := by
  unfold generalizedCycleSymmetryOp generalizedCycleSymmetry
  refine Finset.sum_eq_zero fun C hC => ?_
  have hcl : InEvenHoleDeformationClosure G C₀ C := mem_deformationClosureFinset.1 hC
  exact H.evenHoleOperator_eq_zero_of_not_isEvenHoleCarrier fun hc =>
    h (hcl.symm.isEvenHoleCarrier hc)

/-- `J_κ = 0` for a junk class `κ`. -/
theorem cycleSymmetryOnClass_eq_zero_of_not_isEvenHoleClass
    (H : G.PauliFrustrationRepresentation A) {κ : G.EvenHoleDeformationClass}
    (hκ : ¬ G.IsEvenHoleClass κ) : H.cycleSymmetryOnClass κ = 0 := by
  rcases isEvenHoleClass_or_exists_not κ with h | ⟨C, hC, rfl⟩
  · exact (hκ h).elim
  · exact H.generalizedCycleSymmetryOp_eq_zero_of_not_isEvenHoleCarrier hC

section Star

variable [StarRing A]

/-- Every `J_κ` is Hermitian when the terms are (v1 Definition 15; for junk classes `J_κ = 0`). -/
theorem isSelfAdjoint_cycleSymmetryOnClass (H : G.PauliFrustrationRepresentation A)
    (hstar : ∀ j, IsSelfAdjoint (H.term j)) (κ : G.EvenHoleDeformationClass) :
    IsSelfAdjoint (H.cycleSymmetryOnClass κ) := by
  induction κ using Quotient.inductionOn with
  | _ C₀ => exact H.isSelfAdjoint_generalizedCycleSymmetryOp hstar C₀

end Star

/-! ### The commutation hypothesis (v1 Theorem 1(iii)) -/

/-- **The hypothesis `[J_{⟨C₀⟩}, J_{⟨C₁⟩}] = 0`** for even-hole carriers `C₀`, `C₁`
(v1 Theorem 1(iii), L864-873).  Theorem 1(iii) is not formalised yet, so results that need it
take `H.CycleSymmetriesCommute` as a hypothesis and are named `_of_cycleSymmetry_commute`.  (The
case of weakly separated holes is `generalizedCycleSymmetryOp_commute_of_inducedCompatible`.) -/
def CycleSymmetriesCommute (H : G.PauliFrustrationRepresentation A) : Prop :=
  ∀ C₀ C₁, G.IsEvenHoleCarrier C₀ → G.IsEvenHoleCarrier C₁ →
    Commute (H.generalizedCycleSymmetryOp C₀) (H.generalizedCycleSymmetryOp C₁)

/-- Under `CycleSymmetriesCommute` the `J_κ` commute for *all* classes `κ`, `κ'`: a junk class
contributes `J_κ = 0`. -/
theorem CycleSymmetriesCommute.cycleSymmetryOnClass {H : G.PauliFrustrationRepresentation A}
    (hJ : H.CycleSymmetriesCommute) (κ κ' : G.EvenHoleDeformationClass) :
    Commute (H.cycleSymmetryOnClass κ) (H.cycleSymmetryOnClass κ') := by
  by_cases h : G.IsEvenHoleClass κ
  · by_cases h' : G.IsEvenHoleClass κ'
    · obtain ⟨C₀, hC₀, rfl⟩ := h
      obtain ⟨C₁, hC₁, rfl⟩ := h'
      exact hJ C₀ C₁ hC₀ hC₁
    · rw [H.cycleSymmetryOnClass_eq_zero_of_not_isEvenHoleClass h']
      exact Commute.zero_right _
  · rw [H.cycleSymmetryOnClass_eq_zero_of_not_isEvenHoleClass h]
    exact Commute.zero_left _

/-! ### Commutation of `J_κ` with the charges (v1 Theorem 1(ii)) -/

/-- `[Q_G^(k), J_{C₀}] = 0` for an even-hole carrier `C₀` of a claw-free graph: v1 Theorem 1(ii)
(`paperTheorem1ii`) for the token-sliding charges `q_{k,μ}`, summed over the components `μ`
(`∑_μ q_{k,μ} = Q_G^(k)`, v1 L788). -/
theorem charge_commute_generalizedCycleSymmetryOp (H : G.PauliFrustrationRepresentation A)
    (hclaw : G.IsClawFree) {C₀ : Set V} (hC₀ : G.IsEvenHoleCarrier C₀) (k : ℕ) :
    Commute (H.charge k) (H.generalizedCycleSymmetryOp C₀) := by
  have hsum : H.charge k = ∑ μ ∈ G.tokenSlidingComponentFinset k, H.tokenSlidingChargeOp k μ :=
    (H.sum_tokenSlidingChargeOp k).symm
  rw [hsum]
  refine Commute.sum_left _ _ _ fun μ _ => ?_
  have h := H.paperTheorem1ii hclaw hC₀ k μ
  unfold algebraCommutator at h
  rw [sub_eq_zero] at h
  exact h.symm

/-- `[Q_G^(k), J_κ] = 0` for every class `κ` (for junk classes `J_κ = 0`). -/
theorem charge_commute_cycleSymmetryOnClass (H : G.PauliFrustrationRepresentation A)
    (hclaw : G.IsClawFree) (k : ℕ) (κ : G.EvenHoleDeformationClass) :
    Commute (H.charge k) (H.cycleSymmetryOnClass κ) := by
  by_cases h : G.IsEvenHoleClass κ
  · obtain ⟨C₀, hC₀, rfl⟩ := h
    exact H.charge_commute_generalizedCycleSymmetryOp hclaw hC₀ k
  · rw [H.cycleSymmetryOnClass_eq_zero_of_not_isEvenHoleClass h]
    exact Commute.zero_right _

/-! ### The joint spectral decomposition of the family `{J_κ}` -/

open Matrix in
/-- **Joint spectral decomposition of the cycle symmetries, conditional on `[J, J'] = 0`**
(the linear-algebra content of "a complete set of projectors onto the mutual eigenspaces of
`{J_{⟨C₀⟩}}`" in v1 Theorem 2, L1258-1262).

Let `H` be a Pauli frustration representation in `Matrix (Fin d) (Fin d) ℂ` with Hermitian terms
whose generalized cycle symmetries commute pairwise (`hJ`, v1 Theorem 1(iii)).  Then there are a
finite set `Λ` of tuples `l : G.EvenHoleDeformationClass → ℝ` and matrices `Π_l` such that

* each `Π_l` (`l ∈ Λ`) is Hermitian, idempotent and nonzero;
* `Π_l Π_m = 0` for `l ≠ m` and `∑_{l ∈ Λ} Π_l = 1`;
* `J_{⟨C₀⟩} Π_l = l(⟨C₀⟩) Π_l` for every even-hole carrier `C₀`;
* `l κ = 0` on the junk classes `κ` (those that are not hole classes), `l ∈ Λ`;
* every `x` commuting with all `J_{⟨C₀⟩}` commutes with every `Π_l`;
* `l ∈ Λ` iff the joint eigenspace for `l` of the `J_{⟨C₀⟩}` is nonzero (and `l` vanishes on the
  junk classes).

`Π_l` is the projection onto the joint eigenspace `{x | ∀ C₀ even hole, J_{⟨C₀⟩} x = l(⟨C₀⟩) x}`;
the last clause says that `Λ` consists exactly of the joint-eigenvalue tuples that actually occur,
which is the index set of the sector hypotheses of the solution. -/
theorem exists_jointSpectralProjections_of_cycleSymmetry_commute {d : ℕ}
    (H : G.PauliFrustrationRepresentation (Matrix (Fin d) (Fin d) ℂ))
    (hstar : ∀ j, IsSelfAdjoint (H.term j)) (hJ : H.CycleSymmetriesCommute) :
    ∃ (Λ : Finset (G.EvenHoleDeformationClass → ℝ))
      (Pi : (G.EvenHoleDeformationClass → ℝ) → Matrix (Fin d) (Fin d) ℂ),
      (∀ l ∈ Λ, (Pi l).IsHermitian ∧ Pi l * Pi l = Pi l ∧ Pi l ≠ 0) ∧
      (∀ l ∈ Λ, ∀ m ∈ Λ, l ≠ m → Pi l * Pi m = 0) ∧ ∑ l ∈ Λ, Pi l = 1 ∧
      (∀ l ∈ Λ, ∀ C₀, G.IsEvenHoleCarrier C₀ →
        H.generalizedCycleSymmetryOp C₀ * Pi l =
          ((l (G.evenHoleDeformationClassOf C₀) : ℝ) : ℂ) • Pi l) ∧
      (∀ l ∈ Λ, ∀ κ, ¬ G.IsEvenHoleClass κ → l κ = 0) ∧
      (∀ x : Matrix (Fin d) (Fin d) ℂ,
        (∀ C₀, G.IsEvenHoleCarrier C₀ → Commute x (H.generalizedCycleSymmetryOp C₀)) →
          ∀ l ∈ Λ, Commute x (Pi l)) ∧
      (∀ l : G.EvenHoleDeformationClass → ℝ,
        l ∈ Λ ↔
          ((∃ v : Fin d → ℂ, v ≠ 0 ∧ ∀ C₀, G.IsEvenHoleCarrier C₀ →
              (H.generalizedCycleSymmetryOp C₀).mulVec v =
                ((l (G.evenHoleDeformationClassOf C₀) : ℝ) : ℂ) • v) ∧
            ∀ κ, ¬ G.IsEvenHoleClass κ → l κ = 0)) := by
  classical
  obtain ⟨Λ, P, hP1, hP2, hP3, hP4, hP5, hP6⟩ := exists_joint_spectral_projections
    (ι := G.EvenHoleDeformationClass) H.cycleSymmetryOnClass
    (fun κ => H.isSelfAdjoint_cycleSymmetryOnClass hstar κ) hJ.cycleSymmetryOnClass
  -- on a junk class `J κ = 0`, so a joint eigenvector forces `l κ = 0`
  have hjunk : ∀ (l : G.EvenHoleDeformationClass → ℝ) (v : Fin d → ℂ), v ≠ 0 →
      (∀ κ, (H.cycleSymmetryOnClass κ).mulVec v = ((l κ : ℝ) : ℂ) • v) →
      ∀ κ, ¬ G.IsEvenHoleClass κ → l κ = 0 := by
    intro l v hv hl κ hκ
    have h := hl κ
    rw [H.cycleSymmetryOnClass_eq_zero_of_not_isEvenHoleClass hκ, Matrix.zero_mulVec] at h
    have h' : ((l κ : ℝ) : ℂ) • v = 0 := h.symm
    rcases smul_eq_zero.1 h' with h0 | h0
    · exact_mod_cast h0
    · exact (hv h0).elim
  refine ⟨Λ, P, hP1, hP2, hP3, fun l hl C₀ hC₀ => hP4 l hl (G.evenHoleDeformationClassOf C₀), ?_,
    ?_, ?_⟩
  · intro l hl κ hκ
    obtain ⟨v, hv, hvl⟩ := (hP6 l).2 hl
    exact hjunk l v hv hvl κ hκ
  · intro x hx l hl
    refine hP5 x (fun κ => ?_) l hl
    by_cases h : G.IsEvenHoleClass κ
    · obtain ⟨C₀, hC₀, rfl⟩ := h
      exact hx C₀ hC₀
    · rw [H.cycleSymmetryOnClass_eq_zero_of_not_isEvenHoleClass h]
      exact Commute.zero_right _
  · intro l
    constructor
    · intro hl
      obtain ⟨v, hv, hvl⟩ := (hP6 l).2 hl
      exact ⟨⟨v, hv, fun C₀ _ => hvl (G.evenHoleDeformationClassOf C₀)⟩,
        hjunk l v hv hvl⟩
    · rintro ⟨⟨v, hv, hvl⟩, hzero⟩
      refine (hP6 l).1 ⟨v, hv, fun κ => ?_⟩
      by_cases h : G.IsEvenHoleClass κ
      · obtain ⟨C₀, hC₀, rfl⟩ := h
        exact hvl C₀ hC₀
      · rw [H.cycleSymmetryOnClass_eq_zero_of_not_isEvenHoleClass h, Matrix.zero_mulVec,
          hzero κ h]
        simp

end PauliFrustrationRepresentation

/-! ### Mode sectors of a simplicial-mode Hamiltonian -/

namespace SimplicialModeHamiltonian

variable {Ks : Set V} [Fintype V] [DecidableEq V] {d : ℕ}

open Matrix in
/-- **The mode sector of a joint eigenprojection of the cycle symmetries** (v1 Theorem 2,
L1248-1264 with L577-606).

Let `H` be a simplicial-mode Hamiltonian in `Matrix (Fin d) (Fin d) ℂ` with claw-free frustration
graph `G` and simplicial clique `Ks`.  Let `P` be a Hermitian idempotent such that
`J_{⟨C₀⟩} P = lam(⟨C₀⟩) P` for every even-hole carrier `C₀` and `P` commutes with everything
that commutes with all `J_{⟨C₀⟩}` (this holds for the joint spectral projections `Π_l` of
`exists_jointSpectralProjections_of_cycleSymmetry_commute`).  Then `P` is a `ModeSector`
with `zG = z_{∅,λ}`, `zK = z_{Ks,λ}` (`SimpleGraph.sectorPolynomial`):

* `Π` commutes with every charge `Q_G^(k)` (Theorem 1(ii): `Q_G^(k)` commutes with every `J`,
  `charge_commute_cycleSymmetryOnClass`) and with `χ` (`root_commute_cycleSymmetry`);
* `Π Z_G(-u²) = z_{∅,λ}(-u²) Π` since `Π` commutes with `T_G(u)`;
* `Π Z_{G∖Ks}(-u²) = z_{Ks,λ}(-u²) Π` by taking adjoints in
  `transfer_mul_transfer_neg_mul_sector` (`Π` is not known to commute with the deleted charges,
  but `Z_{G∖Ks}(-u²) = T_{G∖Ks}(u) T_{G∖Ks}(-u)` is Hermitian, as a product of two commuting
  Hermitian operators, and so is `Π`).

The commutation of the `J`'s is not an argument of this construction: it is only needed to
*produce* a `P` as in the hypotheses. -/
noncomputable def jointModeSector {G : SimpleGraph V}
    (H : G.SimplicialModeHamiltonian Ks (Matrix (Fin d) (Fin d) ℂ))
    (hclaw : G.IsClawFree) (hKs : G.IsSimplicialClique Ks)
    (lam : G.EvenHoleDeformationClass → ℝ) (P : Matrix (Fin d) (Fin d) ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P)
    (heig : ∀ C₀, G.IsEvenHoleCarrier C₀ →
      H.frustration.generalizedCycleSymmetryOp C₀ * P =
        ((lam (G.evenHoleDeformationClassOf C₀) : ℝ) : ℂ) • P)
    (hcomm : ∀ x : Matrix (Fin d) (Fin d) ℂ,
      (∀ C₀, G.IsEvenHoleCarrier C₀ →
        Commute x (H.frustration.generalizedCycleSymmetryOp C₀)) → Commute x P) :
    H.ModeSector :=
  have hcharge : ∀ k : ℕ, Commute P (H.frustration.charge k) := fun k =>
    (hcomm _ fun C₀ hC₀ =>
      H.frustration.charge_commute_generalizedCycleSymmetryOp hclaw hC₀ k).symm
  have hT : ∀ u : ℝ, Commute P (H.frustration.transfer ∅ u) := fun u =>
    H.frustration.commute_transfer_of_commute_deletedCharge ∅ (fun k => hcharge k) u
  have heig' : ∀ C₀, G.IsEvenHoleCarrier C₀ →
      H.frustration.generalizedCycleSymmetryOp C₀ * P =
        lam (G.evenHoleDeformationClassOf C₀) • P := fun C₀ hC₀ => by
    rw [heig C₀ hC₀, Complex.coe_smul]
  { Pi := P
    Pi_idem := hPP
    Pi_selfAdjoint := hP.isSelfAdjoint
    Pi_comm_charge := hcharge
    Pi_comm_root := (hcomm _ fun C₀ _ =>
      H.operator.root_commute_cycleSymmetry hKs C₀).symm
    zG := G.sectorPolynomial H.coupling ∅ lam
    zK := G.sectorPolynomial H.coupling Ks lam
    Z_scalar := fun u => by
      have h := H.toPauliCliqueHamiltonianRepresentation.transfer_mul_transfer_neg_mul_sector
        hclaw (W := ∅) (Or.inl rfl) P lam heig' u
      rw [← ((hT u).mul_right (hT (-u))).eq] at h
      exact h
    ZK_scalar := fun u => by
      have h := H.toPauliCliqueHamiltonianRepresentation.transfer_mul_transfer_neg_mul_sector
        hclaw (W := Ks) (Or.inr ⟨rfl, hKs⟩) P lam heig' u
      have hs := congrArg star h
      have hT' : ∀ w : ℝ, star (H.frustration.transfer Ks w) = H.frustration.transfer Ks w :=
        fun w => (H.isSelfAdjoint_transfer Ks w).star_eq
      rw [star_mul, star_mul, hT', hT', hP.star_eq, star_smul, star_trivial, hP.star_eq,
        ← (H.frustration.transfer_commute_transfer_of_deletedCharge_commute Ks
          (fun s t => H.frustration.deletedCharge_commute hclaw Ks s t) u (-u)).eq] at hs
      exact hs }

/-- The sector projection of `jointModeSector` is the given `P`. -/
@[simp]
theorem jointModeSector_Pi {G : SimpleGraph V}
    (H : G.SimplicialModeHamiltonian Ks (Matrix (Fin d) (Fin d) ℂ))
    (hclaw : G.IsClawFree) (hKs : G.IsSimplicialClique Ks)
    (lam : G.EvenHoleDeformationClass → ℝ) (P : Matrix (Fin d) (Fin d) ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P) (heig) (hcomm) :
    (H.jointModeSector hclaw hKs lam P hP hPP heig hcomm).Pi = P :=
  rfl

/-- The polynomial `z_G` of `jointModeSector` is `z_{∅,λ}`. -/
@[simp]
theorem jointModeSector_zG {G : SimpleGraph V}
    (H : G.SimplicialModeHamiltonian Ks (Matrix (Fin d) (Fin d) ℂ))
    (hclaw : G.IsClawFree) (hKs : G.IsSimplicialClique Ks)
    (lam : G.EvenHoleDeformationClass → ℝ) (P : Matrix (Fin d) (Fin d) ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P) (heig) (hcomm) :
    (H.jointModeSector hclaw hKs lam P hP hPP heig hcomm).zG =
      G.sectorPolynomial H.coupling ∅ lam :=
  rfl

/-- The polynomial `z_K` of `jointModeSector` is `z_{Ks,λ}`. -/
@[simp]
theorem jointModeSector_zK {G : SimpleGraph V}
    (H : G.SimplicialModeHamiltonian Ks (Matrix (Fin d) (Fin d) ℂ))
    (hclaw : G.IsClawFree) (hKs : G.IsSimplicialClique Ks)
    (lam : G.EvenHoleDeformationClass → ℝ) (P : Matrix (Fin d) (Fin d) ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P) (heig) (hcomm) :
    (H.jointModeSector hclaw hKs lam P hP hPP heig hcomm).zK =
      G.sectorPolynomial H.coupling Ks lam :=
  rfl

/-- **Mode sectors from the joint eigenprojections of the cycle symmetries, conditional on
`[J, J'] = 0`** (v1 Theorem 2, L1248-1264, first part: the projectors `Π_J`, with the properties
that the proof of the theorem uses).

Let `H` be a simplicial-mode Hamiltonian in `Matrix (Fin d) (Fin d) ℂ` with claw-free frustration
graph `G` and simplicial clique `Ks`, whose cycle symmetries commute (`hJ`, v1 Theorem 1(iii)).
Then there are a finite set `Λ` of tuples `l : EvenHoleDeformationClass → ℝ` (zero on the junk
classes) and Hermitian idempotents `Π_l ≠ 0` (`l ∈ Λ`), pairwise orthogonal, with
`∑ Π_l = 1` and `J_{⟨C₀⟩} Π_l = l(⟨C₀⟩) Π_l`, such that `Λ` is exactly the set of joint
eigenvalue tuples that occur, and every `Π_l` is the projection of a `ModeSector` of `H`
(`Π` Hermitian idempotent commuting with all charges `Q_G^(k)` and with `χ`) with
`zG = z_{∅,l} = sectorPolynomial H.coupling ∅ l` and `zK = z_{Ks,l} = sectorPolynomial H.coupling
Ks l`, i.e. `Π Z_G(-u²) = z_{∅,l}(-u²) Π` and `Π Z_{G∖Ks}(-u²) = z_{Ks,l}(-u²) Π`.

The hypothesis `hJ` is Theorem 1(iii), not yet formalised, hence the name. -/
theorem exists_modeSectors_of_cycleSymmetry_commute {G : SimpleGraph V}
    (H : G.SimplicialModeHamiltonian Ks (Matrix (Fin d) (Fin d) ℂ))
    (hclaw : G.IsClawFree) (hKs : G.IsSimplicialClique Ks)
    (hJ : H.frustration.CycleSymmetriesCommute) :
    ∃ (Λ : Finset (G.EvenHoleDeformationClass → ℝ))
      (Pi : (G.EvenHoleDeformationClass → ℝ) → Matrix (Fin d) (Fin d) ℂ),
      (∀ l ∈ Λ, (Pi l).IsHermitian ∧ Pi l * Pi l = Pi l ∧ Pi l ≠ 0) ∧
      (∀ l ∈ Λ, ∀ m ∈ Λ, l ≠ m → Pi l * Pi m = 0) ∧ ∑ l ∈ Λ, Pi l = 1 ∧
      (∀ l ∈ Λ, ∀ C₀, G.IsEvenHoleCarrier C₀ →
        H.frustration.generalizedCycleSymmetryOp C₀ * Pi l =
          ((l (G.evenHoleDeformationClassOf C₀) : ℝ) : ℂ) • Pi l) ∧
      (∀ l ∈ Λ, ∀ κ, ¬ G.IsEvenHoleClass κ → l κ = 0) ∧
      (∀ x : Matrix (Fin d) (Fin d) ℂ,
        (∀ C₀, G.IsEvenHoleCarrier C₀ →
          Commute x (H.frustration.generalizedCycleSymmetryOp C₀)) →
          ∀ l ∈ Λ, Commute x (Pi l)) ∧
      (∀ l : G.EvenHoleDeformationClass → ℝ,
        l ∈ Λ ↔
          ((∃ v : Fin d → ℂ, v ≠ 0 ∧ ∀ C₀, G.IsEvenHoleCarrier C₀ →
              (H.frustration.generalizedCycleSymmetryOp C₀).mulVec v =
                ((l (G.evenHoleDeformationClassOf C₀) : ℝ) : ℂ) • v) ∧
            ∀ κ, ¬ G.IsEvenHoleClass κ → l κ = 0)) ∧
      (∀ l ∈ Λ, ∃ S : H.ModeSector, S.Pi = Pi l ∧
        S.zG = G.sectorPolynomial H.coupling ∅ l ∧ S.zK = G.sectorPolynomial H.coupling Ks l) := by
  obtain ⟨Λ, Pi, h1, h2, h3, h4, h5, h6, h7⟩ :=
    H.frustration.exists_jointSpectralProjections_of_cycleSymmetry_commute
      (fun j => H.term_selfAdjoint (some j)) hJ
  refine ⟨Λ, Pi, h1, h2, h3, h4, h5, h6, h7, fun l hl => ?_⟩
  exact ⟨H.jointModeSector hclaw hKs l (Pi l) (h1 l hl).1 (h1 l hl).2.1 (h4 l hl)
    (fun x hx => h6 x hx l hl), rfl, rfl, rfl⟩

end SimplicialModeHamiltonian

end SimpleGraph
