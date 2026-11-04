import FreeFermionGraphs.TheoremOneIII
import FreeFermionGraphs.CycleSymmetrySectors
import FreeFermionGraphs.CrossSectorRelations
import FreeFermionGraphs.FreeFermionSolution
import FreeFermionGraphs.Theorem3Sectors

/-!
# Theorem 1 (iii) used downstream: the sector theory without its commutation premise

Manuscript reference: arXiv 2305.15625 v1, Theorem 1 (iii) `theorem:conservedcharges`
(L864-871, proof L929-1243), `[J_{C₀}, J_{C₀'}] = 0`.  The manuscript uses it in Theorem 2
(`theorem:freefermionsolution`, L1248-1264: "`{Π_𝒥}` is a complete set of projectors onto the
mutual eigenspaces of `{J_{⟨C₀⟩}}`") and in Theorem 3 (`theorem:polynomialdivisibility`,
L1328-1336: "over each mutual eigenspace of the `{J_{⟨C₀⟩}}`"): without the commutation of the
`J`'s there is no joint eigenspace decomposition.  (The repository numbers some lemmas of v1
differently, following a revised manuscript that is not available.)

The sector theory (`FreeFermionGraphs.CycleSymmetrySectors`, `CrossSectorRelations`,
`FreeFermionSolution`, `Theorem3Sectors`) was written while Theorem 1 (iii) was open, so its
theorems take the commutation as a hypothesis `hJ : H.CycleSymmetriesCommute` and carry the suffix
`_of_cycleSymmetry_commute` (docs/PAPER_FIDELITY.md).  `FreeFermionGraphs.TheoremOneIII` proves
the hypothesis for every Hamiltonian representation of a claw-free graph
(`PauliFrustrationRepresentation.cycleSymmetriesCommute`).  This module discharges `hJ` in each of
these theorems.  The conditional theorems stay as they are; each gets a wrapper whose proof is the
conditional theorem applied to `cycleSymmetriesCommute`.

## Main declarations

* `PauliFrustrationRepresentation.exists_jointSpectralProjections`: the joint spectral
  decomposition `(Λ, Π_l)` of the cycle symmetries; premises `hclaw`, `hstar`.
* `SimplicialModeHamiltonian.exists_modeSectors`: the same, with the `Π_l` the projections of
  `ModeSector`s with `z_G = z_{∅,l}`, `z_K = z_{Ks,l}`; premises `hclaw`, `hKs`.
* `SimplicialModeHamiltonian.exists_crossSectorModes_of_sectorCoprime`: the cross-sector
  relations and the canonical anticommutation relations of the explicit modes; premises `hclaw`,
  `hKs`, `hND`.
* `SimplicialModeHamiltonian.paperTheorem2_of_sectorCoprime`: **v1 Theorem 2**, the free-fermion
  solution `H = ∑_l (∑_j ε_{l,j} [ψ_{l,j}, ψ_{l,j}^†]) Π_l`; premises `hclaw`, `hKs`, `hND`.
* `PauliCliqueHamiltonianRepresentation.paperTheorem3`: **v1 Theorem 3** over the joint
  eigenspaces of the cycle symmetries; premises `hK`, `hclaw`, `hstar`.
* `SimplicialModeHamiltonian.paperTheorem3_modeSectors`: the same for the projections of the
  `ModeSector`s of Theorem 2; premises `hclaw`, `hKs`.

## Fidelity

* *Names.*  `docs/PAPER_FIDELITY.md` reserves an unqualified paper-facing name for statements with
  no premise beyond the manuscript setup.  After discharging `hJ`, the premises left are
  `hclaw` and `hK`/`hKs` (the standing assumptions "claw-free" and "simplicial" of the theorems)
  and the Hermiticity of the Pauli terms `hstar` (part of the setup, Eq. (1) of v1, L91-93, and a
  field `term_selfAdjoint` of `SimplicialModeHamiltonian`).  So `exists_jointSpectralProjections`,
  `exists_modeSectors`, `paperTheorem3` and `paperTheorem3_modeSectors` are unqualified.
  Theorem 2 keeps the per-sector coprimality hypothesis `hND`, which is not in v1: v1's statement
  is false without it (the `C₄` counterexample in the docstring of
  `paperTheorem2_of_sectorCoprime`).
  Hence `paperTheorem2_of_sectorCoprime`, and likewise `exists_crossSectorModes_of_sectorCoprime`,
  which produces the explicit modes `ψ_{l,j}` and so needs the same non-degeneracy.
* *No structure field or certificate assumes a claim that is to be proved.*  Every wrapper is a
  one-line application of a conditional theorem to `cycleSymmetriesCommute`, itself the theorem
  `paperTheorem1iii`.  The statements are those of the conditional theorems, with `hJ` removed.
* *Claw-freeness behind `restrictSome`.*  For `H : G.PauliCliqueHamiltonianRepresentation K ℝ A`
  the representation behind `H.operator.restrictSome` is a representation of `G` itself
  (`restrictSome` restricts a representation of the root-adjoined graph `G⁺ = G.adjoinRootAt K`
  to the original vertices, and its type is `G.PauliFrustrationRepresentation A`).  The
  hypothesis `hclaw : G.IsClawFree` therefore applies directly, and no statement about induced
  subgraphs or about subtype instances is needed.
* *Remaining deviations from v1* are those of the conditional theorems and are documented there:
  the corrected hopping matrix and the reading of "over a mutual eigenspace" as right
  multiplication by `Π_l` (`Theorem3Sectors`), and `r_l = deg z_{∅,l}` modes per sector instead of
  `α(G)` (`FreeFermionSolution`).

Non-vacuity of `paperTheorem3`, `exists_jointSpectralProjections` and `exists_modeSectors` on
the three-qubit `C₄` model is in `FreeFermionGraphs.TheoremOneIIIConsequencesExample`.  That model
has uniform couplings, where the coprimality premise of the Theorem 2 wrappers fails in the
sector `J = +1`; a multi-sector witness for `paperTheorem2_of_sectorCoprime` needs other couplings.
-/

open scoped BigOperators

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace PauliFrustrationRepresentation

variable [Fintype V] [DecidableEq V]

/-- **Joint spectral decomposition of the cycle symmetries** (v1 Theorem 2, L1258-1262: "a
complete set of projectors onto the mutual eigenspaces of `{J_{⟨C₀⟩}}`"; Theorem 1 (iii),
L864-871, supplies the commutation that makes the mutual eigenspaces exist).

Let `H` be a Pauli frustration representation in `Matrix (Fin d) (Fin d) ℂ` of a claw-free (finite)
graph `G`, with Hermitian terms.  Then there are a finite set `Λ` of tuples
`l : G.EvenHoleDeformationClass → ℝ` (zero on the junk classes) and matrices `Π_l` such that each
`Π_l` (`l ∈ Λ`) is Hermitian, idempotent and nonzero, `Π_l Π_m = 0` for `l ≠ m`,
`∑_{l ∈ Λ} Π_l = 1`, `J_{⟨C₀⟩} Π_l = l(⟨C₀⟩) Π_l` for every even-hole carrier `C₀`, every matrix
commuting with all the `J_{⟨C₀⟩}` commutes with every `Π_l`, and `Λ` is exactly the set of joint
eigenvalue tuples that occur.

This is `exists_jointSpectralProjections_of_cycleSymmetry_commute` with `hJ` supplied by
Theorem 1 (iii) (`cycleSymmetriesCommute`, i.e. `paperTheorem1iii`).  The premises are the setup of
the manuscript (the representation `H`, Hermitian Pauli terms `hstar`, finiteness of `V`) and
claw-freeness `hclaw`; there is no premise beyond these, so the name is unqualified. -/
theorem exists_jointSpectralProjections {d : ℕ}
    (H : G.PauliFrustrationRepresentation (Matrix (Fin d) (Fin d) ℂ)) (hclaw : G.IsClawFree)
    (hstar : ∀ j, IsSelfAdjoint (H.term j)) :
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
            ∀ κ, ¬ G.IsEvenHoleClass κ → l κ = 0)) :=
  H.exists_jointSpectralProjections_of_cycleSymmetry_commute hstar (H.cycleSymmetriesCommute hclaw)

end PauliFrustrationRepresentation

namespace SimplicialModeHamiltonian

variable {Ks : Set V} [Fintype V] [DecidableEq V] {d : ℕ}

/-- **Mode sectors from the joint eigenprojections of the cycle symmetries** (v1 Theorem 2,
L1248-1264, first part: the projectors `Π_𝒥`, with the properties that the proof of the theorem
uses; Theorem 1 (iii) supplies the commutation).

Let `H` be a simplicial-mode Hamiltonian in `Matrix (Fin d) (Fin d) ℂ` with claw-free frustration
graph `G` and simplicial clique `Ks`.  Then the joint spectral decomposition `(Λ, Π_l)` of the
cycle symmetries (`PauliFrustrationRepresentation.exists_jointSpectralProjections`) exists, and
every `Π_l` is the projection of a `ModeSector` of `H` with
`zG = z_{∅,l} = sectorPolynomial H.coupling ∅ l` and
`zK = z_{Ks,l} = sectorPolynomial H.coupling Ks l`, i.e. `Π Z_G(-u²) = z_{∅,l}(-u²) Π` and
`Π Z_{G∖Ks}(-u²) = z_{Ks,l}(-u²) Π`.

This is `exists_modeSectors_of_cycleSymmetry_commute` with `hJ` supplied by Theorem 1 (iii)
(`cycleSymmetriesCommute`, i.e. `paperTheorem1iii`).  The Hermiticity of the Pauli terms is the
field `term_selfAdjoint` of `SimplicialModeHamiltonian`; no premise beyond the setup and
`hclaw`, `hKs`, so the name is unqualified.  The non-degeneracy hypothesis of the explicit modes is
not used here. -/
theorem exists_modeSectors
    (H : G.SimplicialModeHamiltonian Ks (Matrix (Fin d) (Fin d) ℂ))
    (hclaw : G.IsClawFree) (hKs : G.IsSimplicialClique Ks) :
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
        S.zG = G.sectorPolynomial H.coupling ∅ l ∧ S.zK = G.sectorPolynomial H.coupling Ks l) :=
  H.exists_modeSectors_of_cycleSymmetry_commute hclaw hKs
    (H.frustration.cycleSymmetriesCommute hclaw)

open scoped Classical in
/-- **Cross-sector relations of the incognito modes for the sectors of the cycle symmetries,
conditional on per-sector coprimality** (v1 Theorem 2, L1248-1264, the statements
`[Π_J, ψ_{J',j}] = 0` for all `J`, `J'`, `j` and the canonical anticommutation relations of
v1 Lemma 14 including `J ≠ J'`; Theorem 1 (iii) supplies the commutation of the `J`'s).

Let `H` be a simplicial-mode Hamiltonian in `Matrix (Fin d) (Fin d) ℂ` with claw-free frustration
graph `G` and simplicial clique `Ks` such that for every joint-eigenvalue tuple `l` of the
`J_{⟨C₀⟩}` that occurs the sector polynomials `z_{∅,l}`, `z_{Ks,l}` are coprime (`hND`).  Then
the conclusion of `exists_crossSectorModes_of_cycleSymmetry_commute` holds: the sectors `Π_l`
(each the projection of a `ModeSector`), in every sector `r_l = deg z_{∅,l}` distinct positive
numbers `u_{l,j}` with `z_{∅,l} = ∏_j (1 + x/u_{l,j}²)`, `Z_G(-u_{l,j}²) Π_l = 0` and
`z_{Ks,l}(-u_{l,j}²) z_{∅,l}'(-u_{l,j}²) > 0`, the explicit modes
`ψ_{l,j} = N_{l,j}⁻¹ Π_l T(-u_{l,j}) χ T(u_{l,j})`, and for all `l, l' ∈ Λ`:
`Π_l ψ_{l',k} = ψ_{l',k} Π_l = δ_{l,l'} ψ_{l',k}`, `{ψ_{l,j}, ψ_{l',k}^†} = δ_{l,l'} δ_{jk} Π_l`,
`{ψ_{l,j}, ψ_{l',k}} = 0` and `{ψ_{l,j}^†, ψ_{l',k}^†} = 0`.

This is `exists_crossSectorModes_of_cycleSymmetry_commute` with `hJ` supplied by Theorem 1 (iii).
**The premise `hND` remains.**  It is v1's tacit non-degeneracy, which is necessary (see
`paperTheorem2_of_sectorCoprime`, whose `C₄` counterexample shows that the printed Theorem 2 fails
without it: in the sector `J = +1` the double root `x = -1/2` of `z_{∅,l}` is also a root of
`z_{Ks,l}`, so `N_{l,j} = 0` and `ψ_{l,j}` is undefined).  Since `hND` is a premise beyond the
manuscript setup, the name carries `_of_sectorCoprime` (docs/PAPER_FIDELITY.md). -/
theorem exists_crossSectorModes_of_sectorCoprime
    (H : G.SimplicialModeHamiltonian Ks (Matrix (Fin d) (Fin d) ℂ))
    (hclaw : G.IsClawFree) (hKs : G.IsSimplicialClique Ks)
    (hND : ∀ l : G.EvenHoleDeformationClass → ℝ,
      ((∃ v : Fin d → ℂ, v ≠ 0 ∧ ∀ C₀, G.IsEvenHoleCarrier C₀ →
          (H.frustration.generalizedCycleSymmetryOp C₀).mulVec v =
            ((l (G.evenHoleDeformationClassOf C₀) : ℝ) : ℂ) • v) ∧
        ∀ κ, ¬ G.IsEvenHoleClass κ → l κ = 0) →
      IsCoprime (G.sectorPolynomial H.coupling ∅ l) (G.sectorPolynomial H.coupling Ks l)) :
    ∃ (Λ : Finset (G.EvenHoleDeformationClass → ℝ))
      (Pi : (G.EvenHoleDeformationClass → ℝ) → Matrix (Fin d) (Fin d) ℂ)
      (r : (G.EvenHoleDeformationClass → ℝ) → ℕ) (u : ∀ l, Fin (r l) → ℝ)
      (ψ : ∀ l, Fin (r l) → Matrix (Fin d) (Fin d) ℂ),
      -- the joint spectral projectors of the cycle symmetries
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
        S.zG = G.sectorPolynomial H.coupling ∅ l ∧ S.zK = G.sectorPolynomial H.coupling Ks l) ∧
      -- the roots `u_{l,j}` (non-degeneracy data)
      (∀ l ∈ Λ, r l = (G.sectorPolynomial H.coupling ∅ l).natDegree ∧ Function.Injective (u l) ∧
        (∀ j, 0 < u l j) ∧
        G.sectorPolynomial H.coupling ∅ l =
          ∏ j, (1 + Polynomial.C ((u l j)⁻¹ ^ 2) * Polynomial.X) ∧
        (∀ j, 0 < (G.sectorPolynomial H.coupling Ks l).eval (-(u l j) ^ 2) *
          (Polynomial.derivative (G.sectorPolynomial H.coupling ∅ l)).eval (-(u l j) ^ 2)) ∧
        ∀ j, H.frustration.transfer ∅ (u l j) * H.frustration.transfer ∅ (-(u l j)) * Pi l = 0) ∧
      -- the explicit modes
      (∀ l j, ψ l j = H.explicitIncognitoMode (Pi l) (G.sectorPolynomial H.coupling ∅ l)
        (G.sectorPolynomial H.coupling Ks l) (u l j)) ∧
      -- cross-sector commutation: `Π_l ψ_{l',k} = ψ_{l',k} Π_l = δ_{l,l'} ψ_{l',k}`
      (∀ l ∈ Λ, ∀ l' ∈ Λ, ∀ k, Commute (Pi l) (ψ l' k) ∧ Commute (Pi l) (star (ψ l' k))) ∧
      (∀ l ∈ Λ, ∀ l' ∈ Λ, ∀ k, Pi l * ψ l' k = (if l = l' then ψ l' k else 0) ∧
        ψ l' k * Pi l = (if l = l' then ψ l' k else 0)) ∧
      -- the canonical anticommutation relations, across and within sectors
      (∀ l ∈ Λ, ∀ l' ∈ Λ, ∀ (j : Fin (r l)) (k : Fin (r l')),
        ψ l j * star (ψ l' k) + star (ψ l' k) * ψ l j = if l = l' ∧ HEq j k then Pi l else 0) ∧
      (∀ l ∈ Λ, ∀ l' ∈ Λ, ∀ (j : Fin (r l)) (k : Fin (r l')),
        ψ l j * ψ l' k + ψ l' k * ψ l j = 0) ∧
      (∀ l ∈ Λ, ∀ l' ∈ Λ, ∀ (j : Fin (r l)) (k : Fin (r l')),
        star (ψ l j) * star (ψ l' k) + star (ψ l' k) * star (ψ l j) = 0) :=
  H.exists_crossSectorModes_of_cycleSymmetry_commute hclaw hKs
    (H.frustration.cycleSymmetriesCommute hclaw) hND

open scoped Classical in
/-- **Theorem 2 of v1: the free-fermion solution** (`theorem:freefermionsolution`, L1248-1264),
with Theorem 1 (iii) discharged, under per-sector coprimality.

Let `H` be a simplicial-mode Hamiltonian in `Matrix (Fin d) (Fin d) ℂ` with claw-free frustration
graph `G` and simplicial clique `Ks` (an SCF Hamiltonian, `hclaw`, `hKs`), such that for every
joint-eigenvalue tuple `l` of the generalized cycle symmetries `J_{⟨C₀⟩}` that occurs the sector
polynomials `z_{∅,l}`, `z_{Ks,l}` are coprime (`hND`).  Then there are

* `Λ`, the set of joint eigenvalue tuples of `{J_{⟨C₀⟩}}` that occur, and the projections `Π_l`
  onto the mutual eigenspaces (Hermitian idempotents `≠ 0`, pairwise orthogonal, `∑ Π_l = 1`,
  `J_{⟨C₀⟩} Π_l = l(⟨C₀⟩) Π_l`, each the projection of a `ModeSector` with `z_G = z_{∅,l}`,
  `z_K = z_{Ks,l}`);
* in each sector `l ∈ Λ` exactly `r l = deg z_{∅,l}` distinct positive numbers `u l j` with
  `z_{∅,l} = ∏_j (1 + x/u_{l,j}²)` and `Z_G(-u_{l,j}²) Π_l = 0`, `N l j = 4 u_{l,j}
  √(z_{Ks,l}(-u²) z_{∅,l}'(-u²)) > 0`, `ε l j = 1/u_{l,j}` and the modes
  `ψ l j = (N l j)⁻¹ Π_l T(-u_{l,j}) χ T(u_{l,j})`, given by these formulas;

such that `[Π_l, ψ_{l',k}] = 0` (in the form `Π_l ψ_{l',k} = ψ_{l',k} Π_l = δ_{l,l'} ψ_{l',k}`),
`{ψ_{l,j}, ψ_{l',k}^†} = δ_{l,l'} δ_{jk} Π_l`, `{ψ_{l,j}, ψ_{l',k}} = 0`,
`{ψ_{l,j}^†, ψ_{l',k}^†} = 0`,
`[H, ψ_{l,j}] = 2 ε_{l,j} ψ_{l,j}`, `[H, ψ_{l,j}^†] = -2 ε_{l,j} ψ_{l,j}^†`, and

`H = ∑_{l ∈ Λ} (∑_j ε_{l,j} [ψ_{l,j}, ψ_{l,j}^†]) Π_l`.

This is `freeFermionSolution_of_cycleSymmetry_commute` with `hJ` supplied by Theorem 1 (iii)
(`cycleSymmetriesCommute`, i.e. `paperTheorem1iii`); see that theorem for the full description.

**Why `hND` is kept.**  v1 uses non-degeneracy silently: real positive simple roots of
`Z_{G,J}` and a positive normalisation `N_{J,j}`.  The hypothesis `hND` (coprimality of
`z_{∅,l}` and `z_{Ks,l}` in `ℝ[X]`) is equivalent to v1's tacit "`Z_{G,J}` and `Z_{G∖Ks,J}` have
no common complex root": coprime real polynomials have no common complex root
(`ModeSectorPositivity.aeval_ne_zero_of_isCoprime`), and the converse is the Fundamental Theorem of
Algebra (`ModeSectorPositivity.isCoprime_of_forall_aeval_ne_zero`, which takes it as a hypothesis
because `Mathlib.Analysis` is not built here).  It is necessary: v1's Theorem 2 is false without
it.  Take `G = C₄` with uniform couplings and `Ks` an edge (claw-free, `Ks` simplicial,
connected).  In the sector `J = +1`, `z_{∅} = (1+2x)²` and `z_{Ks} = 1+2x` share the root
`x = -1/2`: `Z_G(-u²) Π = 0` has the double root `u² = 1/2`, `N = 0` and `ψ` is undefined.  In the
sector `J = -1`, `z_∅ = 1+4x` has degree `1 < α(G) = 2`, so the sum over `j = 1, …, α(G)` of v1
is ill-defined (this is repaired here by indexing the modes by `Fin (r l)`, `r l = deg z_{∅,l}`,
not by `hND`).  These are hand computations on the three-qubit model of
`CycleSymmetrySectorsExample` (`docs/V1_ERRATA.md`, U1); the model satisfies the commutation
`hJ` (now a theorem) but not `hND` in its sector `J = +1`.

Since `hND` is a premise beyond the manuscript setup, the name carries `_of_sectorCoprime`
(docs/PAPER_FIDELITY.md) and the unqualified `paperTheorem2` is not exported.  Deviations from v1
besides `hND`: the number of modes per sector, the added relations `{ψ, ψ} = 0`,
`{ψ^†, ψ^†} = 0`, `ψ_{J,-j} := ψ_{J,j}^†` (never defined in v1), and `ε = 1/u` with `u > 0`. -/
theorem paperTheorem2_of_sectorCoprime
    (H : G.SimplicialModeHamiltonian Ks (Matrix (Fin d) (Fin d) ℂ))
    (hclaw : G.IsClawFree) (hKs : G.IsSimplicialClique Ks)
    (hND : ∀ l : G.EvenHoleDeformationClass → ℝ,
      ((∃ v : Fin d → ℂ, v ≠ 0 ∧ ∀ C₀, G.IsEvenHoleCarrier C₀ →
          (H.frustration.generalizedCycleSymmetryOp C₀).mulVec v =
            ((l (G.evenHoleDeformationClassOf C₀) : ℝ) : ℂ) • v) ∧
        ∀ κ, ¬ G.IsEvenHoleClass κ → l κ = 0) →
      IsCoprime (G.sectorPolynomial H.coupling ∅ l) (G.sectorPolynomial H.coupling Ks l)) :
    ∃ (Λ : Finset (G.EvenHoleDeformationClass → ℝ))
      (Pi : (G.EvenHoleDeformationClass → ℝ) → Matrix (Fin d) (Fin d) ℂ)
      (r : (G.EvenHoleDeformationClass → ℝ) → ℕ) (u : ∀ l, Fin (r l) → ℝ)
      (N : ∀ l, Fin (r l) → ℝ) (ε : ∀ l, Fin (r l) → ℝ)
      (ψ : ∀ l, Fin (r l) → Matrix (Fin d) (Fin d) ℂ),
      -- the joint spectral projectors of the cycle symmetries `J_{⟨C₀⟩}`
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
        S.zG = G.sectorPolynomial H.coupling ∅ l ∧ S.zK = G.sectorPolynomial H.coupling Ks l) ∧
      -- the roots `u_{l,j}`: `r_l = deg z_{∅,l}` distinct positive numbers with
      -- `z_{∅,l} = ∏_j (1 + x/u_{l,j}²)` and `Z_G(-u_{l,j}²) Π_l = 0`
      (∀ l ∈ Λ, r l = (G.sectorPolynomial H.coupling ∅ l).natDegree ∧ Function.Injective (u l) ∧
        (∀ j, 0 < u l j) ∧
        G.sectorPolynomial H.coupling ∅ l =
          ∏ j, (1 + Polynomial.C ((u l j)⁻¹ ^ 2) * Polynomial.X) ∧
        (∀ j, 0 < (G.sectorPolynomial H.coupling Ks l).eval (-(u l j) ^ 2) *
          (Polynomial.derivative (G.sectorPolynomial H.coupling ∅ l)).eval (-(u l j) ^ 2)) ∧
        ∀ j, H.frustration.transfer ∅ (u l j) * H.frustration.transfer ∅ (-(u l j)) * Pi l = 0) ∧
      -- the explicit normalisation `N`, energies `ε = 1/u` and modes `ψ` of v1
      (∀ l j, N l j = 4 * u l j * Real.sqrt ((G.sectorPolynomial H.coupling Ks l).eval
        (-(u l j) ^ 2) *
          (Polynomial.derivative (G.sectorPolynomial H.coupling ∅ l)).eval (-(u l j) ^ 2))) ∧
      (∀ l ∈ Λ, ∀ j, 0 < N l j) ∧
      (∀ l j, ε l j = (u l j)⁻¹) ∧
      (∀ l j, ψ l j = (N l j)⁻¹ •
        (Pi l * H.frustration.transfer ∅ (-(u l j)) * H.root *
          H.frustration.transfer ∅ (u l j))) ∧
      -- `[Π_l, ψ_{l',k}] = 0`, in the form `Π_l ψ_{l',k} = ψ_{l',k} Π_l = δ_{l,l'} ψ_{l',k}`
      (∀ l ∈ Λ, ∀ l' ∈ Λ, ∀ k, Commute (Pi l) (ψ l' k) ∧ Commute (Pi l) (star (ψ l' k))) ∧
      (∀ l ∈ Λ, ∀ l' ∈ Λ, ∀ k, Pi l * ψ l' k = (if l = l' then ψ l' k else 0) ∧
        ψ l' k * Pi l = (if l = l' then ψ l' k else 0)) ∧
      -- the canonical anticommutation relations, across and within sectors
      (∀ l ∈ Λ, ∀ l' ∈ Λ, ∀ (j : Fin (r l)) (k : Fin (r l')),
        ψ l j * star (ψ l' k) + star (ψ l' k) * ψ l j = if l = l' ∧ HEq j k then Pi l else 0) ∧
      (∀ l ∈ Λ, ∀ l' ∈ Λ, ∀ (j : Fin (r l)) (k : Fin (r l')),
        ψ l j * ψ l' k + ψ l' k * ψ l j = 0) ∧
      (∀ l ∈ Λ, ∀ l' ∈ Λ, ∀ (j : Fin (r l)) (k : Fin (r l')),
        star (ψ l j) * star (ψ l' k) + star (ψ l' k) * star (ψ l j) = 0) ∧
      -- the eigenmode relations `[H, ψ_{±j}] = ± 2 ε ψ_{±j}`
      (∀ l ∈ Λ, ∀ j,
        algebraCommutator H.frustration.hamiltonian (ψ l j) = (2 * ε l j) • ψ l j) ∧
      (∀ l ∈ Λ, ∀ j,
        algebraCommutator H.frustration.hamiltonian (star (ψ l j)) =
          (-(2 * ε l j)) • star (ψ l j)) ∧
      -- the free-fermion form of the Hamiltonian
      H.frustration.hamiltonian = ∑ l ∈ Λ,
        (∑ j, ε l j • (ψ l j * star (ψ l j) - star (ψ l j) * ψ l j)) * Pi l :=
  H.freeFermionSolution_of_cycleSymmetry_commute hclaw hKs
    (H.frustration.cycleSymmetriesCommute hclaw) hND

end SimplicialModeHamiltonian

namespace PauliCliqueHamiltonianRepresentation

variable {K : Set V} [Fintype V] [DecidableEq V] {d : ℕ}
variable [DecidableEq (CliqueRootedInducedPath G K)]

/-- **Theorem 3 of v1 over the joint eigenspaces of the cycle symmetries**
(`theorem:polynomialdivisibility`, L1328-1336: "`Π_𝒥 ad_{iH}^k χ = (-2i)^k ∑_{P ∈ 𝒫}
(A_{G,𝒥}^k)_{{j*},P} h_P` over each mutual eigenspace of the `{J_{⟨C₀⟩}}`"), with Theorem 1 (iii)
(L864-871, `paperTheorem1iii`) discharged.

Let `H` be a Pauli clique Hamiltonian representation in `Matrix (Fin d) (Fin d) ℂ` with real
couplings and Hermitian terms `h_j` (`hstar`), whose frustration graph `G` is claw-free (`hclaw`)
and in which `K` is a simplicial clique (`hK`).  Then there are a finite set `Λ` of tuples
`l : G.EvenHoleDeformationClass → ℝ` (zero on the junk classes) and matrices `Π_l` such that

* (the joint spectral decomposition of
  `PauliFrustrationRepresentation.exists_jointSpectralProjections`) each `Π_l` (`l ∈ Λ`) is
  Hermitian, idempotent and nonzero, `Π_l Π_m = 0` for `l ≠ m`, `∑_{l ∈ Λ} Π_l = 1`,
  `J_{⟨C₀⟩} Π_l = l(⟨C₀⟩) Π_l`, every operator commuting with all the `J_{⟨C₀⟩}` commutes with every
  `Π_l`, and `Λ` is exactly the set of joint eigenvalue tuples that occur;
* for every `l ∈ Λ` the matrix `A_l = cliqueHoppingMatrix G K H.coupling l` is real and bipartite
  (`A_l(P, Q) ≠ 0 → |P| + |Q|` odd), and for every `k`, in the convention `ad_{iH} = [iH, ·]` of
  v1, `Π_l` commutes with `ad_{iH}^k χ` and

  `Π_l ad_{iH}^k χ = ad_{iH}^k χ Π_l = ∑_P ((-2i)^k (A_l^k)_{{j*},P}) • (h_P Π_l)`.

This is `paperTheorem3_of_cycleSymmetry_commute` with `hJ` supplied by Theorem 1 (iii).  The
graph behind `H.operator.restrictSome` is `G` itself, so `hclaw` is exactly the claw-freeness that
`cycleSymmetriesCommute` needs.  The premises are the setup of v1 (the representation `H`,
Hermitian Pauli terms, finiteness of `V`) and the standing assumptions of Theorem 3 (`hK`,
`hclaw`); there is no premise beyond these, so the name is unqualified.

Deviations from v1, as in `paperTheorem3_of_cycleSymmetry_commute`: `A_l` is the corrected matrix
of `CliqueHoppingMatrix.lean`, not the printed Eq. (decoratedtree) (which misses the sign
`(-1)^{k-1}` and the root arcs); and "over each mutual eigenspace" is read as right multiplication
by `Π_l` of each path operator (`J_c` need not commute with the individual `h_P`); since `Π_l`
commutes with `ad^k χ`, the left form `Π_l ad^k χ` has the same value. -/
theorem paperTheorem3
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree)
    (H : G.PauliCliqueHamiltonianRepresentation K ℝ (Matrix (Fin d) (Fin d) ℂ))
    (hstar : ∀ j : V, IsSelfAdjoint (H.operator.term (some j))) :
    ∃ (Λ : Finset (G.EvenHoleDeformationClass → ℝ))
      (Pi : (G.EvenHoleDeformationClass → ℝ) → Matrix (Fin d) (Fin d) ℂ),
      (∀ l ∈ Λ, (Pi l).IsHermitian ∧ Pi l * Pi l = Pi l ∧ Pi l ≠ 0) ∧
      (∀ l ∈ Λ, ∀ m ∈ Λ, l ≠ m → Pi l * Pi m = 0) ∧ ∑ l ∈ Λ, Pi l = 1 ∧
      (∀ l ∈ Λ, ∀ C₀ : Set V, G.IsEvenHoleCarrier C₀ →
        H.operator.restrictSome.generalizedCycleSymmetryOp C₀ * Pi l =
          ((l (G.evenHoleDeformationClassOf C₀) : ℝ) : ℂ) • Pi l) ∧
      (∀ l ∈ Λ, ∀ κ, ¬ G.IsEvenHoleClass κ → l κ = 0) ∧
      (∀ x : Matrix (Fin d) (Fin d) ℂ,
        (∀ C₀ : Set V, G.IsEvenHoleCarrier C₀ →
          Commute x (H.operator.restrictSome.generalizedCycleSymmetryOp C₀)) →
          ∀ l ∈ Λ, Commute x (Pi l)) ∧
      (∀ l : G.EvenHoleDeformationClass → ℝ,
        l ∈ Λ ↔
          ((∃ v : Fin d → ℂ, v ≠ 0 ∧ ∀ C₀ : Set V, G.IsEvenHoleCarrier C₀ →
              (H.operator.restrictSome.generalizedCycleSymmetryOp C₀).mulVec v =
                ((l (G.evenHoleDeformationClassOf C₀) : ℝ) : ℂ) • v) ∧
            ∀ κ, ¬ G.IsEvenHoleClass κ → l κ = 0)) ∧
      (∀ l ∈ Λ,
        (∀ P Q : CliqueRootedInducedPath G K,
          cliqueHoppingMatrix G K H.coupling l P Q ≠ 0 → Odd (P.path.card + Q.path.card)) ∧
        ∀ k : ℕ,
          Commute (Pi l)
              (iteratedCommutator (Complex.I • H.physicalHamiltonian) k H.rootOperator) ∧
          Pi l * iteratedCommutator (Complex.I • H.physicalHamiltonian) k H.rootOperator =
            ∑ P : CliqueRootedInducedPath G K,
              ((-2 * Complex.I) ^ k *
                  ((cliqueHoppingMatrix G K H.coupling l ^ k) (cliqueRootPath G K) P : ℂ)) •
                (H.pathOperator P * Pi l) ∧
          iteratedCommutator (Complex.I • H.physicalHamiltonian) k H.rootOperator * Pi l =
            ∑ P : CliqueRootedInducedPath G K,
              ((-2 * Complex.I) ^ k *
                  ((cliqueHoppingMatrix G K H.coupling l ^ k) (cliqueRootPath G K) P : ℂ)) •
                (H.pathOperator P * Pi l)) :=
  paperTheorem3_of_cycleSymmetry_commute hK hclaw H hstar
    (H.operator.restrictSome.cycleSymmetriesCommute hclaw)

end PauliCliqueHamiltonianRepresentation

namespace SimplicialModeHamiltonian

variable {Ks : Set V} [Fintype V] [DecidableEq V] {d : ℕ}
variable [DecidableEq (CliqueRootedInducedPath G Ks)]

/-- **Theorem 3 over the joint eigenspaces, which are the projections of the mode sectors of
Theorem 2** (v1 Theorem 3, L1328-1336, and v1 Theorem 2, L1248-1264), with Theorem 1 (iii)
discharged.

For a simplicial-mode Hamiltonian `H` in `Matrix (Fin d) (Fin d) ℂ` with claw-free frustration
graph `G` and simplicial clique `Ks`, the joint spectral projectors `Π_l` (`l ∈ Λ`) of
`exists_modeSectors` satisfy, besides all the properties listed there (spectral decomposition;
`Π_l` is the projection of a `ModeSector` with `zG = z_{∅,l}`, `zK = z_{Ks,l}`), the Theorem 3
identity of `PauliCliqueHamiltonianRepresentation.paperTheorem3`: `A_l =
cliqueHoppingMatrix G Ks H.coupling l` is real and bipartite, `Π_l` commutes with every
`ad_{iH}^k χ`, and `Π_l ad_{iH}^k χ = ad_{iH}^k χ Π_l = ∑_P ((-2i)^k (A_l^k)_{{j*},P}) • (h_P Π_l)`.

This is `paperTheorem3_modeSectors_of_cycleSymmetry_commute` with `hJ` supplied by Theorem 1 (iii).
Hermiticity of the Pauli terms is the field `term_selfAdjoint`; there is no premise beyond the
setup and `hclaw`, `hKs`, so the name is unqualified.  The non-degeneracy hypothesis of Theorem 2
is not used. -/
theorem paperTheorem3_modeSectors
    (H : G.SimplicialModeHamiltonian Ks (Matrix (Fin d) (Fin d) ℂ))
    (hclaw : G.IsClawFree) (hKs : G.IsSimplicialClique Ks) :
    ∃ (Λ : Finset (G.EvenHoleDeformationClass → ℝ))
      (Pi : (G.EvenHoleDeformationClass → ℝ) → Matrix (Fin d) (Fin d) ℂ),
      (∀ l ∈ Λ, (Pi l).IsHermitian ∧ Pi l * Pi l = Pi l ∧ Pi l ≠ 0) ∧
      (∀ l ∈ Λ, ∀ m ∈ Λ, l ≠ m → Pi l * Pi m = 0) ∧ ∑ l ∈ Λ, Pi l = 1 ∧
      (∀ l ∈ Λ, ∀ C₀ : Set V, G.IsEvenHoleCarrier C₀ →
        H.frustration.generalizedCycleSymmetryOp C₀ * Pi l =
          ((l (G.evenHoleDeformationClassOf C₀) : ℝ) : ℂ) • Pi l) ∧
      (∀ l ∈ Λ, ∀ κ, ¬ G.IsEvenHoleClass κ → l κ = 0) ∧
      (∀ x : Matrix (Fin d) (Fin d) ℂ,
        (∀ C₀ : Set V, G.IsEvenHoleCarrier C₀ →
          Commute x (H.frustration.generalizedCycleSymmetryOp C₀)) →
          ∀ l ∈ Λ, Commute x (Pi l)) ∧
      (∀ l : G.EvenHoleDeformationClass → ℝ,
        l ∈ Λ ↔
          ((∃ v : Fin d → ℂ, v ≠ 0 ∧ ∀ C₀ : Set V, G.IsEvenHoleCarrier C₀ →
              (H.frustration.generalizedCycleSymmetryOp C₀).mulVec v =
                ((l (G.evenHoleDeformationClassOf C₀) : ℝ) : ℂ) • v) ∧
            ∀ κ, ¬ G.IsEvenHoleClass κ → l κ = 0)) ∧
      (∀ l ∈ Λ, ∃ S : H.ModeSector, S.Pi = Pi l ∧
        S.zG = G.sectorPolynomial H.coupling ∅ l ∧ S.zK = G.sectorPolynomial H.coupling Ks l) ∧
      (∀ l ∈ Λ,
        (∀ P Q : CliqueRootedInducedPath G Ks,
          cliqueHoppingMatrix G Ks H.coupling l P Q ≠ 0 → Odd (P.path.card + Q.path.card)) ∧
        ∀ k : ℕ,
          Commute (Pi l)
              (iteratedCommutator (Complex.I • H.physicalHamiltonian) k H.rootOperator) ∧
          Pi l * iteratedCommutator (Complex.I • H.physicalHamiltonian) k H.rootOperator =
            ∑ P : CliqueRootedInducedPath G Ks,
              ((-2 * Complex.I) ^ k *
                  ((cliqueHoppingMatrix G Ks H.coupling l ^ k) (cliqueRootPath G Ks) P : ℂ)) •
                (H.pathOperator P * Pi l) ∧
          iteratedCommutator (Complex.I • H.physicalHamiltonian) k H.rootOperator * Pi l =
            ∑ P : CliqueRootedInducedPath G Ks,
              ((-2 * Complex.I) ^ k *
                  ((cliqueHoppingMatrix G Ks H.coupling l ^ k) (cliqueRootPath G Ks) P : ℂ)) •
                (H.pathOperator P * Pi l)) :=
  H.paperTheorem3_modeSectors_of_cycleSymmetry_commute hclaw hKs
    (H.frustration.cycleSymmetriesCommute hclaw)

end SimplicialModeHamiltonian

end SimpleGraph
