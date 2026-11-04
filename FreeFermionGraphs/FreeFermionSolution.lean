import FreeFermionGraphs.CrossSectorRelations
import FreeFermionGraphs.HamiltonianReconstruction

/-!
# The free-fermion solution (v1 Theorem 2), conditional on `[J, J'] = 0` and per-sector coprimality

Manuscript (arXiv 2305.15625 v1): Theorem 2 (`theorem:freefermionsolution`, `main.tex`
L1248-1264) and the closing sentence of Section 5 "Exact Solutions" (L1321), "Combining
Lemma 13, Lemma 14 and Lemma 15 proves Theorem 2".  In the numbering of the revised manuscript
used by the repository, v1 Lemmas 13, 14, 15 are "Lemmas 3, 4, 5".

This module is the last of the three pieces of the assembly of Theorem 2.  The first is
`CycleSymmetrySectors` (the joint spectral projections `Π_l` of the cycle symmetries `J_κ` and
the `ModeSector` of each), the second is `CrossSectorRelations` (the cross-sector relations and
the canonical anticommutation relations of the explicit modes).  Here the remaining statements of
Theorem 2 are proved, namely the eigenmode relation (v1 Lemma 13, `[H, ψ_{±j}] = ±2ε ψ_{±j}`) and
the reconstruction of the Hamiltonian (v1 Lemma 15, `H = ∑_J (∑_j ε [ψ, ψ†]) Π_J`), per sector
and summed over the sectors with `∑ Π_l = 1`; they are assembled with the earlier pieces into
`freeFermionSolution_of_cycleSymmetry_commute`.

## What the theorem says

Let `H` be a simplicial-mode Hamiltonian in `Matrix (Fin d) (Fin d) ℂ` (v1 Eq. (1), L91-93:
Hermitian Pauli-type terms `h_j = b_j σ^j`, `b_j ∈ ℝ \ {0}`; v1 Definition 8, L588-595: the
simplicial mode `χ`; `d` may include ancilla qubits that realise `χ`) with claw-free frustration
graph `G` and simplicial clique `Ks` (`hclaw`, `hKs`: "SCF Hamiltonian").  The generalized cycle
symmetries `J_{⟨C₀⟩}` are the *specific* operators `generalizedCycleSymmetryOp C₀` of v1
Definition 15, not existentially chosen ones.  Under the two premises below,
`freeFermionSolution_of_cycleSymmetry_commute` provides

* a finite set `Λ` of joint eigenvalue tuples `l` of the `J`'s (exactly those that occur, with
  `l` zero on the classes that are not classes of even holes) and the orthogonal projections
  `Π_l` onto the mutual eigenspaces of `{J_{⟨C₀⟩}}`: Hermitian, idempotent, nonzero, pairwise
  orthogonal, `∑ Π_l = 1`, `J_{⟨C₀⟩} Π_l = l(⟨C₀⟩) Π_l`; every `Π_l` is the projection of a
  `ModeSector` with `z_G = z_{∅,l}`, `z_K = z_{Ks,l}` (v1's `Z_{G,J}`, `Z_{G∖Ks,J}`);
* in every sector `l ∈ Λ` the `r_l = deg z_{∅,l}` distinct positive numbers `u_{l,j}` with
  `z_{∅,l} = ∏_j (1 + x/u_{l,j}²)` and `Z_G(-u_{l,j}²) Π_l = 0`
  (that is, `T(u) T(-u) Π_l = 0` at `u = u_{l,j}`), with `z_{Ks,l}(-u²) z_{∅,l}'(-u²) > 0` there;
* the explicit modes of v1 Definition 9 and L2097,
  `ψ_{l,j} = N_{l,j}⁻¹ Π_l T(-u_{l,j}) χ T(u_{l,j})`,
  `N_{l,j} = 4 u_{l,j} √(z_{Ks,l}(-u_{l,j}²) z_{∅,l}'(-u_{l,j}²))` (a positive real) and the
  single-particle energies `ε_{l,j} = 1/u_{l,j}` (v1 Theorem 2, last sentence).  The statement
  *pins down* `N`, `ε` and `ψ` by these defining equations (they are bound by `∃` only so that
  the formulas can be named); they are not existentially chosen modes;
* `[Π_l, ψ_{l',k}] = 0` for all `l`, `l'`, `k` (v1 Theorem 2, L1262-1263; more precisely
  `Π_l ψ_{l',k} = ψ_{l',k} Π_l = δ_{l,l'} ψ_{l',k}`), and `[Π_l, ψ_{l',k}^†] = 0`;
* the canonical anticommutation relations `{ψ_{l,j}, ψ_{l',k}^†} = δ_{l,l'} δ_{jk} Π_l`
  (v1 Lemma 14, `ψ_{l,-k} = ψ_{l,k}^†`), `{ψ_{l,j}, ψ_{l',k}} = 0`, `{ψ_{l,j}^†, ψ_{l',k}^†} = 0`;
* the eigenmode relations `[H, ψ_{l,j}] = 2 ε_{l,j} ψ_{l,j}` and `[H, ψ_{l,j}^†] =
  -2 ε_{l,j} ψ_{l,j}^†` (v1 Lemma 13, `[H, ψ_{±j}] = ±2ε ψ_{±j}`);
* the free-fermion form of the Hamiltonian
  `H = ∑_{l ∈ Λ} (∑_{j=1}^{r_l} ε_{l,j} [ψ_{l,j}, ψ_{l,j}^†]) Π_l`
  (v1 Theorem 2 and Lemma 15).

## Premises beyond the manuscript setup

Besides the setup of v1 (`H`, `hclaw`, `hKs`), the theorem has exactly two premises, and its name
says so (docs/PAPER_FIDELITY.md):

* `hJ : H.frustration.CycleSymmetriesCommute`, v1 Theorem 1(iii),
  `[J_{⟨C₀⟩}, J_{⟨C₁⟩}] = 0`, which is not formalised yet.  It is needed only to *produce* the
  joint eigenprojections `Π_l`; once Theorem 1(iii) is proved it is discharged (hence
  `_of_cycleSymmetry_commute`).
* `hND`, the non-degeneracy hypothesis, per joint-eigenvalue tuple `l` that occurs:
  `IsCoprime z_{∅,l} z_{Ks,l}`.  v1 uses non-degeneracy silently (real, positive, simple roots of
  `Z_{G,J}`, `N_{J,j}` real and positive, `Q^(k) Π_J = 0` above `deg Z_{G,J}`).  For *real*
  polynomials, `IsCoprime` is equivalent to "`z_{∅,l}` and `z_{Ks,l}` have no common complex
  root" (coprimality gives no common root directly; the converse needs the Fundamental Theorem of
  Algebra, which is not available in this build, see
  `ModeSectorPositivity.isCoprime_of_forall_aeval_ne_zero`), and this single condition implies
  everything v1 uses silently (`ModeSector.exists_nondegenerate_of_isCoprime` of
  `ModeSectorPositivity`).  The clause `∀ κ, ¬ IsEvenHoleClass κ → l κ = 0` in the antecedent of
  `hND` only discards the junk coordinates of the tuple `l`; `sectorPolynomial` does not see them
  (`sectorClassFamilies` contains only classes of even-hole carriers), so `hND` is precisely
  "coprimality for every joint-eigenvalue tuple of the `J`'s that occurs".

v1's Theorem 2 is **false** without `hND`.  Counterexample: `G = C₄` with uniform couplings and
`Ks` an edge (claw-free, `Ks` simplicial, connected).  In the sector `J = +1` one has
`z_{∅} = (1+2x)²` and `z_{Ks} = 1+2x`: a double root with `N = 0`, so `ψ` is undefined; in the
sector `J = -1` one has `z_∅ = 1+4x`, of degree `1 < α(G) = 2`, so v1's sum over `j = 1..α(G)` is
ill-defined (`CycleSymmetrySectorsExample`, `CrossSectorRelationsExample`).  The hypothesis `hND`
fails in the sector `J = +1` (common root `x = -1/2` of `z_∅` and `z_{Ks}`) but holds in the sector
`J = -1` (`1+4x` and `1+2x` are coprime); the defect of that sector, `deg z_∅ = 1 < α(G) = 2`, is
repaired by indexing the modes by `Fin (r l)` with `r l = deg z_{∅,l}` (see Deviations below), not
by `hND`.  Disconnected `G` also violates `hND` (the component not containing `Ks` contributes a
common root of `Z_G` and `Z_{G∖Ks}`), so connectedness (present in v1's Result 1 only) is
subsumed.

## Deviations from v1 (all deliberate)

* The extra hypothesis `hND`, and the extra hypothesis `hJ` while Theorem 1(iii) is open.
* The inner index runs over `Fin (r l)` with `r l = deg z_{∅,l}` instead of `α(G)`; they coincide
  in generic sectors, but v1 does not say that `deg Z_{G,J} = α(G)` in every sector (`C₄` above).
* The relations `{ψ, ψ} = 0`, `{ψ†, ψ†} = 0` and `[H, ψ†] = -2εψ†` are added, and `ψ_{J,-j}`
  (never defined in v1) is `ψ_{J,j}^†`; the Hamiltonian is written in the form `[ψ, ψ†]` of
  v1 Theorem 2 (v1 Lemma 15 writes `[ψ_{+j}, ψ_{-j}]`).
* The sector labels are tuples on the quotient of all subsets (`EvenHoleDeformationClass`); the
  coordinates on the classes that do not contain an even-hole carrier are `0` and play no role.
* `ε = 1/u` uses `u_{l,j} > 0` (a convention that v1 leaves implicit).
* Individual modes are not claimed to commute with the individual terms `h_j`, nor `Π_l` with
  them (it does not, in general); only with the charges, the Hamiltonian and `χ`.

## Main declarations

* `SimplicialModeHamiltonian.ModeSector.solution_on_sector`: the eigenmode relations and
  the reconstruction `H Π = ∑_j ε_j [ψ_j, ψ_j^†]` in one sector, from raw non-degeneracy data.
* `SimplicialModeHamiltonian.freeFermionSolution_of_cycleSymmetry_commute`: v1 Theorem 2.
-/

open scoped BigOperators

universe u w

variable {V : Type u}

namespace SimpleGraph

namespace SimplicialModeHamiltonian

variable {G : SimpleGraph V} {Ks : Set V} [Fintype V] [DecidableEq V]

namespace ModeSector

namespace Nondegenerate

variable {A : Type w} [Ring A] [StarRing A] [Algebra ℝ A] [StarModule ℝ A]
variable {H : G.SimplicialModeHamiltonian Ks A} {S : H.ModeSector}

omit [StarRing A] [StarModule ℝ A] in
/-- The commutator with `H` is `ℝ`-linear in its second argument (used to pull the
normalisation `N_j⁻¹` out of `[H, ψ_j]`). -/
theorem algebraCommutator_smul_right_real (c : ℝ) (X x : A) :
    algebraCommutator X (c • x) = c • algebraCommutator X x := by
  simp only [algebraCommutator, smul_mul_assoc, mul_smul_comm, smul_sub]

/-- **`[H, ψ_j^+] = 2 ε_j ψ_j^+`** with `ε_j = 1/u_j` (v1 Lemma 13, `lemma:commutationrelation`,
L1285-1304, for `+j`): the eigenmode lemma `ModeSector.eigenmode` for the normalised mode,
at the root `u_j` of `z_G` (`zG_eval_root`); the scalar `N_j⁻¹` drops out. -/
theorem commutator_psiPlus (D : S.Nondegenerate) (hclaw : G.IsClawFree)
    (hKs : G.IsSimplicialClique Ks) (j : Fin D.r) :
    algebraCommutator H.frustration.hamiltonian (D.psiPlus j) =
      (2 * (D.u j)⁻¹) • D.psiPlus j := by
  unfold psiPlus
  rw [algebraCommutator_smul_right_real,
    S.eigenmode hclaw hKs (D.u_pos j).ne' (D.zG_eval_root j), smul_comm, div_eq_mul_inv]

/-- **`[H, ψ_j^-] = -2 ε_j ψ_j^-`** with `ε_j = 1/u_j` (v1 Lemma 13 for `-j`, where
`ψ_{J,-j} = ψ_{J,j}^†`). -/
theorem commutator_psiMinus (D : S.Nondegenerate) (hclaw : G.IsClawFree)
    (hKs : G.IsSimplicialClique Ks) (j : Fin D.r) :
    algebraCommutator H.frustration.hamiltonian (D.psiMinus j) =
      (-(2 * (D.u j)⁻¹)) • D.psiMinus j := by
  unfold psiMinus
  rw [algebraCommutator_smul_right_real,
    S.eigenmode_neg hclaw hKs (D.u_pos j).ne' (D.zG_eval_root j), smul_comm, div_eq_mul_inv,
    neg_smul]

end Nondegenerate

/-- **The solution in one sector, from raw non-degeneracy data** (v1 Lemmas 13 and 15, with the
normalisation of L2097).

Let `S` be a mode sector of a simplicial-mode Hamiltonian in `Matrix (Fin d) (Fin d) ℂ` with
claw-free frustration graph and simplicial clique `Ks`, and let `u_1, …, u_r` be distinct positive reals
with `z_G = ∏_j (1 + x/u_j²)` and `z_K(-u_j²) z_G'(-u_j²) > 0` (the non-degeneracy data of the
sector, `ModeSector.Nondegenerate`).  Then the explicit modes
`ψ_j = N_j⁻¹ Π T(-u_j) χ T(u_j)`, `N_j = 4 u_j √(z_K(-u_j²) z_G'(-u_j²))`, satisfy

* `[H, ψ_j] = 2 u_j⁻¹ ψ_j` and `[H, ψ_j^†] = -2 u_j⁻¹ ψ_j^†`;
* `H Π = ∑_j u_j⁻¹ [ψ_j, ψ_j^†]`, with no hypothesis on the charges: in matrix algebras
  `Q^(k) Π = 0` for `k > deg z_G` (`hamiltonian_mul_Pi_matrix`).

The modes are given by their explicit formula (`hψ`, `explicitIncognitoMode`), not chosen. -/
theorem solution_on_sector {d : ℕ}
    {H : G.SimplicialModeHamiltonian Ks (Matrix (Fin d) (Fin d) ℂ)} (S : H.ModeSector)
    (hclaw : G.IsClawFree) (hKs : G.IsSimplicialClique Ks) {r : ℕ} (u : Fin r → ℝ)
    (hpos : ∀ j, 0 < u j) (hinj : Function.Injective u)
    (hzG : S.zG = ∏ j, (1 + Polynomial.C ((u j)⁻¹ ^ 2) * Polynomial.X))
    (hrad : ∀ j, 0 < S.zK.eval (-(u j) ^ 2) *
      (Polynomial.derivative S.zG).eval (-(u j) ^ 2))
    (ψ : Fin r → Matrix (Fin d) (Fin d) ℂ)
    (hψ : ∀ j, ψ j = H.explicitIncognitoMode S.Pi S.zG S.zK (u j)) :
    (∀ j, algebraCommutator H.frustration.hamiltonian (ψ j) = (2 * (u j)⁻¹) • ψ j) ∧
    (∀ j, algebraCommutator H.frustration.hamiltonian (star (ψ j)) =
      (-(2 * (u j)⁻¹)) • star (ψ j)) ∧
    H.frustration.hamiltonian * S.Pi =
      ∑ j, (u j)⁻¹ • (ψ j * star (ψ j) - star (ψ j) * ψ j) := by
  let D : S.Nondegenerate := ⟨r, u, hpos, hinj, hzG, hrad⟩
  have hψD : ∀ j, ψ j = D.psiPlus j := fun j => hψ j
  have hstar : ∀ j, star (ψ j) = D.psiMinus j := fun j => by
    rw [hψD j]
    exact D.star_psiPlus j
  refine ⟨fun j => ?_, fun j => ?_, ?_⟩
  · rw [hψD j]
    exact D.commutator_psiPlus hclaw hKs j
  · rw [hstar j]
    exact D.commutator_psiMinus hclaw hKs j
  · have h := D.hamiltonian_mul_Pi_matrix hclaw hKs
    rw [h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hstar j, hψD j]

end ModeSector

open scoped Classical in
/-- **The free-fermion solution (v1 Theorem 2, L1248-1264), conditional on `[J, J'] = 0` and on
per-sector coprimality.**

Let `H` be a simplicial-mode Hamiltonian in `Matrix (Fin d) (Fin d) ℂ` with claw-free frustration
graph `G` and simplicial clique `Ks` (an SCF Hamiltonian, `hclaw`, `hKs`), whose generalized cycle
symmetries `J_{⟨C₀⟩} = generalizedCycleSymmetryOp C₀` commute (`hJ`, v1 Theorem 1(iii), not yet
formalised), and such that for every joint-eigenvalue tuple `l` of the `J_{⟨C₀⟩}` that occurs the
sector polynomials `z_{∅,l}`, `z_{Ks,l}` are coprime (`hND`; for real polynomials this is v1's
tacit "no common complex root", see the module docstring).  Then there are

* `Λ`, the set of joint eigenvalue tuples of `{J_{⟨C₀⟩}}` that occur (`l ∈ Λ ↔ …`, zero on the
  classes that are not hole classes), and the projections `Π_l` onto the mutual eigenspaces
  (Hermitian idempotents `≠ 0`, pairwise orthogonal, `∑ Π_l = 1`, `J_{⟨C₀⟩} Π_l = l(⟨C₀⟩) Π_l`,
  in the bicommutant of the `J`'s, each the projection of a `ModeSector` with
  `z_G = z_{∅,l} = sectorPolynomial H.coupling ∅ l`, `z_K = z_{Ks,l} = sectorPolynomial H.coupling
  Ks l`);
* in each sector `l ∈ Λ` exactly `r l = deg z_{∅,l}` distinct positive numbers `u l j` with
  `z_{∅,l} = ∏_j (1 + x/u_{l,j}²)`, `Z_G(-u_{l,j}²) Π_l = 0` (`T(u) T(-u) Π_l = 0`), and
  `z_{Ks,l}(-u_{l,j}²) z_{∅,l}'(-u_{l,j}²) > 0`;
* `N l j = 4 u_{l,j} √(z_{Ks,l}(-u_{l,j}²) z_{∅,l}'(-u_{l,j}²))` (positive), `ε l j = 1/u_{l,j}` and
  the modes `ψ l j = (N l j)⁻¹ Π_l T(-u_{l,j}) χ T(u_{l,j})` (`H.root` is `χ`, `transfer ∅ u` is
  `T_G(u)`), given by these explicit formulas for *all* `l`, `j` (`N`, `ε`, `ψ` are bound by `∃`
  only to be named; their defining equations are conjuncts),

such that for all `l, l' ∈ Λ`, `j : Fin (r l)`, `k : Fin (r l')`:

* `Π_l ψ_{l',k} = ψ_{l',k} Π_l = δ_{l,l'} ψ_{l',k}`, so `[Π_l, ψ_{l',k}] = 0` (v1 Theorem 2,
  L1262-1263), and `[Π_l, ψ_{l',k}^†] = 0`;
* `{ψ_{l,j}, ψ_{l',k}^†} = δ_{l,l'} δ_{jk} Π_l` (v1 Lemma 14; the Kronecker symbol is
  `if l = l' ∧ HEq j k`, as `j` and `k` live in different types when `l ≠ l'`),
  `{ψ_{l,j}, ψ_{l',k}} = 0` and `{ψ_{l,j}^†, ψ_{l',k}^†} = 0`;
* `[H, ψ_{l,j}] = 2 ε_{l,j} ψ_{l,j}` and `[H, ψ_{l,j}^†] = -2 ε_{l,j} ψ_{l,j}^†` (v1 Lemma 13);
* `H = ∑_{l ∈ Λ} (∑_j ε_{l,j} [ψ_{l,j}, ψ_{l,j}^†]) Π_l` (v1 Theorem 2 and Lemma 15).

Proof.  The sectors, the roots and the relations between different or equal sectors are
`exists_crossSectorModes_of_cycleSymmetry_commute` (itself assembled from `CycleSymmetrySectors`,
`ModeSectorPositivity`, `LadderAnticommutation`).  For each `l ∈ Λ` the sector's
non-degeneracy data give the eigenmode relations and `H Π_l = ∑_j ε_j [ψ_j, ψ_j^†]`
(`ModeSector.solution_on_sector`), and `H = H ∑_l Π_l = ∑_l H Π_l = ∑_l (H Π_l) Π_l`.

The premises beyond the manuscript setup are `hJ` (v1 Theorem 1(iii), hence the name) and `hND`
(v1's tacit non-degeneracy; Theorem 2 is false without it, see the module docstring). -/
theorem freeFermionSolution_of_cycleSymmetry_commute {d : ℕ}
    (H : G.SimplicialModeHamiltonian Ks (Matrix (Fin d) (Fin d) ℂ))
    (hclaw : G.IsClawFree) (hKs : G.IsSimplicialClique Ks)
    (hJ : H.frustration.CycleSymmetriesCommute)
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
        (∑ j, ε l j • (ψ l j * star (ψ l j) - star (ψ l j) * ψ l j)) * Pi l := by
  obtain ⟨Λ, Pi, r, u, ψ, h1, h2, h3, h4, h5, h6, h7, h8, hroots, hψ, hcomm, hmul, hCAR1, hCAR2,
    hCAR3⟩ := H.exists_crossSectorModes_of_cycleSymmetry_commute hclaw hKs hJ hND
  -- the solution in each sector
  have hsec : ∀ l ∈ Λ,
      (∀ j, algebraCommutator H.frustration.hamiltonian (ψ l j) = (2 * (u l j)⁻¹) • ψ l j) ∧
      (∀ j, algebraCommutator H.frustration.hamiltonian (star (ψ l j)) =
        (-(2 * (u l j)⁻¹)) • star (ψ l j)) ∧
      H.frustration.hamiltonian * Pi l =
        ∑ j, (u l j)⁻¹ • (ψ l j * star (ψ l j) - star (ψ l j) * ψ l j) := by
    intro l hl
    obtain ⟨S, hSPi, hSzG, hSzK⟩ := h8 l hl
    obtain ⟨-, hinj, hpos, hzG, hrad, -⟩ := hroots l hl
    have key := S.solution_on_sector hclaw hKs (u l) hpos hinj (hSzG.trans hzG)
      (by rw [hSzG, hSzK]; exact hrad) (ψ l)
      (fun j => by rw [hSPi, hSzG, hSzK]; exact hψ l j)
    rw [hSPi] at key
    exact key
  refine ⟨Λ, Pi, r, u,
    fun l j => 4 * u l j * Real.sqrt ((G.sectorPolynomial H.coupling Ks l).eval (-(u l j) ^ 2) *
      (Polynomial.derivative (G.sectorPolynomial H.coupling ∅ l)).eval (-(u l j) ^ 2)),
    fun l j => (u l j)⁻¹, ψ, h1, h2, h3, h4, h5, h6, h7, h8, hroots, fun l j => rfl, ?_,
    fun l j => rfl, hψ, hcomm, hmul, hCAR1, hCAR2, hCAR3, ?_, ?_, ?_⟩
  · -- `N > 0`
    intro l hl j
    obtain ⟨-, -, hpos, -, hrad, -⟩ := hroots l hl
    have h := Real.sqrt_pos.mpr (hrad j)
    have h' := hpos j
    positivity
  · intro l hl j
    exact (hsec l hl).1 j
  · intro l hl j
    exact (hsec l hl).2.1 j
  · calc H.frustration.hamiltonian = H.frustration.hamiltonian * ∑ l ∈ Λ, Pi l := by
          rw [h3, mul_one]
      _ = ∑ l ∈ Λ, H.frustration.hamiltonian * Pi l := Finset.mul_sum _ _ _
      _ = ∑ l ∈ Λ, (∑ j, (u l j)⁻¹ •
            (ψ l j * star (ψ l j) - star (ψ l j) * ψ l j)) * Pi l := by
          refine Finset.sum_congr rfl fun l hl => ?_
          rw [← (hsec l hl).2.2, mul_assoc, (h1 l hl).2.1]

end SimplicialModeHamiltonian

end SimpleGraph
