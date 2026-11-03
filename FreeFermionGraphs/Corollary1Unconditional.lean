import FreeFermionGraphs.TheoremOneIIIConsequences
import FreeFermionGraphs.Corollary1Sector
import FreeFermionGraphs.Theorem3Sectors

/-!
# Corollary 1 (the anticommutator matrix) over the joint eigenprojectors of the cycle symmetries

Manuscript reference: arXiv 2305.15625 v1, Corollary 12 (`corollary:modifiedanticommutationrelation`,
L1341-1392; repository/revised manuscript Corollary 1), and the printed formula of Result 2,
Eq. (`modifiedcommutationrelation`) (L110-127):
`Π_𝒥 {ad^j χ, ad^k χ} = 2 (M_{G,𝒥})_{jk} Π_𝒥` with `M_{G,𝒥}` real symmetric, where `Π_𝒥` is the
projector onto a mutual eigenspace of the generalized cycle symmetries `{J_{⟨C₀⟩}}` and
`ad = [iH, ·]`.  (v1 numbers corollaries with its own counter; the repository follows a revised
manuscript that is not available, in which v1 Corollary 12 is Corollary 1 and v1 Corollary `n - 1`
is Corollary `n` for `n = 2..12`.)

`Corollary1Sector.lean` proves the identity for an arbitrary operator `Pr` with `[H, Pr] = 0`,
`[χ, Pr] = 0` and `J_c Pr = λ_c Pr` (`paperCorollary1_of_commute`).  This module combines it with
the joint spectral decomposition of the cycle symmetries, as `TheoremOneIIIConsequences.paperTheorem3`
does for Theorem 3: for every joint eigenprojector `Π_l` of the `J`'s, `[H, Π_l] = 0` and
`[χ, Π_l] = 0` are *derived* (from the bicommutant clause of `exists_jointSpectralProjections`,
Theorem 1(ii) and Result 2), and `J_c Π_l = l(c) Π_l` is the eigenvalue property.  No commutation
hypothesis on the `J`'s is left: it is Theorem 1(iii)
(`PauliFrustrationRepresentation.cycleSymmetriesCommute`), used inside
`exists_jointSpectralProjections`.

## Main declarations

* `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_bicommutant`: Corollary 1
  for a single `Pr` in the bicommutant of the family `{J_{⟨C₀⟩}}` with `J_{⟨C₀⟩} Pr = λ_{⟨C₀⟩} Pr`
  (premises `hbic`, `heig`); the analogue of `paperTheorem3_of_bicommutant`.
* `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1`: **v1 Corollary 12 over the
  joint eigenprojectors.**  The joint spectral decomposition `(Λ, Π_l)` of the cycle symmetries
  (each `Π_l` Hermitian, idempotent, nonzero, mutually orthogonal, summing to `1`,
  `J Π_l = l Π_l`, in the bicommutant, `Λ` the set of occurring joint eigenvalue tuples) together
  with, for every `l ∈ Λ`, a real symmetric matrix `(M_{jk})_{j,k ∈ ℕ}` with the corrected entries
  `M_{jk} = (-1)^j (-2i)^(j+k) ((A_l)^(j+k))_{{j*},{j*}}`, `A_l = cliqueHoppingMatrix G K H.coupling l`,
  and `Π_l {ad_{iH}^j χ, ad_{iH}^k χ} = {ad_{iH}^j χ, ad_{iH}^k χ} Π_l = 2 M_{jk} Π_l`.
* `SimpleGraph.SimplicialModeHamiltonian.paperCorollary1_modeSectors`: the same for a
  `SimplicialModeHamiltonian` (where `χ² = 1` and the Hermiticity of the Pauli terms are fields),
  for the projections of the `ModeSector`s of Theorem 2.

## Fidelity

* *Names.*  `docs/PAPER_FIDELITY.md` reserves an unqualified paper-facing name for a statement with
  no premise beyond the manuscript setup.  The premises of `paperCorollary1` are
  * `hclaw` (`G` claw-free) and `hK` (`K` a simplicial clique): the standing assumptions of
    Result 2 and Theorem 3 (v1 L110-112, L1328-1336);
  * `hstar` (the Hermitian Pauli terms `h_j = b_j σ^j` with `b_j` real, v1 Eq. (1), L91-93; in
    `SimplicialModeHamiltonian` the field `term_selfAdjoint`), needed to have joint *eigenspaces* of
    the Hermitian `J`'s at all;
  * `hχ : χ² = 1` (`χ = σ^{j*}` is a Pauli operator, v1 Result 2, L111; in
    `SimplicialModeHamiltonian` the field `root_sq`).  The abstract `PauliCliqueHamiltonianRepresentation`
    stores the squares of the original terms (`original_term_sq`) but not that of the root term, so
    this manuscript fact is a hypothesis of the `PauliCliqueHamiltonianRepresentation` form; it is
    not a claim to be proved (it is what "Pauli operator" means), and it is a field of the
    `SimplicialModeHamiltonian` form `paperCorollary1_modeSectors`.
  Connectivity of `G` (Result 2) is not needed and not assumed.  Hence `paperCorollary1` and
  `paperCorollary1_modeSectors` are unqualified, while `paperCorollary1_of_bicommutant`, whose
  premises `hbic`, `heig` describe the operator `Pr` rather than the setup, carries the suffix.
* *No structure field or certificate assumes a claim that is to be proved.*  The projectors
  `Π_l` are produced by `exists_jointSpectralProjections`; `[H, Π_l] = 0` and `[χ, Π_l] = 0` are
  derived, and `J Π_l = l Π_l` is part of that theorem.
* *The sign (correction of v1).*  v1 prints `M_{jk} = (-2i)^(j+k) (A^(j+k))_{{j*},{j*}}`
  (L1388-1389, Result 2 L119-120); the recursion `{ad^j χ, ad^k χ} = -{ad^(j-1) χ, ad^(k+1) χ}`
  (L1380) has a factor `-1` per step, so the solution carries `(-1)^j`, not `(-i)^j`
  (`KrylovAnticommutator.printedCorollary1_fails_single_vertex`).  The statements here carry the
  corrected `(-1)^j`; they are not the printed formula.
* *The matrix.*  `A_l` is the corrected sector matrix of `CliqueHoppingMatrix.lean` (see
  `Theorem3.lean`), not the printed Eq. (decoratedtree) of v1.
* *Reading of "over each mutual eigenspace".*  As in `Theorem3Sectors.lean`, `Π_l` multiplies the
  anticommutator from the left (v1's form) and from the right; the two agree because `Π_l`
  commutes with `H` and `χ`, hence with every `ad^n χ`.
* *Not covered.*  The positive definiteness of `M` (Result 2, L124-125) and the Majorana modes of
  v1 L1394-1430 need a sector trace and are not formalised (see `Corollary1Sector.lean`).

Non-vacuity of `paperCorollary1` (all hypotheses hold and the conclusion is informative) is
checked on the three-qubit `C₄` model in `FreeFermionGraphs.Corollary1Example`.
-/

open scoped BigOperators

universe u v w

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V} {K : Set V}

namespace PauliCliqueHamiltonianRepresentation

/-! ### Corollary 1 for an operator in the bicommutant of the cycle symmetries -/

section Bicommutant

variable [Fintype V] [DecidableEq V] {A : Type w}
variable [Ring A] [Algebra ℂ A] [Algebra ℝ A] [IsScalarTower ℝ ℂ A]
variable [DecidableEq (CliqueRootedInducedPath G K)]

/-- **Corollary 1 of v1 for `Pr` in the bicommutant of the cycle symmetries, with eigenvalues
`λ`** (v1 Corollary 12, L1341-1392; Theorem 1(ii), Result 2).

Let `Pr` be an operator such that
* every `x` that commutes with all `J_{⟨C₀⟩}` (`C₀` an even-hole carrier) commutes with `Pr`
  (`hbic`; the bicommutant clause satisfied by the joint spectral projectors `Π_l` of the `J`'s,
  see `PauliFrustrationRepresentation.exists_jointSpectralProjections`), and
* `J_{⟨C₀⟩} Pr = λ_{⟨C₀⟩} Pr` for every even-hole carrier `C₀` (`heig`, `λ` real).

If `χ² = 1` (`hχ`), then there is a real symmetric matrix `(M_{jk})_{j,k ∈ ℕ}` with the corrected
entries `M_{jk} = (-1)^j (-2i)^(j+k) ((A_λ)^(j+k))_{{j*},{j*}}`, `A_λ = cliqueHoppingMatrix G K
H.coupling lam`, such that, with `ad = [iH, ·]`,
`Pr {ad^j χ, ad^k χ} = {ad^j χ, ad^k χ} Pr = 2 M_{jk} Pr`.

`[H, Pr] = 0` is Theorem 1(ii) (`commute_physicalHamiltonian_of_forall_commute`) and `[χ, Pr] = 0`
is Result 2 (`commute_rootOperator_of_forall_commute`), both derived from `hbic`; then
`paperCorollary1_of_commute_exists` applies.  The statement does not use `Pr² = Pr` or `Pr ≠ 0`.
The name is qualified because `Pr` is assumed to be in the bicommutant (`hbic`) and an
eigen-operator (`heig`); for the joint spectral projector `Π_l` both hold, see `paperCorollary1`. -/
theorem paperCorollary1_of_bicommutant
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree)
    (H : G.PauliCliqueHamiltonianRepresentation K ℝ A) (Pr : A)
    (hbic : ∀ x : A, (∀ C₀ : Set V, G.IsEvenHoleCarrier C₀ →
        Commute x (H.operator.restrictSome.generalizedCycleSymmetryOp C₀)) → Commute x Pr)
    (hχ : H.rootOperator * H.rootOperator = 1)
    (lam : EvenHoleDeformationClass G → ℝ)
    (heig : ∀ C₀ : Set V, G.IsEvenHoleCarrier C₀ →
      H.operator.restrictSome.generalizedCycleSymmetryOp C₀ * Pr =
        ((lam (G.evenHoleDeformationClassOf C₀) : ℝ) : ℂ) • Pr) :
    ∃ M : ℕ → ℕ → ℝ,
      (∀ j k, M j k = M k j) ∧
      (∀ j k, (M j k : ℂ) = (-1) ^ j * (-2 * Complex.I) ^ (j + k) *
        (((cliqueHoppingMatrix G K H.coupling lam ^ (j + k)) (cliqueRootPath G K)
          (cliqueRootPath G K) : ℝ) : ℂ)) ∧
      (∀ j k,
        Pr * (iteratedCommutator (Complex.I • H.physicalHamiltonian) j H.rootOperator *
            iteratedCommutator (Complex.I • H.physicalHamiltonian) k H.rootOperator +
          iteratedCommutator (Complex.I • H.physicalHamiltonian) k H.rootOperator *
            iteratedCommutator (Complex.I • H.physicalHamiltonian) j H.rootOperator) =
          ((2 : ℂ) * (M j k : ℂ)) • Pr) ∧
      (∀ j k,
        (iteratedCommutator (Complex.I • H.physicalHamiltonian) j H.rootOperator *
            iteratedCommutator (Complex.I • H.physicalHamiltonian) k H.rootOperator +
          iteratedCommutator (Complex.I • H.physicalHamiltonian) k H.rootOperator *
            iteratedCommutator (Complex.I • H.physicalHamiltonian) j H.rootOperator) * Pr =
          ((2 : ℂ) * (M j k : ℂ)) • Pr) := by
  have hHP : Commute H.physicalHamiltonian Pr :=
    commute_physicalHamiltonian_of_forall_commute hclaw H hbic
  have hχP : Commute H.rootOperator Pr := commute_rootOperator_of_forall_commute hK H hbic
  have hreal : ∀ (r : ℝ) (x : A), r • x = (r : ℂ) • x := fun r x => by
    calc r • x = r • ((1 : ℂ) • x) := by rw [one_smul]
      _ = (r • (1 : ℂ)) • x := (smul_assoc r (1 : ℂ) x).symm
      _ = (r : ℂ) • x := by rw [Complex.real_smul, mul_one]
  have hJ : ∀ (k : ℕ) (E : EvenHoleLabeling G k), E.HasFullCyclicOrder →
      H.generalizedCycleOperator (G.evenHoleDeformationClassOf E.carrier) * Pr =
        lam (G.evenHoleDeformationClassOf E.carrier) • Pr := by
    intro k' E hE
    rw [generalizedCycleOperator_mk, heig _ (E.isEvenHoleCarrier_of_hasFullCyclicOrder hE),
      ← hreal]
  obtain ⟨M, hsymm, hentry, hright, hleft⟩ :=
    paperCorollary1_of_commute_exists hK hclaw H Pr hHP hχP hχ lam hJ
  exact ⟨M, hsymm, hentry, hleft, hright⟩

end Bicommutant

/-! ### Corollary 1 over the joint eigenprojectors -/

section Joint

variable [Fintype V] [DecidableEq V] {d : ℕ}
variable [DecidableEq (CliqueRootedInducedPath G K)]

/-- **Corollary 1 of v1 over the joint eigenprojectors of the cycle symmetries**
(`corollary:modifiedanticommutationrelation`, L1341-1392, and Result 2 Eq.
(`modifiedcommutationrelation`), L110-127: "`Π_𝒥 {ad^j χ, ad^k χ} = 2 (M_{G,𝒥})_{jk} Π_𝒥` where
`M_{G,𝒥}` is real symmetric"), with Theorem 1 (iii) (L864-871, `paperTheorem1iii`) discharged.

Let `H` be a Pauli clique Hamiltonian representation in `Matrix (Fin d) (Fin d) ℂ` with real
couplings and Hermitian terms `h_j` (`hstar`), whose frustration graph `G` is claw-free (`hclaw`),
in which `K` is a simplicial clique (`hK`), and whose root term squares to the identity
(`hχ : χ² = 1`, `χ = σ^{j*}` a Pauli operator).  Then there are a finite set `Λ` of tuples
`l : G.EvenHoleDeformationClass → ℝ` (zero on the junk classes) and matrices `Π_l` such that

* (the joint spectral decomposition of
  `PauliFrustrationRepresentation.exists_jointSpectralProjections`) each `Π_l` (`l ∈ Λ`) is
  Hermitian, idempotent and nonzero, `Π_l Π_m = 0` for `l ≠ m`, `∑_{l ∈ Λ} Π_l = 1`,
  `J_{⟨C₀⟩} Π_l = l(⟨C₀⟩) Π_l`, every operator commuting with all the `J_{⟨C₀⟩}` commutes with
  every `Π_l`, and `Λ` is exactly the set of joint eigenvalue tuples that occur;
* for every `l ∈ Λ` there is a real matrix `(M_{jk})_{j,k ∈ ℕ}` with `M_{jk} = M_{kj}`,
  `M_{jk} = (-1)^j (-2i)^(j+k) ((A_l)^(j+k))_{{j*},{j*}}` where
  `A_l = cliqueHoppingMatrix G K H.coupling l`, and, in the convention `ad = [iH, ·]` of v1,
  `Π_l {ad^j χ, ad^k χ} = {ad^j χ, ad^k χ} Π_l = 2 M_{jk} Π_l`.

The proof is `exists_jointSpectralProjections` (`Π_l` lies in the bicommutant of the `J`'s, and
`J Π_l = l Π_l`) followed by `paperCorollary1_of_bicommutant`, i.e. by `paperCorollary1_of_commute`
with `[H, Π_l] = 0` from Theorem 1(ii) (`hamiltonian_commute_generalizedCycleSymmetryOp`) and
`[χ, Π_l] = 0` from Result 2 (`commute_rootOperator_generalizedCycleOperator`).

The premises are the setup of v1 (the representation `H`, Hermitian Pauli terms, `χ` a Pauli
operator, finiteness of `V`) and the standing assumptions `hK`, `hclaw`; there is no premise
beyond these, so the name is unqualified (see the module docstring).

Deviations from v1, as in `paperCorollary1_of_commute`: the sign `(-1)^j` corrects v1's printed
`M_{jk}`, which is false already for a single vertex, `A_l` is the corrected matrix of
`CliqueHoppingMatrix.lean`, and positive definiteness of `M` and the Majorana modes are not
covered. -/
theorem paperCorollary1
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree)
    (H : G.PauliCliqueHamiltonianRepresentation K ℝ (Matrix (Fin d) (Fin d) ℂ))
    (hstar : ∀ j : V, IsSelfAdjoint (H.operator.term (some j)))
    (hχ : H.rootOperator * H.rootOperator = 1) :
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
      (∀ l ∈ Λ, ∃ M : ℕ → ℕ → ℝ,
        (∀ j k, M j k = M k j) ∧
        (∀ j k, (M j k : ℂ) = (-1) ^ j * (-2 * Complex.I) ^ (j + k) *
          (((cliqueHoppingMatrix G K H.coupling l ^ (j + k)) (cliqueRootPath G K)
            (cliqueRootPath G K) : ℝ) : ℂ)) ∧
        (∀ j k,
          Pi l * (iteratedCommutator (Complex.I • H.physicalHamiltonian) j H.rootOperator *
              iteratedCommutator (Complex.I • H.physicalHamiltonian) k H.rootOperator +
            iteratedCommutator (Complex.I • H.physicalHamiltonian) k H.rootOperator *
              iteratedCommutator (Complex.I • H.physicalHamiltonian) j H.rootOperator) =
            ((2 : ℂ) * (M j k : ℂ)) • Pi l) ∧
        (∀ j k,
          (iteratedCommutator (Complex.I • H.physicalHamiltonian) j H.rootOperator *
              iteratedCommutator (Complex.I • H.physicalHamiltonian) k H.rootOperator +
            iteratedCommutator (Complex.I • H.physicalHamiltonian) k H.rootOperator *
              iteratedCommutator (Complex.I • H.physicalHamiltonian) j H.rootOperator) * Pi l =
            ((2 : ℂ) * (M j k : ℂ)) • Pi l)) := by
  obtain ⟨Λ, Pi, h1, h2, h3, h4, h5, h6, h7⟩ :=
    H.operator.restrictSome.exists_jointSpectralProjections hclaw hstar
  exact ⟨Λ, Pi, h1, h2, h3, h4, h5, h6, h7, fun l hl =>
    paperCorollary1_of_bicommutant hK hclaw H (Pi l) (fun x hx => h6 x hx l hl) hχ l (h4 l hl)⟩

end Joint

end PauliCliqueHamiltonianRepresentation

/-! ### The same projections are the projections of the mode sectors -/

namespace SimplicialModeHamiltonian

variable {Ks : Set V} [Fintype V] [DecidableEq V] {d : ℕ}
variable [DecidableEq (CliqueRootedInducedPath G Ks)]

/-- **Corollary 1 over the joint eigenprojectors, which are the projections of the mode sectors of
Theorem 2** (v1 Corollary 12, L1341-1392, and v1 Theorem 2, L1248-1264), with Theorem 1 (iii)
discharged.

For a simplicial-mode Hamiltonian `H` in `Matrix (Fin d) (Fin d) ℂ` with claw-free frustration
graph `G` and simplicial clique `Ks`, the joint spectral projectors `Π_l` (`l ∈ Λ`) of
`exists_modeSectors` satisfy, besides all the properties listed there (spectral decomposition;
`Π_l` is the projection of a `ModeSector` with `zG = z_{∅,l}`, `zK = z_{Ks,l}`), the Corollary 1
identity of `PauliCliqueHamiltonianRepresentation.paperCorollary1`: for every `l ∈ Λ` there is a
real symmetric matrix `(M_{jk})` with `M_{jk} = (-1)^j (-2i)^(j+k) ((A_l)^(j+k))_{{j*},{j*}}`,
`A_l = cliqueHoppingMatrix G Ks H.coupling l`, and
`Π_l {ad_{iH}^j χ, ad_{iH}^k χ} = {ad_{iH}^j χ, ad_{iH}^k χ} Π_l = 2 M_{jk} Π_l`.

Hermiticity of the Pauli terms and `χ² = 1` are the fields `term_selfAdjoint` and `root_sq`; there
is no premise beyond the setup and `hclaw`, `hKs`, so the name is unqualified.  The non-degeneracy
hypothesis of Theorem 2 is not used. -/
theorem paperCorollary1_modeSectors
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
      (∀ l ∈ Λ, ∃ M : ℕ → ℕ → ℝ,
        (∀ j k, M j k = M k j) ∧
        (∀ j k, (M j k : ℂ) = (-1) ^ j * (-2 * Complex.I) ^ (j + k) *
          (((cliqueHoppingMatrix G Ks H.coupling l ^ (j + k)) (cliqueRootPath G Ks)
            (cliqueRootPath G Ks) : ℝ) : ℂ)) ∧
        (∀ j k,
          Pi l * (iteratedCommutator (Complex.I • H.physicalHamiltonian) j H.rootOperator *
              iteratedCommutator (Complex.I • H.physicalHamiltonian) k H.rootOperator +
            iteratedCommutator (Complex.I • H.physicalHamiltonian) k H.rootOperator *
              iteratedCommutator (Complex.I • H.physicalHamiltonian) j H.rootOperator) =
            ((2 : ℂ) * (M j k : ℂ)) • Pi l) ∧
        (∀ j k,
          (iteratedCommutator (Complex.I • H.physicalHamiltonian) j H.rootOperator *
              iteratedCommutator (Complex.I • H.physicalHamiltonian) k H.rootOperator +
            iteratedCommutator (Complex.I • H.physicalHamiltonian) k H.rootOperator *
              iteratedCommutator (Complex.I • H.physicalHamiltonian) j H.rootOperator) * Pi l =
            ((2 : ℂ) * (M j k : ℂ)) • Pi l)) := by
  obtain ⟨Λ, Pi, h1, h2, h3, h4, h5, h6, h7, h8⟩ := H.exists_modeSectors hclaw hKs
  exact ⟨Λ, Pi, h1, h2, h3, h4, h5, h6, h7, h8, fun l hl =>
    PauliCliqueHamiltonianRepresentation.paperCorollary1_of_bicommutant hKs hclaw
      H.toPauliCliqueHamiltonianRepresentation (Pi l) (fun x hx => h6 x hx l hl) H.root_sq l
      (h4 l hl)⟩

end SimplicialModeHamiltonian

end SimpleGraph
