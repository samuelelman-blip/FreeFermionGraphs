import FreeFermionGraphs.CycleSymmetrySectors
import FreeFermionGraphs.Theorem3

/-!
# Theorem 3 over the joint spectral projectors of the cycle symmetries

Manuscript reference: arXiv 2305.15625v1, Theorem 3 `theorem:polynomialdivisibility`
(L1328-1336): "`Π_𝒥 ad_{iH}^k χ = (-2i)^k ∑_{P ∈ 𝒫} (A_{G,𝒥}^k)_{{j*},P} h_P` over each mutual
eigenspace of the `{J_{⟨C₀⟩}}`, where `χ` is a simplicial mode corresponding to the vertex `j*`
not in `V`, ... the matrix `A_{G,𝒥}` denotes the weighted adjacency matrix of a directed
bipartite graph", with Theorem 1(ii) (`[H, J_{⟨C₀⟩}] = 0`, L864-871), Result 2 (`[χ, J] = 0`,
L110-127) and Definition 15 (`J_{⟨C₀⟩} = ∑_{C ∈ ⟨C₀⟩} h_C`, L799-803).  (The repository numbers
some lemmas of v1 differently, following a revised manuscript that is not available.)

`Theorem3.lean` proves the identity for an arbitrary operator `Pr` with `[H, Pr] = 0` and
`J_c Pr = λ_c Pr`, and `CycleSymmetrySectors.lean` constructs the joint spectral projectors
`Π_l` of the `J`'s in `Matrix (Fin d) (Fin d) ℂ`.  This module combines the two: for the actual
joint spectral projectors, which exist when the `J`'s commute pairwise.

## Main declarations

* `PauliCliqueHamiltonianRepresentation.paperTheorem3_ad_of_commute`: the manuscript convention
  `ad_{iH} = [iH, ·]` with the explicit corrected matrix `A_λ`, for any `Pr` with `[H, Pr] = 0`
  and `J_c Pr = λ_c Pr` (this is `paperTheorem3_of_commute_exists` with the witness exposed).
* `commute_physicalHamiltonian_of_forall_commute`, `commute_rootOperator_of_forall_commute`: an
  operator that commutes with everything commuting with all `J_{⟨C₀⟩}` (the bicommutant clause
  of `exists_jointSpectralProjections_of_cycleSymmetry_commute`) commutes with `H` (Theorem 1(ii))
  and with `χ` (`commute_rootOperator_generalizedCycleOperator`).
* `paperTheorem3_of_bicommutant`: Theorem 3 for a single `Pr` in the bicommutant of the family
  `{J_{⟨C₀⟩}}` with `J_{⟨C₀⟩} Pr = λ_{⟨C₀⟩} Pr`; the conclusion contains `[Pr, ad^k χ] = 0`, so
  `Pr ad^k χ = ad^k χ Pr`, and both equal `(-2i)^k ∑_P (A_λ^k)_{{j*},P} h_P Pr`.
* `paperTheorem3_of_cycleSymmetry_commute`: **the joint spectral decomposition**
  `{(Λ, Π_l)}` of the `J`'s together with Theorem 3 over every `Π_l`, `l ∈ Λ`, conditional on
  `[J_{⟨C₀⟩}, J_{⟨C₁⟩}] = 0` (v1 Theorem 1(iii), not yet formalised).
* `SimplicialModeHamiltonian.paperTheorem3_modeSectors_of_cycleSymmetry_commute`: the same, with
  the sector projections identified with the projections of the `ModeSector`s of
  `exists_modeSectors_of_cycleSymmetry_commute` (the common input of Theorem 2).

## Fidelity

* *Name.*  The only premise beyond the manuscript setup is `hJ : H.CycleSymmetriesCommute`, the
  commutation `[J_{⟨C₀⟩}, J_{⟨C₁⟩}] = 0` of v1 Theorem 1(iii), which is not formalised yet.
  Without it the "mutual eigenspaces of the `J`'s" of v1 are not defined, so the name carries the
  suffix `_of_cycleSymmetry_commute` (docs/PAPER_FIDELITY.md).  Once Theorem 1(iii) is proved, the
  hypothesis `hJ` is discharged and the theorem is the unqualified statement of v1 over the joint
  eigenspaces.  The Hermiticity of the Pauli terms (`hstar`) is part of the manuscript setup
  (`SimplicialModeHamiltonian.term_selfAdjoint`); `hclaw` (claw-free) and `hK` (`K` simplicial)
  are the standing assumptions of Theorem 3.  No structure field or certificate assumes a claim
  to be proved: the projectors `Π_l` are produced by the spectral theory of commuting Hermitian
  matrices, and `[H, Π_l] = 0 = [χ, Π_l]` are *derived* from the bicommutant clause, Theorem 1(ii)
  and Result 2.
* *Reading of "over each mutual eigenspace".*  As in `Theorem3.lean`, the identity is
  `ad^k χ · Π_l = (-2i)^k ∑_P (A_λ^k)_{{j*},P} h_P Π_l`, with `Π_l` multiplied on the right of
  each path operator: `J_c` need not commute with the individual `h_P`, so `Π_l ∑_P c_P h_P` is
  not the right object.  Since `Π_l` commutes with `ad^k χ`, the left form `Π_l ad^k χ` of v1 has
  the same value.
* *Matrix.*  `A_λ = cliqueHoppingMatrix G K b l` is the corrected matrix of
  `CliqueHoppingMatrix.lean` (sign `(-1)^{k-1}`, root-handle arcs, per-event normalisation), which
  differs from the printed Eq. (decoratedtree) of v1; see `Theorem3.lean`.  It is real (an
  `ℝ`-matrix) and bipartite: `A_λ(P, Q) ≠ 0` forces `|P| + |Q|` odd
  (`cliqueHoppingMatrix_ne_zero_imp_odd`).
* *Sector labels.*  `l` runs over the tuples of `exists_jointSpectralProjections_of_cycleSymmetry_commute`
  (functions on all of `EvenHoleDeformationClass`, zero on the junk classes); only the values on
  the genuine hole classes enter `A_λ` and the eigenvalue equations.
-/

open scoped BigOperators

universe u v w

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V} {K : Set V}

namespace PauliCliqueHamiltonianRepresentation

/-! ### Commutation with `H` and `χ` -/

section Commutation

variable [Fintype V] [DecidableEq V] {R : Type v} {A : Type w}
variable [CommRing R] [Ring A] [Algebra R A]

/-- An operator `Pr` that commutes with every `x` commuting with all `J_{⟨C₀⟩}` (the bicommutant
clause of `PauliFrustrationRepresentation.exists_jointSpectralProjections_of_cycleSymmetry_commute`)
commutes with the physical Hamiltonian, because `[H, J_{⟨C₀⟩}] = 0` (v1 Theorem 1(ii),
`PauliFrustrationRepresentation.hamiltonian_commute_generalizedCycleSymmetryOp`). -/
theorem commute_physicalHamiltonian_of_forall_commute (hclaw : G.IsClawFree)
    (H : G.PauliCliqueHamiltonianRepresentation K R A) {Pr : A}
    (hbic : ∀ x : A, (∀ C₀ : Set V, G.IsEvenHoleCarrier C₀ →
        Commute x (H.operator.restrictSome.generalizedCycleSymmetryOp C₀)) → Commute x Pr) :
    Commute H.physicalHamiltonian Pr := by
  refine hbic _ fun C₀ hC₀ => ?_
  have h := H.operator.restrictSome.hamiltonian_commute_generalizedCycleSymmetryOp hclaw hC₀
  unfold algebraCommutator at h
  exact sub_eq_zero.1 h

/-- An operator `Pr` that commutes with every `x` commuting with all `J_{⟨C₀⟩}` commutes with the
simplicial mode `χ`: `χ` commutes with every generalized cycle symmetry (v1 Result 2, L112,
`commute_rootOperator_generalizedCycleOperator`; this uses that `K` is a simplicial clique). -/
theorem commute_rootOperator_of_forall_commute (hK : G.IsSimplicialClique K)
    (H : G.PauliCliqueHamiltonianRepresentation K R A) {Pr : A}
    (hbic : ∀ x : A, (∀ C₀ : Set V, G.IsEvenHoleCarrier C₀ →
        Commute x (H.operator.restrictSome.generalizedCycleSymmetryOp C₀)) → Commute x Pr) :
    Commute H.rootOperator Pr := by
  refine hbic _ fun C₀ _ => ?_
  rw [← generalizedCycleOperator_mk]
  exact commute_rootOperator_generalizedCycleOperator hK H _

end Commutation

/-- If `H` and `x` commute with `Pr`, then so does every iterated commutator `ad_H^n x`. -/
theorem commute_iteratedCommutator_of_commute {A : Type w} [Ring A] {H x Pr : A}
    (hH : Commute H Pr) (hx : Commute x Pr) (n : ℕ) :
    Commute (iteratedCommutator H n x) Pr := by
  induction n with
  | zero => exact hx
  | succ n ih =>
      rw [iteratedCommutator_succ]
      unfold algebraCommutator
      exact (hH.mul_left ih).sub_left (ih.mul_left hH)

/-! ### The manuscript convention `ad_{iH} = [iH, ·]` with the explicit matrix -/

section AdForm

variable [Fintype V] [DecidableEq V] {A : Type w}
variable [Ring A] [Algebra ℂ A] [Algebra ℝ A] [IsScalarTower ℝ ℂ A]
variable [DecidableEq (CliqueRootedInducedPath G K)]

/-- **Theorem 3 of v1 on a symmetry sector in the manuscript convention** `ad_{iH} = [iH, ·]`
(v1 L1328-1336), with the explicit matrix.  For `Pr` with `[H, Pr] = 0` and
`J_c Pr = λ_c Pr` (`λ_c` real, over the classes of genuine even holes), for every `k`

`ad_{iH}^k (χ) · Pr = ∑_P ((-2i)^k (A_λ^k)_{{j*},P}) • (h_P Pr)`,

where `A_λ = cliqueHoppingMatrix G K H.coupling lam` is real.  This is the identity of
`paperTheorem3_of_commute_exists`, which only asserts the existence of a witness matrix, with the
witness exposed.  The name stays qualified because of the premises `hHP`, `hJ` on `Pr`
(`docs/PAPER_FIDELITY.md`). -/
theorem paperTheorem3_ad_of_commute
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree)
    (H : G.PauliCliqueHamiltonianRepresentation K ℝ A) (Pr : A)
    (hHP : Commute H.physicalHamiltonian Pr) (lam : EvenHoleDeformationClass G → ℝ)
    (hJ : ∀ (k : ℕ) (E : EvenHoleLabeling G k), E.HasFullCyclicOrder →
      H.generalizedCycleOperator (G.evenHoleDeformationClassOf E.carrier) * Pr =
        lam (G.evenHoleDeformationClassOf E.carrier) • Pr)
    (k : ℕ) :
    iteratedCommutator (Complex.I • H.physicalHamiltonian) k H.rootOperator * Pr =
      ∑ P : CliqueRootedInducedPath G K,
        ((-2 * Complex.I) ^ k *
            ((cliqueHoppingMatrix G K H.coupling lam ^ k) (cliqueRootPath G K) P : ℂ)) •
          (H.pathOperator P * Pr) := by
  rw [iteratedCommutator_smul_left, smul_mul_assoc,
    paperTheorem3_of_commute hK hclaw H Pr hHP lam hJ k, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  have hreal : ∀ (r : ℝ) (x : A), r • x = (r : ℂ) • x := fun r x => by
    calc r • x = r • ((1 : ℂ) • x) := by rw [one_smul]
      _ = (r • (1 : ℂ)) • x := (smul_assoc r (1 : ℂ) x).symm
      _ = (r : ℂ) • x := by rw [Complex.real_smul, mul_one]
  rw [hreal, smul_smul, mul_pow]
  push_cast
  ring_nf

/-! ### Theorem 3 for an operator in the bicommutant of the cycle symmetries -/

/-- **Theorem 3 of v1 for `Pr` in the bicommutant of the cycle symmetries, with eigenvalues
`λ`** (v1 L1328-1336; Theorem 1(ii), Result 2).

Let `Pr` be an operator such that
* every `x` that commutes with all `J_{⟨C₀⟩}` (`C₀` an even-hole carrier) commutes with `Pr`
  (`hbic`; this is the bicommutant clause satisfied by the joint spectral projectors `Π_l` of the
  `J`'s, see `exists_jointSpectralProjections_of_cycleSymmetry_commute`), and
* `J_{⟨C₀⟩} Pr = λ_{⟨C₀⟩} Pr` for every even-hole carrier `C₀` (`heig`, `λ` real).

Then for every `k`:
* `Pr` commutes with `ad_{iH}^k χ` (as `[H, Pr] = 0` by Theorem 1(ii) and `[χ, Pr] = 0` by
  Result 2, both derived from `hbic`);
* `Pr · ad_{iH}^k χ = ad_{iH}^k χ · Pr = ∑_P ((-2i)^k (A_λ^k)_{{j*},P}) • (h_P Pr)`,
  with the real matrix `A_λ = cliqueHoppingMatrix G K H.coupling lam`.

The statement does not use `Pr² = Pr` or `Pr ≠ 0`.  The name is qualified because `Pr` is assumed
to be in the bicommutant (`hbic`) and an eigen-operator (`heig`); for the joint spectral projector
`Π_l` of the `J`'s both hold, see `paperTheorem3_of_cycleSymmetry_commute`. -/
theorem paperTheorem3_of_bicommutant
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree)
    (H : G.PauliCliqueHamiltonianRepresentation K ℝ A) (Pr : A)
    (hbic : ∀ x : A, (∀ C₀ : Set V, G.IsEvenHoleCarrier C₀ →
        Commute x (H.operator.restrictSome.generalizedCycleSymmetryOp C₀)) → Commute x Pr)
    (lam : EvenHoleDeformationClass G → ℝ)
    (heig : ∀ C₀ : Set V, G.IsEvenHoleCarrier C₀ →
      H.operator.restrictSome.generalizedCycleSymmetryOp C₀ * Pr =
        ((lam (G.evenHoleDeformationClassOf C₀) : ℝ) : ℂ) • Pr)
    (k : ℕ) :
    Commute Pr (iteratedCommutator (Complex.I • H.physicalHamiltonian) k H.rootOperator) ∧
    Pr * iteratedCommutator (Complex.I • H.physicalHamiltonian) k H.rootOperator =
      ∑ P : CliqueRootedInducedPath G K,
        ((-2 * Complex.I) ^ k *
            ((cliqueHoppingMatrix G K H.coupling lam ^ k) (cliqueRootPath G K) P : ℂ)) •
          (H.pathOperator P * Pr) ∧
    iteratedCommutator (Complex.I • H.physicalHamiltonian) k H.rootOperator * Pr =
      ∑ P : CliqueRootedInducedPath G K,
        ((-2 * Complex.I) ^ k *
            ((cliqueHoppingMatrix G K H.coupling lam ^ k) (cliqueRootPath G K) P : ℂ)) •
          (H.pathOperator P * Pr) := by
  have hHP : Commute H.physicalHamiltonian Pr :=
    commute_physicalHamiltonian_of_forall_commute hclaw H hbic
  have hχP : Commute H.rootOperator Pr := commute_rootOperator_of_forall_commute hK H hbic
  have hcomm : Commute (iteratedCommutator (Complex.I • H.physicalHamiltonian) k H.rootOperator)
      Pr :=
    commute_iteratedCommutator_of_commute (hHP.smul_left Complex.I) hχP k
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
  have hmain := paperTheorem3_ad_of_commute hK hclaw H Pr hHP lam hJ k
  exact ⟨hcomm.symm, hcomm.eq.symm.trans hmain, hmain⟩

end AdForm

/-! ### Theorem 3 over the joint spectral projectors, conditional on `[J, J'] = 0` -/

section Joint

variable [Fintype V] [DecidableEq V] {d : ℕ}
variable [DecidableEq (CliqueRootedInducedPath G K)]

/-- **Theorem 3 of v1 over the joint spectral projectors of the cycle symmetries, conditional on
`[J_{⟨C₀⟩}, J_{⟨C₁⟩}] = 0`** (v1 Theorem 3, L1328-1336: "over each mutual eigenspace of the
`{J_{⟨C₀⟩}}`").

Let `H` be a Pauli clique Hamiltonian representation in `Matrix (Fin d) (Fin d) ℂ` with real
couplings and Hermitian terms `h_j` (`hstar`), whose frustration graph `G` is claw-free
(`hclaw`) and in which `K` is a simplicial clique (`hK`), and suppose that the generalized cycle
symmetries commute pairwise (`hJ`, v1 Theorem 1(iii)).  Then there are a finite set `Λ` of tuples
`l : EvenHoleDeformationClass G → ℝ` (zero on the junk classes) and matrices `Π_l` such that

* (the joint spectral decomposition of `exists_jointSpectralProjections_of_cycleSymmetry_commute`)
  each `Π_l` (`l ∈ Λ`) is Hermitian, idempotent and nonzero, `Π_l Π_m = 0` for `l ≠ m`,
  `∑_{l ∈ Λ} Π_l = 1`, `J_{⟨C₀⟩} Π_l = l(⟨C₀⟩) Π_l`, every operator commuting with all the
  `J_{⟨C₀⟩}` commutes with every `Π_l`, and `Λ` is exactly the set of joint eigenvalue tuples that
  occur;
* for every `l ∈ Λ` the matrix `A_l = cliqueHoppingMatrix G K H.coupling l` is real and bipartite
  (`A_l(P, Q) ≠ 0 → |P| + |Q|` odd), and for every `k`, in the convention `ad_{iH} = [iH, ·]` of
  v1, `Π_l` commutes with `ad_{iH}^k χ` and

  `Π_l ad_{iH}^k χ = ad_{iH}^k χ Π_l = ∑_P ((-2i)^k (A_l^k)_{{j*},P}) • (h_P Π_l)`.

The hypothesis `hJ` is v1 Theorem 1(iii), which is not formalised yet, hence the name
`_of_cycleSymmetry_commute` (docs/PAPER_FIDELITY.md).  It is the only premise beyond the
manuscript setup; once Theorem 1(iii) is proved it is discharged, and this is the unqualified
statement of v1 over the joint eigenspaces of the `J`'s.  The proof combines
`exists_jointSpectralProjections_of_cycleSymmetry_commute` with `paperTheorem3_of_bicommutant`:
`Π_l` lies in the bicommutant of the family `{J_{⟨C₀⟩}}` (so it commutes with `H` by Theorem 1(ii)
and with `χ` by Result 2), and `J_{⟨C₀⟩} Π_l = l(⟨C₀⟩) Π_l`.  Here `Π_l` multiplies the path
operators from the right (see the module docstring). -/
theorem paperTheorem3_of_cycleSymmetry_commute
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree)
    (H : G.PauliCliqueHamiltonianRepresentation K ℝ (Matrix (Fin d) (Fin d) ℂ))
    (hstar : ∀ j : V, IsSelfAdjoint (H.operator.term (some j)))
    (hJ : H.operator.restrictSome.CycleSymmetriesCommute) :
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
                (H.pathOperator P * Pi l)) := by
  obtain ⟨Λ, Pi, h1, h2, h3, h4, h5, h6, h7⟩ :=
    H.operator.restrictSome.exists_jointSpectralProjections_of_cycleSymmetry_commute hstar hJ
  refine ⟨Λ, Pi, h1, h2, h3, h4, h5, h6, h7, fun l hl => ⟨fun P Q h =>
    cliqueHoppingMatrix_ne_zero_imp_odd h, fun k => ?_⟩⟩
  exact paperTheorem3_of_bicommutant hK hclaw H (Pi l) (fun x hx => h6 x hx l hl) l
    (h4 l hl) k

end Joint

end PauliCliqueHamiltonianRepresentation

/-! ### The same projections are the projections of the mode sectors -/

namespace SimplicialModeHamiltonian

variable {Ks : Set V} [Fintype V] [DecidableEq V] {d : ℕ}
variable [DecidableEq (CliqueRootedInducedPath G Ks)]

/-- **Theorem 3 over the joint spectral projectors, which are the projections of the mode
sectors of Theorem 2, conditional on `[J, J'] = 0`** (v1 Theorem 3, L1328-1336, and v1
Theorem 2, L1248-1264).

For a simplicial-mode Hamiltonian `H` in `Matrix (Fin d) (Fin d) ℂ` with claw-free frustration
graph `G`, simplicial clique `Ks` and pairwise commuting cycle symmetries (`hJ`, v1
Theorem 1(iii)), the joint spectral projectors `Π_l` (`l ∈ Λ`) of
`exists_modeSectors_of_cycleSymmetry_commute` satisfy, besides all the properties listed there
(spectral decomposition; `Π_l` is the projection of a `ModeSector` with `zG = z_{∅,l}`,
`zK = z_{Ks,l}`), the Theorem 3 identity of
`paperTheorem3_of_cycleSymmetry_commute`: `A_l = cliqueHoppingMatrix G Ks H.coupling l` is real
and bipartite, `Π_l` commutes with every `ad_{iH}^k χ`, and
`Π_l ad_{iH}^k χ = ad_{iH}^k χ Π_l = ∑_P ((-2i)^k (A_l^k)_{{j*},P}) • (h_P Π_l)`.

The only premise beyond the manuscript setup is `hJ` (v1 Theorem 1(iii), not formalised yet),
hence the name; see `paperTheorem3_of_cycleSymmetry_commute`. -/
theorem paperTheorem3_modeSectors_of_cycleSymmetry_commute
    (H : G.SimplicialModeHamiltonian Ks (Matrix (Fin d) (Fin d) ℂ))
    (hclaw : G.IsClawFree) (hKs : G.IsSimplicialClique Ks)
    (hJ : H.frustration.CycleSymmetriesCommute) :
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
                (H.pathOperator P * Pi l)) := by
  obtain ⟨Λ, Pi, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    H.exists_modeSectors_of_cycleSymmetry_commute hclaw hKs hJ
  refine ⟨Λ, Pi, h1, h2, h3, h4, h5, h6, h7, h8, fun l hl => ⟨fun P Q h =>
    cliqueHoppingMatrix_ne_zero_imp_odd h, fun k => ?_⟩⟩
  exact PauliCliqueHamiltonianRepresentation.paperTheorem3_of_bicommutant hKs hclaw
    H.toPauliCliqueHamiltonianRepresentation (Pi l) (fun x hx => h6 x hx l hl) l (h4 l hl) k

end SimplicialModeHamiltonian

end SimpleGraph
