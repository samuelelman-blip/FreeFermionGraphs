# FreeFermionGraphs

Lean 4 formalisation effort for the graph-theoretic results in
*A Unified Graph-Theoretic Framework for Free-Fermion Solvability* by Adrian
Chapman, Samuel J. Elman, and Ryan L. Mann (arXiv 2305.15625).

The checked-in development covers finite claw-free graph theory, hole
deformations, token sliding, and the Definition 19 obstruction search (with the
caveats recorded below), and, at operator level: the conserved charges of
Theorem 1(i) and 1(ii); Theorem 2 in complex matrix algebras, under two premises
beyond v1's setup (the hypothesis of Theorem 1(iii), and coprimality of the sector
polynomials in each occurring sector, below); Theorem 3 on a symmetry sector (for a
projector with explicit hypotheses, and over the joint spectral projectors of the cycle
symmetries under the hypothesis of Theorem 1(iii), below); and the anticommutator identity of
Corollary 1, with its corrected sign, for graphs without even holes and on a symmetry
sector. Theorem 1(iii) is not formalised, so Theorem 2 is not proved unconditionally.
For Corollary 1, the positive definiteness of `M` and the Majorana modes are not
formalised in any case.

Numbering. The documents in this repository use the numbering of a revised
manuscript (14 July 2026) that is not available. All checks against the source use
arXiv 2305.15625v1, which numbers lemmas, corollaries and definitions with separate
counters. The correspondence is in
[`docs/V1_NUMBERING.md`](docs/V1_NUMBERING.md); defects of v1 found during
formalisation are in [`docs/V1_ERRATA.md`](docs/V1_ERRATA.md). Below, "repo Lemma n"
is followed by "v1 Lemma m" where the numbers differ.

## Toolchain

The repository currently uses:

- Lean 4.32.0
- mathlib through Lake

Install Lean with `elan`, then build the complete project with:

```bash
lake update
lake build
```

Focused checks of the main layers:

```bash
lake build FreeFermionGraphs.TheoremOneI
lake build FreeFermionGraphs.TheoremOneII
lake build FreeFermionGraphs.Theorem3EvenHoleFree
lake build FreeFermionGraphs.Theorem3
lake build FreeFermionGraphs.CycleSymmetrySectors
lake build FreeFermionGraphs.CrossSectorRelations
lake build FreeFermionGraphs.FreeFermionSolution
lake build FreeFermionGraphs.KrylovAnticommutator
lake build FreeFermionGraphs.GeneralizedCharacteristicPolynomial
lake build FreeFermionGraphs.LadderAnticommutation
lake build FreeFermionGraphs.Lemma12Residual
lake build FreeFermionGraphs.Lemma17Paper
```

## Current proof status (2026-10-26)

Each declaration cited below as support is given with its full name (a few mentions in
prose and table descriptions use the short name of a declaration whose full name appears
elsewhere in this file); each cited declaration was checked to exist in the current build
and to depend only on `propext`, `Classical.choice`, `Quot.sound` (2026-10-26). The setup
of the operator-level theorems is: a finite vertex type, a representation of the Hamiltonian
terms (`SimpleGraph.PauliFrustrationRepresentation`: terms that anticommute exactly along
edges of the frustration graph and commute otherwise) in an arbitrary ring, and a claw-free
frustration graph.

### Theorem 1 (conserved charges)

- (i) proved, unconditionally:
  `SimpleGraph.PauliFrustrationRepresentation.paperTheorem1i`
  (`[q_{s,mu}, q_{t,nu}] = 0`), and `[H, q_{t,nu}] = 0` in
  `SimpleGraph.PauliFrustrationRepresentation.hamiltonian_commute_tokenSlidingChargeOp`.
- (ii) proved, unconditionally for an even hole `C_0`
  (`SimpleGraph.IsEvenHoleCarrier`):
  `SimpleGraph.PauliFrustrationRepresentation.paperTheorem1ii`
  (`[J_{C_0}, q_{s,mu}] = 0`), and
  `SimpleGraph.PauliFrustrationRepresentation.hamiltonian_commute_generalizedCycleSymmetryOp`
  (`[H, J_{C_0}] = 0`). v1 does not argue that its pairing of terms is an
  involution; the arguments are
  `SimpleGraph.untetheredSupports_toggle` (the set of untethered runs is stable
  under the toggle, including the cross-class case) and
  `SimpleGraph.EvenHoleLabeling.TetherPair.involutive` (the tether of a tether is the
  original initialiser), together with
  `SimpleGraph.EvenHoleLabeling.SetDeformationPath.tetheredTo_symm` and
  `SimpleGraph.EvenHoleLabeling.TetherPair.symm` (a tether differs from its initialiser,
  so the pairing has no fixed point).
- (iii) not yet. Groundwork: transport of `h_C` along a complete Definition 19
  deformation and along its reverse run
  (`SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.evenHoleOperator_mul_pairProduct`,
  `SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.pairProduct_mul_evenHoleOperator_of_reverseRun`,
  with non-vacuity on a two-step deformation in
  `SimpleGraph.HoleOperatorTransportExample.transport_nonvacuous`); the corrected
  residual form of Lemma 12 (below); the obstruction-graph arithmetic
  (`SimpleGraph.ArcGraph.exists_two_incoming`,
  `SimpleGraph.ArcGraph.odd_and_lt_after_removal`).

### Theorem 2 (free-fermion solution)

Proved in `Matrix (Fin d) (Fin d) ℂ`, conditional on Theorem 1(iii) and on coprimality of
the sector polynomials in each occurring sector (v1 Theorem 2, assembled from v1
Lemmas 13-15):
`SimpleGraph.SimplicialModeHamiltonian.freeFermionSolution_of_cycleSymmetry_commute`.
Setup: `H : G.SimplicialModeHamiltonian Ks (Matrix (Fin d) (Fin d) ℂ)` (Hermitian Pauli
terms and simplicial mode `chi`; `d` may include ancilla qubits), claw-free `G` (`hclaw`),
simplicial clique `Ks` (`hKs`). The `J_{C_0}` are the specific operators
`SimpleGraph.PauliFrustrationRepresentation.generalizedCycleSymmetryOp` of v1 Definition 15.
Premises beyond that setup, exactly two:

- `hJ : H.frustration.CycleSymmetriesCommute`, i.e. `[J_{C_0}, J_{C_1}] = 0` for all
  even-hole carriers `C_0`, `C_1`: v1 Theorem 1(iii), which is open (above). It is used only
  to produce the joint spectral projectors.
- `hND`: for every `l : G.EvenHoleDeformationClass → ℝ` that is a joint eigenvalue tuple of
  the `J`'s (some `v != 0` has `J_{C_0} v = l(<C_0>) v` for every even-hole carrier `C_0`,
  and `l = 0` on every class without an even-hole carrier), the sector polynomials
  `SimpleGraph.sectorPolynomial H.coupling {} l` and `SimpleGraph.sectorPolynomial H.coupling Ks l`
  are coprime in `ℝ[X]` (`IsCoprime`). Coprime real polynomials have no common complex root
  (`ModeSectorPositivity.aeval_ne_zero_of_isCoprime`); the converse needs the Fundamental
  Theorem of Algebra, which is an explicit hypothesis of
  `ModeSectorPositivity.isCoprime_of_forall_aeval_ne_zero` because Mathlib's analytic proof
  is not available in this build. v1 does not state the condition and uses its consequences
  silently. Without it v1's statement fails: hand computation of the `C_4` counterexample
  in `docs/V1_ERRATA.md`, U1 (not a Lean statement).

Conclusion. The objects are fixed by formulas, not chosen. A finite set `Lambda` of joint
eigenvalue tuples `l`, exactly those that occur, and Hermitian idempotents `Pi_l != 0`,
pairwise orthogonal, with `sum_l Pi_l = 1` and `J_{C_0} Pi_l = l(<C_0>) Pi_l`, each the
projector of a `ModeSector` with `zG = z_{{},l}` and `zK = z_{Ks,l}` (the sector polynomials
above). In each sector `l`: `r_l = deg z_{{},l}` distinct positive numbers `u_{l,j}` with
`z_{{},l} = prod_j (1 + x/u_{l,j}^2)`, `T(u) T(-u) Pi_l = 0` at `u = u_{l,j}`
(`Z_G(-u^2) Pi_l = 0`), and `z_{Ks,l}(-u^2) z_{{},l}'(-u^2) > 0` there; further
`N_{l,j} = 4 u_{l,j} sqrt(z_{Ks,l}(-u^2) z_{{},l}'(-u^2)) > 0`, `eps_{l,j} = 1/u_{l,j}` and
`psi_{l,j} = N_{l,j}^{-1} Pi_l T(-u_{l,j}) chi T(u_{l,j})`, and for all `l, l'` in `Lambda`:

- `Pi_l psi_{l',k} = psi_{l',k} Pi_l = delta_{l,l'} psi_{l',k}`, so `[Pi_l, psi_{l',k}] = 0`
  (v1's last display of Theorem 2), and `[Pi_l, psi_{l',k}^dagger] = 0` (stated as a
  commutation only);
- `{psi_{l,j}, psi_{l',k}^dagger} = delta_{l,l'} delta_{jk} Pi_l` (v1 Lemma 14), and
  `{psi, psi} = 0`, `{psi^dagger, psi^dagger} = 0` (not stated in v1), across and within sectors;
- `[H, psi_{l,j}] = 2 eps_{l,j} psi_{l,j}` and `[H, psi_{l,j}^dagger] = -2 eps_{l,j} psi_{l,j}^dagger`
  (v1 Lemma 13);
- `H = sum_l (sum_j eps_{l,j} [psi_{l,j}, psi_{l,j}^dagger]) Pi_l` (v1 Theorem 2 and Lemma 15).

Deviations from v1. The inner index runs over `Fin (r_l)` with `r_l = deg z_{{},l}`, not over
`1..alpha(G)`: v1 does not say that `deg Z_{G,J} = alpha(G)` in every sector; for `C_4` with
uniform couplings and `Ks` an edge, `z = 1 + 4x` in the sector `J = -1`, of degree
`1 < alpha(G) = 2` (hand computation, `docs/V1_ERRATA.md`, U1). The mode
`psi_{J,-j}`, never defined in v1, is `psi_{J,j}^dagger`. `eps = 1/u` uses `u > 0`, which v1 leaves
implicit. Nothing is claimed about commutation of `Pi_l` or of the modes with individual
terms `h_j`.

Non-vacuity. For the one-vertex model (`Ks = {0}`, `H = Z`, `chi = X`, no even hole, so every
`J` is `0`) all premises hold and the conclusion is computed: `Lambda = {0}`, `r = 1`,
`u = 1`, `psi = sigma^+`, `H = Z = [psi, psi^dagger]`, `[H, psi] = 2 psi`
(`SimpleGraph.FreeFermionSolutionExample.freeFermionSolution_ham1`; the cross-sector
statement: `SimpleGraph.CrossSectorRelationsExample.exists_crossSectorModes_ham1`). No
committed example verifies `hJ` and `hND` together with a non-trivial `J`: the 4-cycle model
below satisfies `hJ` and has two sectors, but fails `hND` in the sector `J = +1` by hand
computation.

Components:

- Fundamental Identity (repo Lemma 2 = v1 Lemma 12), without claw-freeness:
  `SimpleGraph.PauliFrustrationRepresentation.fundamentalIdentity`.
- Transfer operators: `SimpleGraph.PauliFrustrationRepresentation.transfer`;
  `SimpleGraph.PauliFrustrationRepresentation.transfer_commute` and
  `SimpleGraph.PauliFrustrationRepresentation.hamiltonian_commute_transfer` for claw-free `G`.
- The clique-deletion identity `Z_G = Z_{G \ Ks} - u^2 B(-u) B(u)` that v1 uses
  without proof in the ladder argument:
  `SimpleGraph.PauliFrustrationRepresentation.transfer_mul_transfer_neg_eq_deleted`,
  `SimpleGraph.PauliFrustrationRepresentation.root_sandwich_anticomm`.
- Generalized characteristic polynomial (repo Lemma 1 = v1 Lemma 11), in operator form
  over families of separated even holes, for any deleted carrier, with only
  claw-freeness assumed:
  `SimpleGraph.PauliCliqueHamiltonianRepresentation.generalizedCharacteristicPolynomial`
  (`W = {}` case: `SimpleGraph.PauliCliqueHamiltonianRepresentation.generalizedCharacteristicPolynomial_empty`).
- Sector form of `Z_G` and `Z_{G \ Ks}` (the regrouping of v1's last display of the
  Lemma 11 proof): for `W = {}` or `W = Ks` and an element `Pi` of the
  operator algebra with `J_{<C_0>} Pi = lambda_{<C_0>} Pi` for every even hole,
  `T_{G \ W}(u) T_{G \ W}(-u) Pi = z_{W,lambda}(-u^2) Pi`:
  `SimpleGraph.PauliCliqueHamiltonianRepresentation.transfer_mul_transfer_neg_mul_sector`
  (the polynomial is `SimpleGraph.sectorPolynomial`).
- Eigenmode lemma (repo Lemma 3 = v1 Lemma 13) and intertwining relation, on a
  `SimpleGraph.SimplicialModeHamiltonian.ModeSector` (the properties of the sector
  projector are explicit structure fields; for the joint projectors of the `J`'s they are
  discharged under the hypothesis of Theorem 1(iii), see below):
  `SimpleGraph.SimplicialModeHamiltonian.ModeSector.eigenmode`,
  `SimpleGraph.SimplicialModeHamiltonian.ModeSector.intertwine`.
- Ladder and canonical anticommutation relations (repo Lemma 4 = v1 Lemma 14),
  including `{psi^+, psi^+} = 0 = {psi^-, psi^-}`, which v1 does not state, on
  `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate` data:
  `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.ladder_plus_minus`,
  `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.ladder_plus_plus`,
  `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.ladder_minus_minus`.
- The commutator `[psi^+, psi^-]` in terms of `T` and `T'` (first half of repo Lemma 5
  = v1 Lemma 15):
  `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.commutator_plus_minus`;
  and the reconstruction on one sector by Lagrange interpolation,
  `H Pi = sum_j u_j^{-1} [psi_j^+, psi_j^-]`
  (`SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.hamiltonian_mul_Pi`,
  and `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.hamiltonian_mul_Pi_matrix`
  in matrix algebras with no further hypothesis). v1's last display of the proof
  has a sign slip: `T(0) T'(0) = -H`, not `H`, because `T'(0) = -Q^(1)`
  (`SimpleGraph.PauliFrustrationRepresentation.transferDeriv_zero`).
- What v1 uses without proof about the roots, in matrix algebras
  `Matrix (Fin d) (Fin d) ℂ`, from the single hypothesis that the sector polynomials
  `z_G`, `z_K` are coprime: roots are real and negative
  (`SimpleGraph.SimplicialModeHamiltonian.ModeSector.root_real_neg`), simple with positive
  radicand (`SimpleGraph.SimplicialModeHamiltonian.ModeSector.radicand_pos`), the charges
  above `deg z_G` vanish on the sector
  (`SimpleGraph.SimplicialModeHamiltonian.ModeSector.charge_mul_Pi_eq_zero`), and
  `Nondegenerate` data exists with `r = deg z_G`
  (`SimpleGraph.SimplicialModeHamiltonian.ModeSector.exists_nondegenerate_of_isCoprime`).
- Even holes against a simplicial clique (`|Ks n C| in {0, 2}`; the simplicial mode
  commutes with every `J`):
  `SimpleGraph.IsSimplicialClique.ncard_inter_evenHoleCarrier`,
  `SimpleGraph.PauliFrustrationRepresentation.root_commute_cycleSymmetry`.
- Joint spectral projections of commuting Hermitian matrices: `exists_joint_spectral_projections`.
- The sectors of Theorem 2, conditional on Theorem 1(iii). In `Matrix (Fin d) (Fin d) ℂ`,
  for claw-free `G` and a simplicial clique `Ks`, from the explicit hypothesis
  `H.frustration.CycleSymmetriesCommute` (`[J_{C_0}, J_{C_1}] = 0` for even-hole carriers,
  i.e. Theorem 1(iii)),
  `SimpleGraph.SimplicialModeHamiltonian.exists_modeSectors_of_cycleSymmetry_commute`
  builds a finite set `Lambda` of tuples `l` and Hermitian idempotents `Pi_l != 0`,
  pairwise orthogonal, with `sum_l Pi_l = 1` and `J_{<C_0>} Pi_l = l(<C_0>) Pi_l`, and for
  each `l` a `SimpleGraph.SimplicialModeHamiltonian.ModeSector` with projector `Pi_l`,
  `zG = SimpleGraph.sectorPolynomial H.coupling {} l` and
  `zK = SimpleGraph.sectorPolynomial H.coupling Ks l`
  (via `SimpleGraph.SimplicialModeHamiltonian.jointModeSector` and
  `SimpleGraph.PauliFrustrationRepresentation.exists_jointSpectralProjections_of_cycleSymmetry_commute`).
  The hypothesis is `SimpleGraph.PauliFrustrationRepresentation.CycleSymmetriesCommute`;
  Theorem 1(iii) itself is open. The hypotheses of this construction (not `hND`) hold, with
  `J` acting non-trivially and two sectors `J = +-1`, on a three-qubit model with
  frustration graph the 4-cycle:
  `SimpleGraph.CycleSymmetrySectorsExample.ham_cycleSymmetriesCommute`,
  `SimpleGraph.CycleSymmetrySectorsExample.exists_two_sectors`. The same projectors `Pi_l`
  satisfy the identity of Theorem 3 (below),
  `SimpleGraph.SimplicialModeHamiltonian.paperTheorem3_modeSectors_of_cycleSymmetry_commute`.
- Cross-sector relations, conditional on `hJ` and `hND` (the premises above):
  `SimpleGraph.SimplicialModeHamiltonian.exists_crossSectorModes_of_cycleSymmetry_commute`
  gives the sectors `Pi_l`, the `r_l = deg z_{{},l}` roots `u_{l,j}` with their
  non-degeneracy facts, the explicit modes
  `psi_{l,j} = SimpleGraph.SimplicialModeHamiltonian.explicitIncognitoMode H (Pi_l) z_{{},l} z_{Ks,l} u_{l,j}`,
  and the commutation with `Pi_l` and the canonical anticommutation relations for all
  pairs of sectors. The cross-sector relations use only orthogonality of the sectors
  (`Pi_S Pi_{S'} = 0`, `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Orthogonal`), no
  claw-freeness, and the non-degeneracy data only supplies the modes:
  `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Orthogonal.commute_psiPlus`,
  `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Orthogonal.psiPlus_anticomm_psiMinus`.
  For any family of pairwise orthogonal sectors with non-degeneracy data (and `hclaw`, `hKs`),
  `{psi_{l,j}, psi_{l',k}^dagger} = delta_{l,l'} delta_{jk} Pi_l` is
  `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Family.psi_anticomm_star_psi`.
- The eigenmode relations and the reconstruction in one sector, from raw non-degeneracy data
  (distinct positive `u_j`, `z_G = prod_j (1 + x/u_j^2)`, positive radicands) and the
  explicit modes: `SimpleGraph.SimplicialModeHamiltonian.ModeSector.solution_on_sector`
  (`[H, psi_j] = 2 u_j^{-1} psi_j`, `[H, psi_j^dagger] = -2 u_j^{-1} psi_j^dagger`,
  `H Pi = sum_j u_j^{-1} [psi_j, psi_j^dagger]`), via
  `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.commutator_psiPlus` and
  `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.commutator_psiMinus`.
  The sum over sectors, `H = H sum_l Pi_l = sum_l (H Pi_l) Pi_l`, is the last step of
  `SimpleGraph.SimplicialModeHamiltonian.freeFermionSolution_of_cycleSymmetry_commute`.
- Repo Lemma 17 = v1 Lemma 18, the charge recursion over a simplicial clique:
  `SimpleGraph.PauliFrustrationRepresentation.paperLemma17`.

Not yet: Theorem 1(iii) (the hypothesis `SimpleGraph.PauliFrustrationRepresentation.CycleSymmetriesCommute` above), the only premise of
the result whose discharge is missing. `hND` is not something to discharge: v1's Theorem 2
as printed needs it (no common root of `Z_{G,J}` and `Z_{G \ Ks,J}` in each sector;
`docs/V1_ERRATA.md`, U1 and E16), so the target is a qualified statement, which is the
result above once Theorem 1(iii) is proved. Algebras other than `Matrix (Fin d) (Fin d) ℂ`
are not covered (the proofs use the Hilbert-Schmidt trace form, `docs/V1_ERRATA.md`, E16).

### Theorem 3 and Corollary 1 (Krylov construction)

For finite claw-free graphs with a simplicial clique and no even hole (then there are
no generalized cycle symmetries and the sector projector is `1`):

- Theorem 3 in the concrete form `[H, .]^k chi = (-2)^k sum_P (T^k)_{{j*},P} h_P`
  with `T` the clique-rooted tree matrix:
  `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_evenHoleFree`;
  and in v1's existential form (a real directed bipartite matrix, `ad = [iH, .]`):
  `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_evenHoleFree_exists`.
- The anticommutator identity of Corollary 1 (`{ad^j chi, ad^k chi} = 2 M_jk`) with the
  corrected sign `M_jk = (-1)^j (-2i)^{j+k} (A^{j+k})_{j*j*}`, with `chi^2 = 1` as a
  hypothesis (`hχ`: `H.rootOperator * H.rootOperator = 1`):
  `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_evenHoleFree`,
  `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_evenHoleFree_ad`.
  The printed formula lacks `(-1)^j`; the smallest counterexample is checked in
  `KrylovAnticommutator.printedCorollary1_fails_single_vertex`.
- The deformation-closure lemma for induced paths (repo Lemma 18 = v1 Lemma 16):
  `SimpleGraph.paperDeformationClosureLemma_of_evenHoleFree`.

For the general (sector) case, done: the corrected matrix of Eq. (decoratedtree) with
root-handle arcs, hoop sign `(-1)^{k-1}` and per-event normalisation
(`SimpleGraph.cliqueHoppingMatrix`, `SimpleGraph.cliqueHoppingMatrix_hoop`), the even-hoop
operator identity `h_P h_j = (-1)^{k-1} h_{P_s} h_C`
(`SimpleGraph.PauliCliqueHamiltonianRepresentation.pathOperator_mul_bubble_eq_holeOperator`),
attachment uniformity of a deformation class at a handle
(`SimpleGraph.RootedInducedPath.holeAttached_of_closure`,
`SimpleGraph.card_evenHoopEvents`), the corrected normalisation
(`SimpleGraph.half_sum_inv_eventNormalisation_of_attached`), `[H, J_{C_0}] = 0` (above),
and the closed form of the Krylov rows with hole terms for any number of hole classes,
`(sum_n X^n (A^n)_{{j*},Q}) Z_V = X^{|Q|-1} Z_{V \ N(Q)}`, where `Z_U` is
`SimpleGraph.sectorIndepSeries`: the sum, over families of pairwise compatible even holes
inside `U` (compatibility of v1 L313), of the product of the hole weights
`2 (-X^2)^{|C|/2} lambda_{<C>} / |<C>|` times the weighted independence series of the
vertices of `U` outside the family's closed neighbourhood
(`SimpleGraph.krylovRow_mul_sectorIndepSeries`). That `Z_U` is the sector reduction
(`J_c -> lambda_c`) of the generalized characteristic polynomial of `G[U]` is not
machine-checked: no theorem relates `SimpleGraph.sectorIndepSeries` to `SimpleGraph.sectorPolynomial`
or to `SimpleGraph.PauliCliqueHamiltonianRepresentation.generalizedCharacteristicPolynomial`, and the docstring of `SimpleGraph.sectorIndepSeries`
allows that reading only when `U` contains all or none of the holes of each deformation
class and `|<C>|` is invertible in the field. The closed form gives that the rows are
constant on deformation closures and wand reversals
(`SimpleGraph.sectorRow_pow_eq_of_closure`, `SimpleGraph.sectorRow_pow_wandReverse`:
v1 Lemma 16 and Eq. (pathcircle) for the corrected matrix with even holes). In v1's form,
for the corrected matrix and the hypotheses of v1's setup (finite claw-free graph,
simplicial clique, arbitrary `lambda`; `(A^k)_{{j*},P} = (A^k)_{{j*},P'}` for `|P| >= 3`
and `P'` in the deformation closure of `P`): `SimpleGraph.paperLemma18`, and
`SimpleGraph.paperLemma18_of_deformationStep` for a single-vertex deformation. With the
printed normalisation of Eq. (decoratedtree) (`(1/2) sum_{P'} N^{-1}_{P,P',<C_0>} = 1`,
read literally as a fixed source `P` and a sum over its targets,
`SimpleGraph.IsPrintedNormalisation`) the lemma is false, checked in the kernel on a 7-vertex
claw-free graph with `K = {2, 5}`: for unit couplings and `lambda = 1`,
`(A^6)_{{j*},P} = 42` and `(A^6)_{{j*},P'} = 40` for a single-vertex deformation `P'` of `P`
(`SimpleGraph.PrintedNormalisation.Example.printed_normalisation_counterexample`), and
`428` against `422` for `b^2 = (4, 4, 1, 3, 5, 4, 4)`, `lambda = 3`
(`SimpleGraph.PrintedNormalisation.Example.printed_pow_six_package`). Not machine-checked:
that the printed sentence means `SimpleGraph.IsPrintedNormalisation`, and that the example is a smallest one.

Theorem 3 on a symmetry sector is proved. For a finite claw-free graph `G`, a simplicial
clique `K`, and any `Pr` with `[H, Pr] = 0` and `J_c Pr = lambda_c Pr` for every
even-hole class `c`,
`[H, .]^k chi * Pr = (-2)^k sum_P ((A_lambda^k)_{{j*},P}) h_P Pr`, with `A_lambda` the
corrected matrix `SimpleGraph.cliqueHoppingMatrix`:
`SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_commute`
(`Pr^2 = Pr` is not assumed). For `Pr` in the subalgebra generated by the `J_c`, the
commutation `[H, Pr] = 0` is discharged by Theorem 1(ii)
(`SimpleGraph.PauliCliqueHamiltonianRepresentation.commute_physicalHamiltonian_of_mem_adjoin`):
`SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_cycleAlgebra`. The
existential form of v1 over `ℝ` (a real directed bipartite matrix, `ad = [iH, .]`) is
`SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_commute_exists`. The
names stay qualified: v1 takes `Pr = Pi_J`, the joint spectral projector of the `J_c`,
and the unqualified `paperTheorem3` is not exported.

Over the joint spectral projectors themselves, conditional on Theorem 1(iii) as the only
premise beyond v1's setup:
`SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_cycleSymmetry_commute`.
Setup: `H : G.PauliCliqueHamiltonianRepresentation K ℝ (Matrix (Fin d) (Fin d) ℂ)` with
Hermitian Pauli terms (`hstar`), claw-free `G` (`hclaw`), simplicial clique `K` (`hK`);
premise `hJ : H.operator.restrictSome.CycleSymmetriesCommute`. Conclusion: the joint spectral
decomposition `(Lambda, Pi_l)` of
`SimpleGraph.PauliFrustrationRepresentation.exists_jointSpectralProjections_of_cycleSymmetry_commute`
and, for every `l` in `Lambda`, the real matrix `A_l = SimpleGraph.cliqueHoppingMatrix`, whose
nonzero entries `(P, Q)` have `|P| + |Q|` odd (bipartite), such that for all `k`, with
`ad_{iH} = [iH, .]`, `Pi_l` commutes with `ad_{iH}^k chi` and
`Pi_l ad_{iH}^k chi = ad_{iH}^k chi Pi_l = sum_P ((-2i)^k (A_l^k)_{{j*},P}) h_P Pi_l`. The
`Pi_l` of the same statement are the projectors of the `ModeSector`s of Theorem 2:
`SimpleGraph.SimplicialModeHamiltonian.paperTheorem3_modeSectors_of_cycleSymmetry_commute`.
The statement is derived from Theorem 3 for any `Pr` in the bicommutant of the `J_c` with
`J_c Pr = lambda_c Pr`, over `ℝ`, in which `[H, Pr] = 0` (Theorem 1(ii)) and `[chi, Pr] = 0`
(`chi` commutes with the `J_c`) are derived rather than assumed:
`SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_bicommutant`. Non-vacuity,
with `J` acting non-trivially, two sectors `J = +-1`, and the left side not zero at `k = 1`:
`SimpleGraph.Theorem3SectorsExample.theorem3_two_sectors` (the three-qubit 4-cycle model).

Corollary 1 on a symmetry sector (the anticommutator identity only). For a finite claw-free
graph `G`, a simplicial clique `K`, `chi^2 = 1` (`hχ`) and any `Pr` with `[H, Pr] = 0`,
`[chi, Pr] = 0` and `J_c Pr = lambda_c Pr` for every even-hole class `c`,
`{ad_H^j chi, ad_H^k chi} Pr = 2 (-1)^j (-2)^{j+k} ((A_lambda^{j+k})_{{j*},{j*}}) Pr` with
`ad_H = [H, .]` and `A_lambda = SimpleGraph.cliqueHoppingMatrix`:
`SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_commute` (with `Pr` on
the left, v1's `Pi {.,.} = 2 M Pi`: `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_commute_left`; the manuscript
convention `ad = [iH, .]`, with `M_jk = (-1)^j (-2i)^{j+k} (A_lambda^{j+k})_{{j*},{j*}}`:
`SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_commute_ad`; all in the same namespace). For `Pr` in the subalgebra
generated by the `J_c`, `[H, Pr] = 0` is Theorem 1(ii) and `[chi, Pr] = 0` is the commutation
of `chi` with the `J_c`
(`SimpleGraph.PauliCliqueHamiltonianRepresentation.commute_rootOperator_of_mem_adjoin`):
`SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_cycleAlgebra`, `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_cycleAlgebra_left`,
`SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_cycleAlgebra_ad`. The existential form of v1's statement, with a real
symmetric matrix `M` whose entries are the corrected `M_jk`: `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_commute_exists`,
`SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_cycleAlgebra_exists` (odd powers of `A_lambda` vanish at the root,
`SimpleGraph.cliqueHoppingMatrix_pow_cliqueRootPath_eq_zero_of_odd`). The names stay
qualified for the reason given for Theorem 3 (v1 takes `Pr = Pi_J`) and because `chi^2 = 1`
is a hypothesis. Not formalised, on a sector or without even holes alike: the positive
definiteness of `M` and the Majorana modes (v1 L1394-1430), which follow the proof of v1
Corollary 12.

### Downgrades from machine-checked audits

These audits (`docs/PAPER_FIDELITY.md`, "Audit 2026-10-26") prove properties of
repository interfaces. They do not show that any manuscript statement is false.

- Lemma 12 (repo; v1 Lemma 7) and Lemma 16 (repo; v1 Lemma 10). The data
  `SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.Lemma12Definition19Data`
  and `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.PaperLemma16Trace`
  are uninhabited on claw-free graphs
  (`SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.not_nonempty_lemma12Data_of_clawFree`,
  `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.not_nonempty_paperLemma16Trace_of_clawFree`),
  so `SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.lemma12` and
  `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.PaperLemma16Trace.paperLemma16`
  are vacuous. The endpoint clause quantified over every `C'`-neighbour of the last
  removed vertex; v1 uses only those not adjacent to the introduced vertex. The
  corrected residual form is `SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.Lemma12ResidualData`,
  with Lemma 12 and its carrier export proved on it
  (`SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.lemma12_of_residualData`,
  `SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.lemma12_carrier_of_residualData`),
  non-vacuous on a claw-free two-step palindromic instance
  (`SimpleGraph.exists_lemma12ResidualData_with_criterion`). The residual data is a
  supplied certificate; no corrected Lemma 16 is in the repository.
- Lemma 15 (repo; v1 Lemma 9). The rerouting transition is uninhabited
  (`SimpleGraph.FixedPairingPathFamily.ObstructionSearchReroutingTransition.isEmpty`),
  every process has `stepCount = 0`
  (`SimpleGraph.FixedPairingPathFamily.ObstructionSearchReroutingProcess.stepCount_eq_zero`),
  so `SimpleGraph.FixedPairingPathFamily.ObstructionSearchReroutingProcess.paperLemma15`
  is Lemma 14 at state 0.
- Definition 19 trace types. The interface field `SimpleGraph.FixedPairingPathFamily.ACHoleStepGeometry.before_subset` is
  false in v1 after the first step. As a result every `FiniteMixedSideSearchTrace` has
  one block with one step
  (`SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.blockCount_eq_one`,
  `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.flattened_stepCount_eq_one`),
  and the positive-history types of Lemma 11 are empty
  (`SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FullDefinition19Lemma11AHistoryData.isEmpty`).
  Lemmas 11, 14, 15 and 16 on these types therefore cover single-step runs only.
  `SimpleGraph.FixedPairingPathFamily.ObstructionSearchInitialization.InitializationFiniteMixedSideLemma14History.paperLemma14`
  is a proved theorem on that degenerate interface, not an exact formalisation of v1
  Lemma 8.
- Corrected statements. Lemma 8 (repo; v1 Lemma 3) is formalised with the premise
  `t not in {s} u C` that the printed statement omits
  (`SimpleGraph.EvenHoleLabeling.CloneAt.lemma8`). Corollary 6 (repo; v1 Corollary 5)
  is stated in the repository for the compatibility notion of v1 L748; the notion of
  v1 L313 is different (`SimpleGraph.exists_evenHoleInducedCompatible_not_evenHoleCompatible`)
  and Corollary 6 holds for it too (`SimpleGraph.corollary6_induced`).

## Fidelity audit

Result-by-result audits are recorded, in order, in
[`docs/PAPER_FIDELITY_AUDIT_2026-08-05.md`](docs/PAPER_FIDELITY_AUDIT_2026-08-05.md)
(14 July 2026 manuscript, historical) and the section "Audit 2026-10-26" of
[`docs/PAPER_FIDELITY.md`](docs/PAPER_FIDELITY.md) (current). Where they conflict, the
latter governs. The Lean terms are internally checked; the status table distinguishes
exact endpoints from conditional, corrected, degenerate and representation-level
ones.

| Manuscript layer (repo / v1) | Status | Supporting declaration |
|---|---|---|
| Lemma 6 / v1 Lemma 1 | Exact for the finite graph setting | `SimpleGraph.lemma6` |
| Lemma 7 / v1 Lemma 2; Corollaries 2-3 / v1 Corollaries 1-2 | Exact indexed path/hole statements | `SimpleGraph.IndexedInducedHole.lemma7`, `SimpleGraph.IndexedInducedPath.lemma7`, `SimpleGraph.IndexedInducedHole.corollary2`, `SimpleGraph.IsClawFree.corollary3` |
| Lemma 8 / v1 Lemma 3; Corollaries 4-5 / v1 Corollaries 3-4 | Corrected forms with the premise `t not in {s} u C` | `SimpleGraph.EvenHoleLabeling.CloneAt.lemma8`, `SimpleGraph.EvenHoleLabeling.CloneAt.corollary4`, `SimpleGraph.EvenHoleLabeling.CloneAt.corollary5` |
| Lemma 9 / v1 Lemma 4 | Exact deformation-closure statement | `SimpleGraph.lemma9` |
| Corollary 6 / v1 Corollary 5 | Exact for both compatibility notions | `SimpleGraph.corollary6`, `SimpleGraph.corollary6_induced` |
| Lemma 10 / v1 Lemma 5 | Statement on the `FixedPairingPathFamily` interface; disjointness is carried by its fields | `SimpleGraph.FixedPairingPathFamily.lemma10` |
| Corollaries 7-10 / v1 Corollaries 6-9 | Conditional or occurrence-erasing cores; exact ordered-path wrappers remain | `SimpleGraph.FixedPairingPathFamily.corollary7`, `SimpleGraph.FixedPairingPathFamily.corollary8`, `SimpleGraph.FixedPairingPathFamily.corollary9`, `SimpleGraph.FixedPairingPathFamily.corollary10` |
| Lemma 11 / v1 Lemma 6; Corollaries 11-12 / v1 Corollaries 10-11 | Single-step runs only on the finite trace types; multi-block history types empty | `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.blockCount_eq_one`, `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FullDefinition19Lemma11AHistoryData.isEmpty` |
| Lemma 12 / v1 Lemma 7 | `lemma12` vacuous on claw-free graphs; corrected `lemma12_of_residualData` conditional on supplied residual data | `SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.not_nonempty_lemma12Data_of_clawFree`, `SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.lemma12_of_residualData` |
| Lemma 13 / v1 Lemma 17 | Exact at the `FullDefinition19Deformation` interface; hypotheses satisfied by a two-step deformation | `SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.lemma13`, `SimpleGraph.Lemma12ResidualExample.criterion` |
| Lemma 14 / v1 Lemma 8 | Proved on one-block, one-step histories only | `SimpleGraph.FixedPairingPathFamily.ObstructionSearchInitialization.InitializationFiniteMixedSideLemma14History.paperLemma14` |
| Lemma 15 / v1 Lemma 9 | Collapses to Lemma 14 at state 0 (transition uninhabited) | `SimpleGraph.FixedPairingPathFamily.ObstructionSearchReroutingTransition.isEmpty` |
| Lemma 16 / v1 Lemma 10 | Vacuous on claw-free graphs | `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.not_nonempty_paperLemma16Trace_of_clawFree` |
| Lemma 17 / v1 Lemma 18 | Exact charge recursion at the Pauli/frustration-graph boundary | `SimpleGraph.PauliFrustrationRepresentation.paperLemma17` |
| Lemma 18 / v1 Lemma 16 | Proved for the printed matrix without even holes; for the corrected matrix with even holes, any number of classes (`SimpleGraph.paperLemma18`, v1's hypotheses); false for the literal printed normalisation with even holes (kernel-checked counterexample) | `SimpleGraph.paperDeformationClosureLemma_of_evenHoleFree`, `SimpleGraph.sectorRow_pow_eq_of_closure`, `SimpleGraph.paperLemma18`, `SimpleGraph.PrintedNormalisation.Example.printed_normalisation_counterexample` |
| Lemma 1 / v1 Lemma 11 | Operator form over hole families, any deleted carrier; sector form `T(u) T(-u) Pi = z(-u^2) Pi` for `W = {}` or `W = Ks` | `SimpleGraph.PauliCliqueHamiltonianRepresentation.generalizedCharacteristicPolynomial`, `SimpleGraph.PauliCliqueHamiltonianRepresentation.transfer_mul_transfer_neg_mul_sector` |
| Lemma 2 / v1 Lemma 12 | Exact | `SimpleGraph.PauliFrustrationRepresentation.fundamentalIdentity` |
| Lemma 3 / v1 Lemma 13 | On a `ModeSector` (class B data); no unqualified paper theorem | `SimpleGraph.SimplicialModeHamiltonian.ModeSector.eigenmode` |
| Lemma 4 / v1 Lemma 14 | On `Nondegenerate` data (class B), which exists in matrix algebras when `z_G`, `z_K` are coprime; no unqualified paper theorem | `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.ladder_plus_minus`, `SimpleGraph.SimplicialModeHamiltonian.ModeSector.exists_nondegenerate_of_isCoprime` |
| Lemma 5 / v1 Lemma 15 | One sector: `H Pi = sum_j u_j^{-1} [psi_j^+, psi_j^-]`; the sum over sectors, `H = sum_l (sum_j eps_{l,j} [psi_{l,j}, psi_{l,j}^dagger]) Pi_l`, only under `hJ` and `hND` (Theorem 2 row) | `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.hamiltonian_mul_Pi_matrix`, `SimpleGraph.SimplicialModeHamiltonian.ModeSector.solution_on_sector` |
| Theorem 1(i) | Proved, unconditional | `SimpleGraph.PauliFrustrationRepresentation.paperTheorem1i` |
| Theorem 1(ii) | Proved, unconditional | `SimpleGraph.PauliFrustrationRepresentation.paperTheorem1ii` |
| Theorem 1(iii) | Not yet; groundwork only | `SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.evenHoleOperator_mul_pairProduct` |
| Theorem 2 | Proved in `Matrix (Fin d) (Fin d) ℂ` with two premises beyond v1's setup: `hJ : H.frustration.CycleSymmetriesCommute` (Theorem 1(iii), open) and `hND` (per occurring joint eigenvalue tuple `l`, `z_{{},l}` and `z_{Ks,l}` coprime; v1 omits it; its printed statement fails in the `C_4` example, a hand computation, `docs/V1_ERRATA.md` U1). Projectors `Pi_l`, `r_l = deg z_{{},l}` modes per sector (not `alpha(G)`), explicit `N`, `eps = 1/u`, `psi`; `[Pi_l, psi_{l',k}] = 0`; canonical anticommutation relations across sectors; `[H, psi] = 2 eps psi`; `H = sum_l (sum_j eps [psi, psi^dagger]) Pi_l`. Name carries `_of_cycleSymmetry_commute`; committed non-vacuity check of all premises: a one-vertex model without even holes | `SimpleGraph.SimplicialModeHamiltonian.freeFermionSolution_of_cycleSymmetry_commute`, `SimpleGraph.SimplicialModeHamiltonian.exists_crossSectorModes_of_cycleSymmetry_commute`, `SimpleGraph.SimplicialModeHamiltonian.exists_modeSectors_of_cycleSymmetry_commute`, `SimpleGraph.FreeFermionSolutionExample.freeFermionSolution_ham1` |
| Theorem 3 | Proved on a symmetry sector for any `Pr` with `[H, Pr] = 0` and `J_c Pr = lambda_c Pr` (name qualified: v1 takes `Pr = Pi_J`); `[H, Pr] = 0` discharged for `Pr` in the algebra generated by the `J_c`; existential form over `ℝ`; without even holes, `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_evenHoleFree`. Over the joint spectral projectors `Pi_l` themselves (also as the projectors of the `ModeSector`s), with `hJ` (Theorem 1(iii), open) as the only premise beyond v1's setup | `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_cycleSymmetry_commute`, `SimpleGraph.SimplicialModeHamiltonian.paperTheorem3_modeSectors_of_cycleSymmetry_commute`, `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_commute`, `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_cycleAlgebra`, `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_commute_exists`, `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_evenHoleFree` |
| Corollary 1 | The anticommutator identity `{ad^j chi, ad^k chi} = 2 M_jk` (corrected sign, `chi^2 = 1` a hypothesis) is proved without even holes, and on a symmetry sector for any `Pr` with `[H, Pr] = 0`, `[chi, Pr] = 0`, `J_c Pr = lambda_c Pr` (name qualified: v1 takes `Pr = Pi_J`), with `Pr` in the algebra generated by the `J_c` discharging the first two, and in an existential form with a real symmetric `M`; positive definiteness of `M` and the Majorana modes: not formalised, in any case | `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_evenHoleFree`, `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_commute`, `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_cycleAlgebra`, `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_cycleAlgebra_exists` |

The next critical path is open work. No declaration covers steps 1-4 (groundwork for
them is in the Theorem 1(iii) row above); steps 5 and 6 name what is already done:

1. Rebuild the Definition 19 layer so that multi-step, multi-block runs are
   representable: assert `before_subset` only at the first step of the first block and
   derive the colour data of later holes from the history; then construct the Lemma 11
   block data from a literal Definition 19 object built from `(C, C', W)`.
2. Derive `Lemma12ResidualData` from `(C, C', W)` and prove a corrected Lemma 16 on a
   residual-endpoint trace.
3. Rebuild the corrective rerouting on an obstruction-search relation that can start
   from a nonempty prefix (Lemma 15); resolve the deleted-source gap in Eq. (C31); prove
   existence, progress and termination of the search and the oddness of `|W n dO|`.
4. Choose the palindromic partner involutively and assemble Theorem 1(iii) from the
   transport identities.
5. Theorem 2, qualified by the no-common-root hypothesis `hND`. Done, conditional on
   `SimpleGraph.PauliFrustrationRepresentation.CycleSymmetriesCommute` and `hND`: the
   sectors, the roots, the explicit modes, the relations and the sum over sectors
   (`SimpleGraph.SimplicialModeHamiltonian.freeFermionSolution_of_cycleSymmetry_commute`).
   Open: discharge the first hypothesis (Theorem 1(iii), steps 1-4); `hND` stays a premise of
   the qualified statement.
6. Corollary 1. Done: the anticommutator identity `{ad^j chi, ad^k chi} = 2 M_jk` without
   even holes
   (`SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_evenHoleFree`) and
   on a sector, `Pr {ad^j chi, ad^k chi} = 2 M_jk Pr`
   (`SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_commute`,
   `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_cycleAlgebra`).
   Open in every case, with or without even holes: the positive definiteness of `M` and the
   Majorana modes (v1 L1394-1430); no declaration constructs the modes.

## Manuscript fidelity policy

A successful `lake build` proves that the Lean terms typecheck. It does not by
itself establish that a theorem has the same hypotheses, quantifiers, deformation
stage, and conclusion as the manuscript.

Paper-facing results are therefore gated by
[`docs/PAPER_FIDELITY.md`](docs/PAPER_FIDELITY.md). In particular:

- every manuscript object must be matched to a Lean object;
- hole stages and degree expressions must be explicit;
- additional premises must be documented in theorem names and docstrings;
- boundary certificates may not appear in an unqualified paper theorem;
- an unqualified paper theorem must have no additional premise beyond the
  manuscript setup;
- any remaining constructor or provenance boundary must be recorded explicitly;
- every status claim in the documents must name the Lean declaration that supports
  it.

For nondeterministic manuscript algorithms, an explicit finite execution history is
part of the setup only when its type is inhabited by genuine multi-step runs. The audits
above show that the current types are not: Lemma 14 histories have one block and one step,
the Lemma 15 transition has no instances, and the Lemma 16 trace has no instances on
claw-free graphs.

For Lemma 17 (v1 Lemma 18), the paper-facing Pauli representation does not accept an
independent-product coherence certificate. The product over an independent set and
its insertion laws are derived from pairwise commutation
(`docs/LEMMA17_FIDELITY.md`).

## Repository layout

- `FreeFermionGraphs/`: individual definitions, lemmas, and integration modules
- `FreeFermionGraphs.lean`: root import for the complete development
- `FORMALIZATION.md`: dependency-oriented proof plan with current status
- `docs/PAPER_FIDELITY.md`: current manuscript correspondence, the audit of
  2026-10-26, and open proof boundaries
- `docs/V1_NUMBERING.md`: correspondence between the numbering used here and that of
  arXiv 2305.15625v1
- `docs/V1_ERRATA.md`: defects of v1 found during formalisation, separated into those
  certified in Lean and those identified but not certified
- `docs/LEMMA17_FIDELITY.md`: detailed paper-facing provenance for Lemma 17 (v1 Lemma 18)
- `docs/PAPER_FIDELITY_AUDIT_2026-08-05.md`: result-by-result historical audit
- `docs/PAPER_AUDIT_2026-08-01.md`: historical audit at the PR #196 baseline
- `docs/LEMMA18_PLAN.md`: historical plan for Lemma 18 (v1 Lemma 16); superseded for the
  matrix of Eq. (E1) by `SimpleGraph.cliqueHoppingMatrix` and `SimpleGraph.paperLemma18`

## Development workflow

Every pull request touching a numbered manuscript result should be validated
with both a focused module build and the full project build:

```bash
lake build FreeFermionGraphs.<ModuleName>
lake build
```

A pull request should not be merged until the exact head has passed the
corresponding validation gate.
