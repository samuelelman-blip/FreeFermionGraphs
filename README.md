# FreeFermionGraphs

Lean 4 formalisation effort for the graph-theoretic results in
*A Unified Graph-Theoretic Framework for Free-Fermion Solvability* by Adrian
Chapman, Samuel J. Elman, and Ryan L. Mann (arXiv 2305.15625).

The checked-in development covers finite claw-free graph theory, hole
deformations, token sliding, and the Definition 19 obstruction search (with the
caveats recorded below), and, at operator level: Theorem 1(i)-(iii), the conserved
charges and the generalized cycle symmetries, with no premise beyond claw-freeness
(`paperTheorem1i`, `paperTheorem1ii`, `paperTheorem1iii`); Theorem 2 in complex matrix
algebras, with one premise beyond v1's setup, coprimality of the sector polynomials in
each occurring sector, which v1 uses silently and without which its printed statement fails
(hand computation, below; `paperTheorem2_of_sectorCoprime`); Theorem 3 over the joint eigenspaces of the cycle
symmetries, with no premise beyond v1's setup and with the corrected decorated-tree matrix
(`paperTheorem3`), and for graphs without even holes (`paperTheorem3_of_evenHoleFree`); and the
anticommutator identity of Corollary 1, with its corrected sign, over the joint eigenprojectors
of the cycle symmetries (`paperCorollary1`; premises claw-free, simplicial clique, Hermitian
terms, `chi^2 = 1`), on a symmetry sector and for graphs without even holes
(`paperCorollary1_of_cycleAlgebra`, `paperCorollary1_of_evenHoleFree`); Lemma 1 (v1 Lemma 11)
for a bare scaled representation with claw-freeness as the only hypothesis
(`ScaledPauliFrustrationRepresentation.generalizedCharacteristicPolynomial`). Theorem 1(iii) is proved by a route that replaces v1's
obstruction search (below, `docs/V1_ERRATA.md` E18). The Definition 19 layer built for the
obstruction search is audited as degenerate (below) and is not used by the results above.
For Corollary 1, the positive definiteness of `M` and the Majorana modes are not formalised.
Non-vacuity witnesses with real content are committed for Theorem 1(i)-(iii), Theorem 2 and
Corollary 1 (below). Open fidelity items are collected at the end
of the status section.

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
lake build FreeFermionGraphs.TheoremOneIII
lake build FreeFermionGraphs.TheoremOneIIIConsequences
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

## Current proof status (2026-11-03)

Each declaration cited below as support is given with its full name (a few mentions in
prose and table descriptions use the short name of a declaration whose full name appears
elsewhere in this file); each cited declaration was checked to exist in the current build
and to depend only on `propext`, `Classical.choice`, `Quot.sound` (2026-11-03). The setup
of the operator-level theorems is: a finite vertex type, a representation of the Hamiltonian
terms (`SimpleGraph.PauliFrustrationRepresentation`: terms that anticommute exactly along
edges of the frustration graph and commute otherwise) in an arbitrary ring, and a claw-free
frustration graph.

### Theorem 1 (conserved charges)

All three parts are proved, with no premise beyond the setup above (and, for (ii) and (iii),
the operators `J_{C_0}` being taken for even-hole carriers, since v1 defines them only for
even holes). The ring is arbitrary; no relation `h_j^2 = b_j^2` and no invertibility of 2 is
used.

- (i) `SimpleGraph.PauliFrustrationRepresentation.paperTheorem1i`
  (`[q_{s,mu}, q_{t,nu}] = 0`), and `[H, q_{t,nu}] = 0` in
  `SimpleGraph.PauliFrustrationRepresentation.hamiltonian_commute_tokenSlidingChargeOp`.
- (ii) `SimpleGraph.PauliFrustrationRepresentation.paperTheorem1ii`
  (`[J_{C_0}, q_{s,mu}] = 0`, `C_0` an even-hole carrier,
  `SimpleGraph.IsEvenHoleCarrier`), and
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
- (iii) `SimpleGraph.PauliFrustrationRepresentation.paperTheorem1iii`
  (`[J_{C_0}, J_{C_0'}] = 0` for even-hole carriers `C_0`, `C_0'`), and in the form
  `H.CycleSymmetriesCommute` used by the sector theory,
  `SimpleGraph.PauliFrustrationRepresentation.cycleSymmetriesCommute`. The statement is v1's;
  the proof is not (`docs/V1_ERRATA.md`, E18). Route (modules `T3*` and `TheoremOneIII`):
  1. Expansion `[J_{C_0}, J_{C_0'}] = sum_{C, C'} [h_C, h_{C'}]` over the deformation
     closures (v1 L934-936):
     `SimpleGraph.PauliFrustrationRepresentation.commutator_generalizedCycleSymmetryOp_pair_eq_sum`.
  2. Frame sign lemma, for hole-class states `s = (C_a, C_b)` (`SimpleGraph.IsHoleClasses`):
     if `t_i = s_i (+) Q_i`, `t'_i = s'_i (+) Q_i`, `Q_i` inside `s_i (+) s'_i`, then
     `[h_{C_t}, h_{C_t'}] = (-1)^{c(Q_1 (+) Q_2, C)} [h_C, h_{C'}]`, `c` the number of edges
     between the two sets; no anticommutation, scale-factor or claw-free hypothesis:
     `SimpleGraph.PauliFrustrationRepresentation.commutator_toggle_holeClasses` (the closed
     form of v1 L1218-1220). For the end states of a palindromic fixed-pairing deformation
     `D` with toggle `T`, `[h_{C+T}, h_{C'+T}] = (-1)^{c(T, C)} [h_C, h_{C'}]`
     (`SimpleGraph.PauliFrustrationRepresentation.commutator_palindromic`), so for an odd `D`
     the two terms cancel
     (`SimpleGraph.PauliFrustrationRepresentation.commutator_palindromic_add_eq_zero_of_isOdd`).
  3. Pairing index `Psi(s, s') = sum_{x,y} chi_s(x) chi_{s'}(y) (A + 2I)_{xy}`
     (`SimpleGraph.pairingIndex`), which has no counterpart in v1. For claw-free `G` it equals
     `|crossed W| - |matched W|` (`SimpleGraph.pairingIndex_eq_card_sub_card`, with `W` the
     vertices of `C'` anticommuting with `h_C` split by pairing type,
     `SimpleGraph.matchedW`, `SimpleGraph.crossedW`), has the parity of `c(C, C')`
     (`SimpleGraph.pairingIndex_emod_two`) and is invariant along a palindromic deformation
     (`SimpleGraph.FPDeformation.pairingIndex_ends`). `Psi < 0` selects v1's source type
     (Definition 21).
  4. Candidate set `K*(C, C')` of the toggles of odd palindromic deformations of hole-class
     states with carriers `C`, `C'` and `Psi < 0` (`SimpleGraph.palindromicToggles`); it
     depends on the pair of carriers only and is invariant under its own toggles,
     `K*(C+T, C'+T) = K*(C, C')` for `T` in `K*(C, C')`
     (`SimpleGraph.palindromicToggles_toggle`, from toggle stability
     `SimpleGraph.FPDeformation.toggle_stable`). The pairing
     `(C, C') -> (C+T, C'+T)`, `T` chosen from `K*` as a function of `K*` alone
     (`SimpleGraph.chosenPalToggle`, `SimpleGraph.holePairToggle`), is an involution
     (`SimpleGraph.holePairToggle_involutive`), moves every pair with `K*` nonempty
     (`SimpleGraph.holePairToggle_ne`), preserves `<C_0> x <C_0'>`
     (`SimpleGraph.holePairToggle_mem_closure`) and reverses the sign of the term
     (`SimpleGraph.PauliFrustrationRepresentation.commutator_holePairToggle`);
     `Finset.sum_involution` concludes. Terms with `K*` empty vanish
     (`SimpleGraph.PauliFrustrationRepresentation.commutator_evenHoleOperator_eq_zero_of_palindromicToggles_eq_empty`).
  5. Existence (replaces v1's obstruction search): if `c(C, C')` is odd then `K*(C, C')` is
     nonempty (`SimpleGraph.palindromicToggles_nonempty`), from the existence of an odd
     palindromic deformation whenever `Psi < 0`
     (`SimpleGraph.FPDeformation.exists_palindromic_odd`), by strong induction on
     `|s_1 (+) s'_1| + |s_2 (+) s'_2|` (source-block induction), through: the component
     tether lemma (on a component of a side graph `G[C_a (+) C'_c]`, either matched `W`
     vertices are at most the crossed ones, or the component is a forward-running block with
     one matched vertex), `SimpleGraph.component_matched_le_crossed`,
     `SimpleGraph.OddBlock.card_matchedW_le_one`, bridged from the untethered paths of
     Theorem 1(ii) by `SimpleGraph.OddBlock.exists_of_untethered`; a good candidate block
     exists when `Psi < 0` by counting over the side components
     (`SimpleGraph.exists_goodCandidate`); the update of `Psi` after toggling a
     forward-running block (`SimpleGraph.OddBlock.pairingIndex_fwdState`); the separator
     lemma, the separators of a good source lie in one component of `G[C_b (+) C'_d]`
     (`SimpleGraph.OddBlock.separators_sameComponent`; general bound
     `SimpleGraph.OddBlock.separators_components_le`), with the parity identities
     `SimpleGraph.OddBlock.crossCount_carrier_mod_two` and
     `SimpleGraph.OddBlock.separatorIncidence_mod_two` and the requirement lemma
     `SimpleGraph.OddBlock.requires_contains_separator`; and the lift lemma, which transports
     an odd palindromic deformation of the reduced pair back to the original pair
     (`SimpleGraph.FPDeformation.lift`).

  Deviations from v1 (proof, not statement): (1) existence of the cancelling deformation is by
  source-block induction (step 5), not by the obstruction search of v1 L1128-1198 and v1
  Lemmas 7-10 (repo Lemmas 12, 14, 15, 16), which are not used; (2) the partner of a term is an
  involution without fixed points on the nonzero terms (step 4), which v1 leaves unargued
  (L1241); (3) the sign is the crossing parity `c(T, C)` (step 2), not v1's
  "`|W n dO|` is odd" (L1226-1227, L1234), anti-Hermiticity of `h_O` and `h_O h_O^dagger =
  B^2 I`; (4) the tether pairing of v1 L913 is used componentwise and proved injective
  (step 5); (5) no scale factors. Used: the Theorem 1(ii) deformation-path machinery
  (`SimpleGraph.EvenHoleLabeling.SetDeformationPath`) and repo Lemmas 7 and 8 and Corollary 3
  (v1 Lemmas 2, 3 and Corollary 2).
  Not used: the Definition 19 interface layer audited below (repo Lemmas 10-16 and
  Corollaries 7-12); a scan of the compiled proof term of `paperTheorem1iii` (a one-off check,
  not a repository declaration) finds no declaration of that layer.

  Non-vacuity. The representation hypothesis is satisfiable for every graph on a linearly
  ordered vertex type (`SimpleGraph.PauliShiftModel.scaledRepresentation`). The route is
  exercised by a seven-vertex claw-free graph with two 4-holes, `Psi = -1`, and an odd
  palindromic two-block deformation, so `K*` is nonempty
  (`SimpleGraph.T3Example.exists_palindromic`, `SimpleGraph.T3Example.toggles_mem`), by another
  seven-vertex claw-free graph whose two blocks share a vertex
  (`SimpleGraph.exists_palindromic_two_block_deformation`,
  `SimpleGraph.fpExD_shared_vertex`, `SimpleGraph.fpExD_union_formula_fails`), and by the
  separator lemma and toggle stability on instances
  (`SimpleGraph.fpEx_separators_sameComponent`, `SimpleGraph.fpExD_toggle_stable`).
  These instances do not witness the content of (iii): the end carrier is `C + T = C'`
  (`SimpleGraph.fpExD_fwdEnd`; for `graph7`, the module documentation of `T3NonVacuity`), so the
  two holes share one deformation class, `J_C = J_{C'}`, and `[J_C, J_{C'}] = 0` is trivial
  there; the three-qubit 4-cycle model has one even hole. `T3NonVacuity` witnesses that the
  existence layer (`palindromicToggles` nonempty) is inhabited, not that (iii) has content.

  Witness for the content of (i)-(iii): `SimpleGraph.TheoremOneExample.thm1iii_content`, on a
  claw-free 8-vertex graph in a three-qubit Pauli representation, with two 4-holes in
  different deformation classes (`SimpleGraph.TheoremOneExample.not_same_class`), crossing
  number `c(C, C') = 7` (read off the edge list `SimpleGraph.TheoremOneExample.edges8`; no Lean statement), hole terms that do not commute
  (`SimpleGraph.TheoremOneExample.terms_anticommute`: `h_C h_{C'} != h_{C'} h_C`), and `[J_C, J_{C'}] = 0`. Likewise
  `SimpleGraph.TheoremOneExample.thm1ii_content` and
  `SimpleGraph.TheoremOneExample.thm1i_content` for (ii) and (i).

### Theorem 2 (free-fermion solution)

Proved in `Matrix (Fin d) (Fin d) ℂ` with one premise beyond v1's setup, coprimality of the
sector polynomials in each occurring sector (v1 Theorem 2, assembled from v1 Lemmas 13-15):
`SimpleGraph.SimplicialModeHamiltonian.paperTheorem2_of_sectorCoprime`. It is
`SimpleGraph.SimplicialModeHamiltonian.freeFermionSolution_of_cycleSymmetry_commute` (the
form that takes `hJ : H.frustration.CycleSymmetriesCommute` as a hypothesis, kept) with `hJ`
supplied by Theorem 1(iii). Setup: `H : G.SimplicialModeHamiltonian Ks (Matrix (Fin d) (Fin d) ℂ)`
(`d` may include ancilla qubits; the structure has the fields `term_selfAdjoint`, all Pauli
terms and `chi` Hermitian, and `root_sq`, `chi^2 = 1`, besides `h_j^2 = b_j^2`), claw-free
`G` (`hclaw`), simplicial clique `Ks` (`hKs`). The `J_{C_0}` are the specific operators
`SimpleGraph.PauliFrustrationRepresentation.generalizedCycleSymmetryOp` of v1 Definition 15.
The premise beyond that setup:

- `hND`: for every `l : G.EvenHoleDeformationClass → ℝ` that is a joint eigenvalue tuple of
  the `J`'s (some `v != 0` has `J_{C_0} v = l(<C_0>) v` for every even-hole carrier `C_0`,
  and `l = 0` on every class without an even-hole carrier), the sector polynomials
  `SimpleGraph.sectorPolynomial H.coupling {} l` and `SimpleGraph.sectorPolynomial H.coupling Ks l`
  are coprime in `ℝ[X]` (`IsCoprime`). Through the fields `Z_scalar` and `ZK_scalar` of the
  `ModeSector` (built below) these are the polynomials by which `T(u) T(-u)` and `T_{G \ Ks}(u) T_{G \ Ks}(-u)`
  act on `Pi_l`. Coprime real polynomials have no common complex root
  (`ModeSectorPositivity.aeval_ne_zero_of_isCoprime`); the converse needs the Fundamental
  Theorem of Algebra, which is an explicit hypothesis of
  `ModeSectorPositivity.isCoprime_of_forall_aeval_ne_zero` because Mathlib's analytic proof
  is not available in this build. So `hND` is the form of v1's tacit "no common root of
  `Z_{G,J}` and `Z_{G \ Ks,J}`" that avoids the Fundamental Theorem of Algebra.

Why `hND` is necessary. v1 divides by `N_{J,j} = 4 u_j sqrt(z_{Ks,J}(-u_j^2) z_{{},J}'(-u_j^2))`,
which is zero at a common root, so `psi_{J,j}` is undefined there, and v1 does not state the
condition. For `C_4` with uniform couplings and `Ks` an edge (claw-free, `Ks` simplicial,
connected), in the sector `J = +1` the sector polynomials are `z = (1+2x)^2` and `z_K = 1+2x`,
sharing the root `x = -1/2`: `N = 0` and `psi` is undefined, so v1's statement fails. These are
hand computations, `docs/V1_ERRATA.md` U1, not Lean statements.

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

Deviations from v1, three in the statement:

1. The premise `hND` (above).
2. The inner index runs over `Fin (r_l)` with `r_l = deg z_{{},l}`, not over `1..alpha(G)`: v1
   does not say that `deg Z_{G,J} = alpha(G)` in every sector; for `C_4` with uniform couplings
   and `Ks` an edge, `z = 1 + 4x` in the sector `J = -1`, of degree `1 < alpha(G) = 2` (hand
   computation, `docs/V1_ERRATA.md`, U1).
3. Only `Matrix (Fin d) (Fin d) ℂ` is covered (the proofs use the Hilbert-Schmidt trace form,
   `docs/V1_ERRATA.md`, E16); for Pauli strings this loses nothing.

Also: the mode `psi_{J,-j}`, never defined in v1, is `psi_{J,j}^dagger`; `eps = 1/u` uses `u > 0`,
which v1 leaves implicit. Nothing is claimed about commutation of `Pi_l` or of the modes with
individual terms `h_j`. `hND` is all-or-nothing: the theorem says nothing for a Hamiltonian with
even one sector in which the polynomials share a root (for example uniform `C_4`, whose sector
`J = -1` is fine and whose sector `J = +1` is not); a per-sector form that assumes coprimality
only for the sectors used is not committed (open).

Non-vacuity. For the one-vertex model (`Ks = {0}`, `H = Z`, `chi = X`, no even hole, so every
`J` is `0`) `hND` holds and the conclusion is computed: `Lambda = {0}`, `r = 1`, `u = 1`,
`psi = sigma^+`, `H = Z = [psi, psi^dagger]`, `[H, psi] = 2 psi`
(`SimpleGraph.FreeFermionSolutionExample.freeFermionSolution_ham1`; the cross-sector
statement: `SimpleGraph.CrossSectorRelationsExample.exists_crossSectorModes_ham1`; both
instantiate the form with `hJ`). The three-qubit 4-cycle model with uniform couplings
(`SimpleGraph.CycleSymmetrySectorsExample.ham`) has two sectors `J = +-1` and fails `hND` in
`J = +1` (hand computation). Multi-sector witness with an even hole:
`SimpleGraph.FreeFermionSolutionMultiSectorExample.theorem2_two_sectors`, the `C_4` model with
couplings `(b_0, b_1, b_2, b_3) = (1, 1, 1, 2)` and `Ks = {0, 1}`, `J = 2 Z_2`: `z_{Ks} = 1 + 5x`,
`z = 1 + 7x + 9x^2` (`J = +2`) and `1 + 7x + x^2` (`J = -2`)
(`SimpleGraph.FreeFermionSolutionMultiSectorExample.z_empty`, `z_Ks`), coprime in both sectors
(`SimpleGraph.FreeFermionSolutionMultiSectorExample.ham2_hND`), each sector with
`r = 2 = alpha(G)`. It is the conclusion of `paperTheorem2_of_sectorCoprime` for that model with
`2 <= |Lambda|`, both signs of `J` occurring: projectors, `u, N > 0`, `T(u) T(-u) Pi_l = 0`,
the explicit modes, the canonical anticommutation relations and `H = sum_l (sum_j eps [psi,
psi^dagger]) Pi_l`. Open: `exists_crossSectorModes_of_sectorCoprime` itself is not
instantiated, and `hND` stays all-or-nothing.

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
  Scope: v1 Lemma 11 is about any Hamiltonian with a claw-free frustration graph. The form above
  is stated for `H : G.PauliCliqueHamiltonianRepresentation K ℝ A`, a representation of the
  root-adjoined graph with a root term `chi` anticommuting exactly with the clique `K`, real
  couplings and `h_j^2 = b_j^2`; the conclusion does not involve `chi` or `K`, which are extra
  data not in v1's Lemma 11. The form for the data of v1's setup, a bare
  `SimpleGraph.ScaledPauliFrustrationRepresentation G ℝ A` (terms with `h_j^2 = b_j^2`, no root,
  no clique, `u` in any commutative `ℝ`-algebra acting on `A`), with `G.IsClawFree` as the only
  hypothesis, is
  `SimpleGraph.ScaledPauliFrustrationRepresentation.generalizedCharacteristicPolynomial`
  (`W = {}`, v1 Lemma 11 itself:
  `SimpleGraph.ScaledPauliFrustrationRepresentation.generalizedCharacteristicPolynomial_empty`).
  It is proved directly, not by instantiating `K = {}`, `chi = 1`, which fails in the zero
  algebra (`docs/V1_ERRATA.md`, E6).
- Sector form of `Z_G` and `Z_{G \ Ks}` (the regrouping of v1's last display of the
  Lemma 11 proof): for `W = {}` or `W = Ks` and an element `Pi` of the
  operator algebra with `J_{<C_0>} Pi = lambda_{<C_0>} Pi` for every even hole,
  `T_{G \ W}(u) T_{G \ W}(-u) Pi = z_{W,lambda}(-u^2) Pi`:
  `SimpleGraph.PauliCliqueHamiltonianRepresentation.transfer_mul_transfer_neg_mul_sector`
  (the polynomial is `SimpleGraph.sectorPolynomial`).
- Eigenmode lemma (repo Lemma 3 = v1 Lemma 13) and intertwining relation, on a
  `SimpleGraph.SimplicialModeHamiltonian.ModeSector` (the properties of the sector
  projector are explicit structure fields; for the joint projectors of the `J`'s they are
  discharged, see below):
  `SimpleGraph.SimplicialModeHamiltonian.ModeSector.eigenmode`,
  `SimpleGraph.SimplicialModeHamiltonian.ModeSector.intertwine`.
- Ladder and canonical anticommutation relations (repo Lemma 4 = v1 Lemma 14),
  including `{psi^+, psi^+} = 0 = {psi^-, psi^-}`, which v1 does not state, on
  `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate` data (one sector, the case
  `J = J'`; the case `J != J'` is only inside Theorem 2):
  `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.ladder_plus_minus`,
  `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.ladder_plus_plus`,
  `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.ladder_minus_minus`.
- The commutator `[psi^+, psi^-]` in terms of `T` and `T'` (first half of repo Lemma 5
  = v1 Lemma 15):
  `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.commutator_plus_minus`;
  and the reconstruction on one sector by Lagrange interpolation,
  `H Pi = sum_j u_j^{-1} [psi_j^+, psi_j^-]`
  (`SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.hamiltonian_mul_Pi`, which
  assumes `Q^(k) Pi = 0` for `k > r`, used silently by v1, and
  `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.hamiltonian_mul_Pi_matrix`
  in matrix algebras with no further hypothesis; the sum over sectors is only inside Theorem 2).
  v1's last display of the proof has a sign slip: `T(0) T'(0) = -H`, not `H`, because
  `T'(0) = -Q^(1)` (`SimpleGraph.PauliFrustrationRepresentation.transferDeriv_zero`).
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
- The sectors of Theorem 2, with no hypothesis on the `J`'s. In `Matrix (Fin d) (Fin d) ℂ`,
  `SimpleGraph.PauliFrustrationRepresentation.exists_jointSpectralProjections` (claw-free `G`,
  Hermitian terms) gives a finite set `Lambda` of tuples `l`, exactly the joint eigenvalue
  tuples that occur, and Hermitian idempotents `Pi_l != 0`, pairwise orthogonal, with
  `sum_l Pi_l = 1`, `J_{<C_0>} Pi_l = l(<C_0>) Pi_l`, and commuting with every matrix that
  commutes with all the `J`'s; for claw-free `G` and a simplicial clique `Ks`,
  `SimpleGraph.SimplicialModeHamiltonian.exists_modeSectors` adds, for each `l`, a
  `SimpleGraph.SimplicialModeHamiltonian.ModeSector` with projector `Pi_l`,
  `zG = SimpleGraph.sectorPolynomial H.coupling {} l` and
  `zK = SimpleGraph.sectorPolynomial H.coupling Ks l`. Both are the conditional forms
  `SimpleGraph.PauliFrustrationRepresentation.exists_jointSpectralProjections_of_cycleSymmetry_commute`
  and `SimpleGraph.SimplicialModeHamiltonian.exists_modeSectors_of_cycleSymmetry_commute`
  (via `SimpleGraph.SimplicialModeHamiltonian.jointModeSector`), which take
  `SimpleGraph.PauliFrustrationRepresentation.CycleSymmetriesCommute` as a hypothesis, applied
  to `SimpleGraph.PauliFrustrationRepresentation.cycleSymmetriesCommute` (Theorem 1(iii)). The
  conditional hypothesis holds, with `J` acting non-trivially and two sectors `J = +-1`, on a
  three-qubit model with frustration graph the 4-cycle:
  `SimpleGraph.CycleSymmetrySectorsExample.ham_cycleSymmetriesCommute`,
  `SimpleGraph.CycleSymmetrySectorsExample.exists_two_sectors`; the unconditional
  `exists_modeSectors` is instantiated on the same model, but only for `sum_l Pi_l = 1` and
  the existence of the `ModeSector`s
  (`SimpleGraph.TheoremOneIIIConsequencesExample.exists_modeSectors_ham`); no committed example
  states `exists_jointSpectralProjections` on its own; it is used inside `paperCorollary1`,
  instantiated by `SimpleGraph.Corollary1Example.paperCorollary1_two_sectors` (below).
  `paperTheorem3` restates the same decomposition through the conditional
  `exists_jointSpectralProjections_of_cycleSymmetry_commute`. The same projectors `Pi_l` satisfy the
  identity of Theorem 3 (below), `SimpleGraph.SimplicialModeHamiltonian.paperTheorem3_modeSectors`.
- Cross-sector relations, under `hND`:
  `SimpleGraph.SimplicialModeHamiltonian.exists_crossSectorModes_of_sectorCoprime`
  (conditional form `..._of_cycleSymmetry_commute`) gives the sectors `Pi_l`, the
  `r_l = deg z_{{},l}` roots `u_{l,j}` with their non-degeneracy facts, the explicit modes
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

Not covered by Theorem 2: algebras other than `Matrix (Fin d) (Fin d) ℂ` (the proofs use the
Hilbert-Schmidt trace form, `docs/V1_ERRATA.md`, E16); the per-sector form of `hND`.

### Theorem 3 and Corollary 1 (Krylov construction)

Theorem 3 over the joint eigenspaces of the cycle symmetries (v1 L1328-1336), with no premise
beyond v1's setup and the standing assumptions (`K` simplicial, `G` claw-free):
`SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3`. Setup:
`H : G.PauliCliqueHamiltonianRepresentation K ℝ (Matrix (Fin d) (Fin d) ℂ)` with Hermitian
Pauli terms (`hstar`), claw-free `G` (`hclaw`), simplicial clique `K` (`hK`). Conclusion: the
joint spectral decomposition `(Lambda, Pi_l)` of
`SimpleGraph.PauliFrustrationRepresentation.exists_jointSpectralProjections` (Hermitian
idempotents `Pi_l != 0`, orthogonal, `sum_l Pi_l = 1`, `J_{<C_0>} Pi_l = l(<C_0>) Pi_l`,
commuting with everything that commutes with all the `J`'s, `Lambda` exactly the joint
eigenvalue tuples that occur) and, for every `l` in `Lambda`, the real matrix
`A_l = SimpleGraph.cliqueHoppingMatrix`, whose nonzero entries `(P, Q)` have `|P| + |Q|` odd
(bipartite), such that for all `k`, with `ad_{iH} = [iH, .]`, `Pi_l` commutes with
`ad_{iH}^k chi` and
`Pi_l ad_{iH}^k chi = ad_{iH}^k chi Pi_l = sum_P ((-2i)^k (A_l^k)_{{j*},P}) h_P Pi_l`. It is
`SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_cycleSymmetry_commute` (the
form with `hJ : H.operator.restrictSome.CycleSymmetriesCommute` as a hypothesis, kept) with
`hJ` supplied by Theorem 1(iii). That statement is derived from Theorem 3 for any `Pr` in the
bicommutant of the `J_c` with `J_c Pr = lambda_c Pr`, over `ℝ`, in which `[H, Pr] = 0`
(Theorem 1(ii)) and `[chi, Pr] = 0` (`chi` commutes with the `J_c`) are derived rather than
assumed: `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_bicommutant`. The
`Pi_l` of the same statement are the projectors of the `ModeSector`s of Theorem 2:
`SimpleGraph.SimplicialModeHamiltonian.paperTheorem3_modeSectors` (conditional form
`SimpleGraph.SimplicialModeHamiltonian.paperTheorem3_modeSectors_of_cycleSymmetry_commute`).
Deviations from v1: the matrix is the corrected one (`SimpleGraph.cliqueHoppingMatrix`, below),
not the printed Eq. (decoratedtree); "over each mutual eigenspace" is read as right
multiplication of each path operator by `Pi_l` (`J_c` need not commute with the individual
`h_P`; since `Pi_l` commutes with `ad^k chi`, the left form has the same value); couplings real,
algebra `Matrix (Fin d) (Fin d) ℂ`. Non-vacuity, with `J` acting non-trivially, two sectors
`J = +-1`, and the left side not zero at `k = 1`:
`SimpleGraph.TheoremOneIIIConsequencesExample.paperTheorem3_two_sectors` (the three-qubit
4-cycle model, with no commutation hypothesis supplied) and, for the conditional form,
`SimpleGraph.Theorem3SectorsExample.theorem3_two_sectors`.

For finite claw-free graphs with a simplicial clique and no even hole (then there are
no generalized cycle symmetries and the sector projector is `1`):

- Theorem 3 in the concrete form `[H, .]^k chi = (-2)^k sum_P (T^k)_{{j*},P} h_P`
  with `T` the clique-rooted tree matrix:
  `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_evenHoleFree`;
  and in v1's existential form (a real directed bipartite matrix, `ad = [iH, .]`):
  `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_evenHoleFree_exists`.
- The anticommutator identity of Corollary 1 (`{ad^j chi, ad^k chi} = 2 M_jk`) with the
  corrected sign `M_jk = (-1)^j (-2i)^{j+k} (A^{j+k})_{j*j*}`, with `chi^2 = 1` as a
  hypothesis (`hχ`: `H.rootOperator * H.rootOperator = 1`; the structure
  `PauliCliqueHamiltonianRepresentation` has no such field):
  `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_evenHoleFree`,
  `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_evenHoleFree_ad`.
  The statement over the joint eigenprojectors is `paperCorollary1` (below). The printed formula lacks `(-1)^j`; the smallest counterexample is checked in
  `KrylovAnticommutator.printedCorollary1_fails_single_vertex` (a direct `2 x 2` matrix
  computation; it does not apply either theorem). That `M` is real and symmetric (`∃ M : ℕ → ℕ → ℝ`, `M j k = M k j`) is stated in
  `paperCorollary1`, `paperCorollary1_of_bicommutant` and `paperCorollary1_modeSectors` (below).
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

Theorem 3 on a symmetry sector. For a finite claw-free graph `G`, a simplicial
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
`SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_commute_exists`. These
names stay qualified: they are stated for an arbitrary `Pr` with explicit hypotheses, where v1
takes `Pr = Pi_J`; the unqualified `paperTheorem3` is the statement over the `Pi_l` themselves
(above).

Corollary 1 (v1 Corollary 12) on a symmetry sector (the anticommutator identity only). For a
finite claw-free graph `G`, a simplicial clique `K`, `chi^2 = 1` (`hχ`) and any `Pr` with
`[H, Pr] = 0`, `[chi, Pr] = 0` and `J_c Pr = lambda_c Pr` for every even-hole class `c`,
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
qualified because v1 takes `Pr = Pi_J`.

Corollary 1 (v1 Corollary 12) over the joint eigenprojectors `Pi_l`:
`SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1`. Premises: `G` claw-free
(`hclaw`), `K` a simplicial clique (`hK`), Hermitian Pauli terms (`hstar`) and `chi^2 = 1`
(`hχ`; the structure has no such field). Conclusion: the joint spectral decomposition
`(Lambda, Pi_l)` of the cycle symmetries (Hermitian, idempotent, nonzero, orthogonal, summing to
`1`, `J_c Pi_l = l(c) Pi_l`, in the bicommutant) together with, for each `l`, a real symmetric
`M` with `M_jk = (-1)^j (-2i)^{j+k} ((A_l^{j+k})_{{j*},{j*}})`, `A_l = SimpleGraph.cliqueHoppingMatrix`,
and `Pi_l {ad_{iH}^j chi, ad_{iH}^k chi} = {ad_{iH}^j chi, ad_{iH}^k chi} Pi_l = 2 M_jk Pi_l`.
No commutation hypothesis on the `J`'s is left (Theorem 1(iii) is inside
`exists_jointSpectralProjections`); `[H, Pi_l] = 0` is Theorem 1(ii) and `[chi, Pi_l] = 0` is
`SimpleGraph.PauliCliqueHamiltonianRepresentation.commute_rootOperator_of_forall_commute` (through `SimpleGraph.PauliCliqueHamiltonianRepresentation.commute_rootOperator_generalizedCycleOperator`), via the bicommutant form
`SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_bicommutant` (qualified: it
takes a single `Pr`). For the projectors of the `ModeSector`s of Theorem 2, with `chi^2 = 1` and
Hermiticity as structure fields:
`SimpleGraph.SimplicialModeHamiltonian.paperCorollary1_modeSectors`. Connectivity of `G` is not
needed. Deviations from v1: the sign `(-1)^j`, the corrected matrix `A_l`, and `chi^2 = 1` as a
hypothesis.

Non-vacuity of `paperCorollary1`: on the three-qubit `C_4` model,
`SimpleGraph.Corollary1Example.paperCorollary1_two_sectors` (all hypotheses hold; nonzero
projections summing to `1` with both `J = +-1` occurring; `(A_l^4)_{{j*},{j*}} = 6 - 2 l(<C>)`
in every sector, forced by the identity at `j = k = 2`), and
`SimpleGraph.Corollary1Example.hopping_sector_dependent` (the corrected matrix takes the values
`4` and `8` in the two sectors, so its hoop arcs are present and sector-dependent; derived from
`paperCorollary1_of_cycleAlgebra` with `Pr = 1 +- J`, via `SimpleGraph.Corollary1Example.hopping_plus`, `SimpleGraph.Corollary1Example.hopping_minus`). For the
one-vertex model without even holes, `SimpleGraph.Corollary1Example.tree_entry` instantiates
`paperCorollary1_of_evenHoleFree`.

Not formalised, over the `Pi_l`, on a sector and without even holes alike: the positive
definiteness of `M` and the Majorana modes (v1 L1394-1430), which follow the proof of v1
Corollary 12.

### Downgrades from machine-checked audits

These audits (`docs/PAPER_FIDELITY.md`, "Audit 2026-10-26") prove properties of
repository interfaces. They do not show that any manuscript statement is false. The first three
items concern the Definition 19 interface layer that was built to follow v1's obstruction
search (v1 Lemmas 5-10 and 17); the last records corrected statements outside that layer
(Lemma 8, which Theorem 1(iii) uses, and Corollary 6). Theorem 1(iii) is not proved through the
layer (above), and a scan of the compiled proof terms of `paperTheorem1iii`,
`paperTheorem2_of_sectorCoprime`, `paperTheorem3`,
`paperTheorem3_of_evenHoleFree`, `paperCorollary1_of_evenHoleFree`,
`paperCorollary1_of_cycleAlgebra`, `generalizedCharacteristicPolynomial`,
`fundamentalIdentity`, `paperLemma17` and `paperLemma18` (a one-off check, not a repository
declaration) finds no declaration of the audited interface types. v1's own proof of Theorem
1(iii), by the obstruction search, is not formalised; its status is U6-U8 in
`docs/V1_ERRATA.md`.

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
  and the positive-history types of Lemma 11 (v1 Lemma 6) are empty
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

### Open fidelity items (2026-11-03)

Recorded by an independent review of the final state; none is a Lean error, each is a gap
between what is committed and what is claimed or could be checked.

1. Theorem 1(iii): the older instances (`T3NonVacuity`, `T3FixedPairingExample`) have the two
   holes in one deformation class; resolved by `SimpleGraph.TheoremOneExample.thm1iii_content`
   (two classes, crossing number 7; above). The Lean statement itself is v1's.
2. `paperTheorem2_of_sectorCoprime` is weaker than v1 in three documented ways (premise
   `hND`; `r_l = deg z_{{},l}` modes instead of `alpha(G)`; `Matrix (Fin d) (Fin d) ℂ`
   only, with `chi` Hermitian and `chi^2 = 1` as structure fields). `hND` is all-or-nothing, so
   nothing is said about a Hamiltonian with one degenerate sector. Non-vacuity with an even
   hole and two sectors: `SimpleGraph.FreeFermionSolutionMultiSectorExample.theorem2_two_sectors`
   (`C_4`, couplings `(1, 1, 1, 2)`, `J = +-2`); `exists_crossSectorModes_of_sectorCoprime` is
   not instantiated separately, and a per-sector form of `hND` is not committed.
3. The module documentation of `TheoremOneIIIConsequences.lean` (line 70) says
   "Non-vacuity of `paperTheorem3`, `exists_jointSpectralProjections` and `exists_modeSectors`
   on the three-qubit `C₄` model is in `FreeFermionGraphs.TheoremOneIIIConsequencesExample`",
   and says that the coprimality premise of the Theorem 2 wrappers fails on that model. The
   only overstatement is `exists_jointSpectralProjections`: the example file does not
   instantiate it (nor `paperTheorem3_modeSectors`); it is used only inside `paperCorollary1`,
   instantiated in `Corollary1Example`, while `paperTheorem3` goes through the conditional
   `exists_jointSpectralProjections_of_cycleSymmetry_commute`. The Lean
   source was not edited in this update.
4. Corollary 1 (v1 Corollary 12): proved over the joint eigenprojectors (`paperCorollary1`)
   with `chi^2 = 1` a hypothesis and the corrected sign; instantiated
   (`SimpleGraph.Corollary1Example.paperCorollary1_two_sectors`). Open: positive definiteness
   of `M` and the Majorana modes (v1 L1394-1430), not formalised.
5. Lemma 1 (v1 Lemma 11): `SimpleGraph.PauliCliqueHamiltonianRepresentation.generalizedCharacteristicPolynomial`
   carries root and clique data that v1's Lemma 11 lacks; the bare form is
   `SimpleGraph.ScaledPauliFrustrationRepresentation.generalizedCharacteristicPolynomial`
   (resolved, above). Lemma 4 (v1 Lemma 14, `ladder_plus_minus`) is the case `J = J'`;
   Lemma 5 (v1 Lemma 15, `hamiltonian_mul_Pi`, `hamiltonian_mul_Pi_matrix`) is one sector, the
   abstract version needing `Q^(k) Pi = 0` for `k > r`.

## Fidelity audit

Result-by-result audits are recorded, in order, in
[`docs/PAPER_FIDELITY_AUDIT_2026-08-05.md`](docs/PAPER_FIDELITY_AUDIT_2026-08-05.md)
(14 July 2026 manuscript, historical), the section "Audit 2026-10-26" of
[`docs/PAPER_FIDELITY.md`](docs/PAPER_FIDELITY.md) (the Definition 19 layer, the corrections to
earlier statements, and the premise table of its section F) and its section
"Audit 2026-10-30" (the Theorem 1(iii) route, the final theorems and the open items). Where they
conflict, the latest governs. The Lean terms are internally checked; the status table
distinguishes exact endpoints from conditional, corrected, degenerate and representation-level
ones.

| Manuscript layer (repo / v1) | Status | Supporting declaration |
|---|---|---|
| Lemma 6 / v1 Lemma 1 | Exact for the finite graph setting | `SimpleGraph.lemma6` |
| Lemma 7 / v1 Lemma 2; Corollaries 2-3 / v1 Corollaries 1-2 | Exact indexed path/hole statements | `SimpleGraph.IndexedInducedHole.lemma7`, `SimpleGraph.IndexedInducedPath.lemma7`, `SimpleGraph.IndexedInducedHole.corollary2`, `SimpleGraph.IsClawFree.corollary3` |
| Lemma 8 / v1 Lemma 3; Corollaries 4-5 / v1 Corollaries 3-4 | Corrected forms with the premise `t not in {s} u C` | `SimpleGraph.EvenHoleLabeling.CloneAt.lemma8`, `SimpleGraph.EvenHoleLabeling.CloneAt.corollary4`, `SimpleGraph.EvenHoleLabeling.CloneAt.corollary5` |
| Lemma 9 / v1 Lemma 4 | Exact deformation-closure statement | `SimpleGraph.lemma9` |
| Corollary 6 / v1 Corollary 5 | Exact for both compatibility notions | `SimpleGraph.corollary6`, `SimpleGraph.corollary6_induced` |
| Lemma 10 / v1 Lemma 5 | Statement on the `FixedPairingPathFamily` interface; disjointness is carried by its fields; not used by Theorem 1(iii) | `SimpleGraph.FixedPairingPathFamily.lemma10` |
| Corollaries 7-10 / v1 Corollaries 6-9 | Conditional or occurrence-erasing cores; exact ordered-path wrappers remain; not used by Theorem 1(iii) | `SimpleGraph.FixedPairingPathFamily.corollary7`, `SimpleGraph.FixedPairingPathFamily.corollary8`, `SimpleGraph.FixedPairingPathFamily.corollary9`, `SimpleGraph.FixedPairingPathFamily.corollary10` |
| Lemma 11 / v1 Lemma 6; Corollaries 11-12 / v1 Corollaries 10-11 | Single-step runs only on the finite trace types; multi-block history types empty; not used by Theorem 1(iii) | `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.blockCount_eq_one`, `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FullDefinition19Lemma11AHistoryData.isEmpty` |
| Lemma 12 / v1 Lemma 7 | `lemma12` vacuous on claw-free graphs; corrected `lemma12_of_residualData` conditional on supplied residual data; not used by Theorem 1(iii) | `SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.not_nonempty_lemma12Data_of_clawFree`, `SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.lemma12_of_residualData` |
| Lemma 13 / v1 Lemma 17 | Exact at the `FullDefinition19Deformation` interface; hypotheses satisfied by a two-step deformation; not used by Theorem 1(iii) | `SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.lemma13`, `SimpleGraph.Lemma12ResidualExample.criterion` |
| Lemma 14 / v1 Lemma 8 | Proved on one-block, one-step histories only; not used by Theorem 1(iii) | `SimpleGraph.FixedPairingPathFamily.ObstructionSearchInitialization.InitializationFiniteMixedSideLemma14History.paperLemma14` |
| Lemma 15 / v1 Lemma 9 | Collapses to Lemma 14 at state 0 (transition uninhabited); not used by Theorem 1(iii) | `SimpleGraph.FixedPairingPathFamily.ObstructionSearchReroutingTransition.isEmpty` |
| Lemma 16 / v1 Lemma 10 | Vacuous on claw-free graphs; not used by Theorem 1(iii) | `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.not_nonempty_paperLemma16Trace_of_clawFree` |
| Lemma 17 / v1 Lemma 18 | Exact charge recursion at the Pauli/frustration-graph boundary | `SimpleGraph.PauliFrustrationRepresentation.paperLemma17` |
| Lemma 18 / v1 Lemma 16 | Proved for the printed matrix without even holes; for the corrected matrix with even holes, any number of classes (`SimpleGraph.paperLemma18`, v1's hypotheses); false for the literal printed normalisation with even holes (kernel-checked counterexample) | `SimpleGraph.paperDeformationClosureLemma_of_evenHoleFree`, `SimpleGraph.sectorRow_pow_eq_of_closure`, `SimpleGraph.paperLemma18`, `SimpleGraph.PrintedNormalisation.Example.printed_normalisation_counterexample` |
| Lemma 1 / v1 Lemma 11 | Exact for a bare scaled representation (no root, no clique; claw-free only; any deleted carrier; `W = {}` is v1 Lemma 11). Also the operator form for a representation with root and clique data that v1's Lemma 11 lacks (E6), and the sector form `T(u) T(-u) Pi = z(-u^2) Pi` for `W = {}` or `W = Ks` | `SimpleGraph.ScaledPauliFrustrationRepresentation.generalizedCharacteristicPolynomial`, `SimpleGraph.ScaledPauliFrustrationRepresentation.generalizedCharacteristicPolynomial_empty`, `SimpleGraph.PauliCliqueHamiltonianRepresentation.generalizedCharacteristicPolynomial`, `SimpleGraph.PauliCliqueHamiltonianRepresentation.transfer_mul_transfer_neg_mul_sector` |
| Lemma 2 / v1 Lemma 12 | Exact | `SimpleGraph.PauliFrustrationRepresentation.fundamentalIdentity` |
| Lemma 3 / v1 Lemma 13 | On a `ModeSector` (class B data); the sectors of the joint projectors are `exists_modeSectors`; no unqualified paper theorem | `SimpleGraph.SimplicialModeHamiltonian.ModeSector.eigenmode`, `SimpleGraph.SimplicialModeHamiltonian.exists_modeSectors` |
| Lemma 4 / v1 Lemma 14 | On `Nondegenerate` data (class B), the case `J = J'`, which exists in matrix algebras when `z_G`, `z_K` are coprime; the case `J != J'` only inside Theorem 2; no unqualified paper theorem | `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.ladder_plus_minus`, `SimpleGraph.SimplicialModeHamiltonian.ModeSector.exists_nondegenerate_of_isCoprime` |
| Lemma 5 / v1 Lemma 15 | One sector: `H Pi = sum_j u_j^{-1} [psi_j^+, psi_j^-]`; the sum over sectors, `H = sum_l (sum_j eps_{l,j} [psi_{l,j}, psi_{l,j}^dagger]) Pi_l`, only inside Theorem 2 (premise `hND`) | `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.hamiltonian_mul_Pi_matrix`, `SimpleGraph.SimplicialModeHamiltonian.ModeSector.solution_on_sector` |
| Theorem 1(i) | Proved, unconditional (claw-free, any ring); non-vacuity `thm1i_content` | `SimpleGraph.PauliFrustrationRepresentation.paperTheorem1i`, `SimpleGraph.TheoremOneExample.thm1i_content` |
| Theorem 1(ii) | Proved, unconditional (claw-free, any ring); non-vacuity `thm1ii_content` | `SimpleGraph.PauliFrustrationRepresentation.paperTheorem1ii`, `SimpleGraph.TheoremOneExample.thm1ii_content` |
| Theorem 1(iii) | Proved, unconditional (claw-free, any ring, even-hole carriers), by a route that replaces v1's obstruction search (`docs/V1_ERRATA.md` E18). Non-vacuity with two deformation classes and crossing number 7 (`T3NonVacuity` has one class and is not such a witness) | `SimpleGraph.PauliFrustrationRepresentation.paperTheorem1iii`, `SimpleGraph.PauliFrustrationRepresentation.cycleSymmetriesCommute`, `SimpleGraph.palindromicToggles_nonempty`, `SimpleGraph.holePairToggle_involutive`, `SimpleGraph.TheoremOneExample.thm1iii_content` |
| Theorem 2 | Proved in `Matrix (Fin d) (Fin d) ℂ` with one premise beyond v1's setup, `hND` (per occurring joint eigenvalue tuple `l`, `z_{{},l}` and `z_{Ks,l}` coprime; v1 omits it and its printed statement fails in the `C_4` example, a hand computation, `docs/V1_ERRATA.md` U1). Projectors `Pi_l`, `r_l = deg z_{{},l}` modes per sector (not `alpha(G)`), explicit `N`, `eps = 1/u`, `psi`; `[Pi_l, psi_{l',k}] = 0`; canonical anticommutation relations across sectors; `[H, psi] = 2 eps psi`; `H = sum_l (sum_j eps [psi, psi^dagger]) Pi_l`. Name carries `_of_sectorCoprime`; `hND` is all-or-nothing; non-vacuity: a two-sector `C_4` model with an even hole, couplings `(1, 1, 1, 2)`, `J = +-2`, satisfying `hND`; also the one-vertex model without even holes (conditional form) | `SimpleGraph.SimplicialModeHamiltonian.paperTheorem2_of_sectorCoprime`, `SimpleGraph.SimplicialModeHamiltonian.exists_crossSectorModes_of_sectorCoprime`, `SimpleGraph.SimplicialModeHamiltonian.exists_modeSectors`, `SimpleGraph.SimplicialModeHamiltonian.freeFermionSolution_of_cycleSymmetry_commute`, `SimpleGraph.FreeFermionSolutionExample.freeFermionSolution_ham1`, `SimpleGraph.FreeFermionSolutionMultiSectorExample.theorem2_two_sectors` |
| Theorem 3 | Proved over the joint spectral projectors `Pi_l` of the `J_c` (also as the projectors of the `ModeSector`s), in complex matrix algebras with real couplings and Hermitian terms, with no premise beyond v1's setup and the corrected matrix `SimpleGraph.cliqueHoppingMatrix`; reading of "over a mutual eigenspace" as right multiplication by `Pi_l`; non-vacuity on the 4-cycle model with two sectors. Also: without even holes; on a symmetry sector for any `Pr` with `[H, Pr] = 0` and `J_c Pr = lambda_c Pr` (qualified names), `[H, Pr] = 0` discharged for `Pr` in the algebra generated by the `J_c`; existential form over `ℝ` | `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3`, `SimpleGraph.SimplicialModeHamiltonian.paperTheorem3_modeSectors`, `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_evenHoleFree`, `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_commute`, `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_cycleAlgebra`, `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_commute_exists`, `SimpleGraph.TheoremOneIIIConsequencesExample.paperTheorem3_two_sectors` |
| Corollary 1 | The anticommutator identity `Pi_l {ad^j chi, ad^k chi} = 2 M_jk Pi_l` over the joint eigenprojectors `Pi_l` (also as the projectors of the `ModeSector`s), `M` real symmetric with `M_jk = (-1)^j (-2i)^{j+k} (A_l^{j+k})_{j*,j*}` (corrected sign); premises claw-free, simplicial clique, Hermitian terms, `chi^2 = 1` (a hypothesis, or structure fields). Also: without even holes, and on a symmetry sector for any `Pr` with `[H, Pr] = 0`, `[chi, Pr] = 0`, `J_c Pr = lambda_c Pr` (qualified names), `Pr` in the algebra generated by the `J_c` discharging the first two; existential form. Non-vacuity: `C_4` model, two sectors, `(A_l^4)_{j*,j*} = 6 - 2l`. Open: positive definiteness of `M` and the Majorana modes (not formalised) | `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1`, `SimpleGraph.SimplicialModeHamiltonian.paperCorollary1_modeSectors`, `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_bicommutant`, `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_evenHoleFree`, `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_commute`, `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_cycleAlgebra`, `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_cycleAlgebra_exists`, `SimpleGraph.Corollary1Example.paperCorollary1_two_sectors`, `SimpleGraph.Corollary1Example.hopping_sector_dependent` |

## Remaining work

Theorem 1(iii) is proved and is no longer on the critical path of Theorem 2 or Theorem 3. The
former plan to rebuild the Definition 19 layer so that multi-step, multi-block runs are
representable (so that v1's own obstruction-search proof could be formalised) is optional:
nothing in the statements above depends on it. It would involve asserting `before_subset` only
at the first step of the first block and deriving the colour data of later holes from the
history; deriving `Lemma12ResidualData` and a corrected Lemma 16; and rebuilding the corrective
rerouting (Lemma 15) on an obstruction-search relation that can start from a nonempty prefix.
The open items proper are the fidelity items listed in the status section: optionally a
per-sector form of `hND`; the instantiation of `exists_crossSectorModes_of_sectorCoprime` and of
`exists_jointSpectralProjections`, `paperTheorem3_modeSectors` and `paperCorollary1_modeSectors`
by a committed example; the
`TheoremOneIIIConsequences` module documentation, which overstates the scope of its example;
and, for Corollary 1, the positive definiteness of `M` and the Majorana modes, which are not
formalised.

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

Names in force: `paperTheorem1i`, `paperTheorem1ii`, `paperTheorem1iii` and `paperTheorem3`
carry no premise beyond the manuscript setup and the standing assumptions (for `paperTheorem3`:
`hK`, `hclaw` and Hermiticity of the Pauli terms, `hstar`). `paperTheorem2_of_sectorCoprime` is
qualified because `hND` is a premise beyond the setup, and the unqualified `paperTheorem2` is
not exported. The `_of_cycleSymmetry_commute` forms take Theorem 1(iii) as a hypothesis and are
kept; the unqualified `exists_jointSpectralProjections`, `exists_modeSectors`,
`paperTheorem3_modeSectors` are their discharged versions.

For nondeterministic manuscript algorithms, an explicit finite execution history is
part of the setup only when its type is inhabited by genuine multi-step runs. The audits
above show that the current types are not: Lemma 14 histories have one block and one step,
the Lemma 15 transition has no instances, and the Lemma 16 trace has no instances on
claw-free graphs. No statement among Theorems 1-3, Corollary 1 and Lemmas 1-5, 17, 18 (repo numbering) depends on these types, directly or transitively. The "Downgrades from machine-checked audits" subsection lists theorems that do.

For Lemma 17 (v1 Lemma 18), the paper-facing Pauli representation does not accept an
independent-product coherence certificate. The product over an independent set and
its insertion laws are derived from pairwise commutation
(`docs/LEMMA17_FIDELITY.md`).

## Repository layout

- `FreeFermionGraphs/`: individual definitions, lemmas, and integration modules
- `FreeFermionGraphs.lean`: root import for the complete development
- `FORMALIZATION.md`: dependency-oriented proof plan with current status
- `docs/PAPER_FIDELITY.md`: current manuscript correspondence, the audits of
  2026-10-26 and 2026-10-30, and open fidelity items
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
