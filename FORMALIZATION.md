# Formalisation plan

The paper has three principal theorems and eighteen named lemmas. The proof
development is organised by mathematical dependency rather than paper order.

Numbers are those of the revised manuscript used throughout the repository; the
arXiv v1 equivalents are in `docs/V1_NUMBERING.md` (for example repo Lemma 17 is v1
Lemma 18, repo Lemma 18 is v1 Lemma 16, repo Lemmas 1-5 are v1 Lemmas 11-15).
Status as of 2026-11-03. Each item is marked `[done]`, `[done, corrected]`,
`[re-scoped]` or `[open]`, and names the declaration that supports the mark. Where an
audit changed the scope, the audit is in `docs/PAPER_FIDELITY.md` ("Audit 2026-10-26" for the
Definition 19 layer, the corrections to earlier statements and the premise table of its
section F; "Audit 2026-10-30" for the proof of Theorem 1(iii), the final forms of
Theorems 2 and 3, and the open fidelity items).

## 1. Finite claw-free graph theory

1. Independent sets, cliques, induced subgraphs, paths, holes, and simplicial
   cliques. `[done]` `SimpleGraph.IsSimplicialClique`, `SimpleGraph.IsEvenHoleCarrier`
   (an even-hole carrier is a finite connected 2-regular vertex set of even size at
   least 4, `SimpleGraph.isEvenHoleCarrier_iff_connected_two_regular`).
2. Lemma 6: the symmetric difference of independent sets induces a bipartite
   graph of maximum degree two. `[done]` `SimpleGraph.lemma6`.
3. Lemma 7 and Corollaries 2-3: classification of how an external vertex can
   meet an induced path or hole. `[done]` `SimpleGraph.IndexedInducedHole.lemma7`,
   `SimpleGraph.IndexedInducedPath.lemma7`, `SimpleGraph.IndexedInducedHole.corollary2`,
   `SimpleGraph.IsClawFree.corollary3`.
4. Lemmas 8-9 and Corollaries 4-6: single-vertex deformations and preservation
   of closed neighborhoods. `[done, corrected]` Lemma 8 and Corollaries 4-5 carry the
   premise `t not in {s} u C` that the printed Lemma 3 of v1 omits:
   `SimpleGraph.EvenHoleLabeling.CloneAt.lemma8`; `SimpleGraph.lemma9`;
   Corollary 6 for the two inequivalent compatibility notions of v1:
   `SimpleGraph.corollary6`, `SimpleGraph.corollary6_induced`.
5. Token sliding and the connected components of the token-sliding graph.
   `[done]` including the odd-component toggle:
   `SimpleGraph.card_and_tokenSlideReachable_symmDiff`,
   `SimpleGraph.tokenSlidingComponentMk_eq_of_tokenSlideReachable`.

## 2. Generalized-cycle combinatorics

Items 1-5 and 8 concern the Definition 19 layer that was built to follow v1's obstruction search
and are marked as audited (`docs/PAPER_FIDELITY.md`, Audit 2026-10-26); none of it is used by the
proof of Theorem 1(iii). Item 6 (Lemmas 17-18) is not part of that layer. Item 7 (deformation
closures and indexing data) is used by the proof of Theorem 1(iii), and item 9 is the combinatorics
that proves it.

1. Fixed-pairing-type deformations and obstruction graphs. `[re-scoped]` Interface
   level: `SimpleGraph.FixedPairingPathFamily`, whose fields carry the disjointness
   facts; `SimpleGraph.FixedPairingPathFamily.lemma10` is proved from them. The
   pigeonhole and corrective-step arithmetic of the obstruction graph are `[done]`:
   `SimpleGraph.ArcGraph.exists_two_incoming`,
   `SimpleGraph.ArcGraph.odd_and_lt_after_removal`.
2. Lemmas 10-13 and Corollaries 7-12.
   - Lemma 11 (v1 Lemma 6) and Corollaries 11-12 (v1 Corollaries 10-11). `[re-scoped]` On the finite trace types they
     cover a single step; the multi-block history types are empty:
     `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.blockCount_eq_one`,
     `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FullDefinition19Lemma11AHistoryData.isEmpty`.
   - Lemma 12. `[re-scoped]` The original data are uninhabited on claw-free graphs
     (`SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.not_nonempty_lemma12Data_of_clawFree`);
     the corrected residual form is `[done]` on supplied data
     (`SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.lemma12_of_residualData`,
     `SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.lemma12_carrier_of_residualData`).
     Deriving the residual data from `(C, C', W)` is `[open]`.
   - Lemma 13. `[done]` at the `FullDefinition19Deformation` interface:
     `SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.lemma13`.
   - Corollaries 7-10. `[re-scoped]` Conditional or occurrence-erasing cores:
     `SimpleGraph.FixedPairingPathFamily.corollary7`,
     `SimpleGraph.FixedPairingPathFamily.corollary8`,
     `SimpleGraph.FixedPairingPathFamily.corollary9`,
     `SimpleGraph.FixedPairingPathFamily.corollary10`.
3. Lemma 14. `[re-scoped]` Proved on histories with one block and one step:
   `SimpleGraph.FixedPairingPathFamily.ObstructionSearchInitialization.InitializationFiniteMixedSideLemma14History.paperLemma14`
   and `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.flattened_stepCount_eq_one`.
   The exact multi-step statement is `[open]`.
4. Lemma 15. `[re-scoped]` The explicit rerouting model is empty beyond state 0:
   `SimpleGraph.FixedPairingPathFamily.ObstructionSearchReroutingTransition.isEmpty`,
   `SimpleGraph.FixedPairingPathFamily.ObstructionSearchReroutingProcess.stepCount_eq_zero`.
   To be rebuilt on an obstruction-search relation that can start from a nonempty
   prefix. `[open]`
5. Lemma 16. `[re-scoped]` The existing theorem is vacuous on claw-free graphs
   (`SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.not_nonempty_paperLemma16Trace_of_clawFree`).
   Proving that the strictly decreasing corrective process terminates at an
   unobstructed deformation, and that every unobstructed deformation satisfies the
   corrected Lemma 12 criterion, is `[open]`.
6. Lemmas 17-18. `[done]` Lemma 17 (v1 Lemma 18), the charge recursion over a
   simplicial clique: `SimpleGraph.PauliFrustrationRepresentation.paperLemma17`.
   `[done, corrected]` Lemma 18 (v1 Lemma 16), proved from the closed form of the
   Krylov rows: `SimpleGraph.paperDeformationClosureLemma_of_evenHoleFree` (printed
   matrix, no even holes) and, with even holes, `SimpleGraph.paperLemma18` (corrected
   matrix; item 6.2). The final generalized-cycle cancellation is Theorem 1(iii), item 4.3.
7. Deformation closures and generalized-cycle indexing data. `[done]`
   `SimpleGraph.InEvenHoleDeformationClosure.isEvenHoleCarrier`,
   `SimpleGraph.EvenHoleLabeling.SetDeformationPath`,
   `SimpleGraph.EvenHoleLabeling.TetherPair.involutive`.
8. Rebuild of the Definition 19 layer. `[open]` The interface field
   `SimpleGraph.FixedPairingPathFamily.ACHoleStepGeometry.before_subset` is false in v1 after the first step and forces
   one block with one step (`SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.blockCount_eq_one`).
   It is to be asserted only at the first step of the first block, with the colour data
   of later holes derived from the history; then a literal Definition 19 object built
   from two holes and the derivation of the repo Lemma 11 (v1 Lemma 6) block data from it.

9. Theorem 1(iii) combinatorics, replacing the obstruction search. `[done]` Hole-class states,
   clone runs, oriented odd blocks and fixed-pairing deformations (`SimpleGraph.IsHoleClasses`,
   `SimpleGraph.ClassRun`, `SimpleGraph.OddBlock`, `SimpleGraph.FPDeformation`); the pairing index
   with `Psi = |crossed W| - |matched W|` (`SimpleGraph.pairingIndex_eq_card_sub_card`) and its
   invariance along a palindromic deformation (`SimpleGraph.FPDeformation.pairingIndex_ends`); the
   component tether lemma (`SimpleGraph.component_matched_le_crossed`); the good-candidate count
   (`SimpleGraph.exists_goodCandidate`); the separator lemma
   (`SimpleGraph.OddBlock.separators_sameComponent`); the lift lemma
   (`SimpleGraph.FPDeformation.lift`); existence of an odd palindromic deformation when `Psi < 0`
   (`SimpleGraph.FPDeformation.exists_palindromic_odd`) and nonemptiness of `K*` for odd `c(C, C')`
   (`SimpleGraph.palindromicToggles_nonempty`); toggle stability and invariance of `K*`
   (`SimpleGraph.FPDeformation.toggle_stable`, `SimpleGraph.palindromicToggles_toggle`).
   Non-vacuity: `SimpleGraph.T3Example.toggles_mem`,
   `SimpleGraph.exists_palindromic_two_block_deformation`.

Theorem 1(iii) does not need the Definition 19 layer (items 1-5 and 8): it is proved through
item 9, on the closure and indexing data of item 7 (`SimpleGraph.InEvenHoleDeformationClosure.isEvenHoleCarrier`,
`SimpleGraph.EvenHoleLabeling.SetDeformationPath`, `SimpleGraph.EvenHoleLabeling.TetherPair`). Items 1-5
and 8 would be needed only for an exact formalisation of v1's own obstruction-search proof, and no
declaration named for Theorems 1-3 or Corollary 1 depends on them.

## 3. Pauli and frustration-graph algebra

1. Finite Pauli strings and the binary symplectic commutation form. `[re-scoped]`
   The development is abstract: `SimpleGraph.PauliFrustrationRepresentation` (terms
   anticommuting exactly along edges), and `SimpleGraph.ScaledPauliFrustrationRepresentation`
   (`h_j^2 = b_j^2`). No binary symplectic form is formalised. A concrete
   representation exists for every graph on a linearly ordered vertex type, so the
   hypotheses are satisfiable: `SimpleGraph.PauliShiftModel.scaledRepresentation`.
2. Weighted Hamiltonian terms and frustration graphs. `[done]`
   `SimpleGraph.PauliFrustrationRepresentation`.
3. Products indexed by independent sets and cycles, including ordering-sign
   lemmas. `[done]` `SimpleGraph.crossCount`,
   `SimpleGraph.PauliFrustrationRepresentation.independentProduct_mul_independentProduct`,
   `SimpleGraph.PauliFrustrationRepresentation.evenHoleOperator`,
   `SimpleGraph.PauliFrustrationRepresentation.labelingOperator_mul_independentProduct`; the sign of
   simultaneous class toggles of two holes (frame sign lemma),
   `SimpleGraph.PauliFrustrationRepresentation.commutator_toggle_holeClasses`.
4. Independent-set charges, transfer operators, and generalized characteristic
   polynomials. `[done]` `SimpleGraph.PauliFrustrationRepresentation.charge`,
   `SimpleGraph.PauliFrustrationRepresentation.transfer`,
   `SimpleGraph.weightedIndependencePolynomial`,
   `SimpleGraph.PauliCliqueHamiltonianRepresentation.generalizedCharacteristicPolynomial`
   (operator form over hole families).

## 4. Conserved charges

1. Theorem 1(i): independent-set charges commute. `[done]`
   `SimpleGraph.PauliFrustrationRepresentation.paperTheorem1i`.
2. Theorem 1(ii): generalized-cycle charges commute with independent-set charges.
   `[done]` `SimpleGraph.PauliFrustrationRepresentation.paperTheorem1ii`, with the
   involution arguments that v1 omits (`SimpleGraph.untetheredSupports_toggle`,
   `SimpleGraph.EvenHoleLabeling.TetherPair.involutive`).
3. Theorem 1(iii): generalized-cycle charges mutually commute. `[done]`
   `SimpleGraph.PauliFrustrationRepresentation.paperTheorem1iii` (claw-free finite `G`,
   even-hole carriers, arbitrary ring; no other premise) and, in the form `H.CycleSymmetriesCommute`
   of the sector theory, `SimpleGraph.PauliFrustrationRepresentation.cycleSymmetriesCommute`. The
   proof pairs `[h_C, h_{C'}]` with `[h_{C+T}, h_{C'+T}]` for `T` in the invariant candidate set
   `K*` (`SimpleGraph.palindromicToggles`, `SimpleGraph.holePairToggle_involutive`), with the sign
   from the frame sign lemma
   (`SimpleGraph.PauliFrustrationRepresentation.commutator_toggle_holeClasses`) and the existence
   of `T` by source-block induction (section 2, item 9). It replaces v1's obstruction search and
   uses section 2, items 7 and 9, but none of the Definition 19 layer (items 1-5 and 8);
   `docs/V1_ERRATA.md` E18 lists the deviations from v1 and the
   v1 gaps closed. Non-vacuity of the content: `SimpleGraph.TheoremOneExample.thm1iii_content`
   (claw-free 8-vertex graph, two 4-holes in different deformation classes, crossing number 7,
   `[h_C, h_{C'}] != 0`, `[J_C, J_{C'}] = 0`); likewise `thm1ii_content`, `thm1i_content` for
   items 1-2. `SimpleGraph.T3Example.toggles_mem` (`T3NonVacuity`) only shows that the toggle
   set is nonempty: its two holes share one deformation class, so it is not a witness for (iii).

## 5. Exact free-fermion solution

1. Lemma 1 (v1 Lemma 11): symmetry-sector decomposition of the generalized
   characteristic polynomial. `[done]` For a bare
   `SimpleGraph.ScaledPauliFrustrationRepresentation` (no root, no clique; `G.IsClawFree` the only
   hypothesis; v1's Lemma 11 itself for `W = {}`):
   `SimpleGraph.ScaledPauliFrustrationRepresentation.generalizedCharacteristicPolynomial`,
   `SimpleGraph.ScaledPauliFrustrationRepresentation.generalizedCharacteristicPolynomial_empty`.
   The operator form over families of separated even holes, for a representation with root and
   clique data that v1's Lemma 11 lacks (`docs/V1_ERRATA.md`, E6)
   (`SimpleGraph.PauliCliqueHamiltonianRepresentation.generalizedCharacteristicPolynomial`)
   and the sector form `T(u) T(-u) Pi = z(-u^2) Pi` for `W = {}` or `W = Ks`
   (`SimpleGraph.PauliCliqueHamiltonianRepresentation.transfer_mul_transfer_neg_mul_sector`).
2. Lemma 2 (v1 Lemma 12) and Lemma 17 (v1 Lemma 18): transfer-operator identity for
   a simplicial mode. `[done]` `SimpleGraph.PauliFrustrationRepresentation.fundamentalIdentity`,
   `SimpleGraph.PauliFrustrationRepresentation.paperLemma17`; also the clique-deletion
   identity `SimpleGraph.PauliFrustrationRepresentation.transfer_mul_transfer_neg_eq_deleted`.
3. Lemmas 3-5 (v1 Lemmas 13-15): eigenmode equation, canonical anticommutation
   relations, and Hamiltonian reconstruction.
   - Lemma 3. `[done]` on a mode sector:
     `SimpleGraph.SimplicialModeHamiltonian.ModeSector.eigenmode`.
   - Lemma 4. `[done]` on non-degeneracy data:
     `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.ladder_plus_minus`.
   - Lemma 5. `[re-scoped]` On one sector `[done]`: the commutator
     (`SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.commutator_plus_minus`)
     and the Lagrange-interpolation reconstruction
     `H Pi = sum_j u_j^{-1} [psi_j^+, psi_j^-]`
     (`SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.hamiltonian_mul_Pi_matrix`;
     with the eigenmode relations and the explicit modes,
     `SimpleGraph.SimplicialModeHamiltonian.ModeSector.solution_on_sector`).
     The sum over sectors needs `sum_J Pi_J = 1`: `[done]` with the premise `hND` of item 5.4,
     `H = sum_l (sum_j eps_{l,j} [psi_{l,j}, psi_{l,j}^dagger]) Pi_l`
     (`SimpleGraph.SimplicialModeHamiltonian.paperTheorem2_of_sectorCoprime`).
   - Deriving `Nondegenerate` data from a no-common-root hypothesis. `[done]` in matrix
     algebras: `SimpleGraph.SimplicialModeHamiltonian.ModeSector.exists_nondegenerate_of_isCoprime`
     (reality, simplicity and positivity of the roots, vanishing of the charges above
     `deg z_G`: `SimpleGraph.SimplicialModeHamiltonian.ModeSector.root_real_neg`,
     `SimpleGraph.SimplicialModeHamiltonian.ModeSector.radicand_pos`,
     `SimpleGraph.SimplicialModeHamiltonian.ModeSector.charge_mul_Pi_eq_zero`).
   - Discharging the projector fields of `ModeSector` for the joint projectors of the
     `J`'s. `[done]` Joint spectral projections of commuting Hermitian matrices:
     `exists_joint_spectral_projections`. In `Matrix (Fin d) (Fin d) ℂ`, for claw-free `G` and a
     simplicial clique `Ks`, with no hypothesis on the `J`'s,
     `SimpleGraph.SimplicialModeHamiltonian.exists_modeSectors` gives Hermitian idempotents
     `Pi_l != 0`, pairwise orthogonal, `sum_l Pi_l = 1`, `J Pi_l = l Pi_l`, and for each `l` a
     `ModeSector` with `zG = SimpleGraph.sectorPolynomial H.coupling {} l`,
     `zK = SimpleGraph.sectorPolynomial H.coupling Ks l` (spectral part:
     `SimpleGraph.PauliFrustrationRepresentation.exists_jointSpectralProjections`; the
     commutation of the `J`'s is Theorem 1(iii), item 4.3). The conditional forms
     `exists_modeSectors_of_cycleSymmetry_commute` (hypothesis
     `SimpleGraph.PauliFrustrationRepresentation.CycleSymmetriesCommute`) are kept; non-vacuity
     on a three-qubit 4-cycle model with two sectors:
     `SimpleGraph.CycleSymmetrySectorsExample.exists_two_sectors`. The unconditional version is
     instantiated on the same model only for `sum_l Pi_l = 1` and the existence of the
     `ModeSector`s (`SimpleGraph.TheoremOneIIIConsequencesExample.exists_modeSectors_ham`);
     `exists_jointSpectralProjections` is not stated on its own by an example; it is used inside
     `paperCorollary1`, which is instantiated (item 6.4); `paperTheorem3` (item 6.3) restates the
     decomposition through the conditional `exists_jointSpectralProjections_of_cycleSymmetry_commute`.
   - Cross-sector relations of the explicit modes. `[done]` under `hND` (item 5.4):
     `SimpleGraph.SimplicialModeHamiltonian.exists_crossSectorModes_of_sectorCoprime` (conditional
     form `exists_crossSectorModes_of_cycleSymmetry_commute`;
     `Pi_l psi_{l',k} = psi_{l',k} Pi_l = delta_{l,l'} psi_{l',k}`;
     `{psi_{l,j}, psi_{l',k}^dagger} = delta_{l,l'} delta_{jk} Pi_l`; `{psi, psi} = 0`); the
     cross-sector part uses only `Pi_l Pi_{l'} = 0`
     (`SimpleGraph.SimplicialModeHamiltonian.ModeSector.Orthogonal`).
4. Theorem 2. `[done]` in `Matrix (Fin d) (Fin d) ℂ` with one premise beyond v1's setup
   (finite claw-free `G`, simplicial clique `Ks`), `hND`:
   `SimpleGraph.SimplicialModeHamiltonian.paperTheorem2_of_sectorCoprime` (the form with
   `hJ : H.frustration.CycleSymmetriesCommute` as a hypothesis, kept, is
   `SimpleGraph.SimplicialModeHamiltonian.freeFermionSolution_of_cycleSymmetry_commute`; `hJ` is
   Theorem 1(iii), item 4.3, discharged by `SimpleGraph.PauliFrustrationRepresentation.cycleSymmetriesCommute`).
   `hND`: for every joint eigenvalue tuple `l` of the `J_{C_0}` that occurs, the real
   polynomials `SimpleGraph.sectorPolynomial H.coupling {} l` and
   `SimpleGraph.sectorPolynomial H.coupling Ks l` are coprime (`IsCoprime`), the form of v1's
   tacit "no common root" that does not need the Fundamental Theorem of Algebra
   (`docs/V1_ERRATA.md`, U1 and E16); it is necessary, since v1's `N` vanishes at a common root
   (the `C_4` example, a hand computation). Conclusion: projectors `Pi_l` (Hermitian
   idempotents, orthogonal, `sum_l Pi_l = 1`, `J Pi_l = l Pi_l`), `r_l = deg z_{{},l}` distinct
   positive roots `u_{l,j}` per sector (v1 sums to `alpha(G)`; for `C_4` with uniform couplings
   and `Ks` an edge, `deg z = 1 < alpha(G) = 2` in the sector `J = -1`, a hand computation,
   `docs/V1_ERRATA.md`, U1), `N`, `eps = 1/u` and `psi = N^{-1} Pi_l T(-u) chi T(u)` fixed by
   formulas, `[Pi_l, psi_{l',k}] = 0`, the canonical anticommutation relations,
   `[H, psi] = 2 eps psi`, and
   `H = sum_l (sum_j eps_{l,j} [psi_{l,j}, psi_{l,j}^dagger]) Pi_l`. Weaker than v1 in three
   ways: `hND`; `Fin (r_l)` modes instead of `alpha(G)`; `Matrix (Fin d) (Fin d) ℂ` only. `hND`
   is all-or-nothing. Non-vacuity: the one-vertex model without even holes, for the conditional
   form (`SimpleGraph.FreeFermionSolutionExample.freeFermionSolution_ham1`). `[open]`: a committed
   instance of `exists_crossSectorModes_of_sectorCoprime` itself; a per-sector form of `hND`.
   Non-vacuity with an even hole and two sectors: the `C_4` model with couplings `(1, 1, 1, 2)`,
   sectors `J = +-2`, `z_{Ks} = 1 + 5x`, `z = 1 + 7x + 9x^2` and `1 + 7x + x^2`, `hND` in both
   sectors (`SimpleGraph.FreeFermionSolutionMultiSectorExample.ham2_hND`), `r_l = 2`: the
   conclusion of `paperTheorem2_of_sectorCoprime` with `2 <= |Lambda|`
   (`SimpleGraph.FreeFermionSolutionMultiSectorExample.theorem2_two_sectors`). The uniform-coupling
   4-cycle model fails `hND` in `J = +1` (hand computation, `docs/V1_ERRATA.md`, U1).

## 6. Krylov construction

1. Induced-path trees and the directed hopping graph. `[done, corrected]`
   `SimpleGraph.cliqueTreeMatrix`, `SimpleGraph.CliqueBubbleWand` (root handle
   allowed), and the corrected matrix of Eq. (decoratedtree) with hoop sign
   `(-1)^{k-1}`, root arcs and per-event normalisation:
   `SimpleGraph.cliqueHoppingMatrix`, `SimpleGraph.cliqueHoppingMatrix_hoop`.
2. Lemma 18 (v1 Lemma 16): path-operator sign identity and deformation closure of
   rows. `[done]` for the printed matrix on graphs without even holes
   (`SimpleGraph.paperDeformationClosureLemma_of_evenHoleFree`) and `[done, corrected]` for
   the corrected matrix with even holes and any number of hole classes
   (`SimpleGraph.krylovRow_mul_sectorIndepSeries`, `SimpleGraph.sectorRow_pow_eq_of_closure`;
   in v1's form, `SimpleGraph.paperLemma18`). For the printed normalisation
   `(1/2) sum_{P'} N^{-1}_{P,P',<C_0>} = 1` read literally (fixed source, sum over targets)
   the lemma is false: `(A^6)_{{j*},P} = 42` against `(A^6)_{{j*},P'} = 40` on a 7-vertex
   claw-free graph, checked in the kernel
   (`SimpleGraph.PrintedNormalisation.Example.printed_normalisation_counterexample`).
   Also done: the even-hoop identity
   (`SimpleGraph.PauliCliqueHamiltonianRepresentation.pathOperator_mul_bubble_eq_holeOperator`)
   and attachment uniformity (`SimpleGraph.RootedInducedPath.holeAttached_of_closure`).
3. Theorem 3: the matrix-power formula for nested commutators. `[done]` for graphs
   without even holes
   (`SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_evenHoleFree`,
   `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_evenHoleFree_exists`);
   `[done, corrected]` on a symmetry sector, for any `Pr` with `[H, Pr] = 0` and
   `J_c Pr = lambda_c Pr` for every even-hole class `c`:
   `[H, .]^k chi * Pr = (-2)^k sum_P ((A_lambda^k)_{{j*},P}) h_P Pr` with
   `A_lambda = SimpleGraph.cliqueHoppingMatrix`
   (`SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_commute`; finite
   claw-free `G`, simplicial `K`; `Pr^2 = Pr` not assumed). The name is qualified because
   v1 takes `Pr = Pi_J`. For `Pr` in the algebra generated by the `J_c`, `[H, Pr] = 0` is
   discharged by Theorem 1(ii)
   (`SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_cycleAlgebra`);
   v1's existential form over `ℝ`:
   `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_commute_exists`.
   Over the joint spectral projectors `Pi_l` themselves (v1's `Pr = Pi_J`), with no premise
   beyond v1's setup (`hK`, `hclaw`, Hermitian terms), complex matrix representations and real
   couplings: `Pi_l ad_{iH}^k chi = ad_{iH}^k chi Pi_l = sum_P ((-2i)^k (A_l^k)_{{j*},P}) h_P Pi_l`
   with `A_l = SimpleGraph.cliqueHoppingMatrix` real and bipartite, for every sector `l`
   (`SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3`; the form with
   `hJ : H.operator.restrictSome.CycleSymmetriesCommute` as a hypothesis is
   `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_cycleSymmetry_commute`, and
   `hJ` is Theorem 1(iii), section 4, item 3; with the `Pi_l` as the projectors of the
   `ModeSector`s of item 5.3: `SimpleGraph.SimplicialModeHamiltonian.paperTheorem3_modeSectors`;
   the commutations `[H, Pr] = 0`, `[chi, Pr] = 0` are derived for `Pr` in the bicommutant of
   the `J_c`: `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_bicommutant`).
   Non-vacuity on the three-qubit 4-cycle model, two sectors `J = +-1`:
   `SimpleGraph.TheoremOneIIIConsequencesExample.paperTheorem3_two_sectors` (and
   `SimpleGraph.Theorem3SectorsExample.theorem3_two_sectors` for the conditional form). The
   construction of the projectors is in section 5, item 3. "Over each mutual eigenspace" is read
   as right multiplication of the path operators by `Pi_l`.
4. Corollary 1 (v1 Corollary 12): the anticommutator identity. `[re-scoped]` v1
   Corollary 12 (L1341-1349) states only `Pi {ad^j chi, ad^k chi} = 2 M_jk Pi` with `M` real
   symmetric; the positive definiteness of `M` and the Majorana modes (v1 L1394-1430) come after
   its proof. The identity is `[done, corrected]` over the joint eigenprojectors `Pi_l`, with the
   sign `(-1)^j` that the printed formula lacks and `chi^2 = 1` a hypothesis (`hχ`):
   `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1` (premises: claw-free `G`,
   simplicial clique `K`, Hermitian Pauli terms, `chi^2 = 1`; complex matrix representations,
   real couplings). It gives the joint spectral decomposition `(Lambda, Pi_l)` of the cycle
   symmetries and, for every `l`, `Pi_l {ad_{iH}^j chi, ad_{iH}^k chi} =
   {ad_{iH}^j chi, ad_{iH}^k chi} Pi_l = 2 M_jk Pi_l` with `M` real symmetric,
   `M_jk = (-1)^j (-2i)^{j+k} ((A_l^{j+k})_{j*,j*})`, `A_l = SimpleGraph.cliqueHoppingMatrix`.
   `[H, Pi_l] = 0` is Theorem 1(ii) and `[chi, Pi_l] = 0` is
   `SimpleGraph.PauliCliqueHamiltonianRepresentation.commute_rootOperator_of_forall_commute` (through `SimpleGraph.PauliCliqueHamiltonianRepresentation.commute_rootOperator_generalizedCycleOperator`), via the bicommutant
   form `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_bicommutant`. With
   the `Pi_l` as the projectors of the `ModeSector`s of item 5.3 (`chi^2 = 1` and Hermiticity are
   then structure fields): `SimpleGraph.SimplicialModeHamiltonian.paperCorollary1_modeSectors`.
   Also: without even holes,
   `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_evenHoleFree`; on a
   symmetry sector, for any `Pr` with `[H, Pr] = 0`, `[chi, Pr] = 0` and `J_c Pr = lambda_c Pr`
   for every even-hole class `c`, with `A_lambda` in place of the tree matrix,
   `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_commute` (for `Pr` in the
   algebra generated by the `J_c`, the first two premises are Theorem 1(ii) and the commutation of
   `chi` with the `J_c`:
   `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_cycleAlgebra`; existential
   form with a real symmetric `M`:
   `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_cycleAlgebra_exists`).
   The `_of_` names are qualified because they take a single `Pr` where v1 takes `Pr = Pi_J`.
   Non-vacuity on the three-qubit 4-cycle model, two sectors `J = +-1`:
   `SimpleGraph.Corollary1Example.paperCorollary1_two_sectors` (nonzero projections summing to
   `1`, `(A_l^4)_{j*,j*} = 6 - 2l`) and `SimpleGraph.Corollary1Example.hopping_sector_dependent`
   (the corrected matrix has the values `4` and `8`: its hoop arcs are present and
   sector-dependent). `[open]`, in every case: the positive definiteness of `M` and the Majorana
   modes; no declaration states positive definiteness or constructs the modes.

## Proof-completeness policy

Statements proved only under an explicit abstraction or additional hypothesis
are marked as such in their theorem names and docstrings. At the theorem and sector level, a
paper name is unqualified only when the statement has no premise beyond the manuscript setup and
its standing assumptions: `paperTheorem1i`, `paperTheorem1ii`, `paperTheorem1iii`,
`paperTheorem3`, `paperCorollary1` and, for the sectors, `exists_jointSpectralProjections`, `exists_modeSectors`,
`paperTheorem3_modeSectors`, `paperCorollary1_modeSectors`. Of the numbered lemmas, `SimpleGraph.PauliFrustrationRepresentation.paperLemma17`
and `SimpleGraph.paperLemma18` are also unqualified and meet this condition (their hypotheses are
those of v1's Lemmas 18 and 16: a simplicial clique and, for `paperLemma18`, the standing
claw-freeness, the couplings and an arbitrary `lam`). The documented exception is `paperLemma14`, `paperLemma15` and `paperLemma16`
(several declarations carry the name `paperLemma14`, on different history types) and the helper
`paperStageCheck` of the Lemma 14 reduction. These are unqualified names on the Definition 19
interface and history types, which do not meet the policy: the data they take are degenerate
(Lemmas 14 and 15, single-step runs only) or uninhabited on claw-free graphs (Lemma 16), as
recorded in `docs/PAPER_FIDELITY.md` (Audit 2026-10-26, sections A-D) and in the README section
"Downgrades from machine-checked audits". They are proved theorems on that degenerate
interface, not exact formalisations of v1 Lemmas 8-10.
Qualified names in force: `_of_evenHoleFree` (no even hole), `_of_residualData` (supplied
Lemma 12 residual data), `_of_commute` and `_of_cycleAlgebra` (a sector element `Pr` with
explicit hypotheses instead of v1's `Pi_J`), `_of_sectorCoprime` (the premise `hND`, part of the
corrected Theorem 2; the unqualified `paperTheorem2` is not exported), and
`_of_cycleSymmetry_commute` (Theorem 1(iii) as a hypothesis; kept as the conditional forms,
discharged by `SimpleGraph.PauliFrustrationRepresentation.cycleSymmetriesCommute`). Lemmas 3-5
(v1 Lemmas 13-15) are stated on `ModeSector` and `Nondegenerate` data and are not exported as
`paperLemma3`-`paperLemma5`. Lemma 1 (v1 Lemma 11) for a bare scaled representation, with
claw-freeness as the only hypothesis, is
`SimpleGraph.ScaledPauliFrustrationRepresentation.generalizedCharacteristicPolynomial`; the form
over a representation with root and clique data that v1's Lemma 11 lacks is the older
`SimpleGraph.PauliCliqueHamiltonianRepresentation.generalizedCharacteristicPolynomial`
(`docs/V1_ERRATA.md`, E6).

For nondeterministic manuscript algorithms, an explicit finite execution
history is part of the setup. It is acceptable in an unqualified theorem only
when its constructors contain literal algorithm branches, no field assumes
the numbered lemma's conclusion, and its type is inhabited by genuine multi-step
runs. The audit of 2026-10-26 shows that the current Lemma 14-16 history types fail
the last condition; no theorem of sections 4-6 depends on them (`docs/PAPER_FIDELITY.md`, Audit
2026-10-30, section H), and Theorem 1(iii) does not use v1's search process.
