# Formalisation plan

The paper has three principal theorems and eighteen named lemmas. The proof
development is organised by mathematical dependency rather than paper order.

Numbers are those of the revised manuscript used throughout the repository; the
arXiv v1 equivalents are in `docs/V1_NUMBERING.md` (for example repo Lemma 17 is v1
Lemma 18, repo Lemma 18 is v1 Lemma 16, repo Lemmas 1-5 are v1 Lemmas 11-15).
Status as of 2026-10-26. Each item is marked `[done]`, `[done, corrected]`,
`[re-scoped]` or `[open]`, and names the declaration that supports the mark. Where an
audit changed the scope, the audit is in `docs/PAPER_FIDELITY.md` ("Audit 2026-10-26").

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

1. Fixed-pairing-type deformations and obstruction graphs. `[re-scoped]` Interface
   level: `SimpleGraph.FixedPairingPathFamily`, whose fields carry the disjointness
   facts; `SimpleGraph.FixedPairingPathFamily.lemma10` is proved from them. The
   pigeonhole and corrective-step arithmetic of the obstruction graph are `[done]`:
   `SimpleGraph.ArcGraph.exists_two_incoming`,
   `SimpleGraph.ArcGraph.odd_and_lt_after_removal`.
2. Lemmas 10-13 and Corollaries 7-12.
   - Lemma 11 and Corollaries 11-12. `[re-scoped]` On the finite trace types they
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
   from two holes and the derivation of the Lemma 11 block data from it.

This is the longest purely combinatorial layer and is required for Theorem
1(iii).

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
   `SimpleGraph.PauliFrustrationRepresentation.labelingOperator_mul_independentProduct`.
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
3. Theorem 1(iii): generalized-cycle charges mutually commute. `[open]` Done:
   transport identities for `h_C` along a deformation and its reverse run
   (`SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.evenHoleOperator_mul_pairProduct`,
   `SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.pairProduct_mul_evenHoleOperator_of_reverseRun`),
   corrected Lemma 12. Open: item 2.8, the rerouting model (2.4), termination of the
   search and oddness of `|W n dO|`, an involutive choice of palindromic partner.
   Theorem 1(iii) is the only premise of the Theorem 2 result (item 5.4) that is not
   discharged; the other premise there, per-sector coprimality, is part of the corrected
   statement.

## 5. Exact free-fermion solution

1. Lemma 1 (v1 Lemma 11): symmetry-sector decomposition of the generalized
   characteristic polynomial. `[done]` The operator form over families of separated
   even holes
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
     The sum over sectors needs `sum_J Pi_J = 1`: `[done]` only under the premises of
     item 5.4, `H = sum_l (sum_j eps_{l,j} [psi_{l,j}, psi_{l,j}^dagger]) Pi_l`
     (`SimpleGraph.SimplicialModeHamiltonian.freeFermionSolution_of_cycleSymmetry_commute`).
   - Deriving `Nondegenerate` data from a no-common-root hypothesis. `[done]` in matrix
     algebras: `SimpleGraph.SimplicialModeHamiltonian.ModeSector.exists_nondegenerate_of_isCoprime`
     (reality, simplicity and positivity of the roots, vanishing of the charges above
     `deg z_G`: `SimpleGraph.SimplicialModeHamiltonian.ModeSector.root_real_neg`,
     `SimpleGraph.SimplicialModeHamiltonian.ModeSector.radicand_pos`,
     `SimpleGraph.SimplicialModeHamiltonian.ModeSector.charge_mul_Pi_eq_zero`).
   - Discharging the projector fields of `ModeSector` for the joint projectors of the
     `J`'s. `[re-scoped]` Joint spectral projections of commuting Hermitian matrices:
     `[done]` `exists_joint_spectral_projections`. Done under an explicit hypothesis: in
     `Matrix (Fin d) (Fin d) ℂ`, for claw-free `G` and a simplicial clique `Ks`, from
     `H.frustration.CycleSymmetriesCommute` (Theorem 1(iii) as a hypothesis),
     `SimpleGraph.SimplicialModeHamiltonian.exists_modeSectors_of_cycleSymmetry_commute`
     gives Hermitian idempotents `Pi_l != 0`, pairwise orthogonal, `sum_l Pi_l = 1`,
     `J Pi_l = l Pi_l`, and for each `l` a `ModeSector` with
     `zG = SimpleGraph.sectorPolynomial H.coupling {} l`,
     `zK = SimpleGraph.sectorPolynomial H.coupling Ks l`
     (hypothesis: `SimpleGraph.PauliFrustrationRepresentation.CycleSymmetriesCommute`;
     non-vacuity on a three-qubit 4-cycle model with two sectors:
     `SimpleGraph.CycleSymmetrySectorsExample.exists_two_sectors`). `[open]` Theorem 1(iii)
     itself, which would discharge the hypothesis.
   - Cross-sector relations of the explicit modes. `[done]` under the premises of item 5.4:
     `SimpleGraph.SimplicialModeHamiltonian.exists_crossSectorModes_of_cycleSymmetry_commute`
     (`Pi_l psi_{l',k} = psi_{l',k} Pi_l = delta_{l,l'} psi_{l',k}`;
     `{psi_{l,j}, psi_{l',k}^dagger} = delta_{l,l'} delta_{jk} Pi_l`; `{psi, psi} = 0`); the
     cross-sector part uses only `Pi_l Pi_{l'} = 0`
     (`SimpleGraph.SimplicialModeHamiltonian.ModeSector.Orthogonal`).
4. Theorem 2. `[re-scoped]` Proved in `Matrix (Fin d) (Fin d) ℂ`, with two premises beyond
   v1's setup (finite claw-free `G`, simplicial clique `Ks`):
   `SimpleGraph.SimplicialModeHamiltonian.freeFermionSolution_of_cycleSymmetry_commute`.
   (a) `hJ : H.frustration.CycleSymmetriesCommute`, Theorem 1(iii) (item 4.3, `[open]`).
   (b) `hND`: for every joint eigenvalue tuple `l` of the `J_{C_0}` that occurs, the real
   polynomials `SimpleGraph.sectorPolynomial H.coupling {} l` and
   `SimpleGraph.sectorPolynomial H.coupling Ks l` are coprime (`IsCoprime`), the form of v1's
   tacit "no common root" that does not need the Fundamental Theorem of Algebra
   (`docs/V1_ERRATA.md`, U1 and E16). Conclusion: projectors `Pi_l` (Hermitian idempotents,
   orthogonal, `sum_l Pi_l = 1`, `J Pi_l = l Pi_l`), `r_l = deg z_{{},l}` distinct positive
   roots `u_{l,j}` per sector (v1 sums to `alpha(G)`; for `C_4` with uniform couplings and
   `Ks` an edge, `deg z = 1 < alpha(G) = 2` in the sector `J = -1`, a hand computation,
   `docs/V1_ERRATA.md`, U1), `N`, `eps = 1/u` and `psi = N^{-1} Pi_l T(-u) chi T(u)` fixed by
   formulas, `[Pi_l, psi_{l',k}] = 0`, the canonical anticommutation relations,
   `[H, psi] = 2 eps psi`, and
   `H = sum_l (sum_j eps_{l,j} [psi_{l,j}, psi_{l,j}^dagger]) Pi_l`. With (a) discharged this
   would be the qualified Theorem 2 (the target); (b) is not to be discharged. Not covered:
   algebras other than `Matrix (Fin d) (Fin d) ℂ`. Non-vacuity of (a) and (b) together: only
   the one-vertex model without even holes
   (`SimpleGraph.FreeFermionSolutionExample.freeFermionSolution_ham1`).

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
   Over the joint spectral projectors `Pi_l` themselves (v1's `Pr = Pi_J`), with
   `hJ : H.operator.restrictSome.CycleSymmetriesCommute` (Theorem 1(iii), section 4, item 3) as
   the only premise beyond v1's setup, complex matrix representations, real couplings and
   Hermitian terms: `Pi_l ad_{iH}^k chi = ad_{iH}^k chi Pi_l = sum_P ((-2i)^k (A_l^k)_{{j*},P}) h_P Pi_l`
   with `A_l = SimpleGraph.cliqueHoppingMatrix` real and bipartite, for every sector `l`
   (`SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_cycleSymmetry_commute`;
   with the `Pi_l` as the projectors of the `ModeSector`s of item 5.3:
   `SimpleGraph.SimplicialModeHamiltonian.paperTheorem3_modeSectors_of_cycleSymmetry_commute`;
   the commutations `[H, Pr] = 0`, `[chi, Pr] = 0` are derived for `Pr` in the bicommutant of
   the `J_c`: `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_bicommutant`).
   The conditional construction of the projectors is in section 5, item 3.
4. Corollary 1: canonical fermionic modes from the Krylov sequence. `[re-scoped]` v1
   Corollary 12 (L1341-1349) states only the anticommutator identity
   `Pi {ad^j chi, ad^k chi} = 2 M_jk Pi` with `M` real symmetric; the positive definiteness
   of `M` and the Majorana modes (v1 L1394-1430) come after its proof. The identity is
   `[done, corrected]`, with the sign `(-1)^j` that the printed formula lacks and with
   `chi^2 = 1` a hypothesis (`hχ`): without even holes,
   `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_evenHoleFree`;
   on a symmetry sector, for any `Pr` with `[H, Pr] = 0`, `[chi, Pr] = 0` and
   `J_c Pr = lambda_c Pr` for every even-hole class `c`, with `A_lambda` in place of the tree
   matrix, `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_commute`
   (for `Pr` in the algebra generated by the `J_c`, the first two premises are Theorem 1(ii)
   and the commutation of `chi` with the `J_c`:
   `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_cycleAlgebra`;
   existential form with a real symmetric `M`:
   `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_cycleAlgebra_exists`).
   The names are qualified because v1 takes `Pr = Pi_J`. `[open]` in every case, on a
   sector and without even holes alike: the positive definiteness of `M` and the Majorana
   modes; no declaration states positive definiteness or constructs the modes.

## Proof-completeness policy

Statements proved only under an explicit abstraction or additional hypothesis
will be marked as such in their theorem names and docstrings. The final paper
theorems will not be exposed under their paper names until every translation
assumption is discharged. Current examples: `_of_evenHoleFree` (no even hole),
`_of_residualData` (supplied Lemma 12 residual data), `_of_commute` and `_of_cycleAlgebra`
(a sector element `Pr` with explicit hypotheses instead of v1's `Pi_J`),
`_of_cycleSymmetry_commute` (Theorem 1(iii) as a hypothesis); the exact-solution lemmas are
stated on `ModeSector` and `Nondegenerate` data and are not exported as `paperLemma*`. The
Theorem 2 result also carries the premise `hND`, which no later theorem discharges (it is
part of the corrected statement); it is not exported as `paperTheorem2`.

For nondeterministic manuscript algorithms, an explicit finite execution
history is part of the setup. It is acceptable in an unqualified theorem only
when its constructors contain literal algorithm branches, no field assumes
the numbered lemma's conclusion, and its type is inhabited by genuine multi-step
runs. The audit of 2026-10-26 shows that the current Lemma 14-16 history types fail
the last condition.
