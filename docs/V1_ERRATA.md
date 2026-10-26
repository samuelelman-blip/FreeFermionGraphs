# arXiv 2305.15625v1: errata found during formalisation

This list covers arXiv 2305.15625v1 only (`main.tex`, 2146 lines). The revised
manuscript of 14 July 2026 is not available, so nothing here is claimed about it.
v1 line numbers refer to `main.tex`. Numbering conversions are in
`docs/V1_NUMBERING.md`.

Each entry gives the v1 location, the problem, the correction, and what is
certified.

- **Certified**: a Lean declaration, named with its full qualified name, states
  and proves the correction or the missing argument. The scope of the Lean
  statement is given; anything it does not cover is listed as "Not certified".
- **Identified, not certified**: found by hand reading or by exact computation
  outside Lean. No Lean statement establishes the defect or the correction these
  entries propose, and they are hypotheses about v1, not machine-checked facts. The
  corrected statements related to them (for U1 to U3) are certified in Part I entries,
  to which the entry's Lean paragraph points by number. Lean declarations that record
  groundwork for an entry (U6, U9) are named as groundwork and do not certify it.

Every repository declaration cited below was checked to exist and to depend only on
`propext`, `Classical.choice`, `Quot.sound` (2026-10-26). Names from Mathlib or Lean core
(for example `IsCoprime`, `Commute`) are not covered by that check.

Summary of consequences for v1's headline results.

| v1 result | as printed | status of the printed statement |
|---|---|---|
| Theorem 1(i) | correct | proved in Lean (`SimpleGraph.PauliFrustrationRepresentation.paperTheorem1i`); the pairing argument is sound as written (Part IV) |
| Theorem 1(ii) | correct | proved in Lean (`SimpleGraph.PauliFrustrationRepresentation.paperTheorem1ii`); the proof needs arguments v1 omits (E4) |
| Theorem 1(iii) | not proved in Lean; its statement is only the hypothesis `SimpleGraph.PauliFrustrationRepresentation.CycleSymmetriesCommute` of E16, E17 and of the joint-projector form of Theorem 3 (E12) | proof omissions U6, U8; groundwork E5 |
| Lemma 3 | premise missing | E3 |
| Corollary 12, Result 2 | sign error in the formula for `M_jk`; the anticommutator identity is proved in Lean with the corrected sign, without even holes and on a symmetry sector; positive definiteness of `M` and the Majorana modes are not formalised | E1, U5 |
| Theorem 2 | ill-defined without a non-degeneracy hypothesis | counterexample U1 (identified, not certified); proved in Lean with that hypothesis (per-sector coprimality) and the commutation of the cycle symmetries (Theorem 1(iii), open) as premises, with `deg z_{G,J}` modes per sector instead of `alpha(G)` (E17); the non-degeneracy consequences are certified in E16 |
| Theorem 3 | existential statement; proof constants and case (b.iv) defective | E12, E14, U3, U4; proved in Lean on a symmetry sector for any `Pr` with `[H, Pr] = 0` and `J_c Pr = lambda_c Pr`, with the corrected matrix (E12); and over the joint spectral projectors `Pi_l` of the `J_c` themselves, in `Matrix (Fin d) (Fin d) ℂ`, with `SimpleGraph.PauliFrustrationRepresentation.CycleSymmetriesCommute` (Theorem 1(iii), open) as the only premise beyond v1's setup (`SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_cycleSymmetry_commute`, E12) |
| Eq. (decoratedtree) normalisation (L1445), Lemma 16 | the lemma fails for the matrix with the literal normalisation | E11, E14: kernel-checked counterexample; the lemma is proved in Lean for the corrected matrix |

## Part I. Certified in Lean

### E1. Sign of the anticommutator matrix (Corollary 12 and Result 2)

Location: Corollary 12, L1341-1348; proof L1351-1392, in particular L1384 and
L1389; Result 2, L119-120.

Problem. The recursion of the proof gives `{ad^j chi, ad^k chi} = -2 M_{j-1,k+1} I`
(L1380), hence `M_{jk} = (-1)^j M_{0,j+k}`. v1 writes `2 (-i)^j M_{0,j+k}` (L1384)
and concludes `M_{jk} = (-2i)^{j+k} (A^{j+k})_{j*j*}` (L1389, repeated at L120).
The factor `(-1)^j` is missing. For the graph with one vertex `a` and `K = {a}`,
`M_11 = 4 b^2 > 0`, whereas the printed formula gives `-4 b^2`, contradicting the
positive definiteness of `M` argued at L1406-1409.

Correction. `M_{jk} = (-1)^j (-2i)^{j+k} (A^{j+k})_{j*j*}`; L1384 should read
`2 (-1)^j M_{0,j+k} I`. Odd powers of `A` vanish at the root, so `M` is real and
symmetric.

Certified.
- `KrylovAnticommutator.printedCorollary1_fails_single_vertex`: in `2 x 2` complex
  matrices (`chi = sigma_x`, `H = sigma_z`, `b = 1`) the anticommutator equals the
  corrected expression and differs from the printed one.
- `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_evenHoleFree`
  (`ad = [H, .]`) and
  `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_evenHoleFree_ad`
  (`ad = [iH, .]`): the corrected formula, for finite claw-free graphs with a
  simplicial clique and no even hole; `chi^2 = 1` is a hypothesis.
- `SimpleGraph.cliqueTreeMatrix_pow_cliqueRootPath_eq_zero_of_odd`: odd powers
  vanish at the root.
- On a symmetry sector, the case with even holes:
  `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_commute`
  (`ad = [H, .]`; `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_commute_left` has `Pr` on the left, v1's
  `Pi {.,.} = 2 M Pi`; `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_commute_ad` is `ad = [iH, .]`): for a finite
  claw-free graph, a simplicial clique, `chi^2 = 1` and any `Pr` with `[H, Pr] = 0`,
  `[chi, Pr] = 0` and `J_c Pr = lambda_c Pr` for every even-hole class `c`,
  `{ad^j chi, ad^k chi} Pr = 2 M_jk Pr` with the corrected
  `M_jk = (-1)^j (-2i)^{j+k} (A_lambda^{j+k})_{{j*},{j*}}`, `A_lambda` the corrected matrix
  `SimpleGraph.cliqueHoppingMatrix` of E11. For `Pr` in the subalgebra generated by the `J_c`
  both commutations are discharged (Theorem 1(ii), and
  `SimpleGraph.PauliCliqueHamiltonianRepresentation.commute_rootOperator_of_mem_adjoin`):
  `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_cycleAlgebra` (also `_left`, `_ad`). Existential form, as in v1's
  statement with `M` real symmetric: `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_commute_exists` and
  `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_cycleAlgebra_exists` (a real matrix `(M_jk)`, symmetric, with the
  entries above; reality and symmetry use
  `SimpleGraph.cliqueHoppingMatrix_pow_cliqueRootPath_eq_zero_of_odd`).

Not certified: Corollary 12 for `Pr = Pi_J` as a single statement, with `Pi_J` the joint
spectral projector produced under `SimpleGraph.PauliFrustrationRepresentation.CycleSymmetriesCommute`
(E16): no committed declaration applies the sector identity to those projectors, and the
existence of the complete family needs Theorem 1(iii); and, in every case, with or without
even holes and on a sector alike, the positive definiteness of `M` and the Majorana
construction (U5). The Lean statements above are the anticommutator identity only.

### E2. Two inequivalent notions of "compatible" even holes

Location: L313 and L748 (corollary at L749-751); use of compatibility at L565-567 and L1270.

Problem. L313 defines compatibility of `C, C'` in `C^(even)` by: `G[C u C']` is
disconnected with components `G[C]`, `G[C']`; for hole carriers `C n Gamma[C'] = {}`.
L748 ("Recall from Section 2 ...") recalls it as: `j not in Gamma[C']` for every
`j in Gamma[C]`, i.e. `Gamma[C] n Gamma[C'] = {}`. The second notion is strictly
stronger. Two non-adjacent 4-holes together with one vertex adjacent to an edge of
each form a claw-free graph in which the holes are compatible in the first sense
only. Corollary 5 (L749) is true for both notions. Compatibility enters only through the
families `C^(even)` in the expansion of `Z_G` (Definition 7 display, L565-567;
Lemma 11, L1270), which use the L313 notion. The symmetries `J_<C0>` (Definition 15,
L799) are sums over a deformation closure and involve no compatibility notion.

Correction. State which notion is meant; use the L313 notion in Lemma 11.

Certified.
- `SimpleGraph.exists_evenHoleInducedCompatible_not_evenHoleCompatible`: there are a
  claw-free graph and even-hole labellings whose carriers are
  `SimpleGraph.EvenHoleInducedCompatible` (L313 notion) but not
  `SimpleGraph.EvenHoleCompatible` (L748 notion).
- `SimpleGraph.corollary6` (Corollary 5 for the L748 notion) and
  `SimpleGraph.corollary6_induced` (Corollary 5 for the L313 notion).
- `SimpleGraph.PauliCliqueHamiltonianRepresentation.generalizedCharacteristicPolynomial`
  is proved with `SimpleGraph.evenHoleFamilies`, whose separation is the L313 notion.

Not certified: that Lemma 11 fails for the L748 notion. This was checked by exact
computation on two 4-holes joined through a vertex adjacent to two consecutive
vertices of each (claw-free, simplicial clique `{0,1}`): the term of the pair
`{C, C'}` occurs in `T(u) T(-u)`.

Repo note: the docstring of `SimpleGraph.EvenHoleCompatible` (`Corollary6.lean`)
says it is the L313 notion; it is the L748 notion. As defined,
`SimpleGraph.EvenHoleCompatible G A B` is
`Disjoint (G.openNeighborhood A) (G.openNeighborhood B)`; this is disjointness of the
closed neighbourhoods (the L748 notion) only for carriers contained in their own open
neighbourhood, such as hole carriers.

### E3. Lemma 3: missing premise `t not in {s} u C`

Location: Lemma 3, L707-725; Corollaries 3 and 4, L727 and L731.

Problem. The proof applies Corollary 1 (L671) to `t` as a vertex outside the
deformed hole, so it uses `t not in {s} u C`; the statement omits it. For `t = s`
or `t = a_0`, `t` neighbours exactly one of `{s, a_0}`; `Gamma_{{s} u C}(t)` is
`{a_0, b_0, b_1}` for `t = s` and `{s, b_0, b_1}` for `t = a_0`, which contains
neither `a_{k-1}` nor `a_1`, while every listed shape contains one of them (cases
(i), (ii): `a_{k-1}`; cases (iii), (iv): `a_1`). The statement is false for every `k >= 2`, not only
`k > 2`. Corollary 4 (L731) is false for `t = s` and `t = a_0`. The "similar
argument" for `u = a_0` and for the `b_1` branch is not written out.

Correction. Add `t not in {s} u C` to Lemma 3 and Corollaries 3, 4.

Certified (corrected statements, with the premise `t not in {s} u C`):
`SimpleGraph.EvenHoleLabeling.CloneAt.lemma8`,
`SimpleGraph.EvenHoleLabeling.CloneAt.corollary4`,
`SimpleGraph.EvenHoleLabeling.CloneAt.corollary5`. All branches, including the
unwritten ones, are proved in Lean.

Not certified: that the printed statement fails for every `k >= 2` (hand check of
the neighbourhood sets; no Lean counterexample).

### E4. Theorem 1(ii): involution, tethering, and stability of untethered paths

Location: L753-766 (tethering), proof L908-927, in particular L762, L766, L913, L926.

Problem.
1. L762 and L913: the association `s_0 <-> s_l` of a tethered initialiser and
   the claim "if every such initializing vertex is tethered, then they can be
   uniquely paired" are asserted without proof.
2. L913: "We have shown in Section [Neighboring Relations] that `C~` is in
   `<C_0>`" refers to no lemma.
3. L762 identifies the deformation path with the component of `G[S + C_a]` having
   endpoint `s_0`. In the tethered case the component continues through the tether
   vertex, so they coincide only when untethered.
4. L926: the cancellation needs the untethered path chosen for `(C~, S~)` to be the
   same path `P`. v1 does not show that the set of untethered paths is invariant
   under the toggle. Toggles of same-class paths are harmless; invariance of runs
   of the opposite colour class is not argued.
5. L766: `l <= k` is stated without proof.

Correction. Prove 1, 2, 4, 5; read 3 as a statement about untethered runs.

Certified.
- `SimpleGraph.EvenHoleLabeling.CloneAt.exists_setDeformationPath`: the run from a
  clone exists and is exactly one of untethered, tethered.
- `SimpleGraph.EvenHoleLabeling.SetDeformationPath.eq_of_start`: the run is unique
  given its initialiser; `SimpleGraph.EvenHoleLabeling.SetDeformationPath.len_le`:
  `l <= k`.
- `SimpleGraph.EvenHoleLabeling.SetDeformationPath.tetheredTo_symm` and
  `SimpleGraph.EvenHoleLabeling.TetherPair.involutive`: the tether is a
  fixed-point-free involution on tethered initialisers.
- `SimpleGraph.EvenHoleLabeling.exists_untethered_of_odd`: an untethered run exists
  when the number of anticommuting vertices is odd.
- `SimpleGraph.EvenHoleLabeling.SetDeformationPath.inEvenHoleDeformationClosure_final`
  (`C + P` is in `<C>`) and
  `SimpleGraph.EvenHoleLabeling.SetDeformationPath.toggle_configuration` (for an
  untethered run `P`: `S + P` is independent, of the same size, token-slide reachable
  from `S`).
- `SimpleGraph.EvenHoleLabeling.SetDeformationPath.toggle_add_eq_zero`: for an
  untethered run `P`, the cancellation identity `h_C h_S + h_{C~} h_{S~} = 0`.
- `SimpleGraph.untetheredSupports_toggle`: the set of supports of untethered runs,
  over both colour classes, is invariant under the toggle, including the
  cross-class case that v1 does not treat.
- `SimpleGraph.cycleChargeToggle_involutive`: the resulting pairing is an
  involution; `SimpleGraph.PauliFrustrationRepresentation.paperTheorem1ii` and
  `SimpleGraph.PauliFrustrationRepresentation.hamiltonian_commute_generalizedCycleSymmetryOp`
  conclude.

Item 3 is reflected in the definitions `SimpleGraph.EvenHoleLabeling.SetDeformationPath.Untethered`
(a whole component) and `SimpleGraph.EvenHoleLabeling.SetDeformationPath.TetheredTo`
but is not stated as a theorem.

### E5. Theorem 1(iii): the transport identities used but never stated

Location: proof of cancellation, L1203-1241, in particular L1217-1222 and L1236.

Problem. v1 uses `h_C h_O = kappa_1 h_{C~}` and `h_O h_{C'} = kappa_2 h_{C~'}` with
the same ordered product `h_O`, and the phrase "all scale factors cancel upon
conjugating by `h_O^2`" (L1222), without stating them.

Correction. With `h_j^2 = b_j^2` (v1 L232) and `h_O = prod_t h_{k_t} h_{j_t}`:
`h_C h_O = (prod_t b_{k_t}^2) h_{C~}` and `h_O h_{C'} = (prod_t b_{j_t}^2) h_{C~'}`,
so `kappa_1 kappa_2 = prod_t (b_{k_t} b_{j_t})^2` (the scalar called `B^2` at L1236).

Certified, for a complete Definition 19 deformation `F` (forward identity needs
`C` of even length; reverse identity needs a reverse run and `C'` of even length):
`SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.evenHoleOperator_mul_pairProduct`,
`SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.pairProduct_mul_evenHoleOperator_of_reverseRun`,
`SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.removedWeight_mul_introducedWeight`,
`SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.evenHoleOperator_mul_pairProduct_mul_pairProduct_mul_evenHoleOperator`.
Non-vacuity on a genuine two-step deformation:
`SimpleGraph.HoleOperatorTransportExample.transport_nonvacuous` (on the concrete
model `SimpleGraph.PauliShiftModel.scaledRepresentation`).
Also certified: under the criterion `U <= C^(m)`, claw-freeness and
`SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.Lemma12ResidualData`
(a supplied certificate, see `docs/PAPER_FIDELITY.md`, Audit 2026-10-26), the end
point of the reverse run has carrier `C' + (C + C^(m))` and lies in `<C'>`
(`SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.lemma12_carrier_of_residualData`).
For several paths the deformed hole is `C^(m) = C + (+)_r P^(r)` (L984-986), which
equals `C + dO` (`dO` is the union of the paths, L990) only when the paths are
pairwise vertex-disjoint (Corollary 8, L1053, allows shared vertices); the Lean
statements use `C^(m)` itself.

Not certified: `h_O h_O^dagger = B^2 I` (L1236), anti-Hermiticity of `h_O`
(L1227-1234), and the choice of partner (U8).

### E6. Lemma 11 (generalized characteristic polynomial): Theorem 1 is not needed

Location: Lemma 11, L1266-1272; proof L1924-1985, in particular L1936-1940,
L1959, L1974, L1981.

Problem. The proof invokes Theorem 1 (L1936-1940) to discard terms with
`|S| + |T|` odd. The path-component involution `(S, T) -> (S + P, T + P)` already
cancels every pair with a non-cycle component, independently of the parity, so only
claw-freeness is needed. The remark "a path cannot be the only component" (L1959)
is unnecessary. The path component must be chosen as a function of `S + T` only
(said in one clause at L1974). L1974 reads `|S| = |S|` for `|S| = |T|`. The final
regrouping into `prod J_<C_0>` (L1981) uses Corollary 5 twice and that two holes of
one deformation class are never compatible.

Correction. Delete the appeal to Theorem 1; hypothesis: claw-free.

Certified.
- `SimpleGraph.PauliFrustrationRepresentation.transfer_mul_transfer_neg_eq_holeOnly`:
  `T(u) T(-u)` is the sum over `SimpleGraph.holeOnlyPairs`; the only hypothesis is
  `G.IsClawFree`.
- The pairing: `SimpleGraph.cancelComponents`, `SimpleGraph.chosenCancelComponent`
  (a function of `cancelComponents S T`), `SimpleGraph.cancelPairToggle`,
  `SimpleGraph.cancelPairToggle_involutive`,
  `SimpleGraph.cancelPairToggle_ne_of_nonempty`.
- `SimpleGraph.PauliCliqueHamiltonianRepresentation.generalizedCharacteristicPolynomial`
  and `SimpleGraph.PauliCliqueHamiltonianRepresentation.generalizedCharacteristicPolynomial_empty`
  (`W = {}`, the printed lemma): operator form over `SimpleGraph.evenHoleFamilies`,
  hypothesis `G.IsClawFree`.
- The regrouping of L1979-1982 into the symmetries `J_<C_0>` and the sector
  restriction: `SimpleGraph.PauliFrustrationRepresentation.sum_sectorFibre_familyOperator_mul`
  (for claw-free `G`, `W` with `G.ClosureAvoids W`, and `Pi` with `J_<C_0> Pi = lambda_<C_0> Pi`
  for every even-hole carrier `C_0`: for every class set `K` in
  `SimpleGraph.sectorClassFamilies W`, the sum of the family operators over
  `SimpleGraph.sectorFibre W K`, multiplied on the right by `Pi`, is
  `(prod_{kappa in K} lambda_kappa) Pi`; the statement is this identity on `Pi` only and
  gives no identity between the sum and a product of `J` operators; the proof peels one
  class at a time, by induction on `K`, using the reindexing
  `SimpleGraph.sum_sectorFibre_insert`) and
  `SimpleGraph.PauliCliqueHamiltonianRepresentation.transfer_mul_transfer_neg_mul_sector`:
  `T_{G\W}(u) T_{G\W}(-u) Pi = z_{W,lambda}(-u^2) Pi` for `W = {}` or `W = Ks`
  (simplicial clique) whenever `J_<C_0> Pi = lambda_<C_0> Pi` for every even-hole
  carrier `C_0`, with the real polynomial `SimpleGraph.sectorPolynomial`.

### E7. The clique-deletion identity used without proof in the ladder argument

Location: proof of Lemma 14, L2085-2094 (in particular L2088-2093).

Problem. "By applying Eq. (transfermatrixrecursion) again" (L2090) requires
`Z_G(-u^2) = Z_{G \ Ks}(-u^2) - u^2 B(-u) B(u)`, equivalently
`A(-u) B(u) = B(-u) A(u)`, with `A = T_{G\Ks}` and
`B(u) = sum_{j in Ks} h_j T_{G \ Gamma[j]}(u)`. It does not follow from the
recursion; it follows from Theorem 1(i) applied to `G`, to `G \ Ks` and to the
root-adjoined graph `G^+` (claw-free because `Ks` is simplicial). v1 gives no
argument.

Correction. Supply the identity as above.

Certified.
- `SimpleGraph.PauliFrustrationRepresentation.transfer_cross_identity`
  (`A(-u) B(u) = B(-u) A(u)`),
  `SimpleGraph.PauliFrustrationRepresentation.transfer_mul_transfer_neg_eq_deleted`
  (`T(u) T(-u) = A(u) A(-u) - u^2 B(-u) B(u)`),
  `SimpleGraph.PauliFrustrationRepresentation.root_sandwich_anticomm`
  (`T(-v) chi T(v) chi + chi T(-v) chi T(v) = 4 Z_{G\Ks}(-v^2) - 2 Z_G(-v^2)`).
- `SimpleGraph.PauliFrustrationRepresentation.transfer_commute` and
  `SimpleGraph.PauliFrustrationRepresentation.hamiltonian_commute_transfer`: `[T(u), T(v)] = 0`
  and `[H, T(u)] = 0` for claw-free `G` (corollaries of Theorem 1(i), used in the
  ladder and diagonal arguments).
- `SimpleGraph.IsSimplicialClique.isClawFree_adjoinRootAt`: `G^+` is claw-free.

### E8. Unstated lemma: even holes versus a simplicial clique

Location: Result 2, L110 (`chi` commutes with every `J`); ladder proof L2088-2093
(`Z_{G \ Ks}` acts as a scalar on `Pi_J`).

Problem. Both use, without proof, that an even hole meets a simplicial clique in 0
or 2 vertices and that deformation closures of holes avoiding `Ks` avoid `Ks`.
Claw-freeness is not needed.

Certified.
- `SimpleGraph.IsSimplicialClique.ncard_inter_evenHoleCarrier` (`|Ks n C| in {0, 2}`),
  `SimpleGraph.IsSimplicialClique.even_ncard_inter_evenHoleCarrier`.
- `SimpleGraph.PauliFrustrationRepresentation.root_commute_evenHoleOperator`,
  `SimpleGraph.PauliFrustrationRepresentation.root_commute_cycleSymmetry`: the simplicial
  mode `chi` commutes with `h_C` and with every `J_<C_0>`.
- `SimpleGraph.InEvenHoleDeformationClosure.disjoint_simplicial`: closures of holes
  avoiding `Ks` avoid `Ks`.

### E9. Lemmas 13-15: statements and proofs of the ladder layer

Location: Lemma 13 L1285-1303; Lemma 14 L1306-1313, proof L2063-2104; Lemma 15
L1315-1321, proof L2106-2139; Definition 9 L597-603.

Problems and corrections.
1. `psi_{J,-j}` is used (L1289, L1310) and never defined (Definition 9 defines only
   `psi_{J,j}`, L600); `N_{J,j}` is used in Definition 9 (L600) and Theorem 2
   (L1256) but first defined at L2097. `psi_{-j} = psi_j^dagger` is not shown.
   Certified: `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.psiMinus`,
   `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.N`,
   `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.star_psiPlus`.
2. Lemma 14 states only `{psi_{+j}, psi_{-k}} = delta Pi`. The relations
   `{psi_+, psi_+} = 0 = {psi_-, psi_-}` are never stated; they follow from the
   same intertwining relation at `u = -u_k`. Certified:
   `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.ladder_plus_minus`,
   `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.ladder_plus_plus`,
   `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.ladder_minus_minus`.
3. The intertwining `(u_j + u) T(u) psi = (u_j - u) psi T(u)` is derived by applying
   `Z^{-1}(-u^2) T(u)` (L2077), which needs `Z psi = psi Z` on the sector and
   excludes `u = +-u_j` (v1 notes this at L2081). It follows directly from the
   Fundamental Identity with no inversion, for all `u`. Certified:
   `SimpleGraph.SimplicialModeHamiltonian.ModeSector.intertwine`.
4. The limits `u -> u_j` (L2081-2101, L2113-2114) should be exact derivative
   identities of operator-valued polynomials. Certified:
   `Polynomial.eval_algebraMap_eq_neg_derivative_of_forall`,
   `Polynomial.IsPolyMap.apply_eq_neg_derivative`,
   `SimpleGraph.SimplicialModeHamiltonian.ModeSector.mode_anticomm_mode_neg`.
5. `T(u_j) psi_+ = 0 = psi_+ T(-u_j)` is used (L2115-2116) without being stated;
   only the first is immediate from `Pi Z(-v^2) = 0`; the second follows from the
   intertwining at `u = -v`. Certified:
   `SimpleGraph.SimplicialModeHamiltonian.ModeSector.transfer_mul_mode_eq_zero`.
6. `epsilon = 1/u` tacitly takes `u > 0`. Certified: the eigenmode relation
   `[H, A_v] = (2/v) A_v` holds for every real `v != 0` that is a root in the sector,
   `z_G(-v^2) = 0`, and `[H, A_{-v}] = -(2/v) A_{-v}` for the same `v`
   (`SimpleGraph.SimplicialModeHamiltonian.ModeSector.eigenmode`,
   `SimpleGraph.SimplicialModeHamiltonian.ModeSector.eigenmode_neg`; both take the
   hypothesis `S.zG.eval (-v ^ 2) = 0`, claw-free `G` and a simplicial clique `Ks`).
7. The display at L2120 (`-8u/N^2 ...`) omits the factor `Z_{G\Ks}(-u_j^2)`
   that comes from `{psi_+, chi} = 4 Pi Z_{G\Ks}/N` (L2093); with it L2120 and the
   next display (L2121) agree. Certified (factor kept explicit):
   `SimpleGraph.SimplicialModeHamiltonian.ModeSector.mode_commutator_mode_neg`,
   `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.commutator_plus_minus`.
8. `Pi_J` does not commute with the individual `h_j`; a naive reading of "restrict
   to the sector" would assume it does. Lean: the structure
   `SimpleGraph.SimplicialModeHamiltonian.ModeSector` has the fields `Pi_idem`,
   `Pi_selfAdjoint`, `Pi_comm_charge` (commutation with the charges `Q_G^(k)`),
   `Pi_comm_root` (commutation with `chi`), `zG`, `zK`, `Z_scalar` and `ZK_scalar`;
   there is no field for the `h_j` or for the deleted charges. Commutation with the
   transfer operators is derived, not a field:
   `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Pi_comm_transfer`.

Scope: the Lean statements are over a `ModeSector` (the properties of the sector
projector are explicit fields) and, for Lemmas 14 and 15, over `Nondegenerate`
data, which E16 derives from a no-common-root hypothesis in matrix algebras.

### E10. Fundamental Identity is over-hypothesised

Location: Lemma 12, L1274-1283; proof L1986-2057. Typo at L2029.

Problem. Lemma 12 is stated for "SCF" Hamiltonians; the proof uses neither
claw-freeness nor Theorem 1, only the simplicial clique, the commutation pattern of
`chi`, the clique charge recursion (L529) and anticommutation inside `Ks`. At L2029 `K_j = Gamma[G] \ (Ks \ {j})`
should read `Gamma[j] \ (Ks \ {j})` (as in the statement of Lemma 18, L1992-1999).

Certified: `SimpleGraph.PauliFrustrationRepresentation.fundamentalIdentity`
(hypothesis: `G.IsSimplicialClique Ks`; no claw-freeness) and
`SimpleGraph.PauliFrustrationRepresentation.paperLemma17` (v1 Lemma 18, hypothesis:
simplicial clique only).

### E11. Eq. (decoratedtree): sign of the hoop weight and normalisation

Location: Eq. (decoratedtree), L1434-1445 (display L1435-1444, normalisation
sentence L1445).

Problem.
1. The hoop weight carries no sign. With v1's convention `h_C = h_{C_a} h_{C_b}`
   (L313), `h_P h_j = (-1)^{k-1} h_{P_s} h_C` for a hoop of length `2k` (a 4-hole
   has sign `-`, a 6-hole `+`).
2. The sentence `(1/2) sum_{P'} N^{-1}_{P,P',<C_0>} = 1` (L1445) is wrong as
   printed. Read literally (fixed source `P`, sum over targets `P'`) the resulting
   matrix violates Lemma 16 (certified below) and, by a numerical check outside Lean,
   Theorem 3. The consistent reading normalises per
   bubble event, `N_{P,Q,c} = |c| / m(P,Q)` with `m(P,Q)` the number of bubbles
   realising `P -> Q`, and the sum runs over the sources `P` of a fixed handle `Q`;
   the factor 2 counts the two directions around the hole, as v1 remarks.

Correction. Weight `(-1)^{k-1} lambda_c m(P,Q) / |c|` for an arc `P -> Q` through a
hoop of class `c` and length `2k`.

Certified.
- `SimpleGraph.PauliCliqueHamiltonianRepresentation.pathOperator_mul_bubble_eq_holeOperator`:
  `h_P h_j = (-1)^{k-1} h_{P_s} h_C` (and, for the root handle,
  `SimpleGraph.PauliCliqueHamiltonianRepresentation.pathOperator_mul_bubble_eq_rootOperator_mul_holeOperator`);
  the pair `(P, P*)` contributes twice:
  `SimpleGraph.PauliCliqueHamiltonianRepresentation.pathOperator_mul_bubble_add_reverse_eq_two_mul`.
- `SimpleGraph.cliqueHoppingMatrix_hoop`: the entry of the corrected matrix
  `SimpleGraph.cliqueHoppingMatrix` for a hoop arc is
  `(-1)^{k-1} lambda_c m(P,Q) / |c|`.
- `SimpleGraph.half_sum_inv_eventNormalisation_of_attached`: the corrected
  normalisation `(1/2) sum_{sources P} N_{P,Q,c}^{-1} = 1`.
- `SimpleGraph.cliqueHoppingMatrix_column_hoop_total`: the column total over sources
  of the hoop part is `2 (-1)^{k_c-1} lambda_c` if a hole of class `c` is attached to
  the handle `Q`, and `0` otherwise.
- The root-handle arcs `P -> {j*}` (split index 0) are included in the Lean matrix
  (example: `SimpleGraph.CliqueBubbleWand.Example.hopping_root_entry`, the entry
  into the root path of the 4-cycle is `-lambda`). v1's labelling starts at
  `j_0 = j*` (L303, L692-698; L1520 uses `0 <= s`), so v1's definition allows them;
  they are not a v1 defect.

Certified: that the literal reading fails Lemma 16 (E14). Read literally, the normalisation
sentence is `SimpleGraph.IsPrintedNormalisation` (a fixed source `P`, the sum over its targets
in the class of the arc, no sign; matrix `SimpleGraph.printedHoppingMatrix`). On `G` with
vertex set `{0..6}`, edges `01 02 03 05 06 12 14 25 34 35 36 46 56` (claw-free), simplicial
clique `K = {2,5}`, `P = (j*,2,0)` and its single-vertex deformation `P~ = (j*,5,0)`:
- `SimpleGraph.PrintedNormalisation.Example.printed_pow_six_package`: for every field of
  characteristic 0, couplings with `b^2 = (4,4,1,3,5,4,4)`, `lambda = 3` on every class and
  every normalisation satisfying `SimpleGraph.IsPrintedNormalisation`, `(A^6)_{{j*},P} = 428` and
  `(A^6)_{{j*},P~} = 422`;
- `SimpleGraph.PrintedNormalisation.Example.printed_pow_unit`: for unit couplings and
  `lambda = 1`, the entries are `42` and `40`, and the two rows agree for `k < 6`;
  `SimpleGraph.PrintedNormalisation.Example.printed_normalisation_counterexample` assembles
  it: claw-free, simplicial clique, `3 <= |P|`, `P~` in the deformation closure of `P`, a
  printed normalisation exists, and for each one the entries are `42` and `40`.
Each source of the example has a single target, so every such normalisation is `1/2`
(`SimpleGraph.IsPrintedNormalisation.eq_half`,
`SimpleGraph.PrintedNormalisation.Example.arc_unique`). The values are computed in the
kernel on a decidable model of the induced-path tree that is proved to represent the repo's
types (`SimpleGraph.PrintedNormalisation.Example.printed_pow_apply`).

Not certified: that the printed sentence is to be read as `SimpleGraph.IsPrintedNormalisation`; that the
corrected weights give `398` for both entries (exact computation outside Lean; Lean proves that
the two entries of the corrected matrix agree, for every power, field, `b` and `lambda`,
`SimpleGraph.PrintedNormalisation.Example.corrected_balanced_of_paperLemma18`); that the
example is a smallest one (numerical search outside Lean). The cause is that the source
`(j*,5,0,1,4)` reaches the handle `(j*,5)` through two bubbles, which a per-arc normalisation
ignores. The operator identity of Theorem 3 with the corrected weights was first checked
numerically in dense Pauli representations (6 hand-made and 25 random claw-free graphs, one
with a two-hole class), outside Lean; it is proved in Lean in E12.

### E12. Theorem 3: printed constants, case (b.iv), and the missing attachment lemma

Location: Theorem 3 statement L1328-1336; proof L1494-1576.

Problem.
1. L1505: the induction hypothesis drops the factor `(-2i)^m`; the second line of
   the induction step (L1510) is correct only with `[H, h_P]` in place of
   `[iH, h_P]`; the `j not in P` sum (L1512) lacks the factor `(-2i)^k`.
2. Case (b.iv) (L1520-1576) assumes, without proof, that every hole of the class
   `<C_0>` is attached to the handle exactly twice. The comparands in Eqs.
   (pathgroupterms) and (patheffectivecircle) live in different re-rooted graphs
   (`(G \ Gamma[P']) u {j_{s+1}}` versus `... u {j}`); a trace/fiducial argument is
   used for a purely combinatorial identity; and the case invokes Lemma 16, whose
   proof is defective (E14).

Correction. Use the corrected matrix of E11; prove attachment uniformity.

Certified.
- Theorem 3 with the correct constants, for finite claw-free graphs with a
  simplicial clique and no even hole: `[H, .]^k chi = (-2)^k sum_P (T^k)_{{j*},P} h_P`,
  `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_evenHoleFree`;
  in v1's existential form (real directed bipartite matrix, `ad = [iH, .]`),
  `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_evenHoleFree_exists`.
  Without even holes there are no generalized cycle symmetries, so `Pi_J = 1` and
  the statement has no projector.
- Attachment uniformity: `SimpleGraph.RootedInducedPath.holeAttached_of_closure`
  (attachment is constant on a deformation class),
  `SimpleGraph.card_evenHoopEvents` (wand events correspond two to one to attached
  even-hole carriers), `SimpleGraph.card_evenHoopEvents_of_attached`,
  `SimpleGraph.card_evenHoopEvents_eq_zero_of_not_attached`.
- Even-hoop operator identity: `SimpleGraph.PauliCliqueHamiltonianRepresentation.pathOperator_mul_bubble_eq_holeOperator`
  (E11).
- Theorem 3 on a symmetry sector, with the corrected matrix
  `A_lambda = SimpleGraph.cliqueHoppingMatrix`:
  `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_commute`,
  `[H, .]^k chi * Pr = (-2)^k sum_P ((A_lambda^k)_{{j*},P}) h_P Pr`, for a finite
  claw-free graph, a simplicial clique `K`, and any `Pr` with `[H, Pr] = 0` and
  `J_c Pr = lambda_c Pr` for every even-hole class `c`; `Pr^2 = Pr` is not assumed. The
  proof is by induction on `k`: one step on a sector-balanced row
  (`SimpleGraph.PauliCliqueHamiltonianRepresentation.commutator_sum_mul_of_isSectorBalancedRow`;
  the rows of the powers of `A_lambda` at the root are balanced,
  `SimpleGraph.isSectorBalancedRow_cliqueHoppingMatrix_pow_root`), where the even-wand terms of
  one handle and one class add up to `2 (-1)^{k-1} h_Q J_c`
  (`SimpleGraph.PauliCliqueHamiltonianRepresentation.sum_holeEvents_pathOperator_mul`), which on
  the sector is `2 (-1)^{k-1} lambda_c h_Q`. This is the reading of U3(b), (c). For `Pr` in the
  subalgebra generated by the `J_c`, `[H, Pr] = 0` follows from Theorem 1(ii)
  (`SimpleGraph.PauliCliqueHamiltonianRepresentation.commute_physicalHamiltonian_of_mem_adjoin`):
  `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_cycleAlgebra`. v1's
  existential form over `ℝ` (a real matrix, nonzero entries `M_PQ` only where `|P| + |Q|` is
  odd, `ad = [iH, .]`, witness `A_lambda`):
  `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_commute_exists`.
- Theorem 3 over the joint spectral projectors of the `J_c`, conditional on Theorem 1(iii)
  (`hJ : H.operator.restrictSome.CycleSymmetriesCommute`) as the only premise beyond v1's setup,
  for `H` over `ℝ` in `Matrix (Fin d) (Fin d) ℂ` with Hermitian terms:
  `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_cycleSymmetry_commute`.
  For every sector `l` of the joint spectral decomposition `(Lambda, Pi_l)`
  (`SimpleGraph.PauliFrustrationRepresentation.exists_jointSpectralProjections_of_cycleSymmetry_commute`,
  E16), `A_l = SimpleGraph.cliqueHoppingMatrix` is real and bipartite (nonzero entries only where
  `|P| + |Q|` is odd), `Pi_l` commutes with every `ad_{iH}^k chi`, and
  `Pi_l ad_{iH}^k chi = ad_{iH}^k chi Pi_l = sum_P ((-2i)^k (A_l^k)_{{j*},P}) h_P Pi_l`. It is
  derived from
  `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_bicommutant` (any `Pr` in
  the bicommutant of the `J_c` with `J_c Pr = lambda_c Pr`: `[H, Pr] = 0` by Theorem 1(ii) and
  `[chi, Pr] = 0` are derived, `Pr^2 = Pr` is not assumed). The same `Pi_l` are the projectors of
  the `ModeSector`s of E16, E17:
  `SimpleGraph.SimplicialModeHamiltonian.paperTheorem3_modeSectors_of_cycleSymmetry_commute`.
  The hypotheses are satisfiable with `J` acting non-trivially, and the left side is not zero at
  `k = 1`, on the three-qubit 4-cycle model of E16
  (`SimpleGraph.Theorem3SectorsExample.theorem3_two_sectors`, two sectors `J = +-1`).

- Eq. (pathcircle) for the corrected matrix `SimpleGraph.cliqueHoppingMatrix`, with
  hole terms and any number of hole classes: `SimpleGraph.sectorRow_pow_wandReverse`
  (`(A^n)_{{j*},P} = (A^n)_{{j*},P*}` for the reversal `P*` of a wand on `P`, any
  hoop) and `SimpleGraph.sectorRow_pow_eq_of_sameHandle` (sources of one handle and
  one hoop class).

Not certified: Theorem 3 without the hypothesis `SimpleGraph.PauliFrustrationRepresentation.CycleSymmetriesCommute` (Theorem 1(iii)): the
complete family of projectors `Pi_J` exists only under it. The anticommutator identity of
Corollary 12 on a sector is certified in E1; the positive definiteness of `M` and the Majorana
modes are not, in any case (U5).

### E13. Implicit facts used but never stated

Location: Theorem 1(ii), (iii) and the definition of `J` (L313, L799).

Problem. v1 uses without statement that every member of `<C_0>` of an even hole
`C_0` is an even hole of the same length with well-defined colour classes, and that
`h_C` does not depend on the labelling (the colour classes commute, L313).

Certified.
- `SimpleGraph.InEvenHoleDeformationClosure.isEvenHoleCarrier`: members of the
  closure are even-hole carriers.
- `SimpleGraph.InEvenHoleDeformationClosure.ncard_eq`: members of the closure have
  the same size.
- `SimpleGraph.PauliFrustrationRepresentation.labelingOperator_comm` (the two colour
  class products commute) and
  `SimpleGraph.PauliFrustrationRepresentation.labelingOperator_eq_of_carrier_eq`
  (`h_C` depends only on the carrier).
- `SimpleGraph.isEvenHoleCarrier_iff_exists_labeling`: a labelling carrier is an
  even-hole carrier exactly when it induces a connected subgraph.

### E14. Lemma 16 (deformation closure of induced paths)

Location: Lemma 16, L1457-1485; gap at L1480.

Problem. The last-crossing substitution is not defined on every walk: after the
final traversal of `P_{i-1} -> P_i`, a walk can leave the prefix chain and come back.
Example: `G = K_4` minus the edge `kx` on `{a, k, b, x}`, `K = {a, k}`,
`P = (j*, a, b)`, `P~ = (j*, k, b)`; the walk `j*, a, ax, a, ab` passes through
`(j*, a, x)`, and `(j*, k, x)` is not a path.

Correction. The lemma holds for the corrected matrix; prove it without the walk
substitution, from the closed form of the rows of the tree matrix.

Certified.
- `SimpleGraph.krylovRow_mul_indepSeries`: for a claw-free graph with a simplicial
  clique, `(sum_n X^n (T^n)_{{j*},Q}) . I_V = X^{|Q|-1} . I_{V \ N(Q)}` for the tree
  matrix `T = SimpleGraph.cliqueTreeMatrix`; the row depends on `Q` only through
  `|Q|` and the closed neighbourhood `N(Q)`.
- `SimpleGraph.cliqueTreeMatrix_pow_root_eq_of_closure`: the entries `(T^n)_{{j*},P}`
  are constant on a deformation closure.
- `SimpleGraph.paperDeformationClosureLemma_of_evenHoleFree`: Lemma 16 (v1 L1457-1464)
  for the repo matrix `SimpleGraph.eqE1WeightedAdjacency`, in the case with no even
  hole, where it equals the tree matrix
  (`SimpleGraph.eqE1WeightedAdjacency_eq_cliqueTreeMatrix`).

- With even holes, for the corrected matrix and any number of hole classes:
  `SimpleGraph.krylovRow_mul_sectorIndepSeries`,
  `(sum_n X^n (A_lambda^n)_{{j*},Q}) . Z_V = X^{|Q|-1} . Z_{V \ N(Q)}`, where
  `Z_U = SimpleGraph.sectorIndepSeries` is defined as the sum, over families of
  pairwise compatible (L313) even holes inside `U`, of the product of the hole weights
  `2 (-X^2)^{|C|/2} lambda_{<C>} / |<C>|` (`SimpleGraph.sectorHoleWeight`) times the
  weighted independence series of the vertices of `U` outside the family's closed
  neighbourhood (`SimpleGraph.holeSeries`); and
  `SimpleGraph.sectorRow_pow_eq_of_closure`: the rows of `SimpleGraph.cliqueHoppingMatrix`
  are constant on a deformation closure. The identity is not stated in v1. The
  single-class form is `SimpleGraph.krylovRow_mul_indepSeries_single_class`.
- v1 Lemma 16 for the corrected matrix, in v1's form: `SimpleGraph.paperLemma18` (finite
  claw-free graph, simplicial clique, couplings `b`, arbitrary `lambda`, `|P| >= 3`, `P'` in
  the deformation closure of `P`: `(A^k)_{{j*},P} = (A^k)_{{j*},P'}` for all `k`, for
  `A = SimpleGraph.cliqueHoppingMatrix`) and `SimpleGraph.paperLemma18_of_deformationStep`
  (a single-vertex deformation, the case to which v1's proof reduces). It follows from
  `SimpleGraph.sectorRow_pow_eq_of_closure` without the last-crossing substitution. For the literal
  printed normalisation the lemma fails: kernel-checked counterexample in E11.

Not certified: the failure of the walk substitution in the example (hand check); that
`Z_U` is the sector reduction (`J_c -> lambda_c`) of the generalized characteristic
polynomial of `G[U]`, and hence that this identity is the polynomial divisibility
behind Theorem 3 (U3). No Lean theorem relates `SimpleGraph.sectorIndepSeries` to
`SimpleGraph.sectorPolynomial`, to
`SimpleGraph.PauliCliqueHamiltonianRepresentation.generalizedCharacteristicPolynomial`
or to `SimpleGraph.PauliCliqueHamiltonianRepresentation.transfer_mul_transfer_neg_mul_sector`.
The docstring of `SimpleGraph.sectorIndepSeries` allows that reading only when `U`
contains all or none of the holes of each deformation class and `|<C>|` is invertible
in the field; for other `U` it calls `Z_U` a bookkeeping series.

### E15. Lemma 15: sign slip in the last display, the Lagrange step, the summation range

Location: L2123-2139, in particular L2129, L2133, L2137.

Problem.
1. The last display (L2137), `(T_G(u) d_u T_G(u))|_{u=0} = H`, is wrong:
   `T(0) T'(0) = -Q^(1) = -H`. The preceding display (L2133) is correct: with
   `D(u) = T(-u) T'(u) + T(u) T'(-u)` and Lagrange weights `w_j`, it is
   `-(1/2) sum_j w_j D(u_j)`, and interpolation gives `-(1/2) D(0) = -T'(0) = H`. The
   conclusion is right, the displayed expression is not.
2. The Lagrange step needs the operator polynomial `D(u) Pi` in `x = -u^2` to have
   degree `< deg z_{G,J}` on the sector; v1 does not say why.
3. The formula for `dZ/dx` at L2129 presumes the product form
   `z_G = prod_j (1 + x/u_j^2)`.
4. The sum runs over `j = 1..alpha(G)`; it must run over the `r = deg z_{G,J}` modes
   of the sector (U1).

Certified.
- `SimpleGraph.PauliFrustrationRepresentation.transferDeriv_zero`:
  `T'_{G\W}(0) = -Q_{G\W}^(1)`; `SimpleGraph.PauliFrustrationRepresentation.transferDerivSymm_zero`:
  `D(0) = -2 Q^(1)`.
- `SimpleGraph.PauliFrustrationRepresentation.sum_weight_smul_transferDerivSymm_mul`:
  the Lagrange interpolation at `0`, `sum_j w_j D(u_j) Pi = D(0) Pi`, for nodes
  `u : Fin r -> ℝ` that are positive and pairwise distinct (`0 < u j`,
  `Function.Injective u`), when the charges of order above `r` vanish on `Pi`
  (`Q^(k) Pi = 0` for `k > r`) and all charges commute pairwise
  (`forall s t, Commute (charge s) (charge t)`).
- `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.weight_eq_inv`:
  `w_j = (u_j^2 z_G'(-u_j^2))^{-1}` (the formula of L2129 from the product form) and
  `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.natDegree_zG`: `r = deg z_G`.
- `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.hamiltonian_mul_Pi`:
  `H Pi = sum_j u_j^{-1} [psi_j^+, psi_j^-]` on a sector when `Q^(k) Pi = 0` for
  `k > r`; `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.hamiltonian_mul_Pi_matrix`:
  the same in matrix algebras with no hypothesis on the charges (E16).

Certified, conditional on Theorem 1(iii) and on per-sector coprimality (E17): the sum over
sectors, `H = sum_J (sum_j epsilon_{J,j} [psi_{J,j}, psi_{J,j}^dagger]) Pi_J`, using
`sum_J Pi_J = 1` from the joint spectral decomposition of the `J`'s, which is available only
under the hypothesis `SimpleGraph.PauliFrustrationRepresentation.CycleSymmetriesCommute`, i.e.
Theorem 1(iii) (`SimpleGraph.SimplicialModeHamiltonian.freeFermionSolution_of_cycleSymmetry_commute`;
the projectors: `SimpleGraph.SimplicialModeHamiltonian.exists_modeSectors_of_cycleSymmetry_commute`,
E16).

The Lean sum runs to `r = deg z_{G,J}`, as item 4 requires. Not certified: the sum over
sectors without those two hypotheses.

### E16. Theorem 2: reality, positivity, simplicity, top charges, non-degeneracy

Location: Definition 9 (L597-603), L604-608, L2097, L2129, the ladder proof (L2058-2104).

Problem. v1 does not prove that the roots `x` of `Z_{G,J}` (with `x = -u^2`) are real
and negative, which is what makes the `u_{J,j}` real, nor that
`Z_{G\Ks}(-u^2) Z'_G(-u^2) > 0`, both needed for
`N_{J,j}` to be a positive real and for `psi_{-j} = psi_j^dagger`; nor that
`Q^(k) Pi_J = 0` above `deg z_{G,J}`; nor that `z_{G,J}` has `alpha(G)` distinct roots
(L2129). The literature cited (L604-608) covers only the `J`-free, even-hole-free case.

Correction. A single hypothesis, that `z_{G,J}` and `z_{G\Ks,J}` have no common root
(equivalently, over `ℝ`, are coprime), gives all of these except the count: `z_{G,J}` then
has `deg z_{G,J}` distinct roots, which can be fewer than `alpha(G)` (E15, item 4; U1: in
the `J = -1` sector of `C_4`, `z = 1+4x` and `z_K = 1+2x` are coprime and `deg z = 1 < 2`;
hand computation).

Certified, for matrix algebras `Matrix (Fin d) (Fin d) ℂ`, a claw-free `G`, a
simplicial clique `Ks` and a `SimpleGraph.SimplicialModeHamiltonian.ModeSector` with
`Pi != 0`:
- `SimpleGraph.SimplicialModeHamiltonian.ModeSector.root_real_neg`: a complex root `x`
  of `z_G` with `z_K(x) != 0` is real and negative.
- `SimpleGraph.SimplicialModeHamiltonian.ModeSector.radicand_pos`: for such a real root,
  `z_K(x) z_G'(x) > 0`; `SimpleGraph.SimplicialModeHamiltonian.ModeSector.derivative_eval_ne_zero`:
  the root is simple.
- `SimpleGraph.SimplicialModeHamiltonian.ModeSector.charge_mul_Pi_eq_zero`:
  `Q_G^(k) Pi = 0` for every `k > deg z_G`.
- `SimpleGraph.SimplicialModeHamiltonian.ModeSector.exists_nondegenerate_of_isCoprime`:
  if `z_G` and `z_K` are coprime in `ℝ[X]`, there is `Nondegenerate` data with
  `r = deg z_G`; `SimpleGraph.SimplicialModeHamiltonian.ModeSector.exists_nondegenerate_of_fta`
  is the same with "no common complex root" and the Fundamental Theorem of Algebra for
  `ℂ` as a hypothesis (Mathlib's proof of it lies outside the import closure built here, so
  that module cannot import it).
  `SimpleGraph.SimplicialModeHamiltonian.ModeSector.card_roots_zG_eq_natDegree`:
  `z_G` has `deg z_G` roots (counted with multiplicity) under coprimality.

Certified, conditional on Theorem 1(iii): a `ModeSector` for the joint projectors of the
`J`'s. In `Matrix (Fin d) (Fin d) ℂ`, for claw-free `G` and a simplicial clique `Ks`,
`SimpleGraph.SimplicialModeHamiltonian.exists_modeSectors_of_cycleSymmetry_commute`
builds, from the hypothesis `H.frustration.CycleSymmetriesCommute` (that is,
`[J_{C_0}, J_{C_1}] = 0` for even-hole carriers: Theorem 1(iii)), a finite set `Lambda` of
tuples `l` and Hermitian idempotents `Pi_l != 0` that are pairwise orthogonal, satisfy
`sum_l Pi_l = 1` and `J_{C_0} Pi_l = l(<C_0>) Pi_l`, and for each `l` a
`SimpleGraph.SimplicialModeHamiltonian.ModeSector` with projector `Pi_l`,
`zG = SimpleGraph.sectorPolynomial H.coupling {} l` and
`zK = SimpleGraph.sectorPolynomial H.coupling Ks l`. The hypothesis is
`SimpleGraph.PauliFrustrationRepresentation.CycleSymmetriesCommute`; Theorem 1(iii) itself
is open (E5, U6, U8). The supporting declarations are
`exists_joint_spectral_projections` (for pairwise commuting Hermitian matrices: orthogonal
Hermitian idempotents `P l != 0` with `sum_l P l = 1`, `J i P l = l i P l`, every matrix
commuting with all `J i` commuting with every `P l`, and `l` in the index set exactly when the
joint eigenspace is nonzero),
`SimpleGraph.PauliFrustrationRepresentation.exists_jointSpectralProjections_of_cycleSymmetry_commute`
(the same for the cycle symmetries, with `hstar` and `hJ`; no claw-freeness, no simplicial clique) and `SimpleGraph.SimplicialModeHamiltonian.jointModeSector` (the
`ModeSector` of a Hermitian idempotent with `J P = l P` that commutes with everything
commuting with the `J`'s; it takes no commutation hypothesis on the `J`'s). The hypotheses
are satisfiable with `J` acting non-trivially: on a three-qubit model with frustration graph
the 4-cycle, `SimpleGraph.CycleSymmetrySectorsExample.ham_cycleSymmetriesCommute` and
`SimpleGraph.CycleSymmetrySectorsExample.exists_two_sectors` (two sectors, `J = +-1`).

Not certified: that coprimality fails in the example of U1 (hand computation);
Theorem 1(iii), hence the sector construction without a hypothesis; the statements for
algebras other than `Matrix (Fin d) (Fin d) ℂ` (the proofs use the Hilbert-Schmidt trace
form). The assembly of these results into Theorem 2 is E17.

### E17. Theorem 2: cross-sector relations, the sum over sectors, and the assembly

Location: Theorem 2, L1248-1264 (in particular `[Pi_J, psi_{J',j}] = 0` for all `J`, `J'`, `j`,
L1259-1263); Lemma 14, L1306-1313; "Combining Lemma 13, Lemma 14, and Lemma 15 proves
Theorem 2", L1322.

Problem. v1 assembles Theorem 2 in one sentence (U2). Not argued: the case `J != J'` of
Lemma 14, whose proof (L2058-2104) computes within one sector and writes `delta_{J,J'}` in the
last display (L2101), and the commutation `[Pi_J, psi_{J',j}] = 0` of Theorem 2 for `J != J'`;
the sum over sectors, which needs `sum_J Pi_J = 1`; and that the objects (`Pi_J`, `u_{J,j}`,
`N_{J,j}`, `psi_{J,j}`) are the specific ones of Definition 9 and L2097 rather than
existentially chosen. The non-degeneracy and index-range defects are E15, E16 and U1.

Certified, conditional on two premises beyond v1's setup, for
`H : G.SimplicialModeHamiltonian Ks (Matrix (Fin d) (Fin d) ℂ)` with claw-free `G` and
simplicial clique `Ks`:
`SimpleGraph.SimplicialModeHamiltonian.freeFermionSolution_of_cycleSymmetry_commute`.
- `hJ : H.frustration.CycleSymmetriesCommute`, Theorem 1(iii) as a hypothesis (open: E5, U6,
  U8). It is used only to produce the joint spectral projectors.
- `hND`: for every `l : G.EvenHoleDeformationClass → ℝ` that is a joint eigenvalue tuple of the
  `J_{C_0}` (some `v != 0` with `J_{C_0} v = l(<C_0>) v` for every even-hole carrier `C_0`, and
  `l = 0` on every class that contains no even-hole carrier),
  `IsCoprime (SimpleGraph.sectorPolynomial H.coupling {} l) (SimpleGraph.sectorPolynomial H.coupling Ks l)`.
  This is the form of v1's tacit "no common root" (E16, U1) that avoids the Fundamental Theorem
  of Algebra: coprime real polynomials have no common complex root
  (`ModeSectorPositivity.aeval_ne_zero_of_isCoprime`); the converse is
  `ModeSectorPositivity.isCoprime_of_forall_aeval_ne_zero`, with the Fundamental Theorem of
  Algebra as a hypothesis.
Conclusion, with the objects fixed by formulas (`N`, `epsilon`, `psi` are bound by `exists`
only to be named): the finite set `Lambda` of joint eigenvalue tuples that occur, and the
projectors `Pi_l` of `SimpleGraph.SimplicialModeHamiltonian.exists_modeSectors_of_cycleSymmetry_commute` (E16), each with a
`ModeSector` of `zG = z_{{},l}`, `zK = z_{Ks,l}`; in every sector `r_l = deg z_{{},l}` distinct
positive `u_{l,j}` with `z_{{},l} = prod_j (1 + x/u_{l,j}^2)`, `T(u) T(-u) Pi_l = 0` at
`u = u_{l,j}` and `z_{Ks,l}(-u^2) z_{{},l}'(-u^2) > 0` there;
`N_{l,j} = 4 u_{l,j} sqrt(z_{Ks,l}(-u^2) z_{{},l}'(-u^2)) > 0`, `epsilon_{l,j} = 1/u_{l,j}`,
`psi_{l,j} = N_{l,j}^{-1} Pi_l T(-u_{l,j}) chi T(u_{l,j})`; for all `l`, `l'` in `Lambda`,
`Pi_l psi_{l',k} = psi_{l',k} Pi_l = delta_{l,l'} psi_{l',k}` (so `[Pi_l, psi_{l',k}] = 0`), and
`[Pi_l, psi_{l',k}^dagger] = 0` (stated as a commutation only);
`{psi_{l,j}, psi_{l',k}^dagger} = delta_{l,l'} delta_{jk} Pi_l`,
`{psi, psi} = 0`, `{psi^dagger, psi^dagger} = 0`; `[H, psi_{l,j}] = 2 epsilon_{l,j} psi_{l,j}`,
`[H, psi_{l,j}^dagger] = -2 epsilon_{l,j} psi_{l,j}^dagger`;
`H = sum_l (sum_j epsilon_{l,j} [psi_{l,j}, psi_{l,j}^dagger]) Pi_l`.
Supporting declarations: the cross-sector statements
`SimpleGraph.SimplicialModeHamiltonian.exists_crossSectorModes_of_cycleSymmetry_commute`
(same premises), which use only `Pi_l Pi_{l'} = 0`
(`SimpleGraph.SimplicialModeHamiltonian.ModeSector.Orthogonal`,
`SimpleGraph.SimplicialModeHamiltonian.ModeSector.Orthogonal.commute_psiPlus`,
`SimpleGraph.SimplicialModeHamiltonian.ModeSector.Orthogonal.psiPlus_anticomm_psiMinus`,
`SimpleGraph.SimplicialModeHamiltonian.ModeSector.Family.psi_anticomm_star_psi`); the explicit
mode `SimpleGraph.SimplicialModeHamiltonian.explicitIncognitoMode` (of which `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.psiPlus`
is an instance, `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.psiPlus_eq_explicitIncognitoMode`);
and in one sector, from raw non-degeneracy data,
`SimpleGraph.SimplicialModeHamiltonian.ModeSector.solution_on_sector`, with
`SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.commutator_psiPlus` and
`SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.commutator_psiMinus`.
The inner index runs over `Fin (r_l)`, `r_l = deg z_{{},l}`, not `alpha(G)` (E15, item 4; U1).
`psi_{J,-j}` of v1, never defined there (E9, item 1), is `psi_{J,j}^dagger`.

Non-vacuity: all premises hold, and the conclusion is computed (`Lambda = {0}`, `r = 1`,
`u = 1`, `psi = sigma^+`, `H = Z = [psi, psi^dagger]`), for the one-vertex model with `Ks = {0}`,
`H = Z`, `chi = X`, which has no even hole:
`SimpleGraph.FreeFermionSolutionExample.freeFermionSolution_ham1`,
`SimpleGraph.CrossSectorRelationsExample.exists_crossSectorModes_ham1`. For that model
`hJ` is vacuous (every `J` is `0`). The 4-cycle model of E16 satisfies `hJ` and has two
sectors, but fails `hND` in the sector `J = +1` (U1, hand computation), so no committed
example verifies `hJ` and `hND` with a non-trivial `J`.

Not certified: Theorem 1(iii), hence the statement without `hJ`; that v1's Theorem 2 as printed
fails without `hND` (the `C_4` computation of U1); the statements for algebras other than
`Matrix (Fin d) (Fin d) ℂ`.

## Part II. Identified, not yet certified

No entry below is certified: no Lean statement establishes the defect or the correction it
proposes. Part I entries certify related corrected statements, and the `Lean` paragraph of an
entry points to them by entry number (U1 to U3: E4, E6, E8, E9, E11, E12, E14 to E17), naming
the declarations where useful; those results are certified in the cited Part I entries and
nowhere in this part. Where a Lean declaration records related groundwork (U6, U9) it is
named as groundwork, and what it does not cover is stated.

### U1. Theorem 2 as printed: counterexample and connectedness

Location: Theorem 2, L1248-1264; the sum `j = 1..alpha(G)` in Theorem 2, Lemma 15
(L1315-1319), Result 1 (L97-105); the ladder proof (L2088-2098). Connectedness is
assumed in Result 1 (L99, "connected, claw-free") and Result 2 (L112, "connected,
simplicial, claw-free"); it is not mentioned in Theorem 2 (L1248), Lemmas 13-15 or
Theorem 3 (L1328), which say "SCF Hamiltonian" or nothing.

Problem. Per symmetry sector `J`, v1 silently needs that `Z_{G,J}` and
`Z_{G\Ks,J}` have no common root (E16 certifies the non-degeneracy consequences of
this hypothesis in matrix algebras, on a `ModeSector`; the corrected Theorem 2 is proved
conditional on Theorem 1(iii) in E17).
Counterexample to the printed statement: `G = C_4` with uniform couplings and `Ks`
an edge (claw-free, simplicial, connected). In the sector `J = +1`,
`z = (1+2x)^2` and `z_K = 1+2x`, so `N = 0` and `psi` is undefined. In the sector
`J = -1`, `z = 1+4x` has degree `1 < alpha(G) = 2`, so the sum over `j = 1..alpha(G)`
is ill-defined. (Hand computation from Lemma 11: `Z = 1 + 4x + 2(1+J)x^2`,
`J^2 = 1`; confirmed by exact computation outside Lean.) For disconnected `G` the
component not containing `Ks` contributes common roots of `Z_G` and `Z_{G\Ks}`, so
`N = 0`; Theorem 2 and Lemmas 13-15 omit connectedness, which is subsumed by the
no-common-root hypothesis.

Correction. Add the hypothesis "no common root of `Z_{G,J}` and `Z_{G\Ks,J}`" and
replace `alpha(G)` by `deg Z_{G,J}` in each sector.

Lean. Nothing in this entry is certified. Related certified results, in Part I: the ladder
and reconstruction statements over `Nondegenerate` data with `r = deg z_G` (E9, E15), which
E16 derives from coprimality; and the corrected Theorem 2, with `hND` and `r_l = deg z_{{},l}`
modes in the sector `l`, conditional on Theorem 1(iii) (E17,
`SimpleGraph.SimplicialModeHamiltonian.freeFermionSolution_of_cycleSymmetry_commute`). Not
certified: the counterexample itself, that the printed statement fails without the
hypothesis, and the corrected Theorem 2 without Theorem 1(iii).

### U2. Theorem 2: omitted steps of "Combining Lemmas 13-15 proves Theorem 2"

Location: L1322.

Problem. Not shown: that the `J`'s are Hermitian and commute (Theorem 1(iii), and
`h_C = h_{C_a} h_{C_b}` Hermitian because the colour classes commute); that the joint
spectral projectors `Pi_J` exist; that `Pi_J` commutes with `T` (Theorem 1(ii)) and with
`chi` (E8), hence `[Pi_J, psi] = 0`; that `Z_G Pi_J` and `Z_{G\Ks} Pi_J` reduce to ordinary
polynomials; the cross-sector `delta_{J,J'}`.

Lean. Nothing in this entry is certified. Related certified results, in Part I:
`[chi, J] = 0` (E8); `[H, J] = 0` (E4); the reduction of `Z_{G\W} Pi` to a polynomial (E6);
existence of joint spectral projections for commuting Hermitian matrices
(`exists_joint_spectral_projections`, E16); and, conditional on the hypothesis
`SimpleGraph.PauliFrustrationRepresentation.CycleSymmetriesCommute` (Theorem 1(iii)), the joint
projectors `Pi_J` with `sum_J Pi_J = 1` and a `SimpleGraph.SimplicialModeHamiltonian.ModeSector`
at each of them (E16), the cross-sector relations, the sum over sectors and the assembly (E17).
Not certified: Theorem 1(iii) (needed for the `J`'s to commute), hence all of these without
that hypothesis.

### U3. Theorem 3: statement, and the operator identity on a sector

Location: L1328-1336.

Problem. (a) The statement is existential; the content is in the specific matrix of
Eq. (decoratedtree), "proposed" only at L1434. (b) The left side carries `Pi_J` but
the right side does not; the correct reading is
`ad^k chi . Pi = sum_P c_P h_P . Pi`, since `J` need not commute with `h_P`.
(c) The statement silently needs `[H, Pi] = 0`, i.e. `[J, H] = 0` from Theorem 1(ii).
(d) The section is titled "Polynomial Divisibility" but no divisibility identity is
stated.

Lean. Nothing in this entry is certified. The related corrected statements are certified in
Part I. (c): E4 (`SimpleGraph.PauliFrustrationRepresentation.hamiltonian_commute_generalizedCycleSymmetryOp`)
and E12 (`SimpleGraph.PauliCliqueHamiltonianRepresentation.commute_physicalHamiltonian_of_mem_adjoin`,
which discharges `[H, Pr] = 0` for `Pr` in the algebra generated by the `J_c`). (b) and the
content of (a): E12, `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_commute`,
`[H, .]^k chi * Pr = (-2)^k sum_P ((A_lambda^k)_{{j*},P}) h_P Pr` for any `Pr` with `[H, Pr] = 0`
and `J_c Pr = lambda_c Pr`, with `A_lambda` the corrected matrix of E11, and its
algebra-generated and existential forms `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_cycleAlgebra` and
`SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_commute_exists`; for `Pr = Pi_J`, the joint spectral projector, as a single
statement, under the hypothesis `SimpleGraph.PauliFrustrationRepresentation.CycleSymmetriesCommute` (Theorem 1(iii)) only,
`SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_cycleSymmetry_commute`.
(d): E14, `SimpleGraph.krylovRow_mul_sectorIndepSeries`, a closed form of the Krylov rows for
the corrected matrix and any number of hole classes, as an identity of power series with
`Z_U = SimpleGraph.sectorIndepSeries` as defined there.
Not certified: that this is the divisibility of the generalized characteristic
polynomial that the section title refers to (E14, "Not certified"); Theorem 3 over the
joint spectral projectors without the hypothesis `SimpleGraph.PauliFrustrationRepresentation.CycleSymmetriesCommute` (Theorem 1(iii);
E16), which the complete family of sector projectors needs.

### U4. Theorem 3, the third case of the induction step

Location: L1514-1576.

Problem. L1514 announces three cases for `h_j` anticommuting with `h_P`, `j not in P`
(Lemma 2, L653). Only (b.i) (L1515-1518) and (b.iv) (L1520-1576) are treated; the
third, the one-neighbour extension (b.iii of Lemma 2, L661), which carries the
unit weights of Eq. (decoratedtree), is not.

### U5. Majorana construction

Location: L1394-1430.

Problem. `ad^k chi` with `ad = [iH, .]` is already Hermitian, so the factor
`i^{(j mod 2)}` in `gamma_j` (L1415) makes the odd modes anti-Hermitian.
Positivity of `M` is argued with the full trace (L1406-1409) although `M` depends on
the sector; `tr(Pi .) / tr Pi` should be used.

Lean. None. The positive definiteness of `M` and the Majorana modes are not
formalised in any case, with or without even holes. The Lean statements of E1 are the
anticommutator identity of Corollary 12 only, which precedes this construction in v1
(L1341-1392).

### U6. Termination of the search process and the rerouting update (C31)

Location: L1157-1167 (update), L1190-1191 (termination).

Problem.
1. (C31) keeps `(O_v, V_v, U_v)` for every `v in W^(i+1) \ {j}`. Arcs into `j''`
   come only from `j` and `j'`, but arcs from obstruction-class vertices into the
   deleted source `j'` are not excluded. Such a `v` has no arc in `D^(i+1)`, yet
   `U_v != {}` and `v` is not unobstructed in the intrinsic sense
   (`V_f = U_f = {}`). This breaks "no unobstructed deformation implies every vertex
   has exactly one outgoing arc" (L1158). Either such `v` do not exist or the
   search must be rerun for them.
2. The termination argument needs four ingredients: `|W|` odd; the source class stays
   strictly larger after removing one vertex from each class; pigeonhole for `j''`
   with two incoming arcs; and the identification of "no outgoing arc" with the
   intrinsic `V_f = U_f = {}`, which fails in the situation of item 1. "The
   unobstructed deformation is trivial" when the obstruction set is empty
   (L1191) is inaccurate: it is nonempty.

Lean groundwork (ingredients 2 and 3 only):
`SimpleGraph.ArcGraph.exists_two_incoming` (odd order, bipartite by pairing type,
every vertex with an out-arc: some vertex of the smaller class has two incoming
arcs from the larger class) and `SimpleGraph.ArcGraph.odd_and_lt_after_removal`
(removing one vertex from each class keeps oddness and the strict class-size
inequality). Not covered: oddness of `|W|`, item 1, and the identification in
item 2.

### U7. Appendix proofs of Lemmas 8, 9, 10 (repo Lemmas 14, 15, 16)

Location: Lemma 8 (iv), L1853-1874; Lemma 9, L1876-1921; Lemma 10, L1192-1200.

Problem.
1. Lemma 9, appendix: only statement (i) is argued (the concatenation and the rerun
   are fixed-pairing type). Statements (ii)-(iv) at step `i+1` are dismissed with
   "closely follows" (L1889) and "the remainder of the proof follows the proof of
   the base case" (L1921). The tree `T^(i)` (L1917) is introduced but its use is
   not made precise.
2. Lemma 10: the steps "`u in C^(g)` since `u, u'` are in the same colour class of
   `C'` and `u in U^(r,s)`" and "`u = k_{s-2}^(r)` and `u = j_{t-1}^(g)`" compress an
   occurrence-indexed transport argument, and rely without saying so on Lemma 7-type
   reverse-clone data.
3. Lemma 8 (iv) is a long case analysis of which only parts are written out.

### U8. Theorem 1(iii): remaining proof omissions

Location: L1203-1241.

Problem.
1. `|W n dO|` is odd (L1234): no argument. The natural proof is the induction
   `|W n dO_j^(i+1)| = |W n dO_{j'}| + |W n dO_j| + 1 + [O_j = {}]`, which needs
   Lemma 9(iii) at the new state to exclude previously deleted `W`-vertices from
   new paths.
2. "`h_{P^(r)}` and `h_{C^(r-1)}` anticommute by construction" (L1227) is true but
   unproved (the degrees are 3, 4, ..., 4 for the `j`'s and 2 for the `k`'s).
3. Pairing involution (L1241): the deformation chosen for `(C~, C~')` must be the
   reverse of `O`; this is not argued, and the search is explicitly
   nondeterministic. A sign-reversing relation that is not a matching does not give
   a zero sum.
4. For several paths the deformed hole is `C^(m) = C + (+)_r P^(r)` (L984-986), not
   `C + dO` with `dO` the union of the paths (L990), unless the paths are pairwise
   vertex-disjoint; paths may share vertices (Corollary 8, L1053). The single-path
   example writes `C~ = C + P` (L965). This is why
   `SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.lemma12_carrier_of_residualData`
   (E5) speaks about `C^(m)`.

### U9. Definition 8: existence of `chi`

Location: Definition 8, L588.

Problem. The existence of a Pauli `chi` with the prescribed commutation relations
(anticommuting exactly with the terms of the simplicial clique) can require an
ancilla qubit; this is assumed implicitly.

Lean groundwork: `SimpleGraph.PauliShiftModel.scaledRepresentation` is a concrete
representation of any graph's frustration structure; it does not address `chi`.

### U10. Lemma 4 without its claw-free hypothesis

Location: Lemma 4, L736.

Problem. Stated without the claw-free hypothesis; it relies on the section-level
assumption through Lemma 3 and Corollaries 1-2. `SimpleGraph.lemma9` carries
`G.IsClawFree`.

## Part III. Typographical (identified, not certified)

Each was read off `main.tex`; none has a Lean statement.

| line | printed | intended |
|---|---|---|
| 1006 | `j_{s-1}^(r) ≺_{C^(r,s-1)} j_{s-1}^(r)` (clone relation) | `j_{s-1}^(r) ≺_{C^(r,s-1)} k_{s-1}^(r)` |
| 1070 | "`u` is in `C_a \ C'`" (proof of Corollary 9) | inconsistent with `u in C'_d`, hence `u in C'`, earlier in the same proof; the intended membership is not determined by the printed text |
| 1137 | "If `P n W_i` is non-empty, then `P` is a path and we update" | "empty" |
| 1143 | "`U^(r,s)(O_t)` as the set in Def. `singlevertexdeformation`" | Def. `anticommutingdependentsubsets` (Definition 20) |
| 1439 | case 2 of Eq. (decoratedtree): `P = P \ {j}` | `P' = P \ {j}`, `j` the terminal vertex of the source `P` |
| 1707 | "Suppose that `u` is in `P^(r)` ..." (the case `u in P^(r)` is treated at L1705) | "is not in `P^(r)`" |
| 1974 | "In this case `\|S\| = \|S\|`" | `\|S\| = \|T\|` |
| 2029 | `K_j = Gamma[G] \ (Ks \ {j})` | `Gamma[j] \ (Ks \ {j})` |
| 2088, 2092, 2093 | `Z_{G \ K}` | `Z_{G \ Ks}` |

## Part IV. Checked, no defect found

- Theorem 1(i) pairing (L876-902): the component is fixed as a function of
  `S + S'`, which the toggle leaves invariant, so the pairing is an involution.
  Certified: `SimpleGraph.chosenOddComponent_symmDiff`, `SimpleGraph.chargePairToggle_involutive`,
  `SimpleGraph.PauliFrustrationRepresentation.paperTheorem1i`.
- Definition 11 (bubble wand, L692-698) allows `i = 0` (labelling starts at
  `j_0 = j*`), and the proof of Theorem 3 uses `0 <= s` (L1520).
- v1 Lemma 7 (repo Lemma 12, L1122), endpoint clause. The appendix proof
  (L1757-1799) uses only that a `C'`-neighbour of the last removed vertex `k` that is
  not adjacent to the introduced vertex `j` would contradict `k` being an endpoint of
  its path (L1795); the palindromic example (L957-966) has two `C'`-neighbours of the
  last removed vertex, adjacent to the introduced vertex, that are not on the path.
  The repository's transcription demanded all `C'`-neighbours of `k` on the path and
  is uninhabited on claw-free graphs
  (`SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.not_nonempty_lemma12Data_of_clawFree`);
  the residual form is
  `SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.lemma12_of_residualData`.
  The defect is in the repository, not in v1 (`docs/PAPER_FIDELITY.md`, Audit
  2026-10-26).
- The graph `G*` of Definition 17 (L846) is claw-free when `G` is claw-free and `K` is
  a simplicial clique: `SimpleGraph.IsSimplicialClique.isClawFree_adjoinRootAt`.
