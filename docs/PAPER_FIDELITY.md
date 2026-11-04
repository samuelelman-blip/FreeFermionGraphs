# Manuscript fidelity gates

This document records the acceptance criteria for claiming that a Lean theorem
formalises a numbered result of *A Unified Graph-Theoretic Framework for
Free-Fermion Solvability*.

A successful build establishes type correctness. It does not by itself show
that the formal statement has the same hypotheses, quantifiers, deformation
stage, provenance, or conclusion as the manuscript.

Numbering. This document follows the revised manuscript of 14 July 2026, which is
not available. Checks against the source use arXiv 2305.15625v1. The
correspondence of numbers is in [`V1_NUMBERING.md`](V1_NUMBERING.md), and defects
of v1 found during formalisation are in [`V1_ERRATA.md`](V1_ERRATA.md). Where this
document says "Lemma n", the v1 equivalent is given at first use; Section
"Audit 2026-10-26" records the machine-checked corrections to the status of
Lemmas 11, 12, 14, 15 and 16 below (sections A-D), the corrections to earlier statements
(section E), the premise table of the paper-facing declarations (section F) and what is not
formalised (section G), and Section "Audit 2026-10-30" records the proof of
Theorem 1(iii), the final forms of Theorems 2 and 3, and the open fidelity items.

Status (2026-11-03). Theorem 1(iii) is proved
(`SimpleGraph.PauliFrustrationRepresentation.paperTheorem1iii`) by a route that does not use
the sections "Lemma 11(b)", "Finite Definition 19 history", "Lemma 14", "Lemma 15" and
"Lemma 16" below, nor v1 Lemmas 5-10 and 17 on which they are modelled. Those sections keep
the repository state of Audit 2026-10-26 and are retained as audits of that interface layer;
their conclusions about the layer are unchanged. No declaration named for Theorems 1-3,
Corollary 1 or Lemmas 1-5, 17, 18 depends on it (section H).

## Merge gates

A pull request touching a numbered manuscript result must identify:

1. the exact manuscript statement or proof sentence being formalised;
2. the Lean object corresponding to every manuscript object;
3. the deformation stage of every hole and degree expression;
4. the provenance of every new structure field;
5. any additional premise not present in the manuscript;
6. the exact paper-facing theorem that the change helps prove.

An unqualified theorem name such as `paperLemma14` is reserved for a theorem
with no additional premise beyond the manuscript setup. Conditional bridges
must retain names of the form `paperLemma14_of_...`.

## Provenance classes

| Class | Meaning | Permitted in an unqualified paper theorem |
|---|---|---|
| D | Literal definition or algorithm data from the manuscript | Yes |
| E | Derived from D by an audited theorem | Yes |
| M | Intermediate claim explicitly proved in the manuscript | Only after it is derived from D/E |
| B | Boundary certificate standing in for an unformalised manuscript argument | No |

## Recurring checks

- **Stage check:** degrees compared in one argument must refer to definitionally
  equal hole objects, or an explicit carrier/index equivalence theorem must be
  supplied.
- **Quantifier check:** pairwise terminal claims must not be strengthened to
  per-arc claims unless the strengthening is separately proved.
- **Orientation check:** public conclusions must be invariant under reversing
  or cyclically shifting an indexed hole.
- **Overlap check:** original-hole and prime-hole colour memberships are not
  globally exclusive.
- **Two-sided path check:** a fixed-pairing deformation may contain both
  `acPaths` and `bdPaths`.
- **Finiteness check:** a finite Definition 19 prefix must not require data
  outside its declared block count.
- **Boundary-case check:** empty deformations, first blocks, the initial-tether
  stopping branch, later Definition 20 stopping, and empty inputs to a
  corrective concatenation must be covered.
- **Dependency check:** a proof of Lemma 14 may use Lemmas 7-13, but it may not
  consume a field that already assumes a conclusion of Lemma 14(iv). A proof
  of Lemma 15 may consume literal histories at successive search states, but no
  state or transition may contain any of the four Lemma 14 conclusions.

## Lemma 11(b)

The manuscript concludes that for `u ∈ U^(r,s)` commuting with the path
operator,

- `Delta_(C^(r))(u) = 4`; and
- an earlier dependent anticommuting vertex lies in the same fixed-pairing path
  component.

The current theorem

```lean
PaperFidelity.paperLemma11b_of_historyContext
```

states the degree on the exact final hole `D.finalHole`, but still takes
`D.Lemma11AHistoryContext` as an additional premise. That context contains
history and endpoint data not yet constructed from the literal finite
Definition 19 deformation. There is therefore no unconditional theorem named
`paperLemma11b`.

Status correction (Audit 2026-10-26, section D). The history types behind the
`later` cases of the `Lemma11AHistoryContext`-style contexts are uninhabited:
`SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FullDefinition19Lemma11AHistoryData.isEmpty`,
`SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideLemma11AHistoryData.isEmpty`,
`SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.MixedSideFullDefinition19Lemma11AHistoryData.isEmpty`.
Lemma 11 (v1 Lemma 6) on the finite Definition 19 types therefore covers one
step, and the versions through a nonempty prefix of earlier blocks say nothing.

## Finite Definition 19 history

The manuscript deformation is finite. Legacy `PathBlockHistory` values are
total over `Nat`, so they are stronger than the manuscript even when later
proofs use only a bounded prefix.

The replacement finite layer uses `FiniteMixedSideSearchTrace`, with:

- a positive finite `blockCount`;
- one `DeformationSide` per block;
- an order-preserving, surjective local-to-flattened step map;
- exact output-path correspondence;
- original-hole provenance for removed vertices.

The repository constructs bounded mixed-side execution data and uses it
throughout the finite Lemma 11, Lemma 14, and Lemma 15 developments. Legacy
total histories remain available internally but are not acceptable final
premises for an unqualified paper theorem.

Status correction (Audit 2026-10-26, section D). The "positive finite
`blockCount`" is in fact `1`: every `FiniteMixedSideSearchTrace` has exactly one
block with exactly one step
(`SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.blockCount_eq_one`,
`SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.flattened_stepCount_eq_one`).
The finite layer therefore describes single-step runs only; v1's Definition 19
has arbitrary numbers of blocks and steps.

## Lemma 14

### Status correction (Audit 2026-10-26)

The theorem named below is a proved Lean theorem. The earlier description of it as
exact on the literal initialized finite history overstated its coverage. Each
nonempty run of an `InitializationFiniteMixedSideLemma14History` is a
`SimpleGraph.FixedPairingPathFamily.ObstructionSearchInitialization.NonemptyFiniteMixedSideOSExecution`,
which carries a `FiniteMixedSideSearchTrace` (its `literal.trace`), and every such
trace has exactly one block and exactly one single-vertex deformation
(`SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.blockCount_eq_one`,
`SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.flattened_stepCount_eq_one`).
Hence `SimpleGraph.FixedPairingPathFamily.ObstructionSearchInitialization.InitializationFiniteMixedSideLemma14History.paperLemma14`
covers histories whose nonempty runs are single-step; v1 Lemma 8 (repo Lemma 14,
L1174) concerns arbitrary numbers of blocks and steps. The cause is the interface
field `SimpleGraph.FixedPairingPathFamily.ACHoleStepGeometry.before_subset`, which is false in v1 after the first
step (Audit 2026-10-26, section D). The per-block `localData` of a trace is a
`FullDefinition19Lemma11AData`, whose fields are supplied rather than derived, so
the sub-fields of `core` that come from it are class B, not class D. Status:
proved on a degenerate interface type; not an exact formalisation of v1 Lemma 8.

### Manuscript conclusion

`PaperLemma14Conclusion` represents the exact four conclusions:

1. every initialized output is a possibly empty fixed-pairing deformation;
2. the obstruction graph is bipartite by pairing type;
3. same-pairing deformations are pairwise path-disjoint;
4. every target has at most two incoming arcs and, for two distinct incoming
   arcs, the target is the unique member of exactly one final dependent set.

### Paper-facing theorem

The finite manuscript endpoint is

```lean
InitializationFiniteMixedSideLemma14History.paperLemma14
```

with hypotheses

```lean
(H : I.InitializationFiniteMixedSideLemma14History)
(hclaw : G.IsClawFree)
```

and conclusion `PaperLemma14Conclusion I`.

`InitializationFiniteMixedSideLemma14History` represents the initialized
Definition 19/20 search history in the finite trace model. It is the manuscript
setup for the lemma, not a structure containing any of the four conclusions; but
see the status correction above: its runs are one-block, one-step traces.

### Provenance audit

The fields and their classes are:

| Lean data | Manuscript object | Class |
|---|---|---|
| `core` | initialized finite deformations, obstruction/dependent outputs, pairing labels, terminal path, nearest-target rule | D for the algorithm data; the per-block `localData` is class B (see status correction) |
| `W_subset_Cprime` | Definition 20 inclusion of initializers in the fixed prime carrier | D |
| `terminal.alternation` | local `j-k-j-k` colour alternation of the terminal path component | D |
| `FiniteMixedSideIncomingTerminalHistory.empty` | empty initialized output branch | D |
| `FiniteMixedSideIncomingTerminalHistory.positive` | positive stopping branch and exact final-hole single-vertex deformation | D |
| `FiniteMixedSideCanonicalTerminalLink` | adjacent link emitted by the stopping rule | D |
| generated propagation derivation | finite sequence assembled by the literal `start` and `snoc` propagation constructors | D |
| even-index labels and odd path cardinality | induction from local alternation | E |
| target path commutation | finite Lemma 11(a), Corollary 11, and parity contradiction from the raw terminal clone | E |
| positive terminal degree three | path commutation, even-hole parity, and Lemma 7 | E |
| two-step clone-to-flank adjacency | induced-path adjacency from the canonical adjacent link | E |
| final same-centre/distinct-centre contradiction | terminal comparison and generated propagation trace | E |

The generated unequal-centre history is indexed by its resulting trace. A
witness is accepted only with
`FiniteMixedSideDistinctPropagationTrace.IsGenerated`, whose constructors are
the finite zero-hop start and one actual-block `snoc` step. Thus a free-standing
terminal-claw or endpoint-alternative certificate cannot enter the theorem.

### Boundary and stage checks

- Empty and positive executions are separate constructors.
- Positive target clones are extracted by case analysis on those constructors.
- The exact `manuscriptFinalHole` is used at the stopping stage.
- The first dependent predecessor is tied to block zero, whose initial carrier
  is proved equal to the initialized original hole.
- Every propagation hop names an actual finite ordered path block.
- Same-centre and distinct-centre cases are split by equality of the two actual
  staged clone centres.
- `PaperLemma14Conclusion` contains no history or terminal certificate.

### Internal bridges

The lower-level theorem

```lean
InitializationFiniteMixedSideExecutableLemma14Data
  .paperLemma14_of_executableData
```

is retained for modularity. Its data are constructed from
`InitializationFiniteMixedSideLemma14History` by
`toExecutableLemma14Data`; it is no longer the paper-facing endpoint.

`InitializationFiniteMixedSideTerminalCoreData` alone intentionally does not
determine a run of the nondeterministic obstruction search: it omits local
stopping and propagation choices. Requiring the explicit finite history is
therefore part of the manuscript algorithm setup, not an additional
mathematical hypothesis.

## Lemma 15

### Status correction (Audit 2026-10-26)

The corrective-update structure `ObstructionSearchReroutingTransition` is
uninhabited, for every pair of states:

- `SimpleGraph.FixedPairingPathFamily.ObstructionSearchReroutingTransition.isEmpty`
- `SimpleGraph.FixedPairingPathFamily.ObstructionSearchReroutingProcess.stepCount_eq_zero`
- `SimpleGraph.FixedPairingPathFamily.ObstructionSearchReroutingProcess.paperLemma15Conclusion_iff_state_zero`

Every `ObstructionSearchReroutingProcess` has `stepCount = 0`, and
`SimpleGraph.FixedPairingPathFamily.ObstructionSearchReroutingProcess.paperLemma15`
is `paperLemma14` at state `0`. The earlier description "exact all-state
conclusion on an explicit finite rerouting process" is withdrawn: the model of v1
Lemma 9 (repo Lemma 15, L1185) collapses to Lemma 14. The cause: v1 reruns the
surviving source `j` as `OS(O_{j'} || O_j, u, W \ {j})` (Eq. (C32), v1 L1166), a
search that starts from the nonempty deformation `O_{j'}` whose first path was
initialised by `j'`; the Lean model of one `OS` call starts from the empty
deformation with the source in its first path block (`source_mem_first`), and its
`avoidsOtherSources` excludes `j` from the first path of `j'`. Lemma 15 must be
rebuilt on an obstruction-search model that can start from a nonempty prefix. This
is a statement about the repository model, not about v1.

The tables and checks below describe the interface; the interface has no
instances beyond state `0`.

### Manuscript conclusion

The manuscript states that all four conclusions of Lemma 14 hold for
`{O_j^(i)}_{j ∈ W^(i)}` and `D^(i)` at every corrective search step `i`.
The Lean proposition

```lean
ObstructionSearchReroutingProcess.PaperLemma15Conclusion
```

is exactly

```lean
∀ i : Fin (P.stepCount + 1),
  PaperLemma14Conclusion (P.state i).initialization
```

and therefore preserves all four quantifier structures rather than replacing
them by a weaker global invariant.

### Paper-facing theorem

The theorem is

```lean
ObstructionSearchReroutingProcess.paperLemma15
```

with hypotheses

```lean
(P : ObstructionSearchReroutingProcess)
(hclaw : G.IsClawFree)
```

and conclusion `P.PaperLemma15Conclusion`.

The explicit finite process was intended to be the manuscript's nondeterministic
corrective search execution, not an additional graph-theoretic premise. By the
status correction above its type has only state `0`.

### State and transition correspondence

| Lean data | Manuscript object | Class |
|---|---|---|
| `ObstructionSearchReroutingState.initialization` | `{O_j^(i)}_{j ∈ W^(i)}`, dependent outputs, and `D^(i)` | D |
| `state.history` | literal finite Definition 19/20 histories specifying all nondeterministic searches at step `i` | D |
| `removedSource`, `removedObstruction` | the source/obstruction pair removed in the corrective update | D |
| `next_W` | `W^(i+1) = W^(i) \ {j',j''}` | D |
| `survivor`, `survivor_value` | inclusion of surviving vertices into the preceding obstruction graph | D |
| `retained_paths`, `retained_dependent`, `retained_arcs` | unchanged searches of Eq. (C31) | D |
| `ConcatenationBranch` | the empty/empty, empty/nonempty, or nonempty/nonempty cases of `O_(j',j)^(i)` in Eq. (C32) | D |
| `reroutingPrefix`, `prefix_is_concatenation` | exact optional concatenation `O_(j',j)^(i)` | D |
| `rerouted_continuation` | the finite rerun `OS(O_(j',j)^(i),u_(j,f)^(i),W^(i+1)\{j})` | D |
| survivor injectivity and deleted-vertex exclusion | value preservation and the set equation for `W^(i+1)` | E |
| `next_W_subset`, `next_W_ne` | strict decrease of the corrective initializer set | E |
| `rerouted_prefix_paths` | both parent path collections occur in the Eq. (C32) rerun output | E |
| all four Lemma 14 clauses at every state | application of the audited history-level Lemma 14 theorem | E |

The optional concatenation interface explicitly records path provenance because
`SearchDeformation` intentionally erases the dependent index equivalence
between concrete concatenated steps and its optional output. These containment
facts describe the literal prefix relation of Eq. (C32); they do not assert
same-pairing disjointness, bipartiteness, indegree bounds, or the dependent-set
alternative.

### Fidelity checks

- No state or transition contains `PaperLemma14Conclusion` or any one of its
  four clauses.
- The next initializer set is exactly the old set with the selected source and
  obstruction removed.
- All retained nodes preserve their underlying vertex and pairing label.
- Eq. (C31) and Eq. (C32) are represented separately.
- All four optional concatenation boundary cases are covered by the branch
  representation.
- The theorem quantifies over every finite state, including state zero; only
  state zero exists (status correction above).
- The theorem uses the exact `PaperLemma14Conclusion` at each state.
- The strict-decrease theorem is available for the subsequent termination
  argument but is not smuggled into the Lemma 15 conclusion.

The implementation does not claim that `ObstructionSearchInitialization` alone
deterministically computes the next state. The manuscript search is
nondeterministic at local selection points, so the explicit finite process and
its histories specify the chosen run.


## Lemma 16

### Status correction (Audit 2026-10-26)

On a claw-free graph no `PaperLemma16Trace` exists, and a trace carrying one is
never unobstructed:

- `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.not_nonempty_paperLemma16Trace_of_clawFree`
- `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.paperLemma16_hyps_inconsistent`
- `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.not_isUnobstructed_of_paperLemma16Trace`

Hence `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.PaperLemma16Trace.paperLemma16`
and `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.paperLemma16_of_terminalPathTransport`
are vacuous in the manuscript's claw-free setting. The earlier description "exact
unqualified theorem on an explicit completed finite Definition 19 trace" is
withdrawn. Further, on every trace `IsUnobstructed` is equivalent to an empty
dependent union
(`SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.isUnobstructed_iff_dependentUnion_eq_empty`),
so the criterion `U <= C^(m)` is trivial on these traces, and traces are
single-step (Lemma 14 status correction). The cause of the vacuity is the endpoint
clause of `Lemma12Definition19Data` (Audit 2026-10-26, section A), which
`toLemma12Definition19Data` below inherits. The corrected Lemma 12 is
`SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.lemma12_of_residualData`
(Audit 2026-10-26, section B); a corrected Lemma 16 built on it is not in the
repository.

### Manuscript conclusion

For an unobstructed fixed-pairing deformation, every Definition 20 dependent
vertex belongs to the terminal hole. The exact Lemma 12 criterion therefore
holds and supplies the palindromic reverse deformation.

### Paper-facing theorem

The theorem is

```lean
FiniteMixedSideSearchTrace.PaperLemma16Trace.paperLemma16
```

with hypotheses

```lean
(Y : X.PaperLemma16Trace)
(hclaw : G.IsClawFree)
(hunobstructed : X.IsUnobstructed)
```

and conclusion `Y.PaperLemma16Conclusion`.

`PaperLemma16Trace` contains only literal completed Definition 19 execution
data: an indexed presentation of the fixed prime hole, preservation of
consecutiveness by the local-to-flattened step map, and terminal component
maximality for each path block. It contains neither `dependentUnion ⊆
terminalHole`, a terminal outside-witness transport certificate, a
`Lemma12Definition19Data` value, nor a reverse run.

### Derived provenance

- `terminalPathTransportData` proves the Corollaries 9-10 occurrence argument
  from the actual finite block occurrences, side tags, path-family uniqueness,
  and pairwise path distinctness.
- `toLemma12Definition19Data` derives original-hole removal provenance, active
  path containment in the flattened boundary, and the endpoint-or-continuation
  alternative from the same trace.
- `dependentUnion_subset_terminal_of_unobstructed` combines the derived
  occurrence transport with Lemma 11(b) and unobstructedness.
- `FullDefinition19Deformation.lemma12` then constructs the reverse run.

The older theorem `paperLemma16_of_terminalPathTransport` remains an explicitly
conditional internal bridge. The unqualified theorem does not take its
transport or Lemma 12 certificates as premises. By the status correction at the
start of this section, the `Lemma12Definition19Data` constructed here, and hence
the whole chain, is uninhabited on claw-free graphs.

## Current manuscript coverage

Numbers are the repo's (revised manuscript); v1 equivalents are in
[`V1_NUMBERING.md`](V1_NUMBERING.md). Declarations are in namespace `SimpleGraph`
unless fully qualified; the full names are in the Audit 2026-10-26 section and in
`README.md`.

| Manuscript layer | Fidelity status | Declaration |
|---|---|---|
| Lemmas 6-9 (v1 Lemmas 1-4) | Exact or corrected graph-level statements (Lemma 8 with the premise `t not in {s} u C`) | `SimpleGraph.lemma6`, `SimpleGraph.IndexedInducedHole.lemma7`, `SimpleGraph.EvenHoleLabeling.CloneAt.lemma8`, `SimpleGraph.lemma9` |
| Lemma 10 (v1 Lemma 5) | Statement on the `FixedPairingPathFamily` interface; disjointness is carried by its fields | `SimpleGraph.FixedPairingPathFamily.lemma10` |
| Definition 14 | Combinatorial token-sliding charges and the operator charge | `SimpleGraph.PauliFrustrationRepresentation.tokenSlidingChargeOp` |
| Definition 15 | Combinatorial deformation closure and the operator symmetry | `SimpleGraph.PauliFrustrationRepresentation.generalizedCycleSymmetryOp` |
| Lemma 11(a)-(b) (v1 Lemma 6) | On the finite trace types: single step only; the positive-history types are empty | `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.blockCount_eq_one`, `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FullDefinition19Lemma11AHistoryData.isEmpty` |
| Corollary 11 (v1 Corollary 10) | Vacuous across blocks: the finite-history theorem takes a `FiniteMixedSideLemma11AHistoryData`, a type with no inhabitants. `SimpleGraph.FixedPairingPathFamily.Corollary11Property` is the statement (a `Prop`), not a theorem | `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideLemma11AHistoryData.noSharedDependentAnticommutingWitness`, `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideLemma11AHistoryData.isEmpty` |
| Lemma 12 (v1 Lemma 7) | `lemma12` vacuous on claw-free graphs; the corrected `lemma12_of_residualData` is conditional on the supplied `Lemma12ResidualData` | `SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.not_nonempty_lemma12Data_of_clawFree`, `SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.lemma12_of_residualData` |
| Lemma 13 (v1 Lemma 17) | Exact at the `FullDefinition19Deformation` interface; its hypotheses are jointly satisfied by a genuine two-step deformation | `SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.lemma13`, `SimpleGraph.Lemma12ResidualExample.criterion` |
| Lemma 14 (v1 Lemma 8) | Proved on histories whose runs are one-block, one-step traces; not exact for v1 | `SimpleGraph.FixedPairingPathFamily.ObstructionSearchInitialization.InitializationFiniteMixedSideLemma14History.paperLemma14` |
| Lemma 15 (v1 Lemma 9) | Collapses to Lemma 14 at state 0: the rerouting transition is uninhabited | `SimpleGraph.FixedPairingPathFamily.ObstructionSearchReroutingTransition.isEmpty`, `SimpleGraph.FixedPairingPathFamily.ObstructionSearchReroutingProcess.stepCount_eq_zero` |
| Lemma 16 (v1 Lemma 10) | Vacuous on claw-free graphs | `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.not_nonempty_paperLemma16Trace_of_clawFree` |
| Lemma 17 (v1 Lemma 18) | Exact positive-degree charge recursion | `SimpleGraph.PauliFrustrationRepresentation.paperLemma17` |
| Lemma 18 (v1 Lemma 16) | Printed matrix without even holes; the corrected matrix with even holes and any number of hole classes, in v1's form (`SimpleGraph.paperLemma18`); false for the literal printed normalisation with even holes (kernel-checked counterexample) | `SimpleGraph.paperDeformationClosureLemma_of_evenHoleFree`, `SimpleGraph.sectorRow_pow_eq_of_closure`, `SimpleGraph.paperLemma18`, `SimpleGraph.PrintedNormalisation.Example.printed_normalisation_counterexample` |
| Lemmas 1-5 (v1 Lemmas 11-15) | Lemma 1 exact for a bare scaled representation, claw-free only (`SimpleGraph.ScaledPauliFrustrationRepresentation.generalizedCharacteristicPolynomial`); also in operator form over hole families for a representation with root and clique data that v1's Lemma 11 lacks (`V1_ERRATA.md` E6), with the sector form `T T Pi = z Pi`; Lemma 2 exact; Lemma 3 on a `ModeSector` (the sectors of the joint projectors: `exists_modeSectors`); Lemma 4 on `Nondegenerate` data, the case `J = J'`; Lemma 5 on one sector, the sum over sectors only inside Theorem 2 (premise `hND`) | `SimpleGraph.ScaledPauliFrustrationRepresentation.generalizedCharacteristicPolynomial`, `SimpleGraph.ScaledPauliFrustrationRepresentation.generalizedCharacteristicPolynomial_empty`, `SimpleGraph.PauliCliqueHamiltonianRepresentation.generalizedCharacteristicPolynomial`, `SimpleGraph.PauliCliqueHamiltonianRepresentation.transfer_mul_transfer_neg_mul_sector`, `SimpleGraph.PauliFrustrationRepresentation.fundamentalIdentity`, `SimpleGraph.SimplicialModeHamiltonian.ModeSector.eigenmode`, `SimpleGraph.SimplicialModeHamiltonian.exists_modeSectors`, `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.ladder_plus_minus`, `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.hamiltonian_mul_Pi_matrix` |
| Theorem 1(i), (ii) | Unconditional (claw-free, any ring); non-vacuity `thm1i_content`, `thm1ii_content` | `SimpleGraph.PauliFrustrationRepresentation.paperTheorem1i`, `SimpleGraph.PauliFrustrationRepresentation.paperTheorem1ii`, `SimpleGraph.TheoremOneExample.thm1i_content`, `SimpleGraph.TheoremOneExample.thm1ii_content` |
| Theorem 1(iii) | Unconditional: claw-free finite `G`, even-hole carriers, arbitrary ring. The statement is v1's; the proof replaces v1's obstruction search (section H, `V1_ERRATA.md` E18). Non-vacuity with two deformation classes and crossing number 7: `thm1iii_content` (section I, item 9; `T3NonVacuity` has one class and is not such a witness) | `SimpleGraph.PauliFrustrationRepresentation.paperTheorem1iii`, `SimpleGraph.PauliFrustrationRepresentation.cycleSymmetriesCommute`, `SimpleGraph.palindromicToggles_nonempty`, `SimpleGraph.holePairToggle_involutive`, `SimpleGraph.TheoremOneExample.thm1iii_content` |
| Theorem 2 | Proved in `Matrix (Fin d) (Fin d) ℂ` for claw-free `G` and simplicial `Ks`, with one premise beyond v1's setup, `hND` (for every joint eigenvalue tuple `l` that occurs, `IsCoprime` of `sectorPolynomial H.coupling {} l` and `sectorPolynomial H.coupling Ks l`; v1 omits it; its printed statement fails in the `C_4` example, a hand computation, `V1_ERRATA.md` U1). `r_l = deg z_{{},l}` modes per sector, not `alpha(G)`. Qualified name; not exported as `paperTheorem2`. `hND` is all-or-nothing. Non-vacuity: `theorem2_two_sectors` (`C_4`, couplings `(1,1,1,2)`, sectors `J = +-2`, `hND` in both, section I, item 10); the conditional form on a one-vertex model without even holes | `SimpleGraph.SimplicialModeHamiltonian.paperTheorem2_of_sectorCoprime`, `SimpleGraph.SimplicialModeHamiltonian.exists_crossSectorModes_of_sectorCoprime`, `SimpleGraph.SimplicialModeHamiltonian.exists_modeSectors`, `SimpleGraph.SimplicialModeHamiltonian.freeFermionSolution_of_cycleSymmetry_commute`, `SimpleGraph.FreeFermionSolutionExample.freeFermionSolution_ham1`, `SimpleGraph.FreeFermionSolutionMultiSectorExample.theorem2_two_sectors` |
| Theorem 3 | Over the joint spectral projectors `Pi_l` of the `J_c` themselves (also as the projectors of the `ModeSector`s), in complex matrix algebras with real couplings and Hermitian terms, with no premise beyond v1's setup and with the corrected matrix `SimpleGraph.cliqueHoppingMatrix`; "over a mutual eigenspace" read as right multiplication by `Pi_l`. Also: without even holes; on a symmetry sector for any `Pr` with `[H, Pr] = 0` and `J_c Pr = lambda_c Pr` (qualified names: v1 takes `Pr = Pi_J`), `[H, Pr] = 0` discharged for `Pr` in the algebra generated by the `J_c`; existential form over `ℝ`. Non-vacuity on the 4-cycle model with two sectors | `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3`, `SimpleGraph.SimplicialModeHamiltonian.paperTheorem3_modeSectors`, `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_evenHoleFree`, `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_commute`, `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_cycleAlgebra`, `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_commute_exists`, `SimpleGraph.TheoremOneIIIConsequencesExample.paperTheorem3_two_sectors` |
| Corollary 1 | The anticommutator identity `Pi_l {ad^j chi, ad^k chi} = 2 M_jk Pi_l` over the joint eigenprojectors `Pi_l` (also as the projectors of the `ModeSector`s), `M` real symmetric, `M_jk = (-1)^j (-2i)^{j+k} (A_l^{j+k})_{j*,j*}` (corrected sign), `A_l = SimpleGraph.cliqueHoppingMatrix`; premises claw-free, simplicial clique, Hermitian terms, `chi^2 = 1` (a hypothesis; a field for the `ModeSector` form). Also: without even holes, and on a symmetry sector for any `Pr` with `[H, Pr] = 0`, `[chi, Pr] = 0` and `J_c Pr = lambda_c Pr` (qualified names: v1 takes `Pr = Pi_J`); existential form. Non-vacuity: `paperCorollary1_two_sectors`, `hopping_sector_dependent` (section I, item 11). Positive definiteness of `M` and the Majorana modes are not formalised. `paperCorollary1_modeSectors` is not instantiated by a committed example | `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1`, `SimpleGraph.SimplicialModeHamiltonian.paperCorollary1_modeSectors`, `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_bicommutant`, `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_evenHoleFree`, `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_commute`, `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_cycleAlgebra`, `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_cycleAlgebra_exists`, `SimpleGraph.Corollary1Example.paperCorollary1_two_sectors`, `SimpleGraph.Corollary1Example.hopping_sector_dependent` |

Rows for Lemmas 10-16 and Corollaries 7-12 describe the Definition 19 interface layer, audited in
the sections below. None of its declarations is used by Theorem 1(iii) or by any declaration named
in the rows for Theorems 1-3, Corollary 1 and Lemmas 1-5, 17, 18 (section H, dependency check).

## Documentation rule

Historical audit documents retain the repository state at their stated date and
baseline. The README and this file are the authoritative current status. Any PR
that changes a paper-facing theorem must update both when the provenance status
changes. Every status claim in either document must name the Lean declaration
that supports it, and must be re-checked when that declaration changes.
`docs/PAPER_FIDELITY_AUDIT_2026-08-05.md` and `docs/LEMMA18_PLAN.md` are
superseded where they conflict with the Audit 2026-10-26 section; the statements about
Theorem 1(iii), Theorem 2 and Theorem 3 in the Audit 2026-10-26 section are superseded by the
Audit 2026-10-30 section.

## Audit 2026-10-26

Basis. Declarations below were checked to exist in the current build, and each
depends only on `propext`, `Classical.choice`, `Quot.sound`. The audit modules are
audits, not paper theorems; each proves a property of a repository interface and
does not show that a manuscript statement is false. v1 line numbers refer to
`main.tex` of arXiv 2305.15625v1; repo numbers follow the revised manuscript
([`V1_NUMBERING.md`](V1_NUMBERING.md)).

### A. The Lemma 12 data and the hypotheses of `paperLemma16` are uninhabited on claw-free graphs

Module `FreeFermionGraphs/Lemma12VacuityAudit.lean`.

| Declaration | Statement |
|---|---|
| `SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.lemma12Data_false_of_clawFree` | a `Lemma12Definition19Data` on a claw-free graph gives `False`; no criterion, no unobstructedness used |
| `SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.not_nonempty_lemma12Data_of_clawFree` | `Lemma12Definition19Data` is not `Nonempty` on a claw-free graph |
| `SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.lemma12_data_inconsistent` | on any graph, the data together with the criterion `U <= C^(m)` give `False` |
| `SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.not_criterion_of_lemma12Data` | the same, as "the criterion fails once the data exist" |
| `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.paperLemma16Trace_false_of_clawFree` | a `PaperLemma16Trace` on a claw-free graph gives `False` |
| `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.not_nonempty_paperLemma16Trace_of_clawFree` | `PaperLemma16Trace` is not `Nonempty` on a claw-free graph |
| `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.paperLemma16_hyps_inconsistent` | on a claw-free graph, `PaperLemma16Trace` and `IsUnobstructed` give `False` |
| `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.not_isUnobstructed_of_paperLemma16Trace` | the same, as "a trace carrying the data is never unobstructed" |

Consequence. The theorems `SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.lemma12`
(repo Lemma 12 = v1 Lemma 7, L1122),
`SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.PaperLemma16Trace.paperLemma16`
(repo Lemma 16 = v1 Lemma 10, L1192) and
`SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.paperLemma16_of_terminalPathTransport`
take `hclaw : G.IsClawFree` together with data that cannot exist, so they carry no
information about v1's Lemmas 7 and 10. The earlier descriptions of these theorems
as exact are withdrawn.

Cause. The endpoint alternative of `SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.Lemma12Definition19Data.endpoint_or_continuation`
(and the field `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.PaperLemma16Trace.terminalEndpointMaximal`) demands that every
neighbour `v` in `C'` of the last removed vertex `k` lies on the active path. At the
last step the continuation alternative is impossible, so the endpoint alternative
is forced; claw-freeness at the introduced vertex `j` then puts a triangle
`j, k, d` on an induced path, which is impossible. v1 needs less: at L1795 only a
neighbour `v` in `C'` of `k` that is not adjacent to `j` (and is not `j`) would
contradict `k` being an endpoint (v1 Corollary 1, L671, and Corollary 6, L1040, as cited there; repo
Corollaries 2 and 7), and the palindromic example (L957-966) has two neighbours of
`C'` adjacent to `j` that are not on the path.

### B. The corrected, residual Lemma 12

Module `FreeFermionGraphs/Lemma12Residual.lean`.

- `SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.Lemma12ResidualData`: `Lemma12Definition19Data` with the endpoint alternative
  restricted to residual neighbours
  (`forall v in C', k ~ v -> v != j -> not (j ~ v) -> v in activePath`).
  `SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.Lemma12Definition19Data.toResidualData` converts old data to new data.
- `SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.exists_reverse_deformation_of_residualEndpoint`, `SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.lemma12_of_residualData`
  (Lemma 12 for the residual data: for the criterion `U <= C^(m)` and claw-free `G`,
  a reverse run exists).
- `SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.lemma12_carrier_of_residualData`: the reverse run ends at a hole whose carrier
  is `C' + (C + C^(m))` and which lies in `<C'>`;
  `SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.lemma12_carrier_even_of_residualData` (even length);
  `SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.ReverseRun.inEvenHoleDeformationClosure`,
  `SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.inEvenHoleDeformationClosure_terminal` (`C^(m)` in `<C>`),
  `SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.ReverseRun.symmDiff_invariant`.
- Non-vacuity: `SimpleGraph.Lemma12ResidualExample.residualData`,
  `SimpleGraph.Lemma12ResidualExample.criterion`,
  `SimpleGraph.Lemma12ResidualExample.clawFree` (a 10-vertex claw-free graph
  realising the palindromic example of v1 L957-966 with `l = 2`, two single-vertex
  steps), `SimpleGraph.Lemma12ResidualExample.reverse_carrier`,
  `SimpleGraph.Lemma12ResidualExample.not_nonempty_lemma12Definition19Data` (the old
  data do not exist on the same deformation), and
  `SimpleGraph.exists_lemma12ResidualData_with_criterion`.

Status. Conditional: `Lemma12ResidualData` is a supplied certificate (the path
geometry of Definition 19 is not derived from `(C, C', W)`), so every consumer carries
the suffix `_of_residualData`. The carrier statement speaks of `C^(m)`, not of
`C + dO` (`dO` the union of the paths, v1 L990), which equals `C^(m)` only for
vertex-disjoint paths. No corrected
Lemma 16 built on `Lemma12ResidualData` is in the repository.

### C. The Lemma 15 rerouting transition is uninhabited

Module `FreeFermionGraphs/ObstructionSearchReroutingAudit.lean`.

- `SimpleGraph.FixedPairingPathFamily.ObstructionSearchReroutingTransition.isEmpty`: for every pair of states there is no
  transition.
- `SimpleGraph.FixedPairingPathFamily.ObstructionSearchReroutingProcess.stepCount_eq_zero`: every process has
  `stepCount = 0`.
- `SimpleGraph.FixedPairingPathFamily.ObstructionSearchReroutingProcess.paperLemma15Conclusion_iff_state_zero`:
  `PaperLemma15Conclusion` is equivalent to `PaperLemma14Conclusion` at state `0`.
- helpers: `SimpleGraph.FixedPairingPathFamily.SearchDeformation.FirstPathIs`,
  `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.firstPathIs`,
  `SimpleGraph.FixedPairingPathFamily.ObstructionSearchInitialization.NonemptyFiniteMixedSideOSExecution.firstPathIs`.

Consequence. `SimpleGraph.FixedPairingPathFamily.ObstructionSearchReroutingProcess.paperLemma15`
(repo Lemma 15 = v1 Lemma 9, L1185) is `paperLemma14` at state `0`. Claw-freeness is
not used by the audit. The Eq. (C31)/(C32) provenance cleanup listed in the earlier
audit is moot until the model is rebuilt on an obstruction-search relation that can
start from a nonempty deformation.

### D. The finite Definition 19 trace types are degenerate

Module `FreeFermionGraphs/Definition19TraceDegeneracyAudit.lean`.

Cause. `SimpleGraph.FixedPairingPathFamily.ACHoleStepGeometry.before_subset` (the hole before a step lies in `C_a u C_b`)
is demanded at every step of every block by `FullDefinition19NeighborhoodData` and
hence by every `FiniteMixedSideSearchTrace` (through its `localData`). In v1 it holds
only at the first step of the first block, where the hole is `C`: the vertex `j_0^(0)`
introduced by the first step is not in `C` (v1 Corollary 6, L1040-1047, proof at
L1045) and is never removed, so it lies in every later hole. The module docstring
lists every consumer of the field.

| Declaration | Statement |
|---|---|
| `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FullDefinition19NeighborhoodData.firstIntroduced_not_mem_ca_cb` | the first introduced vertex lies in neither `C_a` nor `C_b` |
| `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FullDefinition19NeighborhoodData.stepCount_le_one`, `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FullDefinition19NeighborhoodData.stepCount_eq_one` | a block with integrated neighbourhood data has exactly one step |
| `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.blockCount_eq_one`, `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.block_stepCount_eq_one`, `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.flattened_stepCount_eq_one` | a finite mixed-side trace has exactly one block with one step |
| `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.range_path_eq_pair`, `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.pathVertex_eq_introduced_or_removed` | the path of the block is `{introduced, removed}` |
| `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.isUnobstructed_iff_dependentUnion_eq_empty`, `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.dependentAt_eq_empty_of_isUnobstructed` | `IsUnobstructed` is equivalent to `U = {}` |
| `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FullDefinition19Lemma11AHistoryData.isEmpty`, `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideLemma11AHistoryData.isEmpty`, `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.MixedSideFullDefinition19Lemma11AHistoryData.isEmpty` | the positive-history types of Lemma 11 (a.ii) (`0 < priorCount`) are uninhabited |
| `SimpleGraph.FixedPairingPathFamily.ConcreteDeformationStep.dependent_not_mem_after` | helper: a dependent vertex is outside the hole after its step |

Consequences for the repository's statements as typed (not for the paper):

- Lemma 11 (v1 Lemma 6) on the finite types covers a single step; the versions
  through a nonempty prefix take an uninhabited hypothesis and say nothing.
- Corollary 11 (v1 Corollary 10) across blocks: the finite-history theorem
  `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideLemma11AHistoryData.noSharedDependentAnticommutingWitness`
  takes a `FiniteMixedSideLemma11AHistoryData`, which is uninhabited
  (`SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideLemma11AHistoryData.isEmpty`),
  so it says nothing.
- Lemma 14 (v1 Lemma 8): a `FiniteMixedSideSearchTrace` has one block; a genuine
  multi-block Definition 19 run cannot be put in this type.
- Lemma 15 (v1 Lemma 9) is stated on histories built from such traces and inherits the
  restriction (and is in addition degenerate, section C).
- Lemma 16 (v1 Lemma 10): `IsUnobstructed` already says `U = {}`, so the criterion is
  trivial (and the hypotheses are inconsistent, section A).

Minimal repair, per the module: assert `before_subset` only at the first step of the
first block, and derive the colour information needed at later holes `C^(r,s)` from the
Definition 19 history. It cannot be repaired by restricting to the `b`-vertices: for
mixed-side runs the `b`-class of a later hole can contain vertices of `C'_d \ C_b`.

### E. Corrections to earlier statements

1. Lemma 8 (repo; v1 Lemma 3, L707). The earlier audit says the printed statement has
   a counterexample "for holes longer than four". By a hand check, the printed
   statement fails for every `k >= 2` (`t = s` or `t = a_0`; `docs/V1_ERRATA.md`, E3).
   The Lean statement is the corrected one:
   `SimpleGraph.EvenHoleLabeling.CloneAt.lemma8` (premise `t not in {s} u C`). The
   failure of the printed statement is not machine-checked.
2. Corollary 6 (repo; v1 Corollary 5, L749). `SimpleGraph.EvenHoleCompatible` is the
   notion of v1 L748 (disjoint closed neighbourhoods `Gamma[C]`, `Gamma[C']`), not that
   of L313. As defined, `SimpleGraph.EvenHoleCompatible G A B` is
   `Disjoint (G.openNeighborhood A) (G.openNeighborhood B)`; this coincides with
   disjointness of the closed neighbourhoods only for carriers contained in their own
   open neighbourhood, such as hole carriers (every vertex of a hole has a neighbour in
   the hole). That coincidence is read off the definition and is not a separate Lean
   theorem. The two notions differ in claw-free graphs
   (`SimpleGraph.exists_evenHoleInducedCompatible_not_evenHoleCompatible`), and the
   corollary holds for both (`SimpleGraph.corollary6`, `SimpleGraph.corollary6_induced`).
   The docstring of `SimpleGraph.EvenHoleCompatible` (`Corollary6.lean`) equating it with
   the L313 notion is wrong. `SimpleGraph.evenHoleFamilies` uses the L313 notion.
3. Lemma 10 and Corollaries 7-10 (v1 Lemma 5 and Corollaries 6-9). The Lean statements
   are on the `FixedPairingPathFamily` interface, whose structure fields carry the
   pairwise disjointness and containment facts
   (`SimpleGraph.FixedPairingPathFamily.lemma10` is proved from the fields `ac_pairwise`,
   `bd_pairwise`, `ac_subset`, `bd_subset`). `SimpleGraph.FixedPairingPathFamily.corollary8`
   is `Subtype.ext` on a set of subsets and carries no occurrence content.
4. `EvenHoleLabeling` carriers. A labelling carrier is an even-hole carrier exactly
   when it induces a connected subgraph
   (`SimpleGraph.isEvenHoleCarrier_iff_exists_labeling`); operator-level statements use
   `SimpleGraph.IsEvenHoleCarrier`, not a bare labelling. `SimpleGraph.EvenHoleLabeling.hasFullCyclicOrder_of_connected`
   supplies the cyclic order for connected carriers.
5. Lemmas 17 and 18 (repo). Repo Lemma 17 (v1 Lemma 18) is proved:
   `SimpleGraph.PauliFrustrationRepresentation.paperLemma17` (`docs/LEMMA17_FIDELITY.md`).
   Repo Lemma 18 (v1 Lemma 16) is proved for the repo matrix of Eq. (E1) on graphs
   without even holes (`SimpleGraph.paperDeformationClosureLemma_of_evenHoleFree`) and for
   the corrected matrix on graphs with even holes, any number of hole classes
   (`SimpleGraph.sectorRow_pow_eq_of_closure`; in v1's form `SimpleGraph.paperLemma18`).
   The matrix of the repo's Eq. (E1) with canonical weights is not a valid Theorem 3 witness
   for graphs with even holes (numerical check outside Lean, `docs/V1_ERRATA.md`, E11;
   `SimpleGraph.cliqueHoppingMatrix` is the corrected matrix). The `Lemma18Paper` docstring
   identifies it with the printed matrix (not a Lean statement). For the printed
   normalisation of v1 read literally (a fixed source and a sum over its targets,
   `SimpleGraph.IsPrintedNormalisation`, matrix `SimpleGraph.printedHoppingMatrix`) the lemma
   fails in a kernel-checked example,
   `SimpleGraph.PrintedNormalisation.Example.printed_normalisation_counterexample`
   (`docs/V1_ERRATA.md`, E11). The local-weight layer of `docs/LEMMA18_PLAN.md` is superseded.
6. Theorem rows. The earlier "Theorem 1(i)-(iii) not formalised" is replaced: (i), (ii) and
   (iii) are proved (sections F, H). The earlier "Theorem 3 and Corollary 1 not formalised"
   is replaced: Theorem 3 is proved for graphs without even holes (section F), on a symmetry
   sector for any `Pr` with `[H, Pr] = 0` and `J_c Pr = lambda_c Pr` (Corollary 1 also
   `[chi, Pr] = 0`): `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_commute`,
   `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_commute` (section F),
   and over the joint spectral projectors of the `J_c`, with no premise beyond the setup, by
   `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3` (section F). Corollary 1
   is stated over those projectors by `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1`
   (section F, commit f2c3548); its positive definiteness of `M` and Majorana modes
   are not formalised in any case (sections G, I). The earlier "Theorem 2 not formalised" is
   replaced: Theorem 2 is proved in `Matrix (Fin d) (Fin d) ℂ` with the per-sector coprimality
   `hND` as its only premise beyond the setup
   (`SimpleGraph.SimplicialModeHamiltonian.paperTheorem2_of_sectorCoprime`, section F).
   Statements in the earlier audits that Theorem 1(iii) is open, or that Theorems 2 and 3 are
   conditional on it (`hJ`), are withdrawn; the `_of_cycleSymmetry_commute` forms remain as the
   conditional versions.

### F. New paper-facing declarations and their premises

Gate 5 (premises beyond the manuscript setup) for the declarations that were added.
"Setup" means a finite vertex type, a Hamiltonian representation (terms with the
commute/anticommute pattern of the frustration graph, over an arbitrary ring), and the
standing claw-free assumption of the manuscript. This table is kept current: it includes the
declarations added by the proof of Theorem 1(iii) and its consequences (2026-10-30, section H), and
the conditional `_of_cycleSymmetry_commute` rows describe the forms that take Theorem 1(iii) as a
hypothesis.

| Declaration | Extra premises | Note |
|---|---|---|
| `SimpleGraph.PauliFrustrationRepresentation.paperTheorem1i` | none | `[q_{s,mu}, q_{t,nu}] = 0` for the token-sliding charges (v1 Theorem 1(i)); arbitrary ring |
| `SimpleGraph.PauliFrustrationRepresentation.paperTheorem1ii` | `G.IsEvenHoleCarrier C0` | `[J_{C0}, q_{s,mu}] = 0`; v1 defines `J_{C0}` only for even holes; arbitrary ring, no invertibility of 2 |
| `SimpleGraph.PauliFrustrationRepresentation.hamiltonian_commute_tokenSlidingChargeOp` | none (`hclaw`, setup) | `[H, q_{t,nu}] = 0`: the last sentence of Theorem 1, the token-sliding charges are conserved |
| `SimpleGraph.PauliFrustrationRepresentation.hamiltonian_commute_generalizedCycleSymmetryOp` | `G.IsEvenHoleCarrier C0` (`hC0`) | `[H, J_{C0}] = 0`: the last sentence of Theorem 1, the generalized cycle symmetries are conserved |
| `SimpleGraph.PauliFrustrationRepresentation.paperTheorem1iii` | `G.IsClawFree` (`hclaw`, setup); `G.IsEvenHoleCarrier C0`, `G.IsEvenHoleCarrier C0'` (v1 defines `J` only for even holes); finite `V`; arbitrary ring | `[J_{C0}, J_{C0'}] = 0` (v1 Theorem 1(iii)); the same premise set as `paperTheorem1ii`; no `h_j^2 = b_j^2`, no invertibility of 2. The proof route and its deviations from v1 are in section H and `docs/V1_ERRATA.md` E18 |
| `SimpleGraph.PauliFrustrationRepresentation.cycleSymmetriesCommute` | `G.IsClawFree` (`hclaw`, setup); arbitrary ring | `paperTheorem1iii` in the form `H.CycleSymmetriesCommute`, the hypothesis `hJ` of the conditional sector theory (`CycleSymmetrySectors`), now a theorem |
| `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_evenHoleFree` | simplicial clique `K` (`hK`); claw-free `G` (`hclaw`, setup); no even hole (`hfree`: no `G.IndexedInducedHole` of even cardinality; name carries `_of_evenHoleFree`); coefficients in any commutative ring `R` | `[H,.]^k chi = (-2)^k sum_P (T^k)_{{j*},P} h_P`, `T = SimpleGraph.cliqueTreeMatrix` |
| `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_evenHoleFree_exists` | simplicial clique `K` (`hK`); claw-free `G` (`hclaw`, setup); no even hole (`hfree`: no `G.IndexedInducedHole` of even cardinality; name carries `_of_evenHoleFree`); coefficients in `ℝ`, `A` an `ℂ`-algebra and an `ℝ`-algebra with `IsScalarTower ℝ ℂ A` | v1's existential form, `ad = [iH,.]`; witness the tree matrix, every nonzero entry `M_PQ` has odd sum of the path sizes of `P` and `Q` |
| `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_commute` | simplicial clique `K` (`hK`); claw-free `G` (`hclaw`, setup); `R` a field of characteristic 0; `Pr` with `Commute H.physicalHamiltonian Pr` (`hHP`) and `J_c Pr = lambda_c Pr` for every even-hole class (`hJ`); `Pr^2 = Pr` is not assumed (name carries `_of_commute`) | Theorem 3 on a symmetry sector: `[H,.]^k chi * Pr = (-2)^k sum_P ((A_lambda^k)_{{j*},P}) h_P Pr`, `A_lambda = SimpleGraph.cliqueHoppingMatrix` (corrected matrix, not the printed one). v1 takes `Pr = Pi_J` and needs `[H, Pr] = 0` without saying so; no premise is a conclusion; the statement over the `Pi_l` themselves is `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3` (below) |
| `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_cycleAlgebra` | simplicial clique `K` (`hK`); claw-free `G` (`hclaw`, setup); `R` a field of characteristic 0; `Pr` in `Algebra.adjoin` of the generalized cycle operators `J_c` of the even holes (`hPr`), in place of `hHP`; `J_c Pr = lambda_c Pr` for every even-hole class (`hJ`); `Pr^2 = Pr` is not assumed | `[H, Pr] = 0` from Theorem 1(ii) (`SimpleGraph.PauliCliqueHamiltonianRepresentation.commute_physicalHamiltonian_of_mem_adjoin`); membership of the joint spectral projector in that algebra is a hypothesis on `Pr`, as the abstract algebra has no spectral theory |
| `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_commute_exists` | simplicial clique `K` (`hK`); claw-free `G` (`hclaw`, setup); `Pr` with `Commute H.physicalHamiltonian Pr` (`hHP`) and `J_c Pr = lam(c) Pr` for every even-hole class (`hJ`), `lam` real; coefficients in `ℝ`, `A` an `ℂ`-algebra and an `ℝ`-algebra with `IsScalarTower ℝ ℂ A` | v1's existential form, `ad = [iH,.]`; witness `A_lambda`, every nonzero entry `M_PQ` has odd sum of the path sizes of `P` and `Q` |
| `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_ad_of_commute` | simplicial clique `K` (`hK`); claw-free `G` (`hclaw`, setup); `Pr` with `Commute H.physicalHamiltonian Pr` (`hHP`); `lam` with `J_c Pr = lam(c) Pr` for the class `c` of the carrier of every labelling with full cyclic order, i.e. every even-hole class (`hJ`); coefficients in `ℝ`, `A` an `ℂ`-algebra and an `ℝ`-algebra with `IsScalarTower ℝ ℂ A`; `Pr^2 = Pr` is not assumed | the identity of `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_commute_exists` with the witness exposed: `ad_{iH}^k chi * Pr = sum_P ((-2i)^k (A_lambda^k)_{{j*},P}) h_P Pr`, `ad_{iH} = [iH,.]` |
| `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_bicommutant` | simplicial clique `K` (`hK`); claw-free `G` (`hclaw`, setup); coefficients in `ℝ`, `A` an `ℂ`-algebra and an `ℝ`-algebra with `IsScalarTower ℝ ℂ A`; `Pr` with `hbic` (every `x` that commutes with all `J_{C0}`, `C0` an even-hole carrier, commutes with `Pr`) and `heig` (`J_{C0} Pr = lam(<C0>) Pr` for every even-hole carrier `C0`, `lam` real). `Pr^2 = Pr` and `Pr != 0` are not assumed; neither `[H, Pr] = 0` nor `[chi, Pr] = 0` is a premise | `[H, Pr] = 0` (Theorem 1(ii)) and `[chi, Pr] = 0` (`SimpleGraph.PauliCliqueHamiltonianRepresentation.commute_rootOperator_of_forall_commute`, `chi` commutes with every `J_c`) are derived from `hbic`; conclusion: `Pr` commutes with `ad_{iH}^k chi` and `Pr ad_{iH}^k chi = ad_{iH}^k chi Pr = sum_P ((-2i)^k (A_lambda^k)_{{j*},P}) h_P Pr`. Name qualified because `Pr` is an assumed eigen-operator in the bicommutant |
| `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_cycleSymmetry_commute` | simplicial clique `K` (`hK`); claw-free `G` (`hclaw`); `H : G.PauliCliqueHamiltonianRepresentation K ℝ (Matrix (Fin d) (Fin d) ℂ)`; Hermitian Pauli terms (`hstar : ∀ j, IsSelfAdjoint (H.operator.term (some j))`, manuscript setup); `hJ : H.operator.restrictSome.CycleSymmetriesCommute`, `[J_{C0}, J_{C1}] = 0` for even-hole carriers (v1 Theorem 1(iii) as a hypothesis, hence the name `_of_cycleSymmetry_commute`); no other premise | v1 Theorem 3 "over each mutual eigenspace of the `J`'s": the joint spectral decomposition `(Lambda, Pi_l)` of `SimpleGraph.PauliFrustrationRepresentation.exists_jointSpectralProjections_of_cycleSymmetry_commute`, and for every `l` in `Lambda`: `A_l = SimpleGraph.cliqueHoppingMatrix` (corrected matrix) is real with nonzero entries `(P, Q)` only where the path sizes of `P` and `Q` have odd sum, and for all `k`, `Pi_l` commutes with `ad_{iH}^k chi` and `Pi_l ad_{iH}^k chi = ad_{iH}^k chi Pi_l = sum_P ((-2i)^k (A_l^k)_{{j*},P}) h_P Pi_l`, `ad_{iH} = [iH,.]`. `Pi_l` multiplies the path operators from the right, as for `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_commute`. Proof: the decomposition and `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_bicommutant`. `hJ` is discharged in `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3` (next rows) |
| `SimpleGraph.SimplicialModeHamiltonian.paperTheorem3_modeSectors_of_cycleSymmetry_commute` | `H : G.SimplicialModeHamiltonian Ks (Matrix (Fin d) (Fin d) ℂ)`; claw-free `G` (`hclaw`); simplicial clique `Ks` (`hKs`); `hJ : H.frustration.CycleSymmetriesCommute` (discharged in `SimpleGraph.SimplicialModeHamiltonian.paperTheorem3_modeSectors`); Hermiticity of the Pauli terms is the field `term_selfAdjoint`, not a premise | everything of `SimpleGraph.SimplicialModeHamiltonian.exists_modeSectors_of_cycleSymmetry_commute` (the `Pi_l` are the projectors of `ModeSector`s with `zG = z_{{},l}`, `zK = z_{Ks,l}`) together with the Theorem 3 identity of the previous row for the same `Pi_l`, with `A_l = SimpleGraph.cliqueHoppingMatrix G Ks H.coupling l`. Non-vacuity on the three-qubit 4-cycle model (two sectors `J = +-1`, left side nonzero at `k = 1`): `SimpleGraph.Theorem3SectorsExample.theorem3_two_sectors` |
| `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3` | simplicial clique `K` (`hK`); claw-free `G` (`hclaw`); `H : G.PauliCliqueHamiltonianRepresentation K ℝ (Matrix (Fin d) (Fin d) ℂ)`; Hermitian Pauli terms (`hstar : ∀ j, IsSelfAdjoint (H.operator.term (some j))`, manuscript setup); no other premise (unqualified name) | v1 Theorem 3 "over each mutual eigenspace of the `J`'s": `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3_of_cycleSymmetry_commute` (previous rows) with `hJ` supplied by `SimpleGraph.PauliFrustrationRepresentation.cycleSymmetriesCommute`. Deviations from v1: the corrected matrix `SimpleGraph.cliqueHoppingMatrix` (not the printed Eq. (decoratedtree)); "over each mutual eigenspace" read as right multiplication of the path operators by `Pi_l`; real couplings, complex matrices. Non-vacuity: `SimpleGraph.TheoremOneIIIConsequencesExample.paperTheorem3_two_sectors` (4-cycle model, two sectors `J = +-1`, left side nonzero at `k = 1`, no commutation hypothesis supplied) |
| `SimpleGraph.SimplicialModeHamiltonian.paperTheorem3_modeSectors` | `H : G.SimplicialModeHamiltonian Ks (Matrix (Fin d) (Fin d) ℂ)`; claw-free `G` (`hclaw`); simplicial clique `Ks` (`hKs`); no other premise (unqualified name) | `SimpleGraph.SimplicialModeHamiltonian.paperTheorem3_modeSectors_of_cycleSymmetry_commute` with `hJ` discharged: everything in `SimpleGraph.SimplicialModeHamiltonian.exists_modeSectors` together with the Theorem 3 identity of `paperTheorem3` for the same `Pi_l`. Not instantiated by a committed example (section I, item 3) |
| `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_evenHoleFree` | simplicial clique `K` (`hK`); claw-free `G` (`hclaw`, setup); no even hole (`hfree`: no `G.IndexedInducedHole` of even cardinality; name carries `_of_evenHoleFree`); `H.rootOperator * H.rootOperator = 1` (`hχ`); coefficients in any commutative ring `R` | v1 Corollary 12 (repo Corollary 1), anticommutator identity only, `ad_H = [H,.]`: `{ad_H^j chi, ad_H^k chi} = 2 (-1)^j (-2)^(j+k) (T^(j+k))_{{j*},{j*}}`, `T = SimpleGraph.cliqueTreeMatrix`; corrected sign `(-1)^j`; `chi^2 = 1` is a hypothesis (Pauli operators square to 1 in v1). Not covered: positive definiteness of `M`, the Majorana modes |
| `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_evenHoleFree_ad` | simplicial clique `K` (`hK`); claw-free `G` (`hclaw`, setup); no even hole (`hfree`: no `G.IndexedInducedHole` of even cardinality; name carries `_of_evenHoleFree`); `H.rootOperator * H.rootOperator = 1` (`hχ`); coefficients in `ℝ`, `A` an `ℂ`-algebra and an `ℝ`-algebra with `IsScalarTower ℝ ℂ A` | manuscript convention `ad = [iH,.]`: `{ad^j chi, ad^k chi} = 2 M_jk` with the corrected `M_jk = (-1)^j (-2i)^(j+k) (T^(j+k))_{{j*},{j*}}`; `chi^2 = 1` is a hypothesis; same coverage as the previous row (not covered: positive definiteness of `M`, the Majorana modes) |
| `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_commute`, `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_commute_left` | simplicial clique `K` (`hK`); claw-free `G` (`hclaw`, setup); `Pr` with `Commute H.physicalHamiltonian Pr` (`hHP`) and `Commute H.rootOperator Pr` (`hχP`); `H.rootOperator * H.rootOperator = 1` (`hχ`); `lam` with `J_c Pr = lam(c) Pr` for the class `c` of the carrier of every labelling with full cyclic order, i.e. every even-hole class (`hJ`); `R` a field of characteristic 0; `Pr^2 = Pr` is not assumed (name carries `_of_commute`) | v1 Corollary 12 (repo Corollary 1) on a symmetry sector, anticommutator identity only, `ad_H = [H,.]`: `{ad_H^j chi, ad_H^k chi} Pr = 2 (-1)^j (-2)^(j+k) ((A_lambda^(j+k))_{{j*},{j*}}) Pr`, `A_lambda = SimpleGraph.cliqueHoppingMatrix` (corrected matrix, not the printed one); `_left` has `Pr` on the left, v1's `Pi {.,.} = 2 M Pi`; v1 takes `Pr = Pi_J`, the unqualified `paperCorollary1` is not exported. Not covered: positive definiteness of `M`, the Majorana modes |
| `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_commute_ad` | simplicial clique `K` (`hK`); claw-free `G` (`hclaw`, setup); `Pr` with `Commute H.physicalHamiltonian Pr` (`hHP`) and `Commute H.rootOperator Pr` (`hχP`); `H.rootOperator * H.rootOperator = 1` (`hχ`); `lam` with `J_c Pr = lam(c) Pr` for the class `c` of the carrier of every labelling with full cyclic order, i.e. every even-hole class (`hJ`); coefficients in `ℝ`, `A` an `ℂ`-algebra and an `ℝ`-algebra with `IsScalarTower ℝ ℂ A` | manuscript convention `ad = [iH,.]`: `{ad^j chi, ad^k chi} Pr = 2 M_jk Pr`, `M_jk = (-1)^j (-2i)^(j+k) (A_lambda^(j+k))_{{j*},{j*}}` |
| `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_commute_exists` | `hK`, `hclaw`, `hHP`, `hχP`, `hχ`, `lam`, `hJ` exactly as for `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_commute_ad` (restated there), coefficients in `ℝ`, `A` an `ℂ`-algebra and an `ℝ`-algebra with `IsScalarTower ℝ ℂ A` | v1's existential form: there is a real matrix `(M_jk)` indexed by `ℕ × ℕ`, symmetric, with the entries above (odd powers of `A_lambda` vanish at the root, `SimpleGraph.cliqueHoppingMatrix_pow_cliqueRootPath_eq_zero_of_odd`), such that `{ad^j chi, ad^k chi} Pr = 2 M_jk Pr` and `Pr {ad^j chi, ad^k chi} = 2 M_jk Pr`. Positive definiteness is not claimed |
| `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_cycleAlgebra`, `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_cycleAlgebra_left`, `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_cycleAlgebra_ad`, `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_cycleAlgebra_exists` | simplicial clique `K` (`hK`); claw-free `G` (`hclaw`, setup); `Pr` in `Algebra.adjoin` of the generalized cycle operators `J_c` of the even holes (`hPr`), in place of `hHP` and `hχP`; `H.rootOperator * H.rootOperator = 1` (`hχ`); `lam` with `J_c Pr = lam(c) Pr` for the class `c` of the carrier of every labelling with full cyclic order, i.e. every even-hole class (`hJ`); `R` a field of characteristic 0 (`_ad`, `_exists`: coefficients in `ℝ`, `A` an `ℂ`-algebra and an `ℝ`-algebra with `IsScalarTower ℝ ℂ A`) | the conclusions of `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_commute` (resp. `_left`, `_ad`, `_exists`): `[H, Pr] = 0` from Theorem 1(ii) (`SimpleGraph.PauliCliqueHamiltonianRepresentation.commute_physicalHamiltonian_of_mem_adjoin`) and `[chi, Pr] = 0` from `SimpleGraph.PauliCliqueHamiltonianRepresentation.commute_rootOperator_of_mem_adjoin` (`K` simplicial, `chi` commutes with every `J_c`, v1 Result 2 L112); membership of the joint spectral projector in that algebra is a hypothesis on `Pr`, as for Theorem 3 |
| `SimpleGraph.PauliCliqueHamiltonianRepresentation.generalizedCharacteristicPolynomial` | none beyond claw-free | operator form over hole families, any deleted carrier; the regrouping into `J_{<C0>}` is not part of it; name unqualified by `_of_` because no premise is a conclusion |
| `SimpleGraph.ScaledPauliFrustrationRepresentation.generalizedCharacteristicPolynomial`, `SimpleGraph.ScaledPauliFrustrationRepresentation.generalizedCharacteristicPolynomial_empty` | `H : G.ScaledPauliFrustrationRepresentation ℝ A` (terms with `h_j^2 = b_j^2`); claw-free `G` (`hclaw`); no root, no clique; `u` in any commutative `ℝ`-algebra acting on `A` | v1 Lemma 11 (repo Lemma 1) for a bare scaled representation: `T_{G\W}(u) T_{G\W}(-u) = sum_X (-u^2)^{|dX|/2} 2^{|X|} I(-u^2) h_X` over `evenHoleFamilies W`; `_empty` is `W = {}`. Proved directly (the reduction `K = {}`, `chi = 1` fails in the zero algebra). The regrouping into `J_{<C0>}` is not part of it |
| `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1` | simplicial clique `K` (`hK`); claw-free `G` (`hclaw`); `hstar`: Hermitian Pauli terms; `hχ : chi^2 = 1` (v1 Result 2: `chi` is a Pauli operator); complex matrices, real couplings; connectivity not needed; no other premise (unqualified name) | v1 Corollary 12 (repo Corollary 1) over the joint eigenprojectors: `(Lambda, Pi_l)` Hermitian, idempotent, nonzero, orthogonal, summing to `1`, `J_c Pi_l = l(c) Pi_l`, in the bicommutant; for each `l`, `Pi_l {ad_{iH}^j chi, ad_{iH}^k chi} = {..} Pi_l = 2 M_jk Pi_l` with `M` real symmetric, `M_jk = (-1)^j (-2i)^{j+k} (A_l^{j+k})_{j*,j*}` (corrected sign, corrected matrix). Obtained from `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1_of_bicommutant` (single `Pr` in the bicommutant, premises `hbic`, `heig`) with `[H, Pi_l] = 0` from Theorem 1(ii) and `[chi, Pi_l] = 0` from `SimpleGraph.PauliCliqueHamiltonianRepresentation.commute_rootOperator_of_forall_commute` (through `commute_rootOperator_generalizedCycleOperator`). No positive definiteness, no Majorana modes |
| `SimpleGraph.SimplicialModeHamiltonian.paperCorollary1_modeSectors` | `H : G.SimplicialModeHamiltonian Ks (Matrix (Fin d) (Fin d) ℂ)`; claw-free `G`; simplicial clique `Ks`; no other premise (`chi^2 = 1` and Hermiticity are structure fields) | `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1` for the projectors of the `ModeSector`s of Theorem 2 |
| `SimpleGraph.PauliCliqueHamiltonianRepresentation.transfer_mul_transfer_neg_mul_sector` | claw-free; `W = {}` or `W = Ks` simplicial; `Pi` with `J_{<C0>} Pi = lambda Pi` for every even-hole carrier | sector form of Lemma 11 (v1's regrouping, L1979-1982); no premise is a conclusion of the lemma |
| `SimpleGraph.PauliFrustrationRepresentation.fundamentalIdentity` | simplicial clique | no claw-freeness needed |
| `SimpleGraph.SimplicialModeHamiltonian.ModeSector.eigenmode`, `SimpleGraph.SimplicialModeHamiltonian.ModeSector.intertwine` | a `ModeSector` | class B data: the sector projector's properties are structure fields, not derived: `Pi_idem`, `Pi_selfAdjoint`, `Pi_comm_charge` (commutes with the charges `Q_G^(k)`), `Pi_comm_root` (commutes with `chi`), and `zG`, `zK`, `Z_scalar`, `ZK_scalar` (scalar action of `Z_G`, `Z_{G\Ks}`). Commutation with the transfer operators `T(u)` is not a field; it is the derived `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Pi_comm_transfer`. No unqualified `paperLemma13` is exported. For the joint projectors of the `J`'s these fields are discharged by `SimpleGraph.SimplicialModeHamiltonian.exists_modeSectors_of_cycleSymmetry_commute` (below), under `SimpleGraph.PauliFrustrationRepresentation.CycleSymmetriesCommute` |
| `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.ladder_plus_minus`, `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.commutator_plus_minus` | `Nondegenerate` data | class B data: distinct positive roots and positive radicands, which v1 uses silently (`docs/V1_ERRATA.md`, E16); no unqualified `paperLemma14`/`paperLemma15` is exported for the exact solution |
| `SimpleGraph.SimplicialModeHamiltonian.ModeSector.exists_nondegenerate_of_isCoprime`, `SimpleGraph.SimplicialModeHamiltonian.ModeSector.root_real_neg`, `SimpleGraph.SimplicialModeHamiltonian.ModeSector.radicand_pos`, `SimpleGraph.SimplicialModeHamiltonian.ModeSector.charge_mul_Pi_eq_zero` | matrix algebras `Matrix (Fin d) (Fin d) ℂ`; a `ModeSector` with `Pi != 0`; coprime `z_G`, `z_K` (for the existence of `Nondegenerate` data); `SimpleGraph.SimplicialModeHamiltonian.ModeSector.exists_nondegenerate_of_fta` takes the Fundamental Theorem of Algebra as a hypothesis | derives the silent facts of v1 from no common root; not in v1, no `paper` prefix |
| `SimpleGraph.PauliFrustrationRepresentation.exists_jointSpectralProjections_of_cycleSymmetry_commute` | `H : G.PauliFrustrationRepresentation (Matrix (Fin d) (Fin d) ℂ)`; `hstar`: every Pauli term is self-adjoint; `hJ : H.CycleSymmetriesCommute`, i.e. `[J_{C_0}, J_{C_1}] = 0` for even-hole carriers (v1 Theorem 1(iii) as a hypothesis, hence the name `_of_cycleSymmetry_commute`). No claw-freeness, no simplicial clique | the projectors of v1 Theorem 2, first part: a finite set `Lambda` of tuples `l` (zero on the classes that are not even-hole classes) and Hermitian idempotents `Pi_l != 0`, pairwise orthogonal, `sum_l Pi_l = 1`, `J_{C_0} Pi_l = l(<C_0>) Pi_l`, every matrix commuting with all the `J`'s commutes with every `Pi_l`; `Lambda` is exactly the set of joint eigenvalue tuples that occur |
| `SimpleGraph.SimplicialModeHamiltonian.jointModeSector` | `H : G.SimplicialModeHamiltonian Ks (Matrix (Fin d) (Fin d) ℂ)`; claw-free `G` (`hclaw`); simplicial clique `Ks` (`hKs`); `lam : G.EvenHoleDeformationClass → ℝ`; a matrix `P` with `hP` (Hermitian), `hPP` (`P * P = P`), `heig` (`J_{C_0} P = lam(<C_0>) P` for every even-hole carrier) and `hcomm` (`P` commutes with every matrix that commutes with all the `J`'s). Takes no `hJ`: the commutation of the `J`'s is not used, only needed to produce such a `P` | a `ModeSector` with projector `P`, `zG = SimpleGraph.sectorPolynomial H.coupling {} lam`, `zK = SimpleGraph.sectorPolynomial H.coupling Ks lam`; applies to any `P` as described, in particular to the `Pi_l` of the previous row |
| `SimpleGraph.SimplicialModeHamiltonian.exists_modeSectors_of_cycleSymmetry_commute` | `H : G.SimplicialModeHamiltonian Ks (Matrix (Fin d) (Fin d) ℂ)`; claw-free `G` (`hclaw`); simplicial clique `Ks` (`hKs`); `hJ : H.frustration.CycleSymmetriesCommute` (v1 Theorem 1(iii) as a hypothesis). Hermiticity of the Pauli terms is not a premise: it is a field of `SimplicialModeHamiltonian` (`term_selfAdjoint`), which supplies `hstar` of the first row | v1 Theorem 2, first part: the family `Pi_l` of the first row and, for each `l`, a `ModeSector` with `Pi = Pi_l`, `zG = SimpleGraph.sectorPolynomial H.coupling {} l`, `zK = SimpleGraph.sectorPolynomial H.coupling Ks l`. Not used here: the no-common-root hypothesis per sector. Non-vacuity: `SimpleGraph.CycleSymmetrySectorsExample.ham_cycleSymmetriesCommute`, `SimpleGraph.CycleSymmetrySectorsExample.exists_two_sectors` (4-cycle, two sectors `J = +-1`) |
| `SimpleGraph.PauliFrustrationRepresentation.exists_jointSpectralProjections` | `H : G.PauliFrustrationRepresentation (Matrix (Fin d) (Fin d) ℂ)`; claw-free `G` (`hclaw`); `hstar`: every Pauli term is self-adjoint; no other premise (unqualified name) | `SimpleGraph.PauliFrustrationRepresentation.exists_jointSpectralProjections_of_cycleSymmetry_commute` with `hJ` supplied by `SimpleGraph.PauliFrustrationRepresentation.cycleSymmetriesCommute`: the finite set `Lambda` and the projectors `Pi_l` of v1 Theorem 2, first part. Not stated on its own by a committed example (section I, item 3); used inside `paperCorollary1` (instantiated by `SimpleGraph.Corollary1Example.paperCorollary1_two_sectors`); `paperTheorem3` restates the same decomposition through the conditional `exists_jointSpectralProjections_of_cycleSymmetry_commute`; `TheoremOneIIIConsequencesExample` does not instantiate it |
| `SimpleGraph.SimplicialModeHamiltonian.exists_modeSectors` | `H : G.SimplicialModeHamiltonian Ks (Matrix (Fin d) (Fin d) ℂ)`; claw-free `G` (`hclaw`); simplicial clique `Ks` (`hKs`); no other premise (unqualified name); Hermiticity of the Pauli terms is the field `term_selfAdjoint` | `SimpleGraph.SimplicialModeHamiltonian.exists_modeSectors_of_cycleSymmetry_commute` with `hJ` supplied by `SimpleGraph.PauliFrustrationRepresentation.cycleSymmetriesCommute`: the family `Pi_l` and, for each `l`, a `ModeSector` with `zG = SimpleGraph.sectorPolynomial H.coupling {} l`, `zK = SimpleGraph.sectorPolynomial H.coupling Ks l`. The non-degeneracy hypothesis is not used. Instantiated on the 4-cycle model only for `sum_l Pi_l = 1` and the existence of the `ModeSector`s: `SimpleGraph.TheoremOneIIIConsequencesExample.exists_modeSectors_ham` |
| `SimpleGraph.SimplicialModeHamiltonian.exists_crossSectorModes_of_cycleSymmetry_commute` | `H : G.SimplicialModeHamiltonian Ks (Matrix (Fin d) (Fin d) ℂ)`; claw-free `G` (`hclaw`); simplicial clique `Ks` (`hKs`); `hJ : H.frustration.CycleSymmetriesCommute` (v1 Theorem 1(iii) as a hypothesis, hence the name `_of_cycleSymmetry_commute`); `hND : ∀ l : G.EvenHoleDeformationClass → ℝ, ((∃ v : Fin d → ℂ, v ≠ 0 ∧ ∀ C0, G.IsEvenHoleCarrier C0 → (J_{C0}).mulVec v = (l(<C0>) : ℂ) • v) ∧ ∀ κ, ¬ G.IsEvenHoleClass κ → l κ = 0) → IsCoprime (SimpleGraph.sectorPolynomial H.coupling ∅ l) (SimpleGraph.sectorPolynomial H.coupling Ks l)` (the antecedent says that `l` is a joint eigenvalue tuple of the `J_{C0}` that occurs; the clause on non-hole classes only discards junk coordinates, which `SimpleGraph.sectorPolynomial` does not see). Neither premise is a conclusion | the sectors of `SimpleGraph.SimplicialModeHamiltonian.exists_modeSectors_of_cycleSymmetry_commute`, and in every sector `l` of `Lambda`: `r l = natDegree z_{{},l}` distinct positive `u l j` with `z_{{},l} = prod_j (1 + C ((u l j)⁻¹ ^ 2) * X)`, positive radicand `z_{Ks,l}(-u^2) z_{{},l}'(-u^2)`, `T(u) T(-u) Pi_l = 0` at `u = u l j`; the explicit modes `psi l j = SimpleGraph.SimplicialModeHamiltonian.explicitIncognitoMode H (Pi l) z_{{},l} z_{Ks,l} (u l j)`; for all `l, l'` in `Lambda`: `Pi_l psi_{l',k} = psi_{l',k} Pi_l = (if l = l' then psi_{l',k} else 0)`, `[Pi_l, psi_{l',k}] = 0` and with `psi^dagger`, `{psi_{l,j}, psi_{l',k}^dagger} = (if l = l' ∧ HEq j k then Pi_l else 0)` (v1 Lemma 14; `HEq` because `j`, `k` have different types for `l ≠ l'`), `{psi, psi} = 0`, `{psi^dagger, psi^dagger} = 0`. The cross-sector part uses only orthogonality of the `Pi_l` |
| `SimpleGraph.SimplicialModeHamiltonian.freeFermionSolution_of_cycleSymmetry_commute` | `H : G.SimplicialModeHamiltonian Ks (Matrix (Fin d) (Fin d) ℂ)`; claw-free `G` (`hclaw`); simplicial clique `Ks` (`hKs`); `hJ : H.frustration.CycleSymmetriesCommute` (Theorem 1(iii) as a hypothesis, discharged in `SimpleGraph.SimplicialModeHamiltonian.paperTheorem2_of_sectorCoprime`, next rows); `hND` exactly as for `SimpleGraph.SimplicialModeHamiltonian.exists_crossSectorModes_of_cycleSymmetry_commute` (restated there); no others | v1 Theorem 2 (repo Theorem 2), qualified by `hJ` and `hND`: everything in the previous row, and `N l j = 4 u l j sqrt(z_{Ks,l}(-u^2) z_{{},l}'(-u^2)) > 0`, `eps l j = (u l j)^{-1}`, `psi l j = (N l j)^{-1} Pi_l T(-u) chi T(u)` given by these formulas for all `l`, `j` (bound by `∃` only to be named, not chosen), `[H, psi_{l,j}] = 2 eps psi_{l,j}`, `[H, psi_{l,j}^dagger] = -2 eps psi_{l,j}^dagger` (v1 Lemma 13), and `H = sum_{l in Lambda} (sum_j eps_{l,j} (psi_{l,j} psi_{l,j}^dagger - psi_{l,j}^dagger psi_{l,j})) Pi_l` (v1 Theorem 2, Lemma 15). Deviations from v1: the premises `hJ`, `hND`; the inner index `Fin (r l)`, `r l = deg z_{{},l}`, instead of `alpha(G)`; the added relations `{psi, psi} = 0`, `{psi^dagger, psi^dagger} = 0`; `[H, psi^dagger] = -2 eps psi^dagger` is v1 Lemma 13 for `-j` with `psi_{J,-j} := psi_{J,j}^dagger` (never defined in v1); `eps = 1/u` uses `u > 0`. Only `Matrix (Fin d) (Fin d) ℂ`. Non-vacuity of all premises: `SimpleGraph.FreeFermionSolutionExample.freeFermionSolution_ham1` and `SimpleGraph.CrossSectorRelationsExample.exists_crossSectorModes_ham1`, one-vertex model without even holes (every `J` is `0`); the 4-cycle model `SimpleGraph.CycleSymmetrySectorsExample.ham` satisfies `hJ` but, by hand computation, not `hND` in its sector `J = +1`; the even-hole instance (`C_4`, `hND` by `SimpleGraph.FreeFermionSolutionMultiSectorExample.ham2_hND`) is `SimpleGraph.FreeFermionSolutionMultiSectorExample.theorem2_two_sectors`, via `SimpleGraph.SimplicialModeHamiltonian.paperTheorem2_of_sectorCoprime` (section I, item 10) |
| `SimpleGraph.SimplicialModeHamiltonian.exists_crossSectorModes_of_sectorCoprime` | as `SimpleGraph.SimplicialModeHamiltonian.paperTheorem2_of_sectorCoprime`: `hclaw`, `hKs`, `hND` | `SimpleGraph.SimplicialModeHamiltonian.exists_crossSectorModes_of_cycleSymmetry_commute` with `hJ` supplied by `SimpleGraph.PauliFrustrationRepresentation.cycleSymmetriesCommute`: the sectors `Pi_l`, the roots `u_{l,j}`, the explicit modes `psi_{l,j}`, `[Pi_l, psi_{l',k}] = 0` and the canonical anticommutation relations across and within sectors. Not instantiated by a committed example (section I, items 2, 10) |
| `SimpleGraph.SimplicialModeHamiltonian.paperTheorem2_of_sectorCoprime` | `H : G.SimplicialModeHamiltonian Ks (Matrix (Fin d) (Fin d) ℂ)`; claw-free `G` (`hclaw`); simplicial clique `Ks` (`hKs`); `hND` exactly as for `SimpleGraph.SimplicialModeHamiltonian.exists_crossSectorModes_of_cycleSymmetry_commute` (restated in `SimpleGraph.SimplicialModeHamiltonian.exists_crossSectorModes_of_sectorCoprime`); no other premise. `hND` is not a conclusion; it is necessary for v1's `N` to be nonzero at every root (`docs/V1_ERRATA.md` U1) | v1 Theorem 2 (repo Theorem 2), qualified by `hND` only: the conclusion of `SimpleGraph.SimplicialModeHamiltonian.freeFermionSolution_of_cycleSymmetry_commute` (previous rows) with `hJ` supplied by `SimpleGraph.PauliFrustrationRepresentation.cycleSymmetriesCommute`. The name carries `_of_sectorCoprime` because `hND` is a premise beyond the setup; the unqualified `paperTheorem2` is not exported. Deviations from v1: `hND`; `Fin (r l)`, `r l = deg z_{{},l}`, instead of `alpha(G)`; `Matrix (Fin d) (Fin d) ℂ` only; the added relations `{psi, psi} = 0`, `{psi^dagger, psi^dagger} = 0`; `psi_{J,-j} := psi_{J,j}^dagger`; `eps = 1/u` with `u > 0`. `hND` is all-or-nothing. Instantiated: `SimpleGraph.FreeFermionSolutionMultiSectorExample.theorem2_two_sectors` (section I, item 10) |
| `SimpleGraph.SimplicialModeHamiltonian.ModeSector.solution_on_sector` | a `ModeSector` `S` of `H : G.SimplicialModeHamiltonian Ks (Matrix (Fin d) (Fin d) ℂ)`; `hclaw`; `hKs`; `u : Fin r → ℝ` positive and injective; `S.zG = prod_j (1 + C ((u j)⁻¹ ^ 2) * X)`; positive radicands `S.zK.eval (-u_j^2) * (derivative S.zG).eval (-u_j^2)`; `psi j = explicitIncognitoMode H S.Pi S.zG S.zK (u j)`. No coprimality, no `hJ` | in one sector: `[H, psi_j] = 2 u_j^{-1} psi_j`, `[H, psi_j^dagger] = -2 u_j^{-1} psi_j^dagger` (v1 Lemma 13) and `H Pi = sum_j u_j^{-1} [psi_j, psi_j^dagger]` (v1 Lemma 15, via `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.hamiltonian_mul_Pi_matrix`, no hypothesis on the charges). Same class B data as `eigenmode`. The one-mode relations are `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.commutator_psiPlus` and `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.commutator_psiMinus` (`D : S.Nondegenerate`, `hclaw`, `hKs`) |
| `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Orthogonal` and its consequences (`SimpleGraph.SimplicialModeHamiltonian.ModeSector.Orthogonal.commute_psiPlus`, `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Orthogonal.psiPlus_anticomm_psiMinus`), `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Family.psi_anticomm_star_psi`, `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Family.commute_Pi_psi` | two sectors with `Pi_S Pi_{S'} = 0` (`Orthogonal`); for `Family`: pairwise orthogonal sectors `S l` with `Nondegenerate` data `D l` (`hS`), and `hclaw`, `hKs` for the anticommutation statements | the cross-sector half of v1 Lemma 14 (`{psi_{J,+j}, psi_{J',-k}} = 0` for `J ≠ J'`) and of the commutation `[Pi_J, psi_{J',j}] = 0` of v1 Theorem 2; the `Orthogonal` statements need no claw-freeness, and the `Nondegenerate` data only supplies the modes |
| `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.hamiltonian_mul_Pi`, `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.hamiltonian_mul_Pi_matrix` | `Nondegenerate` data; `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.hamiltonian_mul_Pi` also `Q^(k) Pi = 0` for `k > r`, which `SimpleGraph.SimplicialModeHamiltonian.ModeSector.Nondegenerate.hamiltonian_mul_Pi_matrix` discharges in matrix algebras | v1 Lemma 15 for one sector; the sum over sectors needs `sum_J Pi_J = 1` and is `SimpleGraph.SimplicialModeHamiltonian.freeFermionSolution_of_cycleSymmetry_commute` (below), under `hJ` and `hND`; not named `paperLemma15` |
| `SimpleGraph.krylovRow_mul_sectorIndepSeries`, `SimpleGraph.sectorRow_pow_eq_of_closure`, `SimpleGraph.sectorRow_pow_wandReverse` | none beyond the setup: finite claw-free `G`, simplicial `K`, any field, arbitrary `lambda` | the closed form behind Theorem 3 with hole terms, v1 Lemma 16 and Eq. (pathcircle) for the corrected matrix; the identity is not stated in v1, so no `paper` prefix |
| `SimpleGraph.paperLemma18`, `SimpleGraph.paperLemma18_of_deformationStep` | simplicial clique `K` (`hK`); claw-free `G` (`hclaw`); couplings `b`; arbitrary `lam`; `3 ≤ P.path.card` (`hlen`, the literal `ℓ ≥ 2`, unused); `P'` in the deformation closure of `P` in `G.adjoinRootAt K` (resp. a single-vertex deformation step); `R` a field (`DecidableEq (CliqueRootedInducedPath G K)` only to form matrix powers). No premise beyond v1's setup | v1 Lemma 16 (repo Lemma 18): `(A^k)_{{j*},P} = (A^k)_{{j*},P'}` for all `k`, for `A = SimpleGraph.cliqueHoppingMatrix` (corrected matrix, not the printed one); unqualified name because the premises are v1's setup. Proof: `SimpleGraph.sectorRow_pow_eq_of_closure`; v1's last-crossing substitution is not used (`docs/V1_ERRATA.md`, E14) |
| `SimpleGraph.PrintedNormalisation.Example.printed_normalisation_counterexample`, `SimpleGraph.PrintedNormalisation.Example.printed_pow_unit`, `SimpleGraph.PrintedNormalisation.Example.printed_pow_six_package` | none (statements about an explicit 7-vertex claw-free graph with the simplicial clique `{2, 5}`); `printed_pow_six_package` and `printed_pow_unit` also take `SimpleGraph.IsPrintedNormalisation`; fields of characteristic 0 | for the printed matrix `SimpleGraph.printedHoppingMatrix` with any `SimpleGraph.IsPrintedNormalisation` (fixed source, sum over its targets, no sign): unit couplings and `lambda = 1` give `(A^6)_{{j*},P} = 42` and `(A^6)_{{j*},P'} = 40` for the single-vertex deformation `P'` of `P` (rows agree for `k < 6`); `b^2 = (4,4,1,3,5,4,4)`, `lambda = 3` give `428` and `422`. Checked in the kernel on a decidable model proved to represent the repo's structures. Not machine-checked: that the printed sentence of v1 L1445 means `SimpleGraph.IsPrintedNormalisation`; minimality of the example; the value `398` of the corrected matrix |

### G. Not formalised, with the nearest declarations

- v1's own proof of Theorem 1(iii), by the obstruction search (v1 Lemmas 7-10, repo Lemmas 12,
  14, 15, 16, and their appendix proofs). It is not formalised in exact form: the Definition 19
  interface layer built for it is degenerate (sections A-D) and the corrected pieces (section B)
  are conditional on supplied data. Theorem 1(iii) itself is proved by a different route
  (section H) that does not use that layer. Missing for an exact formalisation of v1's route: a
  literal Definition 19 object built from two holes, derivation of the repo Lemma 11 (v1 Lemma 6) block data from
  it (replacing the degenerate interface of section D), an obstruction-search model that starts
  from a nonempty prefix, existence, progress and termination of the search, the (C31)
  deleted-source gap, and oddness of `|W n dO|` (`docs/V1_ERRATA.md`, U6-U8). None of these is
  needed for any declaration named in section F.
- Theorem 2: algebras other than `Matrix (Fin d) (Fin d) ℂ`; a per-sector form of `hND` is
  open; a multi-sector instance with an even hole satisfying `hND` is
  `SimpleGraph.FreeFermionSolutionMultiSectorExample.theorem2_two_sectors` (section I, item 10). The premise
  `hND` is part of the corrected statement (`docs/V1_ERRATA.md`, U1), not to be discharged.
- Corollary 1 (v1 Corollary 12, L1341-1349). The anticommutator identity
  `Pi_l {ad^j chi, ad^k chi} = 2 M_jk Pi_l` is
  `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1` over the joint
  eigenprojectors, with the sector forms `paperCorollary1_of_commute` and
  `paperCorollary1_of_cycleAlgebra` and the even-hole-free form
  `paperCorollary1_of_evenHoleFree` (section F). Not formalised, in every case: the positive
  definiteness of `M` (v1 L1406-1409) and the Majorana modes (v1 L1410-1430). These come after the
  proof of Corollary 12 in v1. No declaration constructs the modes, and none of the Corollary 1
  declarations states positive definiteness (`docs/V1_ERRATA.md`, E1, U5).

## Audit 2026-10-30

Basis. Declarations below were checked to exist in the current build, and each depends only on
`propext`, `Classical.choice`, `Quot.sound` (2026-11-03). The state audited is the commit that
proves Theorem 1(iii) and discharges it in Theorems 2 and 3, extended by commit f2c3548 (Corollary 1
over the joint eigenprojectors, Lemma 1 for a bare scaled representation, and the non-vacuity
witnesses `TheoremOneExample`, `FreeFermionSolutionMultiSectorExample`, `Corollary1Example`). v1 line numbers refer to `main.tex`
of arXiv 2305.15625v1.

### H. Theorem 1(iii) and the final forms of Theorems 2 and 3

Statement. `SimpleGraph.PauliFrustrationRepresentation.paperTheorem1iii` is v1's Theorem 1(iii)
(L864-871): for a claw-free finite `G`, `H : G.PauliFrustrationRepresentation A`, and even-hole
carriers `C0`, `C0'`, `[J_{C0}, J_{C0'}] = 0`. Premises: the representation, finiteness of `V`,
claw-freeness, and `C0`, `C0'` being even-hole carriers. The ring `A` is arbitrary, so the Lean
statement is more general than v1's (Pauli strings with scaled terms): no relation
`h_j^2 = b_j^2` and no invertibility of 2 is used, because the cancellation is a pairing of
terms. The statement is v1's; the proof is not.

Route, by role (modules in parentheses; all declarations are in the namespace `SimpleGraph`):

| Role | Declarations |
|---|---|
| Expansion of `[J_{C0}, J_{C0'}]` over the closures (v1 L934-936; `TheoremOneIIIExpansion`) | `SimpleGraph.PauliFrustrationRepresentation.commutator_generalizedCycleSymmetryOp_pair_eq_sum` |
| Hole-class states and clone runs (`T3HoleClassRun`, `T3OddBlock`, `T3FixedPairing`) | `SimpleGraph.IsHoleClasses`, `SimpleGraph.ClassStep`, `SimpleGraph.ClassRun`, `SimpleGraph.OddBlock`, `SimpleGraph.SideBlock`, `SimpleGraph.FPDeformation`, `SimpleGraph.FPDeformation.carrier_fwdEnd`, `SimpleGraph.FPDeformation.carrier_bwdEnd` |
| Frame sign lemma (`T3FrameSign`): the closed form of v1's three-line display L1218-1220 | `SimpleGraph.PauliFrustrationRepresentation.evenHoleOperator_mul_evenHoleOperator_holeClasses` (`h_C h_C' = (-1)^{c(C,C')} h_C' h_C`), `SimpleGraph.PauliFrustrationRepresentation.commutator_toggle_holeClasses` |
| Cancellation by a palindromic deformation (`T3PalindromicCancel`): sign `(-1)^{c(T, C)}`, replacing "`\|W n dO\|` odd" (L1226-1227, L1234) | `SimpleGraph.PauliFrustrationRepresentation.commutator_palindromic`, `SimpleGraph.PauliFrustrationRepresentation.commutator_palindromic_of_isOdd`, `SimpleGraph.PauliFrustrationRepresentation.commutator_palindromic_add_eq_zero_of_isOdd` |
| Pairing index (`T3PairingIndex`, `T3PairingIndexCount`, `T3PairingIndexInvariance`, `T3PairingIndexUpdate`); no counterpart in v1 | `SimpleGraph.pairingIndex`, `SimpleGraph.pairingIndex_emod_two`, `SimpleGraph.matchedW`, `SimpleGraph.crossedW`, `SimpleGraph.anticommutingVertices_eq_matchedW_union_crossedW`, `SimpleGraph.pairingIndex_eq_card_sub_card`, `SimpleGraph.FPDeformation.pairingIndex_ends`, `SimpleGraph.OddBlock.pairingIndex_fwdState` |
| Candidate set `K*` and the involution (`T3PalindromicToggles`, `T3PalindromicCriterion`, `T3StepCondsTransport`, `T3ToggleStable`, `T3TogglesInvariant`, `T3PairingInvolution`) | `SimpleGraph.palindromicToggles`, `SimpleGraph.PauliFrustrationRepresentation.commutator_palindromicToggle`, `SimpleGraph.FPDeformation.palindromic_iff_stepConds`, `SimpleGraph.FPDeformation.toggle_stable`, `SimpleGraph.palindromicToggles_toggle`, `SimpleGraph.chosenPalToggle`, `SimpleGraph.holePairToggle`, `SimpleGraph.holePairToggle_involutive`, `SimpleGraph.holePairToggle_ne`, `SimpleGraph.holePairToggle_mem_closure`, `SimpleGraph.PauliFrustrationRepresentation.commutator_holePairToggle` |
| Tether lemma, componentwise (`T3ComponentTether`, `T3BlockPathBridge`): v1 L913 | `SimpleGraph.component_matched_le_crossed`, `SimpleGraph.OddBlock.card_matchedW_le_one`, `SimpleGraph.OddBlock.exists_of_untethered` |
| Good candidate by counting (`T3GoodCandidate`), replacing the pigeonhole of v1 L1158 | `SimpleGraph.exists_goodCandidate` |
| Separator lemma and parity (`T3SeparatorComponent`, `T3SeparatorParity`) | `SimpleGraph.OddBlock.separators_sameComponent`, `SimpleGraph.OddBlock.separators_components_le`, `SimpleGraph.OddBlock.crossCount_carrier_mod_two`, `SimpleGraph.OddBlock.separatorIncidence_mod_two`, `SimpleGraph.OddBlock.requires_contains_separator` |
| Lift lemma and existence (`T3Lift`, `T3Existence`), replacing the obstruction search of v1 L1128-1198 | `SimpleGraph.FPDeformation.lift`, `SimpleGraph.FPDeformation.exists_palindromic_odd`, `SimpleGraph.palindromicToggles_nonempty` |
| Conclusion (`TheoremOneIII`) | `SimpleGraph.PauliFrustrationRepresentation.commutator_evenHoleOperator_eq_zero_of_palindromicToggles_eq_empty`, `SimpleGraph.PauliFrustrationRepresentation.paperTheorem1iii`, `SimpleGraph.PauliFrustrationRepresentation.cycleSymmetriesCommute` |

Deviations from v1 (module documentation of `TheoremOneIII`; `docs/V1_ERRATA.md` E18):

1. Existence of the cancelling deformation is by source-block induction (strong induction on
   `|s_1 (+) s'_1| + |s_2 (+) s'_2|`), not by v1's obstruction search (L1128-1198); v1 Lemmas 7-10
   (repo Lemmas 12, 14, 15, 16) are not used.
2. The pairing of terms is an involution without fixed points on the nonzero terms, because the
   partner is chosen from `K*(C, C')`, which depends on the carriers only and is stable under its
   own toggles. v1 asserts the pairing (L1237-1241) without this argument.
3. The sign is `c(T, C)`, the number of edges between the toggle and the carrier, odd for
   `T` in `K*(C, C')`; v1's "`|W n dO|` is odd" (L1226-1227, L1234), the anti-Hermiticity of
   `h_O` and `h_O h_O^dagger = B^2 I` (L1227-1236) are not needed.
4. The tether pairing of v1 L913 ("they can be uniquely paired") is used componentwise in the
   existence argument and is proved injective (`component_matched_le_crossed`, through
   `SimpleGraph.EvenHoleLabeling.TetherPair.symm` and
   `SimpleGraph.EvenHoleLabeling.TetherPair.unique`).

Dependency check (a one-off scan of the compiled proof terms for constants in the namespaces
`FixedPairingPathFamily`, `ConcretePathDeformation`, `ObstructionSearch*`, `ArcGraph`, and for
the types `ACHoleStepGeometry`, `FullDefinition19*`, `FiniteMixedSide*`, `Lemma12Definition19Data`,
`Lemma12ResidualData`, `PaperLemma16*`, `SearchDeformation`; not a repository declaration): none
occurs in the proof of any of `paperTheorem1i`, `paperTheorem1ii`, `paperTheorem1iii`,
`cycleSymmetriesCommute`, `exists_jointSpectralProjections`, `exists_modeSectors`,
`exists_crossSectorModes_of_sectorCoprime`, `paperTheorem2_of_sectorCoprime`,
`freeFermionSolution_of_cycleSymmetry_commute`, `paperTheorem3`, `paperTheorem3_modeSectors`,
`paperTheorem3_of_evenHoleFree`, `paperTheorem3_of_evenHoleFree_exists`,
`paperTheorem3_of_commute`, `paperTheorem3_of_cycleAlgebra`, `paperTheorem3_of_commute_exists`,
`paperTheorem3_of_bicommutant`, `paperCorollary1_of_evenHoleFree`,
`paperCorollary1_of_evenHoleFree_ad`, `paperCorollary1_of_commute`,
`paperCorollary1_of_cycleAlgebra`, `paperCorollary1_of_cycleAlgebra_exists`,
`generalizedCharacteristicPolynomial`, `transfer_mul_transfer_neg_mul_sector`,
`fundamentalIdentity`, `ModeSector.eigenmode`, `ModeSector.Nondegenerate.ladder_plus_minus`,
`ModeSector.Nondegenerate.hamiltonian_mul_Pi_matrix`, `ModeSector.solution_on_sector`,
`paperLemma17`, `paperLemma18`, `paperLemma18_of_deformationStep`,
`paperDeformationClosureLemma_of_evenHoleFree`, `sectorRow_pow_eq_of_closure`,
`krylovRow_mul_sectorIndepSeries`, `lemma6`, `lemma9`, `CloneAt.lemma8`. The audits of sections
A-D therefore concern a layer that no theorem of section F rests on. (The modules of that layer
are still imported by the library; the scan is about declarations, not imports.) The proof of
`paperTheorem1iii` does depend on the Theorem 1(ii) deformation-path machinery
(`SimpleGraph.EvenHoleLabeling.SetDeformationPath`, `SimpleGraph.EvenHoleLabeling.TetherPair`) and
on repo Lemmas 7 and 8 and Corollary 3 (v1 Lemmas 2, 3 and Corollary 2).

Non-vacuity. `SimpleGraph.T3Example.exists_palindromic` and `SimpleGraph.T3Example.toggles_mem`
(`T3NonVacuity`: seven-vertex claw-free `graph7`, 4-holes `C = (0,1,2,3)`, `C' = (0,4,5,6)`,
`Psi = -1`, odd palindromic two-block deformation, `K*` nonempty; `SimpleGraph.T3Example.pairingIndex_eq`);
`SimpleGraph.exists_palindromic_two_block_deformation`, `SimpleGraph.fpExD_carrier_fwdEnd`,
`SimpleGraph.fpExD_shared_vertex`, `SimpleGraph.fpExD_union_formula_fails` (`T3FixedPairingExample`:
the carrier reached is `C + T`, not `C + dO`, when two blocks share a vertex, certifying v1's
bookkeeping `C^(m) = C + (+)_r P^(r)` of L986 for the repository's `FPDeformation`);
`SimpleGraph.fpEx_separators_sameComponent`, `SimpleGraph.exists_separators_two`
(`T3SeparatorComponentExample`); `SimpleGraph.fpExD_toggle_stable` (`T3ToggleStableExample`). In
the first two instances the end carrier is `C + T = C'` (`fpExD_fwdEnd`; `T3NonVacuity`, module
documentation), so `C'` is in the deformation closure of `C` and `[J_C, J_{C'}] = 0` is trivial
there; `T3NonVacuity` therefore witnesses the existence layer only. The witness for the content
of Theorem 1(iii) is `SimpleGraph.TheoremOneExample.thm1iii_content` (section I, item 9).

Theorem 2. `SimpleGraph.SimplicialModeHamiltonian.paperTheorem2_of_sectorCoprime` is
`freeFermionSolution_of_cycleSymmetry_commute` with `hJ` supplied by `cycleSymmetriesCommute`;
the sectors and the cross-sector relations are
`SimpleGraph.SimplicialModeHamiltonian.exists_modeSectors` and
`SimpleGraph.SimplicialModeHamiltonian.exists_crossSectorModes_of_sectorCoprime`, and the
spectral part is `SimpleGraph.PauliFrustrationRepresentation.exists_jointSpectralProjections`.
Premises beyond v1's setup: `hND` only. `hND` is necessary for v1's formulas to be defined
(`N = 0` at a common root of `z_{{},l}` and `z_{Ks,l}`; the `C_4` example, hand computation,
`docs/V1_ERRATA.md` U1) and is equivalent to v1's tacit no-common-root condition modulo the
Fundamental Theorem of Algebra (`ModeSectorPositivity.aeval_ne_zero_of_isCoprime`,
`ModeSectorPositivity.isCoprime_of_forall_aeval_ne_zero`). Deviations from v1: `hND`;
`r_l = deg z_{{},l}` modes per sector, summed over `Fin (r_l)`, instead of `alpha(G)`;
`Matrix (Fin d) (Fin d) ℂ` only, with the structure fields `term_selfAdjoint` and `root_sq`
(`chi` Hermitian, `chi^2 = 1`); the added relations `{psi, psi} = 0`, `{psi^dagger, psi^dagger} = 0`;
`psi_{J,-j} := psi_{J,j}^dagger`; `eps = 1/u`, `u > 0`. The conclusion pins every v1 object by
formula: `N` (v1 L2097), `eps = 1/u`, `psi = N^{-1} Pi T(-u) chi T(u)`, `[Pi_l, psi_{l',k}] = 0`,
`{psi, psi'^dagger} = delta delta Pi`, `[H, psi] = 2 eps psi`, and
`H = sum_l (sum_j eps [psi, psi^dagger]) Pi_l`.

Theorem 3. `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperTheorem3` is
`paperTheorem3_of_cycleSymmetry_commute` with `hJ` supplied by `cycleSymmetriesCommute`; premises
`hK`, `hclaw`, `hstar`. Deviations from v1: the corrected matrix
`SimpleGraph.cliqueHoppingMatrix` (E11), right multiplication by `Pi_l`, real couplings,
complex matrices. Non-vacuity: `SimpleGraph.TheoremOneIIIConsequencesExample.paperTheorem3_two_sectors`
(two sectors `J = +-1`, left side nonzero at `k = 1`, no commutation hypothesis supplied).

Corollary 1 (v1 Corollary 12). `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1`
is `paperCorollary1_of_bicommutant` applied to the `Pi_l` of `exists_jointSpectralProjections`;
premises `hK`, `hclaw`, `hstar`, `hχ : chi^2 = 1`. Deviations from v1: the sign `(-1)^j` that the
printed `M_jk` lacks (E1; the printed formula is false already for one vertex), the corrected matrix
`SimpleGraph.cliqueHoppingMatrix`, `chi^2 = 1` as a hypothesis, complex matrices with real
couplings; positive definiteness of `M` and the Majorana modes are not covered. Non-vacuity:
`SimpleGraph.Corollary1Example.paperCorollary1_two_sectors`.

Lemma 1 (v1 Lemma 11). `SimpleGraph.ScaledPauliFrustrationRepresentation.generalizedCharacteristicPolynomial`
holds for a bare scaled representation with `G.IsClawFree` as the only hypothesis, as v1 states it
(Theorem 1 is not needed, E6).

### I. Independent review of the final state: findings and status

An independent review of the state after the Theorem 1(iii) commit produced the findings below.
Items marked open are gaps in what is committed; none is a Lean error. The review's
non-vacuity witnesses were built outside the repository and are not cited as support.

| # | Finding | Status |
|---|---|---|
| 1 | The documents still said that Theorem 1(iii) is open and that Theorems 2 and 3 are conditional on it; none of `paperTheorem1iii`, `cycleSymmetriesCommute`, `paperTheorem2_of_sectorCoprime`, `paperTheorem3`, `exists_jointSpectralProjections`, `exists_modeSectors` was named, and `docs/V1_ERRATA.md` presented U6, U8 as open omissions | Resolved by this update: README, FORMALIZATION, this file, `V1_ERRATA.md` (E18 and the revised E1, E5, E6, E9, E12, E15-E17, U1-U3, U6-U8) and `V1_NUMBERING.md` |
| 2 | `paperTheorem2_of_sectorCoprime` is weaker than v1: premise `hND`; `Fin (r_l)`, `r_l = deg z_{{},l}`, instead of `alpha(G)`; `Matrix (Fin d) (Fin d) ℂ` only (`chi` Hermitian and `chi^2 = 1` as fields). `hND` is all-or-nothing, so nothing is said for a Hamiltonian with one degenerate sector (uniform `C_4`: `J = -1` fine, `J = +1` not) | Documented (E17, U1, section H). Open: a per-sector form that assumes coprimality for the sectors used only |
| 3 | Module documentation of `TheoremOneIIIConsequences.lean` (line 70) says "Non-vacuity of `paperTheorem3`, `exists_jointSpectralProjections` and `exists_modeSectors` on the three-qubit `C₄` model is in `FreeFermionGraphs.TheoremOneIIIConsequencesExample`" and states that the coprimality premise of the Theorem 2 wrappers fails on that model; that file contains only `paperTheorem3_two_sectors` and `exists_modeSectors_ham`, so `exists_jointSpectralProjections` is not instantiated there (it is used only inside `paperCorollary1`, instantiated in `Corollary1Example`; `paperTheorem3` uses the conditional `exists_jointSpectralProjections_of_cycleSymmetry_commute`), and `paperTheorem3_modeSectors` is not instantiated | Open (Lean documentation, not edited here): the only overstatement is `exists_jointSpectralProjections`. These documents state the scope correctly |
| 4 | `paperCorollary1_of_evenHoleFree` is weaker than v1 Corollary 12: no even hole; `chi^2 = 1` an explicit hypothesis (`PauliCliqueHamiltonianRepresentation` has no such field); anticommutator identity only, "`M` real symmetric" only in the `_exists` variants (at the time of the review; since f2c3548 `paperCorollary1`, `paperCorollary1_of_bicommutant`, `paperCorollary1_modeSectors` also state it); no positive definiteness, no Majorana modes. The formula agrees with the corrected one: `ad_H` form `2 (-1)^j (-2)^{j+k} (T^{j+k})_{rr}` times `i^{j+k}` equals `2 (-1)^j (-2i)^{j+k} A^{j+k}` | Documented (E1, U5). No action |
| 5 | `paperCorollary1_of_cycleAlgebra` is stated for any `Pr` in the algebra generated by the `J_c` with `J_c Pr = lambda_c Pr`; no committed declaration applies it or `paperCorollary1_of_commute` to the `Pi_l` of `exists_jointSpectralProjections`; membership of `Pi_l` in the algebra is used inside `JointSpectralProjections.exists_joint_spectral_projections_fintype` but not exported; Theorem 3 has an unconditional `Pi_l` form, Corollary 1 has none (at the time of the review) | Resolved by `SimpleGraph.PauliCliqueHamiltonianRepresentation.paperCorollary1` and `SimpleGraph.SimplicialModeHamiltonian.paperCorollary1_modeSectors` (commit f2c3548): `[H, Pi_l] = 0` from Theorem 1(ii), `[chi, Pi_l] = 0` from `SimpleGraph.PauliCliqueHamiltonianRepresentation.commute_rootOperator_of_forall_commute` (through `SimpleGraph.PauliCliqueHamiltonianRepresentation.commute_rootOperator_generalizedCycleOperator`), via `paperCorollary1_of_bicommutant` |
| 6 | `generalizedCharacteristicPolynomial` (v1 Lemma 11) requires `H : G.PauliCliqueHamiltonianRepresentation K ℝ A`, a root and clique that v1's Lemma 11 does not have and that play no role in the conclusion; a bare claw-free Hamiltonian is covered by `K = {}`, `chi = 1`, but no committed lemma does that reduction (the reduction fails in the zero algebra) | Resolved by `SimpleGraph.ScaledPauliFrustrationRepresentation.generalizedCharacteristicPolynomial` and `..._empty` (commit f2c3548), a direct proof for a bare scaled representation (E6) |
| 7 | `ModeSector.Nondegenerate.ladder_plus_minus` (v1 Lemma 14) is the case `J = J'`, over explicit `Nondegenerate` data; `J != J'` only in Theorem 2 | Documented (E9, E17). No action |
| 8 | `hamiltonian_mul_Pi`, `hamiltonian_mul_Pi_matrix` (v1 Lemma 15) are per-sector; the abstract version assumes `Q^(k) Pi = 0` for `k > r`, which v1 uses silently and the matrix version discharges; the sum over sectors only in Theorem 2 | Documented (E15). No action |
| 9 | Theorem 1(iii) has no committed witness with real content: the instances of `T3NonVacuity` and `T3FixedPairingExample` have `C + T = C'` (one deformation class, `J_C = J_{C'}`), `SimpleGraph.T3Example.graph7` only checks `K*` nonempty (an independent computation outside the repository: all six 4-holes of `graph7` form a single class), and the 4-cycle model has one hole. The statement itself is not vacuous: an eight-vertex claw-free graph with edges `01 12 23 03 45 56 67 47 05 15 25 04 14 26 16`, even holes `{0,1,2,3}` and `{4,5,6,7}`, `c = 7`, lies in two different deformation classes with anticommuting terms in a three-qubit Pauli representation | Resolved by `SimpleGraph.TheoremOneExample.thm1iii_content` (commit f2c3548): this eight-vertex graph, two classes (`not_same_class`), `c = 7`, `terms_anticommute` (only `h_C h_{C'} != h_{C'} h_C`), `[J_C, J_{C'}] = 0`; `c = 7` is read off `edges8`, no Lean statement; also `thm1ii_content`, `thm1i_content`. Open (Lean documentation, not edited here): the `T3NonVacuity` module documentation does not say that its two holes share a class; this file and the README say it |
| 10 | No committed instance shows `hND` together with an even hole, which is the multi-sector content of Theorem 2. It can hold: `C_4`, `Ks = {0,1}`, couplings `(1,1,1,2)`: `z_{Ks} = 1+5x`, `z = 1+7x+9x^2` (`J = +2`) and `1+7x+x^2` (`J = -2`); `z(-1/5) = -1/25, -9/25`; `r = 2 = alpha(G)` in both sectors. In general `z_{{}}(-1/(b_2^2+b_3^2)) = -(b_0^2 b_3^2 + b_1^2 b_2^2 - 2 lambda)/(b_2^2+b_3^2)^2`, so `hND` fails on this `C_4` exactly when `lambda = (b_0^2 b_3^2 + b_1^2 b_2^2)/2`, that is `b_0 b_3 = +- b_1 b_2` in the sector `J = +- b_0 b_1 b_2 b_3` (hand computation from the sector polynomials; exact arithmetic outside Lean) | Resolved by `SimpleGraph.FreeFermionSolutionMultiSectorExample.theorem2_two_sectors` (commit f2c3548): `C_4`, couplings `(1,1,1,2)`, `hND` in both sectors (`ham2_hND`), `r_l = 2`, both `J = +-2` occurring. Open: an instance of `exists_crossSectorModes_of_sectorCoprime` itself; a per-sector form of `hND` |
| 11 | Neither `paperCorollary1_of_evenHoleFree` nor `paperCorollary1_of_cycleAlgebra` is instantiated on a concrete model; `KrylovAnticommutator.printedCorollary1_fails_single_vertex` is a direct `2 x 2` computation that applies neither theorem; the hypotheses of the cycle-algebra form are satisfiable with `Pr` nonzero, and the conclusions are not trivial | Resolved for the main form: `SimpleGraph.Corollary1Example.paperCorollary1_two_sectors` and `hopping_sector_dependent` (commit f2c3548; `C_4`, `(A_l^4)_{j*,j*} = 6 - 2l`); `hopping_plus`, `hopping_minus` apply `paperCorollary1_of_cycleAlgebra` with `Pr = 1 +- J`; `tree_entry` applies `paperCorollary1_of_evenHoleFree` to the one-vertex model |
| 12 | The documents contradicted the committed code (`README.md`, this file, `V1_ERRATA.md`, `V1_NUMBERING.md` on Theorem 1(iii), 2, 3) | Resolved by this update (item 1) |
