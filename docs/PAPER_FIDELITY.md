# Manuscript fidelity gates

This document records the acceptance criteria for claiming that a Lean theorem
formalises a numbered result of *A Unified Graph-Theoretic Framework for
Free-Fermion Solvability*.

A successful build establishes type correctness. It does not by itself show
that the formal statement has the same hypotheses, quantifiers, deformation
stage, provenance, or conclusion as the manuscript.

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

## Lemma 14

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

`InitializationFiniteMixedSideLemma14History` represents the literal
initialized Definition 19/20 search history. It is the manuscript setup for the
lemma, not a structure containing any of the four conclusions.

### Provenance audit

The fields and their classes are:

| Lean data | Manuscript object | Class |
|---|---|---|
| `core` | initialized finite deformations, obstruction/dependent outputs, pairing labels, terminal path, nearest-target rule | D |
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

The explicit finite process is the manuscript's nondeterministic corrective
search execution. It is not an additional graph-theoretic premise.

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
- The theorem quantifies over every finite state, including state zero.
- The theorem uses the exact `PaperLemma14Conclusion` at each state.
- The strict-decrease theorem is available for the subsequent termination
  argument but is not smuggled into the Lemma 15 conclusion.

The implementation does not claim that `ObstructionSearchInitialization` alone
deterministically computes the next state. The manuscript search is
nondeterministic at local selection points, so the explicit finite process and
its histories specify the chosen run.


## Lemma 16

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
transport or Lemma 12 certificates as premises.

## Current manuscript coverage

| Manuscript layer | Fidelity status |
|---|---|
| Lemmas 6-10 | Substantial graph-level implementations; complete statement audit remains |
| Definition 14 | Combinatorial token-sliding charges only; operator charge absent |
| Definition 15 | Combinatorial deformation closure only; operator symmetry absent |
| Lemma 11(a)-(b) | Substantial finite/mixed-side proofs; paper-facing constructor audit remains |
| Corollary 11 | Proved on bounded mixed-side finite histories |
| Lemmas 12-13 | General supporting interfaces remain, with the Lemma 12 data constructor completed for Lemma 16 traces |
| Lemma 14 | Exact unqualified theorem proved from the literal initialized finite search history |
| Lemma 15 | Exact all-steps theorem proved for explicit finite corrective rerouting executions |
| Lemma 16 | Exact unqualified theorem on an explicit completed finite Definition 19 trace |
| Lemmas 17-18 | Not complete manuscript-level results |
| Theorem 1(i)-(iii) | Operator commutator statements absent |
| Theorem 2 | Transfer/free-fermion reconstruction absent |
| Theorem 3 and Corollary 1 | Weighted matrix-power and nested-commutator theorem absent |

## Documentation rule

Historical audit documents retain the repository state at their stated date and
baseline. The README and this file are the authoritative current status. Any PR
that changes a paper-facing theorem must update both when the provenance status
changes.
