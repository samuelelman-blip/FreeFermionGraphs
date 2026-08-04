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
  stopping branch, and later Definition 20 stopping must be covered.
- **Dependency check:** a proof of Lemma 14 may use Lemmas 7-13, but it may not
  consume a field that already assumes a conclusion of Lemma 14(iv).

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

The repository now constructs substantial bounded mixed-side execution data and
uses it throughout the finite Lemma 11 and Lemma 14 development. Legacy total
histories remain available internally but are not acceptable final premises for
an unqualified paper theorem.

## Lemma 14

### Manuscript conclusion

`PaperLemma14Conclusion` represents the exact four conclusions:

1. every initialized output is a possibly empty fixed-pairing deformation;
2. the obstruction graph is bipartite by pairing type;
3. same-pairing deformations are pairwise path-disjoint;
4. every target has at most two incoming arcs and, for two distinct incoming
   arcs, the target is the unique member of exactly one final dependent set.

### Current strongest bridge

The current finite endpoint is

```lean
InitializationFiniteMixedSideExecutableLemma14Data
  .paperLemma14_of_executableData
```

with hypotheses

```lean
(L : InitializationFiniteMixedSideExecutableLemma14Data T)
(hclaw : G.IsClawFree)
```

and conclusion `PaperLemma14Conclusion I`.

The theorem is valid and proves the exact conclusion, but it is conditional on
`L`. The repository does not yet construct `L` from
`InitializationFiniteMixedSideTerminalCoreData T` and claw-freeness alone.

### What the current route genuinely derives

The current route removes several direct conclusion certificates:

- terminal parity, endpoint-side membership, and odd path cardinality are
  derived from coordinates of the form `j₀-k₀-⋯-k_(ℓ-1)-j_ℓ`;
- target degree is transported through finite block replacement once local
  target balance is supplied;
- clone-to-flank adjacency is derived from a tether-link coordinate adjacent to
  the target;
- unequal-centre propagation traces must carry an `IsGenerated` proof using
  only the finite `start` and `snoc` constructors;
- the final theorem concludes the exact four-part `PaperLemma14Conclusion`.

### Remaining provenance boundary

`InitializationFiniteMixedSideExecutableLemma14Data` still supplies data that
has not been derived from the literal initialized Definition 19/20 search:

1. the terminal coordinate package, including cardinality and target-position
   equalities;
2. one local `TargetBalanced` proof for each incoming execution;
3. the stopping tether-link index, centre equality, and direction toward the
   target;
4. a generated unequal-centre trace whose `start` inputs include the required
   initial avoidance and adjacency facts;
5. each propagation `snoc` input's next avoidance and adjacency facts.

`IsGenerated` verifies that the trace has the intended finite constructor
shape. It does not by itself prove that the search supplies the constructor
inputs.

Consequently, the repository must not currently expose an unconditional
`paperLemma14`. The present theorem is correctly named
`paperLemma14_of_executableData`.

### Acceptance criteria for unconditional Lemma 14

An unqualified theorem may be added only after the repository proves a
constructor or equivalent theorem of the form

```lean
InitializationFiniteMixedSideTerminalCoreData T
  → G.IsClawFree
  → InitializationFiniteMixedSideExecutableLemma14Data T
```

or proves `PaperLemma14Conclusion I` directly from the manuscript setup without
an equivalent additional boundary package.

The proof must derive, rather than assume:

- terminal coordinates and target placement from the stopping component;
- local target balance from the Definition 19/20 path geometry;
- the adjacent stopping tether link;
- every local avoidance and adjacency fact used to start and extend the
  unequal-centre propagation.

## Current manuscript coverage

| Manuscript layer | Fidelity status |
|---|---|
| Lemmas 6-10 | Substantial graph-level implementations; complete statement audit remains |
| Definition 14 | Combinatorial token-sliding charges only; operator charge absent |
| Definition 15 | Combinatorial deformation closure only; operator symmetry absent |
| Lemma 11(a)-(b) | Substantial finite/mixed-side proofs; paper-facing constructor audit remains |
| Corollary 11 | Proved on bounded mixed-side finite histories |
| Lemmas 12-13 | Supporting implementations exist; final statement audit remains |
| Lemma 14 | Exact conclusion proved conditionally from executable-data package; unconditional theorem open |
| Lemmas 15-18 | Not complete manuscript-level results |
| Theorem 1(i)-(iii) | Operator commutator statements absent |
| Theorem 2 | Transfer/free-fermion reconstruction absent |
| Theorem 3 and Corollary 1 | Weighted matrix-power and nested-commutator theorem absent |

## Documentation rule

Historical audit documents retain the repository state at their stated date and
baseline. The README and this file are the authoritative current status. Any PR
that changes a paper-facing theorem must update both when the provenance status
changes.
