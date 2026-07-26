# Manuscript fidelity gates

This document records the acceptance criteria for claiming that a Lean theorem
formalizes a numbered result of *A Unified Graph-Theoretic Framework for
Free-Fermion Solvability*.

A successful build establishes type correctness. It does not by itself show
that the formal statement has the same hypotheses, deformation stage, or
conclusion as the manuscript.

## Merge gates

A pull request touching a numbered manuscript result must identify:

1. the exact manuscript statement or proof sentence being formalized;
2. the Lean object corresponding to every manuscript object;
3. the deformation stage of every hole and degree expression;
4. the provenance of every new structure field;
5. any additional premise not present in the manuscript;
6. the exact paper-facing theorem that the change helps prove.

An unqualified theorem name such as `paperLemma14` is reserved for a theorem
with no additional premise beyond the manuscript setup. Conditional bridges
must retain names of the form `paperLemma14_of_...`.

## Provenance classes

Every field used by a paper-facing theorem belongs to one of these classes.

| Class | Meaning | Permitted in final paper theorem |
|---|---|---|
| D | Literal definition or algorithm data from the manuscript | Yes |
| E | Derived from D by a previously audited theorem | Yes |
| M | Intermediate claim explicitly proved in the manuscript | Only after it is derived from D/E |
| B | Boundary certificate currently standing in for an unformalized manuscript argument | No |

## Lemma 11(b)

Manuscript target: for `u ∈ U^(r,s)` whose operator commutes with the path
operator, `Delta_(C^(r))(u) = 4`, and there is an earlier dependent vertex
whose operator anticommutes with the path operator in the same fixed-pairing
path component.

| Manuscript object | Lean object | Stage/provenance | Status |
|---|---|---|---|
| `P^(r)` | `D.path` | D | Audited |
| `U^(r,s)` | `D.dependentAt s` | D | Audited |
| `C^(r)` | `D.finalHole` | D, final hole of the concrete path block | Audited |
| `Delta_(C^(r))(u)` | `D.finalHole.externalDegree u` | D | Audited |
| earlier anticommuting vertex in same component | `EarlierAnticommutingWitnessInUniqueBDPath` | E from the completed Lemma 11(b) descent | Audited at integration level |

`PaperFidelity.paperLemma11b` states the degree directly on `D.finalHole`, so
a future change to the implementation abbreviation `finalDegree` cannot alter
the public deformation stage silently.

## Lemma 14

The exact four conclusions are represented by `PaperLemma14Conclusion`:

1. every initialized output is a possibly empty fixed-pairing deformation;
2. the obstruction graph is bipartite by pairing type;
3. same-pairing deformations are pairwise path-disjoint;
4. every target has at most two incoming arcs and, for two distinct incoming
   arcs, the target is the unique member of exactly one final dependent set.

### Current provenance

Corollary 9 explicitly allows a vertex to belong to one original-hole colour
class and one prime-hole colour class, and consequently to occur on one `ac`
path and one `bd` path. Therefore `ExactlyOneOfFour` is not a faithful generic
hypothesis for a vertex of `P ∩ C_b`, and opposite-family path occurrence cannot
be excluded merely from component membership.

The manuscript's fixed-pairing deformation may contain components from both
`C_a ⊕ C'_c` and `C_b ⊕ C'_d`. The current `SearchPathHistoryWitness` represents
every output path by a concrete block carrying `ACHoleStepGeometry`; the audit
theorem `SearchHistoryData.paths_subset_acPaths` therefore shows that this
interface forces every represented output path into `acPaths`.

`TwoSidedSearchPathHistoryWitness` records an explicit path side. A `bd` block
is interpreted through the side-swapped family obtained by exchanging
`C_a ↔ C_b`, `C'_c ↔ C'_d`, and `acPaths ↔ bdPaths`.

`TwoSidedOrderedPathExecution` migrates the finite block enumeration, output
coverage, source uniqueness, and literal `W \ {source}` stopping invariant.
`TwoSidedOrderedOSExecution` also records the maximal-`L_{r,s}` update rule: the
first introduced vertex of every later block lies in a dependent set of a
strictly earlier block and anticommutes with that block's path.

The history-backed Corollary 11 theorem is now complete on the two-sided
interface. A hypothetical shared dependent vertex first forces both blocks to
have the same `DeformationSide`; the concrete history theorem then applies in
that common orientation, including the `swapSides` presentation of two `bd`
blocks.

`InitializationTwoSidedFirstCommonPathData` now packages exactly the output of
the manuscript's least-common-path argument and derives same-pairing path
disjointness and canonical path ownership. The remaining statement-(iii)
construction is to derive this data from `TwoSidedOrderedOSExecution`, including
the canonical equality of the first introduced endpoint on a common path.

| Component | Provenance | Status |
|---|---|---|
| initialized ordered executions | D | Side-correct local execution interface formalized; construction from the fully formalized `OS` loop remains open |
| final execution hole `C_j^(m)` | D from ordered block sequence, `manuscriptFinalHole` | Formalized, including the empty-execution case, on the old interface |
| fixed-pairing output conclusion | E | Formalized |
| obstruction arcs cross pairing types | E | Formalized |
| same-pairing path disjointness | E from two-sided Corollary 11 once the least-common-path witness is supplied | Formalized through `InitializationTwoSidedFirstCommonPathData`; derivation of that data from the ordered trace remains open |
| source injectivity at a terminal slot | E | Formalized through the old one-sided execution data |
| distinct incoming sources occupy opposite terminal slots | E from slot injectivity and the two-valued slot type | Formalized through the old one-sided execution data |
| target differs from both path endpoints in the remaining two-incoming branch | E from the two scoped endpoint inequalities | Formalized |
| target has an interior terminal-path index, matching `j_(p-1)` with `1 < p` | E from nearest-target membership and endpoint inequalities | Formalized |
| terminal path has at least three vertices in the remaining branch | E from the interior index | Formalized |
| consecutive path segment `j_(p-2) - j'' - j_p` around the target | E from indexed-path order and inducedness | Formalized |
| same-clone claw contradiction | E/M | Formalized |
| stopping-derived clone centre in the initialized original hole | E | Formalized |
| final-hole target clone for an empty initialized execution | E because `manuscriptFinalHole` is the original hole | Formalized from the stopping branch |
| outside-hole plus degree-three geometry implies a final-hole target clone | E from Lemma 7 and the indexed three-neighbor clone theorem | Formalized on the exact `manuscriptFinalHole` stage |
| positive `manuscriptFinalHole` equals the last concrete block final hole | E from the ordered execution definition | Formalized with `lastBlockIndex` on the old interface |
| original-hole vertices avoiding all recorded prior/current paths persist to the positive terminal hole | E from the finite `Lemma11AHistoryContext` carrier chain | Formalized without terminal-specific data |
| distinct `bd` components are disjoint | E from the `bdPaths.Pairwise Disjoint` field | Formalized |
| a missing original-hole vertex occurs on at least one represented prior/current path | E by contraposition from carrier persistence | Formalized without assigning a component family or introduced/removed role |
| a represented vertex occurrence yields an actual output path containing the vertex | E from current `output_mem` and prior `prior_output_mem` | Formalized |
| a missing original-hole vertex equals the removed vertex of a concrete represented step | E from the one-step carrier replacement and finite block/history chains | Formalized without assigning the step to the `ac` or `bd` family |
| current `SearchHistoryData` forces all represented output paths into `acPaths` | E from the stored `ACHoleStepGeometry` of each witness block | Formalized as an audit guard; this old boundary is stronger than the manuscript |
| explicit two-sided path-history interface | D/E through `DeformationSide`, `swapSides`, and `TwoSidedSearchPathHistoryWitness` | Formalized |
| side-correct ordered path enumeration and stopping invariants | D in `TwoSidedOrderedPathExecution` | Formalized |
| side-correct maximal-step earlier selection | D in `TwoSidedOrderedOSExecution.earlierSelection` | Formalized as the literal local update invariant; construction from the concrete loop remains open |
| shared dependent vertex forces equal component sides | E from Definition 20 prime membership, oriented `dependent_mem_cd`, and overlap-aware prime colour exclusion | Formalized |
| full two-sided no-shared-dependent-anticommuting-witness theorem | E from side reduction and the concrete finite-history Corollary 11 proof | Formalized |
| side-correct first-common-path witness interface | M/D in `InitializationTwoSidedFirstCommonPathData` | Formalized as the exact output consumed by Corollary 11; construction from ordered traces remains open |
| terminal obstruction path is absent from every actual execution path and from the output path set | E from nearest-target membership and the literal stopping rule | Formalized through the old execution interface |
| terminal obstruction path is absent as a represented component of the last block history | E from history-output provenance and the stopping rule | Formalized through the old interface; its vertices may still occur on opposite-family paths |
| prior blocks represented by a positive `SearchPathHistoryWitness` are paths of the same search output | D in `prior_output_mem`, expressing literal earlier-block provenance | Recorded explicitly in both history interfaces; construction from the concrete `OS` loop remains part of the execution-data boundary |
| terminal path belongs to the `bd` family indexed by the opposite target pairing, hence to the incoming source family | D interface in `InitializationTerminalPathComponentData`, then E from obstruction-pairing transport | Recorded explicitly; construction from the concrete `OS` stopping path remains part of the execution-data boundary |
| `P ∩ C_b ⊆ C_j^(m)` for the terminal path | M/B | Not yet formalized faithfully: derive the two-sided least-common-path data from the ordered trace, then prove that a missing `C_b` vertex was removed by a prior `bd` block |
| terminal-path `C_b` vertices belong to the initialized original-hole carrier | D/M | Still requires the literal identification of `C_b` as an original-hole colour class in the initialized data |
| outside-hole and degree-three geometry on the last positive block | M/B | Exact remaining terminal-tether argument after the corrected carrier step |
| scoped target clone interface for the full interior case | M/B | Conditional bridge reduced to the scoped positive last-block geometry |
| unrestricted target clone for every incoming arc | stronger than the manuscript branch | Retained only as an older convenience interface; not used by the strongest fidelity bridge |
| uniqueness of the final-hole clone centre for one incoming search | E from induced-hole clone uniqueness | Formalized |
| canonical centre selected under an interior premise | E once the scoped existence fact is supplied | Formalized, choice-independent, and proof-irrelevant |
| equality-versus-inequality split of the two scoped final-hole clone centres | E once both interior witnesses are supplied | Formalized; no longer an independent branch certificate |
| predecessor original-hole degree two | E from Lemma 11(a) | Formalized |
| predecessor anticommutation from dependent membership and final degree three | E from Lemma 11(b) | Formalized and stage-checked |
| same-centre terminal-neighborhood consequence | M/B | Isolated as a pairwise consequence; not yet derived from the two terminal holes |
| existence of the first-block predecessor with final degree three | M/B | Not yet derived from execution histories |
| propagated centre and original-hole leaf | M/B | Not yet derived from execution histories |
| required propagated nonedges | M/B | Not yet derived from execution histories |

Consequently, the repository must not yet expose an unconditional theorem
named `paperLemma14`. The strongest current bridge is deliberately named
`paperLemma14_of_interiorTerminalCloneData_and_consequences`.

## Additional recurring checks

- **Stage check:** degrees compared in one argument must refer to definitionally
  equal hole objects, or an explicit carrier/index equivalence theorem must be
  supplied.
- **Quantifier check:** pairwise terminal claims must not be strengthened to
  per-arc claims unless that strengthening is separately proved.
- **Orientation check:** statements may use a chosen indexing internally, but
  public conclusions must be invariant under reversing or cyclically shifting
  the indexed hole.
- **Overlap check:** original-hole and prime-hole colour memberships are not
  globally exclusive; any exact-colour hypothesis must be justified for the
  specific vertex class under consideration.
- **Two-sided path check:** a fixed-pairing deformation may contain both
  `acPaths` and `bdPaths`; a history or execution interface restricted to one
  side cannot be used as the final construction of the manuscript search trace.
- **Boundary-case check:** empty deformations, first blocks, the initial-tether
  stopping branch, and later Definition 20 stopping must be covered explicitly.
- **Dependency check:** a proof of Lemma 14 may use Lemmas 7–13, but it may not
  consume a structure field that already assumes a conclusion of Lemma 14(iv).
- **Model check:** small finite claw-free examples should test the encodings of
  clonehood, dependent subsets, hole degree, and path anticommutation. These
  tests supplement but do not replace proofs.
