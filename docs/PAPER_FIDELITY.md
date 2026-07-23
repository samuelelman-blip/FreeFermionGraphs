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

| Component | Provenance | Status |
|---|---|---|
| initialized ordered executions | D | Formalized |
| fixed-pairing output conclusion | E | Formalized |
| obstruction arcs cross pairing types | E | Formalized |
| same-pairing path disjointness | E | Formalized |
| source injectivity at a terminal slot | E | Formalized |
| same-clone claw contradiction | E/M | Formalized |
| stopping-derived clone centre | E | Formalized |
| predecessor original-hole degree two | E from Lemma 11(a) | Formalized |
| predecessor anticommutation from dependent membership and final degree three | E from Lemma 11(b) | Formalized and stage-checked |
| existence of the first-block predecessor with final degree three | M/B | Not yet derived from execution histories |
| propagated centre and original-hole leaf | M/B | Not yet derived from execution histories |
| required propagated nonedges | M/B | Not yet derived from execution histories |
| same-clone/distinct-clone split from the two histories | M/B | Not yet derived from execution histories |

Consequently, the repository must not yet expose an unconditional theorem
named `paperLemma14`. The strongest current bridge is deliberately named
`paperLemma14_of_terminalPredecessorDegreeAnalysis`.

## Additional recurring checks

- **Stage check:** degrees compared in one argument must refer to definitionally
  equal hole objects, or an explicit carrier/index equivalence theorem must be
  supplied.
- **Quantifier check:** pairwise terminal claims must not be strengthened to
  per-arc claims unless that strengthening is separately proved.
- **Orientation check:** statements may use a chosen indexing internally, but
  public conclusions must be invariant under reversing or cyclically shifting
  the indexed hole.
- **Boundary-case check:** empty deformations, first blocks, the initial-tether
  stopping branch, and later Definition 20 stopping must be covered explicitly.
- **Dependency check:** a proof of Lemma 14 may use Lemmas 7–13, but it may not
  consume a structure field that already assumes a conclusion of Lemma 14(iv).
- **Model check:** small finite claw-free examples should test the encodings of
  clonehood, dependent subsets, hole degree, and path anticommutation. These
  tests supplement but do not replace proofs.
