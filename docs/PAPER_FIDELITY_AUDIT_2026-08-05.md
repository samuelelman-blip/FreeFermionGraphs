# Paper-fidelity audit, 2026-08-05

This audit compares the Lean development through the paper-facing Lemma 16
commit `2c67d9580c61c8cf91b6a9327238f278751b955c` with the manuscript
*A Unified Graph-Theoretic Framework for Free-Fermion Solvability* dated
14 July 2026.

The word **faithful** is used narrowly here: the Lean statement must have the
same mathematical objects, quantifiers, deformation stage, and hypotheses as
the manuscript, or any difference must be stated explicitly in the theorem
name and documentation. A successful build alone is not a fidelity result.

## Static integrity

The reviewed Lemma 16 modules contain no `sorry`, `admit`, project `axiom`,
or `opaque`. The exact paper-facing source at commit
`2c67d9580c61c8cf91b6a9327238f278751b955c` passed a complete local
`lake build` of 1457 jobs.

## Audit conclusion

The repository is mathematically consistent and its current exact
paper-facing endpoints for Lemmas 14 and 15 typecheck. It is **not yet correct
to claim that every numbered manuscript result represented in the repository
has been formalised at exact paper fidelity**. Several earlier files contain
conditional cores or representation-level statements whose comments formerly
called them the manuscript lemma or corollary without recording the extra
premises or the information erased by the representation.

This is a fidelity-status defect, not evidence that the Lean theorems are
false. The statements prove what their formal types say. The defect is that
some names or comments overstate the correspondence with the printed result.

## Result-by-result status

| Manuscript result | Lean endpoint | Fidelity status |
|---|---|---|
| Lemma 6 | `SimpleGraph.lemma6` | Exact for the finite vertex type used by the Hamiltonian setup. |
| Lemma 7 | `IndexedInducedPath.lemma7`, `IndexedInducedHole.lemma7` | Exact neighboring-relation classification at the indexed path/hole interface. |
| Corollaries 2-3 | `IndexedInducedHole.corollary2`, `IsClawFree.corollary3` | Exact, with Corollary 3 stated in a slightly stronger local form. |
| Lemma 8 | `EvenHoleLabeling.CloneAt.lemma8` | Corrected statement. Lean assumes `t` is outside the deformed carrier. The printed lemma omits this premise, although its proof uses Corollary 2 with `t` external. Literally allowing `t = s` gives a counterexample for holes longer than four. |
| Corollaries 4-5 | `CloneAt.corollary4`, `CloneAt.corollary5` | Corrected forms inheriting the external-vertex premise required by Lemma 8. |
| Lemma 9 | `SimpleGraph.lemma9` | Exact deformation-closure neighborhood invariance. |
| Corollary 6 | `SimpleGraph.corollary6` | Exact at the open-neighborhood compatibility interface. |
| Lemma 10 | `FixedPairingPathFamily.lemma10` | Exact once the Definition 19 component partition is represented by `acPaths`, `bdPaths`, and their pairwise-disjointness fields. |
| Corollary 7 | `FixedPairingPathFamily.corollary7` | Conditional core. Endpoint exact-color-class membership is supplied as a premise rather than constructed from an indexed Definition 19 path occurrence. |
| Corollary 8 | `FixedPairingPathFamily.corollary8` | Representation-level only. `O.paths` is a set of vertex subsets, so injectivity of subtype coercion does not prove that an ordered deformation contains no repeated path occurrence. |
| Corollary 9 | `FixedPairingPathFamily.corollary9` | Component-family form. It uses pairwise-disjointness already carried by `FixedPairingPathFamily`; an occurrence-level wrapper for the ordered deformation remains to be constructed. |
| Corollary 10 | `FixedPairingPathFamily.corollary10` | Conditional core. The coloring-class facts proved in the manuscript are explicit premises. |
| Lemma 11 | `ConcretePathDeformation.lemma11` | Conditional integration. It requires `Lemma11AHistoryContext`; the paper-facing file correctly exports only `paperLemma11b_of_historyContext`. |
| Corollary 11 | finite mixed-side history theorems | Proved on explicit bounded histories, but a single audited occurrence-level paper endpoint remains outstanding. |
| Lemma 12 | `FullDefinition19Deformation.lemma12` | The general theorem remains conditional on `Lemma12Definition19Data`. For Lemma 16, `PaperLemma16Trace.toLemma12Definition19Data` now constructs those fields from the literal completed trace. |
| Lemma 13 | `FullDefinition19Deformation.lemma13` | Exact at the `FullDefinition19Deformation` interface, whose successor field records the alternating Definition 19 order. |
| Lemma 14 | `InitializationFiniteMixedSideLemma14History.paperLemma14` | Exact on an explicit finite Definition 19/20 execution history. |
| Lemma 15 | `ObstructionSearchReroutingProcess.paperLemma15` | Exact all-state conclusion on an explicit finite process whose states contain their actual search histories. The optional Eq. (C32) interface still stores path-containment provenance instead of deriving it from dependent index transport; that field is not used in the theorem but remains an implementation-fidelity cleanup. |
| Lemma 16 | `FiniteMixedSideSearchTrace.PaperLemma16Trace.paperLemma16` | Exact on an explicit completed finite Definition 19 trace. The occurrence transport and Lemma 12 data are derived rather than accepted as theorem premises. |
| Lemmas 17-18 | none | Not yet formalised at manuscript level. |
| Theorems 1-3 and Corollary 1 | none at operator level | Not formalised. The Pauli/Hamiltonian layer is absent. |

## Printed Lemma 8 discrepancy

The manuscript states Lemma 8 for a vertex `t` that neighbors exactly one of
the clone pair `{s,a_0}` but does not explicitly say that `t` lies outside
`{s} \cup C`. The proof immediately applies Corollary 2 to `t` as an external
vertex of the deformed hole, so the proof uses the missing condition.

The omission is material. Taking `t = s`, the simple-graph convention gives
`not Adj s s`, while the clone relation gives `Adj s a_0`; hence `t` neighbors
exactly one member of `{s,a_0}`. For an even hole longer than four,
`Gamma_({s} union C)(s) = {a_0,b_0,b_1}`, which is not one of the four displayed
alternatives. The Lean theorem therefore formalises the corrected intended
statement, not the literal printed statement.

## Required remediation before a blanket fidelity claim

1. Keep the Lemma 8 externality correction and record it in the manuscript or
   prove a revised statement with the intended distinctness hypothesis.
2. Add occurrence-indexed Definition 19 path blocks and use them to prove
   Corollaries 7-10 without exact-color hypotheses supplied at the theorem
   boundary.
3. Construct `Lemma11AHistoryContext` from literal finite Definition 19/20
   histories and export exact paper-facing Lemma 11 and Corollary 11 endpoints.
4. Generalise the Lemma 16 construction of `Lemma12Definition19Data` to the
   remaining standalone Lemma 12 interfaces.
5. Derive the Eq. (C32) path-containment facts from the concrete concatenation
   index equivalence rather than storing them in `IsConcatenation`.
6. Connect strict initializer decrease to the terminal unobstructed state used
   by the subsequent corrective-process argument.

## Operational rule

Until the remediation items above are complete, the repository may claim that
its Lean terms are internally checked and that Lemmas 14-16 have exact explicit
history-level endpoints. It must not claim that every numbered result currently
represented is already an exact formalisation of the printed manuscript.
