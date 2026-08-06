from pathlib import Path


def replace_once(text: str, old: str, new: str, label: str) -> str:
    if old not in text:
        raise SystemExit(f"Could not find {label}; refusing a partial integration")
    return text.replace(old, new, 1)


# Root import
root = Path("FreeFermionGraphs.lean")
root_text = root.read_text()
imports = """\nimport FreeFermionGraphs.ObstructionSearchFiniteMixedLemma14History
import FreeFermionGraphs.ObstructionSearchReroutingProcess
import FreeFermionGraphs.Lemma16Unobstructed
import FreeFermionGraphs.Lemma16OccurrenceTransport
import FreeFermionGraphs.Lemma16Paper
"""
if "import FreeFermionGraphs.Lemma16Paper" not in root_text:
    root_text = root_text.rstrip() + imports
root.write_text(root_text)


# README
readme = Path("README.md")
text = readme.read_text()
text = replace_once(
    text,
    """The finite Lemmas 14 and 15 integration can be checked first with:

```bash
lake build FreeFermionGraphs.ObstructionSearchReroutingProcess
```
""",
    """The finite Lemmas 14-16 integration can be checked first with:

```bash
lake build FreeFermionGraphs.ObstructionSearchReroutingProcess
lake build FreeFermionGraphs.Lemma16Paper
```
""",
    "README focused-build block",
)
text = replace_once(
    text,
    """and the all-state Lemma 15 theorem

```lean
ObstructionSearchReroutingProcess.paperLemma15
```

The latter proves `PaperLemma14Conclusion` for every state of an explicit
finite corrective rerouting execution. Such an execution records the selected
finite Definition 19/20 history at each state and one transition for every
application of Eqs. (C31) and (C32).
""",
    """and the all-state Lemma 15 theorem

```lean
ObstructionSearchReroutingProcess.paperLemma15
```

The paper-facing Lemma 16 theorem is

```lean
FiniteMixedSideSearchTrace.PaperLemma16Trace.paperLemma16
```

It derives the occurrence-level Corollaries 9-10 transport and constructs the
`Lemma12Definition19Data` certificate from an explicit completed finite trace.
For an unobstructed deformation it proves both
`dependentUnion ⊆ terminalHole` and the palindromic reverse run of Lemma 12.

The Lemma 15 theorem proves `PaperLemma14Conclusion` for every state of an
explicit finite corrective rerouting execution. Such an execution records the
selected finite Definition 19/20 history at each state and one transition for
every application of Eqs. (C31) and (C32).
""",
    "README theorem-status block",
)
text = replace_once(
    text,
    """- Corollaries 7-10 still expose coloring or occurrence information as premises
  or erase repeated path occurrences by using sets of paths;
- Lemma 11 still depends on `Lemma11AHistoryContext`;
- Lemma 12 still depends on `Lemma12Definition19Data`;
""",
    """- the generic Corollaries 7-10 interfaces still expose some coloring or
  occurrence information as premises, although Lemma 16 now derives its
  required occurrence-level Corollaries 9-10 transport from the finite trace;
- Lemma 11 still depends on `Lemma11AHistoryContext`;
- the general Lemma 12 theorem still consumes `Lemma12Definition19Data`, while
  Lemma 16 now constructs that data from `PaperLemma16Trace`;
""",
    "README audit-boundary bullets",
)
text = replace_once(
    text,
    """| Lemma 15 | Exact all-state conclusion on an explicit finite rerouting process; Eq. (C32) provenance cleanup remains |
| Lemmas 16-18 | Not yet formalised at manuscript level |
""",
    """| Lemma 15 | Exact all-state conclusion on an explicit finite rerouting process; Eq. (C32) provenance cleanup remains |
| Lemma 16 | Exact on an explicit completed finite Definition 19 trace |
| Lemmas 17-18 | Not yet formalised at manuscript level |
""",
    "README status-table Lemma 16 row",
)
text = replace_once(
    text,
    """1. formalise Lemma 16 and the termination consequence of strict initializer
   decrease, while keeping any remaining Lemma 11/12 provenance boundary
   explicit in theorem names;
2. replace the conditional Corollary 7-10, Lemma 11, and Lemma 12 interfaces by
   constructors from occurrence-indexed Definition 19 data;
3. formalise Lemmas 17-18 and complete the combinatorial route to Theorem 1(iii);
4. introduce the Pauli/frustration-graph algebra required for Theorem 1;
5. formalise the exact free-fermion solution of Theorem 2 and the Krylov
   construction of Theorem 3.
""",
    """1. connect strict initializer decrease to the terminal unobstructed state of
   the corrective process;
2. replace the remaining generic conditional Corollary 7-10, Lemma 11, and
   Lemma 12 interfaces by occurrence-indexed constructors;
3. formalise Lemmas 17-18 and complete the combinatorial route to Theorem 1(iii);
4. introduce the Pauli/frustration-graph algebra required for Theorem 1;
5. formalise the exact free-fermion solution of Theorem 2 and the Krylov
   construction of Theorem 3.
""",
    "README critical path",
)
readme.write_text(text)


# Current fidelity document
fidelity = Path("docs/PAPER_FIDELITY.md")
text = fidelity.read_text()
lemma16_section = """
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

"""
text = replace_once(
    text,
    "## Current manuscript coverage\n",
    lemma16_section + "## Current manuscript coverage\n",
    "PAPER_FIDELITY Lemma 16 insertion point",
)
text = replace_once(
    text,
    """| Lemmas 12-13 | Supporting implementations exist; final statement audit remains |
| Lemma 14 | Exact unqualified theorem proved from the literal initialized finite search history |
| Lemma 15 | Exact all-steps theorem proved for explicit finite corrective rerouting executions |
| Lemmas 16-18 | Not complete manuscript-level results |
""",
    """| Lemmas 12-13 | General supporting interfaces remain, with the Lemma 12 data constructor completed for Lemma 16 traces |
| Lemma 14 | Exact unqualified theorem proved from the literal initialized finite search history |
| Lemma 15 | Exact all-steps theorem proved for explicit finite corrective rerouting executions |
| Lemma 16 | Exact unqualified theorem on an explicit completed finite Definition 19 trace |
| Lemmas 17-18 | Not complete manuscript-level results |
""",
    "PAPER_FIDELITY coverage rows",
)
fidelity.write_text(text)


# Dated audit
report = Path("docs/PAPER_FIDELITY_AUDIT_2026-08-05.md")
text = report.read_text()
text = replace_once(
    text,
    """This audit compares the root-imported Lean development at commit
`fcc564bda8ddcb7982830b7b13908ed552641a99` with the manuscript
""",
    """This audit compares the Lean development through the paper-facing Lemma 16
commit `2c67d9580c61c8cf91b6a9327238f278751b955c` with the manuscript
""",
    "audit baseline commit",
)
text = replace_once(
    text,
    """Repository-wide code search found no occurrence of `sorry`, `admit`, project
`axiom`, or `opaque`. Lean CI run 1404 passed the complete root project at the
exact head of PR #266 before merge.
""",
    """The reviewed Lemma 16 modules contain no `sorry`, `admit`, project `axiom`,
or `opaque`. The exact paper-facing source at commit
`2c67d9580c61c8cf91b6a9327238f278751b955c` passed a complete local
`lake build` of 1457 jobs.
""",
    "audit static integrity",
)
text = replace_once(
    text,
    """| Lemma 12 | `FullDefinition19Deformation.lemma12` | Conditional on `Lemma12Definition19Data`. Its endpoint/continuation fields are intended Definition 19 facts but are not yet constructed from the current flattened deformation object. |
""",
    """| Lemma 12 | `FullDefinition19Deformation.lemma12` | The general theorem remains conditional on `Lemma12Definition19Data`. For Lemma 16, `PaperLemma16Trace.toLemma12Definition19Data` now constructs those fields from the literal completed trace. |
""",
    "audit Lemma 12 row",
)
text = replace_once(
    text,
    """| Lemmas 16-18 | none | Not yet formalised at manuscript level. |
""",
    """| Lemma 16 | `FiniteMixedSideSearchTrace.PaperLemma16Trace.paperLemma16` | Exact on an explicit completed finite Definition 19 trace. The occurrence transport and Lemma 12 data are derived rather than accepted as theorem premises. |
| Lemmas 17-18 | none | Not yet formalised at manuscript level. |
""",
    "audit Lemma 16 row",
)
text = replace_once(
    text,
    """4. Construct `Lemma12Definition19Data` from the ordered path-block object and
   then reserve the unqualified paper name for that wrapper.
5. Derive the Eq. (C32) path-containment facts from the concrete concatenation
   index equivalence rather than storing them in `IsConcatenation`.
6. Continue with Lemma 16 only with theorem names that state any remaining
   execution or provenance boundary.
""",
    """4. Generalise the Lemma 16 construction of `Lemma12Definition19Data` to the
   remaining standalone Lemma 12 interfaces.
5. Derive the Eq. (C32) path-containment facts from the concrete concatenation
   index equivalence rather than storing them in `IsConcatenation`.
6. Connect strict initializer decrease to the terminal unobstructed state used
   by the subsequent corrective-process argument.
""",
    "audit remediation list",
)
text = replace_once(
    text,
    """Until the remediation items above are complete, the repository may claim that
its Lean terms are internally checked and that Lemmas 14-15 have exact explicit
history-level endpoints. It must not claim that every numbered result currently
represented is already an exact formalisation of the printed manuscript.
""",
    """Until the remediation items above are complete, the repository may claim that
its Lean terms are internally checked and that Lemmas 14-16 have exact explicit
history-level endpoints. It must not claim that every numbered result currently
represented is already an exact formalisation of the printed manuscript.
""",
    "audit operational rule",
)
report.write_text(text)


# PaperFidelity module documentation, without creating an import cycle.
paper_gate = Path("FreeFermionGraphs/PaperFidelity.lean")
text = paper_gate.read_text()
text = replace_once(
    text,
    """The lower-level Lemma 14 bridge in this file is also explicitly conditional.
The completed exact history-level theorem is defined downstream as
`InitializationFiniteMixedSideLemma14History.paperLemma14`; importing that
module here would create an import cycle because the later terminal analysis
uses `PaperLemma14Conclusion` from this file.

The repository-wide status, including corrected-versus-literal manuscript
""",
    """The lower-level Lemma 14 bridge in this file is also explicitly conditional.
The completed exact history-level theorem is defined downstream as
`InitializationFiniteMixedSideLemma14History.paperLemma14`; importing that
module here would create an import cycle because the later terminal analysis
uses `PaperLemma14Conclusion` from this file.

The exact Lemma 16 endpoint is likewise defined downstream as
`FiniteMixedSideSearchTrace.PaperLemma16Trace.paperLemma16`. It derives both
the occurrence transport and `Lemma12Definition19Data` from literal completed
trace data. It is root-imported through `Lemma16Paper` rather than imported
here, avoiding a cycle through the Lemma 14 fidelity proposition.

The repository-wide status, including corrected-versus-literal manuscript
""",
    "PaperFidelity downstream Lemma 16 note",
)
paper_gate.write_text(text)

print("Integrated Lemma 16 into root imports and fidelity documentation")
