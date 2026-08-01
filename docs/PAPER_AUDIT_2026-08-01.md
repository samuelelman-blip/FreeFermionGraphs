# Paper fidelity audit, 2026-08-01

## Scope

This audit compares the manuscript *A Unified Graph-Theoretic Framework for
Free-Fermion Solvability*, supplied as a 52-page PDF dated 2026-07-14, with
[`samuelelman-blip/FreeFermionGraphs`](https://github.com/samuelelman-blip/FreeFermionGraphs).
The repository baseline was pull request
[#196](https://github.com/samuelelman-blip/FreeFermionGraphs/pull/196), head
commit `ca571922a395d5e56c25ce19288a2b88448b79ca`.

The review checked the exact statements of Theorems 1-3, Definitions 14-20,
Lemma 11, and Lemma 14 against the corresponding Lean declarations and public
status claims. It also inspected every root-imported module, searched the Lean
tree for proof placeholders, and traced the provenance fields used by the
paper-facing integration theorems.

## Conclusion

The repository contains a large and useful graph-combinatorial development,
especially around claw-free paths, hole deformations, and the local geometry
used in Lemma 11. It is not yet a formalisation of the paper's main theorems.

The largest discrepancy was public status, not an unsound Lean proof. The
operator algebra required to state the commutators in Theorem 1, the
free-fermion reconstruction in Theorem 2, and the nested-commutator identity in
Theorem 3 is absent. Several numbered graph results are also available only
from supplied history or endpoint certificates that have not been constructed
from the manuscript definitions. The previous README claims that Theorem 1(i)
and Theorem 1(ii) were formalised, and that substantial Theorem 2-3
formalisation existed, were therefore not supported by the declarations.

Pull request #196 is a sound architectural direction: it exposes the exact
mixed-side Lemma 11(a.ii) conclusion for a supplied search witness. It does not
construct that witness from the obstruction search, and its positive history
still inherits an infinite `Nat` interface for the paper's finite sequence.

## Findings

### 1. Theorems 1-3 are not formalised

The manuscript's Theorem 1 is an operator theorem:

1. independent-set charges commute mutually;
2. generalized-cycle charges commute with independent-set charges;
3. generalized-cycle charges commute mutually.

`TokenSlidingCharges.lean` represents an operator term `h_S` by an arbitrary
value in an `AddCommMonoid`. Its principal theorem partitions a finite sum by
token-sliding component. `GeneralizedCycleSymmetry.lean` similarly defines a
generic additive closure sum. There is no multiplication, commutator,
anticommutator, Pauli representation, Hamiltonian, or frustration-graph
realisation in either module. Consequently these definitions cannot state any
clause of Theorem 1.

The repository also contains no transfer operator, generalized characteristic
polynomial, simplicial mode, incognito mode, canonical anticommutation
relation, Hamiltonian reconstruction, or free-fermion spectrum. Theorem 2 is
absent.

`InducedPathTree.lean`, `DirectedHoppingGraph.lean`, and
`BubbleWandHoppingArc.lean` define part of the unweighted graph underlying the
manuscript's Krylov construction. They do not define the weighted matrix
`A_(G,J)`, path operators, nested commutators, or the matrix-power equality in
Theorem 3. Lemma 18, Theorem 3, and Corollary 1 are absent as paper statements.

### 2. The former `paperLemma11b` had an unrecorded boundary premise

The former theorem `PaperFidelity.paperLemma11b` took
`D.Lemma11AHistoryContext` as an argument. That context supplies
`FullDefinition19Lemma11AData`, which includes
`FullDefinition19NeighborhoodData`. The latter stores
`BaseOppositeEndpointNonadjacency` as a field. The local data also stores
`terminalAnticommutingNonadjacency`.

Those facts may be derivable from Definition 19 and the preceding manuscript
lemmas, but the repository does not currently provide that constructor. In the
present theorem they are premises, not derived facts. This violates the
repository's own rule that an unconditional paper theorem may use only
manuscript data and previously audited consequences.

The bridge is now named `paperLemma11b_of_historyContext`. There is
deliberately no unconditional theorem named `paperLemma11b`.

### 3. The positive history interface is stronger than Definition 19

Definition 19 supplies a finite sequence `(P^(r))_(r=0)^m`.
`PathBlockHistory` instead requires:

```lean
block : Nat → ConcretePathDeformation O Cprime
pathOrder : ∀ r : Nat, ...
pathCard : ∀ r : Nat, ...
chain : ∀ r : Nat, ... (block (r + 1)) ...
```

Later structures add `priorCount`, and the proofs use only indices below that
bound. The structure nevertheless demands valid blocks and carrier links for
all natural numbers. A terminating finite execution does not naturally
produce such an infinite tail.

The new `FiniteMixedSideSearchTrace` removes that mismatch. It stores a
positive finite block count and quantifies all blocks by `Fin blockCount`.

### 4. `SearchDeformation.run` loses the path-block decomposition

`SearchDeformation.run` stores `Option FullDefinition19Deformation`. The latter
is a flattened sequence of single-vertex replacements. Its own module states
that flattening forgets the division into path blocks. It also does not retain
the `ac` or `bd` side selected for each block.

That information is exactly what the mixed Lemma 11 history and the terminal
part of Lemma 14 require. A witness cannot be reconstructed from `run` merely
by looking at its set of active paths, because the block order, side labels,
and relationship between local and flattened steps have already been erased.

`FiniteMixedSideSearchTrace.stepIndex` now records the missing mapping.
`step_eq`, `stepIndex_surjective`, and `stepIndex_order` tie every finite local
block step to the flattened run without assuming a conclusion of Lemma 11 or
Lemma 14. `output_path_iff` derives exact equality between the trace's block
paths and `SearchDeformation.paths`.

This is an integration interface, not yet a constructor. The repository still
lacks an executable or inductively generated `OS` object from which to build
the trace.

### 5. Lemma 14 is correctly marked incomplete

The exact four conclusions of Lemma 14 are represented by
`PaperLemma14Conclusion`. There is no theorem named `paperLemma14`. The
strongest public bridge requires terminal predecessor-degree analysis data not
present in the manuscript statement.

This part of the repository's fidelity policy is working as intended. The
remaining mathematical gap is substantive: terminal containment must allow
the original/prime colour overlaps permitted by Corollary 9 and the mixed
`ac`/`bd` blocks permitted by Definition 19.

### 6. The repository is free of explicit proof placeholders

A static scan of the Lean source found no uses of `sorry`, `admit`, project
`axiom`, or `opaque`. The incompleteness is expressed through data structures,
extra premises, conditional theorem names, and missing integration theorems,
not through admitted proofs.

This is good proof hygiene, but it does not make an extra structure field a
manuscript theorem. Provenance still has to be audited.

## Statement matrix

| Manuscript result | Current Lean coverage | Fidelity status |
|---|---|---|
| Lemmas 6-10 | Numerous graph-level implementations | Present, but this audit did not certify every statement end to end |
| Definition 14 | Token-sliding components and generic additive sums | Combinatorial analogue only, not the operator charge |
| Definition 15 | Deformation closures and generic additive sums | Combinatorial analogue only, not the operator symmetry |
| Definitions 16 and 18 | Rooted induced-path tree and a directed arc graph | Partial unweighted graph layer |
| Lemma 11(a) | Exact conclusions proved from supplied first/later contexts, including mixed-side contexts | Conditional until finite literal history and endpoint fields are constructed |
| Lemma 11(b) | Final-hole degree and descent proved from supplied context | Conditional; renamed paper bridge records the premise |
| Corollary 11 | Concrete mixed-side theorem exists | Conditional on supplied mixed history |
| Lemmas 12-13 | Theorems on `FullDefinition19Deformation` | Conditional on its explicit flattening/local fields; constructor audit remains |
| Lemma 14 | Exact conclusion type plus conditional bridges | Incomplete, accurately gated |
| Lemmas 15-17 | No manuscript-level declarations found | Absent |
| Lemma 18 | Some graph definitions used by its setup | Lemma absent |
| Theorem 1(i)-(iii) | No operator commutator declarations | Absent |
| Theorem 2 | No transfer/operator/free-fermion layer | Absent |
| Theorem 3 and Corollary 1 | No weighted matrix-power or nested-commutator theorem | Absent |

## What is already valuable

- The development has extensive concrete path and hole geometry rather than
  only high-level axioms.
- Hole stages and external-degree expressions are usually explicit.
- The code recognises the legitimate overlaps between original-hole and
  prime-hole colour classes.
- The side-swapping construction correctly models `bd` blocks as `ac` blocks
  in a relabelled fixed-pairing family.
- The exact Lemma 14 target is separated from conditional terminal
  certificates.
- Pull requests #188-#196 progressively reduced real interface gaps rather
  than inserting admitted proofs.

## Recommended completion order

1. Define the obstruction search as executable well-founded recursion or as an
   inductively generated finite trace with a proved termination measure.
2. Construct `FiniteMixedSideSearchTrace` from that search, including side
   labels, original removed-vertex labels, block order, and flattened-step
   correspondence.
3. Derive `BaseOppositeEndpointNonadjacency` and
   `terminalAnticommutingNonadjacency` from Definition 19 and the audited graph
   lemmas instead of accepting them as fields.
4. Port the bounded parity, persistence, Corollary 11, and Lemma 11(a.ii)
   arguments to the finite trace. Retire the total `Nat` history from
   paper-facing paths.
5. Use the finite mixed trace to prove terminal containment and the remaining
   two-incoming propagation argument, then expose unconditional
   `paperLemma14`.
6. Formalise Lemmas 15-16 and complete the palindromic search update.
7. Introduce the Pauli/operator algebra and prove Theorem 1. Only after that
   should the transfer-operator and Krylov layers for Theorems 2-3 be claimed.

## Validation status

The current pull request reports no completed local validation. A full Lean
build could not be run in the audit environment because the Lean 4.32.0
launcher needs to resolve `/proc/self/exe`, which the sandbox denies. This is
an environment limitation, not a Lean diagnostic. The new code therefore
requires the repository's normal local checks before merge:

```bash
lake build FreeFermionGraphs.ObstructionSearchFiniteMixedTrace
lake build FreeFermionGraphs.PaperFidelity
lake build
```

Hosted CI was not triggered, consistent with the repository policy of
conserving GitHub Actions usage.
