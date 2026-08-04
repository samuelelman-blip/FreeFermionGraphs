# FreeFermionGraphs

Lean 4 formalisation effort for the graph-theoretic results in
*A Unified Graph-Theoretic Framework for Free-Fermion Solvability* by Adrian
Chapman, Samuel J. Elman, and Ryan L. Mann.

The checked-in development currently concentrates on finite claw-free graph
theory, hole deformations, token sliding, and the Definition 19 obstruction
search. It does not yet contain the Pauli/Hamiltonian operator algebra needed
to state or prove the manuscript's charge commutators, transfer-operator
identities, free-fermion reconstruction, or operator-Krylov formula.

## Toolchain

The repository currently uses:

- Lean 4.32.0
- mathlib through Lake

Install Lean with `elan`, then build the complete project with:

```bash
lake update
lake build
```

The executable Lemma 14 endpoint can be checked first with:

```bash
lake build FreeFermionGraphs.ObstructionSearchFiniteMixedExecutablePaperLemma14
```

## Current proof status

The main active proof program is the graph-combinatorial route toward Theorem
1(iii). The complete finite terminal-analysis route for manuscript Lemma 14 is
imported by `FreeFermionGraphs.lean` and exposes
`InitializationFiniteMixedSideExecutableLemma14Data.paperLemma14`.

The theorem proves the exact four-part `PaperLemma14Conclusion` from the
initialized finite obstruction-search execution and claw-freeness. Its terminal
facts are generated as follows:

- the terminal component is represented in the manuscript coordinate form
  `j₀-k₀-⋯-k_(ℓ-1)-j_ℓ`, from which target parity, endpoint-side membership,
  and odd path cardinality are derived;
- target adjacency balance is proved for the one-block constructor and
  preserved by literal `snoc`, which transports the original stopping-clone
  degree three to the exact positive manuscript final hole;
- clone-to-flank adjacency is derived from the adjacent tether-link coordinate;
- the unequal-centre propagation is accepted only with an `IsGenerated`
  derivation from the finite zero-hop and `snoc` propagation constructors.

The paper-facing theorem therefore contains no terminal parity, degree-three,
flank-adjacency, endpoint conclusion, or arbitrary bounded-propagation
certificate. No clause of Theorem 1 is yet exported as a manuscript-level
Pauli-operator commutator theorem.

| Manuscript layer | Status |
|---|---|
| Finite claw-free graph theory, including Lemmas 6-10 | Lean implementations exist; complete paper-facing audit remains |
| Token sliding, deformation closures, and generalized-cycle sums | Combinatorial and generic additive definitions exist; operator charges are absent |
| Theorem 1(i)-(iii) | Not formalised at manuscript operator level |
| Lemma 11(a)-(b) | Substantial finite and mixed-side implementations exist; final statement audit remains |
| Corollary 11 | Proved on bounded mixed-side finite histories |
| Lemmas 12-13 | Implemented on supporting deformation interfaces; statement audit remains |
| Lemma 14(i)-(iv) | Exact conclusion proved from generated finite obstruction-search events by `InitializationFiniteMixedSideExecutableLemma14Data.paperLemma14` |
| Lemmas 15-18 | Not formalised as complete manuscript lemmas; some underlying graph definitions exist |
| Theorem 2 | Not formalised |
| Theorem 3 and Corollary 1 | Not formalised |

The next critical path is:

1. formalise Lemma 15, preserving the four Lemma 14 invariants after each
   elimination step of the search process;
2. formalise Lemma 16 and the unobstructed-palindromic termination argument;
3. complete the remaining combinatorial route to Theorem 1(iii);
4. introduce the Pauli/frustration-graph algebra required for Theorem 1;
5. formalise the exact free-fermion solution of Theorem 2 and the Krylov
   construction of Theorem 3.

## Manuscript fidelity policy

A successful `lake build` proves that the Lean terms typecheck. It does not by
itself establish that a theorem has the same hypotheses, quantifiers,
deformation stage, and conclusion as the manuscript.

Paper-facing results are therefore gated by
[`docs/PAPER_FIDELITY.md`](docs/PAPER_FIDELITY.md). In particular:

- every manuscript object must be matched to a Lean object;
- hole stages and degree expressions must be explicit;
- additional premises must be documented;
- boundary certificates may not appear in the final paper theorem;
- an unqualified paper theorem must expose the exact manuscript conclusion;
- any remaining constructor or provenance boundary must be recorded explicitly.

This policy is especially important for Definition 19, where one
fixed-pairing deformation may contain paths from both component families. A
one-sided history cannot be used as the final representation of the manuscript
search.

## Repository layout

- `FreeFermionGraphs/`: individual definitions, lemmas, and integration modules
- `FreeFermionGraphs.lean`: root import for the complete development
- `FORMALIZATION.md`: dependency-oriented proof plan
- `docs/PAPER_FIDELITY.md`: manuscript correspondence, provenance, and open
  proof boundaries
- `docs/PAPER_AUDIT_2026-08-01.md`: statement-level audit against the supplied
  manuscript

## Development workflow

Every pull request touching a numbered manuscript result should be validated
with both a focused module build and the full project build:

```bash
lake build FreeFermionGraphs.<ModuleName>
lake build
```

A pull request should not be merged until the exact head has passed the
corresponding validation gate.
