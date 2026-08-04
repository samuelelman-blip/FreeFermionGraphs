# Executable Lemma 14 completion

This document supersedes the earlier Lemma 14 status section of
`docs/PAPER_FIDELITY.md`.

## Paper-facing theorem

The executable finite route exports:

```lean
InitializationFiniteMixedSideExecutableLemma14Data.paperLemma14
```

with conclusion `PaperLemma14Conclusion I`, exactly the four statements of
manuscript Lemma 14.

## Removed boundary certificates

The paper-facing input does not store any of the following conclusions:

- evenness of the obstruction target index;
- odd cardinality of the terminal path;
- positive final-hole external degree three;
- adjacency of the staged clone centre to the two-step terminal flank;
- an arbitrary completed unequal-centre propagation trace;
- the endpoint alternative or any other clause of Lemma 14(iv).

## Generated provenance

### Terminal path

`FiniteMixedSideTerminalPathExecution` records the manuscript coordinate form

```text
j₀-k₀-⋯-k_(ℓ-1)-j_ℓ
```

by a half-length and a target position. The repository derives the target's
even coordinate, the last endpoint's even coordinate, membership in the common
endpoint side, and odd path cardinality.

### Positive terminal degree

`ConcretePathDeformation.TargetBalanced` states the literal per-replacement
invariant that the eventual target is adjacent to the introduced vertex exactly
when it is adjacent to the removed vertex. The invariant is proved for the
one-block constructor and preserved by `FiniteMixedSideSearchTrace.snoc`.
Exact external degree is then transported through every represented block to
the manuscript final hole. The degree on the original hole is three because
the Definition 20 stopping branch supplies the target clone there.

### Tether flank

`FiniteMixedSideIncomingGeneratedTerminalStop` records the adjacent link
coordinate between the target and the source-side same-colour flank. Indexed
path adjacency derives the required clone-centre-to-flank edge.

### Unequal-centre propagation

`FiniteMixedSideDistinctPropagationTrace.start` creates the zero-hop trace and
`FiniteMixedSideDistinctPropagationTrace.snoc` appends one actual execution
path. `FiniteMixedSideDistinctPropagationTrace.IsGenerated` certifies that the
bounded trace was produced only by these constructors. Each hop preserves the
three coordinate-level avoidance invariants used by the final claw
contradiction.

## Validation requirements

The completion is accepted only when:

1. the focused executable Lemma 14 module builds;
2. the root `FreeFermionGraphs` import builds;
3. the exact pull-request head passes Lean CI;
4. no `sorry`, `admit`, project `axiom`, or project `opaque` is introduced.

## Remaining manuscript work

This completion is specific to initialization, Lemma 14. The next search-process
results are Lemmas 15 and 16, followed by the remaining route to Theorem 1(iii).
The Pauli/Hamiltonian operator layer for Theorem 1, the free-fermion
reconstruction of Theorem 2, and the Krylov theorem remain outside the current
repository scope.
