# Lemma 18 formalisation plan

## Manuscript statement

Appendix E.1 states: if

`P = j* - j₁ - … - j_ℓ`

is an induced path with `ℓ ≥ 2`, then

`(A^k)_{ {j*}, P } = (A^k)_{ {j*}, P̃ }`

for every `P̃ ∈ ⟨P⟩` and every `k ≥ 0`, where `A` is the weighted adjacency matrix of the directed hopping graph `Λ(G*)`.

## Existing repository interfaces

The current repository already contains substantial structural ingredients:

- `InducedPathTree.lean`: rooted induced paths and the one-vertex-extension tree;
- `CliqueInducedPathTree.lean`: the augmented graph `G*` with the fresh root `j*` and the induced-path tree rooted at that vertex;
- `DirectedHoppingGraph.lean`: the directed graph obtained by bidirecting tree edges and adding extra arcs;
- `BubbleWandHoppingArc.lean`: the concrete even-hoop bubble-wand arcs of Definition 18.

The existing deformation-closure relation is presently specialized to even holes. Lemma 18 instead needs the deformation closure of induced paths from Definition 12, with fixed endpoints and path length.

## Required new layers

1. Define single-vertex deformations and finite deformation closure for indexed induced paths, preserving their endpoints and length.
2. Define the Eq. (E1) weighted adjacency matrix on `directedHoppingGraphAtClique`.
3. Prove the tree-arc weights for one-vertex extensions and contractions.
4. Represent the generalized-cycle/bubble-wand arc weight and its normalization at the algebraic interface needed by Lemma 18.
5. For a single-vertex deformation `P → P̃`, define the prefix families `P_m` and `P̃_m` of Eqs. (E3)-(E4).
6. Prove the corresponding arcs among the affected prefixes have equal weights.
7. Extend the local correspondence to a weight-preserving bijection of arbitrary finite directed walks from the root singleton.
8. Convert weighted-walk equality to matrix-power equality.
9. Lift along finite deformation sequences to every `P̃ ∈ ⟨P⟩`.
10. Export `paperLemma18` with no walk-bijection or amplitude-invariance certificate among its premises.

## Audit of the printed last-crossing proof

The last-crossing substitution in the manuscript is not defined on every
contributing walk.  After the final traversal of `P_(i-1) -> P_i`, a walk may
enter a non-prefix branch and return without crossing that edge again.  A
replacement of the changed vertex need not be an induced path on that branch.
Accordingly, local equality of the displayed prefix weights does not yet
produce the claimed global walk bijection.

The replacement route is to construct the Krylov transition on deformation
classes and lift it to path indices.  The generic linear-algebra theorem
`quotientLiftMatrix_pow_apply_eq` proves that all matrix-power amplitudes of
such a lift are constant on target classes, including power zero when the
source class is a singleton.  It remains to prove at the operator boundary
that the commutator transition factors through the deformation quotient.

Eq. (E1) also requires a canonical normalization construction.  Its printed
sum rule alone does not imply pointwise equality of corresponding bubble-arc
weights.

## Fidelity constraints

The final theorem must quantify over every nonnegative matrix power and every induced path in the deformation closure, exactly as in the manuscript. Eq. (E1) weights must either be represented literally or related to the formal weights by a proved equality. Intermediate walk correspondences are derived proof objects, not public hypotheses.
