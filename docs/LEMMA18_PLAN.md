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

## Implementation status

Completed on this branch:

1. Single-vertex deformations and finite reversible deformation closure for indexed induced paths, preserving endpoints and length.
2. The literal Eq. (E1) weighted adjacency matrix on `directedHoppingGraphAtClique`.
3. Tree-arc weights for one-vertex extensions and contractions.
4. An algebraic interface for generalized-cycle/bubble-wand arc weights and their normalization.
5. The prefix families `P_m` and `P̃_m` of Eqs. (E3)-(E4).
6. Equality of the corresponding local prefix-transition weights under the stated deformation-compatibility condition.
7. Finite path indexing and the equality between weighted-walk sums and matrix powers.
8. Generic class-constant, quotient-lift, equal-column, and commuting-intertwiner criteria which each imply matrix-power amplitude equality when their hypotheses hold.

Still required for a paper-facing theorem:

1. Construct a global spectral equivalence or commuting intertwiner for the concrete Eq. (E1) transition, or derive the required transition directly from the operator commutator quotient.
2. Lift that construction along finite deformation sequences to every `P̃ ∈ ⟨P⟩`.
3. Export `paperLemma18` with no walk-bijection, spectral-equivalence, or amplitude-invariance certificate among its premises.

## Audit of the printed last-crossing proof

The last-crossing substitution in the manuscript is not defined on every
contributing walk.  After the final traversal of `P_(i-1) -> P_i`, a walk may
enter a non-prefix branch and return without crossing that edge again.  A
replacement of the changed vertex need not be an induced path on that branch.
Accordingly, local equality of the displayed prefix weights does not yet
produce the claimed global walk bijection.

One possible replacement route is global rather than walk-by-walk.  A
sufficient condition is that one Krylov transition preserve every row
function which is constant on chosen classes.  The generic theorem
`matrixPow_apply_eq_of_preservesClassConstant` then proves that every
matrix-power row starting at a singleton source is constant on target
classes, including power zero.  A literal quotient lift satisfies this
criterion, but is only a strong special case.

An alternative sufficient condition is a commuting matrix `S`.  The theorem
`matrixPow_apply_eq_of_intertwiner` proves the desired equality whenever `S`
commutes with the transition, fixes the source row, and maps the chosen target
column to the comparison target.  Unlike a path permutation, such an
intertwiner may mix path states and can therefore express a genuinely spectral
equivalence.

The concrete Eq. (E1) transition does **not** preserve the partition by the
literal internal path-deformation closure in general.  The prefix ending at
the changed vertex is not internally deformable, and incoming branch weights
need not agree class-by-class.  Thus the generic theorem is a diagnostic
linear-algebra layer, not yet a proof of Lemma 18.  A successful replacement
must instead construct the richer spectral equivalence of the weighted
induced-path tree, or derive an equivalent class transition directly from the
operator commutator.

Eq. (E1) also requires a canonical normalization construction.  Its printed
sum rule alone does not imply pointwise equality of corresponding bubble-arc
weights.

## Fidelity constraints

The final theorem must quantify over every nonnegative matrix power and every induced path in the deformation closure, exactly as in the manuscript. Eq. (E1) weights must either be represented literally or related to the formal weights by a proved equality. Intermediate walk correspondences are derived proof objects, not public hypotheses.
