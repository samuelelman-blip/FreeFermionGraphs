import FreeFermionGraphs.KrylovRowClosedFormHoles

/-!
# v1 Lemma 16 (repo Lemma 18): balanced Krylov rows on deformation closures

Manuscript reference: arXiv 2305.15625v1, Lemma `deformationclosurepathsrelation`
(statement L1457-1465, proof L1466-1485), together with Eq. (decoratedtree)
(L1434-1445) and the normalisation sentence on L1445.  In the numbering of the revised
manuscript used by the repo this is Lemma 18; in v1 it is Lemma 16 (v1 numbers lemmas,
theorems and corollaries with separate counters, see `docs/V1_NUMBERING.md`).

The Lemma says: for an induced path `P = j* - j₁ - ⋯ - j_ℓ` with `ℓ ≥ 2` and every `P~` in
the deformation closure `⟨P⟩`,

`(A^k)_{{j*},P} = (A^k)_{{j*},P~}`    for all `k ≥ 0`,

where `A` is the weighted adjacency matrix of the directed hopping graph `Λ(G*)` of
Eq. (decoratedtree).

## Two results

1. **The Lemma holds for the corrected matrix** (`paperLemma18`).  For a finite claw-free
   graph `G`, a simplicial clique `K`, couplings `b` and an arbitrary assignment `lam` of the
   generalized-cycle eigenvalues, the statement holds for the corrected matrix
   `A_λ = cliqueHoppingMatrix G K b lam` of `CliqueHoppingMatrix.lean` (root-handle arcs, the
   sign `(-1)^{k-1}` of a hoop with `2k` vertices, the normalisation `1/|c|` per bubble
   event).  The hypotheses are exactly the setup of the manuscript.  The proof is not v1's
   last-crossing substitution (that argument is not defined on every walk,
   `docs/V1_ERRATA.md`); it is the balance statement `sectorRow_pow_eq_of_closure` of
   `KrylovRowClosedFormHoles.lean`, a consequence of the closed form of the Krylov rows with
   hole terms (`krylovRow_mul_sectorIndepSeries`): a deformation preserves `|P|` and the
   closed neighbourhood `N(P)`, and the row series times the unit `Z_V` is
   `X^{|P|-1} Z_{V ∖ N(P)}`.

2. **The Lemma is false for the printed matrix** (`PrintedNormalisation.Example`).  Read
   literally, the third case of Eq. (decoratedtree) is `A_{PP'} = λ_{⟨C₀⟩} / N_{P,P',⟨C₀⟩}`
   with `(1/2) Σ_{P'} N_{P,P',⟨C₀⟩}^{-1} = 1` (a fixed source `P`, a sum over its targets `P'`
   in the class `⟨C₀⟩`, no sign).  This is `printedHoppingMatrix` with a normalisation
   satisfying `IsPrintedNormalisation`.  Counterexample: `G` on `{0, …, 6}` with the edges
   `01 02 03 05 06 12 14 25 34 35 36 46 56`, `K = {2, 5}` (a simplicial clique; `G` is
   claw-free), `P = (j*, 2, 0)` (`ℓ = 2`), `P~ = (j*, 5, 0)` (the single-vertex deformation of
   `P` by `5 ≺_P 2`).  The even holes `{0134, 0146}` form one deformation class, there are
   eight bubble events, and each source has a single target, so the printed rule forces
   `N = 1/2`: the hoop weight is `2 λ` on every arc.  Then

   * `b² = (4, 4, 1, 3, 5, 4, 4)`, `λ = 3`: `(A^6)_{{j*},P} = 428 ≠ 422 = (A^6)_{{j*},P~}`
     (`printed_pow_six_package`, over any field of characteristic zero containing such `b`);
   * `b = 1`, `λ = 1`: `(A^6)_{{j*},P} = 42 ≠ 40 = (A^6)_{{j*},P~}`, and the two rows agree for
     `k < 6` (`printed_pow_unit`, `printed_normalisation_counterexample`, over `ℚ`).

   The corrected matrix gives `398` for both entries in the first case (an exact computation
   outside Lean; `paperLemma18` proves the equality, `Example.corrected_balanced_of_paperLemma18`).
   The cause: the source `(j*, 5, 0, 1, 4)` reaches the handle `(j*, 5)` through two bubbles
   (`3` and `6`), a multiplicity which a per-arc normalisation ignores.  The root-handle arcs
   play no role (no hole meets `K`).  A search outside Lean (exact rational arithmetic, random
   weights) over all labelled graphs with at most `6` vertices and their simplicial cliques of
   size at most `3` found no counterexample for the printed normalisation, and a random search
   over `7`-vertex graphs found only instances with the same number (`21`) of rooted induced
   paths, so this example appears to be a smallest one (numerical evidence only).

## How the counterexample is checked

The counterexample is stated on the repo's own types.  The graph is a `SimpleGraph (Fin 7)`,
`K` a `Set (Fin 7)`; `IsClawFree`, `IsSimplicialClique`, the paths `P`, `P~`
(`CliqueRootedInducedPath`) and `InducedPathDeformationStep` are proved for these.  The printed
matrix is the matrix `printedHoppingMatrix` on `CliqueRootedInducedPath`, built from
`cliqueTreeMatrix`, `EvenHoopArc` and the deformation class `arcClass` of the hoop of an arc.

To evaluate `(A^6)` by kernel computation, the file contains a decidable list model of the
induced-path tree and of the even-hoop arcs (namespace `PrintedNormalisation`: `rootedPaths`,
`bubbleSplit`, `hoopArcs`, `treeWeight`, `hoopMatrix`), and proves that the model is the repo's
structure:

* `mem_rootedPaths_iff`, `Represents.isRootedInduced_pathList`, `Represents.exists_pathList`,
  `pathList_injective`: the lists `rootedPaths g` are exactly the lists `[j*, j₁, …, j_ℓ]` of the
  `CliqueRootedInducedPath`s, and `Example.pathEquiv` is the resulting bijection;
* `Represents.isArc_pathList_iff`: the model arcs are exactly `EvenHoopArc` (bubble wands with
  the root handle included, Definition 11 and 18);
* `cliqueTreeMatrix_eq_treeWeight`: the tree entries are `cliqueTreeMatrix`;
* `IsPrintedNormalisation.eq_half` and `Example.arc_unique`: each source has at most one
  target, so every printed normalisation is `N = 1/2` and the hoop weight is `2 λ`, without
  identifying the deformation classes of the carriers;
* `Example.printed_pow_apply`: the powers of the repo-level printed matrix are the powers of the
  rational matrix `hoopMatrix g7 bsq (2 c)`, read through `pathEquiv`; these are evaluated by
  kernel computation (`decide +kernel`).

Not machine-checked: the reading of the printed sentence as `IsPrintedNormalisation` (it is the
literal one: fixed source, sum over the targets in the class of the arc); that the even holes
`{0134, 0146}` form a single deformation class (not used: the forcing of `N = 1/2` needs only
that each source has one target); the value `398` of the corrected matrix; minimality of the
example.

The older plan `docs/LEMMA18_PLAN.md` targeted the Eq. (E1) matrix with canonical per-arc
weights; that matrix is the printed one and the plan's global target is false.  This file
supersedes it.

## Main declarations

* `paperLemma18`: the Lemma for `cliqueHoppingMatrix`, hypotheses as in v1.
* `paperLemma18_of_deformationStep`: the single-vertex-deformation form used in v1's proof.
* `arcClass`, `printedHoppingMatrix`, `IsPrintedNormalisation`: the printed Eq. (decoratedtree)
  on `CliqueRootedInducedPath G K` for arbitrary `G`, `K`.
* `PrintedNormalisation.Example.printed_normalisation_counterexample`,
  `PrintedNormalisation.Example.printed_pow_six_package`,
  `PrintedNormalisation.Example.printed_pow_unit`: the machine-checked counterexample.
-/

open scoped BigOperators

universe u w

variable {V : Type u}

namespace SimpleGraph

/-! ### The Lemma for the corrected matrix -/

section PaperLemma

variable {G : SimpleGraph V} {K : Set V}
variable [Fintype V] [DecidableEq V] {R : Type w} [Field R]
  [DecidableEq (CliqueRootedInducedPath G K)]

/-- **v1 Lemma 16 (repo Lemma 18), label `deformationclosurepathsrelation` (L1457-1465), for
the corrected matrix of Eq. (decoratedtree).**

Let `G` be a finite claw-free graph, `K` a simplicial clique, `b` the couplings, `lam` the
generalized-cycle eigenvalue of every deformation class of even holes, and
`A = cliqueHoppingMatrix G K b lam` the weighted adjacency matrix of the directed hopping
graph `Λ(G*)`.  If `P = j* - j₁ - ⋯ - j_ℓ` is a rooted induced path of `G*` with `ℓ ≥ 2` (that
is, `|P| = ℓ + 1 ≥ 3`) and `P'` lies in the deformation closure `⟨P⟩` (Definition 12,
`InInducedPathDeformationClosure`), then

`(A^k)_{{j*},P} = (A^k)_{{j*},P'}`    for every `k ≥ 0`.

*Matrix.*  The statement is for the corrected `A_λ` (root-handle arcs, sign `(-1)^{k-1}`,
normalisation `1/|c|` per bubble event; see `CliqueHoppingMatrix.lean`), not for the printed
Eq. (decoratedtree): with the printed normalisation the Lemma is false
(`PrintedNormalisation.Example.printed_normalisation_counterexample`).  For graphs without
even holes `A_λ` is the tree matrix (`cliqueHoppingMatrix_of_evenHoleFree`) and the statement is
`cliqueTreeMatrix_pow_root_eq_of_closure` (for the Eq. (E1) matrix of the repo,
`paperDeformationClosureLemma_of_evenHoleFree`).  The hypotheses are the manuscript setup
(finite claw-free graph, simplicial clique, couplings, `λ` arbitrary), so the name carries no
`_of_` qualifier; `[Field R]` replaces the reals, and `[DecidableEq (CliqueRootedInducedPath G K)]`
is only needed to form matrix powers.

*Proof.*  `sectorRow_pow_eq_of_closure`; v1's last-crossing substitution is not used (it is not
defined on every walk, `docs/V1_ERRATA.md`).  The hypothesis `hlen` is the literal `ℓ ≥ 2` and is
not used: a deformation needs an internal vertex, so for `|P| ≤ 2` the closure is `{P}` and the
statement is trivial. -/
theorem paperLemma18
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree) (b : V → R)
    (lam : EvenHoleDeformationClass G → R) {P P' : CliqueRootedInducedPath G K}
    (hlen : 3 ≤ P.path.card)
    (h : InInducedPathDeformationClosure (G.adjoinRootAt K) P.path P'.path) (k : ℕ) :
    (cliqueHoppingMatrix G K b lam ^ k) (cliqueRootPath G K) P =
      (cliqueHoppingMatrix G K b lam ^ k) (cliqueRootPath G K) P' := by
  have _ := hlen
  exact sectorRow_pow_eq_of_closure hK hclaw b lam h k

/-- The Lemma for a single-vertex deformation `P' = (P ∖ {j_i}) ∪ {k}` with `k ≺_P j_i`, the
case to which v1's proof reduces ("it is sufficient to prove the lemma for `P~` given by a
single-vertex deformation", L1467).  A corollary of `paperLemma18`
(`InducedPathDeformationStep.inClosure`). -/
theorem paperLemma18_of_deformationStep
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree) (b : V → R)
    (lam : EvenHoleDeformationClass G → R) {P P' : CliqueRootedInducedPath G K}
    (hlen : 3 ≤ P.path.card)
    (h : InducedPathDeformationStep (G.adjoinRootAt K) P.path P'.path) (k : ℕ) :
    (cliqueHoppingMatrix G K b lam ^ k) (cliqueRootPath G K) P =
      (cliqueHoppingMatrix G K b lam ^ k) (cliqueRootPath G K) P' :=
  paperLemma18 hK hclaw b lam hlen h.inClosure k

end PaperLemma

/-! ### The printed matrix on the rooted induced paths of `G*`

The third case of Eq. (decoratedtree), read literally.  The normalisation `N_{P,P',⟨C₀⟩}` is
data, constrained by the printed sentence `(1/2) Σ_{P'} N_{P,P',⟨C₀⟩}^{-1} = 1`. -/

section PrintedMatrix

open Classical

variable {G : SimpleGraph V} {K : Set V} [Fintype V] [DecidableEq V] {R : Type w} [Field R]

/-- The deformation class `⟨C₀⟩` of the hoop of an even-hoop arc `P → Q` (v1 L1445), read off
a bubble wand realising the arc.  For claw-free `G` it does not depend on the wand
(`CliqueBubbleWand.evenHoleDeformationClassOf_hoopCarrier_eq`). -/
noncomputable def arcClass {P Q : CliqueRootedInducedPath G K} (h : EvenHoopArc G K P Q) :
    EvenHoleDeformationClass G :=
  G.evenHoleDeformationClassOf (Classical.choose h).hoopCarrier

/-- The matrix `A` of Eq. (decoratedtree) (v1 L1434-1445) **as printed**, on the rooted induced
paths of `G*`: weight `1` for `P → P + x`, weight `b_x²` for `P + x → P`, weight
`λ_{⟨C₀⟩} / N_{P,P',⟨C₀⟩}` on every even-hoop arc `P → P'` (one weight per arc, no sign, the
root handle allowed as in `EvenHoopArc`), `0` otherwise.  `N` is the normalisation data, which
the printed sentence constrains by `IsPrintedNormalisation`; it is not the corrected matrix
`cliqueHoppingMatrix`, for which v1's Lemma `deformationclosurepathsrelation` holds
(`paperLemma18`). -/
noncomputable def printedHoppingMatrix (G : SimpleGraph V) (K : Set V) (b : V → R)
    (lam : EvenHoleDeformationClass G → R)
    (N : CliqueRootedInducedPath G K → CliqueRootedInducedPath G K → R) :
    Matrix (CliqueRootedInducedPath G K) (CliqueRootedInducedPath G K) R :=
  fun P Q => cliqueTreeMatrix G K b P Q +
    if h : EvenHoopArc G K P Q then lam (arcClass h) / N P Q else 0

/-- The printed normalisation rule (v1 L1445): for every source `P` and class `⟨C₀⟩`,
`(1/2) Σ_{P'} N_{P,P',⟨C₀⟩}^{-1} = 1`, the sum over the targets `P'` of `P` (even-hoop arcs
`P → P'`) whose hoop lies in `⟨C₀⟩`.  The sum runs over a fixed source, as printed.  (The
corrected matrix `cliqueHoppingMatrix` instead normalises per bubble event, which amounts to
summing over the sources of a fixed target.) -/
def IsPrintedNormalisation (G : SimpleGraph V) (K : Set V)
    (N : CliqueRootedInducedPath G K → CliqueRootedInducedPath G K → R) : Prop :=
  ∀ (P Q : CliqueRootedInducedPath G K) (h : EvenHoopArc G K P Q),
    (1 / 2 : R) * ∑ Q' ∈ Finset.univ.filter
      (fun Q' => ∃ h' : EvenHoopArc G K P Q', arcClass h' = arcClass h), (N P Q')⁻¹ = 1

omit [DecidableEq V] in
/-- If every source has at most one target, the printed rule forces `N_{P,P'} = 1/2` on every
arc (the sum has a single term).  No identification of the deformation classes is needed. -/
theorem IsPrintedNormalisation.eq_half [CharZero R]
    {N : CliqueRootedInducedPath G K → CliqueRootedInducedPath G K → R}
    (hN : IsPrintedNormalisation G K N)
    (huniq : ∀ P Q Q' : CliqueRootedInducedPath G K,
      EvenHoopArc G K P Q → EvenHoopArc G K P Q' → Q = Q')
    {P Q : CliqueRootedInducedPath G K} (h : EvenHoopArc G K P Q) : N P Q = 1 / 2 := by
  have h1 := hN P Q h
  have hfilter : Finset.univ.filter
      (fun Q' => ∃ h' : EvenHoopArc G K P Q', arcClass h' = arcClass h) = {Q} := by
    ext Q'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨h', -⟩
      exact huniq P Q' Q h' h
    · rintro rfl
      exact ⟨h, rfl⟩
  rw [hfilter, Finset.sum_singleton] at h1
  have h2 : (N P Q)⁻¹ = 2 := by
    have h3 : (2 : R) ≠ 0 := two_ne_zero
    field_simp at h1
    linear_combination h1
  rw [← inv_inv (N P Q), h2, one_div]

omit [DecidableEq V] in
/-- With unique targets the printed hoop weight is `λ / N = 2 λ`. -/
theorem IsPrintedNormalisation.matrix_apply [CharZero R]
    {N : CliqueRootedInducedPath G K → CliqueRootedInducedPath G K → R}
    (hN : IsPrintedNormalisation G K N)
    (huniq : ∀ P Q Q' : CliqueRootedInducedPath G K,
      EvenHoopArc G K P Q → EvenHoopArc G K P Q' → Q = Q')
    (b : V → R) (lam : EvenHoleDeformationClass G → R) (P Q : CliqueRootedInducedPath G K) :
    printedHoppingMatrix G K b lam N P Q =
      cliqueTreeMatrix G K b P Q + if h : EvenHoopArc G K P Q then 2 * lam (arcClass h) else 0 := by
  unfold printedHoppingMatrix
  congr 1
  split_ifs with h
  · rw [hN.eq_half huniq h]
    field_simp
  · rfl

end PrintedMatrix

/-! ### A decidable list model of the hopping graph -/

namespace PrintedNormalisation

/-- The data of a graph `G` on `Fin n` and a clique `K`, as Boolean functions. -/
structure GraphData (n : ℕ) where
  /-- Adjacency of `G` (symmetric, irreflexive). -/
  adj : Fin n → Fin n → Bool
  /-- Membership in the clique `K`. -/
  clique : Fin n → Bool

variable {n : ℕ}

/-- A rooted path of `G* = G + j*` as a list `[j*, j₁, …, j_ℓ]`; `none` is `j*`. -/
abbrev PathList (n : ℕ) := List (Option (Fin n))

/-- Adjacency in `G*` (`adjoinRootAt`): `j*` is adjacent exactly to `K`. -/
def adjS (g : GraphData n) : Option (Fin n) → Option (Fin n) → Bool
  | some u, some v => g.adj u v
  | none, some v => g.clique v
  | some u, none => g.clique u
  | none, none => false

/-- A list is a rooted induced path of `G*`: it starts at `j*`, has no repeated vertex,
and two entries are adjacent in `G*` exactly when they are consecutive. -/
def isRootedInduced (g : GraphData n) (p : PathList n) : Bool :=
  p.head? == some none && decide p.Nodup &&
    (List.range p.length).all fun i => (List.range p.length).all fun j =>
      !(decide (i < j)) || (adjS g (p.getD i none) (p.getD j none) == decide (j = i + 1))

/-- Depth-first enumeration of the rooted induced paths extending `p`
(`fuel` bounds the number of appended vertices). -/
def pathsAux (g : GraphData n) : ℕ → PathList n → List (PathList n)
  | 0, p => [p]
  | f + 1, p =>
    p :: ((List.finRange n).filter fun x => isRootedInduced g (p ++ [some x])).flatMap
      fun x => pathsAux g f (p ++ [some x])

/-- The rooted induced paths of `G*`, i.e. the vertices of the induced-path tree
`I(K, G)` (Definition 17), in depth-first order (`mem_rootedPaths_iff`). -/
def rootedPaths (g : GraphData n) : List (PathList n) := pathsAux g n [none]

/-- Bubble wand (Definition 11, L692-698): `bubbleSplit g p j = some s` when `j ∉ p` and
`Γ_P(j) = {j_s, j_{s+1}, j_ℓ}` with `0 ≤ s < ℓ - 2` (adjacency read in `G*`, so `s = 0`
is allowed). -/
def bubbleSplit (g : GraphData n) (p : PathList n) (j : Fin n) : Option ℕ :=
  if some j ∈ p then none else
  match (List.range p.length).filter (fun q => adjS g (some j) (p.getD q none)) with
  | [s, s', e] => if s' = s + 1 ∧ e + 1 = p.length ∧ s + 3 < p.length then some s else none
  | _ => none

/-- The arcs added to the induced-path tree by even holes (Definition 18): the pairs
`(j, handle)` of bubbles `j` whose wand on `p` has an even hoop. -/
def hoopArcs (g : GraphData n) (p : PathList n) : List (Fin n × PathList n) :=
  (List.finRange n).flatMap fun j =>
    match bubbleSplit g p j with
    | none => []
    | some s => if (p.length - s) % 2 = 0 then [(j, p.take (s + 1))] else []

/-- There is an even-hoop arc `p → q`. -/
def isArc (g : GraphData n) (p q : PathList n) : Bool :=
  (hoopArcs g p).any fun a => a.2 == q

/-- The tree part of Eq. (decoratedtree), first two cases: weight `1` for `P → P + x`
and `b_x²` for `P + x → P`, with `x` the terminal vertex of the source. -/
def treeWeight (bsq : Fin n → ℚ) (p q : PathList n) : ℚ :=
  if p.length + 1 = q.length ∧ q.take p.length = p then 1
  else if q.length + 1 = p.length ∧ p.take q.length = q then
    (match p.getLast? with | some (some j) => bsq j | _ => 0)
  else 0

/-- A matrix on the positions of a list of paths. -/
def matrixOf (ps : List (PathList n)) (f : PathList n → PathList n → ℚ) :
    Matrix (Fin ps.length) (Fin ps.length) ℚ :=
  Matrix.of fun i j => f (ps.get i) (ps.get j)

/-- The tree matrix plus the constant weight `w` on every even-hoop arc, on the rooted
induced paths of `G*`; `bsq j` is `b_j²`. -/
def hoopMatrix (g : GraphData n) (bsq : Fin n → ℚ) (w : ℚ) :
    Matrix (Fin (rootedPaths g).length) (Fin (rootedPaths g).length) ℚ :=
  matrixOf (rootedPaths g) fun p q => treeWeight bsq p q + if isArc g p q then w else 0

/-- The list `[j*, j₁, …, j_ℓ]` of a rooted induced path of `G*`. -/
def pathList {G : SimpleGraph V} {K : Set V} (P : CliqueRootedInducedPath G K) :
    List (Option V) :=
  List.ofFn P.path.vertex

/-! ### The list model is the induced-path tree of the repo -/

section Bridge

/-- The Boolean data `g` describes the graph `G` and the clique `K`. -/
structure Represents (g : GraphData n) (G : SimpleGraph (Fin n)) (K : Set (Fin n)) : Prop where
  adj_iff : ∀ a b, G.Adj a b ↔ g.adj a b = true
  mem_iff : ∀ v, v ∈ K ↔ g.clique v = true

variable {g : GraphData n} {G : SimpleGraph (Fin n)} {K : Set (Fin n)}

/-- The model adjacency `adjS` is adjacency in `G* = G.adjoinRootAt K`. -/
theorem Represents.adjS_iff (h : Represents g G K) (x y : Option (Fin n)) :
    adjS g x y = true ↔ (G.adjoinRootAt K).Adj x y := by
  cases x with
  | none =>
    cases y with
    | none => simp [adjS, adjoinRootAt]
    | some v => simp [adjS, adjoinRootAt, AdjoinRootAdj, h.mem_iff]
  | some u =>
    cases y with
    | none => simp [adjS, adjoinRootAt, AdjoinRootAdj, h.mem_iff]
    | some v => exact (h.adj_iff u v).symm

/-- The Boolean test `isRootedInduced` unfolded: head `j*`, no repetition, and adjacency in
`G*` exactly between consecutive entries. -/
theorem isRootedInduced_iff (p : PathList n) :
    isRootedInduced g p = true ↔ p.head? = some none ∧ p.Nodup ∧
      ∀ i j, i < j → j < p.length →
        (adjS g (p.getD i none) (p.getD j none) = true ↔ j = i + 1) := by
  unfold isRootedInduced
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, beq_eq_decide, and_assoc]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun i j hij hj => ?_⟩
    have := (h3 i (by omega) j hj).resolve_left (not_not.2 hij)
    rw [this]
    simp
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun i hi j hj => ?_⟩
    by_cases hij : i < j
    · right
      rw [Bool.eq_iff_iff]
      simpa using h3 i j hij hj
    · left
      exact hij

/-- The list of every `CliqueRootedInducedPath` passes the model test. -/
theorem Represents.isRootedInduced_pathList (h : Represents g G K)
    (P : CliqueRootedInducedPath G K) :
    isRootedInduced g (pathList P) = true := by
  rw [isRootedInduced_iff]
  refine ⟨?_, ?_, ?_⟩
  · have h0 := P.root_eq
    have hc := P.path.nonempty
    rw [List.head?_eq_getElem?, pathList, List.getElem?_ofFn]
    simp [hc, h0]
  · exact List.nodup_ofFn.2 P.path.injective
  · intro i j hij hj
    simp only [pathList, List.length_ofFn] at hj
    have hi : i < P.path.card := by omega
    have hj' : j < P.path.card := hj
    simp only [pathList, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
      hi, hj', dite_true, Option.getD_some]
    rw [h.adjS_iff, P.path.adj_iff]
    show i + 1 = j ∨ j + 1 = i ↔ j = i + 1
    omega

/-- Every list passing the model test is the list of a `CliqueRootedInducedPath`. -/
theorem Represents.exists_pathList (h : Represents g G K) {p : PathList n}
    (hp : isRootedInduced g p = true) :
    ∃ P : CliqueRootedInducedPath G K, (pathList P) = p := by
  obtain ⟨h1, h2, h3⟩ := (isRootedInduced_iff p).1 hp
  have hne : 0 < p.length := by
    cases p with
    | nil => simp at h1
    | cons a l => simp
  have hget : ∀ i j : Fin p.length, i.val < j.val →
      ((G.adjoinRootAt K).Adj (p.get i) (p.get j) ↔ j.val = i.val + 1) := by
    intro i j hij
    rw [← h.adjS_iff]
    have := h3 i j hij j.isLt
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.isLt,
      List.getElem?_eq_getElem j.isLt] using this
  refine ⟨⟨⟨p.length, hne, fun i => p.get i, ?_, ?_⟩, ?_⟩, ?_⟩
  · exact List.nodup_iff_injective_get.1 h2
  · intro i j
    rcases lt_trichotomy i.val j.val with hij | hij | hij
    · rw [hget i j hij]; omega
    · have : i = j := Fin.ext hij
      subst this
      constructor
      · intro hh; exact absurd hh ((G.adjoinRootAt K).loopless.irrefl _)
      · intro hh; omega
    · rw [(G.adjoinRootAt K).adj_comm, hget j i hij]; omega
  · cases p with
    | nil => simp at h1
    | cons a l => simpa using h1
  · exact List.ofFn_get p

/-- The root path `[j*]` passes the model test. -/
theorem isRootedInduced_root : isRootedInduced g ([none] : PathList n) = true := by
  rw [isRootedInduced_iff]
  refine ⟨rfl, List.nodup_singleton _, ?_⟩
  intro i j hij hj
  simp at hj
  omega

/-- Prefixes of rooted induced paths are rooted induced paths. -/
theorem isRootedInduced_of_append {a b : PathList n} (ha : a ≠ [])
    (h : isRootedInduced g (a ++ b) = true) : isRootedInduced g a = true := by
  rw [isRootedInduced_iff] at h ⊢
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, h2.sublist (List.prefix_append a b).sublist, ?_⟩
  · rwa [List.head?_append_of_ne_nil _ ha] at h1
  · intro i j hij hj
    have := h3 i j hij (by simp; omega)
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_append_left (show i < a.length by omega),
      List.getElem?_append_left hj] using this

/-- Soundness of the depth-first enumeration. -/
theorem isRootedInduced_of_mem_pathsAux {f : ℕ} {q p : PathList n}
    (hp : p ∈ pathsAux g f q) (hq : isRootedInduced g q = true) :
    isRootedInduced g p = true := by
  induction f generalizing q p with
  | zero =>
    simp only [pathsAux, List.mem_singleton] at hp
    exact hp ▸ hq
  | succ f ih =>
    simp only [pathsAux, List.mem_cons, List.mem_flatMap, List.mem_filter] at hp
    rcases hp with rfl | ⟨x, ⟨_, hx⟩, hp⟩
    · exact hq
    · exact ih hp hx

/-- Completeness of the depth-first enumeration: a rooted induced path `q ++ t`, `t` made of
original vertices with at most `f` entries, is found below `q`. -/
theorem mem_pathsAux_of_append {f : ℕ} :
    ∀ {q t : PathList n}, isRootedInduced g q = true → (∀ y ∈ t, ∃ x, y = some x) →
      isRootedInduced g (q ++ t) = true → t.length ≤ f → q ++ t ∈ pathsAux g f q := by
  induction f with
  | zero =>
    intro q t _ _ _ hl
    have : t = [] := List.length_eq_zero_iff.1 (by omega)
    subst this
    simp [pathsAux]
  | succ f ih =>
    intro q t hq hall hqt hl
    cases t with
    | nil => simp [pathsAux]
    | cons y t' =>
      obtain ⟨x, rfl⟩ := hall y (by simp)
      have hq1 : isRootedInduced g (q ++ [some x]) = true := by
        apply isRootedInduced_of_append (b := t') (by simp)
        simpa using hqt
      have key := ih (q := q ++ [some x]) (t := t') hq1
        (fun z hz => hall z (by simp [hz])) (by simpa using hqt) (by simp at hl; omega)
      simp only [pathsAux, List.mem_cons, List.mem_flatMap, List.mem_filter]
      right
      exact ⟨x, ⟨List.mem_finRange x, hq1⟩, by simpa using key⟩

/-- `rootedPaths g` lists exactly the lists passing the model test (a rooted induced path has at
most `n` original vertices, by `Nodup`). -/
theorem mem_rootedPaths_iff (p : PathList n) :
    p ∈ rootedPaths g ↔ isRootedInduced g p = true := by
  constructor
  · intro hp
    exact isRootedInduced_of_mem_pathsAux hp isRootedInduced_root
  · intro hp
    obtain ⟨h1, h2, -⟩ := (isRootedInduced_iff p).1 hp
    cases p with
    | nil => simp at h1
    | cons a t =>
      have ha : a = none := by simpa using h1
      subst ha
      have hlen : (none :: t : PathList n).length ≤ n + 1 := by
        simpa using h2.length_le_card
      have hall : ∀ y ∈ t, ∃ x, y = some x := by
        intro y hy
        cases y with
        | none => exact absurd hy (List.nodup_cons.1 h2).1
        | some x => exact ⟨x, rfl⟩
      exact mem_pathsAux_of_append isRootedInduced_root hall hp (by simp at hlen; omega)

/-- A rooted induced path is determined by its list. -/
theorem pathList_injective {V : Type u} {G : SimpleGraph V} {K : Set V} :
    Function.Injective (pathList (G := G) (K := K)) := by
  intro P Q h
  apply RootedInducedPath.ext_path
  obtain ⟨⟨c, hc, v, hv, ha⟩, hr⟩ := P
  obtain ⟨⟨c', hc', v', hv', ha'⟩, hr'⟩ := Q
  simp only [pathList] at h
  have := List.ofFn_inj'.1 h
  simp only [Sigma.mk.inj_iff] at this
  obtain ⟨rfl, hh⟩ := this
  cases hh
  rfl

/-- The list of the prefix `P_m` is the corresponding prefix of the list. -/
theorem pathList_initialSegment (P : CliqueRootedInducedPath G K) (m : Fin P.path.card) :
    pathList (P.initialSegment m) = (pathList P).take (m.val + 1) := by
  simp only [pathList]
  apply List.ext_getElem
  · simp [RootedInducedPath.initialSegment, IndexedInducedPath.initialSegment]
  · intro i h1 h2
    rw [List.getElem_ofFn, List.getElem_take, List.getElem_ofFn]
    rfl

/-- The list of a rooted induced path has `|P|` entries. -/
theorem length_pathList (P : CliqueRootedInducedPath G K) :
    (pathList P).length = P.path.card := by
  simp [pathList]

/-- Entries of the list. -/
theorem getD_pathList (P : CliqueRootedInducedPath G K) {q : ℕ} (hq : q < P.path.card) :
    (pathList P).getD q none = P.path.vertex ⟨q, hq⟩ := by
  simp [pathList, List.getD_eq_getElem?_getD, hq]

/-- Membership in the list is membership in the range of the vertex map. -/
theorem mem_pathList_iff (P : CliqueRootedInducedPath G K) (x : Option (Fin n)) :
    x ∈ (pathList P) ↔ x ∈ Set.range P.path.vertex := by
  simp [pathList, List.mem_ofFn]

/-- The model bubble wands are the `CliqueBubbleWand`s (root handle included): `j` has split
index `s` on the list of `P` iff some wand on `P` has bubble `j` and split index `s`. -/
theorem Represents.bubbleSplit_eq_some_iff (h : Represents g G K)
    (P : CliqueRootedInducedPath G K) (j : Fin n) (s : ℕ) :
    bubbleSplit g (pathList P) j = some s ↔
      ∃ w : CliqueBubbleWand G K P, w.bubble = j ∧ w.split.val = s := by
  have hlen := length_pathList P
  constructor
  · intro hb
    unfold bubbleSplit at hb
    by_cases hmem : some j ∈ (pathList P)
    · simp [hmem] at hb
    · rw [if_neg hmem] at hb
      generalize hL : (List.range (pathList P).length).filter
        (fun q => adjS g (some j) ((pathList P).getD q none)) = L at hb
      rcases L with _ | ⟨s0, _ | ⟨s1, _ | ⟨e, _ | ⟨x, l⟩⟩⟩⟩ <;> simp at hb
      obtain ⟨⟨hs1, he, hgap⟩, hs0⟩ := hb
      subst hs0
      have key : ∀ q, q ∈ (List.range (pathList P).length).filter
          (fun q => adjS g (some j) ((pathList P).getD q none)) ↔ q ∈ [s0, s1, e] := by
        intro q; rw [hL]
      simp only [List.mem_filter, List.mem_range, List.mem_cons,
        List.not_mem_nil, or_false] at key
      refine ⟨⟨j, ⟨s0, by omega⟩, (by show s0 + 3 < P.path.card; omega), ?_, ?_⟩,
        rfl, rfl⟩
      · rw [← mem_pathList_iff]; exact hmem
      · intro q
        have hk := key q.val
        rw [getD_pathList P q.isLt, h.adjS_iff] at hk
        have hq : q.val < (pathList P).length := by rw [hlen]; exact q.isLt
        simp only [hq, true_and] at hk
        rw [hk]
        simp only [hs1]
        omega
  · rintro ⟨w, rfl, rfl⟩
    unfold bubbleSplit
    rw [if_neg (by rw [mem_pathList_iff]; exact w.outside)]
    have hL : (List.range (pathList P).length).filter
        (fun q => adjS g (some w.bubble) ((pathList P).getD q none)) =
        [w.split.val, w.split.val + 1, P.path.card - 1] := by
      apply List.Pairwise.eq_of_mem_iff (r := (· < ·))
      · exact List.Pairwise.filter _ List.pairwise_lt_range
      · have := w.gap
        simp [List.pairwise_cons]
        omega
      · intro q
        simp only [List.mem_filter, List.mem_range, List.mem_cons,
          List.not_mem_nil, or_false]
        constructor
        · rintro ⟨hq, hadj⟩
          have hq' : q < P.path.card := by rw [hlen] at hq; exact hq
          rw [getD_pathList P hq', h.adjS_iff, w.adj_iff ⟨q, hq'⟩] at hadj
          simp only at hadj
          omega
        · intro hq
          have hq' : q < P.path.card := by have := w.gap; omega
          refine ⟨by rw [hlen]; exact hq', ?_⟩
          rw [getD_pathList P hq', h.adjS_iff, w.adj_iff ⟨q, hq'⟩]
          simp only
          omega
    rw [hL]
    have := w.gap
    simp only [length_pathList]
    rw [if_pos]
    exact ⟨trivial, by omega, by omega⟩


/-- Membership in `hoopArcs` unfolded. -/
theorem mem_hoopArcs_iff (g : GraphData n) (p : PathList n) (a : Fin n × PathList n) :
    a ∈ hoopArcs g p ↔ ∃ s, bubbleSplit g p a.1 = some s ∧ (p.length - s) % 2 = 0 ∧
      a.2 = p.take (s + 1) := by
  unfold hoopArcs
  simp only [List.mem_flatMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨j, hj⟩
    cases hb : bubbleSplit g p j with
    | none => simp [hb] at hj
    | some s =>
      by_cases hev : (p.length - s) % 2 = 0
      · simp [hb, hev] at hj
        subst hj
        exact ⟨s, hb, hev, rfl⟩
      · simp [hb, hev] at hj
  · rintro ⟨s, hb, hev, h1⟩
    refine ⟨a.1, ?_⟩
    rw [hb]
    simp only [hev, if_true, List.mem_singleton]
    cases a
    simp_all

/-- The model arcs are the even-hoop arcs of `Λ(G*)` (`EvenHoopArc`, root handle included). -/
theorem Represents.isArc_pathList_iff (h : Represents g G K) (P Q : CliqueRootedInducedPath G K) :
    isArc g (pathList P) (pathList Q) = true ↔ EvenHoopArc G K P Q := by
  have hlen := length_pathList P
  unfold isArc
  rw [List.any_eq_true]
  constructor
  · rintro ⟨a, ha, hq⟩
    rw [beq_iff_eq] at hq
    obtain ⟨s, hs, hev, hh⟩ := (mem_hoopArcs_iff g _ a).1 ha
    obtain ⟨w, -, hw2⟩ := (h.bubbleSplit_eq_some_iff P a.1 s).1 hs
    refine ⟨w, ?_, ?_⟩
    · apply pathList_injective
      rw [← hq, hh, ← hw2]
      exact pathList_initialSegment P w.split
    · unfold CliqueBubbleWand.hoopCard
      rw [hw2, ← hlen]
      exact Nat.even_iff.2 hev
  · rintro ⟨w, hw, hev⟩
    have hb := (h.bubbleSplit_eq_some_iff P w.bubble w.split.val).2 ⟨w, rfl, rfl⟩
    refine ⟨(w.bubble, (pathList P).take (w.split.val + 1)), ?_, ?_⟩
    · rw [mem_hoopArcs_iff]
      refine ⟨w.split.val, hb, ?_, rfl⟩
      unfold CliqueBubbleWand.hoopCard at hev
      rw [hlen]
      exact Nat.even_iff.1 hev
    · rw [beq_iff_eq, ← hw]
      exact (pathList_initialSegment P w.split).symm

/-- One-vertex extension, on lists. -/
theorem isOneVertexExtension_iff (P Q : CliqueRootedInducedPath G K) :
    P.IsOneVertexExtension Q ↔
      (pathList P).length + 1 = (pathList Q).length ∧
        (pathList Q).take (pathList P).length = pathList P := by
  rw [length_pathList, length_pathList]
  constructor
  · rintro ⟨hcard, hv⟩
    refine ⟨hcard, ?_⟩
    apply List.ext_getElem
    · simp only [List.length_take, length_pathList]
      omega
    · intro i h1 h2
      simp only [pathList, List.getElem_take, List.getElem_ofFn]
      exact hv ⟨i, by simpa [pathList] using h2⟩
  · rintro ⟨hcard, htake⟩
    refine ⟨hcard, fun i => ?_⟩
    have h1 : i.val < ((pathList Q).take P.path.card).length := by
      simp only [List.length_take, length_pathList]
      omega
    have h2 := List.getElem_of_eq htake h1
    simp only [pathList, List.getElem_take, List.getElem_ofFn] at h2
    exact h2

/-- The last entry of the list is the terminal vertex. -/
theorem getLast?_pathList (P : CliqueRootedInducedPath G K) :
    (pathList P).getLast? = some P.terminalVertex := by
  have hc := P.path.nonempty
  rw [List.getLast?_eq_getElem?, length_pathList]
  simp [pathList, hc, RootedInducedPath.terminalVertex]

/-- The tree entries of the repo matrix are the model tree weights (for `b_j² = bsq j`). -/
theorem cliqueTreeMatrix_eq_treeWeight {R : Type w} [Field R] [CharZero R]
    (b : Fin n → R) (bsq : Fin n → ℚ) (hb : ∀ v, b v ^ 2 = (bsq v : R))
    (P Q : CliqueRootedInducedPath G K) :
    cliqueTreeMatrix G K b P Q = ((treeWeight bsq (pathList P) (pathList Q) : ℚ) : R) := by
  classical
  unfold cliqueTreeMatrix treeWeight
  by_cases h1 : P.IsOneVertexExtension Q
  · rw [if_pos h1, if_pos ((isOneVertexExtension_iff P Q).1 h1), Rat.cast_one]
  · have h1' : ¬((pathList P).length + 1 = (pathList Q).length ∧
        (pathList Q).take (pathList P).length = pathList P) :=
      fun h => h1 ((isOneVertexExtension_iff P Q).2 h)
    rw [if_neg h1, if_neg h1']
    by_cases h2 : Q.IsOneVertexExtension P
    · rw [if_pos h2, if_pos ((isOneVertexExtension_iff Q P).1 h2), getLast?_pathList]
      cases P.terminalVertex with
      | none => simp
      | some j => simp [hb]
    · have h2' : ¬((pathList Q).length + 1 = (pathList P).length ∧
          (pathList P).take (pathList Q).length = pathList Q) :=
        fun h => h2 ((isOneVertexExtension_iff Q P).2 h)
      rw [if_neg h2, if_neg h2', Rat.cast_zero]

end Bridge


/-! ### The counterexample -/

namespace Example

/-- The edges of the counterexample graph on `{0, …, 6}`. -/
def edges7 : List (Fin 7 × Fin 7) :=
  [(0, 1), (0, 2), (0, 3), (0, 5), (0, 6), (1, 2), (1, 4), (2, 5), (3, 4), (3, 5), (3, 6),
    (4, 6), (5, 6)]

/-- The graph and the clique `K = {2, 5}` as list-model data. -/
def g7 : GraphData 7 where
  adj a b := edges7.contains (a, b) || edges7.contains (b, a)
  clique v := decide (v = 2 ∨ v = 5)

/-- The couplings `b_j²` of the work package: `b² = (4, 4, 1, 3, 5, 4, 4)`. -/
def bsq7 : Fin 7 → ℚ := ![4, 4, 1, 3, 5, 4, 4]

/-- The counterexample graph `G` as a `SimpleGraph`. -/
def ex7 : SimpleGraph (Fin 7) where
  Adj a b := g7.adj a b = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

/-- The simplicial clique `K = {2, 5}`. -/
def exK : Set (Fin 7) := {v | g7.clique v = true}

/-- The list-model data `g7`, `K` describe the `SimpleGraph` `ex7` and the set `exK`. -/
theorem represents_g7 : Represents g7 ex7 exK := ⟨fun _ _ => Iff.rfl, fun _ => Iff.rfl⟩

set_option synthInstance.maxSize 1024 in
/-- `G` is claw-free. -/
theorem ex7_isClawFree : ex7.IsClawFree := by
  have h : ∀ c a b d : Fin 7, g7.adj c a = true → g7.adj c b = true →
      g7.adj c d = true → a ≠ b → a ≠ d → b ≠ d →
      g7.adj a b = true ∨ g7.adj a d = true ∨ g7.adj b d = true := by
    decide +kernel
  intro c a b d h1 h2 h3 h4 h5 h6
  exact h c a b d h1 h2 h3 h4 h5 h6

/-- `K = {2, 5}` is a simplicial clique of `G`. -/
theorem ex7_isSimplicialClique : ex7.IsSimplicialClique exK := by
  have h1 : ∀ x y : Fin 7, g7.clique x = true → g7.clique y = true → x ≠ y →
      g7.adj x y = true := by
    decide +kernel
  have h2 : ∀ j x y : Fin 7, g7.clique j = true → g7.adj j x = true → g7.clique x = false →
      g7.adj j y = true → g7.clique y = false → x ≠ y → g7.adj x y = true := by
    decide +kernel
  refine ⟨fun x hx y hy hxy => h1 x y hx hy hxy, ?_⟩
  intro j hj x hx y hy hxy
  refine h2 j x y hj hx.1 ?_ hy.1 ?_ hxy
  · simpa [exK] using hx.2
  · simpa [exK] using hy.2

/-- The path `P = (j*, 2, 0)` of `G*` as an indexed induced path. -/
def exPath : IndexedInducedPath (ex7.adjoinRootAt exK) where
  card := 3
  nonempty := by decide
  vertex := ![none, some 2, some 0]
  injective := by decide
  adj_iff := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [adjoinRootAt, AdjoinRootAdj, ex7, exK, g7, edges7]

/-- The rooted induced path `P = (j*, 2, 0)`, `ℓ = 2`. -/
def exP : CliqueRootedInducedPath ex7 exK where
  path := exPath
  root_eq := rfl

/-- `5` is a clone of `2` in `P`: `Γ_P(5) = {j*, 2, 0}` (`5 ≺_P 2`, Definition 10). -/
theorem exPath_deform : exPath.SingleVertexDeformation (some 5) ⟨1, by decide⟩ := by
  refine ⟨?_, by decide, by decide, ?_⟩
  · rintro ⟨q, hq⟩
    fin_cases q <;> simp [exPath] at hq
  · intro q
    fin_cases q <;> simp [adjoinRootAt, AdjoinRootAdj, exPath, ex7, exK, g7, edges7]

/-- The deformation `P~ = (j*, 5, 0)` of `P`. -/
def exP' : CliqueRootedInducedPath ex7 exK where
  path := exPath.deform exPath_deform
  root_eq := rfl

/-- The list of `P`. -/
theorem pathList_exP : pathList exP = [none, some 2, some 0] := rfl

/-- The list of `P~`. -/
theorem pathList_exP' : pathList exP' = [none, some 5, some 0] := by decide +kernel

/-- The list of the root path. -/
theorem pathList_root : pathList (cliqueRootPath ex7 exK) = [none] := rfl

/-- `P~` is a single-vertex deformation of `P`, hence lies in the deformation closure
`⟨P⟩` of Definition 12. -/
theorem exP'_deformationStep :
    InducedPathDeformationStep (ex7.adjoinRootAt exK) exP.path exP'.path :=
  ⟨some 5, ⟨1, by decide⟩, exPath_deform, rfl⟩

/-- `|P| = 3`, i.e. `ℓ = 2`. -/
theorem exP_card : exP.path.card = 3 := rfl

/-- The model enumerates `21` rooted induced paths of `G*`. -/
theorem rootedPaths_length : (rootedPaths g7).length = 21 := by decide +kernel

/-- The enumeration has no repetition. -/
theorem rootedPaths_nodup : (rootedPaths g7).Nodup := by decide +kernel

/-- The arcs added to the induced-path tree by even holes (Definition 18): eight bubble
events, as triples (source, handle, bubble).  The source `(j*, 5, 0, 1, 4)` reaches the
handle `(j*, 5)` through the two bubbles `3` and `6`. -/
theorem hoop_arcs :
    (rootedPaths g7).flatMap (fun p => (hoopArcs g7 p).map fun a => (p, a.2, a.1)) =
      [([none, some 2, some 0, some 3, some 4], [none, some 2], 1),
       ([none, some 2, some 0, some 6, some 4], [none, some 2], 1),
       ([none, some 2, some 1, some 4, some 3], [none, some 2], 0),
       ([none, some 2, some 1, some 4, some 6], [none, some 2], 0),
       ([none, some 5, some 0, some 1, some 4], [none, some 5], 3),
       ([none, some 5, some 0, some 1, some 4], [none, some 5], 6),
       ([none, some 5, some 3, some 4, some 1], [none, some 5], 0),
       ([none, some 5, some 6, some 4, some 1], [none, some 5], 0)] := by
  decide +kernel

/-- Every source has at most one target. -/
theorem model_arc_unique :
    ∀ p ∈ rootedPaths g7, ∀ a ∈ hoopArcs g7 p, ∀ a' ∈ hoopArcs g7 p, a.2 = a'.2 := by
  decide +kernel

/-- The list of every rooted induced path of the example is in the model list. -/
theorem pathList_mem_rootedPaths (P : CliqueRootedInducedPath ex7 exK) :
    pathList P ∈ rootedPaths g7 :=
  (mem_rootedPaths_iff _).2 (represents_g7.isRootedInduced_pathList P)

/-- In the example every rooted induced path has at most one target through an even hoop. -/
theorem arc_unique (P Q Q' : CliqueRootedInducedPath ex7 exK)
    (h : EvenHoopArc ex7 exK P Q) (h' : EvenHoopArc ex7 exK P Q') : Q = Q' := by
  have hP := (represents_g7.isArc_pathList_iff P Q).2 h
  have hP' := (represents_g7.isArc_pathList_iff P Q').2 h'
  unfold isArc at hP hP'
  rw [List.any_eq_true] at hP hP'
  obtain ⟨a, ha, haq⟩ := hP
  obtain ⟨a', ha', haq'⟩ := hP'
  rw [beq_iff_eq] at haq haq'
  have := model_arc_unique _ (pathList_mem_rootedPaths P) a ha a' ha'
  apply pathList_injective
  rw [← haq, ← haq', this]

/-- The rooted induced paths of `G*` are in bijection with the positions of the model list. -/
noncomputable def pathEquiv : CliqueRootedInducedPath ex7 exK ≃ Fin (rootedPaths g7).length :=
  Equiv.ofBijective
    (fun P => ⟨(rootedPaths g7).idxOf (pathList P),
      List.idxOf_lt_length_iff.2 (pathList_mem_rootedPaths P)⟩)
    ⟨fun P Q h => by
      have h1 := congrArg Fin.val h
      exact pathList_injective
        ((List.idxOf_inj (pathList_mem_rootedPaths P)).1 h1),
     fun i => by
      obtain ⟨P, hP⟩ := represents_g7.exists_pathList
        ((mem_rootedPaths_iff _).1 (List.get_mem (rootedPaths g7) i))
      refine ⟨P, Fin.ext ?_⟩
      show (rootedPaths g7).idxOf (pathList P) = i.val
      rw [hP]
      exact List.get_idxOf rootedPaths_nodup i⟩

/-- `pathEquiv` reads off the list. -/
theorem get_pathEquiv (P : CliqueRootedInducedPath ex7 exK) :
    (rootedPaths g7).get (pathEquiv P) = pathList P := by
  show (rootedPaths g7)[(rootedPaths g7).idxOf (pathList P)]'_ = _
  exact List.getElem_idxOf _


open Classical in
/-- **Transfer to the list model.**  For couplings with `b_j² = bsq j`, a constant eigenvalue
`λ = c` and any printed normalisation `N`, the powers of the printed matrix of the example
are the (rational) powers of the list-model matrix `hoopMatrix g7 bsq (2 c)`, read through
the bijection `pathEquiv`: the hoop weight is `λ / N = 2 λ` because `N = 1/2` is forced. -/
theorem printed_pow_apply {R : Type w} [Field R] [CharZero R] (b : Fin 7 → R)
    (bsq : Fin 7 → ℚ) (hb : ∀ j, b j ^ 2 = (bsq j : R)) (c : ℚ)
    {N : CliqueRootedInducedPath ex7 exK → CliqueRootedInducedPath ex7 exK → R}
    (hN : IsPrintedNormalisation ex7 exK N) (k : ℕ) (P Q : CliqueRootedInducedPath ex7 exK) :
    (printedHoppingMatrix ex7 exK b (fun _ => (c : R)) N ^ k) P Q =
      (((hoopMatrix g7 bsq (2 * c) ^ k) (pathEquiv P) (pathEquiv Q) : ℚ) : R) := by
  have hentry : ∀ P Q : CliqueRootedInducedPath ex7 exK,
      printedHoppingMatrix ex7 exK b (fun _ => (c : R)) N P Q =
        (((hoopMatrix g7 bsq (2 * c)) (pathEquiv P) (pathEquiv Q) : ℚ) : R) := by
    intro P Q
    rw [hN.matrix_apply arc_unique, cliqueTreeMatrix_eq_treeWeight b bsq hb]
    simp only [hoopMatrix, matrixOf, Matrix.of_apply, get_pathEquiv]
    rw [Rat.cast_add]
    congr 1
    by_cases hA : EvenHoopArc ex7 exK P Q
    · rw [dif_pos hA, if_pos ((represents_g7.isArc_pathList_iff P Q).2 hA)]
      push_cast
      ring
    · rw [dif_neg hA, if_neg (fun h => hA ((represents_g7.isArc_pathList_iff P Q).1 h))]
      simp
  set M := hoopMatrix g7 bsq (2 * c) with hM
  have hAB : printedHoppingMatrix ex7 exK b (fun _ => (c : R)) N =
      ((Rat.castHom R).mapMatrix M).submatrix pathEquiv pathEquiv := by
    ext P Q
    simp [hentry]
  have hpow : ∀ k : ℕ, (((Rat.castHom R).mapMatrix M).submatrix pathEquiv pathEquiv) ^ k =
      (((Rat.castHom R).mapMatrix M) ^ k).submatrix pathEquiv pathEquiv := by
    intro k
    induction k with
    | zero => simp [Matrix.submatrix_one_equiv]
    | succ k ih => rw [pow_succ, ih, pow_succ, Matrix.submatrix_mul_equiv]
  rw [hAB, hpow k, ← map_pow]
  simp


/-- The root path is at position `0`. -/
theorem pathEquiv_root : pathEquiv (cliqueRootPath ex7 exK) = ⟨0, by decide +kernel⟩ := by
  apply Fin.ext
  show (rootedPaths g7).idxOf (pathList (cliqueRootPath ex7 exK)) = 0
  rw [pathList_root]
  decide +kernel

/-- `P` is at position `2`. -/
theorem pathEquiv_exP : pathEquiv exP = ⟨2, by decide +kernel⟩ := by
  apply Fin.ext
  show (rootedPaths g7).idxOf (pathList exP) = 2
  rw [pathList_exP]
  decide +kernel

/-- `P~` is at position `12`. -/
theorem pathEquiv_exP' : pathEquiv exP' = ⟨12, by decide +kernel⟩ := by
  apply Fin.ext
  show (rootedPaths g7).idxOf (pathList exP') = 12
  rw [pathList_exP']
  decide +kernel

/-- The data of the work package (`b² = (4, 4, 1, 3, 5, 4, 4)`, `λ = 3`, hoop weight
`2 λ = 6`): `(A^6)` entries `428` and `422` in the list model. -/
theorem model_pow_six_package :
    (hoopMatrix g7 bsq7 (2 * 3) ^ 6) ⟨0, by decide +kernel⟩ ⟨2, by decide +kernel⟩ = 428 ∧
      (hoopMatrix g7 bsq7 (2 * 3) ^ 6) ⟨0, by decide +kernel⟩ ⟨12, by decide +kernel⟩ =
        422 := by
  decide +kernel

/-- Unit couplings `b = 1` and `λ = 1` (hoop weight `2`): the rows of `P` and `P~` agree for
`k < 6`. -/
theorem model_pow_eq_of_lt_six : ∀ k < 6,
    (hoopMatrix g7 (fun _ => 1) (2 * 1) ^ k) ⟨0, by decide +kernel⟩ ⟨2, by decide +kernel⟩ =
      (hoopMatrix g7 (fun _ => 1) (2 * 1) ^ k) ⟨0, by decide +kernel⟩ ⟨12, by decide +kernel⟩ := by
  decide +kernel

/-- Unit couplings `b = 1` and `λ = 1`: `(A^6)` entries `42` and `40` in the list model. -/
theorem model_pow_six_unit :
    (hoopMatrix g7 (fun _ => 1) (2 * 1) ^ 6) ⟨0, by decide +kernel⟩ ⟨2, by decide +kernel⟩ = 42 ∧
      (hoopMatrix g7 (fun _ => 1) (2 * 1) ^ 6) ⟨0, by decide +kernel⟩ ⟨12, by decide +kernel⟩ =
        40 := by
  decide +kernel

open Classical in
/-- A printed normalisation exists on the example (`N = 1/2`), so the counterexample theorems
are not vacuous. -/
theorem exists_isPrintedNormalisation {R : Type w} [Field R] [CharZero R] :
    ∃ N : CliqueRootedInducedPath ex7 exK → CliqueRootedInducedPath ex7 exK → R,
      IsPrintedNormalisation ex7 exK N := by
  refine ⟨fun _ _ => 1 / 2, fun P Q h => ?_⟩
  have hfilter : Finset.univ.filter
      (fun Q' => ∃ h' : EvenHoopArc ex7 exK P Q', arcClass h' = arcClass h) = {Q} := by
    ext Q'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨h', -⟩
      exact arc_unique P Q' Q h' h
    · rintro rfl
      exact ⟨h, rfl⟩
  rw [hfilter, Finset.sum_singleton]
  simp

open Classical in
/-- **The work-package instance.**  For every field `R` of characteristic zero, couplings with
`b² = (4, 4, 1, 3, 5, 4, 4)`, `λ = 3` on every class and every printed normalisation `N`, the
printed matrix has `(A^6)_{{j*},P} = 428` and `(A^6)_{{j*},P~} = 422`. -/
theorem printed_pow_six_package {R : Type w} [Field R] [CharZero R] (b : Fin 7 → R)
    (hb : ∀ j, b j ^ 2 = (bsq7 j : R))
    {N : CliqueRootedInducedPath ex7 exK → CliqueRootedInducedPath ex7 exK → R}
    (hN : IsPrintedNormalisation ex7 exK N) :
    (printedHoppingMatrix ex7 exK b (fun _ => (3 : R)) N ^ 6) (cliqueRootPath ex7 exK) exP = 428 ∧
      (printedHoppingMatrix ex7 exK b (fun _ => (3 : R)) N ^ 6) (cliqueRootPath ex7 exK) exP' =
        422 := by
  have h3 : (fun _ : EvenHoleDeformationClass ex7 => (3 : R)) = fun _ => ((3 : ℚ) : R) := by
    funext _
    simp
  have e1 := printed_pow_apply b bsq7 hb 3 hN 6 (cliqueRootPath ex7 exK) exP
  have e2 := printed_pow_apply b bsq7 hb 3 hN 6 (cliqueRootPath ex7 exK) exP'
  obtain ⟨m1, m2⟩ := model_pow_six_package
  rw [pathEquiv_root, pathEquiv_exP, m1] at e1
  rw [pathEquiv_root, pathEquiv_exP', m2] at e2
  rw [h3]
  exact ⟨by rw [e1]; norm_num, by rw [e2]; norm_num⟩

open Classical in
/-- Unit couplings `b_j = 1` and `λ = 1`, any field `R` of characteristic zero and any printed
normalisation `N`: `(A^6)_{{j*},P} = 42` and `(A^6)_{{j*},P~} = 40`, while the two rows agree for
`k < 6`. -/
theorem printed_pow_unit {R : Type w} [Field R] [CharZero R]
    {N : CliqueRootedInducedPath ex7 exK → CliqueRootedInducedPath ex7 exK → R}
    (hN : IsPrintedNormalisation ex7 exK N) :
    (∀ k < 6, (printedHoppingMatrix ex7 exK (fun _ => (1 : R)) (fun _ => (1 : R)) N ^ k)
        (cliqueRootPath ex7 exK) exP =
      (printedHoppingMatrix ex7 exK (fun _ => (1 : R)) (fun _ => (1 : R)) N ^ k)
        (cliqueRootPath ex7 exK) exP') ∧
    (printedHoppingMatrix ex7 exK (fun _ => (1 : R)) (fun _ => (1 : R)) N ^ 6)
        (cliqueRootPath ex7 exK) exP = 42 ∧
      (printedHoppingMatrix ex7 exK (fun _ => (1 : R)) (fun _ => (1 : R)) N ^ 6)
        (cliqueRootPath ex7 exK) exP' = 40 := by
  have hb : ∀ j : Fin 7,
      (fun _ : Fin 7 => (1 : R)) j ^ 2 = (((fun _ : Fin 7 => (1 : ℚ)) j : ℚ) : R) := by
    intro j
    simp
  have h1 : (fun _ : EvenHoleDeformationClass ex7 => (1 : R)) = fun _ => ((1 : ℚ) : R) := by
    funext _
    simp
  have key := fun k P Q =>
    printed_pow_apply (fun _ : Fin 7 => (1 : R)) (fun _ => (1 : ℚ)) hb 1 hN k P Q
  rw [h1]
  refine ⟨fun k hk => ?_, ?_, ?_⟩
  · rw [key k, key k, pathEquiv_root, pathEquiv_exP, pathEquiv_exP']
    congr 1
    exact model_pow_eq_of_lt_six k hk
  · rw [key 6, pathEquiv_root, pathEquiv_exP, model_pow_six_unit.1]
    norm_num
  · rw [key 6, pathEquiv_root, pathEquiv_exP', model_pow_six_unit.2]
    norm_num

open Classical in
/-- **Counterexample to v1's Lemma `deformationclosurepathsrelation` with the printed
normalisation of Eq. (decoratedtree).**  `G` is claw-free, `K = {2, 5}` is a simplicial
clique, `P = (j*, 2, 0)` has `ℓ = 2`, and `P~ = (j*, 5, 0)` is a single-vertex deformation of
`P` (so `P~ ∈ ⟨P⟩`).  A printed normalisation exists, and for every one the printed matrix `A`
(unit couplings, `λ = 1`) has `(A^6)_{{j*},P} = 42 ≠ 40 = (A^6)_{{j*},P~}`, so the Lemma
fails for `A` (it holds for `k < 6`). -/
theorem printed_normalisation_counterexample :
    ex7.IsClawFree ∧ ex7.IsSimplicialClique exK ∧ 3 ≤ exP.path.card ∧
      InducedPathDeformationStep (ex7.adjoinRootAt exK) exP.path exP'.path ∧
      InInducedPathDeformationClosure (ex7.adjoinRootAt exK) exP.path exP'.path ∧
      (∃ N : CliqueRootedInducedPath ex7 exK → CliqueRootedInducedPath ex7 exK → ℚ,
        IsPrintedNormalisation ex7 exK N) ∧
      ∀ N : CliqueRootedInducedPath ex7 exK → CliqueRootedInducedPath ex7 exK → ℚ,
        IsPrintedNormalisation ex7 exK N →
        (printedHoppingMatrix ex7 exK (fun _ => (1 : ℚ)) (fun _ => (1 : ℚ)) N ^ 6)
            (cliqueRootPath ex7 exK) exP = 42 ∧
          (printedHoppingMatrix ex7 exK (fun _ => (1 : ℚ)) (fun _ => (1 : ℚ)) N ^ 6)
            (cliqueRootPath ex7 exK) exP' = 40 :=
  ⟨ex7_isClawFree, ex7_isSimplicialClique, by decide, exP'_deformationStep,
    exP'_deformationStep.inClosure, exists_isPrintedNormalisation,
    fun _ hN => (printed_pow_unit hN).2⟩

open Classical in
/-- On the same example, `paperLemma18` gives the balance of the rows of the corrected
matrix `cliqueHoppingMatrix` (every power, every field, every `b` and `λ`). -/
theorem corrected_balanced_of_paperLemma18 {R : Type w} [Field R] (b : Fin 7 → R)
    (lam : EvenHoleDeformationClass ex7 → R) (k : ℕ) :
    (cliqueHoppingMatrix ex7 exK b lam ^ k) (cliqueRootPath ex7 exK) exP =
      (cliqueHoppingMatrix ex7 exK b lam ^ k) (cliqueRootPath ex7 exK) exP' :=
  paperLemma18 ex7_isSimplicialClique ex7_isClawFree b lam (by decide)
    exP'_deformationStep.inClosure k

end Example

end PrintedNormalisation

end SimpleGraph
