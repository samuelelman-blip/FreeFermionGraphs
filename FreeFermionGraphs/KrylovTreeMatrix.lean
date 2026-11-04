import FreeFermionGraphs.InducedPathFintype
import FreeFermionGraphs.PauliCliqueHamiltonian
import FreeFermionGraphs.BubbleWandHoop

/-!
# The root path and the clique tree matrix

This file supplies the starting point of the Krylov-subspace argument
(arXiv 2305.15625v1, Section "Krylov Subspaces", Theorem 3 on
L1328-1336 and Eq. (decoratedtree) on L1434-1445).

Let `G*` be `G` with a fresh vertex `j*` adjoined to a set `K`
(Definition 17, v1 L841-858; in Lean `G.adjoinRootAt K`, with `none` playing
`j*`).  The matrix `A` of Theorem 3 is indexed by the rooted induced paths of
`G*`, that is, by the vertices of the induced-path tree `I(K, G) = I(j*, G*)`.

* `cliqueRootPath G K` is the one-vertex path `{j*}`.  The initial operator
  of the Krylov recursion is `h_{{j*}} = χ` (Theorem 3: "`χ` is a simplicial
  mode corresponding to the vertex `j*`", and the base case `k = 0` of its
  proof, L1494-1498).
* `cliqueTreeMatrix G K b` is the tree part of Eq. (decoratedtree): the first
  two cases, namely weight `1` for a one-vertex extension `P → P + x` and
  weight `b_x ^ 2` for the contraction `P + x → P`, where `x` is the terminal
  vertex of the source.  (The printed case "`P = P \ {j}`" is read as
  `P' = P \ {j}` with `j` the terminal vertex of the source `P`, matching the
  repo's `EqE1WeightData.contractionWeight`.)
  The third case of Eq. (decoratedtree) concerns arcs that wrap around an even
  hole and is not part of this matrix.
* The parity of `|P|` is the bipartition that gives the phrase "directed
  bipartite graph" of Theorem 3 its literal meaning: every nonzero entry
  `T_{PQ}` joins paths whose cardinalities have opposite parity, so
  `(T^n)_{PQ} = 0` unless `n + |P| + |Q|` is even.  In particular
  `(T^n)_{j*,j*} = 0` for odd `n`.
* In the absence of even holes, the repo matrix `eqE1WeightedAdjacency`
  (whose extra bubble-wand arcs all point into even holes) coincides with
  `cliqueTreeMatrix` with `b = W.coupling`.  This is a bridge lemma only; its
  premise `hfree` is the paper's notion of hole, `IndexedInducedHole`.
  Note the known defect of `EvenHoopBubbleWandArc` (it omits arcs into the
  root handle) plays no role here, since for even-hole-free graphs there are
  no bubble-wand arcs at all.
-/

open scoped BigOperators

universe u v w

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V} {K : Set V}

/-! ### The root path `{j*}` -/

/-- The one-vertex rooted induced path `{j*}` of `G*`, the initial index of
the Krylov recursion (v1 Theorem 3, L1494-1498: `h_{{j*}} = χ`). -/
def cliqueRootPath (G : SimpleGraph V) (K : Set V) :
    CliqueRootedInducedPath G K where
  path :=
    { card := 1
      nonempty := Nat.one_pos
      vertex := fun _ => none
      injective := fun i j _ => Subsingleton.elim i j
      adj_iff := by
        intro i j
        have hi := i.isLt
        have hj := j.isLt
        constructor
        · intro h
          exact absurd h (G.adjoinRootAt K).irrefl
        · intro h
          omega }
  root_eq := rfl

@[simp]
theorem cliqueRootPath_card (G : SimpleGraph V) (K : Set V) :
    (cliqueRootPath G K).path.card = 1 :=
  rfl

@[simp]
theorem cliqueRootPath_vertex (G : SimpleGraph V) (K : Set V)
    (i : Fin (cliqueRootPath G K).path.card) :
    (cliqueRootPath G K).path.vertex i = none :=
  rfl

@[simp]
theorem RootedInducedPath.terminalVertex_cliqueRootPath
    (G : SimpleGraph V) (K : Set V) :
    (cliqueRootPath G K).terminalVertex = none :=
  rfl

/-- The root path is the unique clique-rooted induced path of cardinality
one: the only vertex of such a path is the root `j*`. -/
theorem RootedInducedPath.eq_cliqueRootPath_iff
    (P : CliqueRootedInducedPath G K) :
    P = cliqueRootPath G K ↔ P.path.card = 1 := by
  constructor
  · rintro rfl
    rfl
  · intro hcard
    have hvertex : ∀ i : Fin P.path.card, P.path.vertex i = none := by
      intro i
      have hi : i = ⟨0, P.path.nonempty⟩ :=
        Fin.ext (by have := i.isLt; omega)
      rw [hi]
      exact P.root_eq
    obtain ⟨path, root_eq⟩ := P
    have hpath : path = (cliqueRootPath G K).path := by
      apply IndexedInducedPath.ext_card_vertex hcard
      exact Function.hfunext (congrArg Fin hcard)
        (fun a _ _ => heq_of_eq (hvertex a))
    subst hpath
    rfl

/-- Base case of Theorem 3 (v1 L1494-1498): the operator of the root path
`{j*}` is the artificial root term `χ`. -/
theorem PauliCliqueHamiltonianRepresentation.pathOperator_cliqueRootPath
    {R : Type v} {A : Type w} [CommRing R] [Ring A] [Algebra R A]
    (H : G.PauliCliqueHamiltonianRepresentation K R A) :
    H.pathOperator (cliqueRootPath G K) = H.rootOperator := by
  simp [PauliCliqueHamiltonianRepresentation.pathOperator,
    PauliFrustrationRepresentation.pathOperator,
    PauliCliqueHamiltonianRepresentation.rootOperator,
    cliqueRootPath, PauliFrustrationRepresentation.listOperator]

/-! ### The tree matrix -/

/-- The tree part of Eq. (decoratedtree) (v1 L1434-1445) on the rooted
induced paths of `G*`: `T_{P,P+x} = 1` for a one-vertex extension and
`T_{P+x,P} = b_x ^ 2`, `x` the terminal vertex of the source `P + x`, and `0`
otherwise.  The even-hole (third) case of Eq. (decoratedtree) is not part of
this matrix; for graphs without even holes it never occurs
(`eqE1WeightedAdjacency_eq_cliqueTreeMatrix`). -/
noncomputable def cliqueTreeMatrix {R : Type w} [CommRing R]
    (G : SimpleGraph V) (K : Set V) (b : V → R) :
    Matrix (CliqueRootedInducedPath G K) (CliqueRootedInducedPath G K) R := by
  classical
  exact fun P Q => if P.IsOneVertexExtension Q then 1
    else if Q.IsOneVertexExtension P then
      P.terminalVertex.elim 0 (fun j => b j ^ 2) else 0

section TreeMatrix

variable {R : Type w} [CommRing R]

/-- A one-vertex extension has weight one. -/
@[simp]
theorem cliqueTreeMatrix_of_extension (b : V → R)
    {P Q : CliqueRootedInducedPath G K}
    (h : P.IsOneVertexExtension Q) :
    cliqueTreeMatrix G K b P Q = 1 := by
  classical
  simp [cliqueTreeMatrix, h]

/-- The contraction `P + x → P` has weight `b_x ^ 2`, where `x` is the
terminal vertex of the source. -/
theorem cliqueTreeMatrix_of_contraction (b : V → R)
    {P Q : CliqueRootedInducedPath G K}
    (h : Q.IsOneVertexExtension P) :
    cliqueTreeMatrix G K b P Q =
      P.terminalVertex.elim 0 (fun j => b j ^ 2) := by
  classical
  simp [cliqueTreeMatrix, h, h.not_reverse]

/-- The contraction weight when the terminal vertex of the source is the
original vertex `j`. -/
theorem cliqueTreeMatrix_of_contraction_at (b : V → R)
    {P Q : CliqueRootedInducedPath G K} {j : V}
    (h : Q.IsOneVertexExtension P)
    (hterminal : P.terminalVertex = some j) :
    cliqueTreeMatrix G K b P Q = b j ^ 2 := by
  rw [cliqueTreeMatrix_of_contraction b h, hterminal]
  rfl

/-- The tree matrix vanishes off the edges of the induced-path tree. -/
theorem cliqueTreeMatrix_eq_zero_of_not_treeAdjacent (b : V → R)
    {P Q : CliqueRootedInducedPath G K}
    (h : ¬P.TreeAdjacent Q) :
    cliqueTreeMatrix G K b P Q = 0 := by
  classical
  have h1 : ¬P.IsOneVertexExtension Q := fun h' => h (Or.inl h')
  have h2 : ¬Q.IsOneVertexExtension P := fun h' => h (Or.inr h')
  simp [cliqueTreeMatrix, h1, h2]

/-- A nonzero entry of the tree matrix joins two paths adjacent in the
induced-path tree. -/
theorem cliqueTreeMatrix_ne_zero_imp_treeAdjacent (b : V → R)
    {P Q : CliqueRootedInducedPath G K}
    (h : cliqueTreeMatrix G K b P Q ≠ 0) : P.TreeAdjacent Q := by
  by_contra hadj
  exact h (cliqueTreeMatrix_eq_zero_of_not_treeAdjacent b hadj)

/-- Every nonzero entry of the tree matrix joins paths whose cardinalities
have opposite parity: the parity of `|P|` is the bipartition of the directed
bipartite graph of Theorem 3. -/
theorem cliqueTreeMatrix_ne_zero_imp_odd (b : V → R)
    {P Q : CliqueRootedInducedPath G K}
    (h : cliqueTreeMatrix G K b P Q ≠ 0) :
    Odd (P.path.card + Q.path.card) := by
  rcases cliqueTreeMatrix_ne_zero_imp_treeAdjacent b h with ⟨hcard, _⟩ | ⟨hcard, _⟩
  · exact ⟨P.path.card, by omega⟩
  · exact ⟨Q.path.card, by omega⟩

/-- `T_{PQ} = 0` whenever `|P| + |Q|` is even. -/
theorem cliqueTreeMatrix_eq_zero_of_even (b : V → R)
    {P Q : CliqueRootedInducedPath G K}
    (h : Even (P.path.card + Q.path.card)) :
    cliqueTreeMatrix G K b P Q = 0 := by
  by_contra hne
  exact (Nat.not_even_iff_odd.mpr (cliqueTreeMatrix_ne_zero_imp_odd b hne)) h

/-- `(T^n)_{PQ} = 0` unless `n + |P| + |Q|` is even. -/
theorem cliqueTreeMatrix_pow_eq_zero_of_odd [Fintype V]
    [DecidableEq (CliqueRootedInducedPath G K)]
    (b : V → R) (n : ℕ) {P Q : CliqueRootedInducedPath G K}
    (h : Odd (n + P.path.card + Q.path.card)) :
    (cliqueTreeMatrix G K b ^ n) P Q = 0 := by
  induction n generalizing P with
  | zero =>
      have hne : P ≠ Q := by
        rintro rfl
        exact (Nat.not_even_iff_odd.mpr h) ⟨P.path.card, by omega⟩
      simp [hne]
  | succ n ih =>
      rw [pow_succ', Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro S _
      by_cases hPS : cliqueTreeMatrix G K b P S = 0
      · rw [hPS, zero_mul]
      · have hodd := cliqueTreeMatrix_ne_zero_imp_odd b hPS
        have hS : Odd (n + S.path.card + Q.path.card) := by
          obtain ⟨a, ha⟩ := hodd
          obtain ⟨c, hc⟩ := h
          exact ⟨c + a - P.path.card, by omega⟩
        rw [ih hS, mul_zero]

/-- `(T^n)_{j*,j*} = 0` for odd `n`. -/
theorem cliqueTreeMatrix_pow_cliqueRootPath_eq_zero_of_odd [Fintype V]
    [DecidableEq (CliqueRootedInducedPath G K)]
    (b : V → R) {n : ℕ} (hn : Odd n) :
    (cliqueTreeMatrix G K b ^ n) (cliqueRootPath G K) (cliqueRootPath G K) =
      0 := by
  apply cliqueTreeMatrix_pow_eq_zero_of_odd
  obtain ⟨m, hm⟩ := hn
  show Odd (n + 1 + 1)
  exact ⟨m + 1, by omega⟩

end TreeMatrix

/-! ### Bridge from the repo matrix Eq. (E1) -/

/-- A bubble-wand arc whose hoop is the carrier of an even-hole labeling
produces an indexed induced hole of even cardinality: the hoop of the bubble
wand is itself an indexed induced hole, and its cardinality is the size
`2k` of the labeling carrier. -/
theorem EvenHoopBubbleWandArc.exists_even_hole
    {P Q : CliqueRootedInducedPath G K}
    (h : EvenHoopBubbleWandArc G K P Q) :
    ∃ C : G.IndexedInducedHole, Even C.card := by
  obtain ⟨B, _, _, k, C, hC⟩ := h
  refine ⟨B.hoopHole, ?_⟩
  have hrange : (Set.range B.hoopHole.vertex).ncard = B.hoopHole.card := by
    rw [← Set.image_univ, Set.ncard_image_of_injective _ B.hoopHole.injective,
      Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hA : (Set.range C.a).ncard = k := by
    rw [← Set.image_univ, Set.ncard_image_of_injective _ C.a_injective,
      Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hB : (Set.range C.b).ncard = k := by
    rw [← Set.image_univ, Set.ncard_image_of_injective _ C.b_injective,
      Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hdisj : Disjoint (Set.range C.a) (Set.range C.b) := by
    rw [Set.disjoint_left]
    rintro _ ⟨i, rfl⟩ ⟨j, hj⟩
    exact C.color_disjoint i j hj.symm
  have hcarrier : C.carrier.ncard = k + k := by
    rw [EvenHoleLabeling.carrier,
      Set.ncard_union_eq hdisj (Set.finite_range _) (Set.finite_range _),
      hA, hB]
  have hcard : B.hoopHole.card = k + k := by
    rw [← hrange, B.range_hoopHole, ← hC, hcarrier]
  exact ⟨k, hcard⟩

/-- For a graph with no even hole, the repo matrix of Eq. (E1) is the tree
matrix with `b = W.coupling`: the bubble-wand branch of Eq. (E1) never fires.

This is a bridge lemma, not a statement of the manuscript; its premise
`hfree` (no `IndexedInducedHole` of even cardinality) is the paper's notion of
even-hole-freeness. -/
theorem eqE1WeightedAdjacency_eq_cliqueTreeMatrix
    {R : Type w} [Field R]
    (hfree : ∀ C : G.IndexedInducedHole, ¬ Even C.card)
    (W : EqE1WeightData G K R) :
    eqE1WeightedAdjacency G K W = cliqueTreeMatrix G K W.coupling := by
  classical
  funext P Q
  have hcontr : W.contractionWeight P =
      P.terminalVertex.elim 0 (fun j => W.coupling j ^ 2) := by
    unfold EqE1WeightData.contractionWeight
    cases P.terminalVertex <;> rfl
  have hnone : ¬EvenHoopBubbleWandArc G K P Q := by
    intro hbubble
    obtain ⟨C, hC⟩ := hbubble.exists_even_hole
    exact hfree C hC
  by_cases h1 : P.IsOneVertexExtension Q
  · rw [eqE1WeightedAdjacency_of_extension W h1,
      cliqueTreeMatrix_of_extension _ h1]
  · by_cases h2 : Q.IsOneVertexExtension P
    · rw [eqE1WeightedAdjacency_of_contraction W h2,
        cliqueTreeMatrix_of_contraction _ h2, hcontr]
    · simp [eqE1WeightedAdjacency, cliqueTreeMatrix, h1, h2, hnone]

end SimpleGraph
