import FreeFermionGraphs.T3HoleClassRun
import FreeFermionGraphs.ChargePairInvolution
import FreeFermionGraphs.CliqueBubbleWand

/-!
# Oriented odd blocks of a side graph

This module formalises the paths `P^{(r)}` of a fixed-pairing-type deformation (arXiv 2305.15625
v1, Definition 19 `definition:fixedpairingtypedeformation`, L978-994) as *oriented* objects.

v1 takes each path `P^{(r)} = j_0^{(r)} k_0^{(r)} … j_{ℓ_r-1}^{(r)} k_{ℓ_r-1}^{(r)}` to be a
component of `G[C_j ⊕ C'_{σ(j)}]` which is an induced path of odd length, "labeled such that
`j_{s-1}^{(r)}` is in `C'_{σ(j)} ∖ C_j` and `k_{s-1}^{(r)}` is in `C_j ∖ C'_{σ(j)}`".  The labelling
is data (it is what makes the sequence `j_{s-1} ≺_{C^{(r,s-1)}} k_{s-1}` a deformation); the
repository's earlier encoding of the paths as bare sets of vertices forgets it.

For two vertex sets `X` (a colour class of `C`) and `Y` (a colour class of `C'`), an
`OddBlock X Y` is

* an `IndexedInducedPath` `p_0 … p_{2ℓ-1}` of even cardinality `2ℓ` (an induced path with an odd
  number `2ℓ - 1` of edges) whose even positions `p_{2i}` lie in `Y ∖ X` (the introduced vertices
  `j`) and whose odd positions `p_{2i+1}` lie in `X ∖ Y` (the removed vertices `k`),
* whose vertex set is a component of `G[X ⊕ Y]` (`IsInducedComponent`; the component property is a
  field, not a hypothesis).

(Here `X ⊕ Y = symmDiff X Y`.  With `X` and `Y` independent this is the situation of v1
Lemma 1, `lemma:clawfreesymmetricdifference`, L622: `G[X ⊕ Y]` is bipartite of maximum degree
two, so its components are paths and even holes; the block is a path component of odd length.)

## Main definitions and results

* `OddBlock.support`, `OddBlock.word`, `OddBlock.first`: the vertex set, the word
  `[(p_0, p_1), (p_2, p_3), …]` of `(introduced, removed)` pairs (the sequence
  `(j_{s-1}, k_{s-1})` of Definition 19, in the format of `ClassRun`), and the first vertex `p_0`.
* `OddBlock.RunsFrom P t`: the word of `P` is a clone run out of the hole-class state `t`.
* `OddBlock.IsSeparator`, `OddBlock.separators`: the vertices of a class `Z` which obstruct a step
  `(j, k)` of the word, i.e. `v = k` or `v` is adjacent to exactly one of `j`, `k`.
* (a) `OddBlock.eq_of_support_eq`, `OddBlock.word_eq_of_support_eq`: a block is determined by its
  support (the orientation is forced by the parity of the positions: the first vertex lies in
  `Y ∖ X`, the last in `X ∖ Y`).  Independence of `X` and `Y` is **not** needed (it is kept as an
  unused hypothesis of `word_eq_of_support_eq`, which is the form recorded in the work package).
* (b) `OddBlock.disjoint_of_support_ne`: blocks with distinct supports are disjoint (v1
  Corollaries 6-7, L1041-1049, read for components of one side graph: two distinct components of
  `G[X ⊕ Y]` are disjoint).
* (c) `OddBlock.reverse`, `reverse_word`, `reverse_support`: reversing the orientation gives an
  `OddBlock Y X` with word `reverseWord word` (the swapped, reversed word of
  `SimpleGraph.ClassRun.reverse`).
* (d) `OddBlock.ofToggle`, `ofToggle_word`: if `Q` is a component of `G[X ⊕ Y]`, a block of
  `(X ⊕ Q, Y)` is a block of `(X, Y)` with the same word.  (Toggling the closed component `Q`
  removes `Q` from `G[X ⊕ Y]` and nothing else changes.)
* (e) `OddBlock.retypeToggled`, `retypeToggled_word` (support `⊆ T`, orientation reversed, word
  `reverseWord word`) and `OddBlock.retypeUntoggled`, `retypeUntoggled_word` (support disjoint
  from `T`, same orientation and word): blocks of `(X ⊕ T, Y ⊕ T)`.  Since
  `(X ⊕ T) ⊕ (Y ⊕ T) = X ⊕ Y` the component property is preserved.

Claw-freeness is not used anywhere in this module.
-/

open scoped symmDiff

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- An *oriented odd block* of the side graph `G[X ⊕ Y]` (v1 Definition 19, L978-994): an induced
path `p_0 … p_{2ℓ-1}` of even cardinality whose even positions (the introduced vertices
`j_{s-1} ∈ C'_{σ(j)} ∖ C_j`) lie in `Y ∖ X` and whose odd positions (the removed vertices
`k_{s-1} ∈ C_j ∖ C'_{σ(j)}`) lie in `X ∖ Y`, and whose vertex set is a component of `G[X ⊕ Y]`. -/
@[ext]
structure OddBlock (G : SimpleGraph V) [DecidableEq V] (X Y : Finset V) where
  /-- The induced path `p_0 … p_{2ℓ-1}` with its vertex order. -/
  path : G.IndexedInducedPath
  /-- The path has an odd number of edges, i.e. an even number of vertices. -/
  even_card : Even path.card
  /-- Even positions hold the introduced vertices `j`, which lie in `Y ∖ X`. -/
  mem_Y : ∀ i : Fin path.card, Even i.val → path.vertex i ∈ Y \ X
  /-- Odd positions hold the removed vertices `k`, which lie in `X ∖ Y`. -/
  mem_X : ∀ i : Fin path.card, Odd i.val → path.vertex i ∈ X \ Y
  /-- The vertex set of the path is a component of `G[X ⊕ Y]`. -/
  component : G.IsInducedComponent ↑(symmDiff X Y) (Set.range path.vertex)

namespace OddBlock

variable [DecidableEq V] {X Y : Finset V}

/-! ### Derived data -/

/-- The vertex set of the block. -/
def support (P : G.OddBlock X Y) : Finset V := Finset.univ.image P.path.vertex

/-- The word of the block: the list of pairs `(p_{2i}, p_{2i+1})`, i.e. `(j_i, k_i)` with `j_i`
introduced and `k_i` removed (v1 Definition 19, L978-994). -/
def word (P : G.OddBlock X Y) : List (V × V) :=
  List.ofFn fun i : Fin (P.path.card / 2) =>
    (P.path.vertex ⟨2 * i.val, by have := i.isLt; omega⟩,
     P.path.vertex ⟨2 * i.val + 1, by
        have := i.isLt; have := P.even_card; obtain ⟨r, hr⟩ := this; omega⟩)

/-- The first vertex `p_0 = j_0` of the block (an endpoint of the path, in `Y ∖ X`). -/
def first (P : G.OddBlock X Y) : V := P.path.vertex ⟨0, P.path.nonempty⟩

/-- The block runs from the hole-class state `t` as one whole block: its word is a clone run
(`ClassRun`) out of `t`. -/
def RunsFrom (P : G.OddBlock X Y) (t : Finset V × Finset V) : Prop :=
  ∃ t', G.ClassRun t P.word t'

/-- The vertex `v` of the class `Z` *separates* a step of the block: `v` is the removed vertex `k`
of some step `(j, k)`, or `v` is different from `j, k` and adjacent to exactly one of them. -/
def IsSeparator (P : G.OddBlock X Y) (Z : Finset V) (v : V) : Prop :=
  v ∈ Z ∧ ∃ p ∈ P.word, v = p.2 ∨ (v ≠ p.1 ∧ v ≠ p.2 ∧ ¬(G.Adj p.1 v ↔ G.Adj p.2 v))

/-- The separators of the steps of `P` lying in the class `Z`. -/
noncomputable def separators (P : G.OddBlock X Y) (Z : Finset V) : Finset V := by
  classical
  exact Z.filter fun v =>
    ∃ p ∈ P.word, v = p.2 ∨ (v ≠ p.1 ∧ v ≠ p.2 ∧ ¬(G.Adj p.1 v ↔ G.Adj p.2 v))

/-! ### Basic API -/

theorem mem_support {P : G.OddBlock X Y} {v : V} :
    v ∈ P.support ↔ ∃ i, P.path.vertex i = v := by
  simp [support]

theorem coe_support (P : G.OddBlock X Y) :
    (↑P.support : Set V) = Set.range P.path.vertex := by
  ext v
  simp [support]

theorem vertex_mem_support (P : G.OddBlock X Y) (i : Fin P.path.card) :
    P.path.vertex i ∈ P.support :=
  mem_support.2 ⟨i, rfl⟩

theorem two_le_card (P : G.OddBlock X Y) : 2 ≤ P.path.card := by
  obtain ⟨r, hr⟩ := P.even_card
  have := P.path.nonempty
  omega

theorem card_support (P : G.OddBlock X Y) : P.support.card = P.path.card := by
  rw [support, Finset.card_image_of_injective _ P.path.injective, Finset.card_univ,
    Fintype.card_fin]

/-- The support is a component of `G[X ⊕ Y]`. -/
theorem isInducedComponent_support (P : G.OddBlock X Y) :
    G.IsInducedComponent ↑(symmDiff X Y) (↑P.support : Set V) := by
  rw [coe_support]
  exact P.component

theorem support_subset_symmDiff (P : G.OddBlock X Y) : P.support ⊆ symmDiff X Y := by
  intro v hv
  have := P.isInducedComponent_support.1 (Finset.mem_coe.2 hv)
  exact Finset.mem_coe.1 this

theorem mem_support_of_mem_Y {P : G.OddBlock X Y} {v : V} (hv : v ∈ P.support) :
    (v ∈ Y ∧ v ∉ X) ∨ (v ∈ X ∧ v ∉ Y) := by
  have := Finset.mem_symmDiff.1 (P.support_subset_symmDiff hv)
  tauto

theorem first_mem_Y (P : G.OddBlock X Y) : P.first ∈ Y \ X :=
  P.mem_Y ⟨0, P.path.nonempty⟩ (by simp)

theorem first_mem_support (P : G.OddBlock X Y) : P.first ∈ P.support :=
  P.vertex_mem_support _

theorem length_word (P : G.OddBlock X Y) : P.word.length = P.path.card / 2 := by
  simp [word]

theorem word_ne_nil (P : G.OddBlock X Y) : P.word ≠ [] := by
  intro h
  have := P.length_word
  rw [h] at this
  have := P.two_le_card
  simp only [List.length_nil] at *
  omega

/-- The entries of the word, by position. -/
theorem getElem_word (P : G.OddBlock X Y) (i : ℕ) (hi : i < P.word.length) :
    P.word[i] =
      (P.path.vertex ⟨2 * i, by rw [length_word] at hi; omega⟩,
        P.path.vertex ⟨2 * i + 1, by
          have := P.even_card; obtain ⟨r, hr⟩ := this; rw [length_word] at hi; omega⟩) := by
  simp [word]

theorem mem_word_iff (P : G.OddBlock X Y) {p : V × V} :
    p ∈ P.word ↔ ∃ (i : ℕ) (h : 2 * i + 1 < P.path.card),
      p = (P.path.vertex ⟨2 * i, by omega⟩, P.path.vertex ⟨2 * i + 1, h⟩) := by
  constructor
  · intro hp
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    have hlen := P.length_word
    have h2 : 2 * i + 1 < P.path.card := by
      have := P.even_card; obtain ⟨r, hr⟩ := this; omega
    exact ⟨i, h2, P.getElem_word i hi⟩
  · rintro ⟨i, h, rfl⟩
    have hi : i < P.word.length := by
      rw [length_word]; have := P.even_card; obtain ⟨r, hr⟩ := this; omega
    rw [← getElem_word P i hi]
    exact List.getElem_mem hi

/-- The introduced vertex `j` of a step lies in `Y ∖ X`. -/
theorem fst_mem {P : G.OddBlock X Y} {p : V × V} (hp : p ∈ P.word) : p.1 ∈ Y \ X := by
  obtain ⟨i, h, rfl⟩ := (mem_word_iff P).1 hp
  exact P.mem_Y _ ⟨i, by simp; omega⟩

/-- The removed vertex `k` of a step lies in `X ∖ Y`. -/
theorem snd_mem {P : G.OddBlock X Y} {p : V × V} (hp : p ∈ P.word) : p.2 ∈ X \ Y := by
  obtain ⟨i, h, rfl⟩ := (mem_word_iff P).1 hp
  exact P.mem_X _ ⟨i, by simp⟩

theorem fst_mem_support {P : G.OddBlock X Y} {p : V × V} (hp : p ∈ P.word) :
    p.1 ∈ P.support := by
  obtain ⟨i, h, rfl⟩ := (mem_word_iff P).1 hp
  exact P.vertex_mem_support _

theorem snd_mem_support {P : G.OddBlock X Y} {p : V × V} (hp : p ∈ P.word) :
    p.2 ∈ P.support := by
  obtain ⟨i, h, rfl⟩ := (mem_word_iff P).1 hp
  exact P.vertex_mem_support _

/-- The introduced and the removed vertex of a step are adjacent (consecutive on the path). -/
theorem adj_of_mem_word {P : G.OddBlock X Y} {p : V × V} (hp : p ∈ P.word) : G.Adj p.1 p.2 := by
  obtain ⟨i, h, rfl⟩ := (mem_word_iff P).1 hp
  exact (P.path.adj_iff _ _).2 (Or.inl rfl)

/-- Every vertex of the support is one of the two vertices of a step of the word. -/
theorem mem_support_iff_exists_mem_word {P : G.OddBlock X Y} {v : V} :
    v ∈ P.support ↔ ∃ p ∈ P.word, v = p.1 ∨ v = p.2 := by
  constructor
  · intro hv
    obtain ⟨i, rfl⟩ := mem_support.1 hv
    obtain ⟨r, hr⟩ := P.even_card
    have hi := i.isLt
    rcases Nat.even_or_odd' i.val with ⟨m, hm | hm⟩
    · refine ⟨_, (mem_word_iff P).2 ⟨m, by omega, rfl⟩, Or.inl ?_⟩
      exact congrArg P.path.vertex (Fin.ext (by simp [hm]))
    · refine ⟨_, (mem_word_iff P).2 ⟨m, by omega, rfl⟩, Or.inr ?_⟩
      exact congrArg P.path.vertex (Fin.ext (by simp [hm]))
  · rintro ⟨p, hp, rfl | rfl⟩
    · exact fst_mem_support hp
    · exact snd_mem_support hp

theorem mem_separators {P : G.OddBlock X Y} {Z : Finset V} {v : V} :
    v ∈ P.separators Z ↔ P.IsSeparator Z v := by
  classical
  simp [separators, IsSeparator]

theorem separators_subset (P : G.OddBlock X Y) (Z : Finset V) : P.separators Z ⊆ Z := fun _ hv =>
  (mem_separators.1 hv).1

/-! ### (c) Reversal -/

/-- The path of the block read backwards. -/
def reversePath (P : G.OddBlock X Y) : G.IndexedInducedPath where
  card := P.path.card
  nonempty := P.path.nonempty
  vertex := fun i => P.path.vertex i.rev
  injective := P.path.injective.comp Fin.rev_injective
  adj_iff := fun i j => by
    rw [P.path.adj_iff]
    have := i.isLt
    have := j.isLt
    simp only [Fin.val_rev]
    omega

@[simp]
theorem reversePath_card (P : G.OddBlock X Y) : P.reversePath.card = P.path.card := rfl

@[simp]
theorem reversePath_vertex (P : G.OddBlock X Y) (i : Fin P.path.card) :
    P.reversePath.vertex i = P.path.vertex i.rev := rfl

theorem range_reversePath (P : G.OddBlock X Y) :
    Set.range P.reversePath.vertex = Set.range P.path.vertex := by
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.rev, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.rev, by simp⟩

/-- Reversing the path exchanges the parity of the positions (the cardinality is even). -/
theorem even_rev_iff (P : G.OddBlock X Y) (i : Fin P.path.card) :
    Even i.rev.val ↔ Odd i.val := by
  have := P.even_card
  rw [Nat.even_iff] at this
  have := i.isLt
  rw [Nat.even_iff, Nat.odd_iff]
  simp only [Fin.val_rev]
  omega

theorem odd_rev_iff (P : G.OddBlock X Y) (i : Fin P.path.card) :
    Odd i.rev.val ↔ Even i.val := by
  have := P.even_card
  rw [Nat.even_iff] at this
  have := i.isLt
  rw [Nat.even_iff, Nat.odd_iff]
  simp only [Fin.val_rev]
  omega

/-- (c) Reversing the orientation of a block of `(X, Y)` gives a block of `(Y, X)` (the same path
read backwards: the vertices of `Y ∖ X` were at even positions and are now at odd positions, since
the cardinality is even). -/
def reverse (P : G.OddBlock X Y) : G.OddBlock Y X where
  path := P.reversePath
  even_card := P.even_card
  mem_Y := fun i hi => P.mem_X i.rev ((P.odd_rev_iff i).2 hi)
  mem_X := fun i hi => P.mem_Y i.rev ((P.even_rev_iff i).2 hi)
  component := by
    rw [symmDiff_comm, range_reversePath]
    exact P.component

@[simp]
theorem reverse_path (P : G.OddBlock X Y) : P.reverse.path = P.reversePath := rfl

/-- (c) The reverse block has the same support. -/
theorem reverse_support (P : G.OddBlock X Y) : P.reverse.support = P.support := by
  apply Finset.coe_injective
  rw [coe_support, coe_support, reverse_path, range_reversePath]

/-- (c) The word of the reverse block is `reverseWord` of the word: the reversed list of swapped
pairs (single-vertex deformations are reversible, v1 L686). -/
theorem reverse_word (P : G.OddBlock X Y) : P.reverse.word = reverseWord P.word := by
  apply List.ext_getElem
  · simp [length_word, reverseWord]
  · intro i h1 h2
    have hlen := P.length_word
    have hlen' : P.reverse.word.length = P.path.card / 2 := P.reverse.length_word
    obtain ⟨r, hr⟩ := P.even_card
    rw [P.reverse.getElem_word i h1]
    simp only [reverseWord, List.getElem_reverse, List.getElem_map, P.getElem_word,
      Prod.swap_prod_mk, reverse_path, reversePath_vertex]
    simp only [List.length_map, hlen]
    rw [hlen'] at h1
    refine Prod.ext ?_ ?_
    · refine congrArg P.path.vertex (Fin.ext ?_)
      simp only [Fin.val_rev]
      omega
    · refine congrArg P.path.vertex (Fin.ext ?_)
      simp only [Fin.val_rev]
      omega

theorem reverse_first (P : G.OddBlock X Y) :
    P.reverse.first = P.path.vertex ⟨P.path.card - 1, by have := P.path.nonempty; omega⟩ := by
  simp only [first, reverse_path, reversePath_vertex]
  exact congrArg P.path.vertex (Fin.ext (by simp))

@[simp]
theorem reverse_reverse (P : G.OddBlock X Y) : P.reverse.reverse = P := by
  apply OddBlock.ext
  refine IndexedInducedPath.ext_card_vertex rfl (heq_of_eq ?_)
  funext i
  simp [reverse]

/-! ### (a) A block is determined by its support -/

/-- The first vertex of a block is determined by its support: it is the endpoint of the induced
path lying in `Y ∖ X`.  (The other endpoint lies in `X ∖ Y`, since the cardinality is even.) -/
theorem first_eq_of_support_eq (P Q : G.OddBlock X Y) (h : P.support = Q.support) :
    Q.first = P.first := by
  have hrange : Set.range P.path.vertex = Set.range Q.path.vertex := by
    rw [← coe_support, ← coe_support, h]
  have hP2 := P.two_le_card
  have hQ2 := Q.two_le_card
  -- the neighbours of `Q.first` inside the common vertex set
  have hnb : ∀ w, w ∈ Set.range P.path.vertex → G.Adj w Q.first →
      w = Q.path.vertex ⟨1, by omega⟩ := by
    intro w hw hadj
    rw [hrange] at hw
    obtain ⟨m, rfl⟩ := hw
    have hm : m.val + 1 = 0 ∨ 0 + 1 = m.val := (Q.path.adj_iff m ⟨0, Q.path.nonempty⟩).1 hadj
    exact congrArg Q.path.vertex (Fin.ext (show m.val = 1 by omega))
  obtain ⟨i, hi⟩ : Q.first ∈ Set.range P.path.vertex := by
    rw [hrange]
    exact ⟨_, rfl⟩
  have hQmem := Q.first_mem_Y
  have hPmem := P.first_mem_Y
  obtain ⟨r, hr⟩ := P.even_card
  have hilt := i.isLt
  by_cases hi0 : i.val = 0
  · have : i = ⟨0, P.path.nonempty⟩ := Fin.ext hi0
    rw [← hi, this]
    rfl
  · exfalso
    by_cases hilast : i.val + 1 = P.path.card
    · -- the last vertex lies in `X ∖ Y`
      have hodd : Odd i.val := ⟨(r - 1), by omega⟩
      have := P.mem_X i hodd
      rw [hi] at this
      exact (Finset.mem_sdiff.1 this).2 (Finset.mem_sdiff.1 hQmem).1
    · -- an interior vertex has two distinct neighbours
      have h1 : P.path.vertex ⟨i.val - 1, by omega⟩ = Q.path.vertex ⟨1, by omega⟩ := by
        apply hnb
        · exact ⟨_, rfl⟩
        · rw [← hi]
          exact (P.path.adj_iff _ _).2 (Or.inl (by simp; omega))
      have h2 : P.path.vertex ⟨i.val + 1, by omega⟩ = Q.path.vertex ⟨1, by omega⟩ := by
        apply hnb
        · exact ⟨_, rfl⟩
        · rw [← hi]
          exact (P.path.adj_iff _ _).2 (Or.inr (by simp))
      have h3 := congrArg Fin.val (P.path.injective (h1.trans h2.symm))
      change i.val - 1 = i.val + 1 at h3
      omega

/-- (a) A block is determined by its support. -/
theorem eq_of_support_eq (P Q : G.OddBlock X Y) (h : P.support = Q.support) : P = Q := by
  apply OddBlock.ext
  apply IndexedInducedPath.eq_of_range_eq_of_first_eq
  · rw [← coe_support, ← coe_support, h]
  · exact (first_eq_of_support_eq P Q h).symm

/-- (a) For independent `X`, `Y` the word of a block is determined by its support.  In fact the
whole block, hence the word, is determined by the support without any independence assumption
(`eq_of_support_eq`); the hypotheses are kept to match the form recorded in the work package. -/
theorem word_eq_of_support_eq (_hX : G.IsIndepSet (↑X : Set V)) (_hY : G.IsIndepSet (↑Y : Set V))
    (P Q : G.OddBlock X Y) (h : P.support = Q.support) : P.word = Q.word := by
  rw [eq_of_support_eq P Q h]

/-! ### (b) Blocks with distinct supports are disjoint -/

/-- (b) Two blocks of `(X, Y)` with distinct supports are disjoint: their supports are distinct
components of `G[X ⊕ Y]` (v1 Corollaries 6-7, L1041-1049). -/
theorem disjoint_of_support_ne (P Q : G.OddBlock X Y) (h : P.support ≠ Q.support) :
    Disjoint P.support Q.support := by
  rw [← Finset.disjoint_coe]
  refine disjoint_of_isInducedComponent_of_ne P.isInducedComponent_support
    Q.isInducedComponent_support ?_
  intro hc
  exact h (Finset.coe_injective hc)

/-- Two blocks of `(X, Y)` are equal or disjoint. -/
theorem eq_or_disjoint (P Q : G.OddBlock X Y) : P = Q ∨ Disjoint P.support Q.support := by
  by_cases h : P.support = Q.support
  · exact Or.inl (eq_of_support_eq P Q h)
  · exact Or.inr (disjoint_of_support_ne P Q h)

/-! ### (d) Transport along a one-sided toggle by another component -/

/-- (d) Transport along a one-sided toggle.  If `Q` is a component of `G[X ⊕ Y]`, then toggling
`Q` in `X` removes `Q` from `G[X ⊕ Y]` and leaves every other component alone; so a block of
`(X ⊕ Q, Y)` is a block of `(X, Y)`, with the same path (hence the same word). -/
def ofToggle {Q : Finset V} (P : G.OddBlock (symmDiff X Q) Y) (hQ : Q ⊆ symmDiff X Y)
    (hQc : G.IsInducedComponent ↑(symmDiff X Y) ↑Q) : G.OddBlock X Y where
  path := P.path
  even_card := P.even_card
  mem_Y := fun i hi => by
    have h := P.mem_Y i hi
    have hq : P.path.vertex i ∈ Q → (P.path.vertex i ∈ X ∧ P.path.vertex i ∉ Y) ∨
        (P.path.vertex i ∈ Y ∧ P.path.vertex i ∉ X) := fun hv => Finset.mem_symmDiff.1 (hQ hv)
    simp only [Finset.mem_sdiff, Finset.mem_symmDiff] at h ⊢
    tauto
  mem_X := fun i hi => by
    have h := P.mem_X i hi
    have hq : P.path.vertex i ∈ Q → (P.path.vertex i ∈ X ∧ P.path.vertex i ∉ Y) ∨
        (P.path.vertex i ∈ Y ∧ P.path.vertex i ∉ X) := fun hv => Finset.mem_symmDiff.1 (hQ hv)
    simp only [Finset.mem_sdiff, Finset.mem_symmDiff] at h ⊢
    tauto
  component := by
    obtain ⟨hRU, hRc, hRcl⟩ := P.component
    have hU : (↑(symmDiff (symmDiff X Q) Y) : Set V) = ↑(symmDiff X Y) \ ↑Q := by
      ext v
      have hq : v ∈ Q → (v ∈ X ∧ v ∉ Y) ∨ (v ∈ Y ∧ v ∉ X) := fun hv =>
        Finset.mem_symmDiff.1 (hQ hv)
      simp only [Set.mem_sdiff, Finset.mem_coe, Finset.mem_symmDiff]
      tauto
    rw [hU] at hRU hRcl
    refine ⟨fun v hv => (hRU hv).1, hRc, ?_⟩
    intro x y hx hy hxy
    by_cases hyQ : y ∈ (↑Q : Set V)
    · exfalso
      exact (hRU hx).2 (hQc.2.2 hyQ ((hRU hx).1) hxy.symm)
    · exact hRcl hx ⟨hy, hyQ⟩ hxy

@[simp]
theorem ofToggle_path {Q : Finset V} (P : G.OddBlock (symmDiff X Q) Y) (hQ : Q ⊆ symmDiff X Y)
    (hQc : G.IsInducedComponent ↑(symmDiff X Y) ↑Q) : (P.ofToggle hQ hQc).path = P.path := rfl

/-- (d) The transported block has the same word. -/
theorem ofToggle_word {Q : Finset V} (P : G.OddBlock (symmDiff X Q) Y) (hQ : Q ⊆ symmDiff X Y)
    (hQc : G.IsInducedComponent ↑(symmDiff X Y) ↑Q) : (P.ofToggle hQ hQc).word = P.word := rfl

theorem ofToggle_support {Q : Finset V} (P : G.OddBlock (symmDiff X Q) Y)
    (hQ : Q ⊆ symmDiff X Y) (hQc : G.IsInducedComponent ↑(symmDiff X Y) ↑Q) :
    (P.ofToggle hQ hQc).support = P.support := rfl

theorem ofToggle_first {Q : Finset V} (P : G.OddBlock (symmDiff X Q) Y) (hQ : Q ⊆ symmDiff X Y)
    (hQc : G.IsInducedComponent ↑(symmDiff X Y) ↑Q) : (P.ofToggle hQ hQc).first = P.first := rfl

/-! ### (e) Retyping along a toggle -/

/-- The symmetric difference of the two toggled sets is unchanged. -/
theorem symmDiff_symmDiff_symmDiff_self (X Y T : Finset V) :
    symmDiff (symmDiff X T) (symmDiff Y T) = symmDiff X Y := by
  ext v
  simp only [Finset.mem_symmDiff]
  tauto

/-- (e) If the support of `P` lies in `T`, then toggling `T` in both `X` and `Y` exchanges the
two roles of every vertex of the block (a vertex of `Y ∖ X` in `T` lies in `X ⊕ T ∖ (Y ⊕ T)`), so
the reversed path is a block of `(X ⊕ T, Y ⊕ T)`.  The component property is kept because
`(X ⊕ T) ⊕ (Y ⊕ T) = X ⊕ Y`. -/
def retypeToggled {T : Finset V} (P : G.OddBlock X Y) (hT : P.support ⊆ T) :
    G.OddBlock (symmDiff X T) (symmDiff Y T) where
  path := P.reversePath
  even_card := P.even_card
  mem_Y := fun i hi => by
    have h := P.mem_X i.rev ((P.odd_rev_iff i).2 hi)
    have hT' : P.path.vertex i.rev ∈ T := hT (P.vertex_mem_support _)
    simp only [Finset.mem_sdiff, Finset.mem_symmDiff] at h ⊢
    simp only [reversePath_vertex]
    tauto
  mem_X := fun i hi => by
    have h := P.mem_Y i.rev ((P.even_rev_iff i).2 hi)
    have hT' : P.path.vertex i.rev ∈ T := hT (P.vertex_mem_support _)
    simp only [Finset.mem_sdiff, Finset.mem_symmDiff] at h ⊢
    simp only [reversePath_vertex]
    tauto
  component := by
    rw [symmDiff_symmDiff_symmDiff_self, range_reversePath]
    exact P.component

/-- (e) Retyping along a toggle containing the block reverses the word. -/
theorem retypeToggled_word {T : Finset V} (P : G.OddBlock X Y) (hT : P.support ⊆ T) :
    (P.retypeToggled hT).word = reverseWord P.word := P.reverse_word

theorem retypeToggled_support {T : Finset V} (P : G.OddBlock X Y) (hT : P.support ⊆ T) :
    (P.retypeToggled hT).support = P.support := P.reverse_support

/-- (e) If the support of `P` is disjoint from `T`, toggling `T` in both `X` and `Y` changes
nothing on the block: the same path is a block of `(X ⊕ T, Y ⊕ T)`. -/
def retypeUntoggled {T : Finset V} (P : G.OddBlock X Y) (hT : Disjoint P.support T) :
    G.OddBlock (symmDiff X T) (symmDiff Y T) where
  path := P.path
  even_card := P.even_card
  mem_Y := fun i hi => by
    have h := P.mem_Y i hi
    have hT' : P.path.vertex i ∉ T := Finset.disjoint_left.1 hT (P.vertex_mem_support _)
    simp only [Finset.mem_sdiff, Finset.mem_symmDiff] at h ⊢
    tauto
  mem_X := fun i hi => by
    have h := P.mem_X i hi
    have hT' : P.path.vertex i ∉ T := Finset.disjoint_left.1 hT (P.vertex_mem_support _)
    simp only [Finset.mem_sdiff, Finset.mem_symmDiff] at h ⊢
    tauto
  component := by
    rw [symmDiff_symmDiff_symmDiff_self]
    exact P.component

/-- (e) Retyping along a disjoint toggle keeps the word. -/
theorem retypeUntoggled_word {T : Finset V} (P : G.OddBlock X Y) (hT : Disjoint P.support T) :
    (P.retypeUntoggled hT).word = P.word := rfl

theorem retypeUntoggled_support {T : Finset V} (P : G.OddBlock X Y) (hT : Disjoint P.support T) :
    (P.retypeUntoggled hT).support = P.support := rfl

end OddBlock

end SimpleGraph
