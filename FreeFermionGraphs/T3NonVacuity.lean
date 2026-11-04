import FreeFermionGraphs.T3PalindromicToggles
import FreeFermionGraphs.T3FixedPairingExample

/-!
# Non-vacuity of the palindromic toggle set: a seven-vertex instance with a type-(b) lift

A concrete claw-free graph `graph7` on `Fin 7` for which the existence layer of the synthesised
proof of Theorem 1(iii) of the manuscript (arXiv 2305.15625 v1, "Palindromic Path Example",
L938-966) is inhabited: the set `K*(C, C')` (`SimpleGraph.palindromicToggles`) is not empty.  The
synthesised proof replaces the obstruction search of v1 (L1128-1172) by the existence argument of
packages T3-20 and T3-24, which has no counterpart in v1; this instance is the worked example of
that argument.

The module guards against vacuity of the definitions `SimpleGraph.IsHoleClasses`,
`SimpleGraph.pairingIndex`, `SimpleGraph.FPDeformation`, `FPDeformation.Palindromic`,
`FPDeformation.IsOdd` and `SimpleGraph.palindromicToggles`: the data below is built from explicit
`IndexedInducedPath`s and explicit `ClassStep`s, with no hypothesis that is supposed to be proved.

## The instance

The graph has the edges `01, 03, 04, 06, 12, 14, 15, 23, 25, 26, 34, 35, 36, 45, 56` (15 edges).
It is claw-free (`clawFree`).  The two 4-holes are

* `C  = (0, 1, 2, 3)` with classes `s  = ({1, 3}, {0, 2})`, and
* `C' = (0, 4, 5, 6)` with classes `s' = ({4, 6}, {0, 5})`

(`holeClasses`).  Their pairing index is `Ψ(s, s') = -1` (`pairingIndex_eq`), the source type of
v1 Definition 21 (L1016-1019), and `c(C', C) = 11` (`crossCount_carriers`), which has the parity of
`Ψ(s, s')` (`pairingIndex_emod_two`).  The set `W = {4, 5, 6}` (the vertices of `C' ∖ C` whose
term anticommutes with `h_C`) is the set of v1 Definition 20
(`definition:anticommutingdependentsubsets`, L997).  The set `W' = {1}` (the vertices of `C ∖ C'`
whose term anticommutes with `h_{C'}`) is the mirror set used by the synthesised route; it is not
defined in v1.  Neither set is formalised in this module.

The deformation `D` (`D`) has two blocks, in this order:

* the side-2 block `Q = 5 - 2`, a component of `G[{0, 2} ⊕ {0, 5}] = G[{2, 5}]`, with word
  `[(5, 2)]`: the introduced vertex `5 ∈ C'_d ∖ C_b` and the removed vertex `2 ∈ C_b ∖ C'_d`;
* the side-1 block `P = 6 - 3 - 4 - 1`, a component of `G[{1, 3} ⊕ {4, 6}] = G[{1, 3, 4, 6}]`,
  with word `[(6, 3), (4, 1)]`.

Its word is `[(5, 2), (6, 3), (4, 1)]` (`D_word`).  The forward run out of `s` is
`({1,3},{0,2}) → ({1,3},{0,5}) → ({1,6},{0,5}) → ({4,6},{0,5}) = s'` (`run`), and the reversed word
runs from `s'` back to `s` (`run_reverse`), so `D` is palindromic (`D_palindromic`).  The toggle is
`T = {1, …, 6}` (`D_toggle`), `c(T, C) = 15` is odd (`D_crossCount`, `D_isOdd`), and
`T ∈ K*(C, C')` (`toggles_mem`).

## Relation to the synthesised existence argument

The following describes how the instance sits in the synthesised argument (the good-candidate
cases of package T3-20 and the lift branches (a)/(b) of package T3-24).  These notions ("good
source", "case (i)", "branch (b)") have no counterpart in v1, where the corresponding step is the
obstruction search and rerouting (L1128-1172).  The side-2 block `Q = 5 - 2` is a good source.  At
the state `(s.1, s.2 ⊕ {2, 5}; s') = ({1,3},{0,5}; s')` the side-1 block `P` runs both ways, and
the lift of `Q` takes branch (b): `D` is `Q` followed by `P`.  (Package T3-24 states the lift for
a side-1 source, whereas here the source `Q` is a side-2 block, so the roles of the two sides are
interchanged.)  Branch (a), which would keep `P` alone, fails in this instance: `P` alone does not
run from `s`, since the step `(4, 1)` at `({1,6},{0,2})` fails because `4` is not adjacent to `2`.
The non-vacuity statements here only use the final object `D`, which is built directly from
explicit blocks and steps.  In this instance `C ⊕ T = C'` and `C' ⊕ T = C`, so the backward run of
`D` is the reverse of its forward run (`run_reverse`); the instance does not exercise a backward
run that is independent of the forward one.

The unqualified names of this module carry no premise beyond the instance itself.
-/

open scoped symmDiff

namespace SimpleGraph

namespace T3Example

/-! ### The graph -/

/-- The edges of the example graph, as pairs of natural numbers. -/
def edges : List (ℕ × ℕ) :=
  [(0, 1), (0, 3), (0, 4), (0, 6), (1, 2), (1, 4), (1, 5), (2, 3), (2, 5), (2, 6), (3, 4), (3, 5),
    (3, 6), (4, 5), (5, 6)]

/-- The seven-vertex example graph `graph7`, with the edges `01, 03, 04, 06, 12, 14, 15, 23, 25,
26, 34, 35, 36, 45, 56`. -/
def graph7 : SimpleGraph (Fin 7) :=
  SimpleGraph.fromRel fun x y => (x.val, y.val) ∈ edges

instance : DecidableRel graph7.Adj := by
  unfold graph7
  infer_instance

set_option synthInstance.maxSize 1000 in
/-- The example graph is claw-free. -/
theorem clawFree : graph7.IsClawFree := by
  have h : ∀ c a b d : Fin 7, graph7.Adj c a → graph7.Adj c b → graph7.Adj c d → a ≠ b → a ≠ d →
      b ≠ d → graph7.Adj a b ∨ graph7.Adj a d ∨ graph7.Adj b d := by decide
  exact fun c a b d => h c a b d

/-! ### The hole-class states -/

/-- A labelling of a 4-hole `a₀ b₀ a₁ b₁` of the example graph from its two colour classes. -/
def label (a b : Fin 2 → Fin 7) (hai : Function.Injective a) (hbi : Function.Injective b)
    (hd : ∀ i j, a i ≠ b j) (haa : ∀ i j, ¬ graph7.Adj (a i) (a j))
    (hbb : ∀ i j, ¬ graph7.Adj (b i) (b j)) (hab : ∀ i j, graph7.Adj (a i) (b j)) :
    graph7.EvenHoleLabeling 2 where
  two_le := le_rfl
  a := a
  b := b
  next := fun i => i + 1
  prev := fun i => i + 1
  next_ne := by decide
  next_next_ne := fun h => absurd h (by decide)
  next_prev := by decide
  prev_next := by decide
  a_injective := hai
  b_injective := hbi
  color_disjoint := hd
  adj_aa := haa
  adj_bb := hbb
  adj_ab_iff := fun i j => by
    have h : ∀ i j : Fin 2, j = i ∨ j = i + 1 := by decide
    exact ⟨fun _ => h i j, fun _ => hab i j⟩

/-- The start state: the 4-hole `C = (0, 1, 2, 3)` with colour classes `{1, 3}` and `{0, 2}`. -/
def s : Finset (Fin 7) × Finset (Fin 7) := ({1, 3}, {0, 2})

/-- The target state: the 4-hole `C' = (0, 4, 5, 6)` with colour classes `{4, 6}` and `{0, 5}`. -/
def s' : Finset (Fin 7) × Finset (Fin 7) := ({4, 6}, {0, 5})

theorem s_isHoleClasses : graph7.IsHoleClasses s := by
  refine ⟨2, label ![1, 3] ![0, 2] (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide), ?_, by decide, by decide⟩
  intro i n hn hk
  obtain rfl : n = 1 := by omega
  exact (label ![1, 3] ![0, 2] (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).next_ne i

theorem s'_isHoleClasses : graph7.IsHoleClasses s' := by
  refine ⟨2, label ![4, 6] ![0, 5] (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide), ?_, by decide, by decide⟩
  intro i n hn hk
  obtain rfl : n = 1 := by omega
  exact (label ![4, 6] ![0, 5] (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).next_ne i

/-- Both pairs of colour classes are hole classes (`IsHoleClasses`): `C = (0, 1, 2, 3)` with
classes `{1, 3}`, `{0, 2}` and `C' = (0, 4, 5, 6)` with classes `{4, 6}`, `{0, 5}`. -/
theorem holeClasses : graph7.IsHoleClasses s ∧ graph7.IsHoleClasses s' :=
  ⟨s_isHoleClasses, s'_isHoleClasses⟩

/-! ### The pairing index -/

/-- The pairing index is `Ψ(s, s') = -1`: the source type of v1 Definition 21 (L1016-1019). -/
theorem pairingIndex_eq : graph7.pairingIndex s s' = -1 := by
  rw [pairingIndex_eq_sum_sum]
  unfold classSign s s'
  decide +kernel

/-- The number of edges between the two carriers is `c(C', C) = 11`, odd like `Ψ(s, s') = -1`. -/
theorem crossCount_carriers : graph7.crossCount (s'.1 ∪ s'.2) (s.1 ∪ s.2) = 11 := by
  rw [crossCount_eq_card_filter]
  unfold s s'
  decide

/-! ### The blocks -/

/-- The side-1 path `6 - 3 - 4 - 1`. -/
def pathP : graph7.IndexedInducedPath where
  card := 4
  nonempty := by decide
  vertex := ![6, 3, 4, 1]
  injective := by decide
  adj_iff := by decide

/-- The side-2 path `5 - 2`. -/
def pathQ : graph7.IndexedInducedPath where
  card := 2
  nonempty := by decide
  vertex := ![5, 2]
  injective := by decide
  adj_iff := by decide

/-- The side-1 block, a block of `(C_a, C'_c) = ({1, 3}, {4, 6})` with word `[(6, 3), (4, 1)]`:
it is the whole of `G[{1, 3} ⊕ {4, 6}] = G[{1, 3, 4, 6}]`. -/
def blockP : graph7.OddBlock s.1 s'.1 where
  path := pathP
  even_card := by decide
  mem_Y := by decide
  mem_X := by decide
  component := by
    refine pathP.fpEx_isInducedComponent_of_range_eq ?_
    have h : Finset.univ.image pathP.vertex = symmDiff s.1 s'.1 := by decide
    rw [← h, Finset.coe_image, Finset.coe_univ, Set.image_univ]

/-- The side-2 block, a block of `(C_b, C'_d) = ({0, 2}, {0, 5})` with word `[(5, 2)]`: it is the
whole of `G[{0, 2} ⊕ {0, 5}] = G[{2, 5}]`. -/
def blockQ : graph7.OddBlock s.2 s'.2 where
  path := pathQ
  even_card := by decide
  mem_Y := by decide
  mem_X := by decide
  component := by
    refine pathQ.fpEx_isInducedComponent_of_range_eq ?_
    have h : Finset.univ.image pathQ.vertex = symmDiff s.2 s'.2 := by decide
    rw [← h, Finset.coe_image, Finset.coe_univ, Set.image_univ]

/-! ### The runs -/

theorem isCloneIn_coe_iff {X : Finset (Fin 7)} {j k : Fin 7} :
    graph7.IsCloneIn (↑X : Set (Fin 7)) j k ↔
      j ∉ X ∧ k ∈ X ∧ ∀ v ∈ X, (graph7.Adj j v ↔ v = k ∨ graph7.Adj k v) := by
  simp [IsCloneIn]

/-- A `ClassStep.a` of the example, with the clone condition and the new class as decidable
side conditions. -/
theorem stepA (A B A' : Finset (Fin 7)) (j k : Fin 7)
    (h : (j ∉ A ∪ B ∧ k ∈ A ∪ B ∧ ∀ v ∈ A ∪ B, (graph7.Adj j v ↔ v = k ∨ graph7.Adj k v)) ∧
      k ∈ A ∧ A' = insert j (A.erase k)) :
    graph7.ClassStep (A, B) (j, k) (A', B) := by
  obtain ⟨hcl, hk, rfl⟩ := h
  exact ClassStep.a (isCloneIn_coe_iff.2 hcl) hk

/-- A `ClassStep.b` of the example. -/
theorem stepB (A B B' : Finset (Fin 7)) (j k : Fin 7)
    (h : (j ∉ A ∪ B ∧ k ∈ A ∪ B ∧ ∀ v ∈ A ∪ B, (graph7.Adj j v ↔ v = k ∨ graph7.Adj k v)) ∧
      k ∈ B ∧ B' = insert j (B.erase k)) :
    graph7.ClassStep (A, B) (j, k) (A, B') := by
  obtain ⟨hcl, hk, rfl⟩ := h
  exact ClassStep.b (isCloneIn_coe_iff.2 hcl) hk

/-- The forward run: `({1,3},{0,2})` is deformed by `2 ← 5`, `3 ← 6`, `1 ← 4` into
`({4,6},{0,5})`. -/
theorem run : graph7.ClassRun s [(5, 2), (6, 3), (4, 1)] s' := by
  unfold s s'
  refine ClassRun.cons (s' := ({1, 3}, {0, 5})) (stepB _ _ _ _ _ (by decide)) ?_
  refine ClassRun.cons (s' := ({1, 6}, {0, 5})) (stepA _ _ _ _ _ (by decide)) ?_
  refine ClassRun.cons (s' := ({4, 6}, {0, 5})) (stepA _ _ _ _ _ (by decide)) ?_
  exact ClassRun.nil _

/-- The backward run: the reversed word `[(1, 4), (3, 6), (2, 5)]` runs from `({4,6},{0,5})` back
to `({1,3},{0,2})`. -/
theorem run_reverse : graph7.ClassRun s' (reverseWord [(5, 2), (6, 3), (4, 1)]) s :=
  run.reverse s_isHoleClasses

/-! ### The deformation -/

/-- The fixed-pairing-type deformation from `C = (0, 1, 2, 3)` to `C' = (0, 4, 5, 6)` with the two
blocks `Q = 5 - 2` (side 2) and `P = 6 - 3 - 4 - 1` (side 1), in this order.  It is the output of
branch (b) of the synthesised lift (package T3-24, which has no counterpart in v1: it replaces the
obstruction search of v1, L1128-1172), as described in the module documentation. -/
def D : graph7.FPDeformation s s' :=
  FPDeformation.cons (Sum.inr blockQ) (FPDeformation.single (Sum.inl blockP)) (by decide)

theorem D_blocks_length : D.blocks.length = 2 := rfl

theorem D_word : D.word = [(5, 2), (6, 3), (4, 1)] := by
  decide

/-- The deformation is palindromic: the word runs forward from `s` and the reversed word runs
from `s'`. -/
theorem D_palindromic : D.Palindromic := by
  have h := run
  rw [← D_word] at h
  exact ⟨⟨_, h⟩, ⟨_, run_reverse⟩⟩

theorem D_toggle₁ : D.toggle₁ = {1, 3, 4, 6} := by decide

theorem D_toggle₂ : D.toggle₂ = {2, 5} := by decide

/-- The toggle `T = T₁ ⊕ T₂ = {1, …, 6}`: the supports of the two blocks are disjoint. -/
theorem D_toggle : D.toggle = Finset.univ.erase 0 := by decide

/-- The number of edges between the toggle `T = {1, …, 6}` and the carrier `C = {0, 1, 2, 3}` is
`c(T, C) = 15`. -/
theorem D_crossCount : graph7.crossCount D.toggle (s.1 ∪ s.2) = 15 := by
  rw [crossCount_eq_card_filter, D_toggle]
  unfold s
  decide

/-- The deformation is odd: `c(T, C) = 15`. -/
theorem D_isOdd : D.IsOdd := by
  unfold FPDeformation.IsOdd
  rw [D_crossCount]
  decide

/-- Non-vacuity: the claw-free graph `graph7` has an odd palindromic fixed-pairing-type
deformation of the 4-hole `C = (0, 1, 2, 3)` by the 4-hole `C' = (0, 4, 5, 6)` with the word
`[(5, 2), (6, 3), (4, 1)]` and two blocks. -/
theorem exists_palindromic : ∃ D : graph7.FPDeformation s s', D.Palindromic ∧ D.IsOdd ∧
    D.word = [(5, 2), (6, 3), (4, 1)] ∧ D.blocks.length = 2 :=
  ⟨D, D_palindromic, D_isOdd, D_word, D_blocks_length⟩

/-- Non-vacuity of `K*(C, C')`: the toggle `{1, …, 6}` lies in `K*(C, C')` for `C = {0, 1, 2, 3}`
and `C' = {0, 4, 5, 6}`.  The proof uses `Ψ(s, s') = -1 < 0`. -/
theorem toggles_mem :
    (Finset.univ.erase 0 : Finset (Fin 7)) ∈
      graph7.palindromicToggles (↑(s.1 ∪ s.2) : Set (Fin 7)) (↑(s'.1 ∪ s'.2) : Set (Fin 7)) := by
  have h := FPDeformation.mem_palindromicToggles_of_palindromic s_isHoleClasses s'_isHoleClasses
    (by rw [pairingIndex_eq]; decide) D_palindromic D_isOdd
  rwa [D_toggle] at h

end T3Example

end SimpleGraph
