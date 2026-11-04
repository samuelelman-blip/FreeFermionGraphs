import FreeFermionGraphs.T3FixedPairing
import FreeFermionGraphs.ClawFree

/-!
# A concrete palindromic fixed-pairing deformation with two blocks

Non-vacuity of `SimpleGraph.FPDeformation` (arXiv 2305.15625 v1, Definition 19, L978-994) and of
its palindromic condition (v1 L965-967): an explicit claw-free graph on seven vertices
`0 = v, 1 = k₁, 2 = b, 3 = b₂, 4 = j₀, 5 = j₁, 6 = y`, the 4-holes

* `C  = a₀ b₀ a₁ b₁ = v b k₁ b₂`, with classes `{v, k₁}` and `{b, b₂}`, and
* `C' = j₀ y j₁ v`, with classes `{j₀, j₁}` and `{y, v}`,

and the deformation `fpExD` with two blocks

* the side-1 block `j₀ - v - j₁ - k₁`, the whole of `G[{v, k₁} ⊕ {j₀, j₁}]`, with word
  `[(j₀, v), (j₁, k₁)]`, followed by
* the side-2 block `y - b - v - b₂`, the whole of `G[{b, b₂} ⊕ {y, v}]`, with word
  `[(y, b), (v, b₂)]`.

The vertex `v` lies in both blocks (v1 Corollary 8, L1053): it is removed from the first class of
`C` by the first block and introduced into the second class of `C'` by the second.  The
deformation is palindromic (`fpExD_palindromic`), odd (`fpExD_isOdd`), has toggle
`{1, 2, 3, 4, 5, 6}` (`fpExD_toggle`), and satisfies `C ⊕ T = C'` (`fpExD_carrier_fwdEnd`), whereas
the union formula `C ⊕ ∂O` fails because `v ∈ ∂O ∖ T` (`fpExD_union_formula_fails`).
-/

open scoped symmDiff

namespace SimpleGraph

/-! ### The graph -/

/-- The edges of the example graph on seven vertices
`0 = v, 1 = k₁, 2 = b, 3 = b₂, 4 = j₀, 5 = j₁, 6 = y`. -/
def fpExEdges : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (1, 2), (1, 3), (4, 0), (4, 2), (4, 3), (5, 1), (5, 2), (5, 3), (5, 0),
    (6, 2), (6, 4), (6, 5), (1, 6)]

/-- The example graph. -/
def fpExG : SimpleGraph (Fin 7) := SimpleGraph.fromRel fun a b => (a.val, b.val) ∈ fpExEdges

instance : DecidableRel fpExG.Adj := by
  unfold fpExG
  infer_instance

set_option synthInstance.maxSize 1000 in
theorem fpExG_clawFree : fpExG.IsClawFree := by
  have h : ∀ c a b d : Fin 7, fpExG.Adj c a → fpExG.Adj c b → fpExG.Adj c d → a ≠ b → a ≠ d →
      b ≠ d → fpExG.Adj a b ∨ fpExG.Adj a d ∨ fpExG.Adj b d := by decide
  exact fun c a b d => h c a b d

/-! ### The hole-class states -/

/-- A labelling of a four-hole `a₀ b₀ a₁ b₁` of the example graph from its two classes. -/
def fpExLabel (a b : Fin 2 → Fin 7) (hai : Function.Injective a) (hbi : Function.Injective b)
    (hd : ∀ i j, a i ≠ b j) (haa : ∀ i j, ¬ fpExG.Adj (a i) (a j))
    (hbb : ∀ i j, ¬ fpExG.Adj (b i) (b j)) (hab : ∀ i j, fpExG.Adj (a i) (b j)) :
    fpExG.EvenHoleLabeling 2 where
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

/-- The start state `C = a₀ b₀ a₁ b₁` with classes `{v, k₁}` and `{b, b₂}`. -/
def fpExS : Finset (Fin 7) × Finset (Fin 7) := ({0, 1}, {2, 3})

/-- The target state `C' = j₀ y j₁ v` with classes `{j₀, j₁}` and `{y, v}`. -/
def fpExS' : Finset (Fin 7) × Finset (Fin 7) := ({4, 5}, {6, 0})

theorem fpExS_isHoleClasses : fpExG.IsHoleClasses fpExS := by
  refine ⟨2, fpExLabel ![0, 1] ![2, 3] (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide), ?_, by decide, by decide⟩
  intro i n hn hk
  obtain rfl : n = 1 := by omega
  exact (fpExLabel ![0, 1] ![2, 3] (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).next_ne i

theorem fpExS'_isHoleClasses : fpExG.IsHoleClasses fpExS' := by
  refine ⟨2, fpExLabel ![4, 5] ![6, 0] (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide), ?_, by decide, by decide⟩
  intro i n hn hk
  obtain rfl : n = 1 := by omega
  exact (fpExLabel ![4, 5] ![6, 0] (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).next_ne i

/-! ### The blocks -/

section Generic

variable {V : Type*} {G : SimpleGraph V}

/-- The vertex set of an indexed induced path induces a connected subgraph. -/
theorem IndexedInducedPath.fpEx_connected_induce_range (P : G.IndexedInducedPath) :
    (G.induce (Set.range P.vertex)).Connected := by
  have key : ∀ n (hn : n < P.card), (G.induce (Set.range P.vertex)).Reachable
      ⟨P.vertex ⟨0, P.nonempty⟩, ⟨_, rfl⟩⟩ ⟨P.vertex ⟨n, hn⟩, ⟨_, rfl⟩⟩ := by
    intro n
    induction n with
    | zero => intro hn; exact Reachable.refl _
    | succ n ih =>
      intro hn
      refine (ih (by omega)).trans (Adj.reachable ?_)
      show G.Adj (P.vertex ⟨n, _⟩) (P.vertex ⟨n + 1, hn⟩)
      exact (P.adj_iff _ _).2 (Or.inl rfl)
  haveI : Nonempty (Set.range P.vertex) := ⟨⟨P.vertex ⟨0, P.nonempty⟩, ⟨_, rfl⟩⟩⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨_, i, rfl⟩ := x
  obtain ⟨_, j, rfl⟩ := y
  exact (key i.val i.isLt).symm.trans (key j.val j.isLt)

/-- If the vertex set of an indexed induced path is the whole set `U`, then it is a component of
`G[U]`. -/
theorem IndexedInducedPath.fpEx_isInducedComponent_of_range_eq (P : G.IndexedInducedPath) {U : Set V}
    (h : Set.range P.vertex = U) : G.IsInducedComponent U (Set.range P.vertex) :=
  ⟨h.le, P.fpEx_connected_induce_range, fun _ _ _ hy _ => h ▸ hy⟩

end Generic

/-- The side-1 path `j₀ - v - j₁ - k₁`. -/
def fpExPathP : fpExG.IndexedInducedPath where
  card := 4
  nonempty := by decide
  vertex := ![4, 0, 5, 1]
  injective := by decide
  adj_iff := by decide

/-- The side-2 path `y - b - v - b₂`. -/
def fpExPathQ : fpExG.IndexedInducedPath where
  card := 4
  nonempty := by decide
  vertex := ![6, 2, 0, 3]
  injective := by decide
  adj_iff := by decide

/-- The side-1 block, a block of `(C_a, C'_c) = ({v, k₁}, {j₀, j₁})` with word
`[(j₀, v), (j₁, k₁)]`. -/
def fpExBlockP : fpExG.OddBlock fpExS.1 fpExS'.1 where
  path := fpExPathP
  even_card := by decide
  mem_Y := by decide
  mem_X := by decide
  component := by
    refine fpExPathP.fpEx_isInducedComponent_of_range_eq ?_
    have h : Finset.univ.image fpExPathP.vertex = symmDiff fpExS.1 fpExS'.1 := by decide
    rw [← h, Finset.coe_image, Finset.coe_univ, Set.image_univ]

/-- The side-2 block, a block of `(C_b, C'_d) = ({b, b₂}, {y, v})` with word
`[(y, b), (v, b₂)]`.  It shares the vertex `v` with the side-1 block. -/
def fpExBlockQ : fpExG.OddBlock fpExS.2 fpExS'.2 where
  path := fpExPathQ
  even_card := by decide
  mem_Y := by decide
  mem_X := by decide
  component := by
    refine fpExPathQ.fpEx_isInducedComponent_of_range_eq ?_
    have h : Finset.univ.image fpExPathQ.vertex = symmDiff fpExS.2 fpExS'.2 := by decide
    rw [← h, Finset.coe_image, Finset.coe_univ, Set.image_univ]

/-! ### The runs -/

theorem fpEx_isCloneIn_coe_iff {X : Finset (Fin 7)} {j k : Fin 7} :
    fpExG.IsCloneIn (↑X : Set (Fin 7)) j k ↔
      j ∉ X ∧ k ∈ X ∧ ∀ v ∈ X, (fpExG.Adj j v ↔ v = k ∨ fpExG.Adj k v) := by
  simp [IsCloneIn]

/-- A `ClassStep.a` of the example, with the clone condition and the new class as decidable
side conditions. -/
theorem fpEx_stepA (A B A' : Finset (Fin 7)) (j k : Fin 7)
    (h : (j ∉ A ∪ B ∧ k ∈ A ∪ B ∧ ∀ v ∈ A ∪ B, (fpExG.Adj j v ↔ v = k ∨ fpExG.Adj k v)) ∧
      k ∈ A ∧ A' = insert j (A.erase k)) :
    fpExG.ClassStep (A, B) (j, k) (A', B) := by
  obtain ⟨hcl, hk, rfl⟩ := h
  exact ClassStep.a (fpEx_isCloneIn_coe_iff.2 hcl) hk

/-- A `ClassStep.b` of the example. -/
theorem fpEx_stepB (A B B' : Finset (Fin 7)) (j k : Fin 7)
    (h : (j ∉ A ∪ B ∧ k ∈ A ∪ B ∧ ∀ v ∈ A ∪ B, (fpExG.Adj j v ↔ v = k ∨ fpExG.Adj k v)) ∧
      k ∈ B ∧ B' = insert j (B.erase k)) :
    fpExG.ClassStep (A, B) (j, k) (A, B') := by
  obtain ⟨hcl, hk, rfl⟩ := h
  exact ClassStep.b (fpEx_isCloneIn_coe_iff.2 hcl) hk

/-- The forward run: `C = a₀ b₀ a₁ b₁` is deformed by `v ← j₀`, `k₁ ← j₁`, `b ← y`, `b₂ ← v` into
`C' = j₀ y j₁ v`. -/
theorem fpExRun : fpExG.ClassRun fpExS [(4, 0), (5, 1), (6, 2), (0, 3)] fpExS' := by
  unfold fpExS fpExS'
  refine ClassRun.cons (s' := ({4, 1}, {2, 3})) (fpEx_stepA _ _ _ _ _ (by decide)) ?_
  refine ClassRun.cons (s' := ({4, 5}, {2, 3})) (fpEx_stepA _ _ _ _ _ (by decide)) ?_
  refine ClassRun.cons (s' := ({4, 5}, {6, 3})) (fpEx_stepB _ _ _ _ _ (by decide)) ?_
  refine ClassRun.cons (s' := ({4, 5}, {6, 0})) (fpEx_stepB _ _ _ _ _ (by decide)) ?_
  exact ClassRun.nil _

/-! ### The deformation -/

/-- A fixed-pairing deformation with two blocks, from `C = a₀ b₀ a₁ b₁` to `C' = j₀ y j₁ v`:
the side-1 block `j₀ - v - j₁ - k₁` and then the side-2 block `y - b - v - b₂`.  The vertex `v`
lies in both blocks: the first removes it from `C_a`, the second introduces it into `C'_d`. -/
def fpExD : fpExG.FPDeformation fpExS fpExS' :=
  FPDeformation.cons (Sum.inl fpExBlockP) (FPDeformation.single (Sum.inr fpExBlockQ)) (by decide)

/-! ### Non-vacuity -/

theorem fpExD_blocks_length : fpExD.blocks.length = 2 := rfl

theorem fpExD_word : fpExD.word = [(4, 0), (5, 1), (6, 2), (0, 3)] := by
  decide

/-- The deformation is palindromic: the word runs forward from `C`, and (by reversibility of clone
steps) the reversed word runs from `C'`. -/
theorem fpExD_palindromic : fpExD.Palindromic := by
  have h := fpExRun
  rw [← fpExD_word] at h
  exact ⟨⟨_, h⟩, ⟨_, h.reverse fpExS_isHoleClasses⟩⟩

theorem fpExD_toggle₁ : fpExD.toggle₁ = {0, 1, 4, 5} := by decide

theorem fpExD_toggle₂ : fpExD.toggle₂ = {0, 2, 3, 6} := by decide

/-- The toggle `T = T₁ ⊕ T₂`: the shared vertex `v = 0` cancels. -/
theorem fpExD_toggle : fpExD.toggle = {1, 2, 3, 4, 5, 6} := by decide

theorem fpExD_fwdEnd : fpExD.fwdEnd = fpExS' := by decide

theorem fpExD_bwdEnd : fpExD.bwdEnd = fpExS := by decide

/-- The carrier of the forward end is `C ⊕ T` (`FPDeformation.carrier_fwdEnd`). -/
theorem fpExD_carrier_fwdEnd :
    fpExD.fwdEnd.1 ∪ fpExD.fwdEnd.2 = symmDiff (fpExS.1 ∪ fpExS.2) fpExD.toggle :=
  FPDeformation.carrier_fwdEnd fpExS_isHoleClasses fpExS'_isHoleClasses fpExD fpExD_palindromic

/-- The carrier of the backward end is `C' ⊕ T` (`FPDeformation.carrier_bwdEnd`). -/
theorem fpExD_carrier_bwdEnd :
    fpExD.bwdEnd.1 ∪ fpExD.bwdEnd.2 = symmDiff (fpExS'.1 ∪ fpExS'.2) fpExD.toggle :=
  FPDeformation.carrier_bwdEnd fpExS_isHoleClasses fpExS'_isHoleClasses fpExD fpExD_palindromic

/-- The vertex `v = 0` lies in both blocks, so it lies in the union `∂O` of the supports but not
in the toggle `T`.  Consequently the union formula `C ⊕ ∂O` (with `∂O` as in v1 L990) is not the
deformed hole: the deformed hole is `C ⊕ T = C'`, v1's `C^{(m)} = C ⊕ ⊕_r P^{(r)}` (Definition 19,
L986). -/
theorem fpExD_union_formula_fails :
    symmDiff (fpExS.1 ∪ fpExS.2) (fpExD.toggle₁ ∪ fpExD.toggle₂) ≠ fpExS'.1 ∪ fpExS'.2 := by
  decide

theorem fpExD_shared_vertex :
    (0 : Fin 7) ∈ fpExD.toggle₁ ∧ (0 : Fin 7) ∈ fpExD.toggle₂ ∧ (0 : Fin 7) ∉ fpExD.toggle := by
  decide

/-- The deformation is odd: `c(T, C) = 15`. -/
theorem fpExD_isOdd : fpExD.IsOdd := by
  unfold FPDeformation.IsOdd
  rw [crossCount_eq_card_filter, fpExD_toggle]
  unfold fpExS
  decide

/-- Non-vacuity: there is a claw-free graph with an odd palindromic fixed-pairing deformation of
one 4-hole by another, having two blocks. -/
theorem exists_palindromic_two_block_deformation :
    ∃ (G : SimpleGraph (Fin 7)) (_ : G.IsClawFree) (s s' : Finset (Fin 7) × Finset (Fin 7))
      (_ : G.IsHoleClasses s) (_ : G.IsHoleClasses s') (D : G.FPDeformation s s'),
      D.Palindromic ∧ D.blocks.length = 2 ∧ D.IsOdd :=
  ⟨fpExG, fpExG_clawFree, fpExS, fpExS', fpExS_isHoleClasses, fpExS'_isHoleClasses, fpExD,
    fpExD_palindromic, fpExD_blocks_length, fpExD_isOdd⟩

end SimpleGraph
