import FreeFermionGraphs.ObstructionSearch

/-!
# Obstruction-graph pigeonhole and the corrective-step arithmetic

Definition 21 of the manuscript (arXiv 2305.15625 v1, `\label{definition:obstructiongraphcoloringclasses}`,
L1016) introduces the obstruction graph `𝒟 = (W, D)`.  It has odd order and is
bipartite with coloring classes given by the pairing types.  Its *source set* is
the larger class and its *obstruction set* is the smaller one.  The correctness
argument for the search process (v1 L1158 and L1190-1191) uses two purely
combinatorial facts about such a graph, which are isolated here.

* If every vertex has an outgoing arc, then because the order is odd the two
  classes differ in size, and by pigeonhole some vertex of the smaller class
  receives arcs from two distinct vertices of the larger class
  (`SimpleGraph.ArcGraph.exists_two_incoming`).  These are v1's "there must be at
  least one vertex `j''` in the obstruction set with at least two incoming arcs".
* Removing one vertex from each class (a source and the obstruction vertex `j''`
  of a rerouting step) preserves oddness of the order and keeps the source
  class strictly larger (`SimpleGraph.ArcGraph.odd_and_lt_after_removal`).  This
  is the invariant that makes the search process terminate (v1 L1190-1191).

The statements are generic in the vertex type and do not mention the obstruction
search itself; the odd order of the initial graph is the parity lemma
`|W|` odd that follows from `h_C` and `h_{C'}` anticommuting (v1 L1013).
-/

universe u

namespace SimpleGraph

namespace ArcGraph

variable {α : Type u} [Fintype α]

/-- The two pairing-type classes of a finite set partition it: their sizes add up
to the order. -/
theorem card_class_add_card_class
    (pairing : α → PairingType) (σ τ : PairingType) (hστ : τ = σ.opposite) :
    Fintype.card {z // pairing z = σ} +
        Fintype.card {z // pairing z = τ} = Fintype.card α := by
  classical
  simp only [Fintype.card_subtype]
  have hfilter :
      (Finset.univ.filter fun z => pairing z = τ) =
        Finset.univ.filter fun z => ¬ pairing z = σ := by
    apply Finset.filter_congr
    intro z _
    subst hστ
    cases σ <;> cases h : pairing z <;> simp [PairingType.opposite]
  rw [hfilter]
  exact Finset.card_filter_add_card_filter_not _ |>.trans (by simp)

/-- **Pigeonhole in the obstruction graph** (v1 Definition 21, L1016, with
L1158).  A finite directed graph of odd order that is bipartite by pairing
type and in which every node has an out-arc has two classes of different size,
and some node of the smaller class receives arcs from two distinct nodes of the
larger class. -/
theorem exists_two_incoming [DecidableEq α] (D : ArcGraph α)
    (pairing : α → PairingType) (hbip : D.IsBipartiteByPairing pairing)
    (hout : ∀ x, ∃ y, D.Arc x y) (hodd : Odd (Fintype.card α)) :
    ∃ σ : PairingType,
      Fintype.card {z // pairing z = σ.opposite} <
        Fintype.card {z // pairing z = σ} ∧
      ∃ x x' y : α, x ≠ x' ∧ pairing x = σ ∧ pairing x' = σ ∧
        D.Arc x y ∧ D.Arc x' y := by
  -- If the class of `σ` is strictly larger than that of its opposite, pigeonhole.
  have key : ∀ σ : PairingType,
      Fintype.card {z // pairing z = σ.opposite} <
        Fintype.card {z // pairing z = σ} →
      ∃ x x' y : α, x ≠ x' ∧ pairing x = σ ∧ pairing x' = σ ∧
        D.Arc x y ∧ D.Arc x' y := by
    intro σ hlt
    let f : {z // pairing z = σ} → {z // pairing z = σ.opposite} :=
      fun x => ⟨(hout x.1).choose, by
        exact (hbip (hout x.1).choose_spec).trans (by rw [x.2])⟩
    obtain ⟨x, x', hne, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f hlt
    refine ⟨x.1, x'.1, (hout x.1).choose, fun h => hne (Subtype.ext h),
      x.2, x'.2, (hout x.1).choose_spec, ?_⟩
    have hy : (hout x'.1).choose = (hout x.1).choose :=
      congrArg Subtype.val hf.symm
    rw [← hy]
    exact (hout x'.1).choose_spec
  have hac := card_class_add_card_class pairing PairingType.ac PairingType.ad rfl
  have had := card_class_add_card_class pairing PairingType.ad PairingType.ac rfl
  have hne : Fintype.card {z // pairing z = PairingType.ad} ≠
      Fintype.card {z // pairing z = PairingType.ac} := by
    intro h
    obtain ⟨k, hk⟩ := hodd
    omega
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact ⟨PairingType.ac, h, key PairingType.ac h⟩
  · exact ⟨PairingType.ad, h, key PairingType.ad h⟩

/-- **Corrective-step arithmetic** (v1 L1190-1191).  Removing one node from each
class of a bipartite graph of odd order, with the source class `n₁` strictly
larger than the obstruction class `n₂ > 0`, keeps the order odd and the source
class strictly larger. -/
theorem odd_and_lt_after_removal (n₁ n₂ : ℕ) (h : n₂ < n₁)
    (hodd : Odd (n₁ + n₂)) (h₂ : 0 < n₂) :
    Odd ((n₁ - 1) + (n₂ - 1)) ∧ n₂ - 1 < n₁ - 1 := by
  obtain ⟨k, hk⟩ := hodd
  refine ⟨⟨k - 1, ?_⟩, ?_⟩ <;> omega

end ArcGraph

end SimpleGraph
