import FreeFermionGraphs.EvenHoleOperators
import FreeFermionGraphs.GeneralizedCharacteristicPolynomialPairs
import FreeFermionGraphs.WeightedIndependencePolynomial

/-!
# Hole-only pairs over a fixed family of separated even holes

Manuscript reference: arXiv 2305.15625 v1, proof of Lemma 11
(`lemma:generalizedcharacteristicpolynomial`, statement L1266, proof L1928-1981), the passage
from Eq. (`setsymmetric`) (L1975-1976) to the form
`Z_G(-u²) = ∑_𝒳 (-u²)^{|∂𝒳|/2} 2^{|𝒳|} I_{G∖Γ[𝒳]}(-u²) ∏_{C ∈ 𝒳} h_C` (L1977).

Throughout, `G` is a finite graph and `W ⊆ V` a deleted carrier (`G ∖ W` is represented by
`G` together with `W`, as in `FreeFermionGraphs.WeightedIndependencePolynomial`).

## Definitions

* `SimpleGraph.evenHoleFamilies G W` : the families `𝒳 ∈ 𝒞^{(even)}_{G∖W}`: finite sets of
  even-hole carriers (`IsEvenHoleCarrier`) avoiding `W` that are pairwise separated in the
  *weak* sense of v1 L313 (`EvenHoleInducedCompatible`: `G[C ∪ C']` is the disjoint union of
  `G[C]` and `G[C']`).  The strong notion of v1 L748 (`EvenHoleCompatible`, disjoint closed
  neighbourhoods) is strictly stronger
  (`exists_evenHoleInducedCompatible_not_evenHoleCompatible`); using it here would drop the
  families whose holes are joined through a common neighbour, and Lemma 11 would fail.
* `SimpleGraph.familyBoundary G X` : `∂𝒳 = ⋃_{C ∈ 𝒳} C` (`G` is carried only so that the
  dot notation `G.familyBoundary X` can be used); `familyBoundaryFinset` is the same set as a
  `Finset`.
* `SimpleGraph.symmDiffHoleFamily G S T` : the vertex sets of the connected components of
  `G[S ⊕ T]`.
* `SimpleGraph.PauliFrustrationRepresentation.familyOperator H X` : `∏_{C ∈ 𝒳} h_C`, a
  `Finset.noncommProd` (the factors commute pairwise because the carriers are weakly
  separated, `evenHoleOperator_commute_of_inducedCompatible`); it is `1` for a family that is
  not pairwise separated.
* `SimpleGraph.twoColourings G D` : the proper two-colourings `(P, D ∖ P)` of `G[D]`,
  recorded by the colour class `P`.

## Main results

* `symmDiffHoleFamily_mem` : for a hole-only pair `(S, T)` avoiding `W` (every vertex of
  `S ⊕ T` has exactly two neighbours in `S ⊕ T`), the components of `G[S ⊕ T]` form a family
  `𝒳 ∈ 𝒞^{(even)}_{G∖W}` (v1 L1974: "a collection of disjoint and non-neighboring even
  holes").  Claw-freeness is not needed.
* `card_twoColourings_familyBoundaryFinset` : `G[∂𝒳]` has exactly `2^{|𝒳|}` proper
  two-colourings (v1's factor `2^{|𝒳|}`, one choice of colour class per hole).
* `familyOperator_eq_of_partition` : `h_P h_{∂𝒳 ∖ P} = ∏_{C ∈ 𝒳} h_C` for every such colouring.
* `sum_holeOnlyPairs_filter_symmDiff_eq` : the pairs `(S, T)` with `S ⊕ T = D` correspond to
  pairs (colouring `P` of `G[D]`, independent set `I` avoiding `W ∪ Γ[D]`) through
  `S = I ∪ P`, `T = I ∪ (D ∖ P)`.
* `PauliFrustrationRepresentation.sum_holeOnlyPairs_fibre_of_sq` and
  `PauliCliqueHamiltonianRepresentation.sum_holeOnlyPairs_fibre` : the fibre identity
  `∑_{(S,T) over 𝒳} (-u²)^{|S|} h_S h_T =
     (-u²)^{|∂𝒳|/2} 2^{|𝒳|} I_{G∖(W ∪ Γ[∂𝒳])}(-u²) ∏_{C∈𝒳} h_C`.

## Deviations from the manuscript and from the package statement

* The deleted graph `G ∖ (W ∪ Γ[∂𝒳])` is represented by the carrier
  `W ∪ ∂𝒳 ∪ openNeighborhood ∂𝒳` (`Γ[∂𝒳] = ∂𝒳 ∪ N(∂𝒳)`; in fact `∂𝒳 ⊆ N(∂𝒳)`, since every
  vertex of a hole has a neighbour in it).
* The separation relation is the repository's `EvenHoleInducedCompatible` (the notion of v1
  L313), the name used by `FreeFermionGraphs.EvenHoleOperators`.
* Neither `symmDiffHoleFamily_mem` nor the fibre identity needs claw-freeness (so, unlike the
  statement of the work package, they carry no `G.IsClawFree` hypothesis): claw-freeness enters
  the proof of Lemma 11 only through `holeOnlyPairs` being the set of surviving terms
  (`transfer_mul_transfer_neg_eq_holeOnly`).
* `familyBoundary` takes the graph as an explicit (unused) argument so that `G.familyBoundary X`
  parses, and `familyOperator` needs no `Fintype V`.
-/

open scoped symmDiff BigOperators

universe u w

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-! ### Definitions -/

/-- The families `𝒳 ∈ 𝒞^{(even)}_{G∖W}` of v1 (L313, with the weak compatibility of L313):
finite families of even-hole carriers avoiding `W` that are pairwise separated, i.e.
`G[C ∪ C']` is the disjoint union of `G[C]` and `G[C']` for distinct `C, C' ∈ 𝒳`
(`EvenHoleInducedCompatible`). -/
noncomputable def evenHoleFamilies (G : SimpleGraph V) [Fintype V] [DecidableEq V] (W : Set V) :
    Finset (Finset (Set V)) := by
  classical exact Finset.univ.filter fun X =>
    (∀ C ∈ X, G.IsEvenHoleCarrier C ∧ Disjoint C W) ∧
      (X : Set (Set V)).Pairwise G.EvenHoleInducedCompatible

/-- The empty family is always in `𝒞^{(even)}_{G∖W}` (it gives the term `S = T`, an
independent set, of `T(u) T(-u)`). -/
theorem empty_mem_evenHoleFamilies [Fintype V] [DecidableEq V] (W : Set V) :
    (∅ : Finset (Set V)) ∈ G.evenHoleFamilies W := by
  classical
  simp [evenHoleFamilies]

/-- Membership in `evenHoleFamilies`. -/
theorem mem_evenHoleFamilies [Fintype V] [DecidableEq V] {W : Set V} {X : Finset (Set V)} :
    X ∈ G.evenHoleFamilies W ↔
      (∀ C ∈ X, G.IsEvenHoleCarrier C ∧ Disjoint C W) ∧
        (X : Set (Set V)).Pairwise G.EvenHoleInducedCompatible := by
  classical
  simp [evenHoleFamilies]

/-- `∂𝒳 = ⋃_{C ∈ 𝒳} C`, the vertex set covered by a family of carriers (v1 L1977).  The graph
argument is unused; it is there so that `G.familyBoundary X` reads as in the manuscript. -/
def familyBoundary (_G : SimpleGraph V) (X : Finset (Set V)) : Set V := ⋃ C ∈ X, C

/-- Membership in `∂𝒳`. -/
theorem mem_familyBoundary {X : Finset (Set V)} {v : V} :
    v ∈ G.familyBoundary X ↔ ∃ C ∈ X, v ∈ C := by
  simp [familyBoundary]

/-- `∂𝒳` as a `Finset` (the ambient vertex type is finite). -/
noncomputable def familyBoundaryFinset (G : SimpleGraph V) [Fintype V] (X : Finset (Set V)) :
    Finset V := by
  classical exact Finset.univ.filter fun v => v ∈ G.familyBoundary X

/-- Membership in `familyBoundaryFinset`. -/
@[simp]
theorem mem_familyBoundaryFinset [Fintype V] {X : Finset (Set V)} {v : V} :
    v ∈ G.familyBoundaryFinset X ↔ ∃ C ∈ X, v ∈ C := by
  classical
  simp [familyBoundaryFinset, mem_familyBoundary]

/-- `familyBoundaryFinset` is `∂𝒳` as a finset. -/
theorem coe_familyBoundaryFinset [Fintype V] (X : Finset (Set V)) :
    (G.familyBoundaryFinset X : Set V) = G.familyBoundary X := by
  ext v
  simp [mem_familyBoundary]

/-- The cardinality of `∂𝒳` is the cardinality of its finset form. -/
theorem ncard_familyBoundary [Fintype V] (X : Finset (Set V)) :
    (G.familyBoundary X).ncard = (G.familyBoundaryFinset X).card := by
  rw [← coe_familyBoundaryFinset, Set.ncard_coe_finset]

/-- A carrier as a `Finset` (the ambient vertex type is finite). -/
noncomputable def holeCarrierFinset [Fintype V] (C : Set V) : Finset V := by
  classical exact Finset.univ.filter fun v => v ∈ C

/-- Membership in `holeCarrierFinset`. -/
@[simp]
theorem mem_holeCarrierFinset [Fintype V] {C : Set V} {v : V} :
    v ∈ holeCarrierFinset C ↔ v ∈ C := by
  classical
  simp [holeCarrierFinset]

/-- `holeCarrierFinset C` is `C` as a finset. -/
theorem coe_holeCarrierFinset [Fintype V] (C : Set V) : (holeCarrierFinset C : Set V) = C := by
  ext v
  simp

/-- The vertex sets of the connected components of `G[S ⊕ T]` (v1 L1974: "`G[S ⊕ T]` ... a
collection of disjoint and non-neighboring even holes"): for each `v ∈ S ⊕ T`, the set of
vertices reachable from `v` inside `G[S ⊕ T]` (`SimpleGraph.inducedComponentSet`). -/
noncomputable def symmDiffHoleFamily (G : SimpleGraph V) [DecidableEq V] (S T : Finset V) :
    Finset (Set V) := by
  classical exact (S ∆ T).image fun v => G.inducedComponentSet ((S ∆ T : Finset V) : Set V) v

/-- Membership in `symmDiffHoleFamily`. -/
theorem mem_symmDiffHoleFamily [DecidableEq V] {S T : Finset V} {C : Set V} :
    C ∈ G.symmDiffHoleFamily S T ↔
      ∃ v ∈ S ∆ T, G.inducedComponentSet ((S ∆ T : Finset V) : Set V) v = C := by
  classical
  simp [symmDiffHoleFamily]

/-- The proper two-colourings of `G[D]`: the sets `P ⊆ D` such that both `P` and `D ∖ P` are
independent in `G`.  (For `D = ∂𝒳` the number of these is `2^{|𝒳|}`, one choice of colour
class per hole.) -/
noncomputable def twoColourings (G : SimpleGraph V) [DecidableEq V] (D : Finset V) :
    Finset (Finset V) := by
  classical exact D.powerset.filter fun P =>
    G.IsIndepSet (P : Set V) ∧ G.IsIndepSet ((D \ P : Finset V) : Set V)

/-- Membership in `twoColourings`. -/
theorem mem_twoColourings [DecidableEq V] {D P : Finset V} :
    P ∈ G.twoColourings D ↔
      P ⊆ D ∧ G.IsIndepSet (P : Set V) ∧ G.IsIndepSet ((D \ P : Finset V) : Set V) := by
  classical
  simp [twoColourings]

/-! ### Independent unions and the colouring count -/

/-- The union of two independent finsets with no edge between them is independent. -/
theorem isIndepSet_union_of_no_edges [DecidableEq V] {A B : Finset V}
    (hA : G.IsIndepSet (A : Set V)) (hB : G.IsIndepSet (B : Set V))
    (h : ∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y) : G.IsIndepSet ((A ∪ B : Finset V) : Set V) := by
  intro x hx y hy hxy hadj
  rw [Finset.coe_union] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hA hx hy hxy hadj
  · exact h x hx y hy hadj
  · exact h y hy x hx hadj.symm
  · exact hB hx hy hxy hadj

/-- Proper two-colourings of a disjoint union without edges between the parts are the pairs of
two-colourings of the parts (`P ↦ (P ∩ D₁, P ∩ D₂)`); so their number is multiplicative. -/
theorem card_twoColourings_union [DecidableEq V] {D₁ D₂ : Finset V} (hd : Disjoint D₁ D₂)
    (hne : ∀ x ∈ D₁, ∀ y ∈ D₂, ¬ G.Adj x y) :
    (G.twoColourings (D₁ ∪ D₂)).card =
      (G.twoColourings D₁).card * (G.twoColourings D₂).card := by
  rw [← Finset.card_product]
  refine Finset.card_nbij' (fun P => (P ∩ D₁, P ∩ D₂)) (fun x => x.1 ∪ x.2) ?_ ?_ ?_ ?_
  · intro P hP
    rw [Finset.mem_coe, mem_twoColourings] at hP
    obtain ⟨hsub, hP1, hP2⟩ := hP
    rw [Finset.mem_coe, Finset.mem_product, mem_twoColourings, mem_twoColourings]
    refine ⟨⟨Finset.inter_subset_right, hP1.mono (by simp), ?_⟩,
      ⟨Finset.inter_subset_right, hP1.mono (by simp), ?_⟩⟩
    · refine hP2.mono ?_
      intro v hv
      simp only [Finset.coe_sdiff, Finset.coe_inter, Finset.coe_union, Set.mem_sdiff,
        Set.mem_inter_iff, Finset.mem_coe] at hv ⊢
      tauto
    · refine hP2.mono ?_
      intro v hv
      simp only [Finset.coe_sdiff, Finset.coe_inter, Finset.coe_union, Set.mem_sdiff,
        Set.mem_inter_iff, Finset.mem_coe] at hv ⊢
      tauto
  · rintro ⟨A, B⟩ hAB
    rw [Finset.mem_coe, Finset.mem_product, mem_twoColourings, mem_twoColourings] at hAB
    obtain ⟨⟨hA1, hA2, hA3⟩, ⟨hB1, hB2, hB3⟩⟩ := hAB
    dsimp only at hA1 hA2 hA3 hB1 hB2 hB3
    have hAB' : ∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y := fun x hx y hy => hne x (hA1 hx) y (hB1 hy)
    have hdiff : (D₁ ∪ D₂) \ (A ∪ B) = (D₁ \ A) ∪ (D₂ \ B) := by
      ext v
      simp only [Finset.mem_sdiff, Finset.mem_union]
      have h1 : v ∈ D₁ → v ∉ D₂ := fun h h' => Finset.disjoint_left.1 hd h h'
      have h2 : v ∈ A → v ∈ D₁ := fun h => hA1 h
      have h3 : v ∈ B → v ∈ D₂ := fun h => hB1 h
      have h4 : v ∈ A → v ∉ D₂ := fun h h' => h1 (h2 h) h'
      have h5 : v ∈ B → v ∉ D₁ := fun h h' => h1 h' (h3 h)
      tauto
    rw [Finset.mem_coe, mem_twoColourings]
    refine ⟨Finset.union_subset_union hA1 hB1, isIndepSet_union_of_no_edges hA2 hB2 hAB', ?_⟩
    rw [hdiff]
    exact isIndepSet_union_of_no_edges hA3 hB3
      (fun x hx y hy => hne x (Finset.mem_sdiff.1 hx).1 y (Finset.mem_sdiff.1 hy).1)
  · intro P hP
    rw [Finset.mem_coe, mem_twoColourings] at hP
    show (P ∩ D₁) ∪ (P ∩ D₂) = P
    rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.2 hP.1]
  · rintro ⟨A, B⟩ hAB
    rw [Finset.mem_coe, Finset.mem_product, mem_twoColourings, mem_twoColourings] at hAB
    obtain ⟨⟨hA1, -, -⟩, ⟨hB1, -, -⟩⟩ := hAB
    dsimp only at hA1 hB1
    have hAd : Disjoint A D₂ := Finset.disjoint_of_subset_left hA1 hd
    have hBd : Disjoint B D₁ := Finset.disjoint_of_subset_left hB1 hd.symm
    show ((A ∪ B) ∩ D₁, (A ∪ B) ∩ D₂) = (A, B)
    rw [Finset.union_inter_distrib_right, Finset.union_inter_distrib_right,
      Finset.inter_eq_left.2 hA1, Finset.inter_eq_left.2 hB1,
      Finset.disjoint_iff_inter_eq_empty.1 hBd, Finset.disjoint_iff_inter_eq_empty.1 hAd]
    simp

/-- An even hole has exactly two proper two-colourings: its two colour classes (a connected
bipartite graph has a unique bipartition up to swapping, `eq_or_swap_of_partition`). -/
theorem card_twoColourings_of_isEvenHoleCarrier [Fintype V] [DecidableEq V] {C : Set V}
    (hC : G.IsEvenHoleCarrier C) {E : Finset V} (hE : (E : Set V) = C) :
    (G.twoColourings E).card = 2 := by
  obtain ⟨k, L, -, rfl⟩ := hC.exists_fullCyclic_labeling
  set Ia : Finset V := Finset.univ.image L.a with hIa
  set Ib : Finset V := Finset.univ.image L.b with hIb
  have hIa_coe : (Ia : Set V) = Set.range L.a := by
    rw [hIa, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have hIb_coe : (Ib : Set V) = Set.range L.b := by
    rw [hIb, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have hEeq : E = Ia ∪ Ib := by
    apply Finset.coe_injective
    rw [hE, Finset.coe_union, hIa_coe, hIb_coe]
    rfl
  have hdisj : Disjoint Ia Ib := by
    rw [← Finset.disjoint_coe, hIa_coe, hIb_coe]
    exact L.disjoint_range_a_range_b
  have hne : Ia ≠ Ib := by
    intro h
    have hk := L.two_le
    have hmem : L.a ⟨0, by omega⟩ ∈ Ia := Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩
    exact Finset.disjoint_left.1 hdisj hmem (h ▸ hmem)
  have hset : G.twoColourings E = {Ia, Ib} := by
    ext P
    rw [mem_twoColourings, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hsub, hP, hQ⟩
      have hcov : (P : Set V) ∪ ((E \ P : Finset V) : Set V) = L.carrier := by
        rw [← hE, ← Finset.coe_union, Finset.union_sdiff_of_subset hsub]
      have hd : Disjoint (P : Set V) ((E \ P : Finset V) : Set V) := by
        rw [Finset.disjoint_coe]
        exact Finset.disjoint_sdiff
      rcases L.eq_or_swap_of_partition hC hcov hd hP hQ with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Or.inl (Finset.coe_injective (h1.trans hIa_coe.symm))
      · exact Or.inr (Finset.coe_injective (h1.trans hIb_coe.symm))
    · rintro (rfl | rfl)
      · refine ⟨by rw [hEeq]; exact Finset.subset_union_left, L.isIndepSet_image_a, ?_⟩
        have : E \ Ia = Ib := by
          rw [hEeq, Finset.union_sdiff_left, Finset.sdiff_eq_self_of_disjoint hdisj.symm]
        rw [this]
        exact L.isIndepSet_image_b
      · refine ⟨by rw [hEeq]; exact Finset.subset_union_right, L.isIndepSet_image_b, ?_⟩
        have : E \ Ib = Ia := by
          rw [hEeq, Finset.union_sdiff_right, Finset.sdiff_eq_self_of_disjoint hdisj]
        rw [this]
        exact L.isIndepSet_image_a
  rw [hset, Finset.card_pair hne]

/-- Two members of a pairwise separated family: the new carrier is disjoint from the rest of
the family and no edge joins them. -/
theorem disjoint_and_no_edges_familyBoundaryFinset [Fintype V] {C : Set V}
    {X : Finset (Set V)} (hC : C ∉ X)
    (h : ((insert C X : Finset (Set V)) : Set (Set V)).Pairwise G.EvenHoleInducedCompatible) :
    Disjoint (holeCarrierFinset C) (G.familyBoundaryFinset X) ∧
      ∀ x ∈ holeCarrierFinset C, ∀ y ∈ G.familyBoundaryFinset X, ¬ G.Adj x y := by
  have hcompat : ∀ y ∈ G.familyBoundaryFinset X,
      ∃ C' ∈ X, y ∈ C' ∧ G.EvenHoleInducedCompatible C C' := by
    intro y hy
    obtain ⟨C', hC'X, hyC'⟩ := mem_familyBoundaryFinset.1 hy
    have hne : C ≠ C' := fun h => hC (h ▸ hC'X)
    exact ⟨C', hC'X, hyC', h (Finset.mem_coe.2 (Finset.mem_insert_self _ _))
      (Finset.mem_coe.2 (Finset.mem_insert_of_mem hC'X)) hne⟩
  refine ⟨Finset.disjoint_left.2 fun y hyC hyX => ?_, fun x hx y hy hadj => ?_⟩
  · obtain ⟨C', -, hyC', hcomp⟩ := hcompat y hyX
    exact Set.disjoint_left.1 hcomp.1 (mem_holeCarrierFinset.1 hyC) hyC'
  · obtain ⟨C', -, hyC', hcomp⟩ := hcompat y hy
    exact hcomp.2 (mem_holeCarrierFinset.1 hx) hyC' hadj

/-- **The number of proper two-colourings of `G[∂𝒳]` is `2^{|𝒳|}`** (v1 L1977: the factor
`2^{|𝒳|}`, one choice of colour class `C_a` or `C_b` for each hole `C ∈ 𝒳`).  Induction on
`𝒳`, using that the new hole is separated from the previous ones
(`card_twoColourings_union`) and that a hole has two colourings. -/
theorem card_twoColourings_familyBoundaryFinset [Fintype V] [DecidableEq V]
    {X : Finset (Set V)} (hX1 : ∀ C ∈ X, G.IsEvenHoleCarrier C)
    (hX2 : (X : Set (Set V)).Pairwise G.EvenHoleInducedCompatible) :
    (G.twoColourings (G.familyBoundaryFinset X)).card = 2 ^ X.card := by
  induction X using Finset.induction_on with
  | empty =>
      have h0 : G.familyBoundaryFinset (∅ : Finset (Set V)) = ∅ := by
        ext v
        simp
      rw [h0]
      have : G.twoColourings (∅ : Finset V) = {∅} := by
        ext P
        rw [mem_twoColourings, Finset.mem_singleton]
        constructor
        · rintro ⟨h, -, -⟩
          exact Finset.subset_empty.1 h
        · rintro rfl
          refine ⟨Finset.Subset.refl _, ?_, ?_⟩ <;>
            · simp only [Finset.empty_sdiff, Finset.coe_empty]
              exact Set.pairwise_empty _
      rw [this]
      simp
  | insert C X hC ih =>
      have hC' : G.IsEvenHoleCarrier C := hX1 C (Finset.mem_insert_self _ _)
      have hX1' : ∀ C' ∈ X, G.IsEvenHoleCarrier C' := fun C' h =>
        hX1 C' (Finset.mem_insert_of_mem h)
      have hX2' : (X : Set (Set V)).Pairwise G.EvenHoleInducedCompatible :=
        hX2.mono (by simp)
      obtain ⟨hdisj, hne⟩ := disjoint_and_no_edges_familyBoundaryFinset hC hX2
      have hbd : G.familyBoundaryFinset (insert C X) =
          holeCarrierFinset C ∪ G.familyBoundaryFinset X := by
        ext v
        simp
      rw [hbd, card_twoColourings_union hdisj hne, ih hX1' hX2',
        card_twoColourings_of_isEvenHoleCarrier hC' (coe_holeCarrierFinset C),
        Finset.card_insert_of_notMem hC, pow_succ, mul_comm]

/-! ### The components of `G[S ⊕ T]` -/

/-- The neighbours of a vertex `x` of a component `C` of `G[U]` inside `C` are exactly its
neighbours inside `U` (a component is closed under adjacency inside `U`). -/
theorem neighborSet_inter_eq_coe_filter [DecidableRel G.Adj] {U : Finset V}
    {C : Set V} (hC : G.IsInducedComponent (U : Set V) C) {x : V} (hx : x ∈ C) :
    G.neighborSet x ∩ C = ((U.filter (G.Adj x) : Finset V) : Set V) := by
  ext y
  simp only [Set.mem_inter_iff, mem_neighborSet, Finset.coe_filter, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hadj, hyC⟩
    exact ⟨Finset.mem_coe.1 (hC.1 hyC), hadj⟩
  · rintro ⟨hyU, hadj⟩
    exact ⟨hadj, hC.2.2 hx (Finset.mem_coe.2 hyU) hadj⟩

section Components

variable [DecidableEq V]

/-- Every member of `symmDiffHoleFamily S T` is a nonempty component of `G[S ⊕ T]`. -/
theorem isInducedComponent_of_mem_symmDiffHoleFamily {S T : Finset V} {C : Set V}
    (hC : C ∈ G.symmDiffHoleFamily S T) :
    G.IsInducedComponent ((S ∆ T : Finset V) : Set V) C ∧ C.Nonempty := by
  obtain ⟨v, hv, rfl⟩ := mem_symmDiffHoleFamily.1 hC
  have hvU : v ∈ ((S ∆ T : Finset V) : Set V) := Finset.mem_coe.2 hv
  exact ⟨isInducedComponent_inducedComponentSet hvU, ⟨v, hvU, hvU, Reachable.refl _⟩⟩

/-- Conversely, every nonempty component of `G[S ⊕ T]` is a member of
`symmDiffHoleFamily S T`. -/
theorem mem_symmDiffHoleFamily_of_isInducedComponent {S T : Finset V} {C : Set V}
    (hC : G.IsInducedComponent ((S ∆ T : Finset V) : Set V) C) (hne : C.Nonempty) :
    C ∈ G.symmDiffHoleFamily S T := by
  obtain ⟨v, hv⟩ := hne
  have hvU := hC.1 hv
  refine mem_symmDiffHoleFamily.2 ⟨v, Finset.mem_coe.1 hvU, ?_⟩
  exact eq_of_isInducedComponent_of_mem (isInducedComponent_inducedComponentSet hvU) hC
    ⟨hvU, hvU, Reachable.refl _⟩ hv

/-- `symmDiffHoleFamily S T` is the set of nonempty components of `G[S ⊕ T]`. -/
theorem mem_symmDiffHoleFamily_iff {S T : Finset V} {C : Set V} :
    C ∈ G.symmDiffHoleFamily S T ↔
      G.IsInducedComponent ((S ∆ T : Finset V) : Set V) C ∧ C.Nonempty :=
  ⟨isInducedComponent_of_mem_symmDiffHoleFamily,
    fun h => mem_symmDiffHoleFamily_of_isInducedComponent h.1 h.2⟩

/-- The components of `G[S ⊕ T]` cover `S ⊕ T`: `∂(symmDiffHoleFamily S T) = S ⊕ T`. -/
theorem familyBoundary_symmDiffHoleFamily (S T : Finset V) :
    G.familyBoundary (G.symmDiffHoleFamily S T) = ((S ∆ T : Finset V) : Set V) := by
  ext v
  rw [mem_familyBoundary]
  constructor
  · rintro ⟨C, hC, hvC⟩
    exact (isInducedComponent_of_mem_symmDiffHoleFamily hC).1.1 hvC
  · intro hv
    have hvU : v ∈ ((S ∆ T : Finset V) : Set V) := hv
    exact ⟨G.inducedComponentSet ((S ∆ T : Finset V) : Set V) v,
      mem_symmDiffHoleFamily.2 ⟨v, Finset.mem_coe.1 hv, rfl⟩, hvU, hvU, Reachable.refl _⟩

/-- **The components of `G[S ⊕ T]` are even holes** (v1 L1974: for a pair of independent sets
such that every vertex of `S ⊕ T` has exactly two neighbours in `S ⊕ T`, "`G[S ⊕ T]` ... must
be a collection of disjoint and non-neighboring even holes").  A component is connected and
2-regular, hence a cycle (`isEvenHoleCarrier_of_connected_two_regular`); it is even because
its vertices alternate between `S ∖ T` and `T ∖ S`, and `|S| = |T|`. -/
theorem isEvenHoleCarrier_of_mem_symmDiffHoleFamily [Fintype V] [DecidableRel G.Adj]
    {S T : Finset V} (hS : G.IsIndepSet (S : Set V)) (hT : G.IsIndepSet (T : Set V))
    (h2 : ∀ v ∈ S ∆ T, ((S ∆ T).filter (G.Adj v)).card = 2) {C : Set V}
    (hC : C ∈ G.symmDiffHoleFamily S T) : G.IsEvenHoleCarrier C := by
  obtain ⟨hcomp, hCne⟩ := isInducedComponent_of_mem_symmDiffHoleFamily hC
  obtain ⟨hCU, hCconn, hCcl⟩ := hcomp
  have hreg : ∀ x ∈ C, (G.neighborSet x ∩ C).ncard = 2 := by
    intro x hx
    rw [neighborSet_inter_eq_coe_filter ⟨hCU, hCconn, hCcl⟩ hx, Set.ncard_coe_finset]
    exact h2 x (Finset.mem_coe.1 (hCU hx))
  set Cf : Finset V := holeCarrierFinset C with hCf
  have hCfU : ∀ v ∈ Cf, v ∈ S ∆ T := fun v hv => Finset.mem_coe.1 (hCU (mem_holeCarrierFinset.1 hv))
  have hcard : C.ncard = Cf.card := by
    conv_lhs => rw [← coe_holeCarrierFinset C]
    exact Set.ncard_coe_finset _
  have hfilter : ∀ v ∈ Cf, Cf.filter (G.Adj v) = (S ∆ T).filter (G.Adj v) := by
    intro v hv
    ext y
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hy, hadj⟩
      exact ⟨hCfU y hy, hadj⟩
    · rintro ⟨hy, hadj⟩
      exact ⟨mem_holeCarrierFinset.2 (hCcl (mem_holeCarrierFinset.1 hv) (Finset.mem_coe.2 hy) hadj),
        hadj⟩
  -- evenness
  have hsd : (S ∩ Cf) ∆ (T ∩ Cf) = Cf := by
    ext v
    simp only [Finset.mem_symmDiff, Finset.mem_inter]
    constructor
    · tauto
    · intro hv
      have := Finset.mem_symmDiff.1 (hCfU v hv)
      tauto
  have hbal : (S ∩ Cf).card = (T ∩ Cf).card := by
    refine card_eq_of_forall_card_filter_symmDiff_eq_two (G := G)
      (hS.mono (by simp)) (hT.mono (by simp)) ?_
    rw [hsd]
    intro v hv
    rw [hfilter v hv]
    exact h2 v (hCfU v hv)
  have hdisj : Disjoint (S ∩ Cf) (T ∩ Cf) := by
    rw [Finset.disjoint_left]
    intro v hvS hvT
    have := Finset.mem_symmDiff.1 (hCfU v (Finset.mem_inter.1 hvS).2)
    have h1 := (Finset.mem_inter.1 hvS).1
    have h2' := (Finset.mem_inter.1 hvT).1
    tauto
  have hunion : (S ∩ Cf) ∪ (T ∩ Cf) = Cf := by
    ext v
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · tauto
    · intro hv
      have := Finset.mem_symmDiff.1 (hCfU v hv)
      tauto
  have hCfcard : Cf.card = 2 * (S ∩ Cf).card := by
    have := Finset.card_union_of_disjoint hdisj
    rw [hunion] at this
    omega
  -- at least three vertices
  obtain ⟨x, hx⟩ := hCne
  have hx2 := h2 x (Finset.mem_coe.1 (hCU hx))
  have hsub : insert x ((S ∆ T).filter (G.Adj x)) ⊆ Cf := by
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact mem_holeCarrierFinset.2 hx
    · rw [Finset.mem_filter] at hy
      exact mem_holeCarrierFinset.2 (hCcl hx (Finset.mem_coe.2 hy.1) hy.2)
  have hxn : x ∉ (S ∆ T).filter (G.Adj x) := by
    simp
  have h3 : 3 ≤ Cf.card := by
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hxn, hx2] at this
    omega
  refine isEvenHoleCarrier_iff_connected_two_regular.2
    ⟨Set.toFinite C, ?_, ?_, hCconn, hreg⟩
  · rw [hcard, hCfcard]
    exact even_two_mul _
  · rw [hcard]
    omega

/-- **The component family of a hole-only pair lies in `𝒞^{(even)}_{G∖W}`** (v1 L1974-1977):
if `S`, `T` are independent sets avoiding `W` such that every vertex of `S ⊕ T` has exactly two
neighbours in `S ⊕ T`, then the vertex sets of the components of `G[S ⊕ T]` are even-hole
carriers avoiding `W` which are pairwise separated (disjoint and non-adjacent).

Claw-freeness is not needed here: it is only used to show that the surviving terms of
`T(u) T(-u)` are the hole-only pairs (`transfer_mul_transfer_neg_eq_holeOnly`). -/
theorem symmDiffHoleFamily_mem [Fintype V] {W : Set V} {p : Finset V × Finset V}
    (hp : p ∈ G.holeOnlyPairs W) : G.symmDiffHoleFamily p.1 p.2 ∈ G.evenHoleFamilies W := by
  classical
  obtain ⟨hS, hT, hSW, hTW, h2⟩ := mem_holeOnlyPairs.1 hp
  rw [mem_evenHoleFamilies]
  refine ⟨fun C hC => ⟨isEvenHoleCarrier_of_mem_symmDiffHoleFamily hS hT h2 hC, ?_⟩, ?_⟩
  · refine Set.disjoint_left.2 fun v hvC hvW => ?_
    have hv := (isInducedComponent_of_mem_symmDiffHoleFamily hC).1.1 hvC
    rcases Finset.mem_symmDiff.1 (Finset.mem_coe.1 hv) with ⟨h, -⟩ | ⟨h, -⟩
    · exact hSW v h hvW
    · exact hTW v h hvW
  · intro C hC C' hC' hne
    have hC1 := (isInducedComponent_of_mem_symmDiffHoleFamily (Finset.mem_coe.1 hC)).1
    have hC1' := (isInducedComponent_of_mem_symmDiffHoleFamily (Finset.mem_coe.1 hC')).1
    have hdisj : Disjoint C C' := disjoint_of_isInducedComponent_of_ne hC1 hC1' hne
    refine ⟨hdisj, fun x y hx hy hadj => ?_⟩
    exact Set.disjoint_left.1 hdisj (hC1.2.2 hx (hC1'.1 hy) hadj) hy

omit [DecidableEq V] in
/-- A member of a family of separated even holes is a component of `G[∂𝒳]`. -/
theorem isInducedComponent_of_mem_family [Fintype V] {X : Finset (Set V)}
    (hX1 : ∀ C ∈ X, G.IsEvenHoleCarrier C)
    (hX2 : (X : Set (Set V)).Pairwise G.EvenHoleInducedCompatible) {C : Set V} (hC : C ∈ X) :
    G.IsInducedComponent ((G.familyBoundaryFinset X : Finset V) : Set V) C := by
  refine ⟨fun v hv => Finset.mem_coe.2 (mem_familyBoundaryFinset.2 ⟨C, hC, hv⟩),
    (hX1 C hC).connected_induce, ?_⟩
  intro x y hx hy hxy
  obtain ⟨C', hC', hyC'⟩ := mem_familyBoundaryFinset.1 (Finset.mem_coe.1 hy)
  by_cases hCC : C = C'
  · exact hCC ▸ hyC'
  · exact absurd hxy ((hX2 (Finset.mem_coe.2 hC) (Finset.mem_coe.2 hC') hCC).2 hx hyC')

/-- **The components of `G[∂𝒳]` are the members of `𝒳`**: if `S ⊕ T = ∂𝒳` for a family `𝒳` of
separated even holes, then `symmDiffHoleFamily S T = 𝒳`. -/
theorem symmDiffHoleFamily_eq [Fintype V] {X : Finset (Set V)}
    (hX1 : ∀ C ∈ X, G.IsEvenHoleCarrier C)
    (hX2 : (X : Set (Set V)).Pairwise G.EvenHoleInducedCompatible) {S T : Finset V}
    (hST : S ∆ T = G.familyBoundaryFinset X) : G.symmDiffHoleFamily S T = X := by
  ext C
  rw [mem_symmDiffHoleFamily_iff, hST]
  constructor
  · rintro ⟨hCc, v, hv⟩
    have hvD := hCc.1 hv
    obtain ⟨C₀, hC₀, hvC₀⟩ := mem_familyBoundaryFinset.1 (Finset.mem_coe.1 hvD)
    have := eq_of_isInducedComponent_of_mem hCc (isInducedComponent_of_mem_family hX1 hX2 hC₀)
      hv hvC₀
    exact this ▸ hC₀
  · intro hC
    exact ⟨isInducedComponent_of_mem_family hX1 hX2 hC, (hX1 C hC).nonempty⟩

omit [DecidableEq V] in
/-- Every vertex of `∂𝒳` has exactly two neighbours in `∂𝒳` (the two neighbours inside its own
hole; separated holes are not adjacent). -/
theorem card_filter_adj_familyBoundaryFinset [Fintype V] [DecidableRel G.Adj]
    {X : Finset (Set V)} (hX1 : ∀ C ∈ X, G.IsEvenHoleCarrier C)
    (hX2 : (X : Set (Set V)).Pairwise G.EvenHoleInducedCompatible) {v : V}
    (hv : v ∈ G.familyBoundaryFinset X) :
    ((G.familyBoundaryFinset X).filter (G.Adj v)).card = 2 := by
  obtain ⟨C, hC, hvC⟩ := mem_familyBoundaryFinset.1 hv
  have h := neighborSet_inter_eq_coe_filter (isInducedComponent_of_mem_family hX1 hX2 hC) hvC
  rw [← Set.ncard_coe_finset, ← h]
  exact (hX1 C hC).ncard_neighborSet_inter hvC

end Components

/-! ### The operator `∏_{C ∈ 𝒳} h_C` -/

namespace PauliFrustrationRepresentation

variable {A : Type w} [Ring A]

/-- The operator `∏_{C ∈ 𝒳} h_C` attached to a family `𝒳` of even-hole carriers (v1 L1977).
For a pairwise separated family the factors `h_C` commute
(`evenHoleOperator_commute_of_inducedCompatible`), so this is a `Finset.noncommProd`; for a
family that is not pairwise separated it is the junk value `1`, which is never used (see
`familyOperator_of_pairwise`). -/
noncomputable def familyOperator [DecidableEq V] (H : G.PauliFrustrationRepresentation A)
    (X : Finset (Set V)) : A := by
  classical exact
    if h : (X : Set (Set V)).Pairwise G.EvenHoleInducedCompatible then
      Finset.noncommProd X H.evenHoleOperator (fun C hC C' hC' hne =>
        H.evenHoleOperator_commute_of_inducedCompatible (h hC hC' hne))
    else 1

/-- For a pairwise separated family, `familyOperator` is the noncommutative product of the
operators `h_C`. -/
theorem familyOperator_of_pairwise [DecidableEq V] (H : G.PauliFrustrationRepresentation A)
    {X : Finset (Set V)} (h : (X : Set (Set V)).Pairwise G.EvenHoleInducedCompatible) :
    H.familyOperator X =
      Finset.noncommProd X H.evenHoleOperator (fun _ hC _ hC' hne =>
        H.evenHoleOperator_commute_of_inducedCompatible (h hC hC' hne)) := by
  classical
  unfold familyOperator
  rw [dif_pos h]

/-- The empty family gives the identity. -/
theorem familyOperator_empty [DecidableEq V] (H : G.PauliFrustrationRepresentation A) :
    H.familyOperator (∅ : Finset (Set V)) = 1 := by
  rw [familyOperator_of_pairwise H (by simp)]
  simp

/-- Adding a new separated carrier multiplies by its operator `h_C` (on the left). -/
theorem familyOperator_insert [DecidableEq V] (H : G.PauliFrustrationRepresentation A)
    {C : Set V} {X : Finset (Set V)} (hC : C ∉ X)
    (h : ((insert C X : Finset (Set V)) : Set (Set V)).Pairwise G.EvenHoleInducedCompatible) :
    H.familyOperator (insert C X) = H.evenHoleOperator C * H.familyOperator X := by
  have hX : (X : Set (Set V)).Pairwise G.EvenHoleInducedCompatible := h.mono (by simp)
  rw [familyOperator_of_pairwise H h, familyOperator_of_pairwise H hX,
    Finset.noncommProd_insert_of_notMem _ _ _ _ hC]

/-- **`h_P h_{∂𝒳 ∖ P} = ∏_{C ∈ 𝒳} h_C`** for every proper two-colouring `(P, ∂𝒳 ∖ P)` of the
holes of a family `𝒳` of separated even holes (v1 L1977, "`h_{C_a} h_{C_b} = h_C`" for each hole,
the factors from different holes commuting).  More generally this holds for any disjoint pair of
independent sets `P`, `Q` with `P ∪ Q = ∂𝒳`.  Induction on `𝒳`: on the new hole `C`, `P ∩ C`
and `Q ∩ C` are the two colour classes (`evenHoleOperator_eq_of_colouring`), and the factors
supported on the other holes commute with those supported on `C` since no edge joins them. -/
theorem familyOperator_eq_of_partition [Fintype V] [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) {X : Finset (Set V)}
    (hX1 : ∀ C ∈ X, G.IsEvenHoleCarrier C)
    (hX2 : (X : Set (Set V)).Pairwise G.EvenHoleInducedCompatible) {P Q : Finset V}
    (hP : G.IsIndepSet (P : Set V)) (hQ : G.IsIndepSet (Q : Set V)) (hdisj : Disjoint P Q)
    (hcov : P ∪ Q = G.familyBoundaryFinset X) :
    H.independentProduct P * H.independentProduct Q = H.familyOperator X := by
  induction X using Finset.induction_on generalizing P Q with
  | empty =>
      have h0 : G.familyBoundaryFinset (∅ : Finset (Set V)) = ∅ := by
        ext v
        simp
      rw [h0, Finset.union_eq_empty] at hcov
      rw [hcov.1, hcov.2, H.independentProduct_empty, familyOperator_empty, one_mul]
  | insert C X hC ih =>
      have hC' : G.IsEvenHoleCarrier C := hX1 C (Finset.mem_insert_self _ _)
      have hX1' : ∀ C' ∈ X, G.IsEvenHoleCarrier C' := fun C' h =>
        hX1 C' (Finset.mem_insert_of_mem h)
      have hX2' : (X : Set (Set V)).Pairwise G.EvenHoleInducedCompatible :=
        hX2.mono (by simp)
      obtain ⟨hdisjCX, hneCX⟩ := disjoint_and_no_edges_familyBoundaryFinset hC hX2
      have hbd : G.familyBoundaryFinset (insert C X) =
          holeCarrierFinset C ∪ G.familyBoundaryFinset X := by
        ext v
        simp
      rw [hbd] at hcov
      -- splitting `P` and `Q` along `C` and the other holes
      have hPsplit : P = (P ∩ holeCarrierFinset C) ∪ (P ∩ G.familyBoundaryFinset X) := by
        rw [← Finset.inter_union_distrib_left, ← hcov,
          Finset.inter_eq_left.2 Finset.subset_union_left]
      have hQsplit : Q = (Q ∩ holeCarrierFinset C) ∪ (Q ∩ G.familyBoundaryFinset X) := by
        rw [← Finset.inter_union_distrib_left, ← hcov,
          Finset.inter_eq_left.2 Finset.subset_union_right]
      have hdP : Disjoint (P ∩ holeCarrierFinset C) (P ∩ G.familyBoundaryFinset X) :=
        Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right hdisjCX
      have hdQ : Disjoint (Q ∩ holeCarrierFinset C) (Q ∩ G.familyBoundaryFinset X) :=
        Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right hdisjCX
      have hhP : H.independentProduct P =
          H.independentProduct (P ∩ holeCarrierFinset C) *
            H.independentProduct (P ∩ G.familyBoundaryFinset X) := by
        have := H.independentProduct_union hdP (by rw [← hPsplit]; exact hP)
        rwa [← hPsplit] at this
      have hhQ : H.independentProduct Q =
          H.independentProduct (Q ∩ holeCarrierFinset C) *
            H.independentProduct (Q ∩ G.familyBoundaryFinset X) := by
        have := H.independentProduct_union hdQ (by rw [← hQsplit]; exact hQ)
        rwa [← hQsplit] at this
      -- the colour classes on `C`
      have hcovC : ((P ∩ holeCarrierFinset C : Finset V) : Set V) ∪
          ((Q ∩ holeCarrierFinset C : Finset V) : Set V) = C := by
        ext v
        simp only [Finset.coe_inter, Set.mem_union, Set.mem_inter_iff, Finset.mem_coe,
          mem_holeCarrierFinset]
        constructor
        · tauto
        · intro hv
          have hv' : v ∈ P ∪ Q := by
            rw [hcov]
            exact Finset.mem_union_left _ (mem_holeCarrierFinset.2 hv)
          rcases Finset.mem_union.1 hv' with h | h
          · exact Or.inl ⟨h, hv⟩
          · exact Or.inr ⟨h, hv⟩
      have hdisjC : Disjoint (P ∩ holeCarrierFinset C) (Q ∩ holeCarrierFinset C) :=
        Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left hdisj
      have hcolour := H.evenHoleOperator_eq_of_colouring hC' hcovC hdisjC
        (hP.mono (by simp)) (hQ.mono (by simp))
      -- the rest of the family
      have hcovX : (P ∩ G.familyBoundaryFinset X) ∪ (Q ∩ G.familyBoundaryFinset X) =
          G.familyBoundaryFinset X := by
        ext v
        simp only [Finset.mem_union, Finset.mem_inter]
        constructor
        · tauto
        · intro hv
          have hv' : v ∈ P ∪ Q := by
            rw [hcov]
            exact Finset.mem_union_right _ hv
          rcases Finset.mem_union.1 hv' with h | h
          · exact Or.inl ⟨h, hv⟩
          · exact Or.inr ⟨h, hv⟩
      have hIH := ih hX1' hX2' (hP.mono (by simp)) (hQ.mono (by simp))
        (Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left hdisj) hcovX
      have hcomm : Commute (H.independentProduct (P ∩ G.familyBoundaryFinset X))
          (H.independentProduct (Q ∩ holeCarrierFinset C)) :=
        H.independentProduct_commute_of_no_edges (hP.mono (by simp)) (hQ.mono (by simp))
          fun x hx y hy => fun hadj =>
            hneCX y (Finset.mem_inter.1 hy).2 x (Finset.mem_inter.1 hx).2 hadj.symm
      calc H.independentProduct P * H.independentProduct Q
          = (H.independentProduct (P ∩ holeCarrierFinset C) *
              H.independentProduct (P ∩ G.familyBoundaryFinset X)) *
            (H.independentProduct (Q ∩ holeCarrierFinset C) *
              H.independentProduct (Q ∩ G.familyBoundaryFinset X)) := by
            rw [← hhP, ← hhQ]
        _ = H.independentProduct (P ∩ holeCarrierFinset C) *
              (H.independentProduct (P ∩ G.familyBoundaryFinset X) *
                H.independentProduct (Q ∩ holeCarrierFinset C)) *
              H.independentProduct (Q ∩ G.familyBoundaryFinset X) := by
            simp only [mul_assoc]
        _ = H.independentProduct (P ∩ holeCarrierFinset C) *
              (H.independentProduct (Q ∩ holeCarrierFinset C) *
                H.independentProduct (P ∩ G.familyBoundaryFinset X)) *
              H.independentProduct (Q ∩ G.familyBoundaryFinset X) := by
            rw [hcomm.eq]
        _ = (H.independentProduct (P ∩ holeCarrierFinset C) *
              H.independentProduct (Q ∩ holeCarrierFinset C)) *
            (H.independentProduct (P ∩ G.familyBoundaryFinset X) *
              H.independentProduct (Q ∩ G.familyBoundaryFinset X)) := by
            simp only [mul_assoc]
        _ = H.evenHoleOperator C * H.familyOperator X := by
            rw [← hcolour.1, hIH]
        _ = H.familyOperator (insert C X) := (familyOperator_insert H hC hX2).symm

end PauliFrustrationRepresentation

/-! ### The fibre over a fixed boundary `D = S ⊕ T` -/

/-- The independent sets of `G ∖ (W ∪ Γ[D])`, `Γ[D] = D ∪ N(D)`: independent sets avoiding `W`
and `D` with no edge to `D`. -/
theorem mem_independentFinsetsAvoid_union_openNeighborhood [Fintype V] [DecidableEq V]
    {W : Set V} {D I : Finset V} :
    I ∈ G.independentFinsetsAvoid (W ∪ (D : Set V) ∪ G.openNeighborhood (D : Set V)) ↔
      G.IsIndepSet (I : Set V) ∧ (∀ v ∈ I, v ∉ W) ∧ (∀ v ∈ I, v ∉ D) ∧
        ∀ v ∈ I, ∀ w ∈ D, ¬ G.Adj v w := by
  rw [mem_independentFinsetsAvoid]
  constructor
  · rintro ⟨hI, hIW⟩
    exact ⟨hI, fun v hv hvW => hIW v hv (Or.inl (Or.inl hvW)),
      fun v hv hvD => hIW v hv (Or.inl (Or.inr (Finset.mem_coe.2 hvD))),
      fun v hv w hw hadj => hIW v hv (Or.inr ⟨w, Finset.mem_coe.2 hw, hadj⟩)⟩
  · rintro ⟨hI, hIW, hID, hIadj⟩
    refine ⟨hI, fun v hv hvW => ?_⟩
    rcases hvW with (hvW | hvD) | ⟨w, hw, hadj⟩
    · exact hIW v hv hvW
    · exact hID v hv (Finset.mem_coe.1 hvD)
    · exact hIadj v hv w (Finset.mem_coe.1 hw) hadj


/-- **Hole-only pairs with `S ⊕ T = D` are the pairs (colouring, independent set).**  Let `D` be
a vertex set in which every vertex has exactly two neighbours inside `D` and which avoids `W`.
The hole-only pairs `(S, T)` of independent sets avoiding `W` with `S ⊕ T = D` correspond
bijectively to the pairs `(P, I)` with `P` a proper two-colouring of `G[D]` and `I` an
independent set avoiding `W ∪ D ∪ N(D)` (`N` the open neighbourhood, so `D ∪ N(D) = Γ[D]`),
via `S = I ∪ P`, `T = I ∪ (D ∖ P)` and `P = S ∖ T`, `I = S ∩ T` (v1 L1974-1977: the
colour-class choices are the factor `2^{|𝒳|}`, `S ∩ T` is counted by `I_{G∖Γ[𝒳]}`).
Consequently every sum over the fibre can be computed on the product. -/
theorem sum_holeOnlyPairs_filter_symmDiff_eq [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {M : Type*} [AddCommMonoid M] {W : Set V} (D : Finset V)
    (hdeg : ∀ v ∈ D, (D.filter (G.Adj v)).card = 2) (hDW : ∀ v ∈ D, v ∉ W)
    (f : Finset V × Finset V → M) :
    ∑ p ∈ (G.holeOnlyPairs W).filter (fun p => p.1 ∆ p.2 = D), f p =
      ∑ x ∈ G.twoColourings D ×ˢ
          G.independentFinsetsAvoid (W ∪ (D : Set V) ∪ G.openNeighborhood (D : Set V)),
        f (x.2 ∪ x.1, x.2 ∪ (D \ x.1)) := by
  -- the facts about the independent part `I`
  have hI := fun I (h : I ∈ G.independentFinsetsAvoid
      (W ∪ (D : Set V) ∪ G.openNeighborhood (D : Set V))) =>
    mem_independentFinsetsAvoid_union_openNeighborhood.1 h
  have hleft : ∀ p ∈ (G.holeOnlyPairs W).filter (fun p => p.1 ∆ p.2 = D),
      ((p.1 ∩ p.2) ∪ (p.1 \ p.2), (p.1 ∩ p.2) ∪ (D \ (p.1 \ p.2))) = p := by
    intro p hp
    rw [Finset.mem_filter] at hp
    have hD := hp.2
    have hdiff : D \ (p.1 \ p.2) = p.2 \ p.1 := by
      rw [← hD]
      ext v
      simp only [Finset.mem_sdiff, Finset.mem_symmDiff]
      tauto
    rw [hdiff]
    refine Prod.ext ?_ ?_
    · ext v
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
      tauto
    · ext v
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
      tauto
  refine (Finset.sum_bij' (fun p _ => (p.1 \ p.2, p.1 ∩ p.2))
    (fun x _ => (x.2 ∪ x.1, x.2 ∪ (D \ x.1))) ?_ ?_ ?_ ?_ ?_)
  · -- `p ↦ (S ∖ T, S ∩ T)` lands in the product
    intro p hp
    rw [Finset.mem_filter, mem_holeOnlyPairs] at hp
    obtain ⟨⟨hS, hT, hSW, hTW, h2⟩, hD⟩ := hp
    have hdiff : D \ (p.1 \ p.2) = p.2 \ p.1 := by
      rw [← hD]
      ext v
      simp only [Finset.mem_sdiff, Finset.mem_symmDiff]
      tauto
    rw [Finset.mem_product, mem_twoColourings, mem_independentFinsetsAvoid]
    refine ⟨⟨?_, hS.mono (by simp), ?_⟩, hS.mono (by simp), ?_⟩
    · intro v hv
      rw [← hD, Finset.mem_symmDiff]
      exact Or.inl ⟨(Finset.mem_sdiff.1 hv).1, (Finset.mem_sdiff.1 hv).2⟩
    · rw [hdiff]
      exact hT.mono (by simp)
    · intro v hv hvW
      have hvS := (Finset.mem_inter.1 hv).1
      have hvT := (Finset.mem_inter.1 hv).2
      rcases hvW with (hvW | hvD) | ⟨w, hwD, hadj⟩
      · exact hSW v hvS hvW
      · have := Finset.mem_coe.1 hvD
        rw [← hD, Finset.mem_symmDiff] at this
        tauto
      · have hw := Finset.mem_coe.1 hwD
        rw [← hD, Finset.mem_symmDiff] at hw
        rcases hw with ⟨hwS, -⟩ | ⟨hwT, -⟩
        · exact hS (Finset.mem_coe.2 hvS) (Finset.mem_coe.2 hwS) hadj.ne hadj
        · exact hT (Finset.mem_coe.2 hvT) (Finset.mem_coe.2 hwT) hadj.ne hadj
  · -- `(P, I) ↦ (I ∪ P, I ∪ (D ∖ P))` lands in the fibre
    rintro ⟨P, I⟩ hx
    rw [Finset.mem_product, mem_twoColourings] at hx
    obtain ⟨⟨hPD, hP, hQ⟩, hIm⟩ := hx
    obtain ⟨hIind, hIW, hID, hIadj⟩ := hI I hIm
    have hQD : ∀ v, v ∈ D \ P → v ∈ D := fun v hv => (Finset.mem_sdiff.1 hv).1
    have hSD : (I ∪ P) ∆ (I ∪ (D \ P)) = D := by
      ext v
      simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_sdiff]
      have h1 := hID v
      have h2 := @hPD v
      tauto
    rw [Finset.mem_filter, mem_holeOnlyPairs]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · exact isIndepSet_union_of_no_edges hIind hP (fun x hx y hy => hIadj x hx y (hPD hy))
    · exact isIndepSet_union_of_no_edges hIind hQ
        (fun x hx y hy => hIadj x hx y (hQD y hy))
    · intro v hv
      rcases Finset.mem_union.1 hv with h | h
      · exact hIW v h
      · exact hDW v (hPD h)
    · intro v hv
      rcases Finset.mem_union.1 hv with h | h
      · exact hIW v h
      · exact hDW v (hQD v h)
    · intro v hv
      rw [hSD] at hv ⊢
      exact hdeg v hv
    · exact hSD
  · -- `p ↦ (S ∖ T, S ∩ T) ↦ (S ∩ T ∪ S ∖ T, ...)` is the identity on the fibre
    intro p hp
    exact hleft p hp
  · -- `(P, I) ↦ (I ∪ P, I ∪ (D ∖ P)) ↦ ((I ∪ P) ∖ (I ∪ (D ∖ P)), (I ∪ P) ∩ (I ∪ (D ∖ P)))`
    rintro ⟨P, I⟩ hx
    rw [Finset.mem_product, mem_twoColourings] at hx
    obtain ⟨⟨hPD, hP, hQ⟩, hIm⟩ := hx
    obtain ⟨hIind, hIW, hID, hIadj⟩ := hI I hIm
    have hPD' : ∀ v, v ∈ P → v ∈ D := fun v hv => hPD hv
    have hID' : ∀ v, v ∈ I → v ∉ D := hID
    refine Prod.ext ?_ ?_
    · ext v
      simp only [Finset.mem_sdiff, Finset.mem_union]
      have h1 := hID' v
      have h2 := hPD' v
      tauto
    · ext v
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
      have h1 := hID' v
      have h2 := hPD' v
      tauto
  · intro p hp
    simp only []
    rw [hleft p hp]

/-! ### The fibre identity -/

namespace PauliFrustrationRepresentation

variable {A : Type w} [Ring A]

/-- **The fibre identity (v1 L1974-1977), for any representation whose independent-set products
square to the right scalars.**  For `𝒳 ∈ 𝒞^{(even)}_{G∖W}`,
`∑_{(S,T) hole-only over 𝒳} (-u²)^{|S|} h_S h_T =
   (-u²)^{|∂𝒳|/2} 2^{|𝒳|} I_{G∖(W ∪ Γ[∂𝒳])}(-u²) ∏_{C ∈ 𝒳} h_C`,
where "over `𝒳`" means that the components of `G[S ⊕ T]` are exactly the members of `𝒳`.

The hypothesis `hsq` (`h_I² = ∏_{j∈I} b_j²` for independent `I`, v1 L231) holds for every
`PauliCliqueHamiltonianRepresentation` (`independentProduct_mul_self`).  The proof: the fibre is
in bijection with `(colourings of G[∂𝒳]) × (independent sets of G∖(W ∪ Γ[∂𝒳]))`
(`sum_holeOnlyPairs_filter_symmDiff_eq`); on the pair `(P, I)` the term is
`(-u²)^{|I| + |∂𝒳|/2} (∏_I b_j²) ∏_{C∈𝒳} h_C` independently of `P`
(`independentProduct_mul_eq`, `hsq`, `familyOperator_eq_of_partition`), and there are `2^{|𝒳|}`
colourings (`card_twoColourings_familyBoundaryFinset`). -/
theorem sum_holeOnlyPairs_fibre_of_sq [Fintype V] [DecidableEq V] {R : Type*} [CommRing R]
    [Algebra ℝ R] [Algebra R A] [Algebra ℝ A] [IsScalarTower ℝ R A]
    (H : G.PauliFrustrationRepresentation A) (b : V → ℝ)
    (hsq : ∀ I : Finset V, G.IsIndepSet (I : Set V) →
      H.independentProduct I * H.independentProduct I = algebraMap ℝ A (∏ j ∈ I, b j ^ 2))
    (W : Set V) {X : Finset (Set V)} (hX : X ∈ G.evenHoleFamilies W) (u : R) :
    ∑ p ∈ (G.holeOnlyPairs W).filter (fun p => G.symmDiffHoleFamily p.1 p.2 = X),
        (-u ^ 2) ^ p.1.card • (H.independentProduct p.1 * H.independentProduct p.2) =
      ((-u ^ 2) ^ ((G.familyBoundary X).ncard / 2) * 2 ^ X.card *
        Polynomial.aeval (-u ^ 2) (G.weightedIndependencePolynomial b
          (W ∪ G.familyBoundary X ∪ G.openNeighborhood (G.familyBoundary X)))) •
        H.familyOperator X := by
  classical
  obtain ⟨hX1, hX2⟩ := mem_evenHoleFamilies.1 hX
  have hXh : ∀ C ∈ X, G.IsEvenHoleCarrier C := fun C hC => (hX1 C hC).1
  set D : Finset V := G.familyBoundaryFinset X with hDdef
  have hcoe : (D : Set V) = G.familyBoundary X := coe_familyBoundaryFinset X
  have hdeg : ∀ v ∈ D, (D.filter (G.Adj v)).card = 2 := fun v hv =>
    card_filter_adj_familyBoundaryFinset hXh hX2 hv
  have hDW : ∀ v ∈ D, v ∉ W := by
    intro v hv hvW
    obtain ⟨C, hC, hvC⟩ := mem_familyBoundaryFinset.1 hv
    exact Set.disjoint_left.1 (hX1 C hC).2 hvC hvW
  -- the fibre over `𝒳` is the set of hole-only pairs with `S ⊕ T = ∂𝒳`
  have hfib : (G.holeOnlyPairs W).filter (fun p => G.symmDiffHoleFamily p.1 p.2 = X) =
      (G.holeOnlyPairs W).filter (fun p => p.1 ∆ p.2 = D) := by
    refine Finset.filter_congr fun p _ => ?_
    constructor
    · intro h
      apply Finset.coe_injective
      rw [← familyBoundary_symmDiffHoleFamily, h, hcoe]
    · intro h
      exact symmDiffHoleFamily_eq hXh hX2 h
  rw [hfib, sum_holeOnlyPairs_filter_symmDiff_eq D hdeg hDW, ← hcoe, Set.ncard_coe_finset]
  -- the value of each summand
  have hval : ∀ x ∈ G.twoColourings D ×ˢ
      G.independentFinsetsAvoid (W ∪ (D : Set V) ∪ G.openNeighborhood (D : Set V)),
      (-u ^ 2) ^ (x.2 ∪ x.1, x.2 ∪ (D \ x.1)).1.card •
          (H.independentProduct (x.2 ∪ x.1, x.2 ∪ (D \ x.1)).1 *
            H.independentProduct (x.2 ∪ x.1, x.2 ∪ (D \ x.1)).2) =
        ((-u ^ 2) ^ (D.card / 2) *
          ((-u ^ 2) ^ x.2.card * algebraMap ℝ R (∏ j ∈ x.2, b j ^ 2))) • H.familyOperator X := by
    rintro ⟨P, I⟩ hx
    rw [Finset.mem_product, mem_twoColourings,
      mem_independentFinsetsAvoid_union_openNeighborhood] at hx
    obtain ⟨⟨hPD, hP, hQ⟩, hIind, hIW, hID, hIadj⟩ := hx
    dsimp only at hPD hP hQ hIind hIW hID hIadj ⊢
    have hQD : ∀ v, v ∈ D \ P → v ∈ D := fun v hv => (Finset.mem_sdiff.1 hv).1
    have hSind : G.IsIndepSet ((I ∪ P : Finset V) : Set V) :=
      isIndepSet_union_of_no_edges hIind hP (fun x hx y hy => hIadj x hx y (hPD hy))
    have hTind : G.IsIndepSet ((I ∪ (D \ P) : Finset V) : Set V) :=
      isIndepSet_union_of_no_edges hIind hQ (fun x hx y hy => hIadj x hx y (hQD y hy))
    have hPD' : ∀ v, v ∈ P → v ∈ D := fun v hv => hPD hv
    have hinter : (I ∪ P) ∩ (I ∪ (D \ P)) = I := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
      have h1 := hID v
      have h2 := hPD' v
      tauto
    have hS' : (I ∪ P) \ (I ∪ (D \ P)) = P := by
      ext v
      simp only [Finset.mem_union, Finset.mem_sdiff]
      have h1 := hID v
      have h2 := hPD' v
      tauto
    have hT' : (I ∪ (D \ P)) \ (I ∪ P) = D \ P := by
      ext v
      simp only [Finset.mem_union, Finset.mem_sdiff]
      have h1 := hID v
      have h2 := hPD' v
      tauto
    have hmul := H.independentProduct_mul_eq hSind hTind
    rw [hinter, hS', hT', hsq I hIind] at hmul
    have hdis : Disjoint P (D \ P) := Finset.disjoint_sdiff
    have hpart := familyOperator_eq_of_partition H hXh hX2 hP hQ hdis
      (Finset.union_sdiff_of_subset hPD)
    -- `|P| = |D ∖ P|`, hence `|P| = |D| / 2`
    have hsymm : P ∆ (D \ P) = D := by
      ext v
      simp only [Finset.mem_symmDiff, Finset.mem_sdiff]
      have h2 := hPD' v
      tauto
    have hbal : P.card = (D \ P).card := by
      refine card_eq_of_forall_card_filter_symmDiff_eq_two hP hQ ?_
      rw [hsymm]
      exact hdeg
    have hPcard : P.card = D.card / 2 := by
      have := Finset.card_sdiff_add_card_eq_card hPD
      omega
    have hIPdisj : Disjoint I P :=
      Finset.disjoint_left.2 fun v hvI hvP => hID v hvI (hPD hvP)
    have hcard : (I ∪ P).card = I.card + P.card := Finset.card_union_of_disjoint hIPdisj
    rw [hmul, hpart, hcard, hPcard, Algebra.smul_def, Algebra.smul_def,
      IsScalarTower.algebraMap_apply ℝ R A, ← mul_assoc, ← map_mul]
    congr 2
    ring
  have haeval : Polynomial.aeval (-u ^ 2) (G.weightedIndependencePolynomial b
      (W ∪ (D : Set V) ∪ G.openNeighborhood (D : Set V))) =
      ∑ I ∈ G.independentFinsetsAvoid (W ∪ (D : Set V) ∪ G.openNeighborhood (D : Set V)),
        (-u ^ 2) ^ I.card * algebraMap ℝ R (∏ j ∈ I, b j ^ 2) := by
    rw [weightedIndependencePolynomial_eq_sum, map_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X, mul_comm]
  rw [Finset.sum_congr rfl hval, ← Finset.sum_smul]
  congr 1
  rw [Finset.sum_product, haeval]
  dsimp only
  rw [Finset.sum_const, card_twoColourings_familyBoundaryFinset hXh hX2, nsmul_eq_mul,
    ← Finset.mul_sum, Nat.cast_pow, Nat.cast_ofNat]
  ring

end PauliFrustrationRepresentation

namespace PauliCliqueHamiltonianRepresentation

variable {K : Set V} {A : Type w} [Ring A] [Algebra ℝ A]

/-- **The fibre identity for the Hamiltonian representation** (v1 L1974-1977).  For a
frustration-graph representation `H` (a `PauliCliqueHamiltonianRepresentation` with real
couplings `b_j = H.coupling j`), `W ⊆ V` and `𝒳 ∈ 𝒞^{(even)}_{G∖W}`,
`∑_{(S,T) hole-only over 𝒳} (-u²)^{|S|} h_S h_T =
   (-u²)^{|∂𝒳|/2} 2^{|𝒳|} I_{G∖(W ∪ Γ[∂𝒳])}(-u²) ∏_{C ∈ 𝒳} h_C`,
where the pairs "over `𝒳`" are those whose symmetric difference has the members of `𝒳` as
connected components (`symmDiffHoleFamily`), `Γ[∂𝒳] = ∂𝒳 ∪ N(∂𝒳)`, `I_{G∖W'}` is the
weighted independence polynomial (`weightedIndependencePolynomial`) and `u` lies in any
commutative `ℝ`-algebra `R` acting on `A`.

No claw-freeness is used (it enters only through the description of the surviving terms of
`T(u) T(-u)` as `holeOnlyPairs`).  The proof is `sum_holeOnlyPairs_fibre_of_sq` together with
`independentProduct_mul_self`. -/
theorem sum_holeOnlyPairs_fibre [Fintype V] [DecidableEq V] {R : Type*} [CommRing R]
    [Algebra ℝ R] [Algebra R A] [IsScalarTower ℝ R A]
    (H : G.PauliCliqueHamiltonianRepresentation K ℝ A) (W : Set V) {X : Finset (Set V)}
    (hX : X ∈ G.evenHoleFamilies W) (u : R) :
    ∑ p ∈ (G.holeOnlyPairs W).filter (fun p => G.symmDiffHoleFamily p.1 p.2 = X),
        (-u ^ 2) ^ p.1.card • (H.operator.restrictSome.independentProduct p.1 *
          H.operator.restrictSome.independentProduct p.2) =
      ((-u ^ 2) ^ ((G.familyBoundary X).ncard / 2) * 2 ^ X.card *
        Polynomial.aeval (-u ^ 2) (G.weightedIndependencePolynomial H.coupling
          (W ∪ G.familyBoundary X ∪ G.openNeighborhood (G.familyBoundary X)))) •
        H.operator.restrictSome.familyOperator X :=
  H.operator.restrictSome.sum_holeOnlyPairs_fibre_of_sq H.coupling
    (fun _ hI => H.independentProduct_mul_self hI) W hX u

end PauliCliqueHamiltonianRepresentation

end SimpleGraph
