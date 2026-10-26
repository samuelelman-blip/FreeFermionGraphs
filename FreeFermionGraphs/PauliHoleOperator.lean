import FreeFermionGraphs.OperatorCharges
import FreeFermionGraphs.HoleChargeSigns
import FreeFermionGraphs.SimplicialModeHamiltonian
import FreeFermionGraphs.PauliCliqueHamiltonian
import FreeFermionGraphs.SimplicialClique
import FreeFermionGraphs.EvenHoleDeformationQuotient

/-!
# Even-hole operators `h_C`, generalized cycle operators `J_c`, and `χ` commuting with `J_c`

This module works over a clique-rooted Pauli Hamiltonian
`SimpleGraph.PauliCliqueHamiltonianRepresentation G K R A`, whose operator data live on the
root-adjoined graph `G.adjoinRootAt K` with the artificial root term `χ`
(`PauliCliqueHamiltonianRepresentation.rootOperator`).  It transports the carrier-level
operators of `FreeFermionGraphs.OperatorCharges` to this setting and proves manuscript
Result 2's first claim, "`χ` commutes with each generalized cycle symmetry"
(arXiv 2305.15625 v1, L112; the claim is not proved in v1).

## Contents (v1 references)

* `holeOperator E = h_{C_a} h_{C_b}` for an alternating labelling `E` (v1 L311-313,
  "We choose the factor ordering for the operator corresponding to `C` as
  `h_C = h_{C_a} h_{C_b}`"), with the independent products taken on the root-adjoined graph
  along `some`.  `holeOperator_eq_labelingOperator` identifies it with
  `PauliFrustrationRepresentation.labelingOperator` of the restricted representation
  `H.operator.restrictSome`, so every fact of `OperatorCharges` applies (the two class products
  commute, `holeOperator_comm`; swapping the colours does not change `h_C`,
  `holeOperator_swapColors`).
* `holeOperator_eq_of_carrier_eq` : for labellings with full cyclic order (so that the carrier is
  a genuine even hole, which is the manuscript setup: `h_C` is defined for an even hole `C`,
  v1 L309-313), `h_C` depends only on the carrier.  The full-cyclic hypotheses are kept to match
  the package statement and the manuscript setup, and only the first of them is used
  (`holeOperator_eq_of_carrier_eq_of_isEvenHoleCarrier` needs just that the carrier is an even
  hole).
* `holeOperatorOfCarrier H C = h_C` (carrier-level; the fallback value `0` is taken exactly
  when `C` is not the carrier of a full-cyclic labelling, i.e. not an even-hole carrier,
  `holeOperatorOfCarrier_eq_zero_of_not_isEvenHoleCarrier`) and
  `generalizedCycleOperator H c = J_c = Σ_{C ∈ c} h_C` (v1 Definition 15, L799-803) as a function
  of the deformation class `c`.  `generalizedCycleOperator_mk` identifies it with the
  `generalizedCycleSymmetryOp` of `OperatorCharges` for the restricted representation, and
  `exists_fullCyclic_labeling_holeOperatorOfCarrier` shows that on an even-hole carrier the value
  is `holeOperator` of a full-cyclic labelling (never the fallback `0`).
* `EvenHoleLabeling.ncard_inter_carrier_eq_zero_or_two` : a simplicial clique meets every
  even hole in `0` or `2` vertices (one vertex `v` would put the two non-adjacent hole
  neighbours of `v` into `Γ(v) \ K`, which is a clique; three would give a triangle in a
  triangle-free hole).  No claw-freeness and no full cyclic order is needed.
* `commute_rootOperator_holeOperator`, `commute_rootOperator_generalizedCycleOperator` :
  `χ` commutes with every `h_C` and every `J_c` (v1 L112).  `χ` anticommutes with `h_j` exactly
  for `j ∈ K`, so it commutes with `h_{C_a} h_{C_b}` because `|C ∩ K|` is even.  Only
  simpliciality of `K` is used (no claw-freeness, no connectedness of `G`).

These are unconditional statements about the manuscript setup (a simplicial clique `K` and the
root `χ` with `⟨χ, h_j⟩ = δ_{j ∈ K}`); `generalizedCycleOperator` is `0` on classes with no
hole carrier, which is why sector hypotheses downstream should be quantified only over classes
of genuine hole carriers.
-/

open scoped BigOperators

universe u v w

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-! ### A simplicial clique meets a 2-regular triangle-free induced subgraph in 0 or 2 vertices -/

namespace IsSimplicialClique

variable {K C : Set V}

/-- Let `K` be a simplicial clique and `C` a set in which every vertex has exactly two
neighbours inside `C`, and these two neighbours are non-adjacent (for instance the carrier of an
even hole).  Then `K ∩ C` is empty or consists of exactly two vertices.

Proof: for `j ∈ K ∩ C` with `C`-neighbours `x ≠ y`, they cannot both lie in `K` (a clique, but
`x, y` are non-adjacent) and cannot both lie outside `K` (`Γ(j) \ K` is a clique), so exactly one,
say `x`, lies in `K`.  Any other `z ∈ K ∩ C` is adjacent to `j`, hence is `x` or `y`, hence `x`. -/
theorem inter_eq_empty_or_pair_of_two_regular (hK : G.IsSimplicialClique K)
    (hC : ∀ v ∈ C, ∃ x y : V, x ≠ y ∧ ¬G.Adj x y ∧ G.neighborSet v ∩ C = {x, y}) :
    K ∩ C = ∅ ∨ ∃ s t : V, s ≠ t ∧ K ∩ C = {s, t} := by
  by_cases hne : (K ∩ C).Nonempty
  · right
    obtain ⟨j, hjK, hjC⟩ := hne
    obtain ⟨x, y, hxy, hnadj, hN⟩ := hC j hjC
    have hx : x ∈ G.neighborSet j ∩ C := by rw [hN]; simp
    have hy : y ∈ G.neighborSet j ∩ C := by rw [hN]; simp
    -- If `x ∈ K` and `y ∉ K`, then `K ∩ C = {j, x}`.
    have key : ∀ x y : V, x ≠ y → G.neighborSet j ∩ C = {x, y} → x ∈ K → y ∉ K →
        K ∩ C = {j, x} := by
      intro x y hxy hN hxK hyK
      have hxC : x ∈ C := by
        have : x ∈ G.neighborSet j ∩ C := by rw [hN]; simp
        exact this.2
      ext z
      constructor
      · rintro ⟨hzK, hzC⟩
        by_cases hzj : z = j
        · exact Or.inl hzj
        · right
          have hadj : G.Adj j z := hK.isClique hjK hzK (Ne.symm hzj)
          have hz : z ∈ G.neighborSet j ∩ C := ⟨hadj, hzC⟩
          rw [hN] at hz
          rcases hz with rfl | rfl
          · rfl
          · exact (hyK hzK).elim
      · rintro (rfl | rfl)
        · exact ⟨hjK, hjC⟩
        · exact ⟨hxK, hxC⟩
    by_cases hxK : x ∈ K
    · by_cases hyK : y ∈ K
      · exact (hnadj (hK.isClique hxK hyK hxy)).elim
      · exact ⟨j, x, G.ne_of_adj hx.1, key x y hxy hN hxK hyK⟩
    · by_cases hyK : y ∈ K
      · refine ⟨j, y, G.ne_of_adj hy.1, key y x hxy.symm ?_ hyK hxK⟩
        rw [hN, Set.pair_comm]
      · exact (hnadj ((hK.externalNeighbors_isClique hjK) ⟨hx.1, hxK⟩ ⟨hy.1, hyK⟩ hxy)).elim
  · left
    rwa [Set.not_nonempty_iff_eq_empty] at hne

end IsSimplicialClique

/-! ### Neighbours inside the carrier of a labelling -/

namespace EvenHoleLabeling

/-- Every vertex `a i` of a labelling has exactly two neighbours `b i ≠ b (next i)` inside the
carrier, and they are non-adjacent. -/
theorem exists_pair_neighborSet_inter_carrier_a {k : ℕ} (L : G.EvenHoleLabeling k) (i : Fin k) :
    ∃ x y : V, x ≠ y ∧ ¬G.Adj x y ∧ G.neighborSet (L.a i) ∩ L.carrier = {x, y} := by
  refine ⟨L.b i, L.b (L.next i), fun h => L.next_ne i (L.b_injective h).symm,
    L.adj_bb _ _, ?_⟩
  ext v
  simp only [Set.mem_inter_iff, mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hadj, hv⟩
    exact (L.adj_a_iff_of_mem_carrier i hv).1 hadj
  · intro hv
    have hv' : v ∈ L.carrier := by
      rcases hv with rfl | rfl
      · exact L.b_mem_carrier i
      · exact L.b_mem_carrier _
    exact ⟨(L.adj_a_iff_of_mem_carrier i hv').2 hv, hv'⟩

/-- Every vertex of the carrier of a labelling has exactly two neighbours inside the carrier,
and they are non-adjacent: `G[C]` is 2-regular and triangle-free (whether or not `next` is a
single cycle).  The `b`-vertices are handled through the colour-swapped labelling. -/
theorem exists_pair_neighborSet_inter_carrier {k : ℕ} (L : G.EvenHoleLabeling k) {v : V}
    (hv : v ∈ L.carrier) :
    ∃ x y : V, x ≠ y ∧ ¬G.Adj x y ∧ G.neighborSet v ∩ L.carrier = {x, y} := by
  rcases hv with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact L.exists_pair_neighborSet_inter_carrier_a i
  · have h := L.swapColors.exists_pair_neighborSet_inter_carrier_a i
    rwa [swapColors_a, swapColors_carrier] at h

/-- **A simplicial clique meets every even hole in `0` or `2` vertices.**  Stated for the
carrier of any alternating labelling (the argument is local, so no full cyclic order and no
claw-freeness are needed). -/
theorem ncard_inter_carrier_eq_zero_or_two {K : Set V} (hK : G.IsSimplicialClique K) {k : ℕ}
    (L : G.EvenHoleLabeling k) :
    (K ∩ L.carrier).ncard = 0 ∨ (K ∩ L.carrier).ncard = 2 := by
  rcases hK.inter_eq_empty_or_pair_of_two_regular
      (fun _ hv => L.exists_pair_neighborSet_inter_carrier hv) with h | ⟨s, t, hst, h⟩
  · left; rw [h, Set.ncard_empty]
  · right; rw [h, Set.ncard_pair hst]

end EvenHoleLabeling

/-! ### The Pauli operators -/

namespace PauliCliqueHamiltonianRepresentation

variable {K : Set V} {R : Type v} {A : Type w} [CommRing R] [Ring A] [Algebra R A]

/-- The image of a colour class under `some` is the image under the embedding `some`. -/
theorem image_some_eq_map [DecidableEq V] {k : ℕ} (f : Fin k → V) :
    (Finset.univ.image fun i => (some (f i) : Option V)) =
      (Finset.univ.image f).map Function.Embedding.some := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_map,
    Function.Embedding.some_apply]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨f i, ⟨i, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩

/-- The image of a finset of original vertices under `some` is independent in the root-adjoined
graph if and only if it is independent in the original graph; we only need the direction
from `G`. -/
theorem isIndepSet_map_some {S : Finset V} (hS : G.IsIndepSet (S : Set V)) :
    (G.adjoinRootAt K).IsIndepSet
      ((S.map Function.Embedding.some : Finset (Option V)) : Set (Option V)) := by
  intro x hx y hy hxy
  rw [Finset.mem_coe, Finset.mem_map] at hx hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  show ¬(G.adjoinRootAt K).Adj (some a) (some b)
  rw [adjoinRootAt_adj_some_some]
  exact hS ha hb (fun h => hxy (by rw [h]))

/-- The number of neighbours of the root `χ` in the image `some '' S` is `|S ∩ K|`: the root is
adjacent to `some j` exactly for `j ∈ K`. -/
theorem crossCount_root_map_some [DecidableEq V] [DecidablePred (· ∈ K)] (S : Finset V) :
    (G.adjoinRootAt K).crossCount {none} (S.map Function.Embedding.some) =
      (S.filter (· ∈ K)).card := by
  classical
  rw [crossCount_eq_sum_card_filter, Finset.sum_singleton]
  have h : (S.map Function.Embedding.some).filter ((G.adjoinRootAt K).Adj none) =
      (S.filter (· ∈ K)).map Function.Embedding.some := by
    ext x
    cases x with
    | none => simp
    | some v =>
      simp only [Finset.mem_filter, Finset.mem_map, Function.Embedding.some_apply,
        adjoinRootAt_adj_none_some, Option.some.injEq]
      constructor
      · rintro ⟨⟨a, ha, rfl⟩, hK⟩
        exact ⟨a, ⟨ha, hK⟩, rfl⟩
      · rintro ⟨a, ⟨ha, hK⟩, rfl⟩
        exact ⟨⟨a, ha, rfl⟩, hK⟩
  rw [h, Finset.card_map]

/-- **`h_C` for an alternating labelling** (v1 L311-313: `h_C := h_{C_a} h_{C_b}`), as the
product, on the root-adjoined graph, of the independent products over the two colour classes
(embedded by `some`). -/
noncomputable def holeOperator [DecidableEq V]
    (H : G.PauliCliqueHamiltonianRepresentation K R A) {k : ℕ}
    (E : G.EvenHoleLabeling k) : A :=
  H.operator.independentProduct (Finset.univ.image fun i => some (E.a i)) *
    H.operator.independentProduct (Finset.univ.image fun i => some (E.b i))

/-- `h_C` is the labelling operator of the restricted representation `H.operator.restrictSome`
(the root-adjoined products along `some` are the products over the original vertices,
`PauliFrustrationRepresentation.independentProduct_map_some`). -/
theorem holeOperator_eq_labelingOperator [DecidableEq V]
    (H : G.PauliCliqueHamiltonianRepresentation K R A) {k : ℕ} (E : G.EvenHoleLabeling k) :
    H.holeOperator E = H.operator.restrictSome.labelingOperator E := by
  unfold holeOperator PauliFrustrationRepresentation.labelingOperator
  rw [image_some_eq_map, image_some_eq_map,
    H.operator.independentProduct_map_some E.isIndepSet_image_a,
    H.operator.independentProduct_map_some E.isIndepSet_image_b]

/-- The two colour-class products of `h_C` commute (v1 L313: "these operators commute"). -/
theorem holeOperator_comm [DecidableEq V]
    (H : G.PauliCliqueHamiltonianRepresentation K R A) {k : ℕ} (E : G.EvenHoleLabeling k) :
    H.operator.independentProduct (Finset.univ.image fun i => some (E.a i)) *
        H.operator.independentProduct (Finset.univ.image fun i => some (E.b i)) =
      H.operator.independentProduct (Finset.univ.image fun i => some (E.b i)) *
        H.operator.independentProduct (Finset.univ.image fun i => some (E.a i)) := by
  rw [image_some_eq_map, image_some_eq_map,
    H.operator.independentProduct_map_some E.isIndepSet_image_a,
    H.operator.independentProduct_map_some E.isIndepSet_image_b]
  exact H.operator.restrictSome.labelingOperator_comm E

/-- Swapping the colours does not change `h_C`. -/
theorem holeOperator_swapColors [DecidableEq V]
    (H : G.PauliCliqueHamiltonianRepresentation K R A) {k : ℕ} (E : G.EvenHoleLabeling k) :
    H.holeOperator E.swapColors = H.holeOperator E := by
  rw [holeOperator_eq_labelingOperator, holeOperator_eq_labelingOperator]
  exact H.operator.restrictSome.labelingOperator_swapColors E

/-- `h_C` depends only on the carrier of an even-hole labelling: two labellings with the same
carrier, which is an even hole, give the same operator (v1 L313; the colour classes of an even
hole are unique up to a swap). -/
theorem holeOperator_eq_of_carrier_eq_of_isEvenHoleCarrier [DecidableEq V]
    (H : G.PauliCliqueHamiltonianRepresentation K R A) {k k' : ℕ}
    (E : G.EvenHoleLabeling k) (E' : G.EvenHoleLabeling k')
    (hC : G.IsEvenHoleCarrier E.carrier) (h : E.carrier = E'.carrier) :
    H.holeOperator E = H.holeOperator E' := by
  rw [holeOperator_eq_labelingOperator, holeOperator_eq_labelingOperator]
  exact H.operator.restrictSome.labelingOperator_eq_of_carrier_eq E E' hC h

/-- **`h_C` depends only on the carrier** (v1 L311-313).  For labellings with full cyclic
order, which present the carrier as a genuine even hole, equal carriers give equal operators.

The full-cyclic hypotheses express the manuscript setup, in which `h_C` is defined for an even
hole `C` (v1 L309-313), and are kept to match the package statement.  The second one, `_hE'`,
is unused; the sharper form `holeOperator_eq_of_carrier_eq_of_isEvenHoleCarrier` assumes only
that the carrier of `E` is an even hole. -/
theorem holeOperator_eq_of_carrier_eq [DecidableEq V]
    (H : G.PauliCliqueHamiltonianRepresentation K R A) {k k' : ℕ}
    (E : G.EvenHoleLabeling k) (E' : G.EvenHoleLabeling k')
    (hE : E.HasFullCyclicOrder) (_hE' : E'.HasFullCyclicOrder)
    (h : E.carrier = E'.carrier) : H.holeOperator E = H.holeOperator E' :=
  H.holeOperator_eq_of_carrier_eq_of_isEvenHoleCarrier E E'
    (E.isEvenHoleCarrier_of_hasFullCyclicOrder hE) h

/-- **`h_C` as a function of the carrier** (v1 L313): `h_{C_a} h_{C_b}` for a full-cyclic
labelling of `C`, and `0` if `C` is not the carrier of any full-cyclic labelling (that is, `C`
is not an even hole, `holeOperatorOfCarrier_eq_zero_of_not_isEvenHoleCarrier`).  The choice of
labelling is irrelevant by `holeOperator_eq_of_carrier_eq`. -/
noncomputable def holeOperatorOfCarrier [DecidableEq V]
    (H : G.PauliCliqueHamiltonianRepresentation K R A) (C : Set V) : A := by
  classical
  exact if h : ∃ k, ∃ E : G.EvenHoleLabeling k, E.HasFullCyclicOrder ∧ E.carrier = C then
    H.holeOperator h.choose_spec.choose else 0

/-- On the carrier of a full-cyclic labelling, `holeOperatorOfCarrier` is `holeOperator`
(for any such labelling of that carrier). -/
theorem holeOperatorOfCarrier_eq [DecidableEq V]
    (H : G.PauliCliqueHamiltonianRepresentation K R A) {k : ℕ}
    (E : G.EvenHoleLabeling k) (hE : E.HasFullCyclicOrder) :
    H.holeOperatorOfCarrier E.carrier = H.holeOperator E := by
  classical
  have hex : ∃ k', ∃ E' : G.EvenHoleLabeling k', E'.HasFullCyclicOrder ∧
      E'.carrier = E.carrier := ⟨k, E, hE, rfl⟩
  unfold holeOperatorOfCarrier
  rw [dif_pos hex]
  exact H.holeOperator_eq_of_carrier_eq _ _ hex.choose_spec.choose_spec.1 hE
    hex.choose_spec.choose_spec.2

/-- On an even-hole carrier `holeOperatorOfCarrier` is the `holeOperator` of some full-cyclic
labelling of that carrier (never the fallback `0`). -/
theorem exists_fullCyclic_labeling_holeOperatorOfCarrier [DecidableEq V]
    (H : G.PauliCliqueHamiltonianRepresentation K R A) {C : Set V} (hC : G.IsEvenHoleCarrier C) :
    ∃ (k : ℕ) (E : G.EvenHoleLabeling k), E.HasFullCyclicOrder ∧ E.carrier = C ∧
      H.holeOperatorOfCarrier C = H.holeOperator E := by
  obtain ⟨k, E, hE, rfl⟩ := (isEvenHoleCarrier_iff_exists_fullCyclic_labeling C).1 hC
  exact ⟨k, E, hE, rfl, H.holeOperatorOfCarrier_eq E hE⟩

/-- `holeOperatorOfCarrier` is the carrier-level operator `evenHoleOperator` of the restricted
representation `H.operator.restrictSome` from `FreeFermionGraphs.OperatorCharges`. -/
theorem holeOperatorOfCarrier_eq_evenHoleOperator [DecidableEq V]
    (H : G.PauliCliqueHamiltonianRepresentation K R A) (C : Set V) :
    H.holeOperatorOfCarrier C = H.operator.restrictSome.evenHoleOperator C := by
  classical
  unfold holeOperatorOfCarrier PauliFrustrationRepresentation.evenHoleOperator
  by_cases hex : ∃ k, ∃ E : G.EvenHoleLabeling k, E.HasFullCyclicOrder ∧ E.carrier = C
  · rw [dif_pos hex, dif_pos hex]
    rw [holeOperator_eq_labelingOperator]
  · rw [dif_neg hex, dif_neg hex]

/-- `holeOperatorOfCarrier` is `0` off the even-hole carriers. -/
theorem holeOperatorOfCarrier_eq_zero_of_not_isEvenHoleCarrier [DecidableEq V]
    (H : G.PauliCliqueHamiltonianRepresentation K R A) {C : Set V}
    (hC : ¬G.IsEvenHoleCarrier C) : H.holeOperatorOfCarrier C = 0 := by
  rw [holeOperatorOfCarrier_eq_evenHoleOperator]
  exact H.operator.restrictSome.evenHoleOperator_eq_zero_of_not_isEvenHoleCarrier hC

/-- **The generalized cycle operator `J_c = Σ_{C ∈ c} h_C`** (v1 Definition 15, L799-803) as a
function of the deformation class `c`.  Terms of `c` that are not even-hole carriers contribute
`0`; for a class of genuine even holes every member is a hole
(`InEvenHoleDeformationClosure.isEvenHoleCarrier`), so this is the paper's sum. -/
noncomputable def generalizedCycleOperator [Fintype V] [DecidableEq V]
    (H : G.PauliCliqueHamiltonianRepresentation K R A) (c : EvenHoleDeformationClass G) : A :=
  G.generalizedCycleSymmetryOnClass H.holeOperatorOfCarrier c

/-- On the class of a carrier `C₀`, `J_c` is the sum of `h_C` over the closure `⟨C₀⟩`. -/
theorem generalizedCycleOperator_mk [Fintype V] [DecidableEq V]
    (H : G.PauliCliqueHamiltonianRepresentation K R A) (C₀ : Set V) :
    H.generalizedCycleOperator (G.evenHoleDeformationClassOf C₀) =
      H.operator.restrictSome.generalizedCycleSymmetryOp C₀ := by
  unfold generalizedCycleOperator PauliFrustrationRepresentation.generalizedCycleSymmetryOp
  rw [generalizedCycleSymmetryOnClass_mk]
  exact G.generalizedCycleSymmetry_congr C₀
    (fun C _ => H.holeOperatorOfCarrier_eq_evenHoleOperator C)

/-! ### `χ` commutes with `h_C` and `J_c` -/

/-- The root `χ` meets the colour classes of a labelling in an even total number of vertices:
the exponent `Σ ⟨χ, h_j⟩` of the sign in `χ h_{C_a} h_{C_b} = ± h_{C_a} h_{C_b} χ` is even,
because a simplicial clique meets the carrier in `0` or `2` vertices. -/
theorem even_crossCount_root_add [DecidableEq V] (hK : G.IsSimplicialClique K) {k : ℕ}
    (E : G.EvenHoleLabeling k) :
    Even ((G.adjoinRootAt K).crossCount {none}
        (Finset.univ.image fun i => (some (E.a i) : Option V)) +
      (G.adjoinRootAt K).crossCount {none}
        (Finset.univ.image fun i => (some (E.b i) : Option V))) := by
  classical
  rw [image_some_eq_map, image_some_eq_map, crossCount_root_map_some, crossCount_root_map_some,
    ← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter E.disjoint_image_a_image_b),
    ← Finset.filter_union]
  have hset : (((Finset.univ.image E.a ∪ Finset.univ.image E.b).filter (· ∈ K) : Finset V) :
      Set V) = K ∩ E.carrier := by
    ext v
    rw [Finset.coe_filter, ← E.coe_image_a_union_image_b]
    simp only [Finset.coe_union, Set.mem_setOf_eq, Set.mem_inter_iff, Finset.mem_union,
      Finset.mem_coe, Set.mem_union]
    tauto
  rw [← Set.ncard_coe_finset, hset]
  rcases E.ncard_inter_carrier_eq_zero_or_two hK with h | h <;> rw [h]
  · exact ⟨0, rfl⟩
  · exact even_two

/-- **`χ` commutes with `h_C`** for every alternating labelling `E` of an even hole, when the
root `χ` is attached to a simplicial clique `K` (v1 Result 2, L112, at the level of a single
`h_C`).  `χ` anticommutes with `h_j` exactly for `j ∈ K`, and `|C ∩ K| ∈ {0, 2}`. -/
theorem commute_rootOperator_holeOperator [DecidableEq V] (hK : G.IsSimplicialClique K)
    (H : G.PauliCliqueHamiltonianRepresentation K R A) {k : ℕ} (E : G.EvenHoleLabeling k) :
    Commute H.rootOperator (H.holeOperator E) := by
  classical
  set Pa := H.operator.independentProduct (Finset.univ.image fun i => (some (E.a i) : Option V))
    with hPa
  set Pb := H.operator.independentProduct (Finset.univ.image fun i => (some (E.b i) : Option V))
    with hPb
  have hia : (G.adjoinRootAt K).IsIndepSet
      ((Finset.univ.image fun i => (some (E.a i) : Option V) : Finset (Option V)) :
        Set (Option V)) := by
    rw [image_some_eq_map]; exact isIndepSet_map_some E.isIndepSet_image_a
  have hib : (G.adjoinRootAt K).IsIndepSet
      ((Finset.univ.image fun i => (some (E.b i) : Option V) : Finset (Option V)) :
        Set (Option V)) := by
    rw [image_some_eq_map]; exact isIndepSet_map_some E.isIndepSet_image_b
  have ea := H.operator.term_mul_independentProduct none hia
  have eb := H.operator.term_mul_independentProduct none hib
  have heven := even_crossCount_root_add hK E
  change H.operator.term none * (Pa * Pb) = (Pa * Pb) * H.operator.term none
  set ca := (G.adjoinRootAt K).crossCount {none}
    (Finset.univ.image fun i => (some (E.a i) : Option V)) with hca
  set cb := (G.adjoinRootAt K).crossCount {none}
    (Finset.univ.image fun i => (some (E.b i) : Option V)) with hcb
  rcases Nat.even_or_odd ca with hea | hoa
  · have heb : Even cb := (Nat.even_add.1 heven).1 hea
    rw [hea.neg_one_pow, one_mul] at ea
    rw [heb.neg_one_pow, one_mul] at eb
    calc H.operator.term none * (Pa * Pb)
        = (H.operator.term none * Pa) * Pb := by rw [mul_assoc]
      _ = (Pa * H.operator.term none) * Pb := by rw [ea]
      _ = Pa * (H.operator.term none * Pb) := by rw [mul_assoc]
      _ = Pa * (Pb * H.operator.term none) := by rw [eb]
      _ = (Pa * Pb) * H.operator.term none := by rw [mul_assoc]
  · have hob : Odd cb := by
      rcases Nat.even_or_odd cb with heb | hob
      · exact absurd (Nat.even_add.1 heven |>.2 heb) (Nat.not_even_iff_odd.2 hoa)
      · exact hob
    rw [hoa.neg_one_pow, neg_one_mul] at ea
    rw [hob.neg_one_pow, neg_one_mul] at eb
    calc H.operator.term none * (Pa * Pb)
        = (H.operator.term none * Pa) * Pb := by rw [mul_assoc]
      _ = -(Pa * H.operator.term none) * Pb := by rw [ea]
      _ = -(Pa * (H.operator.term none * Pb)) := by rw [neg_mul, mul_assoc]
      _ = -(Pa * -(Pb * H.operator.term none)) := by rw [eb]
      _ = (Pa * Pb) * H.operator.term none := by rw [mul_neg, neg_neg, mul_assoc]

/-- `χ` commutes with `h_C` as a function of the carrier, for every set `C` (the fallback value
`0` off the even-hole carriers commutes with everything). -/
theorem commute_rootOperator_holeOperatorOfCarrier [DecidableEq V]
    (hK : G.IsSimplicialClique K) (H : G.PauliCliqueHamiltonianRepresentation K R A)
    (C : Set V) : Commute H.rootOperator (H.holeOperatorOfCarrier C) := by
  classical
  unfold holeOperatorOfCarrier
  by_cases hex : ∃ k, ∃ E : G.EvenHoleLabeling k, E.HasFullCyclicOrder ∧ E.carrier = C
  · rw [dif_pos hex]
    exact commute_rootOperator_holeOperator hK H _
  · rw [dif_neg hex]
    exact Commute.zero_right _

/-- **`χ` commutes with every generalized cycle operator `J_c = Σ_{C ∈ c} h_C`** (v1 Result 2,
L112: "The operator `χ` commutes with each of the generalized cycle symmetries"; the claim is
not proved in v1).  `K` is the simplicial clique at which the root `χ` is attached. -/
theorem commute_rootOperator_generalizedCycleOperator [Fintype V] [DecidableEq V]
    (hK : G.IsSimplicialClique K) (H : G.PauliCliqueHamiltonianRepresentation K R A)
    (c : EvenHoleDeformationClass G) :
    Commute H.rootOperator (H.generalizedCycleOperator c) := by
  induction c using Quotient.inductionOn with
  | h C₀ =>
    show Commute H.rootOperator (H.generalizedCycleOperator (G.evenHoleDeformationClassOf C₀))
    unfold generalizedCycleOperator
    rw [generalizedCycleSymmetryOnClass_mk]
    unfold generalizedCycleSymmetry
    exact Commute.sum_right _ _ _ fun C _ =>
      commute_rootOperator_holeOperatorOfCarrier hK H C

end PauliCliqueHamiltonianRepresentation

end SimpleGraph
