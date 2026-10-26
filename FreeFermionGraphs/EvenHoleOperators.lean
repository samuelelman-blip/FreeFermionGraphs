import FreeFermionGraphs.OperatorCharges
import FreeFermionGraphs.Corollary6Induced
import FreeFermionGraphs.SimplicialModeHamiltonian
import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Even-hole carriers, `h_C`, weak separation and `J_{⟨C₀⟩}` (operator form)

This module completes the operator-level treatment of even holes in manuscript
arXiv 2305.15625 v1 (even-hole labelling and `h_C = h_{C_a} h_{C_b}`, L309-312;
compatibility, L313 (weak notion) versus L748 (strong notion); Definition 15
`definition:generalizedcyclesymmetries`, L799-803; Lemma 4 `evenholeneighbor`, L736;
Corollary 5, L749).  It builds on `FreeFermionGraphs.OperatorCharges`
(`IsEvenHoleCarrier`, `labelingOperator`, `evenHoleOperator`,
`generalizedCycleSymmetryOp`) and `FreeFermionGraphs.Corollary6Induced`
(`EvenHoleInducedCompatible`, the weak notion of v1 L313) and proves what they leave open.

## Genuine carriers are connected 2-regular induced subgraphs

An `EvenHoleLabeling` alone does not force connectivity: for `k ≥ 6` its `next` map may
split into several cycles, and the carrier is then a disjoint union of even holes.
`IsEvenHoleCarrier` (defined in `OperatorCharges` through `IndexedInducedHole`) is the
paper's even hole.  Here it is characterised graph-theoretically
(`isEvenHoleCarrier_iff_connected_two_regular`): `C` is a finite set of even cardinality at
least `4` such that `G[C]` is connected and every vertex of `C` has exactly two neighbours
in `C` (the converse direction goes through Mathlib's
`SimpleGraph.IsCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp`), and
through labellings (`isEvenHoleCarrier_iff_exists_labeling`): `C` is the carrier of an
`EvenHoleLabeling` whose induced graph is connected.

## `h_C`

* `evenHoleOperator_eq_of_colouring` : for *any* partition `(C_a, C_b)` of an even-hole
  carrier `C` into two independent sets, `h_C = h_{C_a} h_{C_b}` and the two factors
  commute (v1 L311-312: "free to exchange the ordering of `h_{C_a}` and `h_{C_b}`").
* `isSelfAdjoint_evenHoleOperator` : `h_C` is Hermitian when the terms are.
* `evenHoleOperator_commute_of_inducedCompatible` : `h_C` and `h_{C'}` commute when `C`,
  `C'` are compatible in the sense of v1 L313.

## Weak separation (v1 L313) versus strong compatibility (v1 L748)

`EvenHoleInducedCompatible` is the notion of v1 L313: `G[C ∪ C']` is the disjoint union of
`G[C]` and `G[C']`.  For hole carriers it is equivalent to `C ∩ Γ[C'] = ∅`
(`evenHoleInducedCompatible_iff_disjoint_openNeighborhood_of_isEvenHoleCarrier`), and
`evenHoleInducedCompatible_iff_components` states it literally as "the connected components
of `G[C ∪ C']` are `G[C]` and `G[C']`".  The strong notion `EvenHoleCompatible`
(`Γ[C] ∩ Γ[C'] = ∅`, v1 L748) implies it (`EvenHoleCompatible.evenHoleInducedCompatible`).
Weak separation is symmetric, invariant along deformation closures of either argument
(`evenHoleInducedCompatible_iff_of_closure`, the weak Corollary 5 of v1 L749), and never
holds for two holes of the same deformation class (`not_evenHoleInducedCompatible`).

## `J_{⟨C₀⟩}`

`isSelfAdjoint_generalizedCycleSymmetryOp` : `J_{⟨C₀⟩} = Σ_{C ∈ ⟨C₀⟩} h_C` is Hermitian when
the terms are; `generalizedCycleSymmetryOp_commute_of_inducedCompatible` : `J_{⟨C₀⟩}` and
`J_{⟨C₀'⟩}` commute for compatible holes `C₀`, `C₀'` in a claw-free graph.

The docstring of `EvenHoleCompatible` in `FreeFermionGraphs.Corollary6` states that the
strong notion is "the paper's condition that their induced union has the two holes as
separate connected components"; that is the weak notion of this module, and the strong
notion is the (strictly stronger) one recalled at v1 L748.
-/

open scoped BigOperators

universe u w

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- An injective map from `Fin k` has range of cardinality `k`. -/
theorem ncard_range_fin_of_injective {k : ℕ} (f : Fin k → V) (hf : Function.Injective f) :
    (Set.range f).ncard = k := by
  rw [← Set.image_univ, Set.ncard_image_of_injective _ hf, Set.ncard_univ,
    Nat.card_eq_fintype_card, Fintype.card_fin]

/-! ### Cardinality and neighbourhoods inside the carrier of a labelling -/

namespace EvenHoleLabeling

/-- The carrier of a labelling is finite. -/
theorem carrier_finite {k : ℕ} (L : G.EvenHoleLabeling k) : L.carrier.Finite :=
  (Set.finite_range _).union (Set.finite_range _)

/-- The two colour classes of a labelling are disjoint. -/
theorem disjoint_range_a_range_b {k : ℕ} (L : G.EvenHoleLabeling k) :
    Disjoint (Set.range L.a) (Set.range L.b) := by
  refine Set.disjoint_left.2 ?_
  rintro _ ⟨i, rfl⟩ ⟨j, hj⟩
  exact L.color_disjoint i j hj.symm

/-- The carrier of a labelling has `2k` vertices. -/
theorem carrier_ncard {k : ℕ} (L : G.EvenHoleLabeling k) : L.carrier.ncard = 2 * k := by
  unfold carrier
  rw [Set.ncard_union_eq L.disjoint_range_a_range_b (Set.finite_range _) (Set.finite_range _),
    ncard_range_fin_of_injective _ L.a_injective, ncard_range_fin_of_injective _ L.b_injective]
  omega

/-- The neighbours of `a i` inside the carrier are `b i` and `b (next i)`. -/
theorem neighborSet_inter_carrier_a {k : ℕ} (L : G.EvenHoleLabeling k) (i : Fin k) :
    G.neighborSet (L.a i) ∩ L.carrier = {L.b i, L.b (L.next i)} := by
  ext v
  simp only [Set.mem_inter_iff, mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hadj, ⟨j, rfl⟩ | ⟨j, rfl⟩⟩
    · exact (L.adj_aa i j hadj).elim
    · rcases (L.adj_ab_iff i j).1 hadj with rfl | rfl <;> simp
  · rintro (rfl | rfl)
    · exact ⟨L.adj_a_b i, L.b_mem_carrier i⟩
    · exact ⟨L.adj_a_b_next i, L.b_mem_carrier _⟩

/-- The neighbours of `b j` inside the carrier are `a j` and `a (prev j)`. -/
theorem neighborSet_inter_carrier_b {k : ℕ} (L : G.EvenHoleLabeling k) (j : Fin k) :
    G.neighborSet (L.b j) ∩ L.carrier = {L.a j, L.a (L.prev j)} := by
  ext v
  simp only [Set.mem_inter_iff, mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hadj, ⟨i, rfl⟩ | ⟨i, rfl⟩⟩
    · rcases (L.adj_ab_iff i j).1 hadj.symm with rfl | rfl
      · simp
      · simp [L.prev_next]
    · exact (L.adj_bb j i hadj).elim
  · rintro (rfl | rfl)
    · exact ⟨(L.adj_a_b j).symm, L.a_mem_carrier j⟩
    · exact ⟨(L.adj_a_prev_b j).symm, L.a_mem_carrier _⟩

/-- Every vertex of the carrier of a labelling has exactly two neighbours in the carrier
(the carrier induces a 2-regular graph, whether or not `next` is a single cycle). -/
theorem ncard_neighborSet_inter_carrier {k : ℕ} (L : G.EvenHoleLabeling k) {v : V}
    (hv : v ∈ L.carrier) : (G.neighborSet v ∩ L.carrier).ncard = 2 := by
  rcases hv with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · rw [L.neighborSet_inter_carrier_a i]
    exact Set.ncard_pair (fun h => L.next_ne i (L.b_injective h).symm)
  · rw [L.neighborSet_inter_carrier_b j]
    exact Set.ncard_pair (fun h => L.prev_ne j (L.a_injective h).symm)

/-- Inside the carrier of a labelling, adjacent vertices lie in different colour classes. -/
theorem mem_range_a_iff_not_mem_range_a_of_adj {k : ℕ} (L : G.EvenHoleLabeling k) {x y : V}
    (hx : x ∈ L.carrier) (hy : y ∈ L.carrier) (hxy : G.Adj x y) :
    x ∈ Set.range L.a ↔ y ∉ Set.range L.a := by
  constructor
  · rintro ⟨i, rfl⟩ ⟨j, rfl⟩
    exact L.adj_aa i j hxy
  · intro hya
    rcases hx with hxa | ⟨i, rfl⟩
    · exact hxa
    · rcases hy with hya' | ⟨j, rfl⟩
      · exact (hya hya').elim
      · exact (L.adj_bb i j hxy).elim

end EvenHoleLabeling

/-! ### Genuine carriers: finiteness, size, connectedness, 2-regularity -/

/-- An even-hole carrier is the carrier of a full-cyclic labelling (restatement of
`isEvenHoleCarrier_iff_exists_fullCyclic_labeling`). -/
theorem IsEvenHoleCarrier.exists_fullCyclic_labeling {C : Set V} (hC : G.IsEvenHoleCarrier C) :
    ∃ (k : ℕ) (L : G.EvenHoleLabeling k), L.HasFullCyclicOrder ∧ L.carrier = C :=
  (isEvenHoleCarrier_iff_exists_fullCyclic_labeling C).1 hC

/-- An even-hole carrier is finite. -/
theorem IsEvenHoleCarrier.finite {C : Set V} (hC : G.IsEvenHoleCarrier C) : C.Finite := by
  obtain ⟨k, L, -, rfl⟩ := hC.exists_fullCyclic_labeling
  exact L.carrier_finite

/-- An even-hole carrier has `2k` vertices for some `k ≥ 2`. -/
theorem IsEvenHoleCarrier.exists_ncard_eq {C : Set V} (hC : G.IsEvenHoleCarrier C) :
    ∃ k : ℕ, 2 ≤ k ∧ C.ncard = 2 * k := by
  obtain ⟨k, L, -, rfl⟩ := hC.exists_fullCyclic_labeling
  exact ⟨k, L.two_le, L.carrier_ncard⟩

/-- An even hole has even length. -/
theorem IsEvenHoleCarrier.even_ncard {C : Set V} (hC : G.IsEvenHoleCarrier C) :
    Even C.ncard := by
  obtain ⟨k, -, hk⟩ := hC.exists_ncard_eq
  exact ⟨k, by omega⟩

/-- An even hole has length at least `4`. -/
theorem IsEvenHoleCarrier.four_le_ncard {C : Set V} (hC : G.IsEvenHoleCarrier C) :
    4 ≤ C.ncard := by
  obtain ⟨k, hk, hC⟩ := hC.exists_ncard_eq
  omega

/-- An even-hole carrier is nonempty. -/
theorem IsEvenHoleCarrier.nonempty {C : Set V} (hC : G.IsEvenHoleCarrier C) : C.Nonempty :=
  Set.nonempty_of_ncard_ne_zero (by have := hC.four_le_ncard; omega)

/-- Every vertex of an even-hole carrier has exactly two neighbours in the carrier. -/
theorem IsEvenHoleCarrier.ncard_neighborSet_inter {C : Set V} (hC : G.IsEvenHoleCarrier C)
    {v : V} (hv : v ∈ C) : (G.neighborSet v ∩ C).ncard = 2 := by
  obtain ⟨k, L, -, rfl⟩ := hC.exists_fullCyclic_labeling
  exact L.ncard_neighborSet_inter_carrier hv

/-- The carrier of an even hole is contained in its own open neighbourhood. -/
theorem IsEvenHoleCarrier.subset_openNeighborhood {C : Set V} (hC : G.IsEvenHoleCarrier C) :
    C ⊆ G.openNeighborhood C := by
  obtain ⟨k, L, -, rfl⟩ := hC.exists_fullCyclic_labeling
  exact L.carrier_subset_openNeighborhood

/-- The graph induced on an even-hole carrier is connected. -/
theorem IsEvenHoleCarrier.connected_induce {C : Set V} (hC : G.IsEvenHoleCarrier C) :
    (G.induce C).Connected := by
  obtain ⟨x₀, hx₀⟩ := hC.nonempty
  have key := hC.pred_iff
    (fun x => ∃ hx : x ∈ C, (G.induce C).Reachable ⟨x₀, hx₀⟩ ⟨x, hx⟩) ?_
  · rw [connected_iff]
    refine ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ => ?_, ⟨⟨x₀, hx₀⟩⟩⟩
    have hx' : (G.induce C).Reachable ⟨x₀, hx₀⟩ ⟨x, hx⟩ :=
      ((key x₀ hx₀ x hx).1 ⟨hx₀, Reachable.refl _⟩).2
    have hy' : (G.induce C).Reachable ⟨x₀, hx₀⟩ ⟨y, hy⟩ :=
      ((key x₀ hx₀ y hy).1 ⟨hx₀, Reachable.refl _⟩).2
    exact hx'.symm.trans hy'
  · intro x hx y hy hxy
    constructor
    · rintro ⟨hx', hr⟩
      exact ⟨hy, hr.trans (Adj.reachable (show (G.induce C).Adj ⟨x, hx⟩ ⟨y, hy⟩ from hxy))⟩
    · rintro ⟨hy', hr⟩
      exact ⟨hx, hr.trans (Adj.reachable (show (G.induce C).Adj ⟨y, hy⟩ ⟨x, hx⟩ from hxy.symm))⟩

/-- A finite set of even cardinality at least `4` that induces a connected 2-regular graph
is an even-hole carrier: it is the vertex set of an indexed induced hole of even length.
The cyclic order comes from Mathlib's
`SimpleGraph.IsCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp` applied to
`G[C]`. -/
theorem isEvenHoleCarrier_of_connected_two_regular {C : Set V} (hfin : C.Finite)
    (hev : Even C.ncard) (h4 : 4 ≤ C.ncard) (hconn : (G.induce C).Connected)
    (hreg : ∀ v ∈ C, (G.neighborSet v ∩ C).ncard = 2) : G.IsEvenHoleCarrier C := by
  classical
  haveI : Finite C := hfin.to_subtype
  have hreg' : ∀ v : C, ((G.induce C).neighborSet v).ncard = 2 := by
    intro v
    have himg : Subtype.val '' (G.induce C).neighborSet v = G.neighborSet v.1 ∩ C := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨hy, y.2⟩
      · rintro ⟨hx, hxC⟩
        exact ⟨⟨x, hxC⟩, hx, rfl⟩
    rw [← Set.ncard_image_of_injective _ Subtype.val_injective, himg]
    exact hreg v.1 v.2
  have hcyc : (G.induce C).IsCycles := fun v _ => hreg' v
  obtain ⟨v₀⟩ := hconn.nonempty
  have hv₀ : v₀ ∈ ((G.induce C).connectedComponentMk v₀).supp := rfl
  have hn : ((G.induce C).neighborSet v₀).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [hreg' v₀]; norm_num)
  obtain ⟨p, hp, hverts⟩ := hcyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp hv₀ hn
  have hn3 : 3 ≤ p.length := hp.three_le_length
  have hcover : ∀ x : C, ∃ i, i < p.length ∧ p.getVert i = x := by
    intro x
    have hx : x ∈ p.toSubgraph.verts := by
      rw [hverts]
      exact (ConnectedComponent.mem_supp_iff _ _).2
        (ConnectedComponent.eq.2 (hconn.preconnected x v₀))
    rw [Walk.mem_verts_toSubgraph, Walk.mem_support_iff_exists_getVert] at hx
    obtain ⟨i, hi, hle⟩ := hx
    rcases hle.lt_or_eq with hlt | heq
    · exact ⟨i, hlt, hi⟩
    · refine ⟨0, by omega, ?_⟩
      rw [Walk.getVert_zero, ← hi, heq, Walk.getVert_length]
  have hinj : ∀ i j, i < p.length → j < p.length → p.getVert i = p.getVert j → i = j :=
    fun i j hi hj h =>
      hp.getVert_injOn' (show i ≤ p.length - 1 by omega) (show j ≤ p.length - 1 by omega) h
  have hidx : ∀ a b, a ≤ p.length → b < p.length → p.getVert a = p.getVert b →
      a = b ∨ (a = p.length ∧ b = 0) := by
    intro a b ha hb h
    rcases ha.lt_or_eq with hlt | heq
    · exact Or.inl (hinj a b hlt hb h)
    · refine Or.inr ⟨heq, ?_⟩
      have h0 : p.getVert p.length = p.getVert 0 := by simp
      rw [heq] at h
      exact (hinj 0 b (by omega) hb (h0.symm.trans h)).symm
  let f : Fin p.length → V := fun i => (p.getVert i.val).1
  have hfinj : Function.Injective f := fun i j h =>
    Fin.ext (hinj _ _ i.2 j.2 (Subtype.ext h))
  have hrange : Set.range f = C := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (p.getVert i.val).2
    · intro hx
      obtain ⟨i, hi, hix⟩ := hcover ⟨x, hx⟩
      exact ⟨⟨i, hi⟩, by simp [f, hix]⟩
  have hlen : p.length = C.ncard :=
    (ncard_range_fin_of_injective f hfinj).symm.trans (by rw [hrange])
  have hwrap : p.getVert p.length = p.getVert 0 := by simp
  have hsub : ∀ x y : C, (G.induce C).Adj x y → p.toSubgraph.Adj x y := by
    intro x y hxy
    obtain ⟨i, hi, hix⟩ := hcover x
    have hxs : x ∈ p.support := by
      rw [Walk.mem_support_iff_exists_getVert]
      exact ⟨i, hix, hi.le⟩
    have h2 := hp.ncard_neighborSet_toSubgraph_eq_two hxs
    have heq : p.toSubgraph.neighborSet x = (G.induce C).neighborSet x :=
      Set.eq_of_subset_of_ncard_le (p.toSubgraph.neighborSet_subset x)
        (by rw [h2, hreg' x]) (Set.toFinite _)
    have : y ∈ p.toSubgraph.neighborSet x := by rw [heq]; exact hxy
    exact this
  have hsucc : ∀ m, m < p.length → G.Adj (p.getVert m).1 (p.getVert (m + 1)).1 :=
    fun m hm => p.adj_getVert_succ hm
  refine ⟨{ card := p.length, four_le_card := by omega, vertex := f, injective := hfinj,
            adj_iff := ?_ },
    (show Even p.length from hlen ▸ hev), hrange⟩
  intro i j
  have hadj0 : G.Adj (f i) (f j) ↔ (G.induce C).Adj (p.getVert i.val) (p.getVert j.val) :=
    Iff.rfl
  rw [hadj0]
  constructor
  · intro hij
    obtain ⟨m, hm, hmlt⟩ := (Walk.toSubgraph_adj_iff p).1 (hsub _ _ hij)
    rw [Sym2.eq_iff] at hm
    unfold CyclicAdjacent
    rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hmi : m = i.val := hinj m i.val hmlt i.2 h1
      rcases hidx (m + 1) j.val (by omega) j.2 h2 with h | ⟨h, h'⟩
      · omega
      · omega
    · have hmj : m = j.val := hinj m j.val hmlt j.2 h1
      rcases hidx (m + 1) i.val (by omega) i.2 h2 with h | ⟨h, h'⟩
      · omega
      · omega
  · intro hij
    unfold CyclicAdjacent at hij
    rcases hij with h | h | ⟨h0, h1⟩ | ⟨h0, h1⟩
    · have := hsucc i.val i.2
      rw [h] at this
      exact this
    · have := hsucc j.val j.2
      rw [h] at this
      exact this.symm
    · have := hsucc j.val j.2
      rw [h1, hwrap, ← h0] at this
      exact this.symm
    · have := hsucc i.val i.2
      rw [h1, hwrap, ← h0] at this
      exact this

/-- **Even holes are the connected 2-regular induced subgraphs of even order** (v1 L305,
L309: an induced cycle of even length `≥ 4`).  A set `C` is an even-hole carrier iff it is
finite, of even cardinality at least `4`, `G[C]` is connected, and every vertex of `C` has
exactly two neighbours in `C`. -/
theorem isEvenHoleCarrier_iff_connected_two_regular {C : Set V} :
    G.IsEvenHoleCarrier C ↔
      C.Finite ∧ Even C.ncard ∧ 4 ≤ C.ncard ∧ (G.induce C).Connected ∧
        ∀ v ∈ C, (G.neighborSet v ∩ C).ncard = 2 :=
  ⟨fun h => ⟨h.finite, h.even_ncard, h.four_le_ncard, h.connected_induce,
      fun _ hv => h.ncard_neighborSet_inter hv⟩,
    fun ⟨hf, he, h4, hc, hr⟩ => isEvenHoleCarrier_of_connected_two_regular hf he h4 hc hr⟩

/-- **Labelling bridge** (alternating labelling `b₀-a₀-b₁-⋯`, v1 L309): `C` is an even hole
iff it is the carrier of an `EvenHoleLabeling` whose induced graph is connected.  The
connectedness requirement cannot be dropped: an `EvenHoleLabeling` alone may have a
carrier that is a disjoint union of several even holes (`next` need not be one cycle). -/
theorem isEvenHoleCarrier_iff_exists_labeling {C : Set V} :
    G.IsEvenHoleCarrier C ↔
      ∃ (k : ℕ) (L : G.EvenHoleLabeling k), L.carrier = C ∧ (G.induce C).Connected := by
  constructor
  · intro hC
    obtain ⟨k, L, -, hL⟩ := hC.exists_fullCyclic_labeling
    exact ⟨k, L, hL, hC.connected_induce⟩
  · rintro ⟨k, L, rfl, hconn⟩
    refine isEvenHoleCarrier_of_connected_two_regular L.carrier_finite ?_ ?_ hconn
      (fun v hv => L.ncard_neighborSet_inter_carrier hv)
    · rw [L.carrier_ncard]
      exact even_two_mul k
    · rw [L.carrier_ncard]
      have := L.two_le
      omega

namespace EvenHoleLabeling

/-- A labelling with connected carrier has full cyclic order, i.e. its carrier is a single
even hole (without connectedness, `next` may split into several cycles). -/
theorem hasFullCyclicOrder_of_connected {k : ℕ} (L : G.EvenHoleLabeling k)
    (hconn : (G.induce L.carrier).Connected) : L.HasFullCyclicOrder :=
  L.hasFullCyclicOrder_of_isEvenHoleCarrier
    (isEvenHoleCarrier_iff_exists_labeling.2 ⟨k, L, rfl, hconn⟩)

end EvenHoleLabeling

/-! ### Two-colourings of an even hole are unique up to a swap -/

namespace EvenHoleLabeling

/-- Any partition of the carrier of a full-cyclic labelling into two independent sets is
the pair of colour classes of the labelling, in one order or the other (a connected
bipartite graph has a unique bipartition up to swapping; v1 L311: "the two unique
independent sets of size `k` in `C`, which are the coloring classes of `C`"). -/
theorem eq_or_swap_of_partition {k : ℕ} (L : G.EvenHoleLabeling k)
    (hC : G.IsEvenHoleCarrier L.carrier) {A B : Set V} (hcov : A ∪ B = L.carrier)
    (hd : Disjoint A B) (hA : G.IsIndepSet A) (hB : G.IsIndepSet B) :
    (A = Set.range L.a ∧ B = Set.range L.b) ∨ (A = Set.range L.b ∧ B = Set.range L.a) := by
  have hmem : ∀ x, x ∈ L.carrier ↔ (x ∈ Set.range L.a ∨ x ∈ Set.range L.b) :=
    fun x => Iff.rfl
  have hcovx : ∀ x, x ∈ L.carrier ↔ (x ∈ A ∨ x ∈ B) := fun x => by rw [← hcov]; rfl
  have hdAB : ∀ x, ¬ (x ∈ A ∧ x ∈ B) := fun x ⟨h1, h2⟩ => Set.disjoint_left.1 hd h1 h2
  have hdab : ∀ x, ¬ (x ∈ Set.range L.a ∧ x ∈ Set.range L.b) := fun x ⟨h1, h2⟩ =>
    Set.disjoint_left.1 L.disjoint_range_a_range_b h1 h2
  have hAflip : ∀ x ∈ L.carrier, ∀ y ∈ L.carrier, G.Adj x y → (x ∈ A ↔ y ∉ A) := by
    intro x hx y hy hxy
    have hne : x ≠ y := hxy.ne
    constructor
    · intro hxA hyA
      exact hA hxA hyA hne hxy
    · intro hyA
      rcases (hcovx x).1 hx with h | h
      · exact h
      · rcases (hcovx y).1 hy with h' | h'
        · exact (hyA h').elim
        · exact (hB h h' hne hxy).elim
  let P : V → Prop := fun x => x ∈ A ↔ x ∈ Set.range L.a
  have hP : ∀ x ∈ L.carrier, ∀ y ∈ L.carrier, G.Adj x y → (P x ↔ P y) := by
    intro x hx y hy hxy
    have h1 := hAflip x hx y hy hxy
    have h2 := L.mem_range_a_iff_not_mem_range_a_of_adj hx hy hxy
    simp only [P]
    tauto
  have hconst := hC.pred_iff P hP
  obtain ⟨x₀, hx₀⟩ := hC.nonempty
  by_cases h0 : P x₀
  · left
    have hall : ∀ x ∈ L.carrier, P x := fun x hx => (hconst x₀ hx₀ x hx).1 h0
    constructor
    · ext x
      by_cases hx : x ∈ L.carrier
      · exact hall x hx
      · have h1 := hcovx x
        have h2 := hmem x
        tauto
    · ext x
      by_cases hx : x ∈ L.carrier
      · have h3 := hall x hx
        have h1 := hcovx x
        have h2 := hmem x
        have h4 := hdAB x
        have h5 := hdab x
        simp only [P] at h3
        tauto
      · have h1 := hcovx x
        have h2 := hmem x
        tauto
  · right
    have hall : ∀ x ∈ L.carrier, ¬ P x := fun x hx hPx => h0 ((hconst x₀ hx₀ x hx).2 hPx)
    constructor
    · ext x
      by_cases hx : x ∈ L.carrier
      · have h3 := hall x hx
        have h1 := hcovx x
        have h2 := hmem x
        have h4 := hdAB x
        have h5 := hdab x
        simp only [P] at h3
        tauto
      · have h1 := hcovx x
        have h2 := hmem x
        tauto
    · ext x
      by_cases hx : x ∈ L.carrier
      · have h3 := hall x hx
        have h1 := hcovx x
        have h2 := hmem x
        have h4 := hdAB x
        have h5 := hdab x
        simp only [P] at h3
        tauto
      · have h1 := hcovx x
        have h2 := hmem x
        tauto

/-- Membership in the `a`-colour class finset implies membership in the carrier. -/
theorem mem_carrier_of_mem_image_a [DecidableEq V] {k : ℕ} (L : G.EvenHoleLabeling k) {x : V}
    (hx : x ∈ (Finset.univ.image L.a : Finset V)) : x ∈ L.carrier := by
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
  exact L.a_mem_carrier i

/-- Membership in the `b`-colour class finset implies membership in the carrier. -/
theorem mem_carrier_of_mem_image_b [DecidableEq V] {k : ℕ} (L : G.EvenHoleLabeling k) {x : V}
    (hx : x ∈ (Finset.univ.image L.b : Finset V)) : x ∈ L.carrier := by
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
  exact L.b_mem_carrier i

end EvenHoleLabeling

/-- No edge between `S` and `T` means the cross count vanishes. -/
theorem crossCount_eq_zero_of_no_edges {S T : Finset V}
    (h : ∀ x ∈ S, ∀ y ∈ T, ¬ G.Adj x y) : G.crossCount S T = 0 := by
  classical
  rw [crossCount_eq_card_filter, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨x, y⟩ hxy
  rw [Finset.mem_product] at hxy
  exact h x hxy.1 y hxy.2

/-! ### The operator `h_C` -/

namespace PauliFrustrationRepresentation

variable {A : Type w} [Ring A]

/-- Products over two independent sets with no edge between them commute. -/
theorem independentProduct_commute_of_no_edges [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) {S T : Finset V}
    (hS : G.IsIndepSet (S : Set V)) (hT : G.IsIndepSet (T : Set V))
    (hST : ∀ x ∈ S, ∀ y ∈ T, ¬ G.Adj x y) :
    Commute (H.independentProduct S) (H.independentProduct T) :=
  H.independentProduct_mul_independentProduct_of_even hS hT
    (by rw [G.crossCount_eq_zero_of_no_edges hST]; exact ⟨0, rfl⟩)

/-- **Colouring independence of `h_C`** (v1 L309-312).  For every partition `(C_a, C_b)` of
an even-hole carrier `C` into two independent sets (the two colour classes, named in either
order), `h_C = h_{C_a} h_{C_b}`, and the two factors commute: "we are free to exchange the
ordering of `h_{C_a}` and `h_{C_b}`, as these operators commute". -/
theorem evenHoleOperator_eq_of_colouring [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) {C : Set V} (hC : G.IsEvenHoleCarrier C)
    {Ca Cb : Finset V} (hcov : (Ca : Set V) ∪ Cb = C) (hd : Disjoint Ca Cb)
    (ha : G.IsIndepSet (Ca : Set V)) (hb : G.IsIndepSet (Cb : Set V)) :
    H.evenHoleOperator C = H.independentProduct Ca * H.independentProduct Cb ∧
      Commute (H.independentProduct Ca) (H.independentProduct Cb) := by
  obtain ⟨k, L, hL, rfl⟩ := hC.exists_fullCyclic_labeling
  have hop : H.evenHoleOperator L.carrier =
      H.independentProduct (Finset.univ.image L.a) *
        H.independentProduct (Finset.univ.image L.b) := H.evenHoleOperator_eq L hL
  have hcomm := H.labelingOperator_comm L
  have hdisj : Disjoint (Ca : Set V) (Cb : Set V) := Finset.disjoint_coe.2 hd
  rcases L.eq_or_swap_of_partition hC hcov hdisj ha hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have e1 : Ca = Finset.univ.image L.a := Finset.coe_injective (by rw [h1]; simp)
    have e2 : Cb = Finset.univ.image L.b := Finset.coe_injective (by rw [h2]; simp)
    subst e1
    subst e2
    exact ⟨hop, hcomm⟩
  · have e1 : Ca = Finset.univ.image L.b := Finset.coe_injective (by rw [h1]; simp)
    have e2 : Cb = Finset.univ.image L.a := Finset.coe_injective (by rw [h2]; simp)
    subst e1
    subst e2
    exact ⟨hop.trans hcomm, hcomm.symm⟩

/-- `h_C` and `h_{C'}` commute when `G[C ∪ C']` is the disjoint union of `G[C]` and
`G[C']` (the compatibility of v1 L313).  If one of the sets is not an even-hole carrier,
`evenHoleOperator` is `0` and the statement is trivial. -/
theorem evenHoleOperator_commute_of_inducedCompatible [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) {C C' : Set V}
    (h : G.EvenHoleInducedCompatible C C') :
    Commute (H.evenHoleOperator C) (H.evenHoleOperator C') := by
  by_cases hC : G.IsEvenHoleCarrier C
  swap
  · rw [H.evenHoleOperator_eq_zero_of_not_isEvenHoleCarrier hC]
    exact Commute.zero_left _
  by_cases hC' : G.IsEvenHoleCarrier C'
  swap
  · rw [H.evenHoleOperator_eq_zero_of_not_isEvenHoleCarrier hC']
    exact Commute.zero_right _
  obtain ⟨k, L, hL, rfl⟩ := hC.exists_fullCyclic_labeling
  obtain ⟨k', L', hL', rfl⟩ := hC'.exists_fullCyclic_labeling
  rw [H.evenHoleOperator_eq L hL, H.evenHoleOperator_eq L' hL']
  have key : ∀ {S T : Finset V}, (∀ x ∈ S, x ∈ L.carrier) → (∀ y ∈ T, y ∈ L'.carrier) →
      G.IsIndepSet (S : Set V) → G.IsIndepSet (T : Set V) →
      Commute (H.independentProduct S) (H.independentProduct T) :=
    fun hS hT iS iT =>
      H.independentProduct_commute_of_no_edges iS iT fun x hx y hy => h.2 (hS x hx) (hT y hy)
  unfold labelingOperator
  exact Commute.mul_left
    (Commute.mul_right
      (key (fun _ => L.mem_carrier_of_mem_image_a) (fun _ => L'.mem_carrier_of_mem_image_a)
        L.isIndepSet_image_a L'.isIndepSet_image_a)
      (key (fun _ => L.mem_carrier_of_mem_image_a) (fun _ => L'.mem_carrier_of_mem_image_b)
        L.isIndepSet_image_a L'.isIndepSet_image_b))
    (Commute.mul_right
      (key (fun _ => L.mem_carrier_of_mem_image_b) (fun _ => L'.mem_carrier_of_mem_image_a)
        L.isIndepSet_image_b L'.isIndepSet_image_a)
      (key (fun _ => L.mem_carrier_of_mem_image_b) (fun _ => L'.mem_carrier_of_mem_image_b)
        L.isIndepSet_image_b L'.isIndepSet_image_b))

section Star

variable [StarRing A]

/-- `h_{C_a} h_{C_b}` is Hermitian when the terms are: both factors are Hermitian and
commute. -/
theorem isSelfAdjoint_labelingOperator [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) (hstar : ∀ j, IsSelfAdjoint (H.term j))
    {k : ℕ} (L : G.EvenHoleLabeling k) : IsSelfAdjoint (H.labelingOperator L) := by
  have ha := H.isSelfAdjoint_independentProduct_of_terms hstar L.isIndepSet_image_a
  have hb := H.isSelfAdjoint_independentProduct_of_terms hstar L.isIndepSet_image_b
  unfold IsSelfAdjoint labelingOperator
  rw [star_mul, ha.star_eq, hb.star_eq]
  exact (H.labelingOperator_comm L).symm

/-- `h_C` is Hermitian when the terms are Hermitian (v1 proof of Theorem 2 omits this:
"`h_C = h_{C_a} h_{C_b}` Hermitian because the colour classes commute"). -/
theorem isSelfAdjoint_evenHoleOperator [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) (hstar : ∀ j, IsSelfAdjoint (H.term j))
    (C : Set V) : IsSelfAdjoint (H.evenHoleOperator C) := by
  by_cases hC : G.IsEvenHoleCarrier C
  · obtain ⟨k, L, hL, rfl⟩ := hC.exists_fullCyclic_labeling
    rw [H.evenHoleOperator_eq L hL]
    exact H.isSelfAdjoint_labelingOperator hstar L
  · rw [H.evenHoleOperator_eq_zero_of_not_isEvenHoleCarrier hC]
    exact IsSelfAdjoint.zero A

/-- **`J_{⟨C₀⟩}` is Hermitian when the terms are** (Definition 15, v1 L799-803). -/
theorem isSelfAdjoint_generalizedCycleSymmetryOp [Fintype V] [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) (hstar : ∀ j, IsSelfAdjoint (H.term j))
    (C₀ : Set V) : IsSelfAdjoint (H.generalizedCycleSymmetryOp C₀) := by
  unfold generalizedCycleSymmetryOp generalizedCycleSymmetry
  exact Finset.sum_induction _ (fun x : A => IsSelfAdjoint x) (fun a b ha hb => ha.add hb)
    (IsSelfAdjoint.zero A) (fun C _ => H.isSelfAdjoint_evenHoleOperator hstar C)

end Star

end PauliFrustrationRepresentation

/-! ### Weak separation (v1 L313) and weak Corollary 5 (v1 L749) -/

/-- For an even-hole carrier `C'`, the weak compatibility of v1 L313 is `C ∩ Γ[C'] = ∅`
(here `Γ[C'] = G.openNeighborhood C'`, which contains `C'`). -/
theorem evenHoleInducedCompatible_iff_disjoint_openNeighborhood_of_isEvenHoleCarrier
    {C C' : Set V} (hC' : G.IsEvenHoleCarrier C') :
    G.EvenHoleInducedCompatible C C' ↔ Disjoint C (G.openNeighborhood C') :=
  evenHoleInducedCompatible_iff_disjoint_openNeighborhood hC'.subset_openNeighborhood

/-- Strong compatibility (disjoint open neighbourhoods, v1 L748; repository
`EvenHoleCompatible`) implies the weak notion of v1 L313.  Only the carrier `C` needs to
be an even hole.  The converse fails (`exists_evenHoleInducedCompatible_not_evenHoleCompatible`). -/
theorem EvenHoleCompatible.evenHoleInducedCompatible {C C' : Set V}
    (hC : G.IsEvenHoleCarrier C) (h : G.EvenHoleCompatible C C') :
    G.EvenHoleInducedCompatible C C' := by
  have hCN := hC.subset_openNeighborhood
  refine ⟨?_, fun x y hx hy hxy => ?_⟩
  · refine Set.disjoint_left.2 fun x hxC hxC' => ?_
    obtain ⟨y, hyC, hxy⟩ := hCN hxC
    exact Set.disjoint_left.1 h (hCN hyC) ⟨x, hxC', hxy.symm⟩
  · exact Set.disjoint_left.1 h (hCN hx) ⟨y, hy, hxy⟩

/-- Weak compatibility with the second argument is invariant along its deformation
closure (v1 Corollary 5, L749, for the notion of v1 L313). -/
theorem InEvenHoleDeformationClosure.evenHoleInducedCompatible_right_iff_of_isEvenHoleCarrier
    {A B C : Set V} (hclo : InEvenHoleDeformationClosure G A B) (hclaw : G.IsClawFree)
    (hA : G.IsEvenHoleCarrier A) :
    G.EvenHoleInducedCompatible C A ↔ G.EvenHoleInducedCompatible C B := by
  rw [evenHoleInducedCompatible_iff_disjoint_openNeighborhood hA.subset_openNeighborhood,
    evenHoleInducedCompatible_iff_disjoint_openNeighborhood
      (hclo.subset_openNeighborhood hA.subset_openNeighborhood),
    hclo.openNeighborhood_eq hclaw]

/-- Weak compatibility with the first argument is invariant along its deformation closure. -/
theorem InEvenHoleDeformationClosure.evenHoleInducedCompatible_left_iff_of_isEvenHoleCarrier
    {A B C : Set V} (hclo : InEvenHoleDeformationClosure G A B) (hclaw : G.IsClawFree)
    (hA : G.IsEvenHoleCarrier A) :
    G.EvenHoleInducedCompatible A C ↔ G.EvenHoleInducedCompatible B C :=
  evenHoleInducedCompatible_comm.trans
    ((hclo.evenHoleInducedCompatible_right_iff_of_isEvenHoleCarrier hclaw hA).trans
      evenHoleInducedCompatible_comm)

/-- **Weak Corollary 5, both arguments** (v1 L749 for the notion of v1 L313): in a claw-free
graph the weak compatibility of two even holes only depends on their deformation classes. -/
theorem evenHoleInducedCompatible_iff_of_closure {A A' B B' : Set V}
    (hA : InEvenHoleDeformationClosure G A A') (hB : InEvenHoleDeformationClosure G B B')
    (hclaw : G.IsClawFree) (hAc : G.IsEvenHoleCarrier A) (hBc : G.IsEvenHoleCarrier B) :
    G.EvenHoleInducedCompatible A B ↔ G.EvenHoleInducedCompatible A' B' :=
  (hB.evenHoleInducedCompatible_right_iff_of_isEvenHoleCarrier hclaw hBc).trans
    (hA.evenHoleInducedCompatible_left_iff_of_isEvenHoleCarrier hclaw hAc)

/-- Two even holes of the same deformation class are never compatible: every vertex of `A`
has a neighbour in `B`, because `Γ(A) = Γ(B)` (Lemma 4, v1 L736). -/
theorem InEvenHoleDeformationClosure.not_evenHoleInducedCompatible {A B : Set V}
    (hclo : InEvenHoleDeformationClosure G A B) (hclaw : G.IsClawFree)
    (hA : G.IsEvenHoleCarrier A) : ¬ G.EvenHoleInducedCompatible A B := by
  rintro ⟨-, hno⟩
  obtain ⟨x, hx⟩ := hA.nonempty
  have hx' : x ∈ G.openNeighborhood B := by
    rw [← hclo.openNeighborhood_eq hclaw]
    exact hA.subset_openNeighborhood hx
  obtain ⟨y, hy, hxy⟩ := hx'
  exact hno hx hy hxy

/-- Two (possibly equal) members of the deformation class `⟨C₀⟩` of an even hole are never
compatible. -/
theorem not_evenHoleInducedCompatible_of_mem_closure {C₀ A B : Set V}
    (hC₀ : G.IsEvenHoleCarrier C₀) (hclaw : G.IsClawFree)
    (hA : InEvenHoleDeformationClosure G C₀ A) (hB : InEvenHoleDeformationClosure G C₀ B) :
    ¬ G.EvenHoleInducedCompatible A B :=
  (hA.symm.trans hB).not_evenHoleInducedCompatible hclaw (hA.isEvenHoleCarrier hC₀)

/-- If `G[D]` is connected and `D ⊆ S`, any two vertices of `D` are reachable from each other
in `G[S]`. -/
theorem reachable_induce_of_connected_induce {S D : Set V} (hD : (G.induce D).Connected)
    (hDS : D ⊆ S) {z w : V} (hz : z ∈ D) (hw : w ∈ D) :
    (G.induce S).Reachable ⟨z, hDS hz⟩ ⟨w, hDS hw⟩ :=
  (hD.preconnected ⟨z, hz⟩ ⟨w, hw⟩).map (G.induceHomOfLE hDS).toHom

/-- **The weak compatibility is the literal definition of v1 L313.**  For even holes
`C`, `C'`, the relation `EvenHoleInducedCompatible` holds iff `G[C ∪ C']` is a disconnected
graph whose components are `G[C]` and `G[C']`: it has exactly two connected components, with
vertex sets `C` and `C'`. -/
theorem evenHoleInducedCompatible_iff_components {C C' : Set V}
    (hC : G.IsEvenHoleCarrier C) (hC' : G.IsEvenHoleCarrier C') :
    G.EvenHoleInducedCompatible C C' ↔
      ∃ c c' : (G.induce (C ∪ C')).ConnectedComponent, c ≠ c' ∧ (∀ d, d = c ∨ d = c') ∧
        Subtype.val '' c.supp = C ∧ Subtype.val '' c'.supp = C' := by
  constructor
  · rintro ⟨hd, hno⟩
    obtain ⟨x₀, hx₀⟩ := hC.nonempty
    obtain ⟨y₀, hy₀⟩ := hC'.nonempty
    have hCS : C ⊆ C ∪ C' := Set.subset_union_left
    have hC'S : C' ⊆ C ∪ C' := Set.subset_union_right
    have hflip : ∀ x y : ↥(C ∪ C'), (G.induce (C ∪ C')).Adj x y → (x.1 ∈ C ↔ y.1 ∈ C) := by
      intro x y hxy
      rcases x.2 with hx | hx <;> rcases y.2 with hy | hy
      · exact ⟨fun _ => hy, fun _ => hx⟩
      · exact (hno hx hy hxy).elim
      · exact (hno hy hx hxy.symm).elim
      · exact ⟨fun h => (Set.disjoint_left.1 hd h hx).elim,
          fun h => (Set.disjoint_left.1 hd h hy).elim⟩
    have hwalk : ∀ {x y : ↥(C ∪ C')} (w : (G.induce (C ∪ C')).Walk x y), (x.1 ∈ C ↔ y.1 ∈ C) := by
      intro x y w
      induction w with
      | nil => exact Iff.rfl
      | cons hadj _ ih => exact (hflip _ _ hadj).trans ih
    have hreach : ∀ x y : ↥(C ∪ C'), (G.induce (C ∪ C')).Reachable x y → (x.1 ∈ C ↔ y.1 ∈ C) :=
      fun x y ⟨w⟩ => hwalk w
    refine ⟨(G.induce (C ∪ C')).connectedComponentMk ⟨x₀, hCS hx₀⟩,
      (G.induce (C ∪ C')).connectedComponentMk ⟨y₀, hC'S hy₀⟩, ?_, ?_, ?_, ?_⟩
    · intro hcc
      have h := hreach _ _ (ConnectedComponent.eq.1 hcc)
      exact Set.disjoint_left.1 hd (h.1 hx₀) hy₀
    · intro d
      refine ConnectedComponent.ind (fun y => ?_) d
      rcases y.2 with hy | hy
      · exact Or.inl (ConnectedComponent.eq.2
          (reachable_induce_of_connected_induce hC.connected_induce hCS hy hx₀))
      · exact Or.inr (ConnectedComponent.eq.2
          (reachable_induce_of_connected_induce hC'.connected_induce hC'S hy hy₀))
    · ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (hreach y _ (ConnectedComponent.eq.1 hy)).2 hx₀
      · intro hz
        exact ⟨⟨z, hCS hz⟩, ConnectedComponent.eq.2
          (reachable_induce_of_connected_induce hC.connected_induce hCS hz hx₀), rfl⟩
    · ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        have h := (hreach y _ (ConnectedComponent.eq.1 hy))
        rcases y.2 with hyC | hyC'
        · exact (Set.disjoint_left.1 hd (h.1 hyC) hy₀).elim
        · exact hyC'
      · intro hz
        exact ⟨⟨z, hC'S hz⟩, ConnectedComponent.eq.2
          (reachable_induce_of_connected_induce hC'.connected_induce hC'S hz hy₀), rfl⟩
  · rintro ⟨c, c', hne, -, hc, hc'⟩
    refine ⟨Set.disjoint_left.2 fun z hzC hzC' => ?_, fun x y hx hy hxy => ?_⟩
    · have hz1 : z ∈ Subtype.val '' c.supp := by rw [hc]; exact hzC
      have hz2 : z ∈ Subtype.val '' c'.supp := by rw [hc']; exact hzC'
      obtain ⟨u, hu, rfl⟩ := hz1
      obtain ⟨u', hu', hu'u⟩ := hz2
      have hu'' : u' = u := Subtype.ext hu'u
      subst hu''
      exact hne (((ConnectedComponent.mem_supp_iff _ _).1 hu).symm.trans
        ((ConnectedComponent.mem_supp_iff _ _).1 hu'))
    · have hx1 : x ∈ Subtype.val '' c.supp := by rw [hc]; exact hx
      have hy1 : y ∈ Subtype.val '' c'.supp := by rw [hc']; exact hy
      obtain ⟨u, hu, rfl⟩ := hx1
      obtain ⟨w, hw, rfl⟩ := hy1
      have hxy' : (G.induce (C ∪ C')).Adj u w := hxy
      exact hne (((ConnectedComponent.mem_supp_iff _ _).1 hu).symm.trans
        ((ConnectedComponent.eq.2 hxy'.reachable).trans
          ((ConnectedComponent.mem_supp_iff _ _).1 hw)))

/-! ### Commutation of generalized cycle symmetries -/

namespace PauliFrustrationRepresentation

variable {A : Type w} [Ring A]

/-- `J_{⟨C₀⟩}` and `J_{⟨C₀'⟩}` commute when the even holes `C₀`, `C₀'` are compatible
(v1 L313) in a claw-free graph: every pair of members is compatible (weak Corollary 5), so
all the terms `h_C`, `h_{C'}` commute. -/
theorem generalizedCycleSymmetryOp_commute_of_inducedCompatible [Fintype V] [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) (hclaw : G.IsClawFree) {C₀ C₀' : Set V}
    (h₀ : G.IsEvenHoleCarrier C₀) (h₀' : G.IsEvenHoleCarrier C₀')
    (h : G.EvenHoleInducedCompatible C₀ C₀') :
    Commute (H.generalizedCycleSymmetryOp C₀) (H.generalizedCycleSymmetryOp C₀') := by
  unfold generalizedCycleSymmetryOp generalizedCycleSymmetry
  refine Commute.sum_left _ _ _ fun C hC => Commute.sum_right _ _ _ fun C' hC' => ?_
  rw [mem_deformationClosureFinset] at hC hC'
  exact H.evenHoleOperator_commute_of_inducedCompatible
    ((evenHoleInducedCompatible_iff_of_closure hC hC' hclaw h₀ h₀').1 h)

end PauliFrustrationRepresentation

end SimpleGraph
