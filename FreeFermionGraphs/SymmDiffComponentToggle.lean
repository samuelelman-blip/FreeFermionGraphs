import FreeFermionGraphs.PauliSetSigns
import FreeFermionGraphs.TokenSlidingComponents
import FreeFermionGraphs.ClawFree

/-!
# Odd components of `G[S ⊕ S']` and token-slide reachability

This module formalises the combinatorial facts behind the pairing argument in
the proof of Theorem 1(i) of the manuscript (arXiv 2305.15625 v1, "Independent
Set Charges", proof at L882-899), which rests on Lemma `clawfreesymmetricdifference`
(v1 L621, repo `Lemma 6`) and the remark after it (L628) that `G[S ⊕ S']` is a
disjoint union of isolated vertices, induced paths and even holes.

Let `G` be claw-free and `S`, `S'` independent.  A *component* of `G[S ⊕ S']` is
a set `Q ⊆ S ⊕ S'` which is connected in `G` and closed under adjacency inside
`S ⊕ S'` (`SimpleGraph.IsInducedComponent`).

* `isIndepSet_symmDiff_of_isInducedComponent`: `S ⊕ Q` is independent.
* `exists_isInducedComponent_odd`: if `c(S, S') = #{(x, y) ∈ S × S' : x ~ y}` is
  odd, some component `Q` has `c(S ∩ Q, S' ∩ Q)` odd (v1 L895: "there is at least
  one (and an odd number in general) path component of `G[S ⊕ S']` with odd
  length").
* `card_and_tokenSlideReachable_symmDiff`: if `c(S ∩ Q, S' ∩ Q)` is odd then
  `|S ⊕ Q| = |S|` and `S ↔_TS S ⊕ Q` (v1 L897: "`S~` can be obtained from `S` by
  successively sliding `s_j` to `s'_j`").  The proof peels a leaf of the path `Q`
  and slides the neighbouring token, by strong induction on `|Q|`; claw-freeness
  enters through the degree bound of Lemma 1 (repo `lemma6_degree_le_two`), used
  below in the finset form `card_filter_adj_le_two`.
* `tokenSlidingComponentMk_eq_of_tokenSlideReachable`: set-level token-slide
  reachability between two `k`-configurations puts them in the same connected
  component of the solution graph `TS_k(G)`.

No classification of the components as paths and even holes is needed: the
induction only uses that the degrees in `G[Q]` are at most two and that `Q` is
connected.  `SimpleGraph.IsInducedComponent` is also the notion of component
used for path components in Definition 19.
-/

open scoped symmDiff

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- `Q` is a connected component of the subgraph of `G` induced by `U`: it lies
in `U`, is connected in `G`, and is closed under adjacency inside `U`.  For
`U = S ⊕ S'` with `S`, `S'` independent this is a component of `G[S ⊕ S']`
(v1 L621-628). -/
def IsInducedComponent (G : SimpleGraph V) (U Q : Set V) : Prop :=
  Q ⊆ U ∧ (G.induce Q).Connected ∧ ∀ ⦃x y : V⦄, x ∈ Q → y ∈ U → G.Adj x y → y ∈ Q

/-! ### Connectivity of induced subgraphs via closed subsets -/

/-- A vertex set induces a connected subgraph exactly when it is nonempty and
the only nonempty subset closed under adjacency inside it is the set itself. -/
theorem connected_induce_iff_closed {Q : Set V} :
    (G.induce Q).Connected ↔ Q.Nonempty ∧ ∀ A : Set V, A ⊆ Q → A.Nonempty →
      (∀ ⦃z w : V⦄, z ∈ A → w ∈ Q → G.Adj z w → w ∈ A) → A = Q := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · obtain ⟨v⟩ := h.nonempty
      exact ⟨v.1, v.2⟩
    · rintro A hAQ ⟨a, ha⟩ hcl
      refine Set.Subset.antisymm hAQ fun b hb => ?_
      have hr := h.preconnected ⟨a, hAQ ha⟩ ⟨b, hb⟩
      rw [reachable_iff_reflTransGen] at hr
      have key : ∀ c : Q,
          Relation.ReflTransGen (G.induce Q).Adj ⟨a, hAQ ha⟩ c → c.1 ∈ A := by
        intro c hc
        induction hc with
        | refl => exact ha
        | tail _ hadj ih => exact hcl ih (Subtype.property _) hadj
      exact key ⟨b, hb⟩ hr
  · rintro ⟨⟨a, ha⟩, h⟩
    rw [connected_iff_exists_forall_reachable]
    refine ⟨⟨a, ha⟩, fun w => ?_⟩
    have hA := h {b | ∃ hb : b ∈ Q, (G.induce Q).Reachable ⟨a, ha⟩ ⟨b, hb⟩}
      (fun b hb => hb.1) ⟨a, ha, Reachable.refl _⟩ (by
        rintro z w ⟨hz, hr⟩ hw hadj
        exact ⟨hw, hr.trans (Adj.reachable (by simpa using hadj))⟩)
    have hw : w.1 ∈ {b | ∃ hb : b ∈ Q, (G.induce Q).Reachable ⟨a, ha⟩ ⟨b, hb⟩} := by
      rw [hA]; exact w.2
    obtain ⟨_, hr⟩ := hw
    exact hr

/-! ### The component of a vertex in an induced subgraph -/

/-- The set of vertices of `U` reachable from `v` inside `G[U]` (empty when
`v ∉ U`). -/
def inducedComponentSet (G : SimpleGraph V) (U : Set V) (v : V) : Set V :=
  {w | ∃ (hv : v ∈ U) (hw : w ∈ U), (G.induce U).Reachable ⟨v, hv⟩ ⟨w, hw⟩}

/-- The component of a vertex of `U` inside `G[U]` is an induced component. -/
theorem isInducedComponent_inducedComponentSet {U : Set V} {v : V} (hv : v ∈ U) :
    G.IsInducedComponent U (G.inducedComponentSet U v) := by
  refine ⟨fun w hw => ?_, ?_, ?_⟩
  · obtain ⟨_, hw', _⟩ := hw
    exact hw'
  · rw [connected_iff_exists_forall_reachable]
    refine ⟨⟨v, hv, hv, Reachable.refl _⟩, ?_⟩
    have key : ∀ c : U, Relation.ReflTransGen (G.induce U).Adj ⟨v, hv⟩ c →
        ∃ hm : c.1 ∈ G.inducedComponentSet U v,
          (G.induce (G.inducedComponentSet U v)).Reachable
            ⟨v, hv, hv, Reachable.refl _⟩ ⟨c.1, hm⟩ := by
      intro c hc
      induction hc with
      | refl => exact ⟨⟨hv, hv, Reachable.refl _⟩, Reachable.refl _⟩
      | @tail b c hab hbc ih =>
          obtain ⟨hmb, hrb⟩ := ih
          have hmc : c.1 ∈ G.inducedComponentSet U v :=
            ⟨hv, c.2, (reachable_iff_reflTransGen _ _).mpr (hab.tail hbc)⟩
          exact ⟨hmc, hrb.trans (Adj.reachable (by simpa using hbc))⟩
    intro w
    obtain ⟨hv', hw', hr⟩ := w.2
    obtain ⟨hm, hrr⟩ := key ⟨w.1, hw'⟩ ((reachable_iff_reflTransGen _ _).mp hr)
    exact hrr
  · rintro x y ⟨hv', hx, hr⟩ hy hxy
    exact ⟨hv', hy, hr.trans (Adj.reachable (by simpa using hxy))⟩

/-! ### Degree bound and (a): toggling a component keeps independence -/

/-- Claw-freeness bounds the number of neighbours of any vertex inside an
independent set by two.  This is the finset form of the degree bound of v1 Lemma
`clawfreesymmetricdifference` (L621; repo `lemma6_degree_le_two`): the same claw
argument, stated for the neighbours of an arbitrary vertex in an independent finset
rather than for the induced subgraph on a symmetric difference. -/
theorem card_filter_adj_le_two [DecidableRel G.Adj] (hclaw : G.IsClawFree) {T : Finset V}
    (hT : G.IsIndepSet (T : Set V)) (v : V) : (T.filter (G.Adj v)).card ≤ 2 := by
  by_contra h
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp (not_le.mp h)
  simp only [Finset.mem_filter] at ha hb hc
  rcases hclaw ha.2 hb.2 hc.2 hab hac hbc with h | h | h
  · exact hT (Finset.mem_coe.mpr ha.1) (Finset.mem_coe.mpr hb.1) hab h
  · exact hT (Finset.mem_coe.mpr ha.1) (Finset.mem_coe.mpr hc.1) hac h
  · exact hT (Finset.mem_coe.mpr hb.1) (Finset.mem_coe.mpr hc.1) hbc h

/-- (a) Toggling a component `Q` of `G[S ⊕ S']` keeps `S` independent:
`S ⊕ Q` is independent (v1 L897, the set `S~ = S ⊕ P` is again an independent
set). -/
theorem isIndepSet_symmDiff_of_isInducedComponent [DecidableEq V] {S S' Q : Finset V}
    (hS : G.IsIndepSet (S : Set V)) (hS' : G.IsIndepSet (S' : Set V))
    (hQ : G.IsInducedComponent ↑(symmDiff S S') ↑Q) :
    G.IsIndepSet ((symmDiff S Q : Finset V) : Set V) := by
  obtain ⟨hsub, -, hcl⟩ := hQ
  have hQS' : ∀ v ∈ Q, v ∉ S → v ∈ S' := by
    intro v hv hvS
    have := hsub (Finset.mem_coe.mpr hv)
    simp only [Finset.coe_symmDiff, Set.mem_symmDiff, Finset.mem_coe] at this
    tauto
  have key : ∀ x y, x ∈ S → x ∉ Q → y ∈ Q → y ∉ S → G.Adj x y → False := by
    intro x y hxS hxQ hyQ hyS hadj
    have hyS' : y ∈ S' := hQS' y hyQ hyS
    have hxS' : x ∉ S' := fun hx =>
      hS' (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hyS') hadj.ne hadj
    have hxU : x ∈ (↑(symmDiff S S') : Set V) := by
      rw [Finset.mem_coe, Finset.mem_symmDiff]
      exact Or.inl ⟨hxS, hxS'⟩
    exact hxQ (hcl (Finset.mem_coe.mpr hyQ) hxU hadj.symm)
  intro a ha b hb hab hadj
  simp only [Finset.mem_coe, Finset.mem_symmDiff] at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact hS (Finset.mem_coe.mpr ha.1) (Finset.mem_coe.mpr hb.1) hab hadj
  · exact key a b ha.1 ha.2 hb.1 hb.2 hadj
  · exact key b a hb.1 hb.2 ha.1 ha.2 hadj.symm
  · exact hS' (Finset.mem_coe.mpr (hQS' a ha.1 ha.2)) (Finset.mem_coe.mpr (hQS' b hb.1 hb.2))
      hab hadj

/-! ### (c) Existence of an odd component -/

/-- (c) If `c(S, S')` is odd, some component `Q` of `G[S ⊕ S']` has
`c(S ∩ Q, S' ∩ Q)` odd: every adjacent pair of `S × S'` lies inside one
component, so `c(S, S')` is the sum of the component counts (v1 L895). -/
theorem exists_isInducedComponent_odd [DecidableEq V] {S S' : Finset V}
    (hS : G.IsIndepSet (S : Set V)) (hS' : G.IsIndepSet (S' : Set V))
    (hodd : Odd (G.crossCount S S')) :
    ∃ Q : Finset V, G.IsInducedComponent ↑(symmDiff S S') ↑Q ∧
      Odd (G.crossCount (S ∩ Q) (S' ∩ Q)) := by
  classical
  by_contra hno
  have heven : ∀ Q : Finset V, G.IsInducedComponent ↑(symmDiff S S') ↑Q →
      Even (G.crossCount (S ∩ Q) (S' ∩ Q)) := fun Q hQ =>
    Nat.not_odd_iff_even.mp fun h => hno ⟨Q, hQ, h⟩
  set U : Set V := ↑(symmDiff S S') with hU
  have hmemU : ∀ v, v ∈ U ↔ (v ∈ S ∧ v ∉ S') ∨ (v ∈ S' ∧ v ∉ S) := by
    intro v
    rw [hU, Finset.mem_coe, Finset.mem_symmDiff]
  -- the count of `S` against `S'` is a sum over `S \ S'`
  have hsum : G.crossCount S S' =
      ∑ x ∈ S \ S', (S'.filter (G.Adj x)).card := by
    rw [crossCount_eq_sum_card_filter]
    symm
    refine Finset.sum_subset Finset.sdiff_subset fun x hxS hx => ?_
    have hxS' : x ∈ S' := by
      by_contra h
      exact hx (Finset.mem_sdiff.mpr ⟨hxS, h⟩)
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro y hy hadj
    exact hS' (Finset.mem_coe.mpr hxS') (Finset.mem_coe.mpr hy) hadj.ne hadj
  -- a base vertex, to define the component map totally
  have hne : (S \ S').Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hsum
    rw [hsum] at hodd
    exact (Nat.not_odd_zero hodd)
  obtain ⟨x0, hx0⟩ := hne
  have hx0U : x0 ∈ U := (hmemU x0).mpr (Or.inl (Finset.mem_sdiff.mp hx0))
  let g : V → (G.induce U).ConnectedComponent := fun v =>
    if h : v ∈ U then (G.induce U).connectedComponentMk ⟨v, h⟩
    else (G.induce U).connectedComponentMk ⟨x0, hx0U⟩
  have hg : ∀ v (hv : v ∈ U), g v = (G.induce U).connectedComponentMk ⟨v, hv⟩ := by
    intro v hv
    simp only [g, dif_pos hv]
  have hfib := Finset.sum_fiberwise_of_maps_to (s := S \ S') (t := (S \ S').image g) (g := g)
    (fun i hi => Finset.mem_image_of_mem g hi) (fun i => (S'.filter (G.Adj i)).card)
  have hev : Even (∑ j ∈ (S \ S').image g, ∑ i ∈ (S \ S').filter (fun i => g i = j),
      (S'.filter (G.Adj i)).card) := by
    refine Finset.even_sum _ fun j hj => ?_
    obtain ⟨v0, hv0, rfl⟩ := Finset.mem_image.mp hj
    have hv0U : v0 ∈ U := (hmemU v0).mpr (Or.inl (Finset.mem_sdiff.mp hv0))
    have hcomp := isInducedComponent_inducedComponentSet (G := G) hv0U
    set Q : Finset V := (S ∪ S').filter (· ∈ G.inducedComponentSet U v0) with hQdef
    have hQcoe : (↑Q : Set V) = G.inducedComponentSet U v0 := by
      ext w
      simp only [hQdef, Finset.coe_filter, Finset.mem_union, Set.mem_setOf_eq]
      constructor
      · exact fun h => h.2
      · intro hw
        refine ⟨?_, hw⟩
        obtain ⟨_, hwU, _⟩ := hw
        rcases (hmemU w).mp hwU with h | h
        · exact Or.inl h.1
        · exact Or.inr h.1
    have hQcomp : G.IsInducedComponent ↑(symmDiff S S') ↑Q := by
      rw [hQcoe]; exact hcomp
    have hfiber : (S \ S').filter (fun i => g i = g v0) = S ∩ Q := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_inter]
      constructor
      · rintro ⟨⟨hiS, hiS'⟩, hgi⟩
        have hiU : i ∈ U := (hmemU i).mpr (Or.inl ⟨hiS, hiS'⟩)
        rw [hg i hiU, hg v0 hv0U, ConnectedComponent.eq] at hgi
        refine ⟨hiS, ?_⟩
        rw [← Finset.mem_coe, hQcoe]
        exact ⟨hv0U, hiU, hgi.symm⟩
      · rintro ⟨hiS, hiQ⟩
        rw [← Finset.mem_coe, hQcoe] at hiQ
        obtain ⟨_, hiU, hr⟩ := hiQ
        refine ⟨⟨hiS, ?_⟩, ?_⟩
        · rcases (hmemU i).mp hiU with h | h
          · exact h.2
          · exact absurd hiS h.2
        · rw [hg i hiU, hg v0 hv0U, ConnectedComponent.eq]
          exact hr.symm
    rw [hfiber]
    have hnbr : ∀ i ∈ S ∩ Q, S'.filter (G.Adj i) = (S' ∩ Q).filter (G.Adj i) := by
      intro i hi
      rw [Finset.mem_inter] at hi
      ext y
      simp only [Finset.mem_filter, Finset.mem_inter]
      constructor
      · rintro ⟨hyS', hadj⟩
        refine ⟨⟨hyS', ?_⟩, hadj⟩
        have hyS : y ∉ S := fun hyS =>
          hS (Finset.mem_coe.mpr hi.1) (Finset.mem_coe.mpr hyS) hadj.ne hadj
        have hyU : y ∈ U := (hmemU y).mpr (Or.inr ⟨hyS', hyS⟩)
        exact Finset.mem_coe.mp (hQcomp.2.2 (Finset.mem_coe.mpr hi.2) hyU hadj)
      · rintro ⟨⟨hyS', _⟩, hadj⟩
        exact ⟨hyS', hadj⟩
    have : G.crossCount (S ∩ Q) (S' ∩ Q) =
        ∑ i ∈ S ∩ Q, (S'.filter (G.Adj i)).card := by
      rw [crossCount_eq_sum_card_filter]
      exact Finset.sum_congr rfl fun i hi => by rw [hnbr i hi]
    rw [← this]
    exact heven Q hQcomp
  rw [hfib, ← hsum] at hev
  exact (Nat.not_even_iff_odd.mpr hodd) hev

/-! ### (b) Leaf peeling: toggling an odd component is a sequence of token slides -/

/-- The cross count is additive in the second argument over disjoint unions. -/
theorem crossCount_union_right [DecidableEq V] {A B C : Finset V} (h : Disjoint B C) :
    G.crossCount A (B ∪ C) = G.crossCount A B + G.crossCount A C := by
  classical
  simp only [crossCount_eq_sum_card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter h)]

/-- Removing one element of the second set from a cross count. -/
theorem crossCount_eq_erase_right_add [DecidableEq V] {A B : Finset V} {x : V} (hx : x ∈ B) :
    G.crossCount A B = G.crossCount A (B.erase x) + G.crossCount A {x} := by
  have hB : B = B.erase x ∪ {x} := by
    ext v
    by_cases hv : v = x <;> simp [hv, hx]
  conv_lhs => rw [hB]
  exact crossCount_union_right (Finset.disjoint_singleton_right.mpr (Finset.notMem_erase x B))

/-- Removing one element of the first set from a cross count. -/
theorem crossCount_eq_erase_left_add [DecidableEq V] {A B : Finset V} {y : V} (hy : y ∈ A) :
    G.crossCount A B = G.crossCount (A.erase y) B + G.crossCount {y} B := by
  rw [crossCount_comm, crossCount_eq_erase_right_add hy, crossCount_comm B (A.erase y),
    crossCount_comm B {y}]

/-- The cross count of a single vertex is its number of neighbours in the set. -/
theorem crossCount_singleton_left [DecidableEq V] [DecidableRel G.Adj] (a : V) (T : Finset V) :
    G.crossCount {a} T = (T.filter (G.Adj a)).card := by
  rw [crossCount_eq_sum_card_filter, Finset.sum_singleton]

/-- Removing a vertex `x` with a unique neighbour `y` from a connected induced
subgraph leaves a connected induced subgraph. -/
theorem connected_induce_diff_singleton_of_unique_adj {Q : Set V} {x y : V}
    (hconn : (G.induce Q).Connected) (hxQ : x ∈ Q) (hyQ : y ∈ Q) (hxy : G.Adj x y)
    (huniq : ∀ w ∈ Q, G.Adj x w → w = y) :
    (G.induce (Q \ {x})).Connected := by
  rw [connected_induce_iff_closed] at hconn ⊢
  obtain ⟨_, hcl⟩ := hconn
  refine ⟨⟨y, hyQ, fun h => hxy.ne (Set.mem_singleton_iff.mp h).symm⟩, ?_⟩
  intro A hAQ ⟨a, ha⟩ hAcl
  have hAQ' : A ⊆ Q := fun v hv => (hAQ hv).1
  have hxA : x ∉ A := fun h => (hAQ h).2 rfl
  by_cases hyA : y ∈ A
  · have h1 : insert x A = Q := by
      refine hcl _ (Set.insert_subset hxQ hAQ') ⟨x, Set.mem_insert _ _⟩ ?_
      intro z w hz hw hzw
      rcases Set.mem_insert_iff.mp hz with rfl | hz
      · rw [huniq w hw hzw]; exact Set.mem_insert_of_mem _ hyA
      · by_cases hwx : w = x
        · exact hwx ▸ Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ (hAcl hz ⟨hw, hwx⟩ hzw)
    refine Set.Subset.antisymm hAQ fun w hw => ?_
    have : w ∈ insert x A := h1 ▸ hw.1
    rcases Set.mem_insert_iff.mp this with h | h
    · exact absurd h hw.2
    · exact h
  · exfalso
    have h1 : A = Q := by
      refine hcl A hAQ' ⟨a, ha⟩ ?_
      intro z w hz hw hzw
      by_cases hwx : w = x
      · subst hwx
        exact absurd (huniq z (hAQ' hz) hzw.symm ▸ hz) hyA
      · exact hAcl hz ⟨hw, hwx⟩ hzw
    exact hxA (h1 ▸ hxQ)

/-- Induction behind (b): strong induction on `|Q|`, peeling a leaf `x ∈ S' ∩ Q`
and sliding the token of its unique neighbour `y ∈ S ∩ Q` onto `x`. -/
theorem card_and_tokenSlideReachable_symmDiff_aux [DecidableEq V]
    (hclaw : G.IsClawFree) {S' : Finset V} (hS' : G.IsIndepSet (S' : Set V)) :
    ∀ (n : ℕ) (S Q : Finset V), Q.card = n → G.IsIndepSet (S : Set V) →
      G.IsInducedComponent ↑(symmDiff S S') ↑Q →
      Odd (G.crossCount (S ∩ Q) (S' ∩ Q)) →
      (symmDiff S Q).card = S.card ∧ G.TokenSlideReachable ↑S ↑(symmDiff S Q) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S Q hn hS hQ hodd
  obtain ⟨hsub, hconn, hcl⟩ := hQ
  -- Finset-level reformulation of the component hypotheses
  have hQU : ∀ v ∈ Q, (v ∈ S ∧ v ∉ S') ∨ (v ∈ S' ∧ v ∉ S) := by
    intro v hv
    have := hsub (Finset.mem_coe.mpr hv)
    rwa [Finset.mem_coe, Finset.mem_symmDiff] at this
  have hQcl : ∀ a b, a ∈ Q → ((b ∈ S ∧ b ∉ S') ∨ (b ∈ S' ∧ b ∉ S)) → G.Adj a b → b ∈ Q := by
    intro a b ha hb hab
    have hb' : b ∈ (↑(symmDiff S S') : Set V) := by
      rw [Finset.mem_coe, Finset.mem_symmDiff]; exact hb
    exact Finset.mem_coe.mp (hcl (Finset.mem_coe.mpr ha) hb' hab)
  have hSS : ∀ a b, a ∈ S → b ∈ S → G.Adj a b → False := fun a b ha hb hab =>
    hS (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab.ne hab
  have hS'S' : ∀ a b, a ∈ S' → b ∈ S' → G.Adj a b → False := fun a b ha hb hab =>
    hS' (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab.ne hab
  -- neighbours across `S`/`S'` stay in the component
  have F1 : ∀ x ∈ Q, x ∈ S' → ∀ z, z ∈ S → G.Adj x z → z ∈ Q := by
    intro x hxQ hxS' z hzS hxz
    exact hQcl x z hxQ (Or.inl ⟨hzS, fun hz => hS'S' x z hxS' hz hxz⟩) hxz
  have F2 : ∀ y ∈ Q, y ∈ S → ∀ z, z ∈ S' → G.Adj y z → z ∈ Q := by
    intro y hyQ hyS z hzS' hyz
    exact hQcl y z hyQ (Or.inr ⟨hzS', fun hz => hSS y z hyS hz hyz⟩) hyz
  -- Step 1: a leaf `x ∈ S' ∩ Q`
  have hsum : G.crossCount (S ∩ Q) (S' ∩ Q) =
      ∑ x ∈ S' ∩ Q, ((S ∩ Q).filter (G.Adj x)).card := by
    rw [crossCount_comm, crossCount_eq_sum_card_filter]
  have hnbr : ∀ x ∈ S' ∩ Q, (S ∩ Q).filter (G.Adj x) = S.filter (G.Adj x) := by
    intro x hx
    rw [Finset.mem_inter] at hx
    ext z
    simp only [Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨⟨hzS, _⟩, hxz⟩
      exact ⟨hzS, hxz⟩
    · rintro ⟨hzS, hxz⟩
      exact ⟨⟨hzS, F1 x hx.2 hx.1 z hzS hxz⟩, hxz⟩
  obtain ⟨x, hxSQ, hx1⟩ : ∃ x ∈ S' ∩ Q, (S.filter (G.Adj x)).card = 1 := by
    by_contra hno
    have hev : Even (∑ x ∈ S' ∩ Q, ((S ∩ Q).filter (G.Adj x)).card) := by
      refine Finset.even_sum _ fun x hx => ?_
      rw [hnbr x hx]
      have h2 := card_filter_adj_le_two hclaw hS x
      have h1 : (S.filter (G.Adj x)).card ≠ 1 := fun h => hno ⟨x, hx, h⟩
      rcases Nat.lt_or_ge (S.filter (G.Adj x)).card 2 with h | h
      · have : (S.filter (G.Adj x)).card = 0 := by omega
        rw [this]; exact ⟨0, rfl⟩
      · have : (S.filter (G.Adj x)).card = 2 := by omega
        rw [this]; exact ⟨1, rfl⟩
    rw [← hsum] at hev
    exact (Nat.not_even_iff_odd.mpr hodd) hev
  rw [Finset.mem_inter] at hxSQ
  obtain ⟨hxS', hxQ⟩ := hxSQ
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hx1
  have hy' : ∀ z, (z ∈ S ∧ G.Adj x z) ↔ z = y := by
    intro z
    have := Finset.ext_iff.mp hy z
    simpa [Finset.mem_filter, Finset.mem_singleton] using this
  have hyS : y ∈ S := ((hy' y).mpr rfl).1
  have hxy : G.Adj x y := ((hy' y).mpr rfl).2
  have hxS : x ∉ S := by
    rcases hQU x hxQ with h | h
    · exact absurd hxS' h.2
    · exact h.2
  have hyS' : y ∉ S' := fun h => hS'S' x y hxS' h hxy
  have hyQ : y ∈ Q := F1 x hxQ hxS' y hyS hxy
  have hne : x ≠ y := hxy.ne
  -- Step 2: the slide
  set S1 : Finset V := insert x (S.erase y) with hS1def
  have hS1mem : ∀ v, v ∈ S1 ↔ v = x ∨ (v ∈ S ∧ v ≠ y) := by
    intro v
    simp [hS1def, Finset.mem_insert, Finset.mem_erase, and_comm]
  have hS1ind : G.IsIndepSet (S1 : Set V) := by
    intro a ha b hb hab hadj
    rw [Finset.mem_coe, hS1mem] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact hab rfl
    · exact hb.2 ((hy' b).mp ⟨hb.1, hadj⟩)
    · exact ha.2 ((hy' a).mp ⟨ha.1, hadj.symm⟩)
    · exact hSS a b ha.1 hb.1 hadj
  have hcard1 : S1.card = S.card := by
    have hxn : x ∉ S.erase y := fun h => hxS (Finset.mem_of_mem_erase h)
    rw [hS1def, Finset.card_insert_of_notMem hxn, Finset.card_erase_of_mem hyS]
    have := Finset.card_pos.mpr ⟨y, hyS⟩
    omega
  have hslide : G.TokenSlide (S : Set V) (S1 : Set V) := by
    refine Or.inl ⟨hS, hS1ind, y, x, hxy.symm, ?_, ?_, ?_⟩
    · refine ⟨Finset.mem_coe.mpr hyS, fun h => ?_⟩
      rw [Finset.mem_coe, hS1mem] at h
      rcases h with h | h
      · exact hne h.symm
      · exact h.2 rfl
    · refine ⟨Finset.mem_coe.mpr ((hS1mem x).mpr (Or.inl rfl)), fun h => hxS (Finset.mem_coe.mp h)⟩
    · rw [hS1def, Finset.coe_insert, Finset.coe_erase]; rfl
  -- Step 3: split on whether `y` has a further neighbour in `S'`
  by_cases hcase : ∀ z ∈ S', G.Adj y z → z = x
  · -- `Q = {x, y}`, so `S ⊕ Q = S1`
    have hQeq : Q = {x, y} := by
      have h := (connected_induce_iff_closed.mp hconn).2 ({x, y} : Set V)
        (by
          intro v hv
          rcases hv with rfl | rfl
          · exact hxQ
          · exact hyQ)
        ⟨x, Or.inl rfl⟩ (by
          intro z w hz hw hzw
          rw [Finset.mem_coe] at hw
          rcases hz with rfl | rfl
          · rcases hQU w hw with h | h
            · exact Or.inr ((hy' w).mp ⟨h.1, hzw⟩)
            · exact absurd h.1 (fun hwS' => hS'S' _ _ hxS' hwS' hzw)
          · rcases hQU w hw with h | h
            · exact absurd h.1 (fun hwS => hSS _ _ hyS hwS hzw)
            · exact Or.inl (hcase w h.1 hzw))
      have h' : ((Q : Finset V) : Set V) = ((({x, y} : Finset V)) : Set V) := by
        rw [← h]; simp
      exact Finset.coe_injective h'
    have hSQ : symmDiff S Q = S1 := by
      ext v
      rw [Finset.mem_symmDiff, hS1mem, hQeq]
      by_cases hvx : v = x
      · subst hvx; simp [hxS]
      · by_cases hvy : v = y
        · subst hvy; simp [hyS, Ne.symm hne]
        · simp [hvx, hvy]
    rw [hSQ]
    exact ⟨hcard1, hslide.reachable⟩
  · -- generic step: `y` has a second neighbour `z ∈ S'`
    push Not at hcase
    obtain ⟨z, hzS', hyz, hzx⟩ := hcase
    have hzQ : z ∈ Q := F2 y hyQ hyS z hzS' hyz
    have hzS : z ∉ S := fun h => hSS y z hyS h hyz
    -- the neighbours of `y` in `S'` are exactly `x` and `z`
    have hNy : S'.filter (G.Adj y) = {x, z} := by
      symm
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact Finset.mem_filter.mpr ⟨hxS', hxy.symm⟩
        · rw [Finset.mem_singleton.mp hv]
          exact Finset.mem_filter.mpr ⟨hzS', hyz⟩
      · rw [Finset.card_pair (Ne.symm hzx)]
        exact card_filter_adj_le_two hclaw hS' y
    have hyS'nbr : ∀ w ∈ S', G.Adj y w → w = x ∨ w = z := by
      intro w hw hyw
      have : w ∈ S'.filter (G.Adj y) := Finset.mem_filter.mpr ⟨hw, hyw⟩
      rw [hNy] at this
      simpa using this
    -- the smaller component
    set Q1 : Finset V := (Q.erase x).erase y with hQ1def
    have hQ1mem : ∀ v, v ∈ Q1 ↔ v ≠ y ∧ v ≠ x ∧ v ∈ Q := by
      intro v
      simp [hQ1def, Finset.mem_erase]
    have hlt : Q1.card < n := by
      rw [hQ1def]
      have h1 : y ∈ Q.erase x := Finset.mem_erase.mpr ⟨hne.symm, hyQ⟩
      have h2 := Finset.card_erase_of_mem h1
      have h3 := Finset.card_erase_of_mem hxQ
      have h4 := Finset.card_pos.mpr ⟨x, hxQ⟩
      omega
    have hQ1cl : G.IsInducedComponent ↑(symmDiff S1 S') ↑Q1 := by
      have hmem1 : ∀ v, v ∈ symmDiff S1 S' ↔
          (v ≠ x ∧ v ≠ y ∧ ((v ∈ S ∧ v ∉ S') ∨ (v ∈ S' ∧ v ∉ S))) := by
        intro v
        rw [Finset.mem_symmDiff, hS1mem]
        by_cases hvx : v = x
        · subst hvx; simp [hxS']
        · by_cases hvy : v = y
          · subst hvy; simp [hyS', hyS, Ne.symm hne]
          · simp [hvx, hvy]
      refine ⟨?_, ?_, ?_⟩
      · intro v hv
        rw [Finset.mem_coe, hQ1mem] at hv
        rw [Finset.mem_coe, hmem1]
        exact ⟨hv.2.1, hv.1, hQU v hv.2.2⟩
      · -- connectedness: remove the leaf `x`, then `y`
        have h1 := connected_induce_diff_singleton_of_unique_adj hconn
          (Finset.mem_coe.mpr hxQ) (Finset.mem_coe.mpr hyQ) hxy (by
            intro w hw hxw
            rw [Finset.mem_coe] at hw
            rcases hQU w hw with h | h
            · exact (hy' w).mp ⟨h.1, hxw⟩
            · exact absurd h.1 (fun hwS' => hS'S' _ _ hxS' hwS' hxw))
        have h2 := connected_induce_diff_singleton_of_unique_adj h1
          (x := y) (y := z) ⟨Finset.mem_coe.mpr hyQ, fun h => hne (Set.mem_singleton_iff.mp h).symm⟩
          ⟨Finset.mem_coe.mpr hzQ, fun h => hzx (Set.mem_singleton_iff.mp h)⟩ hyz (by
            intro w hw hyw
            have hwQ : w ∈ Q := Finset.mem_coe.mp hw.1
            rcases hQU w hwQ with h | h
            · exact absurd h.1 (fun hwS => hSS _ _ hyS hwS hyw)
            · rcases hyS'nbr w h.1 hyw with h' | h'
              · exact absurd h' (fun h'' => hw.2 (Set.mem_singleton_iff.mpr h''))
              · exact h')
        have hset : (↑Q1 : Set V) = (↑Q \ {x}) \ {y} := by
          ext v
          simp only [Finset.mem_coe, hQ1mem, Set.mem_sdiff, Set.mem_singleton_iff]
          tauto
        rw [hset]
        exact h2
      · intro a b ha hb hab
        rw [Finset.mem_coe, hQ1mem] at ha
        rw [Finset.mem_coe, hmem1] at hb
        rw [Finset.mem_coe, hQ1mem]
        exact ⟨hb.2.1, hb.1, hQcl a b ha.2.2 hb.2.2 hab⟩
    have hodd1 : Odd (G.crossCount (S1 ∩ Q1) (S' ∩ Q1)) := by
      have hA : S1 ∩ Q1 = (S ∩ Q).erase y := by
        ext v
        simp only [Finset.mem_inter, Finset.mem_erase, hS1mem, hQ1mem]
        by_cases hvx : v = x
        · subst hvx; simp [hxS, hne]
        · by_cases hvy : v = y
          · subst hvy; simp [Ne.symm hne]
          · simp [hvx, hvy]
      have hB : S' ∩ Q1 = (S' ∩ Q).erase x := by
        ext v
        simp only [Finset.mem_inter, Finset.mem_erase, hQ1mem]
        by_cases hvx : v = x
        · subst hvx; simp
        · by_cases hvy : v = y
          · subst hvy; simp [hyS']
          · simp [hvx, hvy]
      rw [hA, hB]
      have hySQ : y ∈ S ∩ Q := Finset.mem_inter.mpr ⟨hyS, hyQ⟩
      have hxSQ' : x ∈ S' ∩ Q := Finset.mem_inter.mpr ⟨hxS', hxQ⟩
      have e1 := crossCount_eq_erase_right_add (G := G) (A := S ∩ Q) hxSQ'
      have e2 := crossCount_eq_erase_left_add (G := G) (B := (S' ∩ Q).erase x) hySQ
      have e3 : G.crossCount (S ∩ Q) {x} = 1 := by
        rw [crossCount_comm, crossCount_singleton_left, hnbr x (Finset.mem_inter.mpr ⟨hxS', hxQ⟩), hy]
        simp
      have e4 : G.crossCount {y} ((S' ∩ Q).erase x) = 1 := by
        rw [crossCount_singleton_left]
        have : ((S' ∩ Q).erase x).filter (G.Adj y) = {z} := by
          ext w
          simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_inter, Finset.mem_singleton]
          constructor
          · rintro ⟨⟨hwx, hwS', _⟩, hyw⟩
            exact (hyS'nbr w hwS' hyw).resolve_left hwx
          · rintro rfl
            exact ⟨⟨hzx, hzS', hzQ⟩, hyz⟩
        rw [this]; simp
      rw [Nat.odd_iff] at hodd ⊢
      omega
    obtain ⟨hcard', hreach'⟩ := ih Q1.card hlt S1 Q1 rfl hS1ind hQ1cl hodd1
    have hSQ : symmDiff S1 Q1 = symmDiff S Q := by
      ext v
      rw [Finset.mem_symmDiff, Finset.mem_symmDiff, hS1mem, hQ1mem]
      by_cases hvx : v = x
      · subst hvx; simp [hxS, hxQ]
      · by_cases hvy : v = y
        · subst hvy; simp [hyS, hyQ, Ne.symm hne]
        · simp [hvx, hvy]
    rw [hSQ] at hcard' hreach'
    exact ⟨hcard'.trans hcard1, hslide.reachable.trans hreach'⟩

/-- (b) Toggling a component `Q` of `G[S ⊕ S']` with `c(S ∩ Q, S' ∩ Q)` odd keeps
the number of tokens, and `S ⊕ Q` is reached from `S` by token slides: `S` and
`S ⊕ Q` are related by `S ↔_TS S ⊕ Q` (v1 L897, "`S~` can be obtained from `S` by
successively sliding `s_j` to `s'_j`").  The claw-free hypothesis is the degree
bound of Lemma 1; `Q` is then an induced path with an odd number of edges, and
the proof slides the tokens along `Q` by peeling a leaf at a time. -/
theorem card_and_tokenSlideReachable_symmDiff [DecidableEq V]
    (hclaw : G.IsClawFree) {S S' Q : Finset V}
    (hS : G.IsIndepSet (S : Set V)) (hS' : G.IsIndepSet (S' : Set V))
    (hQ : G.IsInducedComponent ↑(symmDiff S S') ↑Q)
    (hodd : Odd (G.crossCount (S ∩ Q) (S' ∩ Q))) :
    (symmDiff S Q).card = S.card ∧ G.TokenSlideReachable ↑S ↑(symmDiff S Q) :=
  card_and_tokenSlideReachable_symmDiff_aux hclaw hS' Q.card S Q rfl hS hQ hodd

/-! ### (d) Token-slide reachability gives the same component of `TS_k(G)` -/

/-- A set related by one token slide to a `k`-configuration is again a
`k`-configuration (as a finset): a slide moves one token. -/
theorem exists_tokenConfiguration_of_tokenSlide [DecidableEq V] {k : ℕ}
    {S : G.TokenConfiguration k} {C : Set V}
    (h : G.TokenSlide (S.1 : Set V) C) :
    ∃ T : G.TokenConfiguration k, (T.1 : Set V) = C := by
  obtain ⟨hSind, hScard⟩ := S.2
  rcases h with ⟨_, hCind, r, a, _, hr, ha, hC⟩ | ⟨hCind, _, r, a, _, hr, ha, hSC⟩
  · -- `C = S - r + a`
    have hrS : r ∈ S.1 := Finset.mem_coe.mp hr.1
    have haS : a ∉ S.1 := fun h => ha.2 (Finset.mem_coe.mpr h)
    have hcoe : ((insert a (S.1.erase r) : Finset V) : Set V) = C := by
      rw [Finset.coe_insert, Finset.coe_erase, hC]; rfl
    refine ⟨⟨insert a (S.1.erase r), ?_, ?_⟩, hcoe⟩
    · rw [hcoe]; exact hCind
    · rw [Finset.card_insert_of_notMem (fun h => haS (Finset.mem_of_mem_erase h)),
        Finset.card_erase_of_mem hrS, hScard]
      have := Finset.card_pos.mpr ⟨r, hrS⟩
      omega
  · -- `S = C - r + a`, so `C = S - a + r`
    have haS : a ∈ S.1 := Finset.mem_coe.mp ha.1
    have hrS : r ∉ S.1 := fun h => hr.2 (Finset.mem_coe.mpr h)
    have hSmem : ∀ v, v ∈ S.1 ↔ v = a ∨ (v ∈ C ∧ v ≠ r) := by
      intro v
      rw [← Finset.mem_coe]
      exact (Set.ext_iff.mp hSC v).trans Iff.rfl
    have hcoe : ((insert r (S.1.erase a) : Finset V) : Set V) = C := by
      ext v
      rw [Finset.mem_coe, Finset.mem_insert, Finset.mem_erase, hSmem]
      constructor
      · rintro (rfl | ⟨hva, h | ⟨hvC, _⟩⟩)
        · exact hr.1
        · exact absurd h hva
        · exact hvC
      · intro hv
        by_cases hvr : v = r
        · exact Or.inl hvr
        · refine Or.inr ⟨?_, Or.inr ⟨hv, hvr⟩⟩
          rintro rfl
          exact ha.2 hv
    refine ⟨⟨insert r (S.1.erase a), ?_, ?_⟩, hcoe⟩
    · rw [hcoe]; exact hCind
    · rw [Finset.card_insert_of_notMem (fun h => hrS (Finset.mem_of_mem_erase h)),
        Finset.card_erase_of_mem haS, hScard]
      have := Finset.card_pos.mpr ⟨a, haS⟩
      omega

/-- (d) Token-slide reachability between two `k`-configurations puts them in the
same connected component of the token-sliding solution graph `TS_k(G)`: every
intermediate set of a slide sequence is again an independent `k`-set, so each
slide is an edge of `TS_k(G)`. -/
theorem tokenSlidingComponentMk_eq_of_tokenSlideReachable [DecidableEq V] {k : ℕ}
    {S T : G.TokenConfiguration k}
    (h : G.TokenSlideReachable (S.1 : Set V) (T.1 : Set V)) :
    G.tokenSlidingComponentMk k S = G.tokenSlidingComponentMk k T := by
  have key : ∀ A B : Set V, G.TokenSlideReachable A B → A = (S.1 : Set V) →
      ∃ T' : G.TokenConfiguration k, (T'.1 : Set V) = B ∧
        G.tokenSlidingComponentMk k S = G.tokenSlidingComponentMk k T' := by
    intro A B hAB
    induction hAB with
    | refl => exact fun hA => ⟨S, hA.symm, rfl⟩
    | @tail B0 C0 _ hBC ih =>
        intro hA
        obtain ⟨T', hT', hcomp⟩ := ih hA
        rw [← hT'] at hBC
        obtain ⟨T'', hT''⟩ := exists_tokenConfiguration_of_tokenSlide hBC
        refine ⟨T'', hT'', hcomp.trans ?_⟩
        exact TokenSlide.same_tokenSlidingComponent (hT'' ▸ hBC)
  obtain ⟨T', hT', hcomp⟩ := key _ _ h rfl
  have hTT : T' = T := Subtype.ext (Finset.coe_injective hT')
  rw [hcomp, hTT]

end SimpleGraph
