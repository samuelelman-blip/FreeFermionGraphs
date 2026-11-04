import FreeFermionGraphs.TransferOperator
import FreeFermionGraphs.ChargePairInvolution

/-!
# `T_{G∖W}(u) T_{G∖W}(-u)` as a sum over pairs of independent sets

Manuscript (arXiv 2305.15625 v1), proof of the generalized characteristic polynomial
(Lemma 11, `lemma:generalizedcharacteristicpolynomial`, statement L1266, proof
L1928-1975) up to and including Eq. (`setsymmetric`) at L1975-1976, before the regrouping
into hole families.

Throughout, `G` is a finite graph, `H : G.PauliFrustrationRepresentation A` is a
Hamiltonian representation of it (term operators `h_j` with `Adj ↔ anticommute`),
`W ⊆ V` is a deleted carrier, and `T_{G∖W}(u) = ∑_{S} (-u)^{|S|} h_S` is
`PauliFrustrationRepresentation.transfer`.

* `SimpleGraph.indepFinsetsAvoid`, `SimpleGraph.indepPairsAvoid`: the independent sets
  of `G ∖ W` (independent sets of `G` avoiding `W`) and the ordered pairs of them.
* `SimpleGraph.holeOnlyPairs`: the pairs `(S, T)` such that every vertex of `S ⊕ T` has
  exactly two neighbours in `S ⊕ T`.  Given `S`, `T` independent and `G` claw-free (so
  that `G[S ⊕ T]` has maximum degree at most two, v1 Lemma 1,
  `lemma:clawfreesymmetricdifference`, L621; repo `lemma6`) this says that `G[S ⊕ T]`
  has no path component (v1 L1974: "`G[S ⊕ T]` contains no path components, so it must be a
  collection of disjoint and non-neighbouring even holes").
* `transfer_eq_sum_indepFinsetsAvoid`: `T_{G∖W}(u) = ∑_{S} (-u)^{|S|} h_S` (v1 Definition 5).
* `transfer_mul_transfer_neg_eq_pairs`: `T_{G∖W}(u) T_{G∖W}(-u) =
  ∑_{(S,T)} (-u)^{|S|} u^{|T|} h_S h_T` over ordered pairs of independent sets avoiding `W`
  (v1 L1930-1934, the display `Z_G(-u²) = ∑_{s,t} (-1)^s u^{s+t} Q^{(s)} Q^{(t)}`).
  Pure algebra; neither claw-freeness nor commutation of charges is used.
* `transfer_mul_transfer_neg_eq_holeOnly`: for claw-free `G`,
  `T_{G∖W}(u) T_{G∖W}(-u) = ∑_{(S,T) ∈ holeOnlyPairs W} (-u²)^{|S|} h_S h_T`, which is v1's
  Eq. (`setsymmetric`) (L1975-1976) for the vertex-deleted graph.  Moreover `|S| = |T|` on
  `holeOnlyPairs` (`card_eq_of_mem_holeOnlyPairs`).

## The proof, and a deliberate deviation from v1

v1 first discards the terms with `|S| + |T|` odd using Theorem 1 (L1936-1940) and the
terms with `|E[S ⊕ T]|` odd by the swap `S ↔ T` (L1952), and only then cancels the terms
with a path component in `G[S ⊕ T]` (L1959-1974).  Here the path-component cancellation is
performed for *all* terms at once, so Theorem 1 is not needed and the only hypothesis is
claw-freeness.

For a pair of independent sets `(S, T)` and a component `Q` of `G[S ⊕ T]` let
`e(Q) = c(S ∩ Q, T ∩ Q)` (`SimpleGraph.crossCount`), the number of edges of `G[Q]`.
Toggling `Q` (replacing `(S, T)` by `(S ⊕ Q, T ⊕ Q)`) keeps the pair of independent sets
(`isIndepSet_symmDiff_of_isInducedComponent`), keeps `S ⊕ T`, and satisfies

* `h_{S ⊕ Q} h_{T ⊕ Q} = (-1)^{e(Q)} h_S h_T`
  (`independentProduct_mul_toggle`; v1 L1964-1968),
* `|S ⊕ Q| + |T ⊕ Q| = |S| + |T|` and `|S ⊕ Q| ≡ |S| + |Q| (mod 2)`.

Hence the two terms of `(S, T)` and `(S ⊕ Q, T ⊕ Q)` cancel as soon as `|Q| + e(Q)` is odd.
`SimpleGraph.cancelComponents S T` is the finite set of components with this property.  When
`G` is claw-free and `S`, `T` are independent, every component of `G[S ⊕ T]` with a vertex of
degree at most one inside `S ⊕ T` is in it
(`odd_card_add_crossCount_of_isInducedComponent`; a connected graph of maximum degree two with
a vertex of degree `≤ 1` is a tree, so `|Q| = e(Q) + 1`, which is the identity
"`|P| + |E[P]|` is odd for a path `P`" of v1 L1968-1974), and `cancelComponents S T` is nonempty
as soon as some vertex of `S ⊕ T` does not have exactly two neighbours in `S ⊕ T`
(`exists_mem_cancelComponents`).  The pairing
`(S, T) ↦ (S ⊕ Q, T ⊕ Q)` for a fixed element `Q` of `cancelComponents S T`, chosen as a
function of the set `cancelComponents S T` alone (v1 L1974: "we can choose a path component
by which to pair terms"), is an involution without fixed points
(`cancelPairToggle_involutive`, `cancelPairToggle_ne_of_nonempty`).

Two small remarks on v1's text: the remark "a path cannot be the only component"
(L1959) is not needed, and the displayed `|S| = |S|` at L1974 should read `|S| = |T|`.
-/

open scoped symmDiff BigOperators

universe u w

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-! ### The families of pairs -/

/-- The independent sets of `G ∖ W`: the independent sets of `G` that avoid `W`.  This is
the union over `k` of `G.independentFinsetsOfCardAvoid W k`
(`independentFinsetsOfCardAvoid_eq_filter`). -/
noncomputable def indepFinsetsAvoid (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    (W : Set V) : Finset (Finset V) := by
  classical exact Finset.univ.filter fun S => G.IsIndepSet (S : Set V) ∧ ∀ v ∈ S, v ∉ W

/-- Membership in `indepFinsetsAvoid`. -/
@[simp]
theorem mem_indepFinsetsAvoid [Fintype V] [DecidableEq V] {W : Set V} {S : Finset V} :
    S ∈ G.indepFinsetsAvoid W ↔ G.IsIndepSet (S : Set V) ∧ ∀ v ∈ S, v ∉ W := by
  classical
  simp [indepFinsetsAvoid]

/-- The `k`-element independent sets avoiding `W` are those of `indepFinsetsAvoid W` of
cardinality `k`. -/
theorem independentFinsetsOfCardAvoid_eq_filter [Fintype V] [DecidableEq V] (W : Set V)
    (k : ℕ) :
    G.independentFinsetsOfCardAvoid W k = (G.indepFinsetsAvoid W).filter fun S => S.card = k := by
  ext S
  simp only [mem_independentFinsetsOfCardAvoid, Finset.mem_filter, mem_indepFinsetsAvoid]
  tauto

/-- The ordered pairs `(S, T)` of independent sets of `G ∖ W`, i.e. of independent sets of
`G` avoiding `W`: the product of the families `independentFinsetsOfCardAvoid W k`, taken over
all `k`. -/
noncomputable def indepPairsAvoid (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    (W : Set V) : Finset (Finset V × Finset V) :=
  G.indepFinsetsAvoid W ×ˢ G.indepFinsetsAvoid W

/-- Membership in `indepPairsAvoid`. -/
@[simp]
theorem mem_indepPairsAvoid [Fintype V] [DecidableEq V] {W : Set V} {p : Finset V × Finset V} :
    p ∈ G.indepPairsAvoid W ↔
      (G.IsIndepSet (p.1 : Set V) ∧ ∀ v ∈ p.1, v ∉ W) ∧
        (G.IsIndepSet (p.2 : Set V) ∧ ∀ v ∈ p.2, v ∉ W) := by
  simp [indepPairsAvoid]

/-- The pairs `(S, T)` of independent sets avoiding `W` such that every vertex of `S ⊕ T` has
exactly two neighbours in `S ⊕ T` (v1 L1974-1975: for claw-free `G` these are exactly the pairs
for which `G[S ⊕ T]` has no path component, so is a collection of even holes). -/
noncomputable def holeOnlyPairs (G : SimpleGraph V) [Fintype V] [DecidableEq V] (W : Set V) :
    Finset (Finset V × Finset V) := by
  classical exact (Finset.univ ×ˢ Finset.univ).filter fun p =>
    G.IsIndepSet (p.1 : Set V) ∧ G.IsIndepSet (p.2 : Set V) ∧ (∀ v ∈ p.1, v ∉ W) ∧
      (∀ v ∈ p.2, v ∉ W) ∧
    ∀ v ∈ p.1 ∆ p.2, ((p.1 ∆ p.2).filter (G.Adj v)).card = 2

/-- Membership in `holeOnlyPairs`. -/
theorem mem_holeOnlyPairs [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {W : Set V}
    {p : Finset V × Finset V} :
    p ∈ G.holeOnlyPairs W ↔
      G.IsIndepSet (p.1 : Set V) ∧ G.IsIndepSet (p.2 : Set V) ∧ (∀ v ∈ p.1, v ∉ W) ∧
        (∀ v ∈ p.2, v ∉ W) ∧
      ∀ v ∈ p.1 ∆ p.2, ((p.1 ∆ p.2).filter (G.Adj v)).card = 2 := by
  classical
  unfold holeOnlyPairs
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
  convert Iff.rfl

/-! ### Degrees in `G[S ⊕ T]` -/

/-- For an independent `S` and `x ∈ S`, the neighbours of `x` in `S ⊕ T` are its neighbours
in `T ∖ S`. -/
theorem filter_symmDiff_adj_of_mem_left [DecidableEq V] [DecidableRel G.Adj] {S T : Finset V}
    (hS : G.IsIndepSet (S : Set V)) {x : V} (hx : x ∈ S) :
    (S ∆ T).filter (G.Adj x) = (T \ S).filter (G.Adj x) := by
  ext y
  simp only [Finset.mem_filter, Finset.mem_symmDiff, Finset.mem_sdiff]
  constructor
  · rintro ⟨h | h, hadj⟩
    · exact (hS (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr h.1) hadj.ne hadj).elim
    · exact ⟨h, hadj⟩
  · rintro ⟨h, hadj⟩
    exact ⟨Or.inr h, hadj⟩

/-- In a claw-free graph, for independent `S`, `T` every vertex of `S ⊕ T` has at most two
neighbours in `S ⊕ T` (the degree part of v1 Lemma 1, `lemma:clawfreesymmetricdifference`,
L621; repo `lemma6`; in finset form). -/
theorem card_filter_adj_symmDiff_le_two [DecidableEq V] [DecidableRel G.Adj]
    (hclaw : G.IsClawFree) {S T : Finset V} (hS : G.IsIndepSet (S : Set V))
    (hT : G.IsIndepSet (T : Set V)) {x : V} (hx : x ∈ S ∆ T) :
    ((S ∆ T).filter (G.Adj x)).card ≤ 2 := by
  rcases Finset.mem_symmDiff.mp hx with ⟨hxS, -⟩ | ⟨hxT, -⟩
  · rw [filter_symmDiff_adj_of_mem_left hS hxS]
    exact (Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset)).trans
      (card_filter_adj_le_two hclaw hT x)
  · rw [symmDiff_comm, filter_symmDiff_adj_of_mem_left hT hxT]
    exact (Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset)).trans
      (card_filter_adj_le_two hclaw hS x)

/-- If every vertex of `S ⊕ T` has exactly two neighbours in `S ⊕ T`, then `|S| = |T|`
(v1 L1974): counting the edges between `S ∖ T` and `T ∖ S` from either side gives
`2 |S ∖ T| = 2 |T ∖ S|`. -/
theorem card_eq_of_forall_card_filter_symmDiff_eq_two [DecidableEq V] [DecidableRel G.Adj]
    {S T : Finset V} (hS : G.IsIndepSet (S : Set V)) (hT : G.IsIndepSet (T : Set V))
    (h : ∀ v ∈ S ∆ T, ((S ∆ T).filter (G.Adj v)).card = 2) : S.card = T.card := by
  have h1 : G.crossCount (S \ T) (T \ S) = 2 * (S \ T).card := by
    rw [crossCount_eq_sum_card_filter, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hxS := (Finset.mem_sdiff.mp hx).1
    rw [← filter_symmDiff_adj_of_mem_left hS hxS]
    exact h x (Finset.mem_symmDiff.mpr (Or.inl (Finset.mem_sdiff.mp hx)))
  have h2 : G.crossCount (T \ S) (S \ T) = 2 * (T \ S).card := by
    rw [crossCount_eq_sum_card_filter, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hxT := (Finset.mem_sdiff.mp hx).1
    rw [← filter_symmDiff_adj_of_mem_left (T := S) hT hxT, symmDiff_comm]
    exact h x (Finset.mem_symmDiff.mpr (Or.inr (Finset.mem_sdiff.mp hx)))
  have h3 := crossCount_comm (G := G) (S \ T) (T \ S)
  have h4 := Finset.card_sdiff_add_card_inter S T
  have h5 := Finset.card_sdiff_add_card_inter T S
  rw [Finset.inter_comm T S] at h5
  omega

/-! ### A connected graph of maximum degree two with a leaf is a tree -/

/-- Induction behind `odd_card_add_crossCount_of_isInducedComponent`: a finite vertex set `Q`
inducing a connected subgraph in which every degree is `≤ 2` and some degree is `≤ 1` has
`2 |Q| = ∑_{x ∈ Q} deg_Q x + 2`, i.e. `G[Q]` has exactly `|Q| - 1` edges.  The proof peels a
leaf (strong induction on `|Q|`). -/
theorem two_mul_card_eq_sum_card_filter_add_two_aux [DecidableEq V] [DecidableRel G.Adj] :
    ∀ (n : ℕ) (Q : Finset V), Q.card = n → (G.induce (Q : Set V)).Connected →
      (∀ x ∈ Q, (Q.filter (G.Adj x)).card ≤ 2) →
      (∃ x ∈ Q, (Q.filter (G.Adj x)).card ≤ 1) →
      2 * Q.card = ∑ x ∈ Q, (Q.filter (G.Adj x)).card + 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Q hQn hconn hdeg hleaf
    obtain ⟨x, hxQ, hx1⟩ := hleaf
    have hcl := connected_induce_iff_closed.mp hconn
    by_cases hx0 : (Q.filter (G.Adj x)).card = 0
    · -- no neighbour: `Q = {x}`
      have hQ : Q = {x} := by
        have hset : ({x} : Set V) = (Q : Set V) := by
          refine hcl.2 {x} (by simpa using hxQ) ⟨x, rfl⟩ ?_
          intro z w hz hw hzw
          rw [Set.mem_singleton_iff] at hz
          subst hz
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hx0
          exact (hx0 (Finset.mem_coe.mp hw) hzw).elim
        apply Finset.coe_injective
        rw [← hset]
        simp
      subst hQ
      simp
    · -- exactly one neighbour `y`: peel `x`
      have h1 : (Q.filter (G.Adj x)).card = 1 := by omega
      obtain ⟨y, hy⟩ := Finset.card_eq_one.mp h1
      have hymem : y ∈ Q.filter (G.Adj x) := by rw [hy]; exact Finset.mem_singleton_self y
      rw [Finset.mem_filter] at hymem
      obtain ⟨hyQ, hxy⟩ := hymem
      have huniq : ∀ w ∈ (Q : Set V), G.Adj x w → w = y := by
        intro w hw hxw
        have : w ∈ Q.filter (G.Adj x) := Finset.mem_filter.mpr ⟨Finset.mem_coe.mp hw, hxw⟩
        rw [hy] at this
        exact Finset.mem_singleton.mp this
      have hyx : y ≠ x := hxy.ne.symm
      set Q' := Q.erase x with hQ'
      have hQ'card : Q'.card + 1 = Q.card := Finset.card_erase_add_one hxQ
      have hconn' : (G.induce (Q' : Set V)).Connected := by
        rw [hQ', Finset.coe_erase]
        exact connected_induce_diff_singleton_of_unique_adj hconn (Finset.mem_coe.mpr hxQ)
          (Finset.mem_coe.mpr hyQ) hxy huniq
      have hyQ' : y ∈ Q' := Finset.mem_erase.mpr ⟨hyx, hyQ⟩
      -- degrees in `Q'` versus `Q`
      have hdegQ : ∀ z ∈ Q', (Q.filter (G.Adj z)).card =
          (Q'.filter (G.Adj z)).card + if G.Adj z x then 1 else 0 := by
        intro z hz
        have hQins : Q = insert x Q' := (Finset.insert_erase hxQ).symm
        have hxn : x ∉ Q'.filter (G.Adj z) := fun h => by
          simp [hQ'] at h
        conv_lhs => rw [hQins, Finset.filter_insert]
        split_ifs with hzx
        · rw [Finset.card_insert_of_notMem hxn]
        · simp
      have hdeg' : ∀ z ∈ Q', (Q'.filter (G.Adj z)).card ≤ 2 := fun z hz =>
        (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset x Q))).trans
          (hdeg z (Finset.mem_of_mem_erase hz))
      have hleaf' : ∃ z ∈ Q', (Q'.filter (G.Adj z)).card ≤ 1 := by
        refine ⟨y, hyQ', ?_⟩
        have := hdegQ y hyQ'
        rw [if_pos hxy.symm] at this
        have := hdeg y hyQ
        omega
      have ihQ' := ih Q'.card (by omega) Q' rfl hconn' hdeg' hleaf'
      -- the neighbours of `x`
      have hnx : (Q'.filter fun z => G.Adj z x).card = 1 := by
        rw [← h1]
        congr 1
        ext z
        simp only [Finset.mem_filter, hQ', Finset.mem_erase]
        constructor
        · rintro ⟨⟨_, hz⟩, hzx⟩
          exact ⟨hz, hzx.symm⟩
        · rintro ⟨hz, hxz⟩
          exact ⟨⟨hxz.ne.symm, hz⟩, hxz.symm⟩
      have hsumQ : ∑ z ∈ Q, (Q.filter (G.Adj z)).card =
          (Q.filter (G.Adj x)).card + ∑ z ∈ Q', (Q.filter (G.Adj z)).card :=
        (Finset.add_sum_erase Q (fun z => (Q.filter (G.Adj z)).card) hxQ).symm
      have hsumQ' : ∑ z ∈ Q', (Q.filter (G.Adj z)).card =
          ∑ z ∈ Q', (Q'.filter (G.Adj z)).card + (Q'.filter fun z => G.Adj z x).card := by
        rw [Finset.card_filter, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl hdegQ
      omega

/-! ### Components of `G[S ⊕ T]` -/

/-- A component `Q` of `G[D]` contains every neighbour inside `D` of each of its vertices. -/
theorem filter_isInducedComponent_adj [DecidableEq V] [DecidableRel G.Adj] {D Q : Finset V}
    (hQ : G.IsInducedComponent ↑D ↑Q) {x : V} (hxQ : x ∈ Q) :
    Q.filter (G.Adj x) = D.filter (G.Adj x) := by
  ext y
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hyQ, hadj⟩
    exact ⟨Finset.mem_coe.mp (hQ.1 (Finset.mem_coe.mpr hyQ)), hadj⟩
  · rintro ⟨hyD, hadj⟩
    exact ⟨Finset.mem_coe.mp (hQ.2.2 (Finset.mem_coe.mpr hxQ) (Finset.mem_coe.mpr hyD) hadj),
      hadj⟩

/-- For an independent `S`, a component `Q` of `G[S ⊕ T]` and `x ∈ S ∩ Q`, the neighbours of
`x` in `Q` are its neighbours in `T ∩ Q`. -/
theorem filter_isInducedComponent_adj_of_mem_left [DecidableEq V] [DecidableRel G.Adj]
    {S T Q : Finset V} (hS : G.IsIndepSet (S : Set V))
    (hQ : G.IsInducedComponent ↑(S ∆ T) ↑Q) {x : V} (hx : x ∈ S) :
    Q.filter (G.Adj x) = (T ∩ Q).filter (G.Adj x) := by
  ext y
  simp only [Finset.mem_filter, Finset.mem_inter]
  constructor
  · rintro ⟨hyQ, hadj⟩
    have hy := hQ.1 (Finset.mem_coe.mpr hyQ)
    rw [Finset.mem_coe, Finset.mem_symmDiff] at hy
    rcases hy with hy | hy
    · exact (hS (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy.1) hadj.ne hadj).elim
    · exact ⟨⟨hy.1, hyQ⟩, hadj⟩
  · rintro ⟨⟨_, hyQ⟩, hadj⟩
    exact ⟨hyQ, hadj⟩

/-- The two halves `S ∩ Q`, `T ∩ Q` of a component `Q` of `G[S ⊕ T]` are disjoint. -/
theorem disjoint_inter_inter_of_isInducedComponent [DecidableEq V] {S T Q : Finset V}
    (hQ : G.IsInducedComponent ↑(S ∆ T) ↑Q) : Disjoint (S ∩ Q) (T ∩ Q) := by
  rw [Finset.disjoint_left]
  intro x hxS hxT
  have h1 := Finset.mem_inter.mp hxS
  have h2 := Finset.mem_inter.mp hxT
  have := hQ.1 (Finset.mem_coe.mpr h1.2)
  rw [Finset.mem_coe, Finset.mem_symmDiff] at this
  tauto

/-- A component `Q` of `G[S ⊕ T]` is the union of its halves `S ∩ Q` and `T ∩ Q`. -/
theorem eq_union_inter_of_isInducedComponent [DecidableEq V] {S T Q : Finset V}
    (hQ : G.IsInducedComponent ↑(S ∆ T) ↑Q) : Q = (S ∩ Q) ∪ (T ∩ Q) := by
  ext x
  simp only [Finset.mem_union, Finset.mem_inter]
  constructor
  · intro hx
    have := hQ.1 (Finset.mem_coe.mpr hx)
    rw [Finset.mem_coe, Finset.mem_symmDiff] at this
    rcases this with h | h
    · exact Or.inl ⟨h.1, hx⟩
    · exact Or.inr ⟨h.1, hx⟩
  · rintro (h | h) <;> exact h.2

/-- `|Q| = |S ∩ Q| + |T ∩ Q|` for a component `Q` of `G[S ⊕ T]`. -/
theorem card_eq_card_inter_add_card_inter [DecidableEq V] {S T Q : Finset V}
    (hQ : G.IsInducedComponent ↑(S ∆ T) ↑Q) :
    Q.card = (S ∩ Q).card + (T ∩ Q).card := by
  rw [← Finset.card_union_of_disjoint (disjoint_inter_inter_of_isInducedComponent hQ),
    ← eq_union_inter_of_isInducedComponent hQ]

/-- **Path components are cancelling components.**  Let `G` be claw-free, `S`, `T` independent
and `Q` a component of `G[S ⊕ T]` containing a vertex `v` with at most one neighbour in
`S ⊕ T`.  Then `G[Q]` is a tree (a connected graph of maximum degree two with a vertex of
degree `≤ 1`), so `|Q| = e(Q) + 1` and `|Q| + e(Q)` is odd, where `e(Q) = c(S ∩ Q, T ∩ Q)` is
the number of edges of `G[Q]` (v1 L1968-1974: a path has an odd number of vertices or an odd
number of edges). -/
theorem odd_card_add_crossCount_of_isInducedComponent [DecidableEq V] [DecidableRel G.Adj]
    (hclaw : G.IsClawFree)
    {S T Q : Finset V} (hS : G.IsIndepSet (S : Set V)) (hT : G.IsIndepSet (T : Set V))
    (hQ : G.IsInducedComponent ↑(S ∆ T) ↑Q) {v : V} (hvQ : v ∈ Q)
    (hv : ((S ∆ T).filter (G.Adj v)).card ≤ 1) :
    Odd (Q.card + G.crossCount (S ∩ Q) (T ∩ Q)) := by
  have hQD : ∀ x ∈ Q, Q.filter (G.Adj x) = (S ∆ T).filter (G.Adj x) := fun x hx =>
    filter_isInducedComponent_adj hQ hx
  have hdeg : ∀ x ∈ Q, (Q.filter (G.Adj x)).card ≤ 2 := fun x hx => by
    rw [hQD x hx]
    exact card_filter_adj_symmDiff_le_two hclaw hS hT
      (Finset.mem_coe.mp (hQ.1 (Finset.mem_coe.mpr hx)))
  have haux := two_mul_card_eq_sum_card_filter_add_two_aux Q.card Q rfl hQ.2.1 hdeg
    ⟨v, hvQ, by rw [hQD v hvQ]; exact hv⟩
  have hsum : ∑ x ∈ Q, (Q.filter (G.Adj x)).card = 2 * G.crossCount (S ∩ Q) (T ∩ Q) := by
    have h := Finset.sum_union (f := fun x => (Q.filter (G.Adj x)).card)
      (disjoint_inter_inter_of_isInducedComponent hQ)
    rw [← eq_union_inter_of_isInducedComponent hQ] at h
    rw [h]
    have hA : ∑ x ∈ S ∩ Q, (Q.filter (G.Adj x)).card = G.crossCount (S ∩ Q) (T ∩ Q) := by
      rw [crossCount_eq_sum_card_filter]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [Finset.mem_inter] at hx
      rw [filter_isInducedComponent_adj_of_mem_left hS hQ hx.1]
    have hB : ∑ x ∈ T ∩ Q, (Q.filter (G.Adj x)).card = G.crossCount (S ∩ Q) (T ∩ Q) := by
      rw [crossCount_comm, crossCount_eq_sum_card_filter]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [Finset.mem_inter] at hx
      have hQ' : G.IsInducedComponent ↑(T ∆ S) ↑Q := by rwa [symmDiff_comm]
      rw [filter_isInducedComponent_adj_of_mem_left hT hQ' hx.1]
    rw [hA, hB]
    ring
  exact ⟨G.crossCount (S ∩ Q) (T ∩ Q), by omega⟩

/-! ### The cancelling components `cancelComponents S T` -/

/-- The components `Q` of `G[S ⊕ T]` with `|Q| + c(S ∩ Q, T ∩ Q)` odd, where `c(S ∩ Q, T ∩ Q)`
(`crossCount`) is the number of edges of `G[Q]`.  Toggling such a component in both `S` and `T`
flips the sign of the term `(-u)^{|S|} u^{|T|} h_S h_T`
(`smul_independentProduct_toggle_add_eq_zero`).  For claw-free `G` and independent `S`, `T`,
every path component (a component with a vertex of degree `≤ 1` in `G[S ⊕ T]`) is one
(`odd_card_add_crossCount_of_isInducedComponent`); v1 L1959-1974. -/
noncomputable def cancelComponents [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (S T : Finset V) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter fun Q =>
    G.IsInducedComponent ↑(S ∆ T) ↑Q ∧ Odd (Q.card + G.crossCount (S ∩ Q) (T ∩ Q))

/-- Membership in `cancelComponents S T`. -/
theorem mem_cancelComponents [Fintype V] [DecidableEq V] {S T Q : Finset V} :
    Q ∈ G.cancelComponents S T ↔
      G.IsInducedComponent ↑(S ∆ T) ↑Q ∧ Odd (Q.card + G.crossCount (S ∩ Q) (T ∩ Q)) := by
  classical
  unfold cancelComponents
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- If some vertex of `S ⊕ T` does not have exactly two neighbours in `S ⊕ T` (for claw-free `G`
and independent `S`, `T`: if `G[S ⊕ T]` has a path component), then `cancelComponents S T` is
nonempty (v1 L1959-1960: a path component exists and is used for the pairing). -/
theorem exists_mem_cancelComponents [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hclaw : G.IsClawFree) {S T : Finset V} (hS : G.IsIndepSet (S : Set V))
    (hT : G.IsIndepSet (T : Set V))
    (hnot : ¬ ∀ v ∈ S ∆ T, ((S ∆ T).filter (G.Adj v)).card = 2) :
    (G.cancelComponents S T).Nonempty := by
  classical
  push Not at hnot
  obtain ⟨v, hv, hne⟩ := hnot
  have hle := card_filter_adj_symmDiff_le_two hclaw hS hT hv
  have hv1 : ((S ∆ T).filter (G.Adj v)).card ≤ 1 := by omega
  have hvU : v ∈ (↑(S ∆ T) : Set V) := Finset.mem_coe.mpr hv
  have hcomp := isInducedComponent_inducedComponentSet (G := G) hvU
  set Q : Finset V := (S ∆ T).filter (· ∈ G.inducedComponentSet ↑(S ∆ T) v) with hQdef
  have hQcoe : (↑Q : Set V) = G.inducedComponentSet ↑(S ∆ T) v := by
    ext w
    constructor
    · intro h
      have := Finset.mem_coe.mp h
      rw [hQdef, Finset.mem_filter] at this
      exact this.2
    · intro hw
      obtain ⟨_, hwU, _⟩ := hw
      rw [Finset.mem_coe, hQdef, Finset.mem_filter]
      exact ⟨Finset.mem_coe.mp hwU, ⟨hvU, hwU, by assumption⟩⟩
  have hQc : G.IsInducedComponent ↑(S ∆ T) ↑Q := by rw [hQcoe]; exact hcomp
  have hvQ : v ∈ Q := by
    rw [← Finset.mem_coe, hQcoe]
    exact ⟨hvU, hvU, Reachable.refl _⟩
  exact ⟨Q, mem_cancelComponents.mpr
    ⟨hQc, odd_card_add_crossCount_of_isInducedComponent hclaw hS hT hQc hvQ hv1⟩⟩

/-! ### Toggling a component -/

/-- Toggling a component `Q` of `G[S ⊕ T]` in `S` exchanges the part `S ∩ Q` for `T ∩ Q`:
`S ⊕ Q = (S ∖ Q) ∪ (T ∩ Q)`. -/
theorem symmDiff_eq_sdiff_union_inter_of_isInducedComponent [DecidableEq V] {S T Q : Finset V}
    (hQ : G.IsInducedComponent ↑(S ∆ T) ↑Q) : S ∆ Q = (S \ Q) ∪ (T ∩ Q) := by
  ext v
  simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · refine Or.inr ⟨?_, h.1⟩
      rcases mem_left_xor_right_of_isInducedComponent hQ h.1 with h' | h'
      · exact absurd h'.1 h.2
      · exact h'.1
  · rintro (h | h)
    · exact Or.inl h
    · refine Or.inr ⟨h.2, ?_⟩
      rcases mem_left_xor_right_of_isInducedComponent hQ h.2 with h' | h'
      · exact absurd h.1 h'.2
      · exact h'.2

/-- Toggling a component `Q` of `G[S ⊕ T]` in `T` exchanges the part `T ∩ Q` for `S ∩ Q`:
`T ⊕ Q = (S ∩ Q) ∪ (T ∖ Q)`. -/
theorem symmDiff_eq_inter_union_sdiff_of_isInducedComponent [DecidableEq V] {S T Q : Finset V}
    (hQ : G.IsInducedComponent ↑(S ∆ T) ↑Q) : T ∆ Q = (S ∩ Q) ∪ (T \ Q) := by
  have hQ' : G.IsInducedComponent ↑(T ∆ S) ↑Q := by rwa [symmDiff_comm]
  rw [symmDiff_eq_sdiff_union_inter_of_isInducedComponent hQ', Finset.union_comm]

/-- `(S ⊕ Q) ∩ Q = T ∩ Q` for a component `Q` of `G[S ⊕ T]`. -/
theorem symmDiff_inter_self_of_isInducedComponent [DecidableEq V] {S T Q : Finset V}
    (hQ : G.IsInducedComponent ↑(S ∆ T) ↑Q) : (S ∆ Q) ∩ Q = T ∩ Q := by
  ext v
  simp only [Finset.mem_inter, Finset.mem_symmDiff]
  constructor
  · rintro ⟨h | h, hvQ⟩
    · exact absurd hvQ h.2
    · refine ⟨?_, hvQ⟩
      rcases mem_left_xor_right_of_isInducedComponent hQ hvQ with h' | h'
      · exact absurd h'.1 h.2
      · exact h'.1
  · rintro ⟨hvT, hvQ⟩
    refine ⟨Or.inr ⟨hvQ, ?_⟩, hvQ⟩
    rcases mem_left_xor_right_of_isInducedComponent hQ hvQ with h' | h'
    · exact absurd hvT h'.2
    · exact h'.2

/-- `(S ⊕ Q) ∩ Q' = S ∩ Q'` for a component `Q'` of `G[S ⊕ T]` disjoint from `Q`. -/
theorem symmDiff_inter_of_disjoint [DecidableEq V] {S Q Q' : Finset V} (hdisj : Disjoint Q Q') :
    (S ∆ Q) ∩ Q' = S ∩ Q' := by
  ext v
  simp only [Finset.mem_inter, Finset.mem_symmDiff]
  constructor
  · rintro ⟨h | h, hvQ'⟩
    · exact ⟨h.1, hvQ'⟩
    · exact absurd h.1 (Finset.disjoint_right.mp hdisj hvQ')
  · rintro ⟨hvS, hvQ'⟩
    exact ⟨Or.inl ⟨hvS, Finset.disjoint_right.mp hdisj hvQ'⟩, hvQ'⟩

/-- Toggling a component of `G[S ⊕ T]` in both `S` and `T` does not change the symmetric
difference. -/
theorem symmDiff_toggle_symmDiff_toggle [DecidableEq V] (S T Q : Finset V) :
    (S ∆ Q) ∆ (T ∆ Q) = S ∆ T := by
  ext v
  simp only [Finset.mem_symmDiff]
  tauto

/-- Toggling a cancelling component `Q ∈ 𝒞(S, T)` in both arguments does not change the set of
cancelling components, `𝒞(S ⊕ Q, T ⊕ Q) = 𝒞(S, T)` (so that the pairing of v1 L1974 is well
defined).  The proof is that of `oddCrossComponents_symmDiff`: distinct components are disjoint, so
the components other than `Q` see `S ⊕ Q` and `T ⊕ Q` as `S` and `T`, and on `Q` the two
arguments are exchanged while `c` is symmetric. -/
theorem cancelComponents_symmDiff [Fintype V] [DecidableEq V] {S T Q : Finset V}
    (hQ : Q ∈ G.cancelComponents S T) :
    G.cancelComponents (S ∆ Q) (T ∆ Q) = G.cancelComponents S T := by
  obtain ⟨hQc, -⟩ := mem_cancelComponents.mp hQ
  have hQc' : G.IsInducedComponent ↑(T ∆ S) ↑Q := by rwa [symmDiff_comm]
  ext Q'
  rw [mem_cancelComponents, mem_cancelComponents, symmDiff_toggle_symmDiff_toggle]
  refine and_congr_right fun hQ'c => ?_
  by_cases hQQ' : Q = Q'
  · subst hQQ'
    rw [symmDiff_inter_self_of_isInducedComponent hQc,
      symmDiff_inter_self_of_isInducedComponent hQc', crossCount_comm]
  · have hdisj : Disjoint Q Q' := by
      have := disjoint_of_isInducedComponent_of_ne hQc hQ'c
        (fun h => hQQ' (Finset.coe_injective h))
      exact Finset.disjoint_coe.mp this
    rw [symmDiff_inter_of_disjoint hdisj, symmDiff_inter_of_disjoint hdisj]

/-- A fixed cancelling component of `G[S ⊕ T]`, chosen as a function of the set
`𝒞(S, T)` alone (and `∅` when it is empty); v1 L1974: "for a given collection of pairs `(S, T)`
such that `G[S ⊕ T]` is fixed, we can choose a path component by which to pair terms". -/
noncomputable def chosenCancelComponent [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (S T : Finset V) : Finset V :=
  if h : (G.cancelComponents S T).Nonempty then h.choose else ∅

/-- The chosen component lies in `𝒞(S, T)` whenever that set is nonempty. -/
theorem chosenCancelComponent_mem [Fintype V] [DecidableEq V] {S T : Finset V}
    (h : (G.cancelComponents S T).Nonempty) :
    G.chosenCancelComponent S T ∈ G.cancelComponents S T := by
  unfold chosenCancelComponent
  rw [dif_pos h]
  exact h.choose_spec

/-- The chosen component only depends on the set `𝒞(S, T)`. -/
theorem chosenCancelComponent_congr [Fintype V] [DecidableEq V] {S T S' T' : Finset V}
    (h : G.cancelComponents S T = G.cancelComponents S' T') :
    G.chosenCancelComponent S T = G.chosenCancelComponent S' T' := by
  unfold chosenCancelComponent
  simp only [h]

/-- The chosen component is invariant under toggling a cancelling component in both
arguments. -/
theorem chosenCancelComponent_symmDiff [Fintype V] [DecidableEq V] {S T Q : Finset V}
    (hQ : Q ∈ G.cancelComponents S T) :
    G.chosenCancelComponent (S ∆ Q) (T ∆ Q) = G.chosenCancelComponent S T :=
  chosenCancelComponent_congr (cancelComponents_symmDiff hQ)

/-- The pairing of v1 L1974 on pairs of vertex sets: if `𝒞(S, T)` is nonempty, toggle the
chosen cancelling component `Q` in both arguments; otherwise do nothing. -/
noncomputable def cancelPairToggle [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (p : Finset V × Finset V) : Finset V × Finset V :=
  if (G.cancelComponents p.1 p.2).Nonempty then
    (p.1 ∆ G.chosenCancelComponent p.1 p.2, p.2 ∆ G.chosenCancelComponent p.1 p.2)
  else p

/-- On a pair with `𝒞(S, T)` nonempty, `cancelPairToggle` toggles the chosen component. -/
theorem cancelPairToggle_of_nonempty [Fintype V] [DecidableEq V] {p : Finset V × Finset V}
    (h : (G.cancelComponents p.1 p.2).Nonempty) :
    G.cancelPairToggle p =
      (p.1 ∆ G.chosenCancelComponent p.1 p.2, p.2 ∆ G.chosenCancelComponent p.1 p.2) := by
  unfold cancelPairToggle
  rw [if_pos h]

/-- On a pair with `𝒞(S, T)` empty, `cancelPairToggle` is the identity. -/
theorem cancelPairToggle_of_not_nonempty [Fintype V] [DecidableEq V] {p : Finset V × Finset V}
    (h : ¬ (G.cancelComponents p.1 p.2).Nonempty) : G.cancelPairToggle p = p := by
  unfold cancelPairToggle
  rw [if_neg h]

/-- `cancelPairToggle` is an involution. -/
theorem cancelPairToggle_involutive [Fintype V] [DecidableEq V] (p : Finset V × Finset V) :
    G.cancelPairToggle (G.cancelPairToggle p) = p := by
  by_cases h : (G.cancelComponents p.1 p.2).Nonempty
  · have hQ : G.chosenCancelComponent p.1 p.2 ∈ G.cancelComponents p.1 p.2 :=
      chosenCancelComponent_mem h
    have h1 := cancelPairToggle_of_nonempty (G := G) h
    have hc : G.cancelComponents (G.cancelPairToggle p).1 (G.cancelPairToggle p).2 =
        G.cancelComponents p.1 p.2 := by
      rw [h1]
      exact cancelComponents_symmDiff hQ
    have hne : (G.cancelComponents (G.cancelPairToggle p).1
        (G.cancelPairToggle p).2).Nonempty := by
      rw [hc]
      exact h
    have hchosen : G.chosenCancelComponent (G.cancelPairToggle p).1
        (G.cancelPairToggle p).2 = G.chosenCancelComponent p.1 p.2 := by
      rw [h1]
      exact chosenCancelComponent_symmDiff hQ
    rw [cancelPairToggle_of_nonempty hne, hchosen]
    refine Prod.ext ?_ ?_
    · simp only [h1]
      exact symmDiff_symmDiff_cancel_right _ _
    · simp only [h1]
      exact symmDiff_symmDiff_cancel_right _ _
  · rw [cancelPairToggle_of_not_nonempty h, cancelPairToggle_of_not_nonempty h]

/-- If `𝒞(S, T)` is nonempty then `cancelPairToggle` moves the pair: a component is nonempty,
and `S ⊕ Q = S` would force `Q = ∅`. -/
theorem cancelPairToggle_ne_of_nonempty [Fintype V] [DecidableEq V] {p : Finset V × Finset V}
    (h : (G.cancelComponents p.1 p.2).Nonempty) : G.cancelPairToggle p ≠ p := by
  intro heq
  have h1 := cancelPairToggle_of_nonempty (G := G) h
  have hQ := chosenCancelComponent_mem h
  obtain ⟨hQc, -⟩ := mem_cancelComponents.mp hQ
  have hne : (G.chosenCancelComponent p.1 p.2).Nonempty := by
    obtain ⟨x⟩ := hQc.2.1.nonempty
    exact ⟨x.1, Finset.mem_coe.mp x.2⟩
  have hfix : symmDiff p.1 (G.chosenCancelComponent p.1 p.2) = p.1 := by
    have := congrArg Prod.fst (h1.symm.trans heq)
    exact this
  rw [symmDiff_eq_left] at hfix
  exact hne.ne_empty hfix

namespace PauliFrustrationRepresentation

variable {A : Type w} [Ring A]

/-! ### The sign of a toggled pair of products -/

/-- Toggling a component `Q` of `G[S ⊕ T]` in both `S` and `T` multiplies the product
`h_S h_T` by `(-1)^{e(Q)}`, `e(Q) = c(S ∩ Q, T ∩ Q)` the number of edges of `G[Q]`:
`h_S h_T = (-1)^{e(Q)} h_{S ⊕ Q} h_{T ⊕ Q}` (v1 L1964-1968:
`h_{S̃} h_{T̃} = h_{S∖P} h_{T∩P} h_{S∩P} h_{T∖P} = (-1)^{|E[P]|} h_{S∖P} h_{S∩P} h_{T∩P} h_{T∖P}`).

Unlike `independentProduct_toggle_add_eq_zero` this holds for every component, whatever the
parity of `e(Q)`. -/
theorem independentProduct_mul_toggle [DecidableEq V] (H : G.PauliFrustrationRepresentation A)
    {S T Q : Finset V} (hS : G.IsIndepSet (S : Set V)) (hT : G.IsIndepSet (T : Set V))
    (hQ : G.IsInducedComponent ↑(S ∆ T) ↑Q) :
    H.independentProduct S * H.independentProduct T =
      (-1 : A) ^ G.crossCount (S ∩ Q) (T ∩ Q) *
        (H.independentProduct (S ∆ Q) * H.independentProduct (T ∆ Q)) := by
  have hQ' : G.IsInducedComponent ↑(T ∆ S) ↑Q := by rwa [symmDiff_comm]
  have hSQ : G.IsIndepSet ((S ∆ Q : Finset V) : Set V) :=
    isIndepSet_symmDiff_of_isInducedComponent hS hT hQ
  have hTQ : G.IsIndepSet ((T ∆ Q : Finset V) : Set V) :=
    isIndepSet_symmDiff_of_isInducedComponent hT hS hQ'
  have hA : G.IsIndepSet ((S ∩ Q : Finset V) : Set V) :=
    IsIndepSet.finset_subset hS Finset.inter_subset_left
  have hB : G.IsIndepSet ((T ∩ Q : Finset V) : Set V) :=
    IsIndepSet.finset_subset hT Finset.inter_subset_left
  have e1 : (S \ Q) ∪ (S ∩ Q) = S := Finset.sdiff_union_inter S Q
  have e2 : (T ∩ Q) ∪ (T \ Q) = T := by
    rw [Finset.union_comm]; exact Finset.sdiff_union_inter T Q
  have e3 := symmDiff_eq_sdiff_union_inter_of_isInducedComponent hQ
  have e4 := symmDiff_eq_inter_union_sdiff_of_isInducedComponent hQ
  have d1 : Disjoint (S \ Q) (S ∩ Q) := Finset.disjoint_sdiff_inter S Q
  have d2 : Disjoint (T ∩ Q) (T \ Q) := (Finset.disjoint_sdiff_inter T Q).symm
  have d3 : Disjoint (S \ Q) (T ∩ Q) := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_inter.mp hv').2
  have d4 : Disjoint (S ∩ Q) (T \ Q) := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    exact (Finset.mem_sdiff.mp hv').2 (Finset.mem_inter.mp hv).2
  have hS1 : H.independentProduct S =
      H.independentProduct (S \ Q) * H.independentProduct (S ∩ Q) := by
    have := H.independentProduct_union d1 (by rw [e1]; exact hS)
    rwa [e1] at this
  have hT1 : H.independentProduct T =
      H.independentProduct (T ∩ Q) * H.independentProduct (T \ Q) := by
    have := H.independentProduct_union d2 (by rw [e2]; exact hT)
    rwa [e2] at this
  have hS3 : H.independentProduct (S ∆ Q) =
      H.independentProduct (S \ Q) * H.independentProduct (T ∩ Q) := by
    have := H.independentProduct_union d3 (by rw [← e3]; exact hSQ)
    rwa [← e3] at this
  have hT3 : H.independentProduct (T ∆ Q) =
      H.independentProduct (S ∩ Q) * H.independentProduct (T \ Q) := by
    have := H.independentProduct_union d4 (by rw [← e4]; exact hTQ)
    rwa [← e4] at this
  have hanti := H.independentProduct_mul_independentProduct hA hB
  rw [hS1, hT1, hS3, hT3]
  calc
    H.independentProduct (S \ Q) * H.independentProduct (S ∩ Q) *
        (H.independentProduct (T ∩ Q) * H.independentProduct (T \ Q)) =
      H.independentProduct (S \ Q) *
        (H.independentProduct (S ∩ Q) * H.independentProduct (T ∩ Q)) *
          H.independentProduct (T \ Q) := by simp only [mul_assoc]
    _ = H.independentProduct (S \ Q) *
        ((-1 : A) ^ G.crossCount (S ∩ Q) (T ∩ Q) *
          (H.independentProduct (T ∩ Q) * H.independentProduct (S ∩ Q))) *
            H.independentProduct (T \ Q) := by rw [hanti]
    _ = (-1 : A) ^ G.crossCount (S ∩ Q) (T ∩ Q) *
        (H.independentProduct (S \ Q) * H.independentProduct (T ∩ Q) *
          (H.independentProduct (S ∩ Q) * H.independentProduct (T \ Q))) := by
      simp only [mul_assoc]
      rw [(neg_one_pow_commute (G.crossCount (S ∩ Q) (T ∩ Q)) _).symm.left_comm]

/-- **The terms of `(S, T)` and `(S ⊕ Q, T ⊕ Q)` cancel for `Q ∈ 𝒞(S, T)`** (v1 L1964-1972):
`(-u)^{|S|} u^{|T|} h_S h_T + (-u)^{|S ⊕ Q|} u^{|T ⊕ Q|} h_{S ⊕ Q} h_{T ⊕ Q} = 0`.

Toggling `Q` preserves `|S| + |T|` and shifts `|S|` by `|Q|` modulo two, and multiplies
`h_S h_T` by `(-1)^{e(Q)}` (`independentProduct_mul_toggle`); the two signs differ because
`|Q| + e(Q)` is odd.  This is where v1 uses "`(-1)^{|S̃| + |E[P]|} = -(-1)^{|S|}`" (L1968-1974). -/
theorem smul_independentProduct_toggle_add_eq_zero [Fintype V] [DecidableEq V]
    {R : Type*} [CommRing R] [Algebra R A] (H : G.PauliFrustrationRepresentation A) (u : R)
    {S T Q : Finset V} (hS : G.IsIndepSet (S : Set V)) (hT : G.IsIndepSet (T : Set V))
    (hQ : Q ∈ G.cancelComponents S T) :
    ((-u) ^ S.card * u ^ T.card) • (H.independentProduct S * H.independentProduct T) +
      ((-u) ^ (S ∆ Q).card * u ^ (T ∆ Q).card) •
        (H.independentProduct (S ∆ Q) * H.independentProduct (T ∆ Q)) = 0 := by
  obtain ⟨hQc, hodd⟩ := mem_cancelComponents.mp hQ
  have hc3 := symmDiff_eq_sdiff_union_inter_of_isInducedComponent hQc
  have hc4 := symmDiff_eq_inter_union_sdiff_of_isInducedComponent hQc
  have d3 : Disjoint (S \ Q) (T ∩ Q) := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_inter.mp hv').2
  have d4 : Disjoint (S ∩ Q) (T \ Q) := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    exact (Finset.mem_sdiff.mp hv').2 (Finset.mem_inter.mp hv).2
  have c1 : (S ∆ Q).card = (S \ Q).card + (T ∩ Q).card := by
    rw [hc3, Finset.card_union_of_disjoint d3]
  have c2 : (T ∆ Q).card = (S ∩ Q).card + (T \ Q).card := by
    rw [hc4, Finset.card_union_of_disjoint d4]
  have c3 := Finset.card_sdiff_add_card_inter S Q
  have c4 := Finset.card_sdiff_add_card_inter T Q
  have c5 := card_eq_card_inter_add_card_inter hQc
  have hn : (S ∆ Q).card + (T ∆ Q).card = S.card + T.card := by omega
  have hweight : ∀ a b : ℕ, (-u) ^ a * u ^ b = (-1 : R) ^ a * u ^ (a + b) := by
    intro a b
    rw [neg_pow, pow_add]
    ring
  have hX : H.independentProduct S * H.independentProduct T =
      (-1 : R) ^ G.crossCount (S ∩ Q) (T ∩ Q) •
        (H.independentProduct (S ∆ Q) * H.independentProduct (T ∆ Q)) := by
    rw [H.independentProduct_mul_toggle hS hT hQc, Algebra.smul_def, map_pow, map_neg, map_one]
  -- the parity of `|S ⊕ Q|`
  have hsq : ∀ k : ℕ, (-1 : R) ^ k * (-1 : R) ^ k = 1 := fun k => by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨k, rfl⟩
  have hpar : (-1 : R) ^ (S ∆ Q).card =
      -((-1 : R) ^ S.card * (-1 : R) ^ G.crossCount (S ∩ Q) (T ∩ Q)) := by
    obtain ⟨k, hk⟩ := hodd
    have hoddsum : Odd (S.card + (S ∆ Q).card + G.crossCount (S ∩ Q) (T ∩ Q)) :=
      ⟨(S \ Q).card + k, by omega⟩
    have h1 := hoddsum.neg_one_pow (α := R)
    rw [pow_add, pow_add] at h1
    set x := (-1 : R) ^ S.card
    set y := (-1 : R) ^ (S ∆ Q).card
    set z := (-1 : R) ^ G.crossCount (S ∩ Q) (T ∩ Q)
    have hx := hsq S.card
    have hz := hsq (G.crossCount (S ∩ Q) (T ∩ Q))
    calc y = y * (x * x) * (z * z) := by rw [hx, hz]; ring
      _ = (x * y * z) * (x * z) := by ring
      _ = -(x * z) := by rw [h1]; ring
  rw [hX, smul_smul, hweight S.card T.card, hweight (S ∆ Q).card (T ∆ Q).card, hn,
    ← add_smul]
  have hcoef : (-1 : R) ^ S.card * u ^ (S.card + T.card) *
      (-1 : R) ^ G.crossCount (S ∩ Q) (T ∩ Q) +
        (-1 : R) ^ (S ∆ Q).card * u ^ (S.card + T.card) = 0 := by
    rw [hpar]
    ring
  rw [hcoef, zero_smul]

end PauliFrustrationRepresentation

/-! ### `T_{G∖W}(u)` and `T_{G∖W}(u) T_{G∖W}(-u)` as sums over independent sets -/

/-- Toggling a component `Q` of `G[S ⊕ T]` in `S` keeps `S` an independent set avoiding `W`,
for `S`, `T` independent sets of `G ∖ W` (the component lies in `S ∪ T`). -/
theorem symmDiff_mem_indepFinsetsAvoid [Fintype V] [DecidableEq V] {W : Set V}
    {S T Q : Finset V} (hS : S ∈ G.indepFinsetsAvoid W) (hT : T ∈ G.indepFinsetsAvoid W)
    (hQ : G.IsInducedComponent ↑(S ∆ T) ↑Q) : S ∆ Q ∈ G.indepFinsetsAvoid W := by
  rw [mem_indepFinsetsAvoid] at hS hT ⊢
  refine ⟨isIndepSet_symmDiff_of_isInducedComponent hS.1 hT.1 hQ, ?_⟩
  intro v hv
  rcases Finset.mem_symmDiff.mp hv with ⟨hvS, -⟩ | ⟨hvQ, -⟩
  · exact hS.2 v hvS
  · rcases mem_left_xor_right_of_isInducedComponent hQ hvQ with h | h
    · exact hS.2 v h.1
    · exact hT.2 v h.1

namespace PauliFrustrationRepresentation

variable {A : Type w} [Ring A]

/-- `T_{G∖W}(u) = ∑_{S} (-u)^{|S|} h_S`, the sum over the independent sets `S` of `G ∖ W`
(v1 Definition 5, L532-540: `T_G(u) = ∑_{S ∈ 𝒮_G} (-u)^{|S|} h_S`). -/
theorem transfer_eq_sum_indepFinsetsAvoid [Fintype V] [DecidableEq V] {R : Type*} [CommRing R]
    [Algebra R A] (H : G.PauliFrustrationRepresentation A) (W : Set V) (u : R) :
    H.transfer W u = ∑ S ∈ G.indepFinsetsAvoid W, (-u) ^ S.card • H.independentProduct S := by
  classical
  have e : ∀ k, H.deletedCharge W k =
      ∑ S ∈ G.independentFinsetsOfCardAvoid W k, H.independentProduct S := fun k => rfl
  unfold transfer
  have step : ∀ k ∈ Finset.range (Fintype.card V + 1),
      (-u) ^ k • H.deletedCharge W k =
        ∑ S ∈ (G.indepFinsetsAvoid W).filter (fun S => S.card = k),
          (-u) ^ S.card • H.independentProduct S := by
    intro k _
    rw [e, Finset.smul_sum, independentFinsetsOfCardAvoid_eq_filter]
    refine Finset.sum_congr rfl fun S hS => ?_
    rw [(Finset.mem_filter.mp hS).2]
  rw [Finset.sum_congr rfl step]
  exact Finset.sum_fiberwise_of_maps_to (s := G.indepFinsetsAvoid W)
    (t := Finset.range (Fintype.card V + 1)) (g := Finset.card)
    (fun S _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_univ S)))
    (fun S => (-u) ^ S.card • H.independentProduct S)

/-- **`T_{G∖W}(u) T_{G∖W}(-u)` as a sum over pairs of independent sets** (v1 L1930-1934:
`Z_G(-u²) = T_G(u) T_G(-u) = ∑_{S,T} (-1)^{|S|} u^{|S|+|T|} h_S h_T`).

This is pure algebra from the definition of the transfer operator: it needs neither
claw-freeness nor any commutation of the charges. -/
theorem transfer_mul_transfer_neg_eq_pairs [Fintype V] [DecidableEq V] {R : Type*} [CommRing R]
    [Algebra R A] (H : G.PauliFrustrationRepresentation A) (W : Set V) (u : R) :
    H.transfer W u * H.transfer W (-u) =
      ∑ p ∈ G.indepPairsAvoid W,
        ((-u) ^ p.1.card * u ^ p.2.card) •
          (H.independentProduct p.1 * H.independentProduct p.2) := by
  rw [H.transfer_eq_sum_indepFinsetsAvoid W u, H.transfer_eq_sum_indepFinsetsAvoid W (-u),
    Finset.sum_mul_sum, indepPairsAvoid, Finset.sum_product]
  refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun T _ => ?_
  rw [smul_mul_smul_comm, neg_neg]

/-- On `holeOnlyPairs`, `|S| = |T|` (v1 L1974, where `|S| = |S|` is a misprint for
`|S| = |T|`). -/
theorem card_eq_of_mem_holeOnlyPairs [Fintype V] [DecidableEq V] {W : Set V}
    {p : Finset V × Finset V} (hp : p ∈ G.holeOnlyPairs W) : p.1.card = p.2.card := by
  classical
  have h := mem_holeOnlyPairs.mp hp
  exact card_eq_of_forall_card_filter_symmDiff_eq_two h.1 h.2.1 h.2.2.2.2

/-- **Eq. (`setsymmetric`) of v1 (L1975-1976), for the vertex-deleted graph `G ∖ W`.**

For claw-free `G`,
`T_{G∖W}(u) T_{G∖W}(-u) = ∑_{(S,T)} (-u²)^{|S|} h_S h_T`,
summed over the pairs `(S, T)` of independent sets avoiding `W` such that every vertex of
`S ⊕ T` has exactly two neighbours in `S ⊕ T` (for claw-free `G` this says that `G[S ⊕ T]` has
no path component, so is a collection of disjoint even holes).  For these pairs `|S| = |T|`
(`card_eq_of_mem_holeOnlyPairs`), whence the weight `(-u)^{|S|} u^{|T|} = (-u²)^{|S|}`.

The only hypothesis is claw-freeness.  v1 first discards the terms with `|S| + |T|` odd using
Theorem 1 (L1936-1940) and the terms with `|E[S ⊕ T]|` odd by swapping `S ↔ T` (L1952); here
both are subsumed by the pairing along a path component (`cancelPairToggle`), which cancels
every term whose `G[S ⊕ T]` has a path component (`smul_independentProduct_toggle_add_eq_zero`),
irrespective of parities. -/
theorem transfer_mul_transfer_neg_eq_holeOnly [Fintype V] [DecidableEq V] {R : Type*}
    [CommRing R] [Algebra R A] (H : G.PauliFrustrationRepresentation A) (hclaw : G.IsClawFree)
    (W : Set V) (u : R) :
    H.transfer W u * H.transfer W (-u) =
      ∑ p ∈ G.holeOnlyPairs W,
        (-u ^ 2) ^ p.1.card • (H.independentProduct p.1 * H.independentProduct p.2) := by
  classical
  rw [H.transfer_mul_transfer_neg_eq_pairs W u]
  set P := G.indepPairsAvoid W with hP
  set F : Finset V × Finset V → A := fun p =>
    ((-u) ^ p.1.card * u ^ p.2.card) •
      (H.independentProduct p.1 * H.independentProduct p.2) with hF
  set Hole : Finset V × Finset V → Prop := fun p =>
    ∀ v ∈ p.1 ∆ p.2, ((p.1 ∆ p.2).filter (G.Adj v)).card = 2 with hHole
  rw [← Finset.sum_filter_add_sum_filter_not P Hole F]
  -- the pairs with a path component cancel in pairs
  have hzero : ∑ p ∈ P.filter (fun p => ¬ Hole p), F p = 0 := by
    have hne : ∀ p ∈ P.filter (fun p => ¬ Hole p), (G.cancelComponents p.1 p.2).Nonempty := by
      intro p hp
      rw [Finset.mem_filter, hP, mem_indepPairsAvoid] at hp
      exact exists_mem_cancelComponents hclaw hp.1.1.1 hp.1.2.1 hp.2
    refine Finset.sum_involution (fun p _ => G.cancelPairToggle p) ?_ ?_ ?_ ?_
    · intro p hp
      have hp' := hp
      rw [Finset.mem_filter, hP, mem_indepPairsAvoid] at hp'
      have hne' := hne p hp
      rw [cancelPairToggle_of_nonempty hne']
      exact H.smul_independentProduct_toggle_add_eq_zero u hp'.1.1.1 hp'.1.2.1
        (chosenCancelComponent_mem hne')
    · intro p hp _
      exact cancelPairToggle_ne_of_nonempty (hne p hp)
    · intro p hp
      have hp' := hp
      rw [Finset.mem_filter, hP, mem_indepPairsAvoid] at hp'
      have hne' := hne p hp
      have hQ := chosenCancelComponent_mem hne'
      obtain ⟨hQc, -⟩ := mem_cancelComponents.mp hQ
      have hQc' : G.IsInducedComponent ↑(p.2 ∆ p.1) ↑(G.chosenCancelComponent p.1 p.2) := by
        rwa [symmDiff_comm p.2 p.1]
      have hS : p.1 ∈ G.indepFinsetsAvoid W := mem_indepFinsetsAvoid.mpr hp'.1.1
      have hT : p.2 ∈ G.indepFinsetsAvoid W := mem_indepFinsetsAvoid.mpr hp'.1.2
      rw [cancelPairToggle_of_nonempty hne', Finset.mem_filter, hP, mem_indepPairsAvoid]
      refine ⟨⟨mem_indepFinsetsAvoid.mp (symmDiff_mem_indepFinsetsAvoid hS hT hQc),
        mem_indepFinsetsAvoid.mp (symmDiff_mem_indepFinsetsAvoid hT hS hQc')⟩, ?_⟩
      simp only [hHole, symmDiff_toggle_symmDiff_toggle]
      exact hp'.2
    · intro p _
      exact cancelPairToggle_involutive p
  have hset : P.filter Hole = G.holeOnlyPairs W := by
    ext p
    rw [Finset.mem_filter, hP, mem_indepPairsAvoid, mem_holeOnlyPairs]
    simp only [hHole]
    tauto
  rw [hzero, add_zero, hset]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hcard := card_eq_of_mem_holeOnlyPairs hp
  simp only [hF]
  rw [← hcard, ← mul_pow, neg_mul, ← sq]

end PauliFrustrationRepresentation

end SimpleGraph
