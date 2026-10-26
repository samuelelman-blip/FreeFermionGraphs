import FreeFermionGraphs.PauliSetSigns
import FreeFermionGraphs.SymmDiffComponentToggle

/-!
# Canonical odd component and pairwise cancellation of independent-set products

This module formalises the pairing step in the proof of Theorem 1(i) of the
manuscript (arXiv 2305.15625 v1, "Independent Set Charges", proof at
L882-902).

For a pair `(S, S')` of vertex sets let `𝒬(S, S')` (`SimpleGraph.oddComponents`)
be the set of components `Q` of `G[S ⊕ S']` with `c(S ∩ Q, S' ∩ Q)` odd, where
`c(X, Y) = #{(x, y) ∈ X × Y : x ~ y}` is `SimpleGraph.crossCount`.  v1 L895
chooses, for each term `(S, S')` of the commutator expansion with `|E[S ⊕ S']|`
odd, "a path `P` of `G[S ⊕ S']` of odd length"; the odd path components are
exactly the elements of `𝒬(S, S')`.

* `oddComponents_symmDiff` (v1 L897-899, the pairing is well defined): for
  `Q ∈ 𝒬(S, S')` the toggled pair `(S ⊕ Q, S' ⊕ Q)` has the same symmetric
  difference, the same components, and the same odd ones, i.e.
  `𝒬(S ⊕ Q, S' ⊕ Q) = 𝒬(S, S')`.  No independence and no claw-freeness is used:
  distinct components of `G[S ⊕ S']` are disjoint, the components other than `Q`
  see `S ⊕ Q` and `S' ⊕ Q` as `S` and `S'`, and on `Q` the two arguments are
  swapped while `c` is symmetric.
* `chosenOddComponent` is a fixed choice of an element of `𝒬(S, S')`, made
  as a function of the set `𝒬(S, S')` alone.  By `oddComponents_symmDiff` it is
  unchanged when `(S, S')` is replaced by `(S ⊕ Q, S' ⊕ Q)` for `Q` the chosen
  component; this is v1 L899-902, "for a collection of such terms ... with fixed
  symmetric difference `S ⊕ S'`, we fix a path component of `G[S ⊕ S']` by which
  corresponding terms are paired", made into a function of the data
  `(S, S')` (the symmetric difference being invariant under the toggle).
* `PauliFrustrationRepresentation.independentProduct_toggle_add_eq_zero` (v1
  L897-899): for independent `S, S'` and `Q ∈ 𝒬(S, S')`,
  `h_S h_{S'} + h_{S ⊕ Q} h_{S' ⊕ Q} = 0`.  This is the displayed identity
  `[h_S, h_{S'}] + [h_{S~}, h_{S'~}] = 2 h_{S∖P}(h_{S∩P} h_{S'∩P} + h_{S'∩P}
  h_{S∩P}) h_{S'∖P} = 0` of v1.  The mirror identity with the two factors of
  each product exchanged follows by swapping `S` and `S'` and is stated as
  `independentProduct_toggle_add_eq_zero_swap`; together they give the
  commutator form `independentProduct_toggle_commutator_add_eq_zero`.

Only the commutation relations of the terms `h_j` are used (the model is
`SimpleGraph.PauliFrustrationRepresentation`); no cross-block commutation
beyond the single sign `h_{S ∩ Q} h_{S' ∩ Q} = -h_{S' ∩ Q} h_{S ∩ Q}` is needed.
v1's argument for part (i) is sound and is followed here.
-/

open scoped symmDiff

universe u w

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-! ### Components of an induced subgraph are disjoint or equal -/

/-- Two components of the same induced subgraph that share a vertex coincide.
(A component is the connected component of any of its vertices in `G[U]`.) -/
theorem eq_of_isInducedComponent_of_mem {U Q Q' : Set V} {v : V}
    (hQ : G.IsInducedComponent U Q) (hQ' : G.IsInducedComponent U Q')
    (hvQ : v ∈ Q) (hvQ' : v ∈ Q') : Q = Q' := by
  have hsub : ∀ {A B : Set V}, G.IsInducedComponent U A → G.IsInducedComponent U B →
      v ∈ A → v ∈ B → A ⊆ B := by
    intro A B hA hB hvA hvB
    have h := (connected_induce_iff_closed.mp hA.2.1).2 (A ∩ B) Set.inter_subset_left
      ⟨v, hvA, hvB⟩ (by
        rintro z w ⟨hzA, hzB⟩ hwA hzw
        exact ⟨hwA, hB.2.2 hzB (hA.1 hwA) hzw⟩)
    intro w hw
    have : w ∈ A ∩ B := by rw [h]; exact hw
    exact this.2
  exact Set.Subset.antisymm (hsub hQ hQ' hvQ hvQ') (hsub hQ' hQ hvQ' hvQ)

/-- Two distinct components of the same induced subgraph are disjoint. -/
theorem disjoint_of_isInducedComponent_of_ne {U Q Q' : Set V}
    (hQ : G.IsInducedComponent U Q) (hQ' : G.IsInducedComponent U Q') (hne : Q ≠ Q') :
    Disjoint Q Q' := by
  rw [Set.disjoint_left]
  intro v hvQ hvQ'
  exact hne (eq_of_isInducedComponent_of_mem hQ hQ' hvQ hvQ')

/-! ### The odd components `𝒬(S, S')` and the toggle invariance -/

/-- `𝒬(S, S')`: the components `Q` of `G[S ⊕ S']` with `c(S ∩ Q, S' ∩ Q)` odd
(v1 L895, the "path component of odd length" along which the pairing of
Theorem 1(i) is performed; for independent `S, S'` the parity of `c(S ∩ Q, S' ∩ Q)`
is the parity of the number of edges of `G[Q]`). -/
noncomputable def oddComponents [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (S S' : Finset V) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter fun Q =>
    G.IsInducedComponent ↑(symmDiff S S') ↑Q ∧ Odd (G.crossCount (S ∩ Q) (S' ∩ Q))

/-- Membership in `𝒬(S, S')`. -/
theorem mem_oddComponents [Fintype V] [DecidableEq V] {S S' Q : Finset V} :
    Q ∈ G.oddComponents S S' ↔
      G.IsInducedComponent ↑(symmDiff S S') ↑Q ∧ Odd (G.crossCount (S ∩ Q) (S' ∩ Q)) := by
  classical
  unfold oddComponents
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- `𝒬(S, S')` is symmetric in `S` and `S'`: the symmetric difference is
symmetric and so is the cross count. -/
theorem oddComponents_comm [Fintype V] [DecidableEq V] (S S' : Finset V) :
    G.oddComponents S' S = G.oddComponents S S' := by
  ext Q
  rw [mem_oddComponents, mem_oddComponents, symmDiff_comm S' S,
    crossCount_comm (S' ∩ Q) (S ∩ Q)]

/-- A component of `G[S ⊕ S']` is a subset of `S ⊕ S'`: every vertex lies in
exactly one of `S`, `S'`. -/
theorem mem_left_xor_right_of_isInducedComponent [DecidableEq V] {S S' Q : Finset V}
    (hQ : G.IsInducedComponent ↑(symmDiff S S') ↑Q) {v : V} (hv : v ∈ Q) :
    (v ∈ S ∧ v ∉ S') ∨ (v ∈ S' ∧ v ∉ S) := by
  have := hQ.1 (Finset.mem_coe.mpr hv)
  rwa [Finset.mem_coe, Finset.mem_symmDiff] at this

/-- (1) of the package: toggling an odd component `Q ∈ 𝒬(S, S')` of
`G[S ⊕ S']` in both arguments does not change the set of odd components,
`𝒬(S ⊕ Q, S' ⊕ Q) = 𝒬(S, S')` (v1 L897-899: the toggled term is again a term
with the same symmetric difference, and the same pairing component applies).

No independence of `S, S'` and no claw-freeness is needed: `(S ⊕ Q) ⊕ (S' ⊕ Q) =
S ⊕ S'`; a component `Q' ≠ Q` is disjoint from `Q`, so `(S ⊕ Q) ∩ Q' = S ∩ Q'` and
`(S' ⊕ Q) ∩ Q' = S' ∩ Q'`; on `Q` itself `(S ⊕ Q) ∩ Q = S' ∩ Q` and
`(S' ⊕ Q) ∩ Q = S ∩ Q`, so the parity is preserved by symmetry of the cross
count. -/
theorem oddComponents_symmDiff [Fintype V] [DecidableEq V] {S S' Q : Finset V}
    (hQ : Q ∈ G.oddComponents S S') :
    G.oddComponents (symmDiff S Q) (symmDiff S' Q) = G.oddComponents S S' := by
  have hU : symmDiff (symmDiff S Q) (symmDiff S' Q) = symmDiff S S' := by
    ext v
    simp only [Finset.mem_symmDiff]
    tauto
  obtain ⟨hQc, -⟩ := mem_oddComponents.mp hQ
  ext Q'
  rw [mem_oddComponents, mem_oddComponents, hU]
  refine and_congr_right fun hQ'c => ?_
  by_cases hQQ' : Q = Q'
  · subst hQQ'
    have h1 : symmDiff S Q ∩ Q = S' ∩ Q := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_symmDiff]
      constructor
      · rintro ⟨h | h, hvQ⟩
        · exact absurd hvQ h.2
        · refine ⟨?_, hvQ⟩
          rcases mem_left_xor_right_of_isInducedComponent hQc hvQ with h' | h'
          · exact absurd h'.1 h.2
          · exact h'.1
      · rintro ⟨hvS', hvQ⟩
        refine ⟨Or.inr ⟨hvQ, ?_⟩, hvQ⟩
        rcases mem_left_xor_right_of_isInducedComponent hQc hvQ with h' | h'
        · exact absurd hvS' h'.2
        · exact h'.2
    have h2 : symmDiff S' Q ∩ Q = S ∩ Q := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_symmDiff]
      constructor
      · rintro ⟨h | h, hvQ⟩
        · exact absurd hvQ h.2
        · refine ⟨?_, hvQ⟩
          rcases mem_left_xor_right_of_isInducedComponent hQc hvQ with h' | h'
          · exact h'.1
          · exact absurd h'.1 h.2
      · rintro ⟨hvS, hvQ⟩
        refine ⟨Or.inr ⟨hvQ, ?_⟩, hvQ⟩
        rcases mem_left_xor_right_of_isInducedComponent hQc hvQ with h' | h'
        · exact h'.2
        · exact absurd hvS h'.2
    rw [h1, h2, crossCount_comm]
  · have hdisj : Disjoint Q Q' := by
      have := disjoint_of_isInducedComponent_of_ne hQc hQ'c (fun h => hQQ' (Finset.coe_injective h))
      exact Finset.disjoint_coe.mp this
    have h1 : symmDiff S Q ∩ Q' = S ∩ Q' := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_symmDiff]
      constructor
      · rintro ⟨h | h, hvQ'⟩
        · exact ⟨h.1, hvQ'⟩
        · exact absurd h.1 (Finset.disjoint_right.mp hdisj hvQ')
      · rintro ⟨hvS, hvQ'⟩
        exact ⟨Or.inl ⟨hvS, Finset.disjoint_right.mp hdisj hvQ'⟩, hvQ'⟩
    have h2 : symmDiff S' Q ∩ Q' = S' ∩ Q' := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_symmDiff]
      constructor
      · rintro ⟨h | h, hvQ'⟩
        · exact ⟨h.1, hvQ'⟩
        · exact absurd h.1 (Finset.disjoint_right.mp hdisj hvQ')
      · rintro ⟨hvS, hvQ'⟩
        exact ⟨Or.inl ⟨hvS, Finset.disjoint_right.mp hdisj hvQ'⟩, hvQ'⟩
    rw [h1, h2]

/-- A fixed odd component of `G[S ⊕ S']`, chosen as a function of the set
`𝒬(S, S')` alone (and `∅` when `𝒬(S, S')` is empty).  This is the "fixed path
component of `G[S ⊕ S']` by which corresponding terms are paired" of v1 L899-902. -/
noncomputable def chosenOddComponent [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (S S' : Finset V) : Finset V :=
  if h : (G.oddComponents S S').Nonempty then h.choose else ∅

/-- The chosen odd component lies in `𝒬(S, S')` whenever that set is nonempty. -/
theorem chosenOddComponent_mem [Fintype V] [DecidableEq V] {S S' : Finset V}
    (h : (G.oddComponents S S').Nonempty) :
    G.chosenOddComponent S S' ∈ G.oddComponents S S' := by
  unfold chosenOddComponent
  rw [dif_pos h]
  exact h.choose_spec

/-- The chosen component only depends on the set `𝒬(S, S')`. -/
theorem chosenOddComponent_congr [Fintype V] [DecidableEq V] {S S' T T' : Finset V}
    (h : G.oddComponents S S' = G.oddComponents T T') :
    G.chosenOddComponent S S' = G.chosenOddComponent T T' := by
  unfold chosenOddComponent
  simp only [h]

/-- The chosen component of the pair `(S, S')` is invariant under toggling an odd
component `Q` in both arguments: the toggled term is paired by the same component
(v1 L899-902). -/
theorem chosenOddComponent_symmDiff [Fintype V] [DecidableEq V] {S S' Q : Finset V}
    (hQ : Q ∈ G.oddComponents S S') :
    G.chosenOddComponent (symmDiff S Q) (symmDiff S' Q) = G.chosenOddComponent S S' :=
  chosenOddComponent_congr (oddComponents_symmDiff hQ)

/-- The chosen component is symmetric in the two arguments. -/
theorem chosenOddComponent_comm [Fintype V] [DecidableEq V] (S S' : Finset V) :
    G.chosenOddComponent S' S = G.chosenOddComponent S S' :=
  chosenOddComponent_congr (oddComponents_comm S S')

/-- For independent `S, S'` with `c(S, S')` odd the set `𝒬(S, S')` is nonempty
(v1 L895: some component of `G[S ⊕ S']` has an odd number of edges; this is
`exists_isInducedComponent_odd`, which does not need claw-freeness). -/
theorem oddComponents_nonempty_of_odd [Fintype V] [DecidableEq V] {S S' : Finset V}
    (hS : G.IsIndepSet (S : Set V)) (hS' : G.IsIndepSet (S' : Set V))
    (hodd : Odd (G.crossCount S S')) : (G.oddComponents S S').Nonempty := by
  obtain ⟨Q, hQ, hQodd⟩ := exists_isInducedComponent_odd hS hS' hodd
  exact ⟨Q, mem_oddComponents.mpr ⟨hQ, hQodd⟩⟩

/-- For independent `S, S'` with `c(S, S')` odd, the chosen component is an odd
component of `G[S ⊕ S']`. -/
theorem chosenOddComponent_mem_of_odd [Fintype V] [DecidableEq V] {S S' : Finset V}
    (hS : G.IsIndepSet (S : Set V)) (hS' : G.IsIndepSet (S' : Set V))
    (hodd : Odd (G.crossCount S S')) :
    G.chosenOddComponent S S' ∈ G.oddComponents S S' :=
  chosenOddComponent_mem (oddComponents_nonempty_of_odd hS hS' hodd)

/-! ### Pairwise cancellation of independent-set products -/

namespace PauliFrustrationRepresentation

variable {A : Type w} [Ring A]

/-- (2) of the package (v1 L897-899): for independent `S, S'` and an odd component
`Q ∈ 𝒬(S, S')` of `G[S ⊕ S']`,
`h_S h_{S'} + h_{S ⊕ Q} h_{S' ⊕ Q} = 0`.

With `T = S ∩ Q` and `T' = S' ∩ Q` one has `h_S = h_{S∖Q} h_T`,
`h_{S'} = h_{T'} h_{S'∖Q}`, `h_{S ⊕ Q} = h_{S∖Q} h_{T'}` and
`h_{S' ⊕ Q} = h_T h_{S'∖Q}`, so the sum is
`h_{S∖Q} (h_T h_{T'} + h_{T'} h_T) h_{S'∖Q} = 0` because `c(T, T')` is odd. -/
theorem independentProduct_toggle_add_eq_zero [Fintype V] [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) {S S' Q : Finset V}
    (hS : G.IsIndepSet (S : Set V)) (hS' : G.IsIndepSet (S' : Set V))
    (hQ : Q ∈ G.oddComponents S S') :
    H.independentProduct S * H.independentProduct S' +
      H.independentProduct (symmDiff S Q) * H.independentProduct (symmDiff S' Q) = 0 := by
  obtain ⟨hQc, hodd⟩ := mem_oddComponents.mp hQ
  have hQc' : G.IsInducedComponent ↑(symmDiff S' S) ↑Q := by
    rwa [symmDiff_comm S' S]
  have hSQ : G.IsIndepSet ((symmDiff S Q : Finset V) : Set V) :=
    isIndepSet_symmDiff_of_isInducedComponent hS hS' hQc
  have hS'Q : G.IsIndepSet ((symmDiff S' Q : Finset V) : Set V) :=
    isIndepSet_symmDiff_of_isInducedComponent hS' hS hQc'
  have hT : G.IsIndepSet ((S ∩ Q : Finset V) : Set V) :=
    IsIndepSet.finset_subset hS Finset.inter_subset_left
  have hT' : G.IsIndepSet ((S' ∩ Q : Finset V) : Set V) :=
    IsIndepSet.finset_subset hS' Finset.inter_subset_left
  -- the four decompositions
  have e1 : S = (S \ Q) ∪ (S ∩ Q) := by
    ext v; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]; tauto
  have e2 : S' = (S' ∩ Q) ∪ (S' \ Q) := by
    ext v; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]; tauto
  have e3 : symmDiff S Q = (S \ Q) ∪ (S' ∩ Q) := by
    ext v
    simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · refine Or.inr ⟨?_, h.1⟩
        rcases mem_left_xor_right_of_isInducedComponent hQc h.1 with h' | h'
        · exact absurd h'.1 h.2
        · exact h'.1
    · rintro (h | h)
      · exact Or.inl h
      · refine Or.inr ⟨h.2, ?_⟩
        rcases mem_left_xor_right_of_isInducedComponent hQc h.2 with h' | h'
        · exact absurd h.1 h'.2
        · exact h'.2
  have e4 : symmDiff S' Q = (S ∩ Q) ∪ (S' \ Q) := by
    ext v
    simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · refine Or.inl ⟨?_, h.1⟩
        rcases mem_left_xor_right_of_isInducedComponent hQc h.1 with h' | h'
        · exact h'.1
        · exact absurd h'.1 h.2
    · rintro (h | h)
      · refine Or.inr ⟨h.2, ?_⟩
        rcases mem_left_xor_right_of_isInducedComponent hQc h.2 with h' | h'
        · exact h'.2
        · exact absurd h.1 h'.2
      · exact Or.inl h
  -- disjointness of the blocks
  have d1 : Disjoint (S \ Q) (S ∩ Q) := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_inter.mp hv').2
  have d2 : Disjoint (S' ∩ Q) (S' \ Q) := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    exact (Finset.mem_sdiff.mp hv').2 (Finset.mem_inter.mp hv).2
  have d3 : Disjoint (S \ Q) (S' ∩ Q) := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_inter.mp hv').2
  have d4 : Disjoint (S ∩ Q) (S' \ Q) := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    exact (Finset.mem_sdiff.mp hv').2 (Finset.mem_inter.mp hv).2
  have hS1 : H.independentProduct S =
      H.independentProduct (S \ Q) * H.independentProduct (S ∩ Q) := by
    conv_lhs => rw [e1]
    exact H.independentProduct_union d1 (e1 ▸ hS)
  have hS2 : H.independentProduct S' =
      H.independentProduct (S' ∩ Q) * H.independentProduct (S' \ Q) := by
    conv_lhs => rw [e2]
    exact H.independentProduct_union d2 (e2 ▸ hS')
  have hS3 : H.independentProduct (symmDiff S Q) =
      H.independentProduct (S \ Q) * H.independentProduct (S' ∩ Q) := by
    conv_lhs => rw [e3]
    exact H.independentProduct_union d3 (e3 ▸ hSQ)
  have hS4 : H.independentProduct (symmDiff S' Q) =
      H.independentProduct (S ∩ Q) * H.independentProduct (S' \ Q) := by
    conv_lhs => rw [e4]
    exact H.independentProduct_union d4 (e4 ▸ hS'Q)
  have hanti := H.independentProduct_mul_independentProduct_of_odd hT hT' hodd
  rw [hS1, hS2, hS3, hS4]
  calc
    H.independentProduct (S \ Q) * H.independentProduct (S ∩ Q) *
        (H.independentProduct (S' ∩ Q) * H.independentProduct (S' \ Q)) +
      H.independentProduct (S \ Q) * H.independentProduct (S' ∩ Q) *
        (H.independentProduct (S ∩ Q) * H.independentProduct (S' \ Q)) =
      H.independentProduct (S \ Q) *
        (H.independentProduct (S ∩ Q) * H.independentProduct (S' ∩ Q) +
          H.independentProduct (S' ∩ Q) * H.independentProduct (S ∩ Q)) *
        H.independentProduct (S' \ Q) := by
      simp only [mul_add, add_mul, mul_assoc]
    _ = 0 := by
      rw [hanti]
      simp

/-- Mirror of `independentProduct_toggle_add_eq_zero` with the two factors of each
product exchanged: `h_{S'} h_S + h_{S' ⊕ Q} h_{S ⊕ Q} = 0` for `Q ∈ 𝒬(S, S')`
(apply the theorem to the pair `(S', S)`, using `𝒬(S', S) = 𝒬(S, S')`). -/
theorem independentProduct_toggle_add_eq_zero_swap [Fintype V] [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) {S S' Q : Finset V}
    (hS : G.IsIndepSet (S : Set V)) (hS' : G.IsIndepSet (S' : Set V))
    (hQ : Q ∈ G.oddComponents S S') :
    H.independentProduct S' * H.independentProduct S +
      H.independentProduct (symmDiff S' Q) * H.independentProduct (symmDiff S Q) = 0 :=
  H.independentProduct_toggle_add_eq_zero hS' hS ((oddComponents_comm (G := G) S S').symm ▸ hQ)

/-- Commutator form (v1 L897-899): for `Q ∈ 𝒬(S, S')`,
`[h_S, h_{S'}] + [h_{S ⊕ Q}, h_{S' ⊕ Q}] = 0`.  Both summands of the sum of the
two products and of their mirror images vanish separately; this is what the
sign-reversing pairing of Theorem 1(i) uses. -/
theorem independentProduct_toggle_commutator_add_eq_zero [Fintype V] [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) {S S' Q : Finset V}
    (hS : G.IsIndepSet (S : Set V)) (hS' : G.IsIndepSet (S' : Set V))
    (hQ : Q ∈ G.oddComponents S S') :
    (H.independentProduct S * H.independentProduct S' -
        H.independentProduct S' * H.independentProduct S) +
      (H.independentProduct (symmDiff S Q) * H.independentProduct (symmDiff S' Q) -
        H.independentProduct (symmDiff S' Q) * H.independentProduct (symmDiff S Q)) = 0 := by
  have h1 := H.independentProduct_toggle_add_eq_zero hS hS' hQ
  have h2 := H.independentProduct_toggle_add_eq_zero_swap hS hS' hQ
  rw [← add_sub_add_comm, h1, h2, sub_zero]

end PauliFrustrationRepresentation

end SimpleGraph
