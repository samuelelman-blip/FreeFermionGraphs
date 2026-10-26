import FreeFermionGraphs.EvenHoleOperators

/-!
# Even holes versus a simplicial clique

Let `Ks` be a simplicial clique of `G` (`SimpleGraph.IsSimplicialClique`: `Ks` is a clique
and, for every `j ∈ Ks`, the neighbours of `j` outside `Ks` form a clique) and let `C` be an
even hole.  Manuscript arXiv 2305.15625 v1 uses the following three facts without proof:

* Result 2, first claim (L110): the simplicial-mode operator `χ` commutes with every
  generalized cycle symmetry `J_{⟨C₀⟩}`;
* the Ladder proof (L2088-2093) treats `Z_{G\Ks}` as a scalar on the joint eigenspace `Π_J`,
  which again needs `χ` to commute with `J` and the closure `⟨C₀⟩` to be disjoint from `Ks`.

Both follow from the statements below, an unstated lemma of v1 (no claw-freeness is needed
for any part).

## Results

* `IsSimplicialClique.not_mem_of_nonadj_neighbors` : a vertex with two distinct nonadjacent
  neighbours outside `Ks` is not in `Ks` (the contrapositive of simpliciality).
* `IsSimplicialClique.ncard_inter_evenHoleCarrier` (a) : `|Ks ∩ C| ∈ {0, 2}`.  Indeed `Ks ∩ C`
  is a clique of the triangle-free graph `G[C]`, so has at most two vertices; and a single
  vertex `j ∈ Ks ∩ C` would have its two nonadjacent cycle neighbours outside `Ks`, which
  simpliciality forbids.  In particular `|Ks ∩ C|` is even
  (`IsSimplicialClique.even_ncard_inter_evenHoleCarrier`).
* `PauliFrustrationRepresentation.root_commute_evenHoleOperator` (b) : the root term
  `χ = Hp.term none` commutes with `h_C` for every `C`; the restriction `Hp.restrictSome`
  of a representation of `G.adjoinRootAt Ks` to the original vertices is the
  representation of `G`.  Moving `χ` across the independent product `h_S` costs the sign
  `(-1)^{|Ks ∩ S|}` (`root_mul_independentProduct`, from v1 Definition 8, L591), so `χ`
  commutes with `h_C = h_{C_a} h_{C_b}` because `|Ks ∩ C_a| + |Ks ∩ C_b| = |Ks ∩ C|` is
  even.  Consequently `χ` commutes with every `J_{⟨C₀⟩}`
  (`root_commute_cycleSymmetry`; in the repo `J_{⟨C₀⟩}` is `generalizedCycleSymmetryOp`).
* `InEvenHoleDeformationClosure.disjoint_simplicial` (c) : if an even hole `A` avoids `Ks`
  then every member of its deformation closure avoids `Ks`.  One deformation step
  replaces the vertex `a i` of a labelled hole by its clone `s`; whichever of the two lies
  in `Ks` would have the two nonadjacent hole neighbours `b i`, `b (next i)`, both outside
  `Ks` (the clone is adjacent to them by `CloneAt.adj_b`, `CloneAt.adj_b_next`), contradicting
  simpliciality.  The hole hypothesis is in fact not needed
  (`InEvenHoleDeformationClosure.disjoint_of_isSimplicialClique`).
-/

open scoped BigOperators

universe u w

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V} {Ks : Set V}

/-! ### Simpliciality, contrapositively -/

namespace IsSimplicialClique

/-- A vertex with two distinct nonadjacent neighbours outside a simplicial clique `Ks` is
itself outside `Ks`: for `x ∈ Ks` the neighbours of `x` outside `Ks` form a clique. -/
theorem not_mem_of_nonadj_neighbors (hKs : G.IsSimplicialClique Ks) {x u v : V}
    (hxu : G.Adj x u) (hxv : G.Adj x v) (huv : u ≠ v) (hnadj : ¬ G.Adj u v)
    (hu : u ∉ Ks) (hv : v ∉ Ks) : x ∉ Ks := fun hx =>
  hnadj (hKs.externalNeighbors_isClique hx
    (show u ∈ G.neighborSet x \ Ks from ⟨hxu, hu⟩)
    (show v ∈ G.neighborSet x \ Ks from ⟨hxv, hv⟩) huv)

/-! ### (a) An even hole meets a simplicial clique in `0` or `2` vertices -/

/-- (a) An even hole `C` meets a simplicial clique `Ks` in `0` or `2` vertices.

`Ks ∩ C` is a clique inside the triangle-free graph `G[C]`, so it has at most two vertices.
A single vertex `j ∈ Ks ∩ C` is impossible: its two nonadjacent cycle neighbours then lie
outside `Ks`, whereas the neighbours of `j` outside `Ks` form a clique.  Neither
claw-freeness nor the evenness of the hole is used (v1 does not state this fact; it uses it
at L110 and L2088-2093). -/
theorem ncard_inter_evenHoleCarrier {C : Set V} (hKs : G.IsSimplicialClique Ks)
    (hC : G.IsEvenHoleCarrier C) :
    (Ks ∩ C).ncard = 0 ∨ (Ks ∩ C).ncard = 2 := by
  obtain ⟨H, -, rfl⟩ := hC
  have hfin : (Ks ∩ Set.range H.vertex).Finite :=
    (Set.finite_range _).subset Set.inter_subset_right
  have hle : (Ks ∩ Set.range H.vertex).ncard ≤ 2 := by
    by_contra hgt
    have hgt : 2 < (Ks ∩ Set.range H.vertex).ncard := not_le.1 hgt
    obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := (Set.two_lt_ncard hfin).1 hgt
    obtain ⟨i, rfl⟩ := hx.2
    obtain ⟨j, rfl⟩ := hy.2
    obtain ⟨l, rfl⟩ := hz.2
    have hij := (H.adj_iff i j).1 (hKs.isClique hx.1 hy.1 hxy)
    have hil := (H.adj_iff i l).1 (hKs.isClique hx.1 hz.1 hxz)
    have hjl := (H.adj_iff j l).1 (hKs.isClique hy.1 hz.1 hyz)
    have hne1 : i ≠ j := fun h => hxy (by rw [h])
    have hne2 : i ≠ l := fun h => hxz (by rw [h])
    have hne3 : j ≠ l := fun h => hyz (by rw [h])
    have hi := i.isLt
    have hj := j.isLt
    have hl := l.isLt
    have h4 := H.four_le_card
    have hne1' : i.val ≠ j.val := fun h => hne1 (Fin.ext h)
    have hne2' : i.val ≠ l.val := fun h => hne2 (Fin.ext h)
    have hne3' : j.val ≠ l.val := fun h => hne3 (Fin.ext h)
    unfold CyclicAdjacent at hij hil hjl
    omega
  have hne : (Ks ∩ Set.range H.vertex).ncard ≠ 1 := by
    intro h1
    obtain ⟨j, hj⟩ := Set.ncard_eq_one.1 h1
    have hjmem : j ∈ Ks ∩ Set.range H.vertex := by rw [hj]; exact rfl
    obtain ⟨i, rfl⟩ := hjmem.2
    obtain ⟨u, v, huv, hiu, hiv, huvadj⟩ := H.exists_two_nonadjacent_neighbors i
    have hout : ∀ w : Fin H.card, G.Adj (H.vertex i) (H.vertex w) → H.vertex w ∉ Ks := by
      intro w hw hwK
      have hmem : H.vertex w ∈ Ks ∩ Set.range H.vertex := ⟨hwK, w, rfl⟩
      rw [hj] at hmem
      exact G.ne_of_adj hw hmem.symm
    exact hKs.not_mem_of_nonadj_neighbors hiu hiv (fun h => huv (H.injective h)) huvadj
      (hout u hiu) (hout v hiv) hjmem.1
  omega

/-- The intersection of a simplicial clique with an even hole has even cardinality. -/
theorem even_ncard_inter_evenHoleCarrier {C : Set V} (hKs : G.IsSimplicialClique Ks)
    (hC : G.IsEvenHoleCarrier C) : Even (Ks ∩ C).ncard := by
  rcases hKs.ncard_inter_evenHoleCarrier hC with h | h
  · rw [h]; exact ⟨0, rfl⟩
  · rw [h]; exact ⟨1, rfl⟩

end IsSimplicialClique

/-! ### (c) Deformation steps and closures preserve avoiding a simplicial clique -/

namespace EvenHoleLabeling

/-- If the deformed carrier `{s} ∪ (C \ {a i})` avoids a simplicial clique `Ks`, so does the
carrier `C`: the vertex `a i` has the two nonadjacent neighbours `b i`, `b (next i)` outside
`Ks`. -/
theorem disjoint_carrier_of_disjoint_deformedCarrier (hKs : G.IsSimplicialClique Ks)
    {k : ℕ} (L : G.EvenHoleLabeling k) (s : V) (i : Fin k)
    (h : Disjoint (L.deformedCarrier s i) Ks) : Disjoint L.carrier Ks := by
  have hai : L.a i ∉ Ks :=
    hKs.not_mem_of_nonadj_neighbors (L.adj_a_b i) (L.adj_a_b_next i)
      (fun h' => L.b_ne_next i h'.symm) (L.adj_bb _ _)
      (Set.disjoint_left.1 h (L.b_mem_deformedCarrier s i))
      (Set.disjoint_left.1 h (L.b_next_mem_deformedCarrier s i))
  refine Set.disjoint_left.2 fun x hx hxK => ?_
  by_cases hxa : x = L.a i
  · exact hai (hxa ▸ hxK)
  · exact Set.disjoint_left.1 h (L.mem_deformedCarrier_of_mem hx hxa) hxK

/-- If the carrier of a labelling avoids a simplicial clique `Ks`, then so does the deformed
carrier `{s} ∪ (C \ {a i})` of a clone `s ≺ a i`: the clone is adjacent to the two
nonadjacent vertices `b i`, `b (next i)`, which lie outside `Ks`. -/
theorem disjoint_deformedCarrier_of_disjoint_carrier (hKs : G.IsSimplicialClique Ks)
    {k : ℕ} (L : G.EvenHoleLabeling k) {s : V} {i : Fin k} (hcl : L.CloneAt s i)
    (h : Disjoint L.carrier Ks) : Disjoint (L.deformedCarrier s i) Ks := by
  have hs : s ∉ Ks :=
    hKs.not_mem_of_nonadj_neighbors hcl.adj_b hcl.adj_b_next
      (fun h' => L.b_ne_next i h'.symm) (L.adj_bb _ _)
      (Set.disjoint_left.1 h (L.b_mem_carrier i))
      (Set.disjoint_left.1 h (L.b_mem_carrier (L.next i)))
  refine Set.disjoint_left.2 fun x hx hxK => ?_
  rcases hx with rfl | ⟨hxC, -⟩
  · exact hs hxK
  · exact Set.disjoint_left.1 h hxC hxK

end EvenHoleLabeling

/-- Strong form of (c): if a set `A` avoids a simplicial clique `Ks`, then every set related
to `A` by the deformation closure avoids `Ks`.  Neither claw-freeness nor a hole hypothesis
on `A` is needed. -/
theorem InEvenHoleDeformationClosure.disjoint_of_isSimplicialClique {A B : Set V}
    (hKs : G.IsSimplicialClique Ks) (hclo : InEvenHoleDeformationClosure G A B)
    (hAK : Disjoint A Ks) : Disjoint B Ks := by
  induction hclo with
  | refl => exact hAK
  | tail _ hstep ih =>
      obtain ⟨k, L, s, i, hcl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := hstep
      · exact L.disjoint_deformedCarrier_of_disjoint_carrier hKs hcl ih
      · exact L.disjoint_carrier_of_disjoint_deformedCarrier hKs s i ih

/-- (c) If an even hole `A` avoids a simplicial clique `Ks`, then every hole `B` in its
deformation closure `⟨A⟩` avoids `Ks` (v1 uses this at L2088-2093 without proof).  The hole
hypothesis `hA` is not needed (`disjoint_of_isSimplicialClique`) and is kept only to match
the manuscript statement. -/
theorem InEvenHoleDeformationClosure.disjoint_simplicial {A B : Set V}
    (hKs : G.IsSimplicialClique Ks) (hclo : InEvenHoleDeformationClosure G A B)
    (_hA : G.IsEvenHoleCarrier A) (hAK : Disjoint A Ks) : Disjoint B Ks :=
  hclo.disjoint_of_isSimplicialClique hKs hAK

/-! ### (b) The simplicial mode `χ` commutes with `h_C` and `J_{⟨C₀⟩}` -/

namespace PauliFrustrationRepresentation

variable {A : Type w} [Ring A]

/-- Moving the root term `χ` across the independent product `h_S` costs the sign
`(-1)^{|Ks ∩ S|}`: `χ` anticommutes with `h_j` exactly for `j ∈ Ks` (v1 Definition 8,
L591) and commutes with it otherwise. -/
theorem root_mul_independentProduct [DecidableEq V]
    (Hp : (G.adjoinRootAt Ks).PauliFrustrationRepresentation A)
    {S : Finset V} (hS : G.IsIndepSet (S : Set V)) :
    Hp.term none * Hp.restrictSome.independentProduct S =
      (-1 : A) ^ (Ks ∩ (S : Set V)).ncard *
        (Hp.restrictSome.independentProduct S * Hp.term none) := by
  classical
  have hU : (G.adjoinRootAt Ks).IsIndepSet
      ((S.map Function.Embedding.some : Finset (Option V)) : Set (Option V)) := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_map] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    show ¬(G.adjoinRootAt Ks).Adj (some a) (some b)
    rw [adjoinRootAt_adj_some_some]
    exact hS ha hb (fun h => hxy (by rw [h]))
  have hcount : (G.adjoinRootAt Ks).crossCount {none} (S.map Function.Embedding.some) =
      (Ks ∩ (S : Set V)).ncard := by
    rw [crossCount_eq_sum_card_filter, Finset.sum_singleton, Finset.filter_map,
      Finset.card_map, ← Set.ncard_coe_finset]
    congr 1
    ext v
    simp [adjoinRootAt_adj_none_some, and_comm]
  rw [← Hp.independentProduct_map_some hS, Hp.term_mul_independentProduct none hU, hcount]

/-- `χ` commutes with `h_S` whenever `|Ks ∩ S|` is even. -/
theorem root_commute_independentProduct_of_even [DecidableEq V]
    (Hp : (G.adjoinRootAt Ks).PauliFrustrationRepresentation A)
    {S : Finset V} (hS : G.IsIndepSet (S : Set V)) (heven : Even (Ks ∩ (S : Set V)).ncard) :
    Commute (Hp.term none) (Hp.restrictSome.independentProduct S) := by
  show Hp.term none * Hp.restrictSome.independentProduct S =
    Hp.restrictSome.independentProduct S * Hp.term none
  rw [Hp.root_mul_independentProduct hS, heven.neg_one_pow, one_mul]

/-- (b) `χ` commutes with `h_C` for every set `C` and every simplicial clique `Ks`: for an even
hole `h_C = h_{C_a} h_{C_b}` and `|Ks ∩ C_a| + |Ks ∩ C_b| = |Ks ∩ C|` is even by
`IsSimplicialClique.ncard_inter_evenHoleCarrier`; for a non-hole `h_C = 0`
(`evenHoleOperator_eq_zero_of_not_isEvenHoleCarrier`).  No claw-freeness is needed
(v1 Result 2, L110, unproved there). -/
theorem root_commute_evenHoleOperator [DecidableEq V]
    (Hp : (G.adjoinRootAt Ks).PauliFrustrationRepresentation A)
    (hKs : G.IsSimplicialClique Ks) (C : Set V) :
    Commute (Hp.term none) (Hp.restrictSome.evenHoleOperator C) := by
  classical
  by_cases hC : G.IsEvenHoleCarrier C
  · obtain ⟨k, L, -, rfl, hop⟩ := Hp.restrictSome.exists_fullCyclic_labeling_evenHoleOperator hC
    rw [hop]
    unfold labelingOperator
    set a := Hp.restrictSome.independentProduct (Finset.univ.image L.a) with ha
    set b := Hp.restrictSome.independentProduct (Finset.univ.image L.b) with hb
    set na := (Ks ∩ ((Finset.univ.image L.a : Finset V) : Set V)).ncard with hna
    set nb := (Ks ∩ ((Finset.univ.image L.b : Finset V) : Set V)).ncard with hnb
    have hsum : na + nb = (Ks ∩ L.carrier).ncard := by
      rw [hna, hnb, Finset.coe_image, Finset.coe_image, Finset.coe_univ, Set.image_univ,
        Set.image_univ, ← Set.ncard_union_eq]
      · rw [EvenHoleLabeling.carrier, Set.inter_union_distrib_left]
      · exact Set.disjoint_left.2 fun x hx hy => (L.disjoint_range_a_range_b).le_bot ⟨hx.2, hy.2⟩
    have heven : Even (na + nb) := by
      rw [hsum]; exact hKs.even_ncard_inter_evenHoleCarrier hC
    have h1 : Hp.term none * a =
        (-1 : A) ^ na * (a * Hp.term none) :=
      Hp.root_mul_independentProduct L.isIndepSet_image_a
    have h2 : Hp.term none * b =
        (-1 : A) ^ nb * (b * Hp.term none) :=
      Hp.root_mul_independentProduct L.isIndepSet_image_b
    show Hp.term none * (a * b) = (a * b) * Hp.term none
    calc Hp.term none * (a * b)
        = (Hp.term none * a) * b := (mul_assoc _ _ _).symm
      _ = ((-1 : A) ^ na * (a * Hp.term none)) * b := by rw [h1]
      _ = (-1 : A) ^ na * (a * (Hp.term none * b)) := by simp only [mul_assoc]
      _ = (-1 : A) ^ na * (a * ((-1 : A) ^ nb * (b * Hp.term none))) := by rw [h2]
      _ = (-1 : A) ^ na * ((-1 : A) ^ nb * (a * (b * Hp.term none))) := by
          rw [(neg_one_pow_commute nb a).symm.left_comm]
      _ = ((-1 : A) ^ na * (-1 : A) ^ nb) * (a * (b * Hp.term none)) := (mul_assoc _ _ _).symm
      _ = (a * b) * Hp.term none := by
          rw [← pow_add, heven.neg_one_pow, one_mul, mul_assoc]
  · rw [Hp.restrictSome.evenHoleOperator_eq_zero_of_not_isEvenHoleCarrier hC]
    exact Commute.zero_right _

/-- (b) `χ` commutes with every generalized cycle symmetry `J_{⟨C₀⟩} = Σ_{C ∈ ⟨C₀⟩} h_C`
(v1 Result 2, L110): each summand commutes by `root_commute_evenHoleOperator`. -/
theorem root_commute_cycleSymmetry [Fintype V] [DecidableEq V]
    (Hp : (G.adjoinRootAt Ks).PauliFrustrationRepresentation A)
    (hKs : G.IsSimplicialClique Ks) (C₀ : Set V) :
    Commute (Hp.term none) (Hp.restrictSome.generalizedCycleSymmetryOp C₀) := by
  unfold generalizedCycleSymmetryOp generalizedCycleSymmetry
  exact Commute.sum_right _ _ _ fun C _ => Hp.root_commute_evenHoleOperator hKs C

end PauliFrustrationRepresentation

end SimpleGraph
