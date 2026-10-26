import FreeFermionGraphs.PauliCliqueHamiltonianOddSupport
import FreeFermionGraphs.CliqueRootedPathOriginalTail
import FreeFermionGraphs.InducedPathDeformationReverse
import FreeFermionGraphs.InducedPathDeformationBubbleWand

/-!
# The closed neighbourhood of a rooted path is invariant under deformation

For a rooted induced path `P = (j*, j₁, …, j_ℓ)` of `G* = G.adjoinRootAt K`
(manuscript Definition 17), put

`N(P) := K ∪ ⋃_{i ≥ 1} Γ_G[j_i]`.

The main results are:

* `RootedInducedPath.closedNbhd_deform`: if `K` is a simplicial clique and
  `G` is claw-free, then `N` does not change under a single-vertex
  deformation (v1 Definition `singlevertexdeformation`, with the clone
  condition `Γ_P(s) = j_{i-1} - j_i - j_{i+1}` in `G*`).
* `RootedInducedPath.closedNbhd_eq_of_closure`: consequently `N` is constant
  on every deformation closure `⟨P⟩`.

This is not a statement of the v1 manuscript (arXiv 2305.15625v1).  It is the
graph-theoretic lemma that replaces the "last-crossing" walk-substitution step
in the proof of Lemma `deformationclosurepathsrelation` (v1 L1466-1485), which
is not defined on every walk.  Claw-freeness of `G*` at the clone (v1 L850:
`G*` is simplicial and claw-free when `K` is a simplicial clique) is genuinely
needed: for the first internal index the left leaf of the claw is the root
`j*`, and that is where simpliciality of `K` enters, through
`IsSimplicialClique.isClawFree_adjoinRootAt`.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace RootedInducedPath

variable {G : SimpleGraph V} {K : Set V}

/-- The closed neighbourhood `N(P) = K ∪ ⋃_{i ≥ 1} Γ_G[j_i]` of a rooted
induced path `P = (j*, j₁, …, j_ℓ)` of `G*`: the clique `K` together with the
closed neighbourhoods in `G` of the original vertices of `P`. -/
def closedNbhd (P : CliqueRootedInducedPath G K) : Set V :=
  K ∪ ⋃ v ∈ P.originalCarrier, G.closedNeighborhood v

theorem subset_closedNbhd (P : CliqueRootedInducedPath G K) :
    K ⊆ P.closedNbhd :=
  Set.subset_union_left

/-- The closed neighbourhood of an original vertex of `P` lies in `N(P)`. -/
theorem closedNeighborhood_subset_closedNbhd
    (P : CliqueRootedInducedPath G K) {v : V}
    (hv : v ∈ P.originalCarrier) :
    G.closedNeighborhood v ⊆ P.closedNbhd := by
  intro x hx
  exact Or.inr (Set.mem_iUnion₂.mpr ⟨v, hv, hx⟩)

/-- An original vertex of `P` lies in `N(P)`. -/
theorem mem_closedNbhd_of_vertex_eq
    (P : CliqueRootedInducedPath G K) (q : Fin P.path.card) {y : V}
    (hq : P.path.vertex q = some y) : y ∈ P.closedNbhd :=
  P.closedNeighborhood_subset_closedNbhd ⟨q, hq⟩ (Or.inl rfl)

/-- A vertex `y` of `G` adjacent in `G*` to some vertex of `P` lies in
`N(P)`: if the vertex of `P` is the root then `y ∈ K`, and otherwise `y` lies
in the closed neighbourhood of an original vertex of `P`. -/
theorem mem_closedNbhd_of_adj
    (P : CliqueRootedInducedPath G K) (q : Fin P.path.card) {y : V}
    (hadj : (G.adjoinRootAt K).Adj (P.path.vertex q) (some y)) :
    y ∈ P.closedNbhd := by
  cases hq : P.path.vertex q with
  | none =>
      rw [hq] at hadj
      exact P.subset_closedNbhd hadj
  | some v =>
      rw [hq] at hadj
      exact P.closedNeighborhood_subset_closedNbhd ⟨q, hq⟩ (Or.inr hadj)

/-- Key step: the closed neighbourhood of a clone `k` of the internal vertex
`j_i` lies in `N(P)`.  Indeed, for `y ∈ Γ_G(k)` the vertices `j_{i-1}`,
`j_{i+1}`, `y` are neighbours of `k` in `G*`, so claw-freeness of `G*` forces
`y` to be adjacent to (or equal to) one of `j_{i-1}`, `j_{i+1}`, the two
being non-adjacent because `P` is induced; if the adjacent one is the root
`j*` then `y ∈ K`. -/
theorem closedNeighborhood_clone_subset_closedNbhd
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree)
    (P : CliqueRootedInducedPath G K) {k : V} {i : Fin P.path.card}
    (h : P.path.SingleVertexDeformation (some k) i) :
    G.closedNeighborhood k ⊆ P.closedNbhd := by
  have hclaw' := hK.isClawFree_adjoinRootAt hclaw
  obtain ⟨j, hj⟩ := P.vertex_eq_some_of_pos i h.internal_left
  have hij : (G.adjoinRootAt K).Adj (some k) (P.path.vertex i) :=
    (h.adj_iff i).2 (Or.inl rfl)
  intro y hy
  rcases hy with rfl | hy
  · -- `k ∈ Γ[j_i]`
    rw [hj] at hij
    exact P.closedNeighborhood_subset_closedNbhd ⟨i, hj⟩ (Or.inr hij.symm)
  · -- `y ∈ Γ_G(k)`
    have hky : (G.adjoinRootAt K).Adj (some k) (some y) := hy
    set ia : Fin P.path.card := ⟨i.val - 1, by omega⟩ with hia
    set ib : Fin P.path.card := ⟨i.val + 1, h.internal_right⟩ with hib
    have hi_a : (G.adjoinRootAt K).Adj (P.path.vertex i) (P.path.vertex ia) :=
      (P.path.adj_iff i ia).2
        (Or.inr (by simp only [hia]; have := h.internal_left; omega))
    have hi_b : (G.adjoinRootAt K).Adj (P.path.vertex i) (P.path.vertex ib) :=
      (P.path.adj_iff i ib).2 (Or.inl rfl)
    have hka : (G.adjoinRootAt K).Adj (some k) (P.path.vertex ia) :=
      (h.adj_iff ia).2 (Or.inr hi_a)
    have hkb : (G.adjoinRootAt K).Adj (some k) (P.path.vertex ib) :=
      (h.adj_iff ib).2 (Or.inr hi_b)
    have hab_ne : P.path.vertex ia ≠ P.path.vertex ib := by
      intro heq
      have := congrArg Fin.val (P.path.injective heq)
      simp only [hia, hib] at this
      have := h.internal_left
      omega
    have hab_nadj : ¬(G.adjoinRootAt K).Adj (P.path.vertex ia) (P.path.vertex ib) := by
      intro hadj
      rcases (P.path.adj_iff ia ib).1 hadj with hh | hh <;>
        · simp only [hia, hib] at hh
          have := h.internal_left
          omega
    by_cases hya : P.path.vertex ia = some y
    · exact P.mem_closedNbhd_of_vertex_eq ia hya
    by_cases hyb : P.path.vertex ib = some y
    · exact P.mem_closedNbhd_of_vertex_eq ib hyb
    rcases hclaw' hka hkb hky hab_ne hya hyb with
      hh | hh | hh
    · exact (hab_nadj hh).elim
    · exact P.mem_closedNbhd_of_adj ia hh
    · exact P.mem_closedNbhd_of_adj ib hh

/-- One inclusion of the invariance: after a single-vertex deformation the
closed neighbourhood can only shrink. -/
theorem closedNbhd_deform_subset
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree)
    (P : CliqueRootedInducedPath G K) {s : Option V}
    {i : Fin P.path.card} (h : P.path.SingleVertexDeformation s i) :
    (P.deform h).closedNbhd ⊆ P.closedNbhd := by
  obtain ⟨k, rfl⟩ := P.deformation_vertex_eq_some h
  intro x hx
  rcases hx with hxK | hx
  · exact P.subset_closedNbhd hxK
  · obtain ⟨v, ⟨q, hq⟩, hxv⟩ := Set.mem_iUnion₂.mp hx
    by_cases hqi : q = i
    · have hvk : v = k := by
        have : (P.path.deform h).vertex q = some k := by
          rw [hqi]
          exact P.path.deform_vertex_at h
        exact Option.some.inj (hq.symm.trans this)
      subst hvk
      exact closedNeighborhood_clone_subset_closedNbhd hK hclaw P h hxv
    · have hqv : P.path.vertex q = some v :=
        (P.path.deform_vertex_away h hqi).symm.trans hq
      exact P.closedNeighborhood_subset_closedNbhd ⟨q, hqv⟩ hxv

/-- Paper-facing statement: `N(P~) = N(P)` for a single-vertex deformation
`P~` of the rooted path `P` (internal index `i`, clone `s` with
`Γ_P(s) = j_{i-1} - j_i - j_{i+1}` in `G*`), when `K` is a simplicial clique
and `G` is claw-free.  The reverse inclusion is the first inclusion applied to
the reverse deformation of `P~`, which recovers `P`. -/
theorem closedNbhd_deform
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree)
    (P : CliqueRootedInducedPath G K) {s : Option V}
    {i : Fin P.path.card} (h : P.path.SingleVertexDeformation s i) :
    (P.deform h).closedNbhd = P.closedNbhd := by
  apply Set.Subset.antisymm (closedNbhd_deform_subset hK hclaw P h)
  have hrev : (P.deform h).deform h.reverse = P :=
    ext_path (IndexedInducedPath.SingleVertexDeformation.deform_reverse_eq
      P.path h)
  have := closedNbhd_deform_subset hK hclaw (P.deform h) h.reverse
  rwa [hrev] at this

/-- Every indexed path in the deformation closure of a clique-rooted path lifts
to a clique-rooted path with the same closed neighbourhood. -/
theorem exists_rooted_closedNbhd_eq_of_closure
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree)
    (P : CliqueRootedInducedPath G K) {Q : IndexedInducedPath (G.adjoinRootAt K)}
    (hPQ : InInducedPathDeformationClosure (G.adjoinRootAt K) P.path Q) :
    ∃ Q' : CliqueRootedInducedPath G K,
      Q'.path = Q ∧ Q'.closedNbhd = P.closedNbhd := by
  generalize hP : P.path = P0 at hPQ
  induction hPQ with
  | refl => exact ⟨P, hP, rfl⟩
  | tail _ hstep ih =>
      obtain ⟨Q', hQ', hnb⟩ := ih
      obtain ⟨s, i, hdef, rfl⟩ := hstep
      subst hQ'
      exact ⟨Q'.deform hdef, rfl, (closedNbhd_deform hK hclaw Q' hdef).trans hnb⟩

/-- `N` is constant on every deformation closure `⟨P⟩` (v1 Definition
`deformationclosure`, here with respect to the induced paths of `G*`). -/
theorem closedNbhd_eq_of_closure
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree)
    {P P' : CliqueRootedInducedPath G K}
    (h : InInducedPathDeformationClosure (G.adjoinRootAt K) P.path P'.path) :
    P'.closedNbhd = P.closedNbhd := by
  obtain ⟨Q', hQ', hnb⟩ := exists_rooted_closedNbhd_eq_of_closure hK hclaw P h
  rw [← ext_path hQ']
  exact hnb

end RootedInducedPath

end SimpleGraph
