import FreeFermionGraphs.KrylovTreeMatrix
import FreeFermionGraphs.PathClosedNeighborhood
import FreeFermionGraphs.IndexedPathAppend

/-!
# Children of a clique-rooted induced path

Let `Q` be a rooted induced path of `G* = G.adjoinRootAt K`, that is, a vertex
of the induced-path tree `I(K, G) = I(j*, G*)` of arXiv 2305.15625v1,
Definition (induced path tree, v1 L841-850).  The children of `Q` in that tree
are the one-vertex extensions `Q + x`.  The recursive definition of v1
(L841-850) takes, for the root `j`, the forest of the trees
`I(k, (G \ Γ[j]) ∪ {k})` over the neighbours `k ∈ Γ(j)`.  The statement
`childCandidates_eq_of_parent` below is the one-step form of that recursion
for the Lean (nonrecursive) tree: the children of a path `Q = P + q` are the
vertices of `Γ_G(q) \ N(P)`, where `N(P)` is the closed neighbourhood of
`PathClosedNeighborhood.lean`.  (The full equivalence between the recursive
definition and the Lean tree is not proved here.)  It is the graph-theoretic
input to the case analysis "(b.iii)" of Table 1 and to the recursion for the
closed form of the Krylov matrix.

* `RootedInducedPath.childCandidates Q` is the set of `x : V` for which `Q + x`
  is an induced path, i.e. `Q.path.TerminalExtensionData (some x)`; this is
  the Lean tree's own edge relation, so its characterisation is a theorem.
* `childCandidates_cliqueRootPath`: the children of the root path `{j*}`
  are the vertices of `K` (the neighbours of `j*` in `G*`).
* `childCandidates_eq_of_parent`: for `Q = P + q` one has
  `C(Q) = Γ_G(q) \ N(P)`.
* `childCandidates_isClique`: `C(Q)` is a clique, by the claw-freeness of `G*`
  at the terminal vertex `q` (v1 L850: `G*` is claw-free when `K` is a
  simplicial clique and `G` is claw-free).  When the predecessor of `q` is the
  root `j*`, the two leaves of the claw avoid `K`, and the simpliciality of
  `K` enters through `IsSimplicialClique.isClawFree_adjoinRootAt`.
* `closedNbhd_eq_parent_union`: `N(Q) = N(P) ⊔ C(Q)`, a disjoint union.
* `closedNbhd_appendTerminal`: `N(Q + x) = N(P) ∪ Γ[x]` for `x ∈ C(Q)`;
  `closedNbhd_appendTerminal_cliqueRootPath`: `N({j*} + x) = Γ[x]` for
  `x ∈ K`.
* `isOneVertexExtension_iff_exists_appendTerminal` and `appendTerminal_inj`
  identify the one-vertex extensions of `Q` with `x ∈ C(Q)`, bijectively
  (`childCandidatesEquivExtensions`).

None of this is stated as such in v1; the statements are graph-theoretic
lemmas used by the tree-matrix closed form.  Only `childCandidates_isClique`
and `closedNbhd_appendTerminal` need the hypotheses on `K` and `G` (simplicial
clique, claw-free); the remaining statements hold for every `G` and `K`.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V} {K : Set V}

namespace IndexedInducedPath

/-- Two indexed induced paths with the same cardinality and the same vertices
(compared through `Fin.cast`) are equal. -/
theorem ext_of_card_eq_vertex_cast {H : SimpleGraph V} {P Q : IndexedInducedPath H}
    (h : P.card = Q.card)
    (hv : ∀ i : Fin P.card, P.vertex i = Q.vertex (Fin.cast h i)) :
    P = Q := by
  apply ext_card_vertex h
  apply Function.hfunext (congrArg Fin h)
  intro a b hab
  have hb : b = Fin.cast h a := Fin.ext ((Fin.heq_ext_iff h).1 hab).symm
  rw [hb]
  exact heq_of_eq (hv a)

end IndexedInducedPath

namespace RootedInducedPath

/-! ### Helper lemmas on one-vertex extensions -/

/-- A one-vertex extension has one more vertex. -/
theorem IsOneVertexExtension.card_eq {P Q : CliqueRootedInducedPath G K}
    (h : P.IsOneVertexExtension Q) : P.path.card + 1 = Q.path.card := by
  obtain ⟨hcard, _⟩ := h
  exact hcard

/-- A one-vertex extension keeps the ordered prefix. -/
theorem IsOneVertexExtension.vertex_of_lt {P Q : CliqueRootedInducedPath G K}
    (h : P.IsOneVertexExtension Q) {j : Fin Q.path.card}
    (hj : j.val < P.path.card) :
    Q.path.vertex j = P.path.vertex ⟨j.val, hj⟩ := by
  obtain ⟨_, hv⟩ := h
  exact hv ⟨j.val, hj⟩

/-- The terminal vertex of a one-vertex extension `Q` of `P` sits at index
`|P|`. -/
theorem IsOneVertexExtension.terminalVertex_eq
    {P Q : CliqueRootedInducedPath G K} (h : P.IsOneVertexExtension Q) :
    Q.terminalVertex =
      Q.path.vertex ⟨P.path.card, by have := h.card_eq; omega⟩ := by
  have hcard := h.card_eq
  unfold terminalVertex
  congr 1
  apply Fin.ext
  simp only
  omega

/-- The terminal vertex of a one-vertex extension is adjacent in `G*` to the
last vertex of the shorter path. -/
theorem IsOneVertexExtension.adj_terminal
    {P Q : CliqueRootedInducedPath G K} (h : P.IsOneVertexExtension Q)
    {q : V} (hq : Q.terminalVertex = some q) :
    (G.adjoinRootAt K).Adj
      (P.path.vertex ⟨P.path.card - 1, by have := P.path.nonempty; omega⟩)
      (some q) := by
  have hcard := h.card_eq
  have hpos := P.path.nonempty
  have hlast : Q.path.vertex ⟨P.path.card, by omega⟩ = some q := by
    rw [← hq, h.terminalVertex_eq]
  have hadj := (Q.path.adj_iff ⟨P.path.card - 1, by omega⟩
    ⟨P.path.card, by omega⟩).2 (Or.inl (by simp only; omega))
  rw [hlast, h.vertex_of_lt (j := ⟨P.path.card - 1, by omega⟩) (by
    simp only; omega)] at hadj
  exact hadj

/-- The original vertices of a one-vertex extension `Q = P + q`. -/
theorem IsOneVertexExtension.originalCarrier_eq
    {P Q : CliqueRootedInducedPath G K} (h : P.IsOneVertexExtension Q)
    {q : V} (hq : Q.terminalVertex = some q) :
    Q.originalCarrier = insert q P.originalCarrier := by
  have hcard := h.card_eq
  have hlast : Q.path.vertex ⟨P.path.card, by omega⟩ = some q := by
    rw [← hq, h.terminalVertex_eq]
  ext v
  constructor
  · rintro ⟨j, hj⟩
    by_cases hjn : j.val < P.path.card
    · rw [h.vertex_of_lt hjn] at hj
      exact Or.inr ⟨_, hj⟩
    · have : j = ⟨P.path.card, by omega⟩ := Fin.ext (by have := j.isLt; simp only; omega)
      rw [this, hlast] at hj
      exact Or.inl (Option.some.inj hj).symm
  · rintro (rfl | ⟨i, hi⟩)
    · exact ⟨_, hlast⟩
    · refine ⟨⟨i.val, by omega⟩, ?_⟩
      rw [h.vertex_of_lt (j := ⟨i.val, by omega⟩) i.isLt]
      exact hi

/-- Appending `q` to `P` adds exactly the closed neighbourhood `Γ[q]`:
`N(P + q) = N(P) ∪ Γ[q]`.  No hypothesis on `K` or `G` is needed. -/
theorem IsOneVertexExtension.closedNbhd_eq
    {P Q : CliqueRootedInducedPath G K} (h : P.IsOneVertexExtension Q)
    {q : V} (hq : Q.terminalVertex = some q) :
    Q.closedNbhd = P.closedNbhd ∪ G.closedNeighborhood q := by
  unfold closedNbhd
  rw [h.originalCarrier_eq hq, Set.biUnion_insert]
  ext x
  simp only [Set.mem_union]
  tauto

/-- The terminal vertex of `P + q`, for `q` adjacent to the last vertex of
`P`, lies in `N(P)`. -/
theorem IsOneVertexExtension.mem_closedNbhd_terminal
    {P Q : CliqueRootedInducedPath G K} (h : P.IsOneVertexExtension Q)
    {q : V} (hq : Q.terminalVertex = some q) : q ∈ P.closedNbhd :=
  P.mem_closedNbhd_of_adj _ (h.adj_terminal hq)

/-! ### The set of children -/

/-- The set `C(Q)` of vertices `x` of `G` such that appending `x` to the
rooted induced path `Q` gives an induced path of `G*`: `x` is adjacent to
the terminal vertex of `Q` and to no other vertex of `Q` (including the root
`j*`), and does not lie on `Q`.  These are the children of `Q` in the
induced-path tree (v1 L841-850). -/
def childCandidates (Q : CliqueRootedInducedPath G K) : Set V :=
  {x | Q.path.TerminalExtensionData (some x)}

theorem mem_childCandidates_iff {Q : CliqueRootedInducedPath G K} {x : V} :
    x ∈ Q.childCandidates ↔ Q.path.TerminalExtensionData (some x) :=
  Iff.rfl

end RootedInducedPath

/-- The children of the root path `{j*}` are the vertices of `K`, the
neighbours of `j*` in `G*`: `C({j*}) = K`. -/
theorem childCandidates_cliqueRootPath :
    (cliqueRootPath G K).childCandidates = K := by
  ext x
  constructor
  · intro hx
    have := (hx.adj_iff ⟨0, Nat.one_pos⟩).2 rfl
    exact this
  · intro hx
    refine ⟨?_, ?_⟩
    · rintro ⟨j, hj⟩
      simp [cliqueRootPath] at hj
    · intro j
      have hj : j = ⟨0, Nat.one_pos⟩ :=
        Fin.ext (by have := j.isLt; change j.val < 1 at this; simp only; omega)
      subst hj
      exact ⟨fun _ => rfl, fun _ => hx⟩

namespace RootedInducedPath

/-- The children of `Q = P + q` are the neighbours of `q` outside `N(P)`:
`C(Q) = Γ_G(q) \ N(P)`.  For `P = {j*}` this reads `C(Q) = Γ_G(q) \ K`.

This is the content of the recursion of v1 Definition (induced path tree,
L841-850): the children of a path are the roots of the sub-forests built on
the graph from which the closed neighbourhoods of the path so far have been
deleted.  No hypothesis on `K` or `G` is needed. -/
theorem childCandidates_eq_of_parent {P Q : CliqueRootedInducedPath G K}
    (hPQ : P.IsOneVertexExtension Q) {q : V}
    (hq : Q.terminalVertex = some q) :
    Q.childCandidates = SDiff.sdiff (G.neighborSet q) P.closedNbhd := by
  have hcard := hPQ.card_eq
  have hpos := P.path.nonempty
  have hlast : Q.path.vertex ⟨P.path.card, by omega⟩ = some q := by
    rw [← hq, hPQ.terminalVertex_eq]
  ext x
  constructor
  · intro hx
    have hadj : (G.adjoinRootAt K).Adj (some x)
        (Q.path.vertex ⟨P.path.card, by omega⟩) :=
      (hx.adj_iff _).2 (by simp only; omega)
    rw [hlast] at hadj
    refine ⟨hadj.symm, ?_⟩
    rintro (hxK | hxU)
    · have h0 := (hx.adj_iff ⟨0, by omega⟩).1 (by
        have hroot : Q.path.vertex ⟨0, by omega⟩ = none := Q.root_eq
        rw [hroot]
        exact hxK)
      simp only at h0
      omega
    · obtain ⟨v, ⟨i, hi⟩, hxv⟩ := Set.mem_iUnion₂.mp hxU
      have hiQ : Q.path.vertex ⟨i.val, by omega⟩ = some v := by
        rw [hPQ.vertex_of_lt (j := ⟨i.val, by omega⟩) i.isLt]
        exact hi
      rcases hxv with rfl | hxv
      · exact hx.outside ⟨_, hiQ⟩
      · have := (hx.adj_iff ⟨i.val, by omega⟩).1 (by
          rw [hiQ]
          exact hxv.symm)
        simp only at this
        have := i.isLt
        omega
  · rintro ⟨hxq, hxN⟩
    have hxq' : G.Adj q x := hxq
    refine ⟨?_, ?_⟩
    · rintro ⟨j, hj⟩
      by_cases hjn : j.val < P.path.card
      · rw [hPQ.vertex_of_lt hjn] at hj
        exact hxN (P.mem_closedNbhd_of_vertex_eq _ hj)
      · have : j = ⟨P.path.card, by omega⟩ :=
          Fin.ext (by have := j.isLt; simp only; omega)
        rw [this, hlast] at hj
        have hxq2 : q = x := Option.some.inj hj
        exact G.irrefl (hxq2 ▸ hxq')
    · intro j
      constructor
      · intro hadj
        by_contra hne
        have hjn : j.val < P.path.card := by
          have := j.isLt
          omega
        rw [hPQ.vertex_of_lt hjn] at hadj
        exact hxN (P.mem_closedNbhd_of_adj ⟨j.val, hjn⟩ hadj.symm)
      · intro hj
        have : j = ⟨P.path.card, by omega⟩ := Fin.ext (by simp only; omega)
        rw [this, hlast]
        exact hxq'.symm

/-- `N(Q) = N(P) ⊔ C(Q)`: the closed neighbourhood of a path `Q = P + q`
is the disjoint union of that of `P` and of the set of children of `Q`. -/
theorem closedNbhd_eq_parent_union {P Q : CliqueRootedInducedPath G K}
    (hPQ : P.IsOneVertexExtension Q) {q : V}
    (hq : Q.terminalVertex = some q) :
    Q.closedNbhd = P.closedNbhd ∪ Q.childCandidates ∧
      Disjoint P.closedNbhd Q.childCandidates := by
  rw [childCandidates_eq_of_parent hPQ hq]
  refine ⟨?_, Set.disjoint_sdiff_right⟩
  rw [hPQ.closedNbhd_eq hq]
  have hqN := hPQ.mem_closedNbhd_terminal hq
  ext x
  by_cases hx : x ∈ P.closedNbhd
  · simp [hx]
  · have hxq : x ≠ q := fun h => hx (h ▸ hqN)
    simp [closedNeighborhood, hx, hxq]

/-- `C(Q)` is a clique.  If `x ≠ y` in `C(Q)` were non-adjacent, then `x`, `y`
and the predecessor of the terminal vertex `q` would be three pairwise
non-adjacent neighbours of `q` in `G*`, a claw.  When the predecessor is the
root `j*`, the candidates `x`, `y` avoid `K` (they are not adjacent to `j*`),
and the claw lives in `G*`: this is where the simpliciality of `K` is used,
through `IsSimplicialClique.isClawFree_adjoinRootAt`.  For the root path the
statement is `C({j*}) = K`, a clique. -/
theorem childCandidates_isClique (hK : G.IsSimplicialClique K)
    (hclaw : G.IsClawFree) (Q : CliqueRootedInducedPath G K) :
    G.IsClique Q.childCandidates := by
  by_cases h1 : Q.path.card = 1
  · rw [(eq_cliqueRootPath_iff Q).2 h1, childCandidates_cliqueRootPath]
    exact hK.isClique
  · intro x hx y hy hxy
    by_contra hnadj
    have hclaw' := hK.isClawFree_adjoinRootAt hclaw
    have hpos := Q.path.nonempty
    have hcard : 2 ≤ Q.path.card := by omega
    set a : Fin Q.path.card := ⟨Q.path.card - 1, by omega⟩ with ha
    set b : Fin Q.path.card := ⟨Q.path.card - 2, by omega⟩ with hb
    have hxa : (G.adjoinRootAt K).Adj (some x) (Q.path.vertex a) :=
      (hx.adj_iff a).2 (by simp only [ha]; omega)
    have hya : (G.adjoinRootAt K).Adj (some y) (Q.path.vertex a) :=
      (hy.adj_iff a).2 (by simp only [ha]; omega)
    have hba : (G.adjoinRootAt K).Adj (Q.path.vertex a) (Q.path.vertex b) :=
      (Q.path.adj_iff a b).2 (Or.inr (by simp only [ha, hb]; omega))
    have hbx : ¬(G.adjoinRootAt K).Adj (some x) (Q.path.vertex b) := fun h =>
      by have := (hx.adj_iff b).1 h; simp only [hb] at this; omega
    have hby : ¬(G.adjoinRootAt K).Adj (some y) (Q.path.vertex b) := fun h =>
      by have := (hy.adj_iff b).1 h; simp only [hb] at this; omega
    have hbx' : Q.path.vertex b ≠ some x := fun h => hx.outside ⟨b, h⟩
    have hby' : Q.path.vertex b ≠ some y := fun h => hy.outside ⟨b, h⟩
    rcases hclaw' hba hxa.symm hya.symm hbx' hby'
        (fun h => hxy (Option.some.inj h)) with h | h | h
    · exact hbx h.symm
    · exact hby h.symm
    · exact hnadj h

/-- The terminal vertex of `Q + x` is `x`. -/
theorem terminalVertex_appendTerminal (Q : CliqueRootedInducedPath G K) {x : V}
    (hx : Q.path.TerminalExtensionData (some x)) :
    (Q.appendTerminal hx).terminalVertex = some x := by
  rw [(isOneVertexExtension_appendTerminal Q hx).terminalVertex_eq]
  exact IndexedInducedPath.appendTerminal_vertex_last Q.path hx

/-- Appending `x` to `Q` adds `Γ[x]` to the closed neighbourhood:
`N(Q + x) = N(Q) ∪ Γ[x]`.  No hypothesis on `K` or `G` is needed. -/
theorem closedNbhd_appendTerminal_eq (Q : CliqueRootedInducedPath G K) {x : V}
    (hx : Q.path.TerminalExtensionData (some x)) :
    (Q.appendTerminal hx).closedNbhd = Q.closedNbhd ∪ G.closedNeighborhood x :=
  (isOneVertexExtension_appendTerminal Q hx).closedNbhd_eq
    (terminalVertex_appendTerminal Q hx)

/-- For `Q = P + q` and a child `x ∈ C(Q)`: `N(Q + x) = N(P) ∪ Γ[x]`.  Indeed
`N(Q) = N(P) ⊔ C(Q)` and `C(Q) ⊆ Γ[x]`, as `C(Q)` is a clique containing `x`. -/
theorem closedNbhd_appendTerminal (hK : G.IsSimplicialClique K)
    (hclaw : G.IsClawFree) {P Q : CliqueRootedInducedPath G K}
    (hPQ : P.IsOneVertexExtension Q) {q : V}
    (hq : Q.terminalVertex = some q) {x : V}
    (hx : Q.path.TerminalExtensionData (some x)) :
    (Q.appendTerminal hx).closedNbhd = P.closedNbhd ∪ G.closedNeighborhood x := by
  rw [closedNbhd_appendTerminal_eq, (closedNbhd_eq_parent_union hPQ hq).1]
  have hsub : Q.childCandidates ⊆ G.closedNeighborhood x := by
    intro y hy
    by_cases hyx : y = x
    · exact Or.inl hyx
    · exact Or.inr (childCandidates_isClique hK hclaw Q hy hx hyx).symm
  rw [Set.union_assoc, Set.union_eq_self_of_subset_left hsub]

end RootedInducedPath

/-- `N({j*}) = K`: the closed neighbourhood of the root path is the clique. -/
theorem RootedInducedPath.closedNbhd_cliqueRootPath :
    (cliqueRootPath G K).closedNbhd = K := by
  have : (cliqueRootPath G K).originalCarrier = ∅ := by
    ext v
    simp [RootedInducedPath.originalCarrier, cliqueRootPath]
  simp [RootedInducedPath.closedNbhd, this]

/-- `N({j*} + x) = Γ[x]` for `x ∈ K`: the closed neighbourhood of a child of
the root path is the closed neighbourhood of its original vertex.  Only the
fact that `K` is a clique is used. -/
theorem closedNbhd_appendTerminal_cliqueRootPath (hK : G.IsClique K) {x : V}
    (hx : (cliqueRootPath G K).path.TerminalExtensionData (some x)) :
    ((cliqueRootPath G K).appendTerminal hx).closedNbhd =
      G.closedNeighborhood x := by
  have hxK : x ∈ K := by
    rw [← childCandidates_cliqueRootPath (G := G) (K := K)]
    exact hx
  rw [RootedInducedPath.closedNbhd_appendTerminal_eq,
    RootedInducedPath.closedNbhd_cliqueRootPath]
  apply Set.union_eq_self_of_subset_left
  intro y hy
  by_cases hyx : y = x
  · exact Or.inl hyx
  · exact Or.inr (hK hy hxK hyx).symm

namespace RootedInducedPath

/-- The one-vertex extensions of `Q` are exactly the paths `Q + x` with
`x ∈ C(Q)`: `Q + x` is the path obtained by appending `x`. -/
theorem isOneVertexExtension_iff_exists_appendTerminal
    (Q P' : CliqueRootedInducedPath G K) :
    Q.IsOneVertexExtension P' ↔
      ∃ (x : V) (hx : Q.path.TerminalExtensionData (some x)),
        P' = Q.appendTerminal hx := by
  constructor
  · intro h
    have hcard := h.card_eq
    have hpos := Q.path.nonempty
    obtain ⟨x, hxv⟩ := P'.vertex_eq_some_of_pos ⟨Q.path.card, by omega⟩
      (by simp only; omega)
    have hlt : ∀ j : Fin Q.path.card,
        P'.path.vertex ⟨j.val, by omega⟩ = Q.path.vertex j := fun j =>
      (h.vertex_of_lt (j := ⟨j.val, by omega⟩) j.isLt)
    have hx : Q.path.TerminalExtensionData (some x) := by
      refine ⟨?_, ?_⟩
      · rintro ⟨j, hj⟩
        have h2 : P'.path.vertex ⟨j.val, by omega⟩ =
            P'.path.vertex ⟨Q.path.card, by omega⟩ := by
          rw [hlt j, hj, hxv]
        have := congrArg Fin.val (P'.path.injective h2)
        have := j.isLt
        simp only at *
        omega
      · intro j
        have hadj := P'.path.adj_iff ⟨Q.path.card, by omega⟩ ⟨j.val, by omega⟩
        rw [hxv, hlt j] at hadj
        constructor
        · intro h'
          have := hadj.1 h'
          simp only at this
          omega
        · intro h'
          apply hadj.2
          right
          simp only
          omega
    refine ⟨x, hx, ?_⟩
    have hP : P'.path.card = (Q.path.appendTerminal hx).card := by
      change P'.path.card = Q.path.card + 1
      omega
    apply ext_path
    show P'.path = Q.path.appendTerminal hx
    apply IndexedInducedPath.ext_of_card_eq_vertex_cast hP
    intro i
    by_cases hi : i.val < Q.path.card
    · have e : Fin.cast hP i = Fin.castSucc ⟨i.val, hi⟩ := Fin.ext rfl
      rw [e, IndexedInducedPath.appendTerminal_vertex_castSucc]
      exact hlt ⟨i.val, hi⟩
    · have e : Fin.cast hP i = Fin.last Q.path.card :=
        Fin.ext (by have := i.isLt; simp only [Fin.val_cast, Fin.val_last]; omega)
      have e' : i = ⟨Q.path.card, by omega⟩ :=
        Fin.ext (by have := i.isLt; simp only; omega)
      rw [e, IndexedInducedPath.appendTerminal_vertex_last, e', hxv]
  · rintro ⟨x, hx, rfl⟩
    exact isOneVertexExtension_appendTerminal Q hx

/-- Appending `x` and `y` to `Q` gives the same path iff `x = y`. -/
theorem appendTerminal_inj {Q : CliqueRootedInducedPath G K} {x y : V}
    (hx : Q.path.TerminalExtensionData (some x))
    (hy : Q.path.TerminalExtensionData (some y)) :
    Q.appendTerminal hx = Q.appendTerminal hy ↔ x = y := by
  constructor
  · intro h
    have := congrArg terminalVertex h
    rw [terminalVertex_appendTerminal, terminalVertex_appendTerminal] at this
    exact Option.some.inj this
  · rintro rfl
    rfl

/-- The children `x ∈ C(Q)` are in bijection with the one-vertex extensions of
`Q`, via `x ↦ Q + x`. -/
noncomputable def childCandidatesEquivExtensions
    (Q : CliqueRootedInducedPath G K) :
    Q.childCandidates ≃ {P' : CliqueRootedInducedPath G K //
      Q.IsOneVertexExtension P'} where
  toFun x := ⟨Q.appendTerminal x.2, isOneVertexExtension_appendTerminal Q x.2⟩
  invFun P' :=
    ⟨(Q.isOneVertexExtension_iff_exists_appendTerminal P'.1).1 P'.2 |>.choose,
      (Q.isOneVertexExtension_iff_exists_appendTerminal P'.1).1 P'.2
        |>.choose_spec.choose⟩
  left_inv x := by
    apply Subtype.ext
    set h := (Q.isOneVertexExtension_iff_exists_appendTerminal
      (Q.appendTerminal x.2)).1 (isOneVertexExtension_appendTerminal Q x.2)
    exact ((appendTerminal_inj h.choose_spec.choose x.2).1
      h.choose_spec.choose_spec.symm)
  right_inv P' := by
    apply Subtype.ext
    exact ((Q.isOneVertexExtension_iff_exists_appendTerminal P'.1).1
      P'.2).choose_spec.choose_spec.symm

end RootedInducedPath

end SimpleGraph
