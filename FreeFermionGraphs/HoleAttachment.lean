import FreeFermionGraphs.CliqueHoppingMatrix
import FreeFermionGraphs.CliqueBubbleWandReverse
import FreeFermionGraphs.OperatorCharges
import FreeFermionGraphs.PathClosedNeighborhood

/-!
# Attachment uniformity of a deformation class at a handle

arXiv 2305.15625v1, proof of Theorem 3, case (b.iv), L1527-1576, and the normalisation
sentence after Eq. (decoratedtree), L1445.  The proof of case (b.iv) sums over every
hole of the deformation class `⟨C₀⟩` at the handle `P'` and silently assumes that the
class is *attached uniformly*: each hole of `⟨C₀⟩` occurs at `P'` exactly twice.  v1 never
proves this.  This file makes it a lemma and counts the wand events of a handle.

For a clique-rooted induced path `Q = (j*, j₁, ..., j_s)` of `G* = G + j*` with terminal
vertex `t = j_s` and a vertex set `C` we say that `C` is *attached* to `Q`
(`RootedInducedPath.HoleAttached`) if

* no vertex of `C` lies on `Q`;
* no earlier vertex of `Q` (the root `j*` included) is adjacent in `G*` to a vertex of `C`;
* the neighbours of `t` in `C` are exactly two vertices `x ∼ y`.

## Main results

* `RootedInducedPath.holeAttached_of_closure` (claim (i)): attachment is constant on a
  deformation class.  The proof is by induction along the single-vertex deformation steps
  (`HoleAttached.deformedCarrier`, `HoleAttached.of_deformedCarrier`,
  `HoleAttached.of_closure`).  Earlier path vertices stay non-adjacent to the new clone
  `s` because a vertex adjacent to `s` and not to `a i` is dependent on the deformation,
  so it is adjacent to the hole by the first half of Lemma 8 (v1 Lemma
  `evenholecloneneighbor`, L707-, and its use in Lemma `evenholeneighbor`, L737-,
  the repo's Lemma 9 / `InEvenHoleDeformationClosure.openNeighborhood_eq`).  Lemma 8 is
  re-proved for a dependent vertex of `G*` that may be the root
  (`EvenHoleLabeling.CloneAt.dependent_forces_side_adjoinRoot`; claw-freeness of `G*`).
  The terminal `t` is adjacent to `s` iff it is adjacent to `a i`, since otherwise the claw
  `{t; prev(t), a, s}` appears (`prev(t)` is neither adjacent to the hole nor to `s`); for
  `t = j*` the vertices `s` and `a` would lie in the clique `K` but are not adjacent.
* `card_evenHoopEvents` (claim (ii)): the wand events `(P, j)` with handle `Q` and an even
  hoop of the class `c` correspond two to one to the even-hole carriers of `c` that are
  attached to `Q`: `#events = 2 * #(attached holes of c)`.  The two events of a hole are
  `(P, j)` and the reversal `(P*, j_{s+1})` of `CliqueBubbleWandReverse.lean`.  Combined
  with claim (i): `#events = 2 |c|` if one hole of `c` is attached to `Q`
  (`card_evenHoopEvents_of_attached`), and `0` otherwise
  (`card_evenHoopEvents_eq_zero_of_not_attached`, `card_evenHoopEvents_eq`).
* `half_sum_inv_eventNormalisation_of_attached` (claim (iii)): the corrected form of the
  normalisation sentence of v1 L1445, `(1/2) Σ_{sources P} N_{P,Q,c}⁻¹ = 1` with
  `N_{P,Q,c} = |c| / m(P, Q, c)`.
* `cliqueHoppingMatrix_column_hoop_total`: the column total over the sources of the hoop
  part (`cliqueHoppingHoopPart`) of the matrix `A_λ` of `CliqueHoppingMatrix.lean`:
  `2 (-1)^{k_c - 1} λ_c` if a hole of `c` is attached to `Q`, and `0` otherwise; the hoop
  part is the hoop term of `cliqueHoppingMatrix` restricted to the class `c`
  (`cliqueHoppingMatrix_eq_tree_add_sum_hoopPart`).
* `exists_cliqueBubbleWand_of_holeAttached`: a hole attached to `Q` is the hoop of a wand
  with handle `Q`; `CliqueBubbleWand.holeAttached_hoopCarrier` is the converse.

## Deviations from the package statement

* The right-hand side of the package target `card_evenHoopEvents` counts *all* vertex sets
  of the class `c` that are attached to `Q`.  This is false:
  `EvenHoleDeformationClass` is the quotient of all vertex sets, an attached non-hole set
  (for example an edge of `K` and `Q = {j*}`) is a class of its own with no events.
  `HoleAttachmentExample.card_evenHoopEvents_literal_false` is the machine-checked
  counterexample (`G = K₂`, `K = V`).  `card_evenHoopEvents` counts the even-hole carriers
  (`IsEvenHoleCarrier`); `card_evenHoopEvents_of_holeClass` gives the literal right-hand
  side under the hypothesis that `c` is the class of a hole.
* Claim (ii) needs neither claw-freeness nor simpliciality, so these hypotheses are
  absent from `card_evenHoopEvents`; claim (i) and its consequences need them.
* Claim (i) does not need the hypothesis `∃ k E, E.HasFullCyclicOrder ∧ E.carrier = C` of
  the package target (every step of the closure carries its own labeling); it is kept as
  an unused hypothesis in `holeAttached_of_closure` for the signature, and
  `HoleAttached.of_closure` is the version without it.
* `cliqueHoppingMatrix` is not edited; the class-wise hoop part `cliqueHoppingHoopPart`
  is defined here and shown to add up to the matrix entry.
-/

open scoped BigOperators

universe u w

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V} {K : Set V}

namespace RootedInducedPath

/-- A vertex set `C` is *attached* to the clique-rooted path `Q` with terminal
vertex `t` (v1 proof of Theorem 3, case (b.iv), L1555-1576, where it is assumed
implicitly): no vertex of `C` is on `Q`; no earlier vertex of `Q`, including the
root `j*`, is adjacent in `G*` to a vertex of `C`; and the neighbours of `t` in
`C` are exactly two adjacent vertices `x ∼ y`. -/
def HoleAttached (Q : CliqueRootedInducedPath G K) (C : Set V) : Prop :=
  (∀ v ∈ C, some v ∉ Set.range Q.path.vertex) ∧
  (∀ p : Fin Q.path.card, p.val + 1 < Q.path.card → ∀ v ∈ C,
      ¬ (G.adjoinRootAt K).Adj (Q.path.vertex p) (some v)) ∧
  ∃ x y, x ∈ C ∧ y ∈ C ∧ G.Adj x y ∧
    ∀ v ∈ C, ((G.adjoinRootAt K).Adj Q.terminalVertex (some v) ↔ v = x ∨ v = y)

end RootedInducedPath

/-! ### The first half of Lemma 8 with the root as the dependent vertex -/

namespace EvenHoleLabeling

/-- The first half of Lemma 8 (`CloneAt.dependent_forces_side`) in the graph
`G* = G + j*`, for a *dependent* vertex `t` of `G*` that may be the root `j*`.
If `t` is adjacent to exactly one of the clone `s` and its original `a i`, then
`t` is adjacent to `b i` and `a (prev i)` or to `b (next i)` and `a (next i)`.

Claw-freeness of `G*` (not of `G`) is used, so for the root `t = none` the
conclusion needs `K` simplicial (`IsSimplicialClique.isClawFree_adjoinRootAt`).
The proof is that of `CloneAt.dependent_forces_side` with the vertex `t`
read in `Option V`. -/
theorem CloneAt.dependent_forces_side_adjoinRoot {k : Nat}
    {C : EvenHoleLabeling G k} {s : V} {i : Fin k}
    (h : C.CloneAt s i) (hclaw : (G.adjoinRootAt K).IsClawFree)
    {t : Option V} (ht : ∀ v ∈ Set.insert s C.carrier, t ≠ some v)
    (hexact :
      ((G.adjoinRootAt K).Adj t (some s) ∧
        ¬(G.adjoinRootAt K).Adj t (some (C.a i))) ∨
      (¬(G.adjoinRootAt K).Adj t (some s) ∧
        (G.adjoinRootAt K).Adj t (some (C.a i)))) :
    ((G.adjoinRootAt K).Adj t (some (C.b i)) ∧
        (G.adjoinRootAt K).Adj t (some (C.a (C.prev i)))) ∨
    ((G.adjoinRootAt K).Adj t (some (C.b (C.next i))) ∧
        (G.adjoinRootAt K).Adj t (some (C.a (C.next i)))) := by
  have ht_b : ∀ q : Fin k, t ≠ some (C.b q) := fun q =>
    ht _ (Set.mem_insert_iff.2 (Or.inr (C.b_mem_carrier q)))
  have ht_a : ∀ q : Fin k, t ≠ some (C.a q) := fun q =>
    ht _ (Set.mem_insert_iff.2 (Or.inr (C.a_mem_carrier q)))
  have ht_s : t ≠ some s := ht _ (Set.mem_insert_iff.2 (Or.inl rfl))
  have hs_a_prev : some s ≠ some (C.a (C.prev i)) := by
    intro hs
    exact h.outside ((Option.some.inj hs) ▸ C.a_mem_carrier (C.prev i))
  have hs_a_next : some s ≠ some (C.a (C.next i)) := by
    intro hs
    exact h.outside ((Option.some.inj hs) ▸ C.a_mem_carrier (C.next i))
  have hne : ∀ {x y : V}, x ≠ y → some x ≠ some y := fun hxy h => hxy (Option.some.inj h)
  have lift : ∀ {x y : V}, G.Adj x y → (G.adjoinRootAt K).Adj (some x) (some y) :=
    fun h => h
  have hforce_prev :
      (G.adjoinRootAt K).Adj t (some (C.b i)) →
      (¬(G.adjoinRootAt K).Adj t (some (C.a i)) ∨
        ¬(G.adjoinRootAt K).Adj t (some s)) →
      (G.adjoinRootAt K).Adj t (some (C.a (C.prev i))) := by
    intro htb hnot
    rcases hnot with htai | hts
    · rcases hclaw.adjacent_to_one_of_nonadjacent_neighbors
          htb (lift (C.adj_a_b i).symm) (lift (C.adj_a_prev_b i).symm)
          (ht_a i) (ht_a (C.prev i)) (hne (C.a_ne_prev i).symm)
          (C.adj_aa i (C.prev i)) with htai' | htprev
      · exact (htai htai').elim
      · exact htprev
    · rcases hclaw.adjacent_to_one_of_nonadjacent_neighbors
          htb (lift h.adj_b.symm) (lift (C.adj_a_prev_b i).symm)
          ht_s (ht_a (C.prev i)) hs_a_prev
          h.not_adj_a_prev with hts' | htprev
      · exact (hts hts').elim
      · exact htprev
  have hforce_next :
      (G.adjoinRootAt K).Adj t (some (C.b (C.next i))) →
      (¬(G.adjoinRootAt K).Adj t (some (C.a i)) ∨
        ¬(G.adjoinRootAt K).Adj t (some s)) →
      (G.adjoinRootAt K).Adj t (some (C.a (C.next i))) := by
    intro htb hnot
    rcases hnot with htai | hts
    · rcases hclaw.adjacent_to_one_of_nonadjacent_neighbors
          htb (lift (C.adj_a_b_next i).symm)
          (lift (C.adj_a_b (C.next i)).symm)
          (ht_a i) (ht_a (C.next i)) (hne (C.a_ne_next i).symm)
          (C.adj_aa i (C.next i)) with htai' | htnext
      · exact (htai htai').elim
      · exact htnext
    · rcases hclaw.adjacent_to_one_of_nonadjacent_neighbors
          htb (lift h.adj_b_next.symm) (lift (C.adj_a_b (C.next i)).symm)
          ht_s (ht_a (C.next i)) hs_a_next
          h.not_adj_a_next with hts' | htnext
      · exact (hts hts').elim
      · exact htnext
  have hbb : some (C.b i) ≠ some (C.b (C.next i)) :=
    hne (C.b_ne_next i).symm
  rcases hexact with ⟨hts, htai⟩ | ⟨hts, htai⟩
  · have hb : (G.adjoinRootAt K).Adj t (some (C.b i)) ∨
        (G.adjoinRootAt K).Adj t (some (C.b (C.next i))) :=
      hclaw.adjacent_to_one_of_nonadjacent_neighbors
        hts (lift h.adj_b) (lift h.adj_b_next) (ht_b i) (ht_b (C.next i))
        hbb (C.adj_bb i (C.next i))
    rcases hb with htb | htb
    · exact Or.inl ⟨htb, hforce_prev htb (Or.inl htai)⟩
    · exact Or.inr ⟨htb, hforce_next htb (Or.inl htai)⟩
  · have hb : (G.adjoinRootAt K).Adj t (some (C.b i)) ∨
        (G.adjoinRootAt K).Adj t (some (C.b (C.next i))) :=
      hclaw.adjacent_to_one_of_nonadjacent_neighbors
        htai (lift (C.adj_a_b i)) (lift (C.adj_a_b_next i))
        (ht_b i) (ht_b (C.next i)) hbb
        (C.adj_bb i (C.next i))
    rcases hb with htb | htb
    · exact Or.inl ⟨htb, hforce_prev htb (Or.inr hts)⟩
    · exact Or.inr ⟨htb, hforce_next htb (Or.inr hts)⟩

end EvenHoleLabeling

/-! ### Attachment is stable under one single-vertex deformation -/

namespace EvenHoleLabeling

/-- The labeling `deform` of a clone has the original vertex `a i` as a clone
of the new `a`-vertex: the clone relation is symmetric. -/
theorem CloneAt.cloneAt_deform {k : Nat} {C : EvenHoleLabeling G k}
    {s : V} {i : Fin k} (h : C.CloneAt s i) :
    (C.deform h).CloneAt (C.a i) i := by
  have hcar := C.deform_carrier h
  refine ⟨?_, ?_⟩
  · rw [hcar]
    rintro hmem
    rcases Set.mem_insert_iff.1 hmem with hs | ⟨_, hne⟩
    · exact h.outside (hs ▸ C.a_mem_carrier i)
    · exact hne rfl
  · intro v hv
    rw [hcar] at hv
    rw [C.deform_a_at h]
    rcases Set.mem_insert_iff.1 hv with hvs | ⟨hvA, hvne⟩
    · rw [hvs]
      exact ⟨fun _ => Or.inl rfl, fun _ => h.adj_original.symm⟩
    · have hvi : v ≠ C.a i := fun hv' => hvne hv'
      have hsv := h.adj_iff v hvA
      constructor
      · intro hav
        exact Or.inr (hsv.2 (Or.inr hav))
      · rintro (hvs | hsv')
        · exact absurd (hvs ▸ hvA) h.outside
        · rcases hsv.1 hsv' with hv' | hav
          · exact absurd hv' hvi
          · exact hav

/-- Deforming the clone back recovers the original carrier. -/
theorem deformedCarrier_deform {k : Nat} {C : EvenHoleLabeling G k}
    {s : V} {i : Fin k} (h : C.CloneAt s i) :
    (C.deform h).deformedCarrier (C.a i) i = C.carrier := by
  have hcar := C.deform_carrier h
  have hai := C.deform_a_at h
  ext v
  constructor
  · intro hv
    rcases (Set.mem_insert_iff.1 hv : v = C.a i ∨
        v ∈ (C.deform h).carrier \ {(C.deform h).a i}) with hvi | ⟨hvB, hvn⟩
    · exact hvi ▸ C.a_mem_carrier i
    · rw [hcar] at hvB
      rcases Set.mem_insert_iff.1 hvB with hvs | ⟨hvA, _⟩
      · exact absurd (show v = (C.deform h).a i from hvs.trans hai.symm) hvn
      · exact hvA
  · intro hvA
    by_cases hvi : v = C.a i
    · exact Set.mem_insert_iff.2 (Or.inl hvi)
    · refine Set.mem_insert_iff.2 (Or.inr ⟨?_, ?_⟩)
      · rw [hcar]
        exact Set.mem_insert_iff.2 (Or.inr ⟨hvA, hvi⟩)
      · intro hvs
        exact h.outside ((show v = s from hvs.trans hai) ▸ hvA)

end EvenHoleLabeling

namespace RootedInducedPath

variable {Q : CliqueRootedInducedPath G K}

/-- One forward deformation step preserves attachment: if the carrier of the
labeling `E` is attached to `Q` and `s` is a clone of `a i`, then the deformed
carrier `E.carrier - a i + s` is attached to `Q`.

The proof follows the sketch of v1 (and the package statement): earlier path
vertices and the new clone `s` are non-adjacent because such a vertex that were
adjacent to `s` but not to `a i` would be dependent on the deformation, hence
adjacent to the hole by Lemma 8
(`EvenHoleLabeling.CloneAt.dependent_forces_side_adjoinRoot`, which also covers the
root `j*` through claw-freeness of `G*`); the terminal `t` of `Q` is adjacent to `s`
iff it is adjacent to `a i`, since otherwise `t` is adjacent to `s` and two further
vertices of the hole and the claw `{t; prev(t), a, s}` appears (`prev(t) = j_{s-1}` is
not adjacent to the hole or to `s`); for `t = j*` the vertices `s` and `a` would lie in
the clique `K` while being non-adjacent. -/
theorem HoleAttached.deformedCarrier (hK : G.IsSimplicialClique K)
    (hclaw : G.IsClawFree) {k : Nat} (E : EvenHoleLabeling G k) {s : V}
    {i : Fin k} (h : E.CloneAt s i) (hQ : Q.HoleAttached E.carrier) :
    Q.HoleAttached (E.deformedCarrier s i) := by
  have hclaw' := hK.isClawFree_adjoinRootAt hclaw
  obtain ⟨hQ1, hQ2, x, y, hx, hy, hxy, hQ3⟩ := hQ
  have lift : ∀ {x y : V}, G.Adj x y →
      (G.adjoinRootAt K).Adj (some x) (some y) := fun h => h
  have hsA : s ∉ E.carrier := h.outside
  have hterm : Q.terminalVertex = Q.path.vertex Q.terminalIndex := rfl
  -- Step 1: the clone is not on `Q`
  have hs_nQ : ∀ p : Fin Q.path.card, Q.path.vertex p ≠ some s := by
    intro p hp
    by_cases hpe : p.val + 1 < Q.path.card
    · exact hQ2 p hpe (E.a i) (E.a_mem_carrier i) (hp ▸ lift h.adj_original)
    · have hpt : Q.path.vertex p = Q.terminalVertex := by
        have hval : p.val = Q.path.card - 1 := by have := p.isLt; omega
        exact congrArg Q.path.vertex (Fin.ext hval)
      rw [hpt] at hp
      have h1 := (hQ3 (E.a i) (E.a_mem_carrier i)).1 (hp ▸ lift h.adj_original)
      have h2 := (hQ3 (E.b i) (E.b_mem_carrier i)).1 (hp ▸ lift h.adj_b)
      have h3 := (hQ3 (E.b (E.next i)) (E.b_mem_carrier _)).1
        (hp ▸ lift h.adj_b_next)
      have d1 : E.a i ≠ E.b i := E.color_disjoint i i
      have d2 : E.a i ≠ E.b (E.next i) := E.color_disjoint _ _
      have d3 : E.b i ≠ E.b (E.next i) := (E.b_ne_next i).symm
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
        rcases h3 with h3 | h3 <;>
        first
        | exact d1 (h1.trans h2.symm)
        | exact d2 (h1.trans h3.symm)
        | exact d3 (h2.trans h3.symm)
  -- Step 2: no earlier vertex of `Q` is adjacent to the clone
  have hdep : ∀ p : Fin Q.path.card, p.val + 1 < Q.path.card →
      ¬ (G.adjoinRootAt K).Adj (Q.path.vertex p) (some s) := by
    intro p hp hadj
    have hno : ∀ v ∈ Set.insert s E.carrier, Q.path.vertex p ≠ some v := by
      intro v hv hq
      rcases Set.mem_insert_iff.1 hv with hvs | hv
      · rw [hvs] at hq
        exact hs_nQ p hq
      · exact hQ1 v hv ⟨p, hq⟩
    rcases EvenHoleLabeling.CloneAt.dependent_forces_side_adjoinRoot h hclaw' hno
        (Or.inl ⟨hadj, hQ2 p hp (E.a i) (E.a_mem_carrier i)⟩) with
      ⟨hb, _⟩ | ⟨hb, _⟩
    · exact hQ2 p hp _ (E.b_mem_carrier i) hb
    · exact hQ2 p hp _ (E.b_mem_carrier _) hb
  -- Conditions 1 and 2 for the deformed carrier
  have hB1 : ∀ v ∈ E.deformedCarrier s i, some v ∉ Set.range Q.path.vertex := by
    intro v hv
    rcases Set.mem_insert_iff.1 hv with hvs | ⟨hvA, _⟩
    · rintro ⟨p, hp⟩
      rw [hvs] at hp
      exact hs_nQ p hp
    · exact hQ1 v hvA
  have hB2 : ∀ p : Fin Q.path.card, p.val + 1 < Q.path.card →
      ∀ v ∈ E.deformedCarrier s i,
        ¬ (G.adjoinRootAt K).Adj (Q.path.vertex p) (some v) := by
    intro p hp v hv
    rcases Set.mem_insert_iff.1 hv with hvs | ⟨hvA, _⟩
    · rw [hvs]
      exact hdep p hp
    · exact hQ2 p hp v hvA
  refine ⟨hB1, hB2, ?_⟩
  -- the terminal vertex is not a vertex of the hole or the clone
  have hno : ∀ v ∈ Set.insert s E.carrier, Q.terminalVertex ≠ some v := by
    intro v hv hq
    rcases Set.mem_insert_iff.1 hv with hvs | hv
    · rw [hvs] at hq
      exact hs_nQ Q.terminalIndex (hterm ▸ hq)
    · exact hQ1 v hv ⟨Q.terminalIndex, hterm ▸ hq⟩
  have hsne : ∀ v ∈ E.carrier, v ≠ s := fun v hv hvs => hsA (hvs ▸ hv)
  -- a bad configuration: `t` adjacent to `s` and to a vertex `u` of the hole that is
  -- not adjacent to `s`
  have hbad : (G.adjoinRootAt K).Adj Q.terminalVertex (some s) →
      ∀ u ∈ E.carrier, (G.adjoinRootAt K).Adj Q.terminalVertex (some u) →
        ¬ G.Adj s u → False := by
    intro hts u hu htu hsu
    by_cases hcard : Q.path.card = 1
    · have hroot : Q.terminalVertex = none := by
        have h0 : Q.path.vertex ⟨0, Q.path.nonempty⟩ = none := Q.root_eq
        rw [← h0]
        exact congrArg Q.path.vertex (Fin.ext (by
          change Q.path.card - 1 = 0
          omega))
      rw [hroot] at hts htu
      exact hsu (hK.isClique hts htu (hsne u hu).symm)
    · have hc2 : 2 ≤ Q.path.card := by have := Q.path.nonempty; omega
      let π : Fin Q.path.card := ⟨Q.path.card - 2, by omega⟩
      have hπt : (G.adjoinRootAt K).Adj Q.terminalVertex (Q.path.vertex π) := by
        rw [hterm]
        exact (Q.path.adj_iff Q.terminalIndex π).2
          (Or.inr (by change Q.path.card - 2 + 1 = Q.path.card - 1; omega))
      have hπe : π.val + 1 < Q.path.card := by
        change Q.path.card - 2 + 1 < Q.path.card
        omega
      rcases hclaw' hπt htu hts
          (fun hq => hQ1 u hu ⟨π, hq⟩)
          (fun hq => hs_nQ π hq)
          (fun hq => hsne u hu (Option.some.inj hq)) with
        hπu | hπs | hus
      · exact hQ2 π hπe u hu hπu
      · exact hdep π hπe hπs
      · exact hsu hus.symm
  by_cases hta : (G.adjoinRootAt K).Adj Q.terminalVertex (some (E.a i))
  · -- `a i` is a neighbour of `t`
    obtain ⟨b', hb'A, hab', hΓ⟩ : ∃ b', b' ∈ E.carrier ∧ G.Adj (E.a i) b' ∧
        ∀ v ∈ E.carrier, ((G.adjoinRootAt K).Adj Q.terminalVertex (some v) ↔
          v = E.a i ∨ v = b') := by
      rcases (hQ3 _ (E.a_mem_carrier i)).1 hta with hax | hay
      · refine ⟨y, hy, by rw [hax]; exact hxy, fun v hv => ?_⟩
        rw [hQ3 v hv, hax]
      · refine ⟨x, hx, by rw [hay]; exact hxy.symm, fun v hv => ?_⟩
        rw [hQ3 v hv, hay, or_comm]
    by_cases hts : (G.adjoinRootAt K).Adj Q.terminalVertex (some s)
    · refine ⟨s, b', Set.mem_insert_iff.2 (Or.inl rfl),
        Set.mem_insert_iff.2 (Or.inr ⟨hb'A, fun hb => hab'.ne hb.symm⟩),
        (h.adj_iff b' hb'A).2 (Or.inr hab'), ?_⟩
      intro v hv
      rcases Set.mem_insert_iff.1 hv with hvs | ⟨hvA, hvne⟩
      · exact ⟨fun _ => Or.inl hvs, fun _ => by rw [hvs]; exact hts⟩
      · have hvi : v ≠ E.a i := hvne
        rw [hΓ v hvA]
        constructor
        · rintro (hv' | hv')
          · exact absurd hv' hvi
          · exact Or.inr hv'
        · rintro (hv' | hv')
          · exact absurd hv' (hsne v hvA)
          · exact Or.inr hv'
    · exfalso
      rcases EvenHoleLabeling.CloneAt.dependent_forces_side_adjoinRoot h hclaw' hno
          (Or.inr ⟨hts, hta⟩) with ⟨_, hap⟩ | ⟨_, han⟩
      · rcases (hΓ _ (E.a_mem_carrier _)).1 hap with hv | hv
        · exact E.a_ne_prev i hv
        · exact E.adj_aa i (E.prev i) (hv ▸ hab')
      · rcases (hΓ _ (E.a_mem_carrier _)).1 han with hv | hv
        · exact E.a_ne_next i hv
        · exact E.adj_aa i (E.next i) (hv ▸ hab')
  · -- `a i` is not a neighbour of `t`
    have hxi : x ≠ E.a i := fun hxa =>
      hta (hxa ▸ (hQ3 x hx).2 (Or.inl rfl))
    have hyi : y ≠ E.a i := fun hya =>
      hta (hya ▸ (hQ3 y hy).2 (Or.inr rfl))
    by_cases hts : (G.adjoinRootAt K).Adj Q.terminalVertex (some s)
    · exfalso
      rcases EvenHoleLabeling.CloneAt.dependent_forces_side_adjoinRoot h hclaw' hno
          (Or.inl ⟨hts, hta⟩) with ⟨_, hap⟩ | ⟨_, han⟩
      · exact hbad hts _ (E.a_mem_carrier _) hap h.not_adj_a_prev
      · exact hbad hts _ (E.a_mem_carrier _) han h.not_adj_a_next
    · refine ⟨x, y, Set.mem_insert_iff.2 (Or.inr ⟨hx, hxi⟩),
        Set.mem_insert_iff.2 (Or.inr ⟨hy, hyi⟩), hxy, ?_⟩
      intro v hv
      rcases Set.mem_insert_iff.1 hv with hvs | ⟨hvA, _⟩
      · refine ⟨fun hadj => absurd (hvs ▸ hadj) hts, fun hv' => ?_⟩
        rcases hv' with hv' | hv'
        · exact absurd (hvs ▸ hv' ▸ hx) hsA
        · exact absurd (hvs ▸ hv' ▸ hy) hsA
      · exact hQ3 v hvA

/-- A backward deformation step preserves attachment: the clone relation is
symmetric (`CloneAt.cloneAt_deform`), so this is the forward step for the
deformed labeling. -/
theorem HoleAttached.of_deformedCarrier (hK : G.IsSimplicialClique K)
    (hclaw : G.IsClawFree) {k : Nat} (E : EvenHoleLabeling G k) {s : V}
    {i : Fin k} (h : E.CloneAt s i)
    (hQ : Q.HoleAttached (E.deformedCarrier s i)) :
    Q.HoleAttached E.carrier := by
  have hc : (E.deform h).carrier = E.deformedCarrier s i := E.deform_carrier h
  have key := HoleAttached.deformedCarrier hK hclaw (E.deform h) h.cloneAt_deform
    (by rw [hc]; exact hQ)
  rwa [EvenHoleLabeling.deformedCarrier_deform h] at key

/-- A reversible deformation step (either direction) preserves attachment. -/
theorem HoleAttached.of_step (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree)
    {A B : Set V} (hstep : EvenHoleDeformationStep G A B)
    (hQ : Q.HoleAttached A) : Q.HoleAttached B := by
  obtain ⟨k, E, s, i, h, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := hstep
  · exact HoleAttached.deformedCarrier hK hclaw E h hQ
  · exact HoleAttached.of_deformedCarrier hK hclaw E h hQ

/-- (i) Attachment is constant on a deformation class: if `C` is attached to `Q`
and `C'` lies in the deformation closure of `C`, then `C'` is attached to `Q`.
No hypothesis on `C` is needed: every step of the closure carries its own
labeling. -/
theorem HoleAttached.of_closure (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree)
    {C C' : Set V} (h : InEvenHoleDeformationClosure G C C')
    (hQ : Q.HoleAttached C) : Q.HoleAttached C' := by
  induction h with
  | refl => exact hQ
  | tail _ hstep ih => exact HoleAttached.of_step hK hclaw hstep ih

/-- Claim (i) of the package: attachment is constant on the deformation class of an
even hole (the uniformity that v1 assumes at L1555-1576).  The hypothesis `_hC` that
`C` is the carrier of a full-cyclic labeling is not needed (`HoleAttached.of_closure`);
it is kept so that the statement has the signature of the package target. -/
theorem holeAttached_of_closure (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree)
    {Q : CliqueRootedInducedPath G K} {C C' : Set V}
    (_hC : ∃ k, ∃ E : EvenHoleLabeling G k, E.HasFullCyclicOrder ∧ E.carrier = C)
    (hQ : Q.HoleAttached C) (h : InEvenHoleDeformationClosure G C C') :
    Q.HoleAttached C' :=
  HoleAttached.of_closure hK hclaw h hQ

/-- Attachment is a property of the deformation class. -/
theorem holeAttached_iff_of_closure (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree)
    {Q : CliqueRootedInducedPath G K} {C C' : Set V}
    (h : InEvenHoleDeformationClosure G C C') :
    Q.HoleAttached C ↔ Q.HoleAttached C' :=
  ⟨HoleAttached.of_closure hK hclaw h, HoleAttached.of_closure hK hclaw h.symm⟩

end RootedInducedPath

/-! ### A wand is determined by its handle, hoop carrier and bubble -/

namespace CliqueBubbleWand

variable {P : CliqueRootedInducedPath G K}

/-- The vertices of the handle are vertices of `P`. -/
theorem handle_originalCarrier_subset (w : CliqueBubbleWand G K P) :
    w.handle.originalCarrier ⊆ P.originalCarrier := by
  intro v hv
  obtain ⟨q, _, hq⟩ := (w.mem_handle_originalCarrier_iff v).1 hv
  exact ⟨q, hq⟩

/-- The original carrier of the source path is the handle together with the hoop
without its bubble. -/
theorem originalCarrier_eq (w : CliqueBubbleWand G K P) :
    P.originalCarrier = (w.hoopCarrier \ {w.bubble}) ∪ w.handle.originalCarrier := by
  ext v
  constructor
  · intro hv
    by_cases hvh : v ∈ w.handle.originalCarrier
    · exact Or.inr hvh
    · refine Or.inl ⟨Or.inl ⟨hv, hvh⟩, ?_⟩
      intro hvb
      have hvb' : v = w.bubble := hvb
      exact w.bubble_notMem_originalCarrier (hvb' ▸ hv)
  · rintro (⟨hv | hv, _⟩ | hv)
    · exact hv.1
    · exact absurd hv ‹_›
    · exact w.handle_originalCarrier_subset hv

/-- Two wands with the same handle, the same hoop carrier and the same bubble are
wands on the same path: the original carrier of the path is determined, and a rooted
path is determined by its original carrier. -/
theorem eq_of_handle_hoopCarrier_bubble_eq {P' : CliqueRootedInducedPath G K}
    (w : CliqueBubbleWand G K P) (w' : CliqueBubbleWand G K P')
    (hh : w.handle = w'.handle) (hc : w.hoopCarrier = w'.hoopCarrier)
    (hb : w.bubble = w'.bubble) : P = P' := by
  apply RootedInducedPath.ext_of_originalCarrier_eq
  rw [w.originalCarrier_eq, w'.originalCarrier_eq, hh, hc, hb]

/-- The terminal vertex of the handle is `j_s`. -/
theorem handle_terminalVertex (w : CliqueBubbleWand G K P) :
    w.handle.terminalVertex = P.path.vertex w.split :=
  congrArg P.path.vertex (Fin.ext (by
    change w.split.val + 1 - 1 = w.split.val
    omega))

/-- The hoop carrier of a wand is attached to its handle: no hoop vertex is on the
handle, no earlier handle vertex is adjacent to the hoop, and the terminal `j_s` of the
handle has exactly the two hoop neighbours `j` (the bubble) and `j_{s+1}`, which are
adjacent.  This is the converse direction of the correspondence between wand events
and attached holes (`card_evenHoopEvents`). -/
theorem holeAttached_hoopCarrier (w : CliqueBubbleWand G K P) :
    w.handle.HoleAttached w.hoopCarrier := by
  have hgap := w.gap
  -- a vertex of the hoop carrier is the bubble or a vertex of `P` outside the handle
  have hcases : ∀ v ∈ w.hoopCarrier, v = w.bubble ∨
      ∃ r : Fin P.path.card, w.split.val < r.val ∧ P.path.vertex r = some v := by
    intro v hv
    rcases hv with ⟨⟨r, hr⟩, hvh⟩ | hv
    · right
      refine ⟨r, ?_, hr⟩
      by_contra hle
      exact hvh ((w.mem_handle_originalCarrier_iff v).2 ⟨r, by omega, hr⟩)
    · left
      exact hv
  refine ⟨?_, ?_, ⟨w.bubble, w.reverseBubble, Or.inr rfl, ?_,
    w.adj_bubble_reverseBubble, ?_⟩⟩
  · -- no hoop vertex is on the handle
    intro v hv ⟨q, hq⟩
    have hqlt : q.val < w.split.val + 1 := q.isLt
    have hq' : P.path.vertex ⟨q.val, by omega⟩ = some v := hq
    rcases hcases v hv with rfl | ⟨r, hr, hrv⟩
    · exact w.outside ⟨⟨q.val, by omega⟩, hq'⟩
    · have hidx := P.path.injective (hq'.trans hrv.symm)
      have := congrArg Fin.val hidx
      simp only at this
      omega
  · -- no earlier handle vertex is adjacent to the hoop
    intro p hp v hv
    change p.val + 1 < w.split.val + 1 at hp
    have hadj : (G.adjoinRootAt K).Adj (w.handle.path.vertex p) (some v) ↔
        (G.adjoinRootAt K).Adj (P.path.vertex ⟨p.val, by omega⟩) (some v) := Iff.rfl
    rw [hadj]
    rcases hcases v hv with rfl | ⟨r, hr, hrv⟩
    · intro hpv
      have h2 := (w.adj_iff ⟨p.val, by omega⟩).1 hpv.symm
      change p.val = w.split.val ∨ p.val = w.split.val + 1 ∨ p.val + 1 = P.path.card at h2
      omega
    · intro hpv
      rw [← hrv] at hpv
      rcases (P.path.adj_iff _ _).1 hpv with h2 | h2
      · change p.val + 1 = r.val at h2
        omega
      · change r.val + 1 = p.val at h2
        omega
  · -- the clone `j_{s+1}` lies in the hoop
    refine ⟨w.reverseBubble_mem_originalCarrier, w.reverseBubble_notMem_handle⟩ |> Or.inl
  · -- the neighbours of `j_s` in the hoop
    intro v hv
    rw [w.handle_terminalVertex]
    rcases hcases v hv with rfl | ⟨r, hr, hrv⟩
    · constructor
      · intro _
        exact Or.inl rfl
      · intro _
        exact w.adj_split.symm
    · rw [← hrv]
      have hrv' : (G.adjoinRootAt K).Adj (P.path.vertex w.split) (P.path.vertex r) ↔
          r.val = w.split.val + 1 := by
        rw [P.path.adj_iff]
        omega
      rw [hrv']
      constructor
      · intro hr1
        right
        have h1 := w.path_vertex_split_succ r hr1
        rw [hrv] at h1
        exact Option.some.inj h1
      · rintro (hvb | hvb)
        · exfalso
          have hbub : P.path.vertex r = some w.bubble := hvb ▸ hrv
          exact w.outside ⟨r, hbub⟩
        · rw [hvb] at hrv
          exact (w.path_vertex_eq_reverseBubble_iff r).1 hrv

end CliqueBubbleWand

/-! ### Appending an induced path to a rooted path -/

namespace RootedInducedPath

variable {Q : CliqueRootedInducedPath G K}

/-- The data needed to append the induced path `T` of `G` to the clique-rooted path
`Q`: the vertices of `T` are off `Q`, no earlier vertex of `Q` is adjacent to `T`, and
the terminal vertex of `Q` is adjacent exactly to the first vertex of `T`. -/
structure AppendData (Q : CliqueRootedInducedPath G K) (T : IndexedInducedPath G) :
    Prop where
  outside : ∀ r, some (T.vertex r) ∉ Set.range Q.path.vertex
  early : ∀ p : Fin Q.path.card, p.val + 1 < Q.path.card → ∀ r,
    ¬ (G.adjoinRootAt K).Adj (Q.path.vertex p) (some (T.vertex r))
  terminal : ∀ r, (G.adjoinRootAt K).Adj Q.terminalVertex (some (T.vertex r)) ↔
    r.val = 0

/-- The vertex map of the concatenation `Q ++ T`. -/
def appendVertex (Q : CliqueRootedInducedPath G K) (T : IndexedInducedPath G)
    (q : Fin (Q.path.card + T.card)) : Option V :=
  if h : q.val < Q.path.card then Q.path.vertex ⟨q.val, h⟩
  else some (T.vertex ⟨q.val - Q.path.card, by have := q.isLt; omega⟩)

theorem appendVertex_of_lt {T : IndexedInducedPath G} {q : Fin (Q.path.card + T.card)}
    (h : q.val < Q.path.card) :
    appendVertex Q T q = Q.path.vertex ⟨q.val, h⟩ := by
  simp only [appendVertex, dif_pos h]

theorem appendVertex_of_ge {T : IndexedInducedPath G} {q : Fin (Q.path.card + T.card)}
    (h : Q.path.card ≤ q.val) (r : Fin T.card) (hr : r.val = q.val - Q.path.card) :
    appendVertex Q T q = some (T.vertex r) := by
  have h1 : ¬ q.val < Q.path.card := by omega
  simp only [appendVertex, dif_neg h1]
  congr 2
  exact Fin.ext hr.symm

theorem appendVertex_injective {T : IndexedInducedPath G} (hA : AppendData Q T) :
    Function.Injective (appendVertex Q T) := by
  intro p q hpq
  by_cases hp : p.val < Q.path.card <;> by_cases hq : q.val < Q.path.card
  · rw [appendVertex_of_lt hp, appendVertex_of_lt hq] at hpq
    have := congrArg Fin.val (Q.path.injective hpq)
    exact Fin.ext this
  · rw [appendVertex_of_lt hp,
      appendVertex_of_ge (by omega) ⟨q.val - Q.path.card, by have := q.isLt; omega⟩ rfl]
      at hpq
    exact absurd ⟨_, hpq⟩ (hA.outside _)
  · rw [appendVertex_of_lt hq,
      appendVertex_of_ge (by omega) ⟨p.val - Q.path.card, by have := p.isLt; omega⟩ rfl]
      at hpq
    exact absurd ⟨_, hpq.symm⟩ (hA.outside _)
  · rw [appendVertex_of_ge (by omega) ⟨p.val - Q.path.card, by have := p.isLt; omega⟩ rfl,
      appendVertex_of_ge (by omega) ⟨q.val - Q.path.card, by have := q.isLt; omega⟩ rfl]
      at hpq
    have h1 := T.injective (Option.some.inj hpq)
    have h2 := congrArg Fin.val h1
    simp only at h2
    exact Fin.ext (by omega)

/-- Adjacency between a vertex of `Q` and a vertex of `T` in `Q ++ T`. -/
theorem appendVertex_adj_lt_ge {T : IndexedInducedPath G} (hA : AppendData Q T)
    {p q : Fin (Q.path.card + T.card)} (hp : p.val < Q.path.card)
    (hq : Q.path.card ≤ q.val) :
    (G.adjoinRootAt K).Adj (appendVertex Q T p) (appendVertex Q T q) ↔
      p.val + 1 = q.val ∨ q.val + 1 = p.val := by
  have hqT : q.val - Q.path.card < T.card := by have := q.isLt; omega
  rw [appendVertex_of_lt hp, appendVertex_of_ge hq ⟨q.val - Q.path.card, hqT⟩ rfl]
  by_cases hpe : p.val + 1 < Q.path.card
  · constructor
    · intro hadj
      exact absurd hadj (hA.early ⟨p.val, hp⟩ hpe _)
    · rintro (h | h) <;> omega
  · have hpt : Q.path.vertex ⟨p.val, hp⟩ = Q.terminalVertex :=
      congrArg Q.path.vertex (Fin.ext (by
        change p.val = Q.path.card - 1
        omega))
    rw [hpt, hA.terminal ⟨q.val - Q.path.card, hqT⟩]
    simp only
    omega

theorem appendVertex_adj_iff {T : IndexedInducedPath G} (hA : AppendData Q T)
    (p q : Fin (Q.path.card + T.card)) :
    (G.adjoinRootAt K).Adj (appendVertex Q T p) (appendVertex Q T q) ↔
      p.val + 1 = q.val ∨ q.val + 1 = p.val := by
  by_cases hp : p.val < Q.path.card <;> by_cases hq : q.val < Q.path.card
  · rw [appendVertex_of_lt hp, appendVertex_of_lt hq]
    exact Q.path.adj_iff _ _
  · exact appendVertex_adj_lt_ge hA hp (by omega)
  · rw [(G.adjoinRootAt K).adj_comm, appendVertex_adj_lt_ge hA hq (by omega)]
    omega
  · rw [appendVertex_of_ge (by omega) ⟨p.val - Q.path.card, by have := p.isLt; omega⟩ rfl,
      appendVertex_of_ge (by omega) ⟨q.val - Q.path.card, by have := q.isLt; omega⟩ rfl]
    change G.Adj _ _ ↔ _
    rw [T.adj_iff]
    simp only
    omega

/-- The concatenation `Q ++ T` of a clique-rooted path with an induced path of `G`
that is attached at the terminal vertex of `Q` (`AppendData`). -/
def appendPath (Q : CliqueRootedInducedPath G K) (T : IndexedInducedPath G)
    (hA : AppendData Q T) : CliqueRootedInducedPath G K where
  path :=
    { card := Q.path.card + T.card
      nonempty := by have := Q.path.nonempty; omega
      vertex := appendVertex Q T
      injective := appendVertex_injective hA
      adj_iff := appendVertex_adj_iff hA }
  root_eq := by
    change appendVertex Q T ⟨0, _⟩ = none
    rw [appendVertex_of_lt (by have := Q.path.nonempty; omega)]
    exact Q.root_eq

@[simp]
theorem appendPath_card {T : IndexedInducedPath G} (hA : AppendData Q T) :
    (appendPath Q T hA).path.card = Q.path.card + T.card :=
  rfl

theorem appendPath_vertex_of_lt {T : IndexedInducedPath G} (hA : AppendData Q T)
    {q : Fin (appendPath Q T hA).path.card} (h : q.val < Q.path.card) :
    (appendPath Q T hA).path.vertex q = Q.path.vertex ⟨q.val, h⟩ :=
  appendVertex_of_lt h

theorem appendPath_vertex_of_ge {T : IndexedInducedPath G} (hA : AppendData Q T)
    {q : Fin (appendPath Q T hA).path.card} (h : Q.path.card ≤ q.val)
    (r : Fin T.card) (hr : r.val = q.val - Q.path.card) :
    (appendPath Q T hA).path.vertex q = some (T.vertex r) :=
  appendVertex_of_ge h r hr

/-- The original carrier of `Q ++ T` is the original carrier of `Q` together with the
vertices of `T`. -/
theorem appendPath_originalCarrier {T : IndexedInducedPath G} (hA : AppendData Q T) :
    (appendPath Q T hA).originalCarrier = Q.originalCarrier ∪ Set.range T.vertex := by
  ext v
  constructor
  · rintro ⟨q, hq⟩
    have hqlt : q.val < Q.path.card + T.card := q.isLt
    by_cases hql : q.val < Q.path.card
    · left
      exact ⟨⟨q.val, hql⟩, (appendPath_vertex_of_lt hA hql).symm.trans hq⟩
    · right
      refine ⟨⟨q.val - Q.path.card, by omega⟩, ?_⟩
      have := (appendPath_vertex_of_ge hA (by omega) ⟨q.val - Q.path.card, by omega⟩
        rfl).symm.trans hq
      exact Option.some.inj this
  · rintro (⟨q, hq⟩ | ⟨r, hr⟩)
    · have hqlt : q.val < Q.path.card := q.isLt
      exact ⟨⟨q.val, by rw [appendPath_card]; omega⟩, by
        rw [appendPath_vertex_of_lt hA hqlt]
        exact hq⟩
    · have hrlt : r.val < T.card := r.isLt
      exact ⟨⟨Q.path.card + r.val, by rw [appendPath_card]; omega⟩, by
        rw [appendPath_vertex_of_ge hA (by simp) r (by simp)]
        exact congrArg some hr⟩

/-- The initial segment of `Q ++ T` ending at the last vertex of `Q` is `Q`. -/
theorem appendPath_initialSegment {T : IndexedInducedPath G} (hA : AppendData Q T) :
    (appendPath Q T hA).initialSegment ⟨Q.path.card - 1, by
      have := Q.path.nonempty
      change Q.path.card - 1 < Q.path.card + T.card
      omega⟩ = Q := by
  have hc : Q.path.card - 1 + 1 = Q.path.card := by have := Q.path.nonempty; omega
  apply ext_path
  apply IndexedInducedPath.ext_card_vertex (by exact hc)
  apply Function.hfunext (congrArg Fin hc)
  intro a b hab
  have hval : a.val = b.val := (Fin.heq_ext_iff hc).1 hab
  have hb : b.val < Q.path.card := b.isLt
  apply heq_of_eq
  change (appendPath Q T hA).path.vertex ⟨a.val, _⟩ = Q.path.vertex b
  rw [appendPath_vertex_of_lt hA (by simp [hval, hb])]
  exact congrArg Q.path.vertex (Fin.ext hval)

end RootedInducedPath

/-! ### Opening a hole at a vertex -/

namespace IndexedInducedHole

variable (H : G.IndexedInducedHole)

/-- The index reached from `p` after `r` steps around a cycle of `n` positions. -/
def stepIndex (n p r : ℕ) : ℕ := if p + r < n then p + r else p + r - n

theorem stepIndex_lt {n p r : ℕ} (hp : p < n) (hr : r < n) : stepIndex n p r < n := by
  unfold stepIndex
  split_ifs <;> omega

/-- The position reached from `p` after `r < n` steps around the hole. -/
def stepFin (p : Fin H.card) (r : ℕ) (hr : r < H.card) : Fin H.card :=
  ⟨stepIndex H.card p.val r, stepIndex_lt p.isLt hr⟩

theorem stepFin_injective (p : Fin H.card) {r r' : ℕ} (hr : r < H.card)
    (hr' : r' < H.card) (h : H.stepFin p r hr = H.stepFin p r' hr') : r = r' := by
  have := congrArg Fin.val h
  simp only [stepFin, stepIndex] at this
  have := p.isLt
  split_ifs at * <;> omega

/-- The induced path obtained by opening the hole `H` at the vertex of index `p`:
it runs `H.vertex p, H.vertex (p + 1), ..., ` around the cycle and omits the vertex
`H.vertex (p - 1)`, so that it has `H.card - 1` vertices. -/
def pathFrom (p : Fin H.card) : IndexedInducedPath G where
  card := H.card - 1
  nonempty := by have := H.four_le_card; omega
  vertex r := H.vertex (H.stepFin p r.val (by have := r.isLt; omega))
  injective := by
    intro r r' h
    exact Fin.ext (H.stepFin_injective p _ _ (H.injective h))
  adj_iff := by
    intro r r'
    rw [H.adj_iff]
    have hr := r.isLt
    have hr' := r'.isLt
    have hp := p.isLt
    have h4 := H.four_le_card
    change r.val < H.card - 1 at hr
    change r'.val < H.card - 1 at hr'
    simp only [CyclicAdjacent, stepFin, stepIndex]
    split_ifs <;> omega

/-- The last position of the walk around the hole from `p`, i.e. `p - 1`. -/
def lastFin (p : Fin H.card) : Fin H.card :=
  H.stepFin p (H.card - 1) (by have := H.four_le_card; omega)

theorem pathFrom_vertex_zero (p : Fin H.card) :
    (H.pathFrom p).vertex ⟨0, (H.pathFrom p).nonempty⟩ = H.vertex p := by
  change H.vertex (H.stepFin p 0 _) = _
  congr 1
  apply Fin.ext
  simp only [stepFin, stepIndex]
  have := p.isLt
  split_ifs <;> omega

/-- The vertex `H.vertex (p - 1)` closing the walk is adjacent to the walk exactly at
its two ends. -/
theorem adj_lastFin_pathFrom (p : Fin H.card) (r : Fin (H.pathFrom p).card) :
    G.Adj (H.vertex (H.lastFin p)) ((H.pathFrom p).vertex r) ↔
      r.val = 0 ∨ r.val + 1 = (H.pathFrom p).card := by
  refine (H.adj_iff _ _).trans ?_
  have hr := r.isLt
  have hp := p.isLt
  have h4 := H.four_le_card
  change r.val < H.card - 1 at hr
  change _ ↔ r.val = 0 ∨ r.val + 1 = H.card - 1
  simp only [CyclicAdjacent, lastFin, pathFrom, stepFin, stepIndex]
  split_ifs <;> omega

/-- The vertex `H.vertex (p - 1)` is not on the opened path. -/
theorem lastFin_ne_pathFrom (p : Fin H.card) (r : Fin (H.pathFrom p).card) :
    (H.pathFrom p).vertex r ≠ H.vertex (H.lastFin p) := by
  intro h
  have := H.stepFin_injective p _ _ (H.injective h)
  have hr := r.isLt
  change r.val < H.card - 1 at hr
  omega

/-- The opened path and the closing vertex exhaust the hole. -/
theorem range_pathFrom (p : Fin H.card) :
    Set.range (H.pathFrom p).vertex = Set.range H.vertex \ {H.vertex (H.lastFin p)} := by
  ext v
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨⟨_, rfl⟩, H.lastFin_ne_pathFrom p r⟩
  · rintro ⟨⟨m, rfl⟩, hm⟩
    have hmne : m ≠ H.lastFin p := fun h => hm (by rw [h]; rfl)
    have hp := p.isLt
    have hm' := m.isLt
    have h4 := H.four_le_card
    by_cases hmp : p.val ≤ m.val
    · refine ⟨⟨m.val - p.val, ?_⟩, ?_⟩
      · change m.val - p.val < H.card - 1
        by_contra hbig
        apply hmne
        apply Fin.ext
        simp only [lastFin, stepFin, stepIndex]
        split_ifs <;> omega
      · change H.vertex (H.stepFin p (m.val - p.val) _) = _
        congr 1
        apply Fin.ext
        simp only [stepFin, stepIndex]
        split_ifs <;> omega
    · refine ⟨⟨m.val + H.card - p.val, ?_⟩, ?_⟩
      · change m.val + H.card - p.val < H.card - 1
        by_contra hbig
        apply hmne
        apply Fin.ext
        simp only [lastFin, stepFin, stepIndex]
        split_ifs <;> omega
      · change H.vertex (H.stepFin p (m.val + H.card - p.val) _) = _
        congr 1
        apply Fin.ext
        simp only [stepFin, stepIndex]
        split_ifs <;> omega

/-- For two cyclically adjacent positions `a`, `b` there is a starting position `p`
for opening the hole such that the first vertex of the opened path and the closing
vertex are the two given vertices, in one order or the other. -/
theorem exists_pathFrom_ends {a b : Fin H.card} (hab : CyclicAdjacent a b) :
    ∃ p : Fin H.card, (p = a ∧ H.lastFin p = b) ∨ (p = b ∧ H.lastFin p = a) := by
  have ha := a.isLt
  have hb := b.isLt
  have h4 := H.four_le_card
  unfold CyclicAdjacent at hab
  rcases hab with h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨b, Or.inr ⟨rfl, Fin.ext ?_⟩⟩
    simp only [lastFin, stepFin, stepIndex]
    split_ifs <;> omega
  · refine ⟨a, Or.inl ⟨rfl, Fin.ext ?_⟩⟩
    simp only [lastFin, stepFin, stepIndex]
    split_ifs <;> omega
  · refine ⟨a, Or.inl ⟨rfl, Fin.ext ?_⟩⟩
    simp only [lastFin, stepFin, stepIndex]
    split_ifs <;> omega
  · refine ⟨b, Or.inr ⟨rfl, Fin.ext ?_⟩⟩
    simp only [lastFin, stepFin, stepIndex]
    split_ifs <;> omega

end IndexedInducedHole

/-! ### Every attached hole is the hoop of a wand with handle `Q` -/

namespace RootedInducedPath

/-- Existence: if the vertex set of an indexed hole `H` is attached to the rooted path
`Q`, then there is a rooted path `P` and a bubble wand `w` on `P` whose handle is `Q`
and whose hoop carrier is the vertex set of `H`.

Opening `H` at one of the two neighbours `x`, `y` of the terminal `t` of `Q` gives an
induced path `T` starting at that neighbour and ending next to the other one; `P` is the
concatenation `Q ++ T` and the bubble is the closing vertex of the hole.  Only the
definition of attachment is used: neither claw-freeness nor a clique is needed. -/
theorem exists_cliqueBubbleWand_of_holeAttached {Q : CliqueRootedInducedPath G K}
    (H : G.IndexedInducedHole) (hQ : Q.HoleAttached (Set.range H.vertex)) :
    ∃ (P : CliqueRootedInducedPath G K) (w : CliqueBubbleWand G K P),
      w.handle = Q ∧ w.hoopCarrier = Set.range H.vertex := by
  obtain ⟨hQ1, hQ2, x, y, hx, hy, hxy, hQ3⟩ := hQ
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  have hab : CyclicAdjacent a b := (H.adj_iff a b).1 hxy
  obtain ⟨p, hp⟩ := H.exists_pathFrom_ends hab
  -- the neighbours of `t` in the hole are the first vertex and the closing vertex
  have hΓ : ∀ v ∈ Set.range H.vertex,
      ((G.adjoinRootAt K).Adj Q.terminalVertex (some v) ↔
        v = H.vertex p ∨ v = H.vertex (H.lastFin p)) := by
    intro v hv
    rw [hQ3 v hv]
    rcases hp with ⟨hpa, h2⟩ | ⟨hpb, h2⟩
    · rw [h2, hpa]
    · rw [h2, hpb, or_comm]
  have hTC : ∀ r : Fin (H.pathFrom p).card,
      (H.pathFrom p).vertex r ∈ Set.range H.vertex := fun r => ⟨_, rfl⟩
  have hA : AppendData Q (H.pathFrom p) :=
    { outside := fun r => hQ1 _ (hTC r)
      early := fun p' hp' r => hQ2 p' hp' _ (hTC r)
      terminal := fun r => by
        rw [hΓ _ (hTC r)]
        constructor
        · rintro (h | h)
          · have h0 := H.pathFrom_vertex_zero p
            have := (H.pathFrom p).injective (h.trans h0.symm)
            exact congrArg Fin.val this
          · exact absurd h (H.lastFin_ne_pathFrom p r)
        · intro hr0
          left
          have : r = ⟨0, (H.pathFrom p).nonempty⟩ := Fin.ext hr0
          rw [this]
          exact H.pathFrom_vertex_zero p }
  have hcardQ := Q.path.nonempty
  have hn := H.four_le_card
  have hTcard : (H.pathFrom p).card = H.card - 1 := rfl
  have hjmem : H.vertex (H.lastFin p) ∈ Set.range H.vertex := ⟨_, rfl⟩
  let P := appendPath Q (H.pathFrom p) hA
  let w : CliqueBubbleWand G K P :=
    { bubble := H.vertex (H.lastFin p)
      split := ⟨Q.path.card - 1, by
        change Q.path.card - 1 < Q.path.card + (H.pathFrom p).card
        omega⟩
      gap := by
        change Q.path.card - 1 + 3 < Q.path.card + (H.pathFrom p).card
        omega
      outside := by
        rintro ⟨m, hm⟩
        have hmlt : m.val < Q.path.card + (H.pathFrom p).card := m.isLt
        by_cases hml : m.val < Q.path.card
        · rw [appendPath_vertex_of_lt hA hml] at hm
          exact hQ1 _ hjmem ⟨_, hm⟩
        · rw [appendPath_vertex_of_ge hA (by omega)
            ⟨m.val - Q.path.card, by omega⟩ rfl] at hm
          exact H.lastFin_ne_pathFrom p _ (Option.some.inj hm)
      adj_iff := by
        intro m
        have hmlt : m.val < Q.path.card + (H.pathFrom p).card := m.isLt
        change _ ↔ m.val = Q.path.card - 1 ∨ m.val = Q.path.card - 1 + 1 ∨
          m.val + 1 = Q.path.card + (H.pathFrom p).card
        by_cases hml : m.val < Q.path.card
        · rw [appendPath_vertex_of_lt hA hml]
          by_cases hme : m.val + 1 < Q.path.card
          · constructor
            · intro hadj
              exact absurd hadj.symm (hQ2 ⟨m.val, hml⟩ hme _ hjmem)
            · intro h
              omega
          · have hmt : Q.path.vertex ⟨m.val, hml⟩ = Q.terminalVertex :=
              congrArg Q.path.vertex (Fin.ext (by
                change m.val = Q.path.card - 1
                omega))
            rw [hmt]
            constructor
            · intro _
              omega
            · intro _
              exact ((hΓ _ hjmem).2 (Or.inr rfl)).symm
        · rw [appendPath_vertex_of_ge hA (by omega) ⟨m.val - Q.path.card, by omega⟩ rfl]
          change G.Adj _ _ ↔ _
          refine (H.adj_lastFin_pathFrom p ⟨m.val - Q.path.card, by omega⟩).trans ?_
          change m.val - Q.path.card = 0 ∨ m.val - Q.path.card + 1 = (H.pathFrom p).card ↔ _
          omega }
  have hh : w.handle = Q := appendPath_initialSegment hA
  refine ⟨P, w, hh, ?_⟩
  have hcarrier : w.hoopCarrier = (P.originalCarrier \ Q.originalCarrier) ∪
      {H.vertex (H.lastFin p)} := by
    unfold CliqueBubbleWand.hoopCarrier bubbleWandArcHoopCarrier
    rw [hh]
  rw [hcarrier, appendPath_originalCarrier hA]
  have hdisj : Disjoint Q.originalCarrier (Set.range (H.pathFrom p).vertex) := by
    rw [Set.disjoint_left]
    rintro v ⟨q, hq⟩ ⟨r, hr⟩
    exact hA.outside r ⟨q, hr ▸ hq⟩
  rw [Set.union_sdiff_cancel_left (Set.disjoint_iff.1 hdisj), H.range_pathFrom p]
  ext v
  constructor
  · rintro (⟨hv, _⟩ | hv)
    · exact hv
    · exact hv ▸ hjmem
  · intro hv
    by_cases hvj : v = H.vertex (H.lastFin p)
    · exact Or.inr hvj
    · exact Or.inl ⟨hv, hvj⟩

end RootedInducedPath

/-! ### The events of a handle correspond two to one to the attached holes -/

namespace CliqueBubbleWand

variable {P : CliqueRootedInducedPath G K}

/-- The bubble lies in the hoop carrier. -/
theorem bubble_mem_hoopCarrier (w : CliqueBubbleWand G K P) :
    w.bubble ∈ w.hoopCarrier :=
  Or.inr rfl

/-- The bubble is adjacent to the terminal vertex of the handle. -/
theorem adj_handle_terminalVertex (w : CliqueBubbleWand G K P) :
    (G.adjoinRootAt K).Adj w.handle.terminalVertex (some w.bubble) := by
  rw [w.handle_terminalVertex]
  exact w.adj_split.symm

/-- Even hoop sizes: the hoop carrier of a wand has `hoopCard` elements. -/
theorem even_hoopCard_of_range_eq (w : CliqueBubbleWand G K P) (H : G.IndexedInducedHole)
    (hev : Even H.card) (h : w.hoopCarrier = Set.range H.vertex) : Even w.hoopCard := by
  have hnc : (Set.range H.vertex).ncard = H.card := by
    rw [Set.ncard_range_of_injective H.injective, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  rw [← w.hoopCarrier_ncard, h, hnc]
  exact hev

end CliqueBubbleWand

section Events

variable [Fintype V] [DecidableEq V]

open Classical in
/-- The two-to-one correspondence between wand events and attached holes (claim (ii)
of the package, with the hole condition made explicit).  The *wand events* with handle
`Q` and hoop class `c` are the pairs `(P, j)` with a bubble wand on `P` with bubble `j`,
handle `Q` and an even hoop in the class `c`.  They correspond two to one to the
even-hole carriers of `c` that are attached to `Q`: a hole `C` attached to `Q` gives the
event `(P, j)` with hoop carrier `C`, and its reversal `(P*, j_{s+1})`
(`CliqueBubbleWand.reverseWand`); there are no others, because the bubble is one of the
two neighbours of the terminal of `Q` in `C` and the source path is determined by its
original carrier.  Hence `#events = 2 |c|` or `0` once claim (i) is used
(`card_evenHoopEvents_of_attached`).

The sets counted on the right are the even-hole carriers (`IsEvenHoleCarrier`) of the
class `c`.  Without this condition the statement is false
(`HoleAttachmentExample.card_evenHoopEvents_literal_false`): the quotient `EvenHoleDeformationClass`
ranges over all sets of vertices, and an attached non-hole vertex set (for instance an
edge `{x, y} ⊆ K` with `Q = {j*}`) is a class of its own with no events.  For a class `c`
of a hole the two readings agree (`card_evenHoopEvents_of_holeClass`).  Neither
claw-freeness nor simpliciality is used here. -/
theorem card_evenHoopEvents (Q : CliqueRootedInducedPath G K)
    (c : EvenHoleDeformationClass G) :
    (Finset.univ.filter fun e : CliqueRootedInducedPath G K × V =>
        ∃ w : CliqueBubbleWand G K e.1, w.bubble = e.2 ∧ w.handle = Q ∧
          Even w.hoopCard ∧ G.evenHoleDeformationClassOf w.hoopCarrier = c).card =
      2 * (Finset.univ.filter fun C : Set V =>
        G.IsEvenHoleCarrier C ∧ G.evenHoleDeformationClassOf C = c ∧
          Q.HoleAttached C).card := by
  set Ev := Finset.univ.filter fun e : CliqueRootedInducedPath G K × V =>
        ∃ w : CliqueBubbleWand G K e.1, w.bubble = e.2 ∧ w.handle = Q ∧
          Even w.hoopCard ∧ G.evenHoleDeformationClassOf w.hoopCarrier = c with hEv
  set Hs := Finset.univ.filter fun C : Set V =>
        G.IsEvenHoleCarrier C ∧ G.evenHoleDeformationClassOf C = c ∧
          Q.HoleAttached C with hHs
  let φ : CliqueRootedInducedPath G K × V → Set V :=
    fun e => bubbleWandArcHoopCarrier e.1 Q e.2
  have hφ : ∀ (e : CliqueRootedInducedPath G K × V) (w : CliqueBubbleWand G K e.1),
      w.handle = Q → w.bubble = e.2 → φ e = w.hoopCarrier := by
    intro e w hh hb
    unfold φ CliqueBubbleWand.hoopCarrier
    rw [hh, hb]
  have hmaps : ∀ e ∈ Ev, φ e ∈ Hs := by
    intro e he
    rw [hEv, Finset.mem_filter] at he
    obtain ⟨-, w, hb, hh, hev, hc⟩ := he
    rw [hHs, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hφ e w hh hb]
    refine ⟨⟨w.hoopHole, by rw [w.hoopHole_card]; exact hev, w.range_hoopHole⟩, hc, ?_⟩
    have := w.holeAttached_hoopCarrier
    rwa [hh] at this
  have hfiber : ∀ C ∈ Hs, (Ev.filter fun e => φ e = C).card = 2 := by
    intro C hC
    rw [hHs, Finset.mem_filter] at hC
    obtain ⟨-, ⟨H, hHev, hHC⟩, hcC, hQC⟩ := hC
    have hQH : Q.HoleAttached (Set.range H.vertex) := hHC ▸ hQC
    obtain ⟨P, w, hh, hcar⟩ :=
      RootedInducedPath.exists_cliqueBubbleWand_of_holeAttached H hQH
    rw [hHC] at hcar
    have hw_ev : Even w.hoopCard :=
      w.even_hoopCard_of_range_eq H hHev (hcar.trans hHC.symm)
    have hw_cls : G.evenHoleDeformationClassOf w.hoopCarrier = c := by
      rw [hcar]
      exact hcC
    -- the second wand: the reversal
    have hh2 : w.reverseWand.handle = Q := w.reverseWand_handle.trans hh
    have hcar2 : w.reverseWand.hoopCarrier = C := w.reverseWand_hoopCarrier.trans hcar
    have hev2 : Even w.reverseWand.hoopCard := by
      rw [w.reverseWand_hoopCard]
      exact hw_ev
    have hcls2 : G.evenHoleDeformationClassOf w.reverseWand.hoopCarrier = c := by
      rw [hcar2]
      exact hcC
    have he1 : (P, w.bubble) ∈ Ev ∧ φ (P, w.bubble) = C := by
      refine ⟨?_, (hφ (P, w.bubble) w hh rfl).trans hcar⟩
      rw [hEv, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, w, rfl, hh, hw_ev, hw_cls⟩
    have he2 : (w.reverse, w.reverseBubble) ∈ Ev ∧
        φ (w.reverse, w.reverseBubble) = C := by
      refine ⟨?_, (hφ (w.reverse, w.reverseBubble) w.reverseWand hh2 rfl).trans hcar2⟩
      rw [hEv, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, w.reverseWand, rfl, hh2, hev2, hcls2⟩
    have hne : ((P, w.bubble) : CliqueRootedInducedPath G K × V) ≠
        (w.reverse, w.reverseBubble) :=
      fun h => w.adj_bubble_reverseBubble.ne (congrArg Prod.snd h)
    rw [Finset.card_eq_two]
    refine ⟨(P, w.bubble), (w.reverse, w.reverseBubble), hne, ?_⟩
    obtain ⟨-, -, x, y, hx, hy, hxy, hΓ⟩ := hQC
    -- a bubble of a wand with handle `Q` and hoop carrier `C` is `x` or `y`
    have hbub : ∀ {P' : CliqueRootedInducedPath G K} (w' : CliqueBubbleWand G K P'),
        w'.handle = Q → w'.hoopCarrier = C → w'.bubble = x ∨ w'.bubble = y := by
      intro P' w' hh' hc'
      refine (hΓ w'.bubble (hc' ▸ w'.bubble_mem_hoopCarrier)).1 ?_
      have := w'.adj_handle_terminalVertex
      rwa [hh'] at this
    ext e
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨he, hφe⟩
      rw [hEv, Finset.mem_filter] at he
      obtain ⟨-, w', hb', hh', -, -⟩ := he
      have hc' : w'.hoopCarrier = C := by rw [← hφ e w' hh' hb']; exact hφe
      have hj : e.2 = w.bubble ∨ e.2 = w.reverseBubble := by
        have h1 := hbub w' hh' hc'
        have h2 := hbub w hh hcar
        have h3 := hbub w.reverseWand hh2 hcar2
        have h4 := w.adj_bubble_reverseBubble.ne
        rw [hb'] at h1
        change e.2 = x ∨ e.2 = y at h1
        change w.bubble = x ∨ w.bubble = y at h2
        change w.reverseBubble = x ∨ w.reverseBubble = y at h3
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
          first
          | exact Or.inl (h1.trans h2.symm)
          | exact Or.inr (h1.trans h3.symm)
          | exact absurd (h2.trans h3.symm) h4
      rcases hj with hj | hj
      · left
        exact Prod.ext (w.eq_of_handle_hoopCarrier_bubble_eq w' (hh.trans hh'.symm)
          (hcar.trans hc'.symm) (hb'.trans hj).symm).symm hj
      · right
        exact Prod.ext (w.reverseWand.eq_of_handle_hoopCarrier_bubble_eq w'
          (hh2.trans hh'.symm) (hcar2.trans hc'.symm) (hb'.trans hj).symm).symm hj
    · rintro (rfl | rfl)
      · exact he1
      · exact he2
  rw [Finset.card_eq_sum_card_fiberwise hmaps, Finset.sum_const_nat hfiber, mul_comm]

end Events

/-! ### Sizes are constant on a deformation class -/

section ClassSizes

variable [Finite V]

/-- A single-vertex deformation step does not change the number of vertices. -/
theorem EvenHoleDeformationStep.ncard_eq {A B : Set V}
    (hstep : EvenHoleDeformationStep G A B) : A.ncard = B.ncard := by
  obtain ⟨k, E, s, i, h, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := hstep
  · have key : (E.deformedCarrier s i).ncard = E.carrier.ncard := by
      have hfin : (E.carrier \ {E.a i}).Finite := (Set.toFinite _)
      have h1 : (E.deformedCarrier s i).ncard = (E.carrier \ {E.a i}).ncard + 1 :=
        Set.ncard_insert_of_notMem (fun hmem => h.outside hmem.1) hfin
      have h2 := Set.ncard_sdiff_singleton_add_one (E.a_mem_carrier i)
        (Set.toFinite E.carrier)
      omega
    exact key.symm
  · have hfin : (E.carrier \ {E.a i}).Finite := (Set.toFinite _)
    have h1 : (E.deformedCarrier s i).ncard = (E.carrier \ {E.a i}).ncard + 1 :=
      Set.ncard_insert_of_notMem (fun hmem => h.outside hmem.1) hfin
    have h2 := Set.ncard_sdiff_singleton_add_one (E.a_mem_carrier i)
      (Set.toFinite E.carrier)
    omega

/-- All carriers of a deformation class have the same number of vertices. -/
theorem InEvenHoleDeformationClosure.ncard_eq {A B : Set V}
    (h : InEvenHoleDeformationClosure G A B) : A.ncard = B.ncard := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans hstep.ncard_eq

/-- The half-length `k` of the holes of a deformation class: the number of vertices of
any carrier of the class, halved. -/
noncomputable def evenHoleClassHalfLength (c : EvenHoleDeformationClass G) : ℕ :=
  Quotient.liftOn c (fun C => C.ncard / 2) (fun _ _ h => by
    have := (show InEvenHoleDeformationClosure G _ _ from h).ncard_eq
    simp only [this])

@[simp]
theorem evenHoleClassHalfLength_classOf (C : Set V) :
    evenHoleClassHalfLength (G.evenHoleDeformationClassOf C) = C.ncard / 2 :=
  rfl

end ClassSizes

/-! ### Counting for the class of an attached hole -/

section ClassCounts

variable [Fintype V] [DecidableEq V]

open Classical in
/-- If the class `c` is the class of an even hole then every set of `c` is an even-hole
carrier, so the hole condition in `card_evenHoopEvents` is automatic. -/
theorem card_evenHoopEvents_of_holeClass (Q : CliqueRootedInducedPath G K)
    (c : EvenHoleDeformationClass G)
    (hc : ∃ D : Set V, G.IsEvenHoleCarrier D ∧ G.evenHoleDeformationClassOf D = c) :
    (Finset.univ.filter fun e : CliqueRootedInducedPath G K × V =>
        ∃ w : CliqueBubbleWand G K e.1, w.bubble = e.2 ∧ w.handle = Q ∧
          Even w.hoopCard ∧ G.evenHoleDeformationClassOf w.hoopCarrier = c).card =
      2 * (Finset.univ.filter fun C : Set V =>
        G.evenHoleDeformationClassOf C = c ∧ Q.HoleAttached C).card := by
  rw [card_evenHoopEvents]
  congr 2
  apply Finset.filter_congr
  intro C _
  obtain ⟨D, hD, rfl⟩ := hc
  constructor
  · rintro ⟨-, h⟩
    exact h
  · rintro ⟨hcl, hQ⟩
    exact ⟨(evenHoleDeformationClassOf_eq_iff.1 hcl.symm).isEvenHoleCarrier hD, hcl, hQ⟩

open Classical in
/-- The attached even holes of the class of an attached even hole `C₀` are exactly the
carriers of the deformation closure `⟨C₀⟩`: claim (i) makes every member of the class
attached, and the closure consists of even-hole carriers. -/
theorem attachedHoleFinset_eq_closure (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree)
    {Q : CliqueRootedInducedPath G K} {C₀ : Set V} (hC₀ : G.IsEvenHoleCarrier C₀)
    (hQ : Q.HoleAttached C₀) :
    (Finset.univ.filter fun C : Set V =>
        G.IsEvenHoleCarrier C ∧ G.evenHoleDeformationClassOf C =
          G.evenHoleDeformationClassOf C₀ ∧ Q.HoleAttached C) =
      G.deformationClosureFinset C₀ := by
  ext C
  rw [Finset.mem_filter, mem_deformationClosureFinset]
  constructor
  · rintro ⟨-, -, hcl, -⟩
    exact evenHoleDeformationClassOf_eq_iff.1 hcl.symm
  · intro h
    exact ⟨Finset.mem_univ _, h.isEvenHoleCarrier hC₀,
      evenHoleDeformationClassOf_eq_iff.2 h.symm,
      RootedInducedPath.HoleAttached.of_closure hK hclaw h hQ⟩

open Classical in
/-- If one even hole `C₀` of the class `c` is attached to `Q`, there are exactly
`2 |c|` wand events with handle `Q` and hoop class `c` (v1 assumes this at the handle
`P'` of case (b.iv), L1555-1576: every hole of `⟨C₀⟩` occurs at the handle twice, the two
directions around the hole). -/
theorem card_evenHoopEvents_of_attached (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree)
    {Q : CliqueRootedInducedPath G K} {C₀ : Set V} (hC₀ : G.IsEvenHoleCarrier C₀)
    (hQ : Q.HoleAttached C₀) :
    (Finset.univ.filter fun e : CliqueRootedInducedPath G K × V =>
        ∃ w : CliqueBubbleWand G K e.1, w.bubble = e.2 ∧ w.handle = Q ∧
          Even w.hoopCard ∧
          G.evenHoleDeformationClassOf w.hoopCarrier = G.evenHoleDeformationClassOf C₀).card =
      2 * evenHoleClassSize (G.evenHoleDeformationClassOf C₀) := by
  rw [card_evenHoopEvents, attachedHoleFinset_eq_closure hK hclaw hC₀ hQ,
    evenHoleClassSize_classOf]

open Classical in
/-- If no even hole of the class `c` is attached to `Q` there are no wand events with
handle `Q` and hoop class `c`. -/
theorem card_evenHoopEvents_eq_zero_of_not_attached (Q : CliqueRootedInducedPath G K)
    (c : EvenHoleDeformationClass G)
    (h : ∀ C : Set V, G.IsEvenHoleCarrier C → G.evenHoleDeformationClassOf C = c →
      ¬ Q.HoleAttached C) :
    (Finset.univ.filter fun e : CliqueRootedInducedPath G K × V =>
        ∃ w : CliqueBubbleWand G K e.1, w.bubble = e.2 ∧ w.handle = Q ∧
          Even w.hoopCard ∧ G.evenHoleDeformationClassOf w.hoopCarrier = c).card = 0 := by
  rw [card_evenHoopEvents]
  have : (Finset.univ.filter fun C : Set V =>
        G.IsEvenHoleCarrier C ∧ G.evenHoleDeformationClassOf C = c ∧
          Q.HoleAttached C) = ∅ := by
    apply Finset.filter_false_of_mem
    rintro C _ ⟨h1, h2, h3⟩
    exact h C h1 h2 h3
  rw [this]
  rfl

open Classical in
/-- The two cases together: `2 |c|` events if an even hole of the class `c` is attached
to `Q` (every hole of `c` then is), and none otherwise. -/
theorem card_evenHoopEvents_eq (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree)
    (Q : CliqueRootedInducedPath G K) (c : EvenHoleDeformationClass G) :
    (Finset.univ.filter fun e : CliqueRootedInducedPath G K × V =>
        ∃ w : CliqueBubbleWand G K e.1, w.bubble = e.2 ∧ w.handle = Q ∧
          Even w.hoopCard ∧ G.evenHoleDeformationClassOf w.hoopCarrier = c).card =
      if ∃ C : Set V, G.IsEvenHoleCarrier C ∧ G.evenHoleDeformationClassOf C = c ∧
          Q.HoleAttached C then 2 * evenHoleClassSize c else 0 := by
  by_cases hex : ∃ C : Set V, G.IsEvenHoleCarrier C ∧ G.evenHoleDeformationClassOf C = c ∧
      Q.HoleAttached C
  · rw [if_pos hex]
    obtain ⟨C₀, hC₀, rfl, hQ⟩ := hex
    exact card_evenHoopEvents_of_attached hK hclaw hC₀ hQ
  · rw [if_neg hex]
    exact card_evenHoopEvents_eq_zero_of_not_attached Q c
      (fun C h1 h2 h3 => hex ⟨C, h1, h2, h3⟩)

end ClassCounts

/-! ### The literal statement without the hole condition is false -/

namespace HoleAttachmentExample

open Classical in
/-- Counterexample to the package target `card_evenHoopEvents` read literally, with the
right-hand side counting *all* vertex sets of the class `c` that are attached to `Q`
(and not only the even-hole carriers among them).

Take `G = K₂` on `Fin 2`, the simplicial clique `K = {0, 1}` and the root path
`Q = {j*}`.  The vertex set `C = {0, 1}` is attached to `Q` (`j*` has the neighbours
`0 ∼ 1` in `C`), but `G` has no path with four vertices, so there is no wand event at
all: the left-hand side is `0` and the right-hand side is at least `2`.  The point is
that `EvenHoleDeformationClass` is the quotient of *all* sets of vertices, and the class
of a set that is not an even hole is a singleton; the correct statement counts the
even-hole carriers (`card_evenHoopEvents`) or assumes that `c` is a hole class
(`card_evenHoopEvents_of_holeClass`).  `G` is claw-free and `K` is a simplicial
clique. -/
theorem card_evenHoopEvents_literal_false :
    ∃ (G : SimpleGraph (Fin 2)) (K : Set (Fin 2)), G.IsSimplicialClique K ∧ G.IsClawFree ∧
      ∃ (Q : CliqueRootedInducedPath G K) (c : EvenHoleDeformationClass G),
        (Finset.univ.filter fun e : CliqueRootedInducedPath G K × Fin 2 =>
            ∃ w : CliqueBubbleWand G K e.1, w.bubble = e.2 ∧ w.handle = Q ∧
              Even w.hoopCard ∧ G.evenHoleDeformationClassOf w.hoopCarrier = c).card ≠
          2 * (Finset.univ.filter fun C : Set (Fin 2) =>
            G.evenHoleDeformationClassOf C = c ∧ Q.HoleAttached C).card := by
  refine ⟨⊤, Set.univ, ⟨?_, ?_⟩, ?_, cliqueRootPath ⊤ Set.univ,
    (⊤ : SimpleGraph (Fin 2)).evenHoleDeformationClassOf Set.univ, ?_⟩
  · intro x _ y _ hxy
    exact (top_adj x y).2 hxy
  · intro j _
    have : (⊤ : SimpleGraph (Fin 2)).neighborSet j \ Set.univ = ∅ :=
      Set.sdiff_univ _
    rw [this]
    exact Set.pairwise_empty _
  · have key : ∀ a b c : Fin 2, a ≠ b → a ≠ c → b ≠ c → False := by decide
    intro _ a b c _ _ _ hab hac hbc
    exact (key a b c hab hac hbc).elim
  · have hLHS : (Finset.univ.filter fun e : CliqueRootedInducedPath (⊤ : SimpleGraph (Fin 2))
        Set.univ × Fin 2 =>
        ∃ w : CliqueBubbleWand ⊤ Set.univ e.1, w.bubble = e.2 ∧
          w.handle = cliqueRootPath ⊤ Set.univ ∧ Even w.hoopCard ∧
          (⊤ : SimpleGraph (Fin 2)).evenHoleDeformationClassOf w.hoopCarrier =
            (⊤ : SimpleGraph (Fin 2)).evenHoleDeformationClassOf Set.univ).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro e _ ⟨w, -, -, -, -⟩
      have h4 := w.four_le_card
      have hle := Fintype.card_le_of_injective e.1.path.vertex e.1.path.injective
      simp only [Fintype.card_fin, Fintype.card_option] at hle
      omega
    have hRHS : 0 < (Finset.univ.filter fun C : Set (Fin 2) =>
        (⊤ : SimpleGraph (Fin 2)).evenHoleDeformationClassOf C =
          (⊤ : SimpleGraph (Fin 2)).evenHoleDeformationClassOf Set.univ ∧
        (cliqueRootPath ⊤ Set.univ).HoleAttached C).card := by
      apply Finset.card_pos.2
      refine ⟨Set.univ, Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl, ?_, ?_, ?_⟩⟩
      · intro v _ ⟨i, hi⟩
        rw [cliqueRootPath_vertex] at hi
        exact absurd hi (by simp)
      · intro p hp
        change p.val + 1 < 1 at hp
        omega
      · refine ⟨0, 1, Set.mem_univ _, Set.mem_univ _, ?_, ?_⟩
        · exact (top_adj 0 1).2 (by decide)
        · intro v _
          rw [RootedInducedPath.terminalVertex_cliqueRootPath]
          change v ∈ (Set.univ : Set (Fin 2)) ↔ _
          simp only [Set.mem_univ, true_iff]
          fin_cases v <;> simp
    rw [hLHS]
    omega

end HoleAttachmentExample

/-! ### The corrected normalisation sentence -/

section Normalisation

variable [Fintype V] [DecidableEq V] {R : Type w} [Field R]

/-- `m(P, Q, c)`: the number of bubbles `j` realising the arc `P → Q` with an even hoop of
the class `c` (the number of wand events `(P, j)` with handle `Q` and hoop class `c`). -/
noncomputable def cliqueWandBubbleCount (G : SimpleGraph V) (K : Set V)
    (P Q : CliqueRootedInducedPath G K) (c : EvenHoleDeformationClass G) : ℕ := by
  classical
  exact (Finset.univ.filter fun j : V => ∃ w : CliqueBubbleWand G K P,
    w.bubble = j ∧ w.handle = Q ∧ Even w.hoopCard ∧
      G.evenHoleDeformationClassOf w.hoopCarrier = c).card

/-- The normalisation `N_{P,Q,c} = |c| / m(P, Q, c)` of the corrected sentence of v1
L1445, read per bubble event: the sources `P` of a fixed handle `Q` carry the weights
`N_{P,Q,c}^{-1} = m(P, Q, c) / |c|`.  (Over a field; `N = 0` when `m = 0`, which is
consistent with `N⁻¹ = 0` for a non-source.) -/
noncomputable def cliqueEventNormalisation (R : Type w) [Field R] (G : SimpleGraph V)
    (K : Set V) (P Q : CliqueRootedInducedPath G K) (c : EvenHoleDeformationClass G) : R :=
  (evenHoleClassSize c : R) / (cliqueWandBubbleCount G K P Q c : R)

open Classical in
omit [DecidableEq V] in
/-- The number of events with handle `Q` and hoop class `c` is the sum over the sources
`P` of the number of bubbles. -/
theorem card_evenHoopEvents_eq_sum (Q : CliqueRootedInducedPath G K)
    (c : EvenHoleDeformationClass G) :
    (Finset.univ.filter fun e : CliqueRootedInducedPath G K × V =>
        ∃ w : CliqueBubbleWand G K e.1, w.bubble = e.2 ∧ w.handle = Q ∧
          Even w.hoopCard ∧ G.evenHoleDeformationClassOf w.hoopCarrier = c).card =
      ∑ P : CliqueRootedInducedPath G K, cliqueWandBubbleCount G K P Q c := by
  rw [Finset.card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun P _ => ?_
  unfold cliqueWandBubbleCount
  rw [Finset.card_filter]

omit [DecidableEq V] in
/-- In a claw-free graph the bubbles of one arc `P → Q` all realise hoops of one class
(`CliqueBubbleWand.evenHoleDeformationClassOf_hoopCarrier_eq`), so the number
`m(P, Q, c)` of the normalisation is the number `m(P, Q)` of all bubbles realising the
arc, as used in `cliqueHoppingMatrix_hoop`, as soon as the arc has an event of class
`c`. -/
theorem cliqueWandBubbleCount_eq_card (hclaw : G.IsClawFree)
    {P Q : CliqueRootedInducedPath G K} {c : EvenHoleDeformationClass G}
    (h : ∃ w : CliqueBubbleWand G K P, w.handle = Q ∧ Even w.hoopCard ∧
      G.evenHoleDeformationClassOf w.hoopCarrier = c) :
    cliqueWandBubbleCount G K P Q c =
      Nat.card {j : V // ∃ w' : CliqueBubbleWand G K P, w'.bubble = j ∧ w'.handle = Q} := by
  classical
  obtain ⟨w, hh, hev, hcl⟩ := h
  unfold cliqueWandBubbleCount
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  apply Finset.filter_congr
  intro j _
  constructor
  · rintro ⟨w', hb, hh', -, -⟩
    exact ⟨w', hb, hh'⟩
  · rintro ⟨w', hb, hh'⟩
    have hh2 : w'.handle = w.handle := hh'.trans hh.symm
    have hev' : Even w'.hoopCard :=
      (CliqueBubbleWand.hoopCard_eq_of_handle_eq w w' hh2.symm) ▸ hev
    refine ⟨w', hb, hh', hev', ?_⟩
    rw [← hcl]
    exact (CliqueBubbleWand.evenHoleDeformationClassOf_hoopCarrier_eq hclaw w w' hh2.symm
      hev).symm

open Classical in
/-- (iii) The corrected normalisation sentence (v1 L1445).  If an even hole `C₀` is
attached to `Q`, then, summing over the sources `P` of the handle `Q`,
`(1/2) Σ_P N_{P,Q,c}^{-1} = 1` with `N_{P,Q,c} = |c| / m(P, Q, c)` and `c = ⟨C₀⟩`.  The
factor `2` counts the two directions around a hole; the printed version, read with a
fixed source and a sum over the targets, is wrong (see `CliqueHoppingMatrix.lean`). -/
theorem half_sum_inv_eventNormalisation_of_attached [CharZero R]
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree)
    {Q : CliqueRootedInducedPath G K} {C₀ : Set V} (hC₀ : G.IsEvenHoleCarrier C₀)
    (hQ : Q.HoleAttached C₀) :
    (1 / 2 : R) * ∑ P ∈ Finset.univ.filter (fun P : CliqueRootedInducedPath G K =>
        0 < cliqueWandBubbleCount G K P Q (G.evenHoleDeformationClassOf C₀)),
      (cliqueEventNormalisation R G K P Q (G.evenHoleDeformationClassOf C₀))⁻¹ = 1 := by
  set c := G.evenHoleDeformationClassOf C₀ with hc
  have hsize : (evenHoleClassSize c : R) ≠ 0 :=
    Nat.cast_ne_zero.2 (evenHoleClassSize_pos c).ne'
  have hevents := card_evenHoopEvents_of_attached hK hclaw hC₀ hQ
  rw [card_evenHoopEvents_eq_sum] at hevents
  have hsum : (∑ P : CliqueRootedInducedPath G K, (cliqueWandBubbleCount G K P Q c : R)) =
      2 * (evenHoleClassSize c : R) := by
    exact_mod_cast hevents
  have hterm : ∀ P : CliqueRootedInducedPath G K,
      (cliqueEventNormalisation R G K P Q c)⁻¹ =
        (cliqueWandBubbleCount G K P Q c : R) / (evenHoleClassSize c : R) := by
    intro P
    unfold cliqueEventNormalisation
    rw [inv_div]
  rw [Finset.sum_congr rfl (fun P _ => hterm P), Finset.sum_filter]
  have hzero : ∀ P : CliqueRootedInducedPath G K,
      (if 0 < cliqueWandBubbleCount G K P Q c then
        (cliqueWandBubbleCount G K P Q c : R) / (evenHoleClassSize c : R) else 0) =
      (cliqueWandBubbleCount G K P Q c : R) / (evenHoleClassSize c : R) := by
    intro P
    split_ifs with h
    · rfl
    · have : cliqueWandBubbleCount G K P Q c = 0 := by omega
      rw [this]
      simp
  rw [Finset.sum_congr rfl (fun P _ => hzero P)]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, hsum, one_mul, mul_assoc (2 : R) _ _, mul_inv_cancel₀ hsize,
    mul_one, inv_mul_cancel₀ two_ne_zero]

open Classical in
/-- If no even hole of `c` is attached to `Q`, every source weight vanishes:
there are no events and the normalised sum is `0`. -/
theorem sum_inv_eventNormalisation_eq_zero_of_not_attached
    (Q : CliqueRootedInducedPath G K) (c : EvenHoleDeformationClass G)
    (h : ∀ C : Set V, G.IsEvenHoleCarrier C → G.evenHoleDeformationClassOf C = c →
      ¬ Q.HoleAttached C) :
    ∑ P : CliqueRootedInducedPath G K, (cliqueEventNormalisation R G K P Q c)⁻¹ = 0 := by
  have hevents := card_evenHoopEvents_eq_zero_of_not_attached Q c h
  rw [card_evenHoopEvents_eq_sum, Finset.sum_eq_zero_iff] at hevents
  apply Finset.sum_eq_zero
  intro P _
  unfold cliqueEventNormalisation
  rw [hevents P (Finset.mem_univ P)]
  simp

end Normalisation

/-! ### The hoop part of the matrix `A_λ`, class by class -/

section HoopPart

variable [Fintype V] [DecidableEq V] {R : Type w} [Field R]

/-- The part of the third case (the even-hoop part) of the entry `A_λ(P, Q)` of
`cliqueHoppingMatrix` that comes from the hoops of the class `c`: the sum, over the
bubbles `j` realising the arc `P → Q` with an even hoop of the class `c`, of
`(-1)^(k-1) λ_c / |c|`, where `2k` is the size of the hoop carrier.  The entry of
`cliqueHoppingMatrix` is the tree entry plus the sum of these parts over all classes
(`cliqueHoppingMatrix_eq_tree_add_sum_hoopPart`). -/
noncomputable def cliqueHoppingHoopPart (G : SimpleGraph V) (K : Set V)
    (lam : EvenHoleDeformationClass G → R) (c : EvenHoleDeformationClass G)
    (P Q : CliqueRootedInducedPath G K) : R := by
  classical
  exact ∑ j : V,
    if ∃ w : CliqueBubbleWand G K P, w.bubble = j ∧ w.handle = Q ∧ Even w.hoopCard ∧
        G.evenHoleDeformationClassOf w.hoopCarrier = c then
      (-1 : R) ^ ((bubbleWandArcHoopCarrier P Q j).ncard / 2 - 1) * lam c /
        (evenHoleClassSize c : R)
    else 0

omit [Fintype V] [DecidableEq V] in
/-- The hoop carrier determined by a wand event is the carrier `bubbleWandArcHoopCarrier`
of its arc. -/
theorem bubbleWandArcHoopCarrier_eq_hoopCarrier {P Q : CliqueRootedInducedPath G K}
    {j : V} (w : CliqueBubbleWand G K P) (hb : w.bubble = j) (hh : w.handle = Q) :
    bubbleWandArcHoopCarrier P Q j = w.hoopCarrier := by
  unfold CliqueBubbleWand.hoopCarrier
  rw [hh, hb]

/-- The hoop part is the number of bubbles times the weight `(-1)^(k_c-1) λ_c / |c|`
of one event of the class `c`; the half-length `k_c` is a function of the class
(`evenHoleClassHalfLength`). -/
theorem cliqueHoppingHoopPart_eq (lam : EvenHoleDeformationClass G → R)
    (c : EvenHoleDeformationClass G) (P Q : CliqueRootedInducedPath G K) :
    cliqueHoppingHoopPart G K lam c P Q =
      (cliqueWandBubbleCount G K P Q c : R) *
        ((-1 : R) ^ (evenHoleClassHalfLength c - 1) * lam c / (evenHoleClassSize c : R)) := by
  classical
  unfold cliqueHoppingHoopPart cliqueWandBubbleCount
  set S : R := (-1 : R) ^ (evenHoleClassHalfLength c - 1) * lam c / (evenHoleClassSize c : R)
    with hS
  have hterm : ∀ j : V,
      (if ∃ w : CliqueBubbleWand G K P, w.bubble = j ∧ w.handle = Q ∧ Even w.hoopCard ∧
          G.evenHoleDeformationClassOf w.hoopCarrier = c then
        (-1 : R) ^ ((bubbleWandArcHoopCarrier P Q j).ncard / 2 - 1) * lam c /
          (evenHoleClassSize c : R)
       else 0) =
      if ∃ w : CliqueBubbleWand G K P, w.bubble = j ∧ w.handle = Q ∧ Even w.hoopCard ∧
          G.evenHoleDeformationClassOf w.hoopCarrier = c then S else 0 := by
    intro j
    by_cases hj : ∃ w : CliqueBubbleWand G K P, w.bubble = j ∧ w.handle = Q ∧
        Even w.hoopCard ∧ G.evenHoleDeformationClassOf w.hoopCarrier = c
    · obtain ⟨w, hb, hh, hev, hcl⟩ := hj
      rw [if_pos ⟨w, hb, hh, hev, hcl⟩, if_pos ⟨w, hb, hh, hev, hcl⟩]
      have hk : (bubbleWandArcHoopCarrier P Q j).ncard / 2 = evenHoleClassHalfLength c := by
        rw [bubbleWandArcHoopCarrier_eq_hoopCarrier w hb hh, ← hcl,
          evenHoleClassHalfLength_classOf]
      rw [hk]
    · rw [if_neg hj, if_neg hj]
  rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul]

/-- The entry of `A_λ` is the tree entry plus the hoop parts of all classes. -/
theorem cliqueHoppingMatrix_eq_tree_add_sum_hoopPart [Fintype (EvenHoleDeformationClass G)]
    (b : V → R) (lam : EvenHoleDeformationClass G → R)
    (P Q : CliqueRootedInducedPath G K) :
    cliqueHoppingMatrix G K b lam P Q =
      cliqueTreeMatrix G K b P Q +
        ∑ c : EvenHoleDeformationClass G, cliqueHoppingHoopPart G K lam c P Q := by
  classical
  unfold cliqueHoppingMatrix cliqueHoppingHoopPart
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : ∃ w : CliqueBubbleWand G K P, w.bubble = j ∧ w.handle = Q ∧
      Even w.hoopCard
  · obtain ⟨w, hb, hh, hev⟩ := hj
    have hcar := bubbleWandArcHoopCarrier_eq_hoopCarrier w hb hh
    -- the event is determined by its bubble, so exactly one class occurs
    have hpred : ∀ c : EvenHoleDeformationClass G,
        (∃ w' : CliqueBubbleWand G K P, w'.bubble = j ∧ w'.handle = Q ∧
          Even w'.hoopCard ∧ G.evenHoleDeformationClassOf w'.hoopCarrier = c) ↔
          G.evenHoleDeformationClassOf w.hoopCarrier = c := by
      intro c
      constructor
      · rintro ⟨w', hb', -, -, hcl⟩
        have : w' = w := CliqueBubbleWand.ext_of_bubble_eq w' w (hb'.trans hb.symm)
        rw [← this]
        exact hcl
      · intro hcl
        exact ⟨w, hb, hh, hev, hcl⟩
    rw [if_pos ⟨w, hb, hh, hev⟩]
    rw [Finset.sum_congr rfl (fun c _ => if_congr (hpred c) rfl rfl)]
    rw [Finset.sum_ite_eq Finset.univ (G.evenHoleDeformationClassOf w.hoopCarrier)]
    rw [if_pos (Finset.mem_univ _), hcar]
  · rw [if_neg hj]
    refine (Finset.sum_eq_zero fun c _ => ?_).symm
    rw [if_neg]
    rintro ⟨w, hb, hh, hev, -⟩
    exact hj ⟨w, hb, hh, hev⟩

open Classical in
/-- The column total of the hoop part, class by class (v1 L1555-1576, with the
corrected normalisation): summing the hoop part of `A_λ(P, Q)` of the class `c` over all
sources `P` gives `2 (-1)^{k_c-1} λ_c` if some even hole of `c` is attached to `Q`
(and then every hole of `c` is, by claim (i)), and `0` otherwise.  The factor `2` is the
two directions around each hole and the weights `λ_c / |c|` per event sum over the
`|c|` holes of the class. -/
theorem cliqueHoppingMatrix_column_hoop_total [CharZero R]
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree)
    (lam : EvenHoleDeformationClass G → R) (Q : CliqueRootedInducedPath G K)
    (c : EvenHoleDeformationClass G) :
    ∑ P : CliqueRootedInducedPath G K, cliqueHoppingHoopPart G K lam c P Q =
      if ∃ C : Set V, G.IsEvenHoleCarrier C ∧ G.evenHoleDeformationClassOf C = c ∧
          Q.HoleAttached C then
        2 * (-1 : R) ^ (evenHoleClassHalfLength c - 1) * lam c
      else 0 := by
  simp only [cliqueHoppingHoopPart_eq]
  rw [← Finset.sum_mul]
  have hsize : (evenHoleClassSize c : R) ≠ 0 :=
    Nat.cast_ne_zero.2 (evenHoleClassSize_pos c).ne'
  have hsum := card_evenHoopEvents_eq_sum Q c
  by_cases hex : ∃ C : Set V, G.IsEvenHoleCarrier C ∧ G.evenHoleDeformationClassOf C = c ∧
      Q.HoleAttached C
  · rw [if_pos hex]
    obtain ⟨C₀, hC₀, rfl, hQ⟩ := hex
    have hevents := card_evenHoopEvents_of_attached hK hclaw hC₀ hQ
    rw [hsum] at hevents
    have hcast : (∑ P : CliqueRootedInducedPath G K,
        (cliqueWandBubbleCount G K P Q (G.evenHoleDeformationClassOf C₀) : R)) =
        2 * (evenHoleClassSize (G.evenHoleDeformationClassOf C₀) : R) := by
      exact_mod_cast hevents
    rw [hcast]
    calc 2 * (evenHoleClassSize (G.evenHoleDeformationClassOf C₀) : R) *
          ((-1 : R) ^ (evenHoleClassHalfLength (G.evenHoleDeformationClassOf C₀) - 1) *
            lam (G.evenHoleDeformationClassOf C₀) /
            (evenHoleClassSize (G.evenHoleDeformationClassOf C₀) : R))
        = 2 * ((-1 : R) ^ (evenHoleClassHalfLength (G.evenHoleDeformationClassOf C₀) - 1) *
            lam (G.evenHoleDeformationClassOf C₀)) *
          ((evenHoleClassSize (G.evenHoleDeformationClassOf C₀) : R) *
            (evenHoleClassSize (G.evenHoleDeformationClassOf C₀) : R)⁻¹) := by
          rw [div_eq_mul_inv]
          ring
      _ = 2 * (-1 : R) ^ (evenHoleClassHalfLength (G.evenHoleDeformationClassOf C₀) - 1) *
            lam (G.evenHoleDeformationClassOf C₀) := by
          rw [mul_inv_cancel₀ (by exact_mod_cast hsize), mul_one]
          ring
  · rw [if_neg hex]
    have hnone : ∀ C : Set V, G.IsEvenHoleCarrier C → G.evenHoleDeformationClassOf C = c →
        ¬ Q.HoleAttached C := fun C h1 h2 h3 => hex ⟨C, h1, h2, h3⟩
    have hzero := card_evenHoopEvents_eq_zero_of_not_attached Q c hnone
    rw [hsum] at hzero
    have hnat : (∑ P : CliqueRootedInducedPath G K,
        (cliqueWandBubbleCount G K P Q c : R)) = 0 := by
      exact_mod_cast hzero
    rw [hnat, zero_mul]

end HoopPart

/-! ### A worked example: the 4-cycle with an edge clique

For the 4-cycle `0 - 1 - 2 - 3 - 0` with `K = {0, 1}` (`CliqueBubbleWand.Example`) the
whole vertex set is a hole attached to the root path `{j*}`: the root is adjacent to the
edge `{0, 1}` of the hole.  There are exactly `2 |c| = 2` wand events with the root handle:
the wand `(j*, 0, 3, 2)` with bubble `1` of `CliqueBubbleWand.Example.wand`, and its
reversal `(j*, 1, 2, 3)` with bubble `0`.  The column total of the hoop part of `A_λ` is
`2 (-1)^{2-1} λ = -2 λ`; each of the two sources contributes the entry `-λ` of
`CliqueBubbleWand.Example.hopping_root_entry`. -/

namespace HoleAttachmentExample

open CliqueBubbleWand.Example

theorem fourCycle_isSimplicialClique : fourCycle.IsSimplicialClique edgeClique := by
  refine ⟨?_, ?_⟩
  · have key : ∀ x y : Fin 4, (x = 0 ∨ x = 1) → (y = 0 ∨ y = 1) → x ≠ y →
        fourCycle.Adj x y := by decide
    intro x hx y hy hxy
    exact key x y hx hy hxy
  · have key : ∀ j x y : Fin 4, (j = 0 ∨ j = 1) → fourCycle.Adj j x → ¬ (x = 0 ∨ x = 1) →
        fourCycle.Adj j y → ¬ (y = 0 ∨ y = 1) → x ≠ y → fourCycle.Adj x y := by decide
    intro j hj x hx y hy hxy
    exact key j x y hj hx.1 hx.2 hy.1 hy.2 hxy

/-- The whole vertex set of the 4-cycle is an even hole carrier. -/
theorem fourCycle_isEvenHoleCarrier : fourCycle.IsEvenHoleCarrier Set.univ :=
  ⟨wand.hoopHole, by rw [wand.hoopHole_card]; decide,
    by rw [wand.range_hoopHole]; exact wand_hoopCarrier⟩

/-- The whole vertex set is attached to the root path `{j*}`. -/
theorem fourCycle_holeAttached :
    (cliqueRootPath fourCycle edgeClique).HoleAttached Set.univ := by
  refine ⟨?_, ?_, 0, 1, Set.mem_univ _, Set.mem_univ _, ?_, ?_⟩
  · intro v _ ⟨i, hi⟩
    rw [cliqueRootPath_vertex] at hi
    exact absurd hi (by simp)
  · intro p hp
    change p.val + 1 < 1 at hp
    omega
  · decide
  · intro v _
    rw [RootedInducedPath.terminalVertex_cliqueRootPath]
    change v ∈ edgeClique ↔ _
    simp [edgeClique]

open Classical in
/-- There are exactly two wand events with the root handle for the 4-cycle. -/
theorem fourCycle_card_events :
    (Finset.univ.filter fun e : CliqueRootedInducedPath fourCycle edgeClique × Fin 4 =>
        ∃ w : CliqueBubbleWand fourCycle edgeClique e.1, w.bubble = e.2 ∧
          w.handle = cliqueRootPath fourCycle edgeClique ∧ Even w.hoopCard ∧
          fourCycle.evenHoleDeformationClassOf w.hoopCarrier =
            fourCycle.evenHoleDeformationClassOf Set.univ).card = 2 := by
  rw [card_evenHoopEvents_of_attached fourCycle_isSimplicialClique fourCycle_isClawFree
    fourCycle_isEvenHoleCarrier fourCycle_holeAttached, classSize_univ]

open Classical in
/-- The column total of the hoop part for the 4-cycle is `-2 λ`. -/
theorem fourCycle_column_hoop_total {R : Type} [Field R] [CharZero R]
    (lam : EvenHoleDeformationClass fourCycle → R) :
    ∑ P : CliqueRootedInducedPath fourCycle edgeClique,
        cliqueHoppingHoopPart fourCycle edgeClique lam
          (fourCycle.evenHoleDeformationClassOf Set.univ) P
          (cliqueRootPath fourCycle edgeClique) =
      -2 * lam (fourCycle.evenHoleDeformationClassOf Set.univ) := by
  rw [cliqueHoppingMatrix_column_hoop_total fourCycle_isSimplicialClique
    fourCycle_isClawFree, if_pos ⟨Set.univ, fourCycle_isEvenHoleCarrier, rfl,
      fourCycle_holeAttached⟩, evenHoleClassHalfLength_classOf]
  have h4 : (Set.univ : Set (Fin 4)).ncard = 4 := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [h4]
  norm_num

end HoleAttachmentExample

end SimpleGraph
