import FreeFermionGraphs.T3BlockStep
import FreeFermionGraphs.T3PairingIndexCount
import FreeFermionGraphs.Neighboring
import FreeFermionGraphs.SymmDiffComponentToggle

/-!
# The separator lemma: the separators of a good source lie in one component

This module proves the *separator lemma* of the synthesised proof of Theorem 1(iii) of arXiv
2305.15625 v1 (label `theorem:conservedcharges`), package T3-22.  It has no counterpart in v1: it
replaces the search-history argument of v1 Lemma 8 (iii)-(iv) and Lemma 9 ("`j''` is the only
member of exactly one of `U_j`, `U_{j'}`", L1174-1189, proved in the appendix at L1843-1921) by a
purely local statement about one oriented block.

## Setting

`G` is claw-free, `s = (A, B)` and `s' = (A', B')` are hole-class states (the colouring classes of
the even holes `C = A ∪ B` and `C' = A' ∪ B'`), and `Q : OddBlock A A'` is a side-1 block, i.e. an
induced path `j_0 k_0 j_1 k_1 … j_{ℓ-1} k_{ℓ-1}` with `j_t ∈ A' ∖ A`, `k_t ∈ A ∖ A'`, which is a
whole component of `G[A ⊕ A']`, and which *runs from `s`* (its word is a clone run out of `s`,
`OddBlock.RunsFrom`).  A *separator* of `Q` in `B'` is a vertex `v ∈ B'` which obstructs a step
`(j_t, k_t)`, i.e. `v = k_t` or `v` is adjacent to exactly one of `j_t`, `k_t`
(`OddBlock.separators`).  Write `m' = |Q ∩ matchedW s' s|` and `x' = |Q ∩ crossedW s' s|`: the
number of vertices of `Q` that are matched, resp. crossed, clones in `C'`.

## Main results

* `SimpleGraph.OddBlock.separators_sameComponent` (package T3-22): if the `W'`-content of `Q` is
  balanced, `(m', x') ∈ {(0,0), (1,1)}`, then any two separators of `Q` in `s'.2` lie in the same
  component of `G[s.2 ⊕ s'.2]`.
* `SimpleGraph.OddBlock.separators_components_le` (the general bound): for every forward-running
  `Q` (any key) the separators of `Q` in `s'.2` are connected, inside `G[s.2 ⊕ s'.2]`, to the
  members of a set `R` of *root separators* with `|R| + m' ≤ 1 + x'`.  In particular they meet at
  most `1 - m' + x'` components of `G[s.2 ⊕ s'.2]`.
* `SimpleGraph.OddBlock.separators_snd_subset_symmDiff`: the separators avoid `s.2`, so they are
  vertices of `G[s.2 ⊕ s'.2]`.
* `SimpleGraph.OddBlock.exists_separatorData`: the bridge from a block of hole-class states which
  runs from `s` to the abstract local data `SimpleGraph.SeparatorData`.

## Abstract core

`SimpleGraph.SeparatorData` records only the local facts used by the argument: independence and
disjointness of the four classes, "every vertex of `A`, `A'`, `B'` has exactly two hole neighbours
in the opposite class", the induced-path facts about `Q` (its `A'`-neighbours, which uses that the
support is a component), and the forward conditions of `OddBlock.classRun_iff`
(`j_t ∉ B` and `Γ_B(j_t) = Γ_B(k_t)`).  No field assumes a conclusion: each field is derived from
the hole-class and block hypotheses in `OddBlock.exists_separatorData`.  The proof is a chain of
local claw arguments, each of which is a use of v1 Corollary 2 (`corollary2_hole_neighbor`) or a
direct claw exclusion at one named vertex:

* `SeparatorData.sepAt_notB`: the separators avoid `B`.
* `SeparatorData.jsep_unique`, `ksep_unique`, `exists_common`: the shape of the separators of one
  step.
* `SeparatorData.comp_JK`: the separators of one step lie in one component of `G[B ⊕ B']`.
* `SeparatorData.handoff`: the `k`-type separator of a step reappears as a `j`-type separator of
  the step `t + 1` or `t + 2`.
* `SeparatorData.chain`: hence every separator is connected to the `j`-type separator of a step
  with no `k`-type separator (a type-1 step).
* `SeparatorData.type1_unbal`, `not_matched_of_lt`, `card_unbal_add_le`: a type-1 step is
  *unbalanced*, i.e. its removed vertex `k_t` is a crossed clone in `C'` (`t < ℓ - 1`) or is not a
  matched clone (`t = ℓ - 1`); only the last removed vertex can be a matched clone; so there are
  at most `1 - m' + x'` unbalanced steps.
* `SeparatorData.exists_roots`: the separators are connected to a set of roots (one `j`-type
  separator per unbalanced step), so there are at most as many roots as unbalanced steps, i.e. at
  most `1 - m' + x'`.

## Corrections to the work package

* The package's structural remark "consecutive `δ`'s share a neighbour in `s.2 ∖ s'.2`" is false,
  and is not claimed: the two separators of one step may need a path of length `4` through the two
  `C`-neighbours of `k_t` and a vertex `b ∈ N(j_t) ∩ N(k_t) ∩ B'` (`SeparatorData.comp_JK`).  A
  12-vertex claw-free counterexample (two 6-holes) was found by exhaustive search.  What is proved
  is that the separators of one step lie in one component, which is all that is needed.
* The goodness hypothesis `hW'` is essential: exhaustive search found blocks with key `(0, 1)`
  whose separators lie in two components of `G[s.2 ⊕ s'.2]`.  The general bound
  `separators_components_le` is what remains true for every key.

Claw-freeness enters only through `IsClawFree.adjacent_to_one_of_nonadjacent_neighbors` and the
direct claw exclusions in `SeparatorData.ksep_unique`, `handoff` and `link_K`.  `Fintype V` is not
needed.
-/

open scoped symmDiff

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- Local data of a forward-running side block against two hole-class pairs: the hole-class
states `(A, B)`, `(A', B')` and the block `Q = j_0 k_0 … j_{ℓ-1} k_{ℓ-1}` of `G[A ⊕ A']` (as
functions `j, k : ℕ → V`, read on `t < ℓ`).  Only the facts used by the separator lemma are
recorded; `OddBlock.exists_separatorData` produces such data from a block that runs from a
hole-class state. -/
structure SeparatorData (G : SimpleGraph V) where
  /-- first colouring class of the first hole -/
  A : Set V
  /-- second colouring class of the first hole -/
  B : Set V
  /-- first colouring class of the second hole -/
  A' : Set V
  /-- second colouring class of the second hole -/
  B' : Set V
  /-- the number of steps of the block -/
  l : ℕ
  /-- the introduced vertices `j_t` -/
  j : ℕ → V
  /-- the removed vertices `k_t` -/
  k : ℕ → V
  indepA : ∀ ⦃x y⦄, x ∈ A → y ∈ A → ¬G.Adj x y
  indepB : ∀ ⦃x y⦄, x ∈ B → y ∈ B → ¬G.Adj x y
  indepA' : ∀ ⦃x y⦄, x ∈ A' → y ∈ A' → ¬G.Adj x y
  indepB' : ∀ ⦃x y⦄, x ∈ B' → y ∈ B' → ¬G.Adj x y
  disjAB : ∀ ⦃x⦄, x ∈ A → x ∉ B
  disjA'B' : ∀ ⦃x⦄, x ∈ A' → x ∉ B'
  /-- a vertex of `A'` has exactly two hole neighbours, both in `B'` -/
  nbrA' : ∀ x ∈ A', ∃ u w, u ≠ w ∧ u ∈ B' ∧ w ∈ B' ∧ ∀ y ∈ B', (G.Adj x y ↔ y = u ∨ y = w)
  /-- a vertex of `B'` has exactly two hole neighbours, both in `A'` -/
  nbrB' : ∀ x ∈ B', ∃ u w, u ≠ w ∧ u ∈ A' ∧ w ∈ A' ∧ ∀ y ∈ A', (G.Adj x y ↔ y = u ∨ y = w)
  /-- a vertex of `A` has exactly two hole neighbours, both in `B` -/
  nbrA : ∀ x ∈ A, ∃ u w, u ≠ w ∧ u ∈ B ∧ w ∈ B ∧ ∀ y ∈ B, (G.Adj x y ↔ y = u ∨ y = w)
  j_memA' : ∀ t < l, j t ∈ A'
  k_memA : ∀ t < l, k t ∈ A
  k_notA' : ∀ t < l, k t ∉ A'
  j_inj : ∀ t < l, ∀ t' < l, j t = j t' → t = t'
  k_inj : ∀ t < l, ∀ t' < l, k t = k t' → t = t'
  adj_kj : ∀ t < l, G.Adj (k t) (j t)
  adj_kj_succ : ∀ t, t + 1 < l → G.Adj (k t) (j (t + 1))
  /-- the `A'`-neighbours of `k t` are `j t` and `j (t+1)` (component + induced path) -/
  nbrA'_k : ∀ t < l, ∀ a ∈ A', G.Adj (k t) a → a = j t ∨ (t + 1 < l ∧ a = j (t + 1))
  /-- forward running (`OddBlock.classRun_iff`): `j_t ∉ B` -/
  fwd_notB : ∀ t < l, j t ∉ B
  /-- forward running (`OddBlock.classRun_iff`): `Γ_B(j_t) = Γ_B(k_t)` -/
  fwd_adj : ∀ t < l, ∀ v ∈ B, (G.Adj (j t) v ↔ G.Adj (k t) v)

namespace SeparatorData

variable (D : SeparatorData G)

/-- The *`j`-type separators* of step `t`: the vertices `v ∈ B'`, different from `k_t`, which are
adjacent to `j_t` but not to `k_t`. -/
def JSep (t : ℕ) (v : V) : Prop :=
  v ∈ D.B' ∧ v ≠ D.k t ∧ G.Adj (D.j t) v ∧ ¬G.Adj (D.k t) v

/-- The *`k`-type separators* of step `t`: the vertices `v ∈ B'` which are adjacent to `k_t` but not
to `j_t`, and the removed vertex `k_t` itself when it lies in `B'`. -/
def KSep (t : ℕ) (v : V) : Prop :=
  v ∈ D.B' ∧ ((G.Adj (D.k t) v ∧ ¬G.Adj (D.j t) v) ∨ v = D.k t)

/-- The separators of step `t`: the `j`-type and the `k`-type ones. -/
def SepAt (t : ℕ) (v : V) : Prop := D.JSep t v ∨ D.KSep t v

/-- The separators of the block in `B'`, in the form of `OddBlock.IsSeparator`: `v ∈ B'` with
`v = k_t`, or `v ≠ j_t, k_t` adjacent to exactly one of `j_t`, `k_t`, for some step `t`. -/
def Sep (v : V) : Prop :=
  v ∈ D.B' ∧ ∃ t < D.l, v = D.k t ∨ (v ≠ D.j t ∧ v ≠ D.k t ∧ ¬(G.Adj (D.j t) v ↔ G.Adj (D.k t) v))

/-- Step `t` is of *type 1* if it has a `j`-type separator and no `k`-type separator.  Its
`j`-type separator is then unique (`jsep_unique`); it is the *root* of the step. -/
def Type1 (t : ℕ) : Prop := (∃ v, D.JSep t v) ∧ ∀ v, ¬D.KSep t v

/-- The removed vertex `k_t` is a clone, in the hole `C' = A' ∪ B'`, of a vertex of `A'`
(`k_t ∈ matchedW s' s`, see `OddBlock.exists_separatorData`). -/
def Matched (t : ℕ) : Prop := ∃ x ∈ D.A', G.IsCloneIn (D.A' ∪ D.B') (D.k t) x
/-- The removed vertex `k_t` is a clone, in the hole `C' = A' ∪ B'`, of a vertex of `B'`
(`k_t ∈ crossedW s' s`, see `OddBlock.exists_separatorData`). -/
def Crossed (t : ℕ) : Prop := ∃ x ∈ D.B', G.IsCloneIn (D.A' ∪ D.B') (D.k t) x

/-- Step `t` is *unbalanced*: it carries a vertex of `W'` that is not paired off, i.e. it is the
last step and `k_t` is not a matched clone, or it is an interior step and `k_t` is a crossed
clone.  Type-1 steps are unbalanced (`type1_unbal`), and there are `1 - m' + x'` unbalanced steps
(`card_unbal_add_le`). -/
def Unbal (t : ℕ) : Prop :=
  (t + 1 = D.l ∧ ¬D.Matched t) ∨ (t + 1 < D.l ∧ D.Crossed t)

/-- The component of `u` in the side graph `G[B ⊕ B']`. -/
def Comp (u : V) : Set V := G.inducedComponentSet (D.B ∆ D.B') u

/-! ### Component bookkeeping -/

theorem comp_self {u : V} (hu : u ∈ D.B ∆ D.B') : u ∈ D.Comp u :=
  ⟨hu, hu, Reachable.refl _⟩

theorem comp_adj {u w x : V} (hw : w ∈ D.Comp u) (hx : x ∈ D.B ∆ D.B') (hwx : G.Adj w x) :
    x ∈ D.Comp u := by
  obtain ⟨hu, hw', hr⟩ := hw
  exact ⟨hu, hx, hr.trans (Adj.reachable (by simpa using hwx))⟩

theorem comp_symm {u w : V} (hw : w ∈ D.Comp u) : u ∈ D.Comp w := by
  obtain ⟨hu, hw', hr⟩ := hw
  exact ⟨hw', hu, hr.symm⟩

theorem comp_trans {u w x : V} (hw : w ∈ D.Comp u) (hx : x ∈ D.Comp w) : x ∈ D.Comp u := by
  obtain ⟨hu, hw', hr⟩ := hw
  obtain ⟨hw'', hx', hr'⟩ := hx
  exact ⟨hu, hx', hr.trans hr'⟩

theorem mem_symmDiff_of_B' {v : V} (hv : v ∈ D.B') (hvB : v ∉ D.B) : v ∈ D.B ∆ D.B' :=
  Set.mem_symmDiff.mpr (Or.inr ⟨hv, hvB⟩)

theorem mem_symmDiff_of_B {g v : V} (hg : g ∈ D.B) (hv : v ∈ D.B') (hgv : G.Adj g v) :
    g ∈ D.B ∆ D.B' :=
  Set.mem_symmDiff.mpr (Or.inl ⟨hg, fun hg' => D.indepB' hg' hv hgv⟩)

/-! ### Elementary facts -/

theorem k_notB {t : ℕ} (ht : t < D.l) : D.k t ∉ D.B := D.disjAB (D.k_memA t ht)

theorem j_ne_of_B' {t : ℕ} (ht : t < D.l) {v : V} (hv : v ∈ D.B') : v ≠ D.j t := by
  rintro rfl; exact D.disjA'B' (D.j_memA' t ht) hv

theorem k_ne_of_A' {t : ℕ} (ht : t < D.l) {a : V} (ha : a ∈ D.A') : D.k t ≠ a := by
  rintro rfl; exact D.k_notA' t ht ha

/-- From "exactly two neighbours `u, w` in `S`" and two distinct neighbours `b, p` in `S`,
every neighbour in `S` is `b` or `p`. -/
theorem two_nbrs {x u w b p : V} {S : Set V}
    (hS : ∀ y ∈ S, (G.Adj x y ↔ y = u ∨ y = w)) (hb : b ∈ S) (hp : p ∈ S)
    (hxb : G.Adj x b) (hxp : G.Adj x p) (hbp : b ≠ p) :
    ∀ y ∈ S, G.Adj x y → y = b ∨ y = p := by
  intro y hy hxy
  have hb' := (hS b hb).1 hxb
  have hp' := (hS p hp).1 hxp
  have hy' := (hS y hy).1 hxy
  rcases hb' with rfl | rfl <;> rcases hp' with rfl | rfl <;> rcases hy' with rfl | rfl <;>
    simp_all

/-- The separators of a step avoid `B`: for `v ∈ B` the forward condition `Γ_B(j_t) = Γ_B(k_t)`
says that `v` is adjacent to both or neither of `j_t`, `k_t`, and `k_t ∉ B`. -/
theorem sepAt_notB {t : ℕ} (ht : t < D.l) {v : V} (hv : D.SepAt t v) : v ∉ D.B := by
  intro hvB
  have hiff := D.fwd_adj t ht v hvB
  rcases hv with ⟨_, _, hj, hk⟩ | ⟨_, ⟨hk, hj⟩ | rfl⟩
  · exact hk (hiff.1 hj)
  · exact hj (hiff.2 hk)
  · exact D.k_notB ht hvB

theorem sepAt_mem {t : ℕ} (ht : t < D.l) {v : V} (hv : D.SepAt t v) : v ∈ D.B ∆ D.B' := by
  have hvB' : v ∈ D.B' := by rcases hv with h | h <;> exact h.1
  exact D.mem_symmDiff_of_B' hvB' (D.sepAt_notB ht hv)

/-- `Sep` is the union of the step sets. -/
theorem sep_iff {v : V} : D.Sep v ↔ ∃ t < D.l, D.SepAt t v := by
  constructor
  · rintro ⟨hv, t, ht, h | ⟨hvj, hvk, hiff⟩⟩
    · exact ⟨t, ht, Or.inr ⟨hv, Or.inr h⟩⟩
    · refine ⟨t, ht, ?_⟩
      by_cases hj : G.Adj (D.j t) v
      · exact Or.inl ⟨hv, hvk, hj, fun hk => hiff ⟨fun _ => hk, fun _ => hj⟩⟩
      · have hk : G.Adj (D.k t) v := by
          by_contra hk; exact hiff ⟨fun h => (hj h).elim, fun h => (hk h).elim⟩
        exact Or.inr ⟨hv, Or.inl ⟨hk, hj⟩⟩
  · rintro ⟨t, ht, ⟨hv, hvk, hj, hk⟩ | ⟨hv, ⟨hk, hj⟩ | h⟩⟩
    · exact ⟨hv, t, ht, Or.inr ⟨D.j_ne_of_B' ht hv, hvk, fun h => hk (h.1 hj)⟩⟩
    · refine ⟨hv, t, ht, Or.inr ⟨D.j_ne_of_B' ht hv, ?_, fun h => hj (h.2 hk)⟩⟩
      rintro rfl; exact hk.ne rfl
    · exact ⟨hv, t, ht, Or.inl h⟩

/-- The separators are vertices of the side graph `G[B ⊕ B']`. -/
theorem sep_mem {v : V} (hv : D.Sep v) : v ∈ D.B ∆ D.B' := by
  obtain ⟨t, ht, h⟩ := D.sep_iff.1 hv
  exact D.sepAt_mem ht h

/-! ### The shape of one step -/

/-- A step has at most one `j`-type separator: one of the two `C'`-neighbours of `j_t` is `k_t` or
is adjacent to `k_t` (Corollary 2, `corollary2_hole_neighbor`). -/
theorem jsep_unique (hclaw : G.IsClawFree) {t : ℕ} (ht : t < D.l) {p q : V}
    (hp : D.JSep t p) (hq : D.JSep t q) : p = q := by
  obtain ⟨u₀, w₀, huw, hu, hw, hN⟩ := D.nbrA' (D.j t) (D.j_memA' t ht)
  have hp' := (hN p hp.1).1 hp.2.2.1
  have hq' := (hN q hq.1).1 hq.2.2.1
  by_cases hkB' : D.k t ∈ D.B'
  · have hk' := (hN (D.k t) hkB').1 (D.adj_kj t ht).symm
    rcases hk' with hk' | hk'
    · have hp'' : p = w₀ := hp'.resolve_left (fun h => hp.2.1 (h.trans hk'.symm))
      have hq'' : q = w₀ := hq'.resolve_left (fun h => hq.2.1 (h.trans hk'.symm))
      rw [hp'', hq'']
    · have hp'' : p = u₀ := hp'.resolve_right (fun h => hp.2.1 (h.trans hk'.symm))
      have hq'' : q = u₀ := hq'.resolve_right (fun h => hq.2.1 (h.trans hk'.symm))
      rw [hp'', hq'']
  · have hc := hclaw.adjacent_to_one_of_nonadjacent_neighbors (D.adj_kj t ht)
      ((hN u₀ hu).2 (Or.inl rfl)) ((hN w₀ hw).2 (Or.inr rfl))
      (fun h => hkB' (h ▸ hu)) (fun h => hkB' (h ▸ hw)) huw (D.indepB' hu hw)
    rcases hc with hc | hc
    · have hp'' : p = w₀ := hp'.resolve_left (fun h => hp.2.2.2 (by rw [h]; exact hc))
      have hq'' : q = w₀ := hq'.resolve_left (fun h => hq.2.2.2 (by rw [h]; exact hc))
      rw [hp'', hq'']
    · have hp'' : p = u₀ := hp'.resolve_right (fun h => hp.2.2.2 (by rw [h]; exact hc))
      have hq'' : q = u₀ := hq'.resolve_right (fun h => hq.2.2.2 (by rw [h]; exact hc))
      rw [hp'', hq'']

/-- The common `B'`-neighbour `b` of `j t` and `k t` next to a `j`-type separator `p`. -/
theorem exists_common (hclaw : G.IsClawFree) {t : ℕ} (ht : t < D.l) {p : V} (hp : D.JSep t p)
    (hkB' : D.k t ∉ D.B') :
    ∃ b ∈ D.B', b ≠ p ∧ G.Adj (D.j t) b ∧ G.Adj (D.k t) b ∧
      ∀ y ∈ D.B', G.Adj (D.j t) y → y = b ∨ y = p := by
  obtain ⟨u₀, w₀, huw, hu, hw, hN⟩ := D.nbrA' (D.j t) (D.j_memA' t ht)
  have hc := hclaw.adjacent_to_one_of_nonadjacent_neighbors (D.adj_kj t ht)
    ((hN u₀ hu).2 (Or.inl rfl)) ((hN w₀ hw).2 (Or.inr rfl))
    (fun h => hkB' (h ▸ hu)) (fun h => hkB' (h ▸ hw)) huw (D.indepB' hu hw)
  have hp' := (hN p hp.1).1 hp.2.2.1
  have hju : G.Adj (D.j t) u₀ := (hN u₀ hu).2 (Or.inl rfl)
  have hjw : G.Adj (D.j t) w₀ := (hN w₀ hw).2 (Or.inr rfl)
  rcases hp' with rfl | rfl
  · refine ⟨w₀, hw, huw.symm, hjw, ?_, ?_⟩
    · rcases hc with hc | hc
      · exact (hp.2.2.2 hc).elim
      · exact hc
    · intro y hy hjy
      rcases (hN y hy).1 hjy with h | h
      · exact Or.inr h
      · exact Or.inl h
  · refine ⟨u₀, hu, huw, hju, ?_, ?_⟩
    · rcases hc with hc | hc
      · exact hc
      · exact (hp.2.2.2 hc).elim
    · intro y hy hjy
      exact (hN y hy).1 hjy

/-- A step has at most one `k`-type separator: two of them, together with `j_t`, would form a claw
at `k_t`. -/
theorem ksep_unique (hclaw : G.IsClawFree) {t : ℕ} (ht : t < D.l) {u v : V}
    (hu : D.KSep t u) (hv : D.KSep t v) : u = v := by
  rcases hu with ⟨hu, ⟨hku, hju⟩ | rfl⟩ <;> rcases hv with ⟨hv, ⟨hkv, hjv⟩ | rfl⟩
  · by_contra huv
    rcases hclaw hku hkv (D.adj_kj t ht) huv (D.j_ne_of_B' ht hu) (D.j_ne_of_B' ht hv) with
      h | h | h
    · exact D.indepB' hu hv h
    · exact hju h.symm
    · exact hjv h.symm
  · exact (D.indepB' hv hu hku).elim
  · exact (D.indepB' hu hv hkv).elim
  · rfl

/-! ### Hand-off: the `k`-type separator of a step reappears later -/

/-- The `k`-type separator `q` of step `t` is a `j`-type separator of step `t + 1` or `t + 2`.
(In the second case `q` is adjacent to `k_t`, `k_{t+1}`, `j_{t+1}` and `j_{t+2}`, and not to
`j_t` or `k_{t+2}`.) -/
theorem handoff (hclaw : G.IsClawFree) {t : ℕ} (ht : t < D.l) {q : V} (hq : D.KSep t q) :
    ∃ t', t < t' ∧ t' < D.l ∧ D.JSep t' q := by
  rcases hq with ⟨hqB', ⟨hkq, hjq⟩ | rfl⟩
  · -- `k`-type separator `q = v`
    have hkB' : D.k t ∉ D.B' := fun h => D.indepB' h hqB' hkq
    obtain ⟨e₁, e₂, he, he₁, he₂, hN⟩ := D.nbrB' q hqB'
    have hq₁ : G.Adj q e₁ := (hN e₁ he₁).2 (Or.inl rfl)
    have hq₂ : G.Adj q e₂ := (hN e₂ he₂).2 (Or.inr rfl)
    have hqA : q ∉ D.A := fun h => D.indepA (D.k_memA t ht) h hkq
    have hqk : ∀ s < D.l, q ≠ D.k s := fun s hs h => hqA (h ▸ D.k_memA s hs)
    -- `k t` is adjacent to one of the two `A'`-neighbours of `q`; it is `j (t+1)`
    have hc := hclaw.adjacent_to_one_of_nonadjacent_neighbors hkq hq₁ hq₂
      (D.k_ne_of_A' ht he₁) (D.k_ne_of_A' ht he₂) he (D.indepA' he₁ he₂)
    -- the neighbour `e` of `q` adjacent to `k t`, and the other one `a`
    obtain ⟨e, a, heA, haA, hqe, hqa, hea, hke, hothers⟩ :
        ∃ e a, e ∈ D.A' ∧ a ∈ D.A' ∧ G.Adj q e ∧ G.Adj q a ∧ e ≠ a ∧ G.Adj (D.k t) e ∧
          ∀ y ∈ D.A', G.Adj q y → y = e ∨ y = a := by
      rcases hc with hc | hc
      · exact ⟨e₁, e₂, he₁, he₂, hq₁, hq₂, he, hc, fun y hy h => (hN y hy).1 h⟩
      · exact ⟨e₂, e₁, he₂, he₁, hq₂, hq₁, he.symm, hc,
          fun y hy h => ((hN y hy).1 h).symm⟩
    have ht1 : t + 1 < D.l ∧ e = D.j (t + 1) := by
      rcases D.nbrA'_k t ht e heA hke with h | h
      · exact (hjq (h ▸ hqe.symm)).elim
      · exact h
    obtain ⟨ht1, rfl⟩ := ht1
    by_cases hk1 : G.Adj (D.k (t + 1)) q
    · -- the jump case: `a = j (t+2)`
      have hat : a ≠ D.j t := by rintro rfl; exact hjq hqa.symm
      have hka : ¬G.Adj (D.k t) a := by
        intro h
        rcases D.nbrA'_k t ht a haA h with h' | h'
        · exact hat h'
        · exact hea h'.2.symm
      have hkk : D.k t ≠ D.k (t + 1) := fun h => by
        have := D.k_inj t ht (t + 1) ht1 h; omega
      have hcl := hclaw hkq.symm hk1.symm hqa hkk (D.k_ne_of_A' ht haA)
        (D.k_ne_of_A' ht1 haA)
      have hk1a : G.Adj (D.k (t + 1)) a := by
        rcases hcl with h | h | h
        · exact (D.indepA (D.k_memA t ht) (D.k_memA (t + 1) ht1) h).elim
        · exact (hka h).elim
        · exact h
      have ht2 : t + 2 < D.l ∧ a = D.j (t + 2) := by
        rcases D.nbrA'_k (t + 1) ht1 a haA hk1a with h | h
        · exact (hea h.symm).elim
        · exact h
      obtain ⟨ht2, rfl⟩ := ht2
      refine ⟨t + 2, by omega, ht2, hqB', hqk _ ht2, hqa.symm, ?_⟩
      intro hk2
      have hkk2 : D.k t ≠ D.k (t + 2) := fun h => by
        have := D.k_inj t ht (t + 2) ht2 h; omega
      have hk12 : D.k (t + 1) ≠ D.k (t + 2) := fun h => by
        have := D.k_inj (t + 1) ht1 (t + 2) ht2 h; omega
      rcases hclaw hkq.symm hk1.symm hk2.symm hkk hkk2 hk12 with h | h | h
      · exact D.indepA (D.k_memA t ht) (D.k_memA (t + 1) ht1) h
      · exact D.indepA (D.k_memA t ht) (D.k_memA (t + 2) ht2) h
      · exact D.indepA (D.k_memA (t + 1) ht1) (D.k_memA (t + 2) ht2) h
    · exact ⟨t + 1, by omega, ht1, hqB', hqk _ ht1, hqe.symm, hk1⟩
  · -- removed-vertex separator `q = k t ∈ B'`
    obtain ⟨e₁, e₂, he, he₁, he₂, hN⟩ := D.nbrB' (D.k t) hqB'
    have h₁ := D.nbrA'_k t ht e₁ he₁ ((hN e₁ he₁).2 (Or.inl rfl))
    have h₂ := D.nbrA'_k t ht e₂ he₂ ((hN e₂ he₂).2 (Or.inr rfl))
    have ht1 : t + 1 < D.l := by
      rcases h₁ with h₁ | h₁
      · rcases h₂ with h₂ | h₂
        · exact (he (h₁.trans h₂.symm)).elim
        · exact h₂.1
      · exact h₁.1
    refine ⟨t + 1, by omega, ht1, hqB', ?_, (D.adj_kj_succ t ht1).symm, ?_⟩
    · intro h; have := D.k_inj t ht (t + 1) ht1 h; omega
    · exact fun h => D.indepA (D.k_memA (t + 1) ht1) (D.k_memA t ht) h

/-! ### The separators of one step lie in one component -/

/-- Linking step for the `k`-type case, symmetric in the two `C`-neighbours `g₁ g₂` of `k t`. -/
theorem link_K (hclaw : G.IsClawFree) {t : ℕ} {p v b g₁ g₂ : V}
    (hp : D.JSep t p) (hvB' : v ∈ D.B') (hkv : G.Adj (D.k t) v) (hjv : ¬G.Adj (D.j t) v)
    (hb : b ∈ D.B') (hbp : b ≠ p) (hjb : G.Adj (D.j t) b) (hkb : G.Adj (D.k t) b)
    (hg₁ : g₁ ∈ D.B) (hg₂ : g₂ ∈ D.B) (hg₁₂ : g₁ ≠ g₂)
    (hjg₁ : G.Adj (D.j t) g₁) (hjg₂ : G.Adj (D.j t) g₂)
    (hkg₁ : G.Adj (D.k t) g₁) (hkg₂ : G.Adj (D.k t) g₂)
    (hpB : p ∉ D.B) (hvB : v ∉ D.B) (hpg₁ : G.Adj p g₁) (hvg : G.Adj v g₁ ∨ G.Adj v g₂)
    (hbg : b = g₁ ∨ b = g₂ ∨ b ∉ D.B) :
    v ∈ D.Comp p := by
  have hpU := D.mem_symmDiff_of_B' hp.1 hpB
  have hvU := D.mem_symmDiff_of_B' hvB' hvB
  have hbv : b ≠ v := by rintro rfl; exact hjv hjb
  -- (†) at `j t` and (‡) at `k t`
  have dag : ∀ g ∈ D.B, G.Adj (D.j t) g → g ≠ b → G.Adj g p ∨ G.Adj g b := fun g hg hjg hgb =>
    hclaw.adjacent_to_one_of_nonadjacent_neighbors hjg.symm hp.2.2.1 hjb
      (fun h => hpB (h ▸ hg)) hgb hbp.symm (D.indepB' hp.1 hb)
  have ddag : ∀ g ∈ D.B, G.Adj (D.k t) g → g ≠ b → G.Adj g b ∨ G.Adj g v := fun g hg hkg hgb =>
    hclaw.adjacent_to_one_of_nonadjacent_neighbors hkg.symm hkb hkv hgb
      (fun h => hvB (h ▸ hg)) hbv (D.indepB' hb hvB')
  have hg₁U := D.mem_symmDiff_of_B hg₁ hp.1 hpg₁.symm
  have hg₁c : g₁ ∈ D.Comp p := D.comp_adj (D.comp_self hpU) hg₁U hpg₁
  rcases hbg with rfl | rfl | hbB
  · -- `b = g₁ ∈ B`: impossible since `g₁ ~ p` and `b, p ∈ B'`
    exact (D.indepB' hb hp.1 hpg₁.symm).elim
  · -- `b = g₂ ∈ B`: `g₁ ≁ b`, so `g₁ ~ v` by (‡)
    rcases ddag g₁ hg₁ hkg₁ hg₁₂ with h | h
    · exact (D.indepB hg₁ hg₂ h).elim
    · exact D.comp_adj hg₁c hvU h
  · have hbU := D.mem_symmDiff_of_B' hb hbB
    by_cases h₁v : G.Adj v g₁
    · exact D.comp_adj hg₁c hvU h₁v.symm
    · have hvg₂ : G.Adj v g₂ := hvg.resolve_left h₁v
      have hg₁b : g₁ ≠ b := fun h => hbB (h ▸ hg₁)
      have hg₂b : g₂ ≠ b := fun h => hbB (h ▸ hg₂)
      have hg₂U := D.mem_symmDiff_of_B hg₂ hvB' hvg₂.symm
      -- (‡) for g₁: g₁ ~ b
      have h1b : G.Adj g₁ b := (ddag g₁ hg₁ hkg₁ hg₁b).resolve_right (fun h => h₁v h.symm)
      have hbc : b ∈ D.Comp p := D.comp_adj hg₁c hbU h1b
      rcases dag g₂ hg₂ hjg₂ hg₂b with h | h
      · exact D.comp_adj (D.comp_adj (D.comp_self hpU) hg₂U h.symm) hvU hvg₂.symm
      · exact D.comp_adj (D.comp_adj hbc hg₂U h.symm) hvU hvg₂.symm

/-- The `j`-type and the `k`-type separator of the same step lie in one component of
`G[B ⊕ B']`.  They are joined by a path of length `2` through a `C`-neighbour of `k_t`, or of
length `4` through both `C`-neighbours `γ, γ'` of `k_t` and a common `B'`-neighbour of `j_t`, `k_t`
(in general there is no common neighbour in `B ∖ B'`). -/
theorem comp_JK (hclaw : G.IsClawFree) {t : ℕ} (ht : t < D.l) {p q : V}
    (hp : D.JSep t p) (hq : D.KSep t q) : q ∈ D.Comp p := by
  obtain ⟨γ, γ', hγγ', hγ, hγ', hNk⟩ := D.nbrA (D.k t) (D.k_memA t ht)
  have hkγ : G.Adj (D.k t) γ := (hNk γ hγ).2 (Or.inl rfl)
  have hkγ' : G.Adj (D.k t) γ' := (hNk γ' hγ').2 (Or.inr rfl)
  have hjγ : G.Adj (D.j t) γ := (D.fwd_adj t ht γ hγ).2 hkγ
  have hjγ' : G.Adj (D.j t) γ' := (D.fwd_adj t ht γ' hγ').2 hkγ'
  have hpB : p ∉ D.B := D.sepAt_notB ht (Or.inl hp)
  have hpU := D.mem_symmDiff_of_B' hp.1 hpB
  -- (*) claw at `j t` on `{γ, γ', p}`
  have hstar : G.Adj p γ ∨ G.Adj p γ' :=
    hclaw.adjacent_to_one_of_nonadjacent_neighbors hp.2.2.1.symm hjγ hjγ'
      (fun h => hpB (h ▸ hγ)) (fun h => hpB (h ▸ hγ')) hγγ' (D.indepB hγ hγ')
  rcases hq with ⟨hqB', ⟨hkq, hjq⟩ | rfl⟩
  · have hkB' : D.k t ∉ D.B' := fun h => D.indepB' h hqB' hkq
    have hqB : q ∉ D.B := D.sepAt_notB ht (Or.inr ⟨hqB', Or.inl ⟨hkq, hjq⟩⟩)
    obtain ⟨b, hb, hbp, hjb, hkb, -⟩ := D.exists_common hclaw ht hp hkB'
    -- (**) claw at `k t` on `{γ, γ', q}`
    have hss : G.Adj q γ ∨ G.Adj q γ' :=
      hclaw.adjacent_to_one_of_nonadjacent_neighbors hkq.symm hkγ hkγ'
        (fun h => hqB (h ▸ hγ)) (fun h => hqB (h ▸ hγ')) hγγ' (D.indepB hγ hγ')
    have hbg : ∀ g₁ g₂, (g₁ = γ ∧ g₂ = γ' ∨ g₁ = γ' ∧ g₂ = γ) → b = g₁ ∨ b = g₂ ∨ b ∉ D.B := by
      intro g₁ g₂ hg
      by_cases hbB : b ∈ D.B
      · rcases (hNk b hbB).1 hkb with h | h <;> rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          simp [h]
      · exact Or.inr (Or.inr hbB)
    rcases hstar with h | h
    · exact D.link_K hclaw hp hqB' hkq hjq hb hbp hjb hkb hγ hγ' hγγ' hjγ hjγ' hkγ hkγ'
        hpB hqB h hss (hbg γ γ' (Or.inl ⟨rfl, rfl⟩))
    · exact D.link_K hclaw hp hqB' hkq hjq hb hbp hjb hkb hγ' hγ hγγ'.symm hjγ' hjγ hkγ'
        hkγ hpB hqB h hss.symm (hbg γ' γ (Or.inr ⟨rfl, rfl⟩))
  · -- `q = k t ∈ B'`: both `C`-neighbours of `k t` lie in `B \ B'`
    have hkU := D.mem_symmDiff_of_B' hqB' (D.k_notB ht)
    rcases hstar with h | h
    · have hγU := D.mem_symmDiff_of_B hγ hqB' hkγ.symm
      exact D.comp_adj (D.comp_adj (D.comp_self hpU) hγU h) hkU hkγ.symm
    · have hγU := D.mem_symmDiff_of_B hγ' hqB' hkγ'.symm
      exact D.comp_adj (D.comp_adj (D.comp_self hpU) hγU h) hkU hkγ'.symm

/-! ### Type-1 steps are unbalanced -/

/-- A step of type 1 is unbalanced.  For an interior step `t < ℓ - 1`, type 1 forces `k_t` to be a
clone in `C'` of the `B'`-vertex `b` adjacent to both `j_t` and `j_{t+1}` (a crossed clone); for
the last step it forces `k_{ℓ-1}` not to be a clone of `j_{ℓ-1}` (not a matched clone). -/
theorem type1_unbal (hclaw : G.IsClawFree) {t : ℕ} (ht : t < D.l) (h1 : D.Type1 t) :
    D.Unbal t := by
  obtain ⟨⟨p, hp⟩, hnoK⟩ := h1
  rcases Nat.lt_or_ge (t + 1) D.l with ht1 | ht1
  · right
    refine ⟨ht1, ?_⟩
    have hkB' : D.k t ∉ D.B' := fun h => hnoK (D.k t) ⟨h, Or.inr rfl⟩
    obtain ⟨b, hb, hbp, hjb, hkb, hNj⟩ := D.exists_common hclaw ht hp hkB'
    -- every `B'`-neighbour of `k t` is a neighbour of `j t`
    have hKk : ∀ y ∈ D.B', G.Adj (D.k t) y → G.Adj (D.j t) y := by
      intro y hy hky
      by_contra hjy
      exact hnoK y ⟨hy, Or.inl ⟨hky, hjy⟩⟩
    have hKb : ∀ y ∈ D.B', G.Adj (D.k t) y → y = b := by
      intro y hy hky
      rcases hNj y hy (hKk y hy hky) with h | h
      · exact h
      · exact (hp.2.2.2 (h ▸ hky)).elim
    -- `b ~ j (t+1)`
    obtain ⟨c₁, c₂, hc, hc₁, hc₂, hNc⟩ := D.nbrA' (D.j (t + 1)) (D.j_memA' (t + 1) ht1)
    have hbj1 : G.Adj b (D.j (t + 1)) := by
      rcases hclaw.adjacent_to_one_of_nonadjacent_neighbors (D.adj_kj_succ t ht1)
          ((hNc c₁ hc₁).2 (Or.inl rfl)) ((hNc c₂ hc₂).2 (Or.inr rfl))
          (fun h => hkB' (h ▸ hc₁)) (fun h => hkB' (h ▸ hc₂)) hc (D.indepB' hc₁ hc₂) with
        h | h
      · rw [← hKb c₁ hc₁ h]; exact ((hNc c₁ hc₁).2 (Or.inl rfl)).symm
      · rw [← hKb c₂ hc₂ h]; exact ((hNc c₂ hc₂).2 (Or.inr rfl)).symm
    have hjj : D.j t ≠ D.j (t + 1) := fun h => by
      have := D.j_inj t ht (t + 1) ht1 h; omega
    obtain ⟨e₁, e₂, he, he₁, he₂, hNb⟩ := D.nbrB' b hb
    have hbA := two_nbrs hNb (D.j_memA' t ht) (D.j_memA' (t + 1) ht1) hjb.symm hbj1 hjj
    refine ⟨b, hb, ?_, Or.inr hb, ?_⟩
    · rintro (h | h)
      · exact D.k_notA' t ht h
      · exact hkB' h
    · intro y hy
      rcases hy with hyA | hyB
      · constructor
        · intro hky
          right
          rcases D.nbrA'_k t ht y hyA hky with rfl | ⟨-, rfl⟩
          · exact hjb.symm
          · exact hbj1
        · rintro (rfl | hby)
          · exact (D.disjA'B' hyA hb).elim
          · rcases hbA y hyA hby with rfl | rfl
            · exact D.adj_kj t ht
            · exact D.adj_kj_succ t ht1
      · constructor
        · intro hky; exact Or.inl (hKb y hyB hky)
        · rintro (rfl | hby)
          · exact hkb
          · exact (D.indepB' hb hyB hby).elim
  · left
    refine ⟨by omega, ?_⟩
    rintro ⟨x, hxA, hcl⟩
    have hkx : G.Adj (D.k t) x := (hcl.2.2 x hcl.2.1).2 (Or.inl rfl)
    have hxj : x = D.j t := by
      rcases D.nbrA'_k t ht x hxA hkx with h | h
      · exact h
      · omega
    subst hxj
    exact hp.2.2.2 ((hcl.2.2 p (Or.inr hp.1)).2 (Or.inr hp.2.2.1))

/-- An interior removed vertex `k_t`, `t < ℓ - 1`, is never a matched clone: a clone of a vertex
of `A'` has a single neighbour in `A'`, whereas `k_t` has the two neighbours `j_t`, `j_{t+1}`. -/
theorem not_matched_of_lt {t : ℕ} (ht1 : t + 1 < D.l) : ¬D.Matched t := by
  rintro ⟨x, hxA, hcl⟩
  have ht : t < D.l := by omega
  have h0 := (hcl.2.2 (D.j t) (Or.inl (D.j_memA' t ht))).1 (D.adj_kj t ht)
  have h1 := (hcl.2.2 (D.j (t + 1)) (Or.inl (D.j_memA' (t + 1) ht1))).1 (D.adj_kj_succ t ht1)
  have e0 : D.j t = x := h0.resolve_right (fun h => D.indepA' hxA (D.j_memA' t ht) h)
  have e1 : D.j (t + 1) = x :=
    h1.resolve_right (fun h => D.indepA' hxA (D.j_memA' (t + 1) ht1) h)
  have := D.j_inj t ht (t + 1) ht1 (e0.trans e1.symm)
  omega

/-! ### The chain of separators -/

/-- Downward induction on the step: the separators of the step `t` are connected to a root
(the `j`-type separator of a type-1 step `t' ≥ t`). -/
theorem chain_aux (hclaw : G.IsClawFree) :
    ∀ n t, D.l - t ≤ n → t < D.l → ∀ u, D.SepAt t u →
      ∃ t' < D.l, D.Type1 t' ∧ ∃ σ, D.JSep t' σ ∧ σ ∈ D.Comp u := by
  intro n
  induction n with
  | zero => intro t h ht; omega
  | succ n ih =>
    intro t hn ht u hu
    have huU := D.sepAt_mem ht hu
    -- find a `k`-type separator `q` of step `t` connected to `u`, unless `t` is of type 1
    by_cases h1 : D.Type1 t
    · rcases hu with hu | hu
      · exact ⟨t, ht, h1, u, hu, D.comp_self huU⟩
      · exact (h1.2 u hu).elim
    · obtain ⟨q, hq, hqc⟩ : ∃ q, D.KSep t q ∧ q ∈ D.Comp u := by
        rcases hu with hu | hu
        · have : ∃ q, D.KSep t q := by
            by_contra hno
            exact h1 ⟨⟨u, hu⟩, fun v hv => hno ⟨v, hv⟩⟩
          obtain ⟨q, hq⟩ := this
          exact ⟨q, hq, D.comp_JK hclaw ht hu hq⟩
        · exact ⟨u, hu, D.comp_self huU⟩
      obtain ⟨t', htt', ht', hq'⟩ := D.handoff hclaw ht hq
      obtain ⟨t'', ht'', h1', σ, hσ, hσc⟩ :=
        ih t' (by omega) ht' q (Or.inl hq')
      exact ⟨t'', ht'', h1', σ, hσ, D.comp_trans hqc hσc⟩

/-- **Chain lemma.**  Every separator of step `t` is connected, inside `G[B ⊕ B']`, to the
`j`-type separator of a type-1 step `t' < ℓ`. -/
theorem chain (hclaw : G.IsClawFree) {t : ℕ} (ht : t < D.l) {u : V} (hu : D.SepAt t u) :
    ∃ t' < D.l, D.Type1 t' ∧ ∃ σ, D.JSep t' σ ∧ σ ∈ D.Comp u :=
  D.chain_aux hclaw (D.l - t) t le_rfl ht u hu

/-- General bound, in chain form: every separator is connected, inside `G[B ⊕ B']`, to the
`j`-type separator of an unbalanced step. -/
theorem sep_connected_to_unbal (hclaw : G.IsClawFree) {u : V} (hu : D.Sep u) :
    ∃ t < D.l, D.Unbal t ∧ ∃ σ, D.JSep t σ ∧ σ ∈ D.Comp u := by
  obtain ⟨t, ht, hut⟩ := D.sep_iff.1 hu
  obtain ⟨t', ht', h1, σ, hσ, hσc⟩ := D.chain hclaw ht hut
  exact ⟨t', ht', D.type1_unbal hclaw ht' h1, σ, hσ, hσc⟩

/-! ### The roots of the separators (general bound, abstract form) -/

/-- A `j`-type separator of a step is a separator. -/
theorem sep_of_jsep {t : ℕ} (ht : t < D.l) {v : V} (hv : D.JSep t v) : D.Sep v :=
  D.sep_iff.2 ⟨t, ht, Or.inl hv⟩

/-- **General bound, abstract form.**  The separators are connected to a set `R` of *root
separators*, with at most one root for each step of a set `T` of unbalanced steps (the root of the
step `t` being its unique `j`-type separator, `jsep_unique`). -/
theorem exists_roots (hclaw : G.IsClawFree) :
    ∃ (R : Finset V) (T : Finset ℕ), (∀ r ∈ R, D.Sep r) ∧ (∀ t ∈ T, t < D.l ∧ D.Unbal t) ∧
      R.card ≤ T.card ∧ ∀ u, D.Sep u → ∃ r ∈ R, r ∈ D.Comp u := by
  classical
  let σ : ℕ → V := fun t => if h : ∃ v, D.JSep t v then h.choose else D.k 0
  have hσ : ∀ t, (∃ v, D.JSep t v) → D.JSep t (σ t) := fun t h => by
    simp only [σ, dif_pos h]
    exact h.choose_spec
  let T : Finset ℕ := (Finset.range D.l).filter fun t => D.Unbal t ∧ ∃ v, D.JSep t v
  have hT : ∀ t, t ∈ T ↔ t < D.l ∧ D.Unbal t ∧ ∃ v, D.JSep t v := fun t => by simp [T]
  refine ⟨T.image σ, T, ?_, ?_, Finset.card_image_le, ?_⟩
  · intro r hr
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨htl, -, hex⟩ := (hT t).1 ht
    exact D.sep_of_jsep htl (hσ t hex)
  · intro t ht
    obtain ⟨htl, hub, -⟩ := (hT t).1 ht
    exact ⟨htl, hub⟩
  · intro u hu
    obtain ⟨t, ht, hub, v, hv, hvc⟩ := D.sep_connected_to_unbal hclaw hu
    have hex : ∃ v, D.JSep t v := ⟨v, hv⟩
    have hv' : σ t = v := D.jsep_unique hclaw ht (hσ t hex) hv
    exact ⟨σ t, Finset.mem_image.2 ⟨t, (hT t).2 ⟨ht, hub, hex⟩, rfl⟩, hv' ▸ hvc⟩

/-- The count of unbalanced steps: `|T| + |M| ≤ 1 + |X|` for a set `T` of unbalanced steps, where
`M` collects the (removed vertices of the) matched steps and `X` the crossed ones.  Only the last
step can be matched (`not_matched_of_lt`); an interior step is unbalanced exactly when it is
crossed, and the last step is unbalanced exactly when it is not matched. -/
theorem card_unbal_add_le (M X : Finset V) (T : Finset ℕ)
    (hT : ∀ t ∈ T, t < D.l ∧ D.Unbal t)
    (hM : ∀ w ∈ M, ∃ t < D.l, w = D.k t ∧ D.Matched t)
    (hX : ∀ t < D.l, D.Crossed t → D.k t ∈ X) :
    T.card + M.card ≤ 1 + X.card := by
  classical
  -- the interior unbalanced steps inject into `X`
  have hint : (T.filter fun t => t + 1 < D.l).card ≤ X.card := by
    refine Finset.card_le_card_of_injOn D.k ?_ ?_
    · intro t ht
      have ht' := Finset.mem_filter.1 (Finset.mem_coe.1 ht)
      obtain ⟨htl, hub⟩ := hT t ht'.1
      have hc : D.Crossed t := by
        rcases hub with ⟨he, -⟩ | ⟨-, hc⟩
        · omega
        · exact hc
      exact Finset.mem_coe.2 (hX t htl hc)
    · intro t ht t' ht' h
      have h1 := Finset.mem_filter.1 (Finset.mem_coe.1 ht)
      have h2 := Finset.mem_filter.1 (Finset.mem_coe.1 ht')
      exact D.k_inj t (hT t h1.1).1 t' (hT t' h2.1).1 h
  -- a matched step is the last one
  have hMlast : ∀ w ∈ M, ∃ t, t + 1 = D.l ∧ w = D.k t ∧ D.Matched t := by
    intro w hw
    obtain ⟨t, htl, rfl, hm⟩ := hM w hw
    refine ⟨t, ?_, rfl, hm⟩
    by_contra hne
    exact D.not_matched_of_lt (by omega) hm
  have hsplit : T ⊆ (T.filter fun t => t + 1 < D.l) ∪ (T.filter fun t => ¬ t + 1 < D.l) := by
    intro t ht
    by_cases h : t + 1 < D.l
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨ht, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨ht, h⟩)
  have hlast : (T.filter fun t => ¬ t + 1 < D.l).card + M.card ≤ 1 := by
    by_cases hM0 : M = ∅
    · rw [hM0, Finset.card_empty]
      have hsub : (T.filter fun t => ¬ t + 1 < D.l) ⊆ {D.l - 1} := by
        intro t ht
        have h1 := Finset.mem_filter.1 ht
        have h2 := (hT t h1.1).1
        simp only [Finset.mem_singleton]
        omega
      have := Finset.card_le_card hsub
      simp only [Finset.card_singleton] at this
      omega
    · obtain ⟨w, hw⟩ := Finset.nonempty_iff_ne_empty.2 hM0
      obtain ⟨t₀, ht₀, rfl, hm₀⟩ := hMlast w hw
      have hMc : M.card ≤ 1 := by
        refine Finset.card_le_one.2 fun a ha b hb => ?_
        obtain ⟨ta, hta, rfl, -⟩ := hMlast a ha
        obtain ⟨tb, htb, rfl, -⟩ := hMlast b hb
        have : ta = tb := by omega
        rw [this]
      have hnone : (T.filter fun t => ¬ t + 1 < D.l) = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun t ht => ?_
        have h1 := Finset.mem_filter.1 ht
        obtain ⟨htl, hub⟩ := hT t h1.1
        rcases hub with ⟨he, hnm⟩ | ⟨h2, -⟩
        · have : t = t₀ := by omega
          subst this
          exact hnm hm₀
        · exact h1.2 h2
      rw [hnone, Finset.card_empty]
      omega
  have := (Finset.card_le_card hsplit).trans (Finset.card_union_le _ _)
  omega

end SeparatorData

/-! ### The bridge: hole-class blocks give `SeparatorData` -/

section HoleClassNeighbours

variable [DecidableEq V] {s : Finset V × Finset V}

/-- A vertex of the first class of a hole-class state has exactly two neighbours in the second
class (explicit form of `IsHoleClasses.card_filter_snd_of_mem_fst`). -/
theorem IsHoleClasses.exists_two_adj_snd (hs : G.IsHoleClasses s) {x : V} (hx : x ∈ s.1) :
    ∃ u w, u ≠ w ∧ u ∈ (↑s.2 : Set V) ∧ w ∈ (↑s.2 : Set V) ∧
      ∀ y ∈ (↑s.2 : Set V), (G.Adj x y ↔ y = u ∨ y = w) := by
  classical
  obtain ⟨u, w, huw, hfil⟩ := Finset.card_eq_two.1 (hs.card_filter_snd_of_mem_fst hx)
  have hmem : ∀ y, y ∈ s.2.filter (G.Adj x) ↔ y = u ∨ y = w := by
    intro y
    rw [hfil]
    simp
  refine ⟨u, w, huw, ?_, ?_, ?_⟩
  · exact Finset.mem_coe.2 (Finset.mem_filter.1 ((hmem u).2 (Or.inl rfl))).1
  · exact Finset.mem_coe.2 (Finset.mem_filter.1 ((hmem w).2 (Or.inr rfl))).1
  · intro y hy
    rw [← hmem, Finset.mem_filter]
    exact ⟨fun h => ⟨Finset.mem_coe.1 hy, h⟩, fun h => h.2⟩

/-- A vertex of the second class of a hole-class state has exactly two neighbours in the first
class (explicit form of `IsHoleClasses.card_filter_fst_of_mem_snd`). -/
theorem IsHoleClasses.exists_two_adj_fst (hs : G.IsHoleClasses s) {x : V} (hx : x ∈ s.2) :
    ∃ u w, u ≠ w ∧ u ∈ (↑s.1 : Set V) ∧ w ∈ (↑s.1 : Set V) ∧
      ∀ y ∈ (↑s.1 : Set V), (G.Adj x y ↔ y = u ∨ y = w) := by
  classical
  obtain ⟨u, w, huw, hfil⟩ := Finset.card_eq_two.1 (hs.card_filter_fst_of_mem_snd hx)
  have hmem : ∀ y, y ∈ s.1.filter (G.Adj x) ↔ y = u ∨ y = w := by
    intro y
    rw [hfil]
    simp
  refine ⟨u, w, huw, ?_, ?_, ?_⟩
  · exact Finset.mem_coe.2 (Finset.mem_filter.1 ((hmem u).2 (Or.inl rfl))).1
  · exact Finset.mem_coe.2 (Finset.mem_filter.1 ((hmem w).2 (Or.inr rfl))).1
  · intro y hy
    rw [← hmem, Finset.mem_filter]
    exact ⟨fun h => ⟨Finset.mem_coe.1 hy, h⟩, fun h => h.2⟩

end HoleClassNeighbours

namespace OddBlock

variable [DecidableEq V] {X Y : Finset V}

/-- Membership in the word of a block, by step index. -/
theorem mem_word_iff_exists_lt (Q : G.OddBlock X Y) {p : V × V} :
    p ∈ Q.word ↔ ∃ t < Q.word.length, p = (Q.vtx (2 * t), Q.vtx (2 * t + 1)) := by
  constructor
  · intro hp
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hp
    exact ⟨t, ht, Q.word_getElem_eq ht⟩
  · rintro ⟨t, ht, rfl⟩
    rw [← Q.word_getElem_eq ht]
    exact List.getElem_mem ht

/-- **The bridge.**  A side-1 block `Q` of hole-class states which runs from `s` yields the abstract
`SeparatorData`: the vertices `j_t = p_{2t}`, `k_t = p_{2t+1}` of `Q`, with `A = s.1`, `B = s.2`,
`A' = s'.1`, `B' = s'.2`.  The facts about hole classes are `IsHoleClasses.disjoint`,
`isIndepSet_fst/snd` and the "exactly two neighbours" count; the facts about `Q` are the induced
path property and the component property of its support (for `nbrA'_k`); the forward conditions
`j_t ∉ B` and `Γ_B(j_t) = Γ_B(k_t)` are the "only if" half of `OddBlock.classRun_iff`.

The data has `B = s.2`, `B' = s'.2`; its separators are `Q.separators s'.2`; every vertex of `Q`
in `matchedW s' s` is the removed vertex `k_t` of a matched step `t`; and the removed vertex of
every crossed step lies in `crossedW s' s`. -/
theorem exists_separatorData {s s' : Finset V × Finset V} (hs : G.IsHoleClasses s)
    (hs' : G.IsHoleClasses s') (Q : G.OddBlock s.1 s'.1) (hQ : Q.RunsFrom s) :
    ∃ D : SeparatorData G, D.B = ↑s.2 ∧ D.B' = ↑s'.2 ∧
      (∀ v, D.Sep v ↔ v ∈ Q.separators s'.2) ∧
      (∀ w ∈ Q.support ∩ G.matchedW s' s, ∃ t < D.l, w = D.k t ∧ D.Matched t) ∧
      (∀ t < D.l, D.Crossed t → D.k t ∈ Q.support ∩ G.crossedW s' s) := by
  classical
  obtain ⟨r, hr⟩ := Q.even_card
  have hl : Q.word.length = r := by rw [Q.length_word]; omega
  have hcard : ∀ t < Q.word.length, 2 * t + 1 < Q.path.card := fun t ht => Q.two_mul_succ_lt ht
  have hfwd := (classRun_iff (A := s.1) (B := s.2) hs.isIndepSet_fst hs'.isIndepSet_fst hs
    Finset.subset_union_left Q (Finset.inter_comm _ _)).1 hQ
  have hstep : ∀ t, (hlt : t < Q.word.length) →
      (Q.vtx (2 * t), Q.vtx (2 * t + 1)) ∈ Q.word := fun t hlt =>
    (Q.mem_word_iff_exists_lt).2 ⟨t, hlt, rfl⟩
  have hindep : ∀ {S : Finset V}, G.IsIndepSet (↑S : Set V) → ∀ ⦃x y : V⦄,
      x ∈ (↑S : Set V) → y ∈ (↑S : Set V) → ¬G.Adj x y :=
    fun h x y hx hy hxy => h hx hy hxy.ne hxy
  have hdisj : ∀ {S T : Finset V}, Disjoint S T → ∀ ⦃x : V⦄, x ∈ (↑S : Set V) → x ∉ (↑T : Set V) :=
    fun h x hx hxT => Finset.disjoint_left.1 h (Finset.mem_coe.1 hx) (Finset.mem_coe.1 hxT)
  -- the `A'`-neighbours of `k t`
  have hnbr : ∀ t < Q.word.length, ∀ a ∈ (↑s'.1 : Set V), G.Adj (Q.vtx (2 * t + 1)) a →
      a = Q.vtx (2 * t) ∨ (t + 1 < Q.word.length ∧ a = Q.vtx (2 * (t + 1))) := by
    intro t ht a ha hadj
    have hkX : Q.vtx (2 * t + 1) ∈ s.1 :=
      (Finset.mem_sdiff.1 (Q.vtx_odd_mem (hcard t ht) (odd_two_mul_add_one t))).1
    have haX : a ∉ s.1 := fun h => hindep hs.isIndepSet_fst (Finset.mem_coe.2 hkX)
      (Finset.mem_coe.2 h) hadj
    have hasd : a ∈ (↑(symmDiff s.1 s'.1) : Set V) := by
      rw [Finset.mem_coe, Finset.mem_symmDiff]
      exact Or.inr ⟨Finset.mem_coe.1 ha, haX⟩
    have hks : Q.vtx (2 * t + 1) ∈ (↑Q.support : Set V) :=
      Finset.mem_coe.2 (Q.vtx_mem_support (hcard t ht))
    have has : a ∈ (↑Q.support : Set V) := Q.isInducedComponent_support.2.2 hks hasd hadj
    obtain ⟨i, hi, rfl⟩ := Q.vtx_lt_of_mem_support (Finset.mem_coe.1 has)
    have h := (Q.adj_vtx_iff (hcard t ht) hi).1 hadj
    rcases h with h | h
    · right
      refine ⟨by omega, ?_⟩
      rw [show 2 * (t + 1) = i by omega]
    · left
      rw [show 2 * t = i by omega]
  have hlt2 : ∀ t < Q.word.length, 2 * t < Q.path.card := fun t ht => by
    have := hcard t ht
    omega
  have hkX : ∀ t < Q.word.length, Q.vtx (2 * t + 1) ∈ s.1 ∧ Q.vtx (2 * t + 1) ∉ s'.1 :=
    fun t ht => Finset.mem_sdiff.1 (Q.vtx_odd_mem (hcard t ht) (odd_two_mul_add_one t))
  have hjY : ∀ t < Q.word.length, Q.vtx (2 * t) ∈ s'.1 ∧ Q.vtx (2 * t) ∉ s.1 :=
    fun t ht => Finset.mem_sdiff.1 (Q.vtx_even_mem (hlt2 t ht) (even_two_mul t))
  refine ⟨{ A := ↑s.1, B := ↑s.2, A' := ↑s'.1, B' := ↑s'.2, l := Q.word.length,
            j := fun t => Q.vtx (2 * t), k := fun t => Q.vtx (2 * t + 1),
            indepA := hindep hs.isIndepSet_fst, indepB := hindep hs.isIndepSet_snd,
            indepA' := hindep hs'.isIndepSet_fst, indepB' := hindep hs'.isIndepSet_snd,
            disjAB := hdisj hs.disjoint, disjA'B' := hdisj hs'.disjoint,
            nbrA' := fun x hx => hs'.exists_two_adj_snd (Finset.mem_coe.1 hx),
            nbrB' := fun x hx => hs'.exists_two_adj_fst (Finset.mem_coe.1 hx),
            nbrA := fun x hx => hs.exists_two_adj_snd (Finset.mem_coe.1 hx),
            j_memA' := fun t ht => Finset.mem_coe.2 (hjY t ht).1,
            k_memA := fun t ht => Finset.mem_coe.2 (hkX t ht).1,
            k_notA' := fun t ht h => (hkX t ht).2 (Finset.mem_coe.1 h),
            j_inj := fun t ht t' ht' h => by
              have := Q.vtx_injective_of_lt (hlt2 t ht) (hlt2 t' ht') h
              omega,
            k_inj := fun t ht t' ht' h => by
              have := Q.vtx_injective_of_lt (hcard t ht) (hcard t' ht') h
              omega,
            adj_kj := fun t ht => (Q.adj_vtx_iff (hcard t ht) (hlt2 t ht)).2 (Or.inr rfl),
            adj_kj_succ := fun t ht => by
              have h2 : 2 * (t + 1) < Q.path.card := by
                have := hcard (t + 1) ht
                omega
              exact (Q.adj_vtx_iff (hcard t (by omega)) h2).2 (Or.inl (by omega)),
            nbrA'_k := hnbr,
            fwd_notB := fun t ht h => (hfwd _ (hstep t ht)).1 (Finset.mem_coe.1 h),
            fwd_adj := fun t ht v hv => (hfwd _ (hstep t ht)).2 v (Finset.mem_coe.1 hv) },
    rfl, rfl, ?_, ?_, ?_⟩
  · intro v
    rw [Q.mem_separators]
    constructor
    · rintro ⟨hv, t, ht, h⟩
      exact ⟨Finset.mem_coe.1 hv, _, hstep t ht, h⟩
    · rintro ⟨hv, p, hp, h⟩
      obtain ⟨t, ht, rfl⟩ := Q.mem_word_iff_exists_lt.1 hp
      exact ⟨Finset.mem_coe.2 hv, t, ht, h⟩
  · intro w hw
    obtain ⟨hws, hwm⟩ := Finset.mem_inter.1 hw
    obtain ⟨i, hi, rfl⟩ := Q.vtx_lt_of_mem_support hws
    rw [mem_matchedW] at hwm
    rcases Nat.even_or_odd' i with ⟨m, hm | hm⟩
    · exfalso
      subst hm
      have hY := (Finset.mem_sdiff.1 (Q.vtx_even_mem hi (even_two_mul m))).1
      rcases hwm with ⟨-, h2, -⟩ | ⟨-, h2, -⟩ <;> exact h2 (Finset.mem_union_left _ hY)
    · subst hm
      refine ⟨m, (show m < Q.word.length by omega), rfl, ?_⟩
      rcases hwm with ⟨-, -, x, hx, hcl⟩ | ⟨h1, -, -⟩
      · rw [Finset.coe_union] at hcl
        exact ⟨x, Finset.mem_coe.2 hx, hcl⟩
      · exfalso
        have hX := (Finset.mem_sdiff.1 (Q.vtx_odd_mem hi (odd_two_mul_add_one m))).1
        exact Finset.disjoint_left.1 hs.disjoint hX h1
  · intro t ht hcr
    obtain ⟨x, hx, hcl⟩ := hcr
    refine Finset.mem_inter.2 ⟨Q.vtx_mem_support (hcard t ht), ?_⟩
    rw [mem_crossedW]
    refine Or.inl ⟨(hkX t ht).1, ?_, x, Finset.mem_coe.1 hx, ?_⟩
    · intro h
      rw [← Finset.mem_coe, Finset.coe_union] at h
      exact hcl.1 h
    · rw [Finset.coe_union]
      exact hcl

/-- **Lemma 1 for hole-class blocks** (T3-23(a)).  The separators of a forward-running block in
`s'.2` avoid `s.2`, so they are vertices of the side graph `G[s.2 ⊕ s'.2]`. -/
theorem separators_snd_subset_symmDiff {s s' : Finset V × Finset V} (hs : G.IsHoleClasses s)
    (hs' : G.IsHoleClasses s') (Q : G.OddBlock s.1 s'.1) (hQ : Q.RunsFrom s) :
    Q.separators s'.2 ⊆ symmDiff s.2 s'.2 := by
  obtain ⟨D, hB, hB', hSep, -⟩ := Q.exists_separatorData hs hs' hQ
  intro v hv
  have h := D.sep_mem ((hSep v).2 hv)
  rw [hB, hB', ← Finset.coe_symmDiff] at h
  exact Finset.mem_coe.1 h

/-- **Separator lemma, general bound** (for every key; strengthens
`separators_sameComponent`).  For a block `Q` of hole-class states which runs from `s`, the
separators of `Q` in `s'.2` are connected, inside `G[s.2 ⊕ s'.2]`, to the members of a set `R` of
at most `1 - m' + x'` *root separators* (`|R| + m' ≤ 1 + x'` with
`m' = |Q ∩ matchedW s' s|`, `x' = |Q ∩ crossedW s' s|`).  In particular the separators meet at most
`1 - m' + x'` components of `G[s.2 ⊕ s'.2]`.  The roots are the `j`-type separators of the
*unbalanced* steps: those whose removed vertex `k_t` is a crossed clone in `C'` (`t < ℓ - 1`), or
the last step when `k_{ℓ-1}` is not a matched clone. -/
theorem separators_components_le (hclaw : G.IsClawFree) {s s' : Finset V × Finset V}
    (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s') (Q : G.OddBlock s.1 s'.1)
    (hQ : Q.RunsFrom s) :
    ∃ R ⊆ Q.separators s'.2,
      R.card + (Q.support ∩ G.matchedW s' s).card ≤ 1 + (Q.support ∩ G.crossedW s' s).card ∧
      ∀ u ∈ Q.separators s'.2, ∃ r ∈ R, r ∈ G.inducedComponentSet ↑(symmDiff s.2 s'.2) u := by
  obtain ⟨D, hB, hB', hSep, hM, hX⟩ := Q.exists_separatorData hs hs' hQ
  obtain ⟨R, T, hR, hT, hRT, hconn⟩ := D.exists_roots hclaw
  have hU : (↑(symmDiff s.2 s'.2) : Set V) = D.B ∆ D.B' := by
    rw [hB, hB', Finset.coe_symmDiff]
  refine ⟨R, fun r hr => (hSep r).1 (hR r hr), ?_, ?_⟩
  · have := D.card_unbal_add_le (Q.support ∩ G.matchedW s' s) (Q.support ∩ G.crossedW s' s) T hT
      hM hX
    omega
  · intro u hu
    obtain ⟨r, hr, hrc⟩ := hconn u ((hSep u).2 hu)
    rw [hU]
    exact ⟨r, hr, hrc⟩

/-- **Separator lemma** (package T3-22; no counterpart in v1, it replaces the search-history
argument of v1 Lemma 8 (iii)-(iv) and Lemma 9, L1174-1189).  Let `G` be claw-free, `s`, `s'`
hole-class states and `Q` a side-1 block of `(s.1, s'.1)` which runs from `s`, with balanced
`W'`-content: `(m', x') ∈ {(0,0), (1,1)}`, where `m' = |Q ∩ matchedW s' s|` and
`x' = |Q ∩ crossedW s' s|`.  Then any two separators of `Q` in `s'.2` lie in the same component of
`G[s.2 ⊕ s'.2]`.

The hypothesis `hW'` is essential: for the key `(0, 1)` the separators can lie in two components
(`separators_components_le` is the statement that survives for every key).  The local statement
in the work package, that consecutive separators share a neighbour in `s.2 ∖ s'.2`, is false and
is not claimed: the two separators of one step may be joined by a path of length `4`
(`SeparatorData.comp_JK`). -/
theorem separators_sameComponent (hclaw : G.IsClawFree) {s s' : Finset V × Finset V}
    (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s') (Q : G.OddBlock s.1 s'.1)
    (hQ : Q.RunsFrom s)
    (hW' : ((Q.support ∩ G.matchedW s' s).card = 0 ∧ (Q.support ∩ G.crossedW s' s).card = 0) ∨
      ((Q.support ∩ G.matchedW s' s).card = 1 ∧ (Q.support ∩ G.crossedW s' s).card = 1))
    {u v : V} (hu : u ∈ Q.separators s'.2) (hv : v ∈ Q.separators s'.2) :
    v ∈ G.inducedComponentSet ↑(symmDiff s.2 s'.2) u := by
  obtain ⟨D, hB, hB', hSep, hM, hX⟩ := Q.exists_separatorData hs hs' hQ
  obtain ⟨R, T, hR, hT, hRT, hconn⟩ := D.exists_roots hclaw
  have hcard := D.card_unbal_add_le (Q.support ∩ G.matchedW s' s) (Q.support ∩ G.crossedW s' s) T
    hT hM hX
  have hR1 : R.card ≤ 1 := by
    rcases hW' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have hU : (↑(symmDiff s.2 s'.2) : Set V) = D.B ∆ D.B' := by
    rw [hB, hB', Finset.coe_symmDiff]
  obtain ⟨r, hr, hru⟩ := hconn u ((hSep u).2 hu)
  obtain ⟨r', hr', hrv⟩ := hconn v ((hSep v).2 hv)
  obtain rfl := Finset.card_le_one.1 hR1 r hr r' hr'
  rw [hU]
  exact D.comp_trans hru (D.comp_symm hrv)

end OddBlock

end SimpleGraph
