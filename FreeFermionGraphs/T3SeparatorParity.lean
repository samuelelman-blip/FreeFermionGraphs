import FreeFermionGraphs.T3BlockStep
import FreeFermionGraphs.T3PairingIndexCount
import FreeFermionGraphs.T3InteractionSymm

/-!
# Separator parity and the requirement lemma

This module proves the local parity identities and the *requirement lemma* of the synthesised
proof of Theorem 1(iii) of arXiv 2305.15625 v1 (label `theorem:conservedcharges`), package T3-23.
They concern a *side-1 block* `Q : OddBlock s.1 s'.1` of two hole-class states `s = (A, B)`,
`s' = (A', B')` (the colouring classes of the even holes `C = A ∪ B` and `C' = A' ∪ B'`): an induced
path `j_0 k_0 j_1 k_1 … j_{ℓ-1} k_{ℓ-1}` with `j_t ∈ A' ∖ A`, `k_t ∈ A ∖ A'`, which is a whole
component of `G[A ⊕ A']`.  The block *runs from `s`* when its word is a clone run out of `s`
(`OddBlock.RunsFrom`).  A *separator* of `Q` in a class `Z` is a vertex `v ∈ Z` which obstructs a
step `(j_t, k_t)`, i.e. `v = k_t` or `v` is adjacent to exactly one of `j_t`, `k_t`
(`OddBlock.separators`).  We write `W = matchedW s s' ∪ crossedW s s'` for the set of vertices of
`C'` whose term anticommutes with `h_C` (v1 Definition 20
`definition:anticommutingdependentsubsets`, L996-1013, and
`anticommutingVertices_eq_matchedW_union_crossedW`) and `W' = matchedW s' s ∪ crossedW s' s` for the
set of vertices of `C` which anticommute with `h_{C'}`.

The facts are the block-level form of the commutation count of v1 L1219-1233 ("the commutation of
`h_{P^{(r)}}` with `h_C` counts the `W`-vertices of the path") and of the base case (i) of the proof
of Theorem 1(iii), L1814-1829.  v1 never states them as separate lemmas; "`|W ∩ ∂O|` is odd" is used
there without proof, and (d) below is its closed form for one block.

## Main results

* (a) `OddBlock.separators_inter_fst_eq_empty`: `Q` has no separator in `s.2` (these are exactly the
  forward conditions of the block step lemma `OddBlock.classRun_iff`).
* (b) `OddBlock.crossCount_carrier_mod_two`: `c(Q, C) ≡ |Q ∩ W| (mod 2)`, where `c` is
  `SimpleGraph.crossCount`.  A vertex of `Q ∩ C` has two neighbours on the hole, and a vertex of `Q`
  outside `C` (a `j_t`) has an odd number of neighbours in `C` iff it lies in `W` (claw-freeness).
* (c) `OddBlock.crossCount_component_mod_two`: for a component `R` of `G[s.2 ⊕ s'.2]`,
  `c(R, Q) ≡ Σ_t #{v ∈ R ∩ s'.2 : v = k_t or v separates (j_t, k_t)} (mod 2)`.  No
  claw-freeness; the forward conditions of `Q` make `R ∩ s.2` irrelevant, and for `v ∈ R ∩ s'.2` the
  parity of `[v ~ j_t] + [v ~ k_t]` is the indicator that `v` is `k_t` or separates the step.
* (d) `OddBlock.separatorIncidence_mod_two`: `c(Q, s'.2) ≡ 1 + |Q ∩ W'| (mod 2)`.  This is the
  closed form, for one block, of the unproved "`|W ∩ ∂O|` odd" of v1.  The `1` is the last removed
  vertex `k_{ℓ-1}`, which has a single neighbour in `s'.1` (its predecessor on the path) and
  therefore lies outside `C'`; every other `k_t` has two.  The proof is direct (a per-vertex parity
  count, `card_filter_snd_adj_mod_two`, summed over the support) and does not use the forward
  conditions: the statement without the running hypothesis is
  `OddBlock.crossCount_support_snd_mod_two`, and `separatorIncidence_mod_two` keeps `Q.RunsFrom s`
  only to match the signature recorded in the work package.
* (e) `OddBlock.requires_contains_separator` (**requirement lemma**): let `D₁` be a palindromic
  deformation at `(s.1 ⊕ Q, s.2; s')` and `R` a side-2 block of `D₁` one of whose steps `(j', k')`
  has its introduced vertex `j'` equal to a removed vertex `k ∈ Q ∩ s.1` of `Q`, or is separated by
  such a `k` (`k ≠ j', k'` adjacent to exactly one of `j', k'`).  Then `R` contains a separator of
  `Q` in `s'.2`: namely `j'` itself.  The proof is the case analysis on `k` using the forward
  condition of `Q` (`j_t ~ v ↔ k_t ~ v` for `v ∈ s.2`) and the forward and backward conditions of
  `R` in `D₁` (`FPDeformation.Palindromic.stepConds_inr`) against the vertex `j_t`, which lies in no
  side-1 block of `D₁` and so stays in both first classes.

Claw-freeness is used only in (b) and (d) (through
`anticommutingVertices_eq_matchedW_union_crossedW`); (a), (c) and (e) are purely local.
-/

open scoped symmDiff

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace OddBlock

variable [DecidableEq V] {s s' : Finset V × Finset V}

/-! ### The forward conditions of a running side-1 block -/

/-- A side-1 block which runs from `s` satisfies the second-class clone conditions against `s.2`
(the forward block step lemma `OddBlock.classRun_iff`, in the direction needed here, which uses only
that the two classes of `s` are disjoint): every step `(j, k)` has `j ∉ s.2` and
`Γ_{s.2}(j) = Γ_{s.2}(k)`. -/
theorem forward_cond_of_runsFrom (hs : G.IsHoleClasses s) (Q : G.OddBlock s.1 s'.1)
    (hQ : Q.RunsFrom s) :
    ∀ p ∈ Q.word, p.1 ∉ s.2 ∧ ∀ v ∈ s.2, (G.Adj p.1 v ↔ G.Adj p.2 v) := by
  obtain ⟨t', h⟩ := hQ
  have hPA : s.1 ∩ Q.support = Q.support ∩ s.1 := Finset.inter_comm _ _
  have h0 : G.ClassRun (Q.stateA s.1 0, s.2) (Q.word.drop 0) t' := by simpa using h
  obtain ⟨hc, -⟩ := Q.cond_of_classRun_drop hs.disjoint hPA Q.word.length 0 (by omega) t' h0
  intro p hp
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hp
  exact hc m hm (Nat.zero_le _)

/-! ### (a) No separator in the second class -/

/-- **(a) A running side-1 block has no separator in `s.2`.**  A removed vertex `k_t` lies in `s.1`,
hence outside `s.2`; and a vertex of `s.2` is adjacent to both or to neither of `j_t`, `k_t`, by the
forward conditions. -/
theorem separators_inter_fst_eq_empty (hs : G.IsHoleClasses s) (Q : G.OddBlock s.1 s'.1)
    (hQ : Q.RunsFrom s) : Q.separators s.2 = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro v hv
  obtain ⟨hvB, p, hp, h⟩ := mem_separators.1 hv
  obtain ⟨-, hcond⟩ := forward_cond_of_runsFrom hs Q hQ p hp
  rcases h with rfl | ⟨-, -, hne⟩
  · exact Finset.disjoint_left.1 hs.disjoint (Finset.mem_sdiff.1 (snd_mem hp)).1 hvB
  · exact hne (hcond v hvB)

/-! ### Counting incidences -/

/-- A vertex `x` of the carrier of a hole-class state has exactly two neighbours in the carrier
(its two neighbours on the hole), so `c(x, C)` is even. -/
theorem card_filter_carrier_of_mem (hs : G.IsHoleClasses s) [DecidableRel G.Adj] {x : V}
    (hx : x ∈ s.1 ∪ s.2) : ((s.1 ∪ s.2).filter (G.Adj x)).card = 2 := by
  rw [← adjacencyCount_coe_finset, hs.adjacencyCount_eq]
  exact hs.card_filter_adj_fst_add_snd hx

omit [DecidableEq V] in
/-- `AnticommutesWithSet` for a finset, as the parity of a filter cardinality. -/
theorem anticommutesWithSet_iff_card_filter [DecidableRel G.Adj] (x : V) (C : Finset V) :
    G.AnticommutesWithSet x (↑C : Set V) ↔ (C.filter (G.Adj x)).card % 2 = 1 := by
  unfold AnticommutesWithSet
  rw [adjacencyCount_coe_finset]

/-- A vertex of the support of a block of `G[X ⊕ Y]` lies in `X` or in `Y`. -/
theorem mem_or_mem_of_mem_support {X Y : Finset V} (Q : G.OddBlock X Y) {x : V}
    (hx : x ∈ Q.support) : x ∈ X ∨ x ∈ Y := by
  rcases mem_support_of_mem_Y hx with h | h
  · exact Or.inr h.1
  · exact Or.inl h.1

/-- A sum over the support of a block is the sum over the steps of its word. -/
theorem sum_support_eq {X Y : Finset V} (Q : G.OddBlock X Y) (f : V → ℕ) :
    ∑ x ∈ Q.support, f x = (Q.word.map fun p => f p.1 + f p.2).sum := by
  have key : ∀ w : List (V × V),
      ((wordVertices w).map f).sum = (w.map fun p => f p.1 + f p.2).sum := by
    intro w
    induction w with
    | nil => simp
    | cons p w ih => simp [wordVertices_cons, ih, add_assoc]
  rw [← toFinset_wordVertices, List.sum_toFinset f Q.nodup_wordVertices, key]

/-- A list sum modulo two only depends on the summands modulo two. -/
private theorem list_sum_mod_two_congr {α : Type*} (l : List α) (f g : α → ℕ)
    (h : ∀ a ∈ l, f a % 2 = g a % 2) : (l.map f).sum % 2 = (l.map g).sum % 2 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [Nat.add_mod, ih (fun b hb => h b (List.mem_cons_of_mem _ hb)), h a (List.mem_cons_self ..),
      ← Nat.add_mod]

/-! ### (b) The carrier incidence -/

/-- **(b) Parity of the incidence of a side-1 block with the carrier `C`** (v1 L1219-1233: the
commutation of `h_{P}` with `h_C` counts the `W`-vertices of `P`):
`c(Q, C) ≡ |Q ∩ W| (mod 2)`, with `W = matchedW s s' ∪ crossedW s s'`.

A vertex of `Q ∩ C` has two neighbours on the hole and is not in `W ⊆ C' ∖ C`; a vertex of `Q`
outside `C` lies in `A'` (the support is in `A ∪ A'`) and has an odd number of neighbours in `C`
iff it is in `W` (`anticommutingVertices_eq_matchedW_union_crossedW`, claw-freeness). -/
theorem crossCount_carrier_mod_two (hclaw : G.IsClawFree) (hs : G.IsHoleClasses s)
    (hs' : G.IsHoleClasses s') (Q : G.OddBlock s.1 s'.1) :
    G.crossCount Q.support (s.1 ∪ s.2) % 2 =
      (Q.support ∩ (G.matchedW s s' ∪ G.crossedW s s')).card % 2 := by
  classical
  rw [crossCount_eq_sum_card_filter, sum_mod_two_eq_card_filter_odd]
  have hW := (anticommutingVertices_eq_matchedW_union_crossedW hclaw hs hs').1
  have hWC : ∀ y, y ∈ G.matchedW s s' ∪ G.crossedW s s' → y ∉ s.1 ∪ s.2 := fun y hy => by
    rcases Finset.mem_union.1 hy with h | h
    · exact (Finset.mem_sdiff.1 (matchedW_subset_sdiff h)).2
    · exact (Finset.mem_sdiff.1 (crossedW_subset_sdiff h)).2
  have key : ∀ x ∈ Q.support, ((s.1 ∪ s.2).filter (G.Adj x)).card % 2 = 1 ↔
      x ∈ G.matchedW s s' ∪ G.crossedW s s' := by
    intro x hx
    have hanti := anticommutesWithSet_iff_card_filter (G := G) x (s.1 ∪ s.2)
    have hmem : x ∈ G.matchedW s s' ∪ G.crossedW s s' ↔
        x ∈ s'.1 ∪ s'.2 ∧ G.AnticommutesWithSet x (↑(s.1 ∪ s.2) : Set V) := by
      rw [← hW, mem_anticommutingVertices]
    by_cases hxC : x ∈ s.1 ∪ s.2
    · have h2 := card_filter_carrier_of_mem hs hxC
      constructor
      · intro h
        rw [h2] at h
        omega
      · intro h
        exact absurd hxC (hWC x h)
    · have hxA' : x ∈ s'.1 := by
        rcases mem_or_mem_of_mem_support Q hx with h | h
        · exact absurd (Finset.mem_union_left _ h) hxC
        · exact h
      rw [hmem, ← hanti]
      exact ⟨fun h => ⟨Finset.mem_union_left _ hxA', h⟩, fun h => h.2⟩
  have hfil : Q.support.filter (fun x => ((s.1 ∪ s.2).filter (G.Adj x)).card % 2 = 1) =
      Q.support ∩ (G.matchedW s s' ∪ G.crossedW s s') := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨hx, h⟩
      exact ⟨hx, (key x hx).1 h⟩
    · rintro ⟨hx, h⟩
      exact ⟨hx, (key x hx).2 h⟩
  rw [hfil]

/-! ### (c) The incidence of a component of the second side graph -/

/-- A double sum over a finset and a list can be exchanged. -/
private theorem sum_finset_list_sum_comm {α β : Type*} (R : Finset β) (l : List α) (g : β → α → ℕ) :
    ∑ v ∈ R, (l.map (g v)).sum = (l.map fun a => ∑ v ∈ R, g v a).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Finset.sum_add_distrib, ih]

omit [DecidableEq V] in
/-- The parity of `[v ~ a] + [v ~ b]` is the indicator that `v` is adjacent to exactly one of
`a`, `b`. -/
private theorem adj_indicator_add_mod_two [DecidableRel G.Adj] (a b v : V) :
    ((if G.Adj v a then 1 else 0) + (if G.Adj v b then 1 else 0)) % 2 =
      if ¬(G.Adj a v ↔ G.Adj b v) then 1 else 0 := by
  have h1 : G.Adj v a ↔ G.Adj a v := G.adj_comm v a
  have h2 : G.Adj v b ↔ G.Adj b v := G.adj_comm v b
  by_cases ha : G.Adj a v <;> by_cases hb : G.Adj b v <;> simp [h1, h2, ha, hb]

/-- **(c) Parity of the incidence of a component of `G[s.2 ⊕ s'.2]` with a running side-1 block**
(v1 L1219-1233; base case (i), L1814-1829):
`c(R, Q) ≡ Σ_t #{v ∈ R ∩ s'.2 : v = k_t or v separates (j_t, k_t)} (mod 2)`.

Expanding `c(R, Q) = Σ_{v ∈ R} Σ_t ([v ~ j_t] + [v ~ k_t])`, the vertices of `R ∩ s.2` contribute
nothing because no vertex of `s.2` separates a step of a running block (the forward conditions),
and for `v ∈ R ∩ s'.2` the parity of `[v ~ j_t] + [v ~ k_t]` is `1` exactly when `v` is adjacent to
exactly one of `j_t`, `k_t`, which for `v ∈ s'.2` (so `v ≠ j_t`) is the condition
"`v = k_t` or `v` separates `(j_t, k_t)`".  No claw-freeness is used, and of the component property
of `R` only `R ⊆ s.2 ⊕ s'.2`. -/
theorem crossCount_component_mod_two [DecidableRel G.Adj] (hs : G.IsHoleClasses s)
    (hs' : G.IsHoleClasses s') (Q : G.OddBlock s.1 s'.1) (hQ : Q.RunsFrom s) {R : Finset V}
    (hR : G.IsInducedComponent ↑(symmDiff s.2 s'.2) ↑R) :
    G.crossCount R Q.support % 2 =
      (Q.word.map fun p => (R.filter fun v => v ∈ s'.2 ∧
        (v = p.2 ∨ (v ≠ p.1 ∧ v ≠ p.2 ∧ ¬(G.Adj p.1 v ↔ G.Adj p.2 v)))).card).sum % 2 := by
  have hRsub : ∀ v ∈ R, v ∈ symmDiff s.2 s'.2 := fun v hv =>
    Finset.mem_coe.1 (hR.1 (Finset.mem_coe.2 hv))
  have hcond := forward_cond_of_runsFrom hs Q hQ
  have h1 : G.crossCount R Q.support = (Q.word.map fun p => ∑ v ∈ R,
      ((if G.Adj v p.1 then 1 else 0) + (if G.Adj v p.2 then 1 else 0))).sum := by
    rw [crossCount_eq_sum_sum]
    have : ∀ v ∈ R, ∑ t ∈ Q.support, (if G.Adj v t then 1 else 0) =
        (Q.word.map fun p => ((if G.Adj v p.1 then 1 else 0) +
          (if G.Adj v p.2 then 1 else 0))).sum := fun v _ =>
      sum_support_eq Q (fun t => if G.Adj v t then 1 else 0)
    rw [Finset.sum_congr rfl this, sum_finset_list_sum_comm]
  rw [h1]
  apply list_sum_mod_two_congr
  intro p hp
  have hp1 : p.1 ∈ s'.1 \ s.1 := fst_mem hp
  have hadj := adj_of_mem_word hp
  have hpt : ∀ v ∈ R, ((if G.Adj v p.1 then 1 else 0) + (if G.Adj v p.2 then 1 else 0)) % 2 =
      if (v ∈ s'.2 ∧ (v = p.2 ∨ (v ≠ p.1 ∧ v ≠ p.2 ∧ ¬(G.Adj p.1 v ↔ G.Adj p.2 v)))) then 1
      else 0 := by
    intro v hv
    rw [adj_indicator_add_mod_two]
    have hφ : (v ∈ s'.2 ∧ (v = p.2 ∨ (v ≠ p.1 ∧ v ≠ p.2 ∧ ¬(G.Adj p.1 v ↔ G.Adj p.2 v)))) ↔
        ¬(G.Adj p.1 v ↔ G.Adj p.2 v) := by
      rcases Finset.mem_symmDiff.1 (hRsub v hv) with ⟨hvB, hvB'⟩ | ⟨hvB', hvB⟩
      · have := (hcond p hp).2 v hvB
        simp only [hvB', false_and, false_iff, not_not]
        exact this
      · constructor
        · rintro ⟨-, rfl | ⟨-, -, h⟩⟩
          · intro h
            exact G.loopless.irrefl _ (h.1 hadj)
          · exact h
        · intro h
          refine ⟨hvB', ?_⟩
          by_cases hv2 : v = p.2
          · exact Or.inl hv2
          · refine Or.inr ⟨?_, hv2, h⟩
            rintro rfl
            exact Finset.disjoint_left.1 hs'.disjoint (Finset.mem_sdiff.1 hp1).1 hvB'
    simp only [hφ]
  have : (∑ v ∈ R, ((if G.Adj v p.1 then 1 else 0) + (if G.Adj v p.2 then 1 else 0))) % 2 =
      (R.filter fun v => v ∈ s'.2 ∧
        (v = p.2 ∨ (v ≠ p.1 ∧ v ≠ p.2 ∧ ¬(G.Adj p.1 v ↔ G.Adj p.2 v)))).card % 2 := by
    rw [Finset.sum_nat_mod, Finset.card_filter]
    rw [Finset.sum_congr rfl hpt]
  exact this

/-! ### (d) The incidence with the second class of the other hole -/

section Snd

variable {X Y : Finset V}

/-- The last vertex `p_{2ℓ-1} = k_{ℓ-1}` of a block. -/
def lastV (Q : G.OddBlock X Y) : V := Q.vtx (Q.path.card - 1)

theorem lastV_mem_support (Q : G.OddBlock X Y) : Q.lastV ∈ Q.support :=
  Q.vtx_mem_support (by have := Q.path.nonempty; omega)

/-- The vertices at even and odd positions are different from the last vertex, which sits at the odd
position `2ℓ - 1`. -/
theorem vtx_eq_lastV_iff (Q : G.OddBlock X Y) {i : ℕ} (hi : i < Q.path.card) :
    Q.vtx i = Q.lastV ↔ i + 1 = Q.path.card := by
  have hc : Q.path.card - 1 < Q.path.card := by have := Q.path.nonempty; omega
  constructor
  · intro h
    have := Q.vtx_injective_of_lt hi hc h
    have := Q.path.nonempty
    omega
  · intro h
    have : i = Q.path.card - 1 := by omega
    rw [this]
    rfl

/-- **The neighbours of a removed vertex in `Y`.**  A vertex `k = p_i` at an odd position of a block
of `G[X ⊕ Y]` (with `X` independent) has exactly one neighbour in `Y` (its predecessor `p_{i-1}`)
if it is the last vertex of the path, and exactly two (`p_{i-1}`, `p_{i+1}`) otherwise.  A neighbour
`a ∈ Y` of `k ∈ X` lies outside `X` (independence), hence in `X ⊕ Y`, hence in the component of
`k`, i.e. on the path. -/
theorem card_filter_snd_adj_vtx_odd [DecidableRel G.Adj] (hX : G.IsIndepSet (↑X : Set V))
    (Q : G.OddBlock X Y) {i : ℕ} (hi : i < Q.path.card) (ho : Odd i) :
    (Y.filter (G.Adj (Q.vtx i))).card = if i + 1 < Q.path.card then 2 else 1 := by
  obtain ⟨m, rfl⟩ := ho
  have hx : Q.vtx (2 * m + 1) ∈ X \ Y := Q.vtx_odd_mem hi ⟨m, rfl⟩
  have hlt0 : 2 * m < Q.path.card := by omega
  have hprevY : Q.vtx (2 * m) ∈ Y := (Finset.mem_sdiff.1 (Q.vtx_even_mem hlt0 (even_two_mul m))).1
  have hprevAdj : G.Adj (Q.vtx (2 * m + 1)) (Q.vtx (2 * m)) :=
    (Q.adj_vtx_iff hi hlt0).2 (by omega)
  have hsub : ∀ a ∈ Y, G.Adj (Q.vtx (2 * m + 1)) a →
      a = Q.vtx (2 * m) ∨ (2 * m + 2 < Q.path.card ∧ a = Q.vtx (2 * m + 2)) := by
    intro a haY hadj
    have haX : a ∉ X := fun haX =>
      hX (Finset.mem_coe.2 (Finset.mem_sdiff.1 hx).1) (Finset.mem_coe.2 haX) hadj.ne hadj
    have hasd : a ∈ (↑(symmDiff X Y) : Set V) := by
      rw [Finset.mem_coe, Finset.mem_symmDiff]
      exact Or.inr ⟨haY, haX⟩
    have hxs : Q.vtx (2 * m + 1) ∈ (↑Q.support : Set V) :=
      Finset.mem_coe.2 (Q.vtx_mem_support hi)
    have has := Q.isInducedComponent_support.2.2 hxs hasd hadj
    obtain ⟨n, hn, rfl⟩ := Q.vtx_lt_of_mem_support (Finset.mem_coe.1 has)
    rcases (Q.adj_vtx_iff hi hn).1 hadj with h | h
    · right
      refine ⟨by omega, ?_⟩
      rw [show n = 2 * m + 2 by omega]
    · left
      rw [show n = 2 * m by omega]
  by_cases hlast : 2 * m + 1 + 1 < Q.path.card
  · rw [if_pos hlast]
    have hlt2 : 2 * m + 2 < Q.path.card := by omega
    have hnextY : Q.vtx (2 * m + 2) ∈ Y :=
      (Finset.mem_sdiff.1 (Q.vtx_even_mem hlt2 ⟨m + 1, by omega⟩)).1
    have hnextAdj : G.Adj (Q.vtx (2 * m + 1)) (Q.vtx (2 * m + 2)) :=
      (Q.adj_vtx_iff hi hlt2).2 (by omega)
    have hset : Y.filter (G.Adj (Q.vtx (2 * m + 1))) = {Q.vtx (2 * m), Q.vtx (2 * m + 2)} := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨haY, hadj⟩
        rcases hsub a haY hadj with h | ⟨-, h⟩
        · exact Or.inl h
        · exact Or.inr h
      · rintro (rfl | rfl)
        · exact ⟨hprevY, hprevAdj⟩
        · exact ⟨hnextY, hnextAdj⟩
    rw [hset, Finset.card_pair]
    intro h
    have := Q.vtx_injective_of_lt hlt0 hlt2 h
    omega
  · rw [if_neg hlast]
    have hset : Y.filter (G.Adj (Q.vtx (2 * m + 1))) = {Q.vtx (2 * m)} := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨haY, hadj⟩
        rcases hsub a haY hadj with h | ⟨h, -⟩
        · exact h
        · omega
      · rintro rfl
        exact ⟨hprevY, hprevAdj⟩
    rw [hset, Finset.card_singleton]

/-- **Per-vertex parity of the incidence with `s'.2`.**  For a vertex `x` of a side-1 block `Q`,
the number of neighbours of `x` in `s'.2` has the parity of `[x ∈ W'] + [x = k_{ℓ-1}]`, where
`W' = matchedW s' s ∪ crossedW s' s`.

* An introduced vertex `j_t ∈ s'.1` has two neighbours in `s'.2` and is not in `W' ⊆ C ∖ C'`.
* A removed vertex `k_t ∈ s.1 ∖ s'.1` which lies in `s'.2` has no neighbour there, is not in `W'`,
  and has two neighbours in `s'.1`, so is not the last vertex.
* A removed vertex `k_t` outside `C'` has `|Γ_{s'.1}(k_t)| + |Γ_{s'.2}(k_t)|` neighbours in `C'`,
  an odd number iff `k_t ∈ W'` (claw-freeness); and `|Γ_{s'.1}(k_t)|` is `2`, or `1` for the last
  vertex. -/
theorem card_filter_snd_adj_mod_two [DecidableRel G.Adj] (hclaw : G.IsClawFree)
    (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s') (Q : G.OddBlock s.1 s'.1) {x : V}
    (hx : x ∈ Q.support) :
    (s'.2.filter (G.Adj x)).card % 2 =
      ((if x ∈ G.matchedW s' s ∪ G.crossedW s' s then 1 else 0) +
        (if x = Q.lastV then 1 else 0)) % 2 := by
  have hW := (anticommutingVertices_eq_matchedW_union_crossedW hclaw hs' hs).1
  have hWC : ∀ y, y ∈ G.matchedW s' s ∪ G.crossedW s' s → y ∉ s'.1 ∪ s'.2 := fun y hy => by
    rcases Finset.mem_union.1 hy with h | h
    · exact (Finset.mem_sdiff.1 (matchedW_subset_sdiff h)).2
    · exact (Finset.mem_sdiff.1 (crossedW_subset_sdiff h)).2
  obtain ⟨i, hi, rfl⟩ := Q.vtx_lt_of_mem_support hx
  have hceven := Q.even_card
  rw [Nat.even_iff] at hceven
  have hlast := Q.vtx_eq_lastV_iff hi
  rcases Nat.even_or_odd i with he | ho
  · -- an introduced vertex
    have hxY : Q.vtx i ∈ s'.1 \ s.1 := Q.vtx_even_mem hi he
    have h2 := hs'.card_filter_snd_of_mem_fst (Finset.mem_sdiff.1 hxY).1
    have hnW : Q.vtx i ∉ G.matchedW s' s ∪ G.crossedW s' s := fun h =>
      hWC _ h (Finset.mem_union_left _ (Finset.mem_sdiff.1 hxY).1)
    have hnl : ¬ Q.vtx i = Q.lastV := by
      rw [hlast]
      rw [Nat.even_iff] at he
      omega
    rw [h2, if_neg hnW, if_neg hnl]
  · -- a removed vertex
    have hxX : Q.vtx i ∈ s.1 \ s'.1 := Q.vtx_odd_mem hi ho
    have ha := card_filter_snd_adj_vtx_odd hs.isIndepSet_fst Q hi ho
    by_cases hxB' : Q.vtx i ∈ s'.2
    · have h2 := hs'.card_filter_fst_of_mem_snd hxB'
      have hsum := hs'.card_filter_adj_fst_add_snd (Finset.mem_union_right _ hxB')
      have hn0 : (s'.2.filter (G.Adj (Q.vtx i))).card = 0 := by omega
      have hi1 : i + 1 < Q.path.card := by
        by_contra hcon
        rw [if_neg hcon] at ha
        omega
      have hnW : Q.vtx i ∉ G.matchedW s' s ∪ G.crossedW s' s := fun h =>
        hWC _ h (Finset.mem_union_right _ hxB')
      have hnl : ¬ Q.vtx i = Q.lastV := by
        rw [hlast]
        omega
      rw [hn0, if_neg hnW, if_neg hnl]
    · have hxC' : Q.vtx i ∉ s'.1 ∪ s'.2 := by
        intro h
        rcases Finset.mem_union.1 h with h | h
        · exact (Finset.mem_sdiff.1 hxX).2 h
        · exact hxB' h
      have hmem : Q.vtx i ∈ G.matchedW s' s ∪ G.crossedW s' s ↔
          (Q.vtx i ∈ s.1 ∪ s.2 ∧ G.AnticommutesWithSet (Q.vtx i) (↑(s'.1 ∪ s'.2) : Set V)) := by
        rw [← hW, mem_anticommutingVertices]
      have hanti := anticommutesWithSet_iff_card_filter (G := G) (Q.vtx i) (s'.1 ∪ s'.2)
      have hcard : ((s'.1 ∪ s'.2).filter (G.Adj (Q.vtx i))).card =
          (s'.1.filter (G.Adj (Q.vtx i))).card + (s'.2.filter (G.Adj (Q.vtx i))).card := by
        rw [Finset.filter_union, Finset.card_union_of_disjoint
          (Finset.disjoint_filter_filter hs'.disjoint)]
      have hxC : Q.vtx i ∈ s.1 ∪ s.2 := Finset.mem_union_left _ (Finset.mem_sdiff.1 hxX).1
      have hmem' : Q.vtx i ∈ G.matchedW s' s ∪ G.crossedW s' s ↔
          ((s'.1.filter (G.Adj (Q.vtx i))).card +
            (s'.2.filter (G.Adj (Q.vtx i))).card) % 2 = 1 := by
        rw [hmem, hanti, hcard]
        exact ⟨fun h => h.2, fun h => ⟨hxC, h⟩⟩
      by_cases hW' : Q.vtx i ∈ G.matchedW s' s ∪ G.crossedW s' s
      · have h1 := hmem'.1 hW'
        by_cases hl : i + 1 < Q.path.card
        · rw [if_pos hl] at ha
          have hnl : ¬ Q.vtx i = Q.lastV := by
            rw [hlast]
            omega
          rw [if_pos hW', if_neg hnl]
          omega
        · rw [if_neg hl] at ha
          have hl' : Q.vtx i = Q.lastV := by
            rw [hlast]
            omega
          rw [if_pos hW', if_pos hl']
          omega
      · have h1 : ¬ ((s'.1.filter (G.Adj (Q.vtx i))).card +
            (s'.2.filter (G.Adj (Q.vtx i))).card) % 2 = 1 := fun h => hW' (hmem'.2 h)
        by_cases hl : i + 1 < Q.path.card
        · rw [if_pos hl] at ha
          have hnl : ¬ Q.vtx i = Q.lastV := by
            rw [hlast]
            omega
          rw [if_neg hW', if_neg hnl]
          omega
        · rw [if_neg hl] at ha
          have hl' : Q.vtx i = Q.lastV := by
            rw [hlast]
            omega
          rw [if_neg hW', if_pos hl']
          omega

/-- **(d), without the running hypothesis.**  For a side-1 block `Q` of `G[s.1 ⊕ s'.1]` (claw-free
`G`, hole-class states `s`, `s'`), `c(Q, s'.2) ≡ 1 + |Q ∩ W'| (mod 2)` with
`W' = matchedW s' s ∪ crossedW s' s`.  Summing `card_filter_snd_adj_mod_two` over the support: the
terms `[x ∈ W']` add up to `|Q ∩ W'|` and the terms `[x = k_{ℓ-1}]` to `1`. -/
theorem crossCount_support_snd_mod_two (hclaw : G.IsClawFree) (hs : G.IsHoleClasses s)
    (hs' : G.IsHoleClasses s') (Q : G.OddBlock s.1 s'.1) :
    G.crossCount Q.support s'.2 % 2 =
      (1 + (Q.support ∩ (G.matchedW s' s ∪ G.crossedW s' s)).card) % 2 := by
  classical
  rw [crossCount_eq_sum_card_filter, Finset.sum_nat_mod,
    Finset.sum_congr rfl (fun x hx => card_filter_snd_adj_mod_two hclaw hs hs' Q hx),
    ← Finset.sum_nat_mod, Finset.sum_add_distrib, ← Finset.card_filter, ← Finset.card_filter,
    Finset.filter_mem_eq_inter]
  have hsingle : Q.support.filter (fun x => x = Q.lastV) = {Q.lastV} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · exact fun h => h.2
    · rintro rfl
      exact ⟨Q.lastV_mem_support, rfl⟩
  rw [hsingle, Finset.card_singleton, add_comm]

/-- **(d) The closed form of v1's "`|W ∩ ∂O|` odd" for one block** (v1 L1219-1233, base case (i)
L1814-1829; package T3-23):
`c(Q, s'.2) ≡ 1 + |Q ∩ W'| (mod 2)` with `W' = matchedW s' s ∪ crossedW s' s` the vertices of `C`
whose term anticommutes with `h_{C'}`.  The `1` is the C-end `k_{ℓ-1}` of the path, which has a
single neighbour in `s'.1` and so lies outside `C'`.

The running hypothesis `Q.RunsFrom s` is not needed (`crossCount_support_snd_mod_two`); it is kept
to match the signature recorded in the work package. -/
theorem separatorIncidence_mod_two (hclaw : G.IsClawFree) (hs : G.IsHoleClasses s)
    (hs' : G.IsHoleClasses s') (Q : G.OddBlock s.1 s'.1) (_hQ : Q.RunsFrom s) :
    G.crossCount Q.support s'.2 % 2 =
      (1 + (Q.support ∩ (G.matchedW s' s ∪ G.crossedW s' s)).card) % 2 :=
  crossCount_support_snd_mod_two hclaw hs hs' Q

end Snd

/-! ### (e) The requirement lemma -/

/-- **(e) Requirement lemma** (v1 L1219-1233, base case (i) L1814-1829; package T3-23).  Let `Q` be
a side-1 block running from `s`, let `D₁` be a palindromic deformation at `(s.1 ⊕ Q, s.2; s')`, and
let `R` be a side-2 block of `D₁` one of whose steps `(j', k')` is *obstructed by a removed vertex
of `Q`*: there is `k ∈ Q ∩ s.1` (so `k = k_t` for some step `(j_t, k_t)` of `Q`) with `k = j'`, or
with `k ≠ j', k'` adjacent to exactly one of `j'`, `k'`.  Then `R` contains a separator of `Q` in
`s'.2`, namely `j'` itself.

Proof.  If `k = j'` then `j' = k_t` is a separator of the step `(j_t, k_t)`.  Otherwise `k_t`
separates `(j', k')`, and we use the vertex `j_t`, which lies in `(s.1 ⊕ Q) ∩ s'.1`.  The side-1
blocks of `D₁` are components of `G[(s.1 ⊕ Q) ⊕ s'.1]`, so none of them contains `j_t`; hence `j_t`
is in the first class both when `R` runs forward from `(s.1 ⊕ T₁(pre), …)` and when it runs backward
from `(s'.1 ⊕ T₁(post), …)`, and the first and second parts of `stepConds_inr` apply to it.

* `k_t ~ k'`, `k_t ≁ j'`: the forward condition of `Q` against `k' ∈ s.2` gives `j_t ~ k'`; the
  forward condition of `R` against `j_t` gives `j_t ~ j'`.  Then `j' ≠ j_t, k_t` is adjacent to
  `j_t` but not to `k_t`: it separates `(j_t, k_t)`.
* `k_t ~ j'`, `k_t ≁ k'`: if `j_t ≁ j'`, then `j'` separates `(j_t, k_t)`.  Otherwise the backward
  condition of `R` against `j_t` gives `j_t ~ k'`, and then the forward condition of `Q` gives
  `k_t ~ k'`, a contradiction.

No claw-freeness is used. -/
theorem requires_contains_separator (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s')
    (Q : G.OddBlock s.1 s'.1) (hQ : Q.RunsFrom s)
    {D₁ : G.FPDeformation (symmDiff s.1 Q.support, s.2) s'} (hD₁ : D₁.Palindromic)
    {R : G.OddBlock s.2 s'.2} (hR : Sum.inr R ∈ D₁.blocks)
    (hsep : ∃ p ∈ R.word, ∃ k ∈ Q.support ∩ s.1,
      k = p.1 ∨ (k ≠ p.1 ∧ k ≠ p.2 ∧ ¬(G.Adj p.1 k ↔ G.Adj p.2 k))) :
    (R.support ∩ Q.separators s'.2).Nonempty := by
  classical
  -- the intermediate state `(s.1 ⊕ Q, s.2)` is a hole-class state
  have hs₁ : G.IsHoleClasses (symmDiff s.1 Q.support, s.2) := by
    obtain ⟨t', hrun⟩ := hQ
    have hrun' : G.ClassRun (s.1, s.2) Q.word t' := hrun
    have hend := classRun_end_of_indep hs.disjoint Q (Finset.inter_comm _ _) hrun'
    rw [← hend]
    exact hrun.isHoleClasses hs
  have hcond := forward_cond_of_runsFrom hs Q hQ
  obtain ⟨pre, post, hdec⟩ := List.append_of_mem hR
  obtain ⟨hF, hBk⟩ := FPDeformation.Palindromic.stepConds_inr hs₁ hs' hD₁ hdec
  obtain ⟨p, hp, k, hk, hcase⟩ := hsep
  obtain ⟨hkQ, hkA⟩ := Finset.mem_inter.1 hk
  -- `k` is the removed vertex of a step `q` of `Q`
  obtain ⟨q, hq, hkq⟩ : ∃ q ∈ Q.word, k = q.2 := by
    obtain ⟨q, hq, h | h⟩ := mem_support_iff_exists_mem_word.1 hkQ
    · exact absurd hkA (by rw [h]; exact (Finset.mem_sdiff.1 (fst_mem hq)).2)
    · exact ⟨q, hq, h⟩
  obtain ⟨hqB, hqcond⟩ := hcond q hq
  have hq1 : q.1 ∈ s'.1 \ s.1 := fst_mem hq
  have hp1 : p.1 ∈ s'.2 \ s.2 := fst_mem hp
  have hp2 : p.2 ∈ s.2 \ s'.2 := snd_mem hp
  have hq1sd : q.1 ∈ symmDiff s.1 Q.support :=
    Finset.mem_symmDiff.2 (Or.inr ⟨fst_mem_support hq, (Finset.mem_sdiff.1 hq1).2⟩)
  -- the vertex `q.1` lies in no block of `D₁`
  have hq1pre : q.1 ∉ SideBlock.listToggle₁ pre := fun h => by
    have := SideBlock.listToggle₁_subset pre h
    rcases Finset.mem_symmDiff.1 this with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact h2 (Finset.mem_sdiff.1 hq1).1
    · exact h2 hq1sd
  have hq1post : q.1 ∉ SideBlock.listToggle₁ post := fun h => by
    have := SideBlock.listToggle₁_subset post h
    rcases Finset.mem_symmDiff.1 this with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact h2 (Finset.mem_sdiff.1 hq1).1
    · exact h2 hq1sd
  have hAcur : q.1 ∈ symmDiff (symmDiff s.1 Q.support) (SideBlock.listToggle₁ pre) :=
    Finset.mem_symmDiff.2 (Or.inl ⟨hq1sd, hq1pre⟩)
  have hA'cur : q.1 ∈ symmDiff s'.1 (SideBlock.listToggle₁ post) :=
    Finset.mem_symmDiff.2 (Or.inl ⟨(Finset.mem_sdiff.1 hq1).1, hq1post⟩)
  have hFj := (hF p hp).2 q.1 hAcur
  have hBkj := (hBk p hp).2 q.1 hA'cur
  have hne11 : p.1 ≠ q.1 := fun h =>
    Finset.disjoint_left.1 hs'.disjoint (Finset.mem_sdiff.1 hq1).1
      (h ▸ (Finset.mem_sdiff.1 hp1).1)
  refine ⟨p.1, Finset.mem_inter.2 ⟨fst_mem_support hp, mem_separators.2 ⟨(Finset.mem_sdiff.1 hp1).1,
    q, hq, ?_⟩⟩⟩
  rcases hcase with h | ⟨hne1, hne2, hnot⟩
  · exact Or.inl (h.symm.trans hkq)
  · right
    rw [hkq] at hne1 hne2 hnot
    refine ⟨hne11, fun h => hne1 h.symm, ?_⟩
    have hqk' := hqcond p.2 (Finset.mem_sdiff.1 hp2).1
    by_cases hA : G.Adj p.1 q.2
    · -- `k_t ~ j'`, so `k_t ≁ k'`
      have hB : ¬ G.Adj p.2 q.2 := fun hB => hnot ⟨fun _ => hB, fun _ => hA⟩
      have hnj : ¬ G.Adj p.1 q.1 := by
        intro hj
        have h1 : G.Adj p.2 q.1 := hBkj.2 hj
        have h2 : G.Adj q.2 p.2 := hqk'.1 h1.symm
        exact hB h2.symm
      intro hiff
      exact hnj (hiff.2 hA.symm).symm
    · -- `k_t ~ k'`, `k_t ≁ j'`
      have hB : G.Adj p.2 q.2 := by
        by_contra hB
        exact hnot ⟨fun h => absurd h hA, fun h => absurd h hB⟩
      have h1 : G.Adj q.1 p.2 := hqk'.2 hB.symm
      have h2 : G.Adj p.1 q.1 := hFj.2 h1.symm
      intro hiff
      exact hA (hiff.1 h2.symm).symm

end OddBlock

end SimpleGraph
