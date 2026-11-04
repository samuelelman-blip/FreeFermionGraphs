import FreeFermionGraphs.T3OddBlock

/-!
# The block step lemma: when does an odd block run?

This module is the local content behind the manuscript's statement that, in a fixed-pairing-type
deformation (arXiv 2305.15625 v1, Definition 19 `definition:fixedpairingtypedeformation`,
L978-994), the vertices of a path `P^{(r)}` are deformed one after the other,
`j_{s-1}^{(r)} ≺_{C^{(r,s-1)}} k_{s-1}^{(r)}` (v1 L992; the base case (i) of the proof of
Theorem 1(iii), L1808-1830, checks exactly the clone conditions below; Fig.
`figure:deformationsequence`, L756-766).

Throughout, `(A, B)` is a hole-class state (the two colouring classes of an even hole `C = A ∪ B`),
`X` and `Y` are independent sets with `A ⊆ X ∪ Y` (`X` plays the role of the colour class `C_j`
and `Y` that of the colour class `C'_{σ(j)}` of the other hole), and `P` is an `OddBlock X Y`,
a path component of `G[X ⊕ Y]` with word `[(j_0, k_0), …, (j_{ℓ-1}, k_{ℓ-1})]`.  The block is
*untoggled in `A`* when `A ∩ supp P = supp P ∩ X`: the vertices `k_s ∈ X ∖ Y` of the block lie in
`A` and the vertices `j_s ∈ Y ∖ X` do not.

## Main results

* `OddBlock.classRun_iff` (forward step lemma, v1 L992): `P` runs from `(A, B)` if and only if
  every step `(j, k)` of `P` has `j ∉ B` and `Γ_B(j) = Γ_B(k)` (`∀ v ∈ B, j ~ v ↔ k ~ v`).  The
  `A`-part of each clone condition is automatic: `k_s` is not adjacent to the other vertices of
  the current first class because `A` is independent and `P` is an induced path, and `j_s` is not
  adjacent to them because `Y` is independent, `P` is a *whole* component of `G[X ⊕ Y]` and the
  only vertices of `X ∖ Y` on `P` adjacent to `j_s` are `k_s` and `k_{s-1}` (already removed).
* `OddBlock.classRun_end`: the run ends in `(A ⊕ supp P, B)` (the carrier `C^{(r)}` of v1
  Definition 19, with its colouring).
* `OddBlock.runsBack_iff` (backward step lemma): the reversed word of `P` runs from a state
  `(A', B')` with `A' ∩ supp P = supp P ∩ Y` if and only if every step `(j, k)` has `k ∉ B'` and
  `Γ_{B'}(k) = Γ_{B'}(j)`.  It is the forward lemma for the reversed block
  `P.reverse : OddBlock Y X`, whose word is `reverseWord P.word`.

Claw-freeness is not used anywhere in this module.  Of the hole-class hypothesis only the
disjointness of `A` and `B` and the independence of `A` are used
(`classRun_iff_of_indep`, `classRun_end_of_indep`).
-/

open scoped symmDiff

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- The *second-class clone condition* of a step `(j, k)` of a block against the class `B`: the
introduced vertex `j` is not in `B`, and `j` and `k` have the same neighbours in `B`
(`Γ_B(j) = Γ_B(k)`).  This is the only part of the clone condition `j ≺_{A_t ∪ B} k` which is not
automatic (v1 L992, L1808-1830). -/
def BlockStepCond (G : SimpleGraph V) (B : Finset V) (p : V × V) : Prop :=
  p.1 ∉ B ∧ ∀ v ∈ B, (G.Adj p.1 v ↔ G.Adj p.2 v)

namespace OddBlock

variable [DecidableEq V] {X Y : Finset V}

/-! ### Natural-number indexing of the path -/

/-- The `i`-th vertex `p_i` of the block, indexed by a natural number (a junk value, the first
vertex, is used outside the range). -/
def vtx (P : G.OddBlock X Y) (i : ℕ) : V :=
  if h : i < P.path.card then P.path.vertex ⟨i, h⟩ else P.first

theorem vtx_eq (P : G.OddBlock X Y) {i : ℕ} (h : i < P.path.card) :
    P.vtx i = P.path.vertex ⟨i, h⟩ := by
  simp [vtx, h]

theorem vtx_injective_of_lt (P : G.OddBlock X Y) {i i' : ℕ} (hi : i < P.path.card)
    (hi' : i' < P.path.card) (h : P.vtx i = P.vtx i') : i = i' := by
  rw [vtx_eq P hi, vtx_eq P hi'] at h
  exact congrArg Fin.val (P.path.injective h)

/-- Consecutive vertices of the block are adjacent and no others (the block is an induced path). -/
theorem adj_vtx_iff (P : G.OddBlock X Y) {i i' : ℕ} (hi : i < P.path.card)
    (hi' : i' < P.path.card) : G.Adj (P.vtx i) (P.vtx i') ↔ i + 1 = i' ∨ i' + 1 = i := by
  rw [vtx_eq P hi, vtx_eq P hi']
  exact P.path.adj_iff _ _

theorem vtx_mem_support (P : G.OddBlock X Y) {i : ℕ} (hi : i < P.path.card) :
    P.vtx i ∈ P.support := by
  rw [vtx_eq P hi]
  exact P.vertex_mem_support _

/-- The vertices at even positions lie in `Y ∖ X` (they are the introduced vertices `j`). -/
theorem vtx_even_mem (P : G.OddBlock X Y) {i : ℕ} (hi : i < P.path.card) (he : Even i) :
    P.vtx i ∈ Y \ X := by
  rw [vtx_eq P hi]
  exact P.mem_Y ⟨i, hi⟩ he

/-- The vertices at odd positions lie in `X ∖ Y` (they are the removed vertices `k`). -/
theorem vtx_odd_mem (P : G.OddBlock X Y) {i : ℕ} (hi : i < P.path.card) (ho : Odd i) :
    P.vtx i ∈ X \ Y := by
  rw [vtx_eq P hi]
  exact P.mem_X ⟨i, hi⟩ ho

theorem two_mul_succ_lt (P : G.OddBlock X Y) {n : ℕ} (hn : n < P.word.length) :
    2 * n + 1 < P.path.card := by
  have h := P.length_word
  obtain ⟨r, hr⟩ := P.even_card
  omega

/-- The `n`-th step of the word is `(p_{2n}, p_{2n+1})`. -/
theorem word_getElem_eq (P : G.OddBlock X Y) {n : ℕ} (hn : n < P.word.length) :
    P.word[n] = (P.vtx (2 * n), P.vtx (2 * n + 1)) := by
  have h1 := P.two_mul_succ_lt hn
  rw [getElem_word P n hn, vtx_eq P (by omega), vtx_eq P h1]

theorem vtx_lt_of_mem_support (P : G.OddBlock X Y) {v : V} (hv : v ∈ P.support) :
    ∃ i, i < P.path.card ∧ P.vtx i = v := by
  obtain ⟨i, rfl⟩ := mem_support.1 hv
  exact ⟨i.val, i.isLt, by rw [vtx_eq P i.isLt]⟩

/-! ### The first class after `n` steps -/

/-- The introduced vertices `j_0, …, j_{n-1}` of the first `n` steps. -/
def jPre (P : G.OddBlock X Y) (n : ℕ) : Finset V :=
  (Finset.range n).image fun m => P.vtx (2 * m)

/-- The removed vertices `k_0, …, k_{n-1}` of the first `n` steps. -/
def kPre (P : G.OddBlock X Y) (n : ℕ) : Finset V :=
  (Finset.range n).image fun m => P.vtx (2 * m + 1)

/-- The first class after the first `n` steps of the block: `A` with `k_0, …, k_{n-1}` replaced by
`j_0, …, j_{n-1}`.  (For an untoggled block it is `A ⊕ {p_0, …, p_{2n-1}}`.) -/
def stateA (P : G.OddBlock X Y) (A : Finset V) (n : ℕ) : Finset V :=
  (A \ P.kPre n) ∪ P.jPre n

theorem mem_jPre {P : G.OddBlock X Y} {n : ℕ} {v : V} :
    v ∈ P.jPre n ↔ ∃ m < n, P.vtx (2 * m) = v := by
  simp [jPre]

theorem mem_kPre {P : G.OddBlock X Y} {n : ℕ} {v : V} :
    v ∈ P.kPre n ↔ ∃ m < n, P.vtx (2 * m + 1) = v := by
  simp [kPre]

theorem mem_stateA {P : G.OddBlock X Y} {A : Finset V} {n : ℕ} {v : V} :
    v ∈ P.stateA A n ↔ (v ∈ A ∧ v ∉ P.kPre n) ∨ v ∈ P.jPre n := by
  simp [stateA]

@[simp]
theorem stateA_zero (P : G.OddBlock X Y) (A : Finset V) : P.stateA A 0 = A := by
  simp [stateA, jPre, kPre]

theorem jPre_succ (P : G.OddBlock X Y) (n : ℕ) :
    P.jPre (n + 1) = insert (P.vtx (2 * n)) (P.jPre n) := by
  simp [jPre, Finset.range_add_one, Finset.image_insert]

theorem kPre_succ (P : G.OddBlock X Y) (n : ℕ) :
    P.kPre (n + 1) = insert (P.vtx (2 * n + 1)) (P.kPre n) := by
  simp [kPre, Finset.range_add_one, Finset.image_insert]

theorem vtx_even_not_mem_jPre (P : G.OddBlock X Y) {n : ℕ} (hn : 2 * n + 1 < P.path.card) :
    P.vtx (2 * n) ∉ P.jPre n := by
  intro h
  obtain ⟨m, hm, hmv⟩ := mem_jPre.1 h
  have := P.vtx_injective_of_lt (by omega) (by omega) hmv
  omega

theorem vtx_odd_not_mem_kPre (P : G.OddBlock X Y) {n : ℕ} (hn : 2 * n + 1 < P.path.card) :
    P.vtx (2 * n + 1) ∉ P.kPre n := by
  intro h
  obtain ⟨m, hm, hmv⟩ := mem_kPre.1 h
  have := P.vtx_injective_of_lt (by omega) (by omega) hmv
  omega

theorem vtx_odd_not_mem_jPre (P : G.OddBlock X Y) {n : ℕ} (hn : 2 * n + 1 < P.path.card) :
    P.vtx (2 * n + 1) ∉ P.jPre n := by
  intro h
  obtain ⟨m, hm, hmv⟩ := mem_jPre.1 h
  have := P.vtx_injective_of_lt (by omega) (by omega) hmv
  omega

/-- One step replaces `k_n` by `j_n` in the first class. -/
theorem stateA_succ (P : G.OddBlock X Y) (A : Finset V) {n : ℕ} (hn : 2 * n + 1 < P.path.card) :
    P.stateA A (n + 1) = insert (P.vtx (2 * n)) ((P.stateA A n).erase (P.vtx (2 * n + 1))) := by
  have hkJ := P.vtx_odd_not_mem_jPre hn
  ext v
  simp only [mem_stateA, jPre_succ, kPre_succ, Finset.mem_insert, Finset.mem_erase]
  by_cases hvj : v = P.vtx (2 * n)
  · simp [hvj]
  by_cases hvk : v = P.vtx (2 * n + 1)
  · subst hvk
    simp [hkJ]
  · simp [hvj, hvk]

/-! ### Consequences of being untoggled in `A` -/

section Untoggled

variable {A B : Finset V} (P : G.OddBlock X Y)

/-- A vertex at an even position (an introduced vertex `j`) is not in `A`. -/
theorem vtx_even_not_mem_of_untoggled (hPA : A ∩ P.support = P.support ∩ X) {i : ℕ}
    (hi : i < P.path.card) (he : Even i) : P.vtx i ∉ A := by
  intro hA
  have h1 : P.vtx i ∈ A ∩ P.support := Finset.mem_inter.2 ⟨hA, P.vtx_mem_support hi⟩
  rw [hPA] at h1
  exact (Finset.mem_sdiff.1 (P.vtx_even_mem hi he)).2 (Finset.mem_inter.1 h1).2

/-- A vertex at an odd position (a removed vertex `k`) is in `A`. -/
theorem vtx_odd_mem_of_untoggled (hPA : A ∩ P.support = P.support ∩ X) {i : ℕ}
    (hi : i < P.path.card) (ho : Odd i) : P.vtx i ∈ A := by
  have h1 : P.vtx i ∈ P.support ∩ X :=
    Finset.mem_inter.2 ⟨P.vtx_mem_support hi, (Finset.mem_sdiff.1 (P.vtx_odd_mem hi ho)).1⟩
  rw [← hPA] at h1
  exact (Finset.mem_inter.1 h1).1

/-- **The `A`-part of the clone condition for `j_n`.**  A vertex `v` of `A`, other than `k_n` and
not yet removed, is not adjacent to `j_n`: if `v ∈ Y` this is the independence of `Y`; otherwise
`v ∈ X ∖ Y`, and adjacency to `j_n` would put `v` on the block (it is a whole component of
`G[X ⊕ Y]`), at an odd position adjacent to `j_n`, i.e. `v ∈ {k_n, k_{n-1}}`. -/
theorem not_adj_vtx_even_of_mem (hY : G.IsIndepSet (↑Y : Set V)) (hAXY : A ⊆ X ∪ Y) {n : ℕ}
    (hn : 2 * n + 1 < P.path.card) {v : V} (hvA : v ∈ A) (hvk : v ≠ P.vtx (2 * n + 1))
    (hvK : v ∉ P.kPre n) : ¬ G.Adj (P.vtx (2 * n)) v := by
  intro hadj
  have hjY : P.vtx (2 * n) ∈ Y := (Finset.mem_sdiff.1 (P.vtx_even_mem (by omega) (even_two_mul n))).1
  by_cases hvY : v ∈ Y
  · exact hY (Finset.mem_coe.2 hjY) (Finset.mem_coe.2 hvY) hadj.ne hadj
  have hvX : v ∈ X := by
    rcases Finset.mem_union.1 (hAXY hvA) with h | h
    · exact h
    · exact absurd h hvY
  have hvsd : v ∈ (↑(symmDiff X Y) : Set V) := by
    rw [Finset.mem_coe, Finset.mem_symmDiff]
    exact Or.inl ⟨hvX, hvY⟩
  have hjs : P.vtx (2 * n) ∈ (↑P.support : Set V) :=
    Finset.mem_coe.2 (P.vtx_mem_support (by omega))
  have hvs : v ∈ (↑P.support : Set V) := P.isInducedComponent_support.2.2 hjs hvsd hadj
  obtain ⟨i, hi, rfl⟩ := P.vtx_lt_of_mem_support (Finset.mem_coe.1 hvs)
  rcases Nat.even_or_odd' i with ⟨m, hm | hm⟩
  · exact hvY (Finset.mem_sdiff.1 (P.vtx_even_mem hi ⟨m, by omega⟩)).1
  · subst hm
    have h := (P.adj_vtx_iff (by omega) hi).1 hadj
    rcases h with h | h
    · exact hvk (by rw [show 2 * m + 1 = 2 * n + 1 by omega])
    · exact hvK (mem_kPre.2 ⟨m, by omega, rfl⟩)

/-- The clone condition `j_n ≺_{A_n ∪ B} k_n` of the `n`-th step, given the second-class
condition.  The first-class part is automatic. -/
theorem isCloneIn_stateA (hY : G.IsIndepSet (↑Y : Set V)) (hAind : G.IsIndepSet (↑A : Set V))
    (hAB : Disjoint A B) (hAXY : A ⊆ X ∪ Y) (hPA : A ∩ P.support = P.support ∩ X) {n : ℕ}
    (hn : 2 * n + 1 < P.path.card) (hjB : P.vtx (2 * n) ∉ B)
    (hBad : ∀ v ∈ B, (G.Adj (P.vtx (2 * n)) v ↔ G.Adj (P.vtx (2 * n + 1)) v)) :
    G.IsCloneIn (↑(P.stateA A n ∪ B) : Set V) (P.vtx (2 * n)) (P.vtx (2 * n + 1)) := by
  have hjA : P.vtx (2 * n) ∉ A := P.vtx_even_not_mem_of_untoggled hPA (by omega) (even_two_mul n)
  have hkA : P.vtx (2 * n + 1) ∈ A :=
    P.vtx_odd_mem_of_untoggled hPA hn (odd_two_mul_add_one n)
  have hkK := P.vtx_odd_not_mem_kPre hn
  have hjJ := P.vtx_even_not_mem_jPre hn
  have hkB : P.vtx (2 * n + 1) ∉ B := fun h => Finset.disjoint_left.1 hAB hkA h
  refine ⟨?_, ?_, ?_⟩
  · simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, not_or, mem_stateA]
    exact ⟨⟨fun h => hjA h.1, hjJ⟩, hjB⟩
  · simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, mem_stateA]
    exact Or.inl (Or.inl ⟨hkA, hkK⟩)
  · intro v hv
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hv
    rcases hv with hv | hvB
    · rw [mem_stateA] at hv
      by_cases hvk : v = P.vtx (2 * n + 1)
      · subst hvk
        exact ⟨fun _ => Or.inl rfl,
          fun _ => (P.adj_vtx_iff (by omega) hn).2 (Or.inl rfl)⟩
      rcases hv with ⟨hvA, hvK⟩ | hvJ
      · have h1 := P.not_adj_vtx_even_of_mem hY hAXY hn hvA hvk hvK
        have h2 : ¬ G.Adj (P.vtx (2 * n + 1)) v := hAind hkA hvA (Ne.symm hvk)
        exact ⟨fun h => absurd h h1, fun h => h.elim (fun h => absurd h hvk) fun h => absurd h h2⟩
      · obtain ⟨m, hm, rfl⟩ := mem_jPre.1 hvJ
        have h1 : ¬ G.Adj (P.vtx (2 * n)) (P.vtx (2 * m)) := by
          rw [P.adj_vtx_iff (by omega) (by omega)]
          omega
        have h2 : ¬ G.Adj (P.vtx (2 * n + 1)) (P.vtx (2 * m)) := by
          rw [P.adj_vtx_iff (by omega) (by omega)]
          omega
        exact ⟨fun h => absurd h h1, fun h => h.elim (fun h => absurd h hvk) fun h => absurd h h2⟩
    · have hvk : v ≠ P.vtx (2 * n + 1) := fun h => hkB (h ▸ hvB)
      exact ⟨fun h => Or.inr ((hBad v hvB).1 h), fun h =>
        (hBad v hvB).2 (h.elim (fun h => absurd h hvk) id)⟩

/-- The `n`-th step of the word is a `ClassStep` out of the current state as soon as the
second-class condition holds. -/
theorem classStep_stateA_of_cond (hY : G.IsIndepSet (↑Y : Set V))
    (hAind : G.IsIndepSet (↑A : Set V)) (hAB : Disjoint A B) (hAXY : A ⊆ X ∪ Y)
    (hPA : A ∩ P.support = P.support ∩ X) {n : ℕ} (hn : 2 * n + 1 < P.path.card)
    (hc : BlockStepCond G B (P.vtx (2 * n), P.vtx (2 * n + 1))) :
    G.ClassStep (P.stateA A n, B) (P.vtx (2 * n), P.vtx (2 * n + 1)) (P.stateA A (n + 1), B) := by
  have hcl := P.isCloneIn_stateA hY hAind hAB hAXY hPA hn hc.1 hc.2
  have hkA : P.vtx (2 * n + 1) ∈ A :=
    P.vtx_odd_mem_of_untoggled hPA hn (odd_two_mul_add_one n)
  have hkK := P.vtx_odd_not_mem_kPre hn
  rw [P.stateA_succ A hn]
  exact ClassStep.a hcl (mem_stateA.2 (Or.inl ⟨hkA, hkK⟩))

/-- Conversely, a `ClassStep` out of the current state forces the second-class condition and ends
in the next state.  (The `b`-case of `ClassStep` is impossible because `k_n ∈ A` and `A`, `B` are
disjoint.) -/
theorem cond_of_classStep (hAB : Disjoint A B) (hPA : A ∩ P.support = P.support ∩ X) {n : ℕ}
    (hn : 2 * n + 1 < P.path.card) {s' : Finset V × Finset V}
    (h : G.ClassStep (P.stateA A n, B) (P.vtx (2 * n), P.vtx (2 * n + 1)) s') :
    BlockStepCond G B (P.vtx (2 * n), P.vtx (2 * n + 1)) ∧ s' = (P.stateA A (n + 1), B) := by
  have hkA : P.vtx (2 * n + 1) ∈ A :=
    P.vtx_odd_mem_of_untoggled hPA hn (odd_two_mul_add_one n)
  have hkB : P.vtx (2 * n + 1) ∉ B := fun h => Finset.disjoint_left.1 hAB hkA h
  cases h with
  | a hcl hk =>
    refine ⟨⟨fun hjB => hcl.1 (by simp [hjB]), fun v hv => ?_⟩, ?_⟩
    · have hvk : v ≠ P.vtx (2 * n + 1) := fun h => hkB (h ▸ hv)
      have := hcl.2.2 v (by simp [hv])
      simp only [hvk, false_or] at this
      exact this
    · rw [P.stateA_succ A hn]
  | b hcl hk => exact absurd hk hkB

end Untoggled

/-! ### Runs of a whole block -/

section Run

variable {A B : Finset V} (P : G.OddBlock X Y)

/-- If every step satisfies the second-class condition, the suffix of the word starting at the
`n`-th step runs from the `n`-th state to the final state. -/
theorem classRun_drop_of_cond (hY : G.IsIndepSet (↑Y : Set V))
    (hAind : G.IsIndepSet (↑A : Set V)) (hAB : Disjoint A B) (hAXY : A ⊆ X ∪ Y)
    (hPA : A ∩ P.support = P.support ∩ X)
    (hc : ∀ p ∈ P.word, BlockStepCond G B p) :
    ∀ d n : ℕ, n + d = P.word.length →
      G.ClassRun (P.stateA A n, B) (P.word.drop n) (P.stateA A P.word.length, B) := by
  intro d
  induction d with
  | zero =>
    intro n hn
    have hn' : n = P.word.length := by omega
    subst hn'
    simpa using ClassRun.nil _
  | succ d ih =>
    intro n hn
    have hlt : n < P.word.length := by omega
    rw [List.drop_eq_getElem_cons hlt]
    refine ClassRun.cons ?_ (ih (n + 1) (by omega))
    rw [P.word_getElem_eq hlt]
    refine P.classStep_stateA_of_cond hY hAind hAB hAXY hPA (P.two_mul_succ_lt hlt) ?_
    have := hc _ (List.getElem_mem hlt)
    rwa [P.word_getElem_eq hlt] at this

/-- A run of the suffix of the word from the `n`-th state forces the second-class condition at
every later step and ends in the final state. -/
theorem cond_of_classRun_drop (hAB : Disjoint A B) (hPA : A ∩ P.support = P.support ∩ X) :
    ∀ d n : ℕ, n + d = P.word.length → ∀ t' : Finset V × Finset V,
      G.ClassRun (P.stateA A n, B) (P.word.drop n) t' →
        (∀ (m : ℕ) (hm : m < P.word.length), n ≤ m → BlockStepCond G B P.word[m]) ∧
          t' = (P.stateA A P.word.length, B) := by
  intro d
  induction d with
  | zero =>
    intro n hn t' h
    have hn' : n = P.word.length := by omega
    subst hn'
    rw [List.drop_length] at h
    cases h
    exact ⟨fun m hm hnm => absurd hm (by omega), rfl⟩
  | succ d ih =>
    intro n hn t' h
    have hlt : n < P.word.length := by omega
    rw [List.drop_eq_getElem_cons hlt, P.word_getElem_eq hlt] at h
    cases h with
    | cons hstep hrest =>
      obtain ⟨hc, rfl⟩ := P.cond_of_classStep hAB hPA (P.two_mul_succ_lt hlt) hstep
      obtain ⟨hrest', hend⟩ := ih (n + 1) (by omega) t' hrest
      refine ⟨fun m hm hnm => ?_, hend⟩
      by_cases hmn : m = n
      · subst hmn
        rw [P.word_getElem_eq hm]
        exact hc
      · exact hrest' m hm (by omega)

/-- With the untoggled hypothesis, the state after all steps is `A ⊕ supp P`. -/
theorem stateA_length (hPA : A ∩ P.support = P.support ∩ X) :
    P.stateA A P.word.length = symmDiff A P.support := by
  have hlen : P.word.length = P.path.card / 2 := P.length_word
  obtain ⟨r, hr⟩ := P.even_card
  ext v
  rw [mem_stateA, Finset.mem_symmDiff]
  constructor
  · rintro (⟨hvA, hvK⟩ | hvJ)
    · left
      refine ⟨hvA, fun hvs => hvK ?_⟩
      obtain ⟨i, hi, rfl⟩ := P.vtx_lt_of_mem_support hvs
      rcases Nat.even_or_odd' i with ⟨m, hm | hm⟩
      · exact absurd hvA (by
          subst hm
          exact P.vtx_even_not_mem_of_untoggled hPA hi ⟨m, by omega⟩)
      · subst hm
        exact mem_kPre.2 ⟨m, by omega, rfl⟩
    · right
      obtain ⟨m, hm, rfl⟩ := mem_jPre.1 hvJ
      exact ⟨P.vtx_mem_support (by omega),
        P.vtx_even_not_mem_of_untoggled hPA (by omega) (even_two_mul m)⟩
  · rintro (⟨hvA, hvs⟩ | ⟨hvs, hvA⟩)
    · left
      refine ⟨hvA, fun hvK => hvs ?_⟩
      obtain ⟨m, hm, rfl⟩ := mem_kPre.1 hvK
      exact P.vtx_mem_support (by omega)
    · right
      obtain ⟨i, hi, rfl⟩ := P.vtx_lt_of_mem_support hvs
      rcases Nat.even_or_odd' i with ⟨m, hm | hm⟩
      · subst hm
        exact mem_jPre.2 ⟨m, by omega, rfl⟩
      · subst hm
        exact absurd (P.vtx_odd_mem_of_untoggled hPA hi ⟨m, rfl⟩) hvA

end Run

/-! ### The forward step lemma -/

section Main

variable {A B : Finset V}

/-- **Block step lemma, forward form** (v1 L992, base case L1808-1830), for an independent first
class `A` disjoint from `B`: a block untoggled in `A` runs from `(A, B)` if and only if every step
`(j, k)` has `j ∉ B` and `Γ_B(j) = Γ_B(k)`. -/
theorem classRun_iff_of_indep (hY : G.IsIndepSet (↑Y : Set V))
    (hAind : G.IsIndepSet (↑A : Set V)) (hAB : Disjoint A B) (hAXY : A ⊆ X ∪ Y)
    (P : G.OddBlock X Y) (hPA : A ∩ P.support = P.support ∩ X) :
    P.RunsFrom (A, B) ↔ ∀ p ∈ P.word, BlockStepCond G B p := by
  constructor
  · rintro ⟨t', h⟩
    have h0 : G.ClassRun (P.stateA A 0, B) (P.word.drop 0) t' := by simpa using h
    obtain ⟨hc, -⟩ := P.cond_of_classRun_drop hAB hPA P.word.length 0 (by omega) t' h0
    intro p hp
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hp
    exact hc m hm (Nat.zero_le _)
  · intro hc
    have := P.classRun_drop_of_cond hY hAind hAB hAXY hPA hc P.word.length 0 (by omega)
    exact ⟨(P.stateA A P.word.length, B), by simpa using this⟩

/-- The end of a run of a block untoggled in `A` is `(A ⊕ supp P, B)`. -/
theorem classRun_end_of_indep (hAB : Disjoint A B) (P : G.OddBlock X Y)
    (hPA : A ∩ P.support = P.support ∩ X) {t' : Finset V × Finset V}
    (h : G.ClassRun (A, B) P.word t') : t' = (symmDiff A P.support, B) := by
  have h0 : G.ClassRun (P.stateA A 0, B) (P.word.drop 0) t' := by simpa using h
  obtain ⟨-, hend⟩ := P.cond_of_classRun_drop hAB hPA P.word.length 0 (by omega) t' h0
  rw [hend, P.stateA_length hPA]

/-- **Block step lemma, forward form** (v1 L992; base case (i) clone checks L1808-1830).  Let
`(A, B)` be hole classes and `X`, `Y` independent sets with `A ⊆ X ∪ Y`, and let `P` be a block of
`G[X ⊕ Y]` untoggled in `A` (`A ∩ supp P = supp P ∩ X`).  Then the word of `P` is a clone run out
of `(A, B)` if and only if every step `(j, k)` of `P` has `j ∉ B` and `j`, `k` have the same
neighbours in `B`.  The condition on the first class is automatic, because `A` is independent and
`P` is a whole induced-path component of `G[X ⊕ Y]`; claw-freeness is not used.  (Independence of
`X` is not needed either, since the first class `A` is independent; `_hX` is kept to match the
form recorded in the work package.) -/
theorem classRun_iff {X Y A B : Finset V} (_hX : G.IsIndepSet (↑X : Set V))
    (hY : G.IsIndepSet (↑Y : Set V)) (ht : G.IsHoleClasses (A, B)) (hAXY : A ⊆ X ∪ Y)
    (P : G.OddBlock X Y) (hPA : A ∩ P.support = P.support ∩ X) :
    P.RunsFrom (A, B) ↔ ∀ p ∈ P.word, p.1 ∉ B ∧ ∀ v ∈ B, (G.Adj p.1 v ↔ G.Adj p.2 v) := by
  exact classRun_iff_of_indep hY ht.isIndepSet_fst ht.disjoint hAXY P hPA

/-- A run of a block untoggled in `A` out of the hole classes `(A, B)` ends in
`(A ⊕ supp P, B)`: the carrier `C^{(r)} = C^{(r-1)} ⊕ P^{(r)}` of v1 Definition 19, with its
colouring. -/
theorem classRun_end {X Y A B : Finset V} (_hX : G.IsIndepSet (↑X : Set V))
    (_hY : G.IsIndepSet (↑Y : Set V)) (ht : G.IsHoleClasses (A, B)) (_hAXY : A ⊆ X ∪ Y)
    (P : G.OddBlock X Y) (hPA : A ∩ P.support = P.support ∩ X) {t' : Finset V × Finset V}
    (h : G.ClassRun (A, B) P.word t') : t' = (symmDiff A P.support, B) := by
  exact classRun_end_of_indep ht.disjoint P hPA h

/-- When the second-class conditions hold, the block runs and ends in `(A ⊕ supp P, B)`. -/
theorem classRun_of_cond {X Y A B : Finset V} (hX : G.IsIndepSet (↑X : Set V))
    (hY : G.IsIndepSet (↑Y : Set V)) (ht : G.IsHoleClasses (A, B)) (hAXY : A ⊆ X ∪ Y)
    (P : G.OddBlock X Y) (hPA : A ∩ P.support = P.support ∩ X)
    (hc : ∀ p ∈ P.word, p.1 ∉ B ∧ ∀ v ∈ B, (G.Adj p.1 v ↔ G.Adj p.2 v)) :
    G.ClassRun (A, B) P.word (symmDiff A P.support, B) := by
  obtain ⟨t', h⟩ := (classRun_iff hX hY ht hAXY P hPA).2 hc
  rwa [classRun_end hX hY ht hAXY P hPA h] at h

/-! ### The backward step lemma -/

/-- **Block step lemma, backward form.**  Mirror of `classRun_iff`: the reversed word of `P` runs
from a state `(A', B')` with `A'` containing exactly the introduced vertices of the block
(`A' ∩ supp P = supp P ∩ Y`: the state after the block has run) if and only if every step
`(j, k)` has `k ∉ B'` and `k`, `j` have the same neighbours in `B'`.  This is the forward lemma
for `P.reverse : OddBlock Y X`, whose word is `reverseWord P.word` (`reverse_word`). -/
theorem runsBack_iff {X Y A' B' : Finset V} (hX : G.IsIndepSet (↑X : Set V))
    (hY : G.IsIndepSet (↑Y : Set V)) (ht : G.IsHoleClasses (A', B')) (hAXY : A' ⊆ X ∪ Y)
    (P : G.OddBlock X Y) (hPA : A' ∩ P.support = P.support ∩ Y) :
    (∃ t', G.ClassRun (A', B') (reverseWord P.word) t') ↔
      ∀ p ∈ P.word, p.2 ∉ B' ∧ ∀ v ∈ B', (G.Adj p.2 v ↔ G.Adj p.1 v) := by
  have hAXY' : A' ⊆ Y ∪ X := by rwa [Finset.union_comm]
  have hPA' : A' ∩ P.reverse.support = P.reverse.support ∩ Y := by
    rwa [P.reverse_support]
  have key := classRun_iff hY hX ht hAXY' P.reverse hPA'
  have hrun : P.reverse.RunsFrom (A', B') ↔ ∃ t', G.ClassRun (A', B') (reverseWord P.word) t' := by
    unfold RunsFrom
    rw [P.reverse_word]
  have hmem : ∀ p : V × V, p ∈ P.reverse.word ↔ p.swap ∈ P.word := by
    intro p
    rw [P.reverse_word]
    obtain ⟨a, b⟩ := p
    simp [reverseWord]
  rw [← hrun, key]
  constructor
  · intro h p hp
    exact h p.swap ((hmem _).2 (by simpa using hp))
  · intro h p hp
    exact h p.swap ((hmem p).1 hp)

/-- The end of a backward run of a block is `(A' ⊕ supp P, B')`. -/
theorem runsBack_end {X Y A' B' : Finset V} (hX : G.IsIndepSet (↑X : Set V))
    (hY : G.IsIndepSet (↑Y : Set V)) (ht : G.IsHoleClasses (A', B')) (hAXY : A' ⊆ X ∪ Y)
    (P : G.OddBlock X Y) (hPA : A' ∩ P.support = P.support ∩ Y) {t' : Finset V × Finset V}
    (h : G.ClassRun (A', B') (reverseWord P.word) t') : t' = (symmDiff A' P.support, B') := by
  have hAXY' : A' ⊆ Y ∪ X := by rwa [Finset.union_comm]
  have hPA' : A' ∩ P.reverse.support = P.reverse.support ∩ Y := by
    rwa [P.reverse_support]
  rw [← P.reverse_word] at h
  have := classRun_end hY hX ht hAXY' P.reverse hPA' h
  rwa [P.reverse_support] at this

end Main

end OddBlock

end SimpleGraph
