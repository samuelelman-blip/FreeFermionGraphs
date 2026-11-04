import FreeFermionGraphs.SetDeformationTether

/-!
# Hole-class states and clone runs

This module is the carrier-level, colour-preserving form of the manuscript's single-vertex
deformation (arXiv 2305.15625 v1, Definition 10 `definition:singlevertexdeformation`, L682-686,
with the reversibility remark at L686), of the deformation closure (Definition 12,
`definition:deformationclosure`, L700), and of the bookkeeping `C^{(r,s)}` of a fixed-pairing-type
deformation (Definition 19, `definition:fixedpairingtypedeformation`, L978-994).

A *hole-class state* is a pair `s = (A, B)` of finsets of vertices which are the two colouring
classes `C_a`, `C_b` of an even hole `C = A ∪ B` (v1 Eq. `equation:evenholelabel`, L313).  The pair
keeps the colouring, which the `C^{(r,s)}` of v1 Definition 19 needs and which a bare carrier
forgets.

* `SimpleGraph.IsCloneIn G X j k` is the carrier-level clone relation `j ≺_X k` of v1 Definition 10:
  `j ∉ X`, `k ∈ X`, and `j` is adjacent to a vertex `v ∈ X` exactly when `v = k` or `v ~ k`.
* `SimpleGraph.IsHoleClasses G s` says that `s` is the pair of colouring classes
  `(image L.a, image L.b)` of a labelling `L` with full cyclic order.
* `SimpleGraph.ClassStep G s (j, k) s'` replaces the clone-target `k` by `j` inside the class of
  `k` (`k` lies in `s.1` or in `s.2`), provided `j ≺_{s.1 ∪ s.2} k`.
* `SimpleGraph.ClassRun G s w s'` is the list closure of `ClassStep`: the word `w` is the sequence
  of pairs `(j, k)` (`j` introduced, `k` removed).
* `SimpleGraph.reverseWord w = (w.map Prod.swap).reverse` is the word of the reverse run.

## Main results

* `IsHoleClasses.isEvenHoleCarrier`, `IsHoleClasses.swap`, `IsHoleClasses.eq_or_eq_swap` and
  `exists_isHoleClasses`: the hole-class states of a graph are exactly the colourings of its even
  hole carriers, each carrier having exactly two (a state and its swap).
* `ClassStep.exists_cloneAt`: the labelling bridge.  Every `ClassStep` out of a hole-class state is
  the deformation `EvenHoleLabeling.deform` of a full-cyclic labelling realising `s` (or, if the
  clone-target lies in the second class, of one realising `s.swap`).  No labelling is ever
  transported along a run: one is chosen afresh at each step.
* `ClassStep.isHoleClasses` and `ClassRun.isHoleClasses`: steps and runs preserve hole classes.
* `ClassStep.reverse` and `ClassRun.reverse`: single-vertex deformations are reversible
  (v1 L686: "if `j ≺_L k`, then `k ≺_{L'} j`"), hence runs reverse with `reverseWord`.
* `ClassRun.append`, `ClassRun.swap_iff`: runs concatenate and commute with swapping the classes.
* `ClassRun.inEvenHoleDeformationClosure`: the carriers visited by a run lie in one deformation
  closure `⟨C⟩`.

Claw-freeness is not used anywhere in this module.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- The carrier-level clone relation `j ≺_X k` (v1 Definition 10, L682-686): `j ∉ X`, `k ∈ X`, and
for every `v ∈ X`, `j` is adjacent to `v` exactly when `v = k` or `v` is adjacent to `k`.  For an
even-hole carrier `X` this says `Γ_X(j) = {k} ∪ Γ_X(k)`, i.e. `j` is a clone of `k` in `X`. -/
def IsCloneIn (G : SimpleGraph V) (X : Set V) (j k : V) : Prop :=
  j ∉ X ∧ k ∈ X ∧ ∀ v ∈ X, (G.Adj j v ↔ v = k ∨ G.Adj k v)

/-- `s = (A, B)` is a *hole-class state*: the pair of colouring classes `(C_a, C_b)` of an even hole
`C = A ∪ B` (v1 Eq. `equation:evenholelabel`, L313), presented as the images of the two label maps
of a full-cyclic alternating labelling. -/
def IsHoleClasses (G : SimpleGraph V) [DecidableEq V] (s : Finset V × Finset V) : Prop :=
  ∃ (k : ℕ) (L : G.EvenHoleLabeling k), L.HasFullCyclicOrder ∧
    Finset.univ.image L.a = s.1 ∧ Finset.univ.image L.b = s.2

/-- One step of a clone run (v1 Definition 10 applied to a hole presented by its two colour
classes): if `j ≺_{A ∪ B} k`, replace `k` by `j` inside the class of `k`.  The pair `(j, k)` records
the vertex introduced and the vertex removed. -/
inductive ClassStep (G : SimpleGraph V) [DecidableEq V] :
    Finset V × Finset V → V × V → Finset V × Finset V → Prop
  | a {A B : Finset V} {j k : V} : G.IsCloneIn ↑(A ∪ B) j k → k ∈ A →
      ClassStep G (A, B) (j, k) (insert j (A.erase k), B)
  | b {A B : Finset V} {j k : V} : G.IsCloneIn ↑(A ∪ B) j k → k ∈ B →
      ClassStep G (A, B) (j, k) (A, insert j (B.erase k))

/-- A clone run: the list closure of `ClassStep`, labelled by the word of `(introduced, removed)`
pairs (the sequence `(j_{s-1}^{(r)}, k_{s-1}^{(r)})` of v1 Definition 19). -/
inductive ClassRun (G : SimpleGraph V) [DecidableEq V] :
    Finset V × Finset V → List (V × V) → Finset V × Finset V → Prop
  | nil (s : Finset V × Finset V) : ClassRun G s [] s
  | cons {s s' s'' : Finset V × Finset V} {p : V × V} {w : List (V × V)} :
      ClassStep G s p s' → ClassRun G s' w s'' → ClassRun G s (p :: w) s''

/-- The word of the reversed run: reverse the order and swap each pair `(j, k)` to `(k, j)`
(v1 L686: single-vertex deformations are reversible). -/
def reverseWord (w : List (V × V)) : List (V × V) := (w.map Prod.swap).reverse

@[simp]
theorem reverseWord_nil : reverseWord ([] : List (V × V)) = [] := rfl

theorem reverseWord_cons (p : V × V) (w : List (V × V)) :
    reverseWord (p :: w) = reverseWord w ++ [p.swap] := by
  simp [reverseWord]

theorem reverseWord_append (w₁ w₂ : List (V × V)) :
    reverseWord (w₁ ++ w₂) = reverseWord w₂ ++ reverseWord w₁ := by
  simp [reverseWord]

@[simp]
theorem reverseWord_reverseWord (w : List (V × V)) : reverseWord (reverseWord w) = w := by
  simp [reverseWord, List.map_reverse, List.map_map]

/-! ### Labelling lemmas -/

namespace EvenHoleLabeling

variable [DecidableEq V]

/-- The `b`-class of the colour swap is the `a`-class (the label `b i` of the swap is
`a (prev i)`, and `prev` is a bijection). -/
theorem image_swapColors_b {k : ℕ} (L : G.EvenHoleLabeling k) :
    Finset.univ.image L.swapColors.b = Finset.univ.image L.a := by
  ext v
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨L.next j, by simp [EvenHoleLabeling.swapColors, L.prev_next]⟩

/-- The `a`-class of the deformed labelling is the original class with `a i` replaced by the clone
`s`. -/
theorem image_deform_a {k : ℕ} (L : G.EvenHoleLabeling k) {s : V} {i : Fin k}
    (h : L.CloneAt s i) :
    Finset.univ.image (L.deform h).a =
      insert s ((Finset.univ.image L.a).erase (L.a i)) := by
  ext v
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_erase]
  constructor
  · rintro ⟨q, rfl⟩
    by_cases hq : q = i
    · subst hq
      left
      simp
    · right
      refine ⟨?_, q, ?_⟩
      · rw [deform_a_away L h hq]
        exact fun hqi => hq (L.a_injective hqi)
      · rw [deform_a_away L h hq]
  · rintro (rfl | ⟨hvi, q, rfl⟩)
    · exact ⟨i, by simp⟩
    · have hq : q ≠ i := fun hq => hvi (by rw [hq])
      exact ⟨q, deform_a_away L h hq⟩

/-- Unfolding `IsCloneIn` on the carrier of a labelling: a carrier-level clone of `L.a i` is an
`L.CloneAt` (v1 L682: `j ≺_C a_i`). -/
theorem cloneAt_of_isCloneIn {k : ℕ} (L : G.EvenHoleLabeling k) {j : V} {i : Fin k}
    (h : G.IsCloneIn (↑(Finset.univ.image L.a ∪ Finset.univ.image L.b) : Set V) j (L.a i)) :
    L.CloneAt j i := by
  rw [L.coe_image_a_union_image_b] at h
  exact ⟨h.1, h.2.2⟩

/-- A deformation of a labelling by a clone of an `a`-vertex replaces `a i = kk` by `j` in the
`a`-class and leaves the `b`-class unchanged. -/
theorem exists_cloneAt_deform_a {k : ℕ} (L : G.EvenHoleLabeling k) {j kk : V}
    (hcl : G.IsCloneIn
      (↑(Finset.univ.image L.a ∪ Finset.univ.image L.b) : Set V) j kk)
    (hk : kk ∈ Finset.univ.image L.a) :
    ∃ (i : Fin k) (hi : L.CloneAt j i), L.a i = kk ∧
      Finset.univ.image (L.deform hi).a = insert j ((Finset.univ.image L.a).erase kk) ∧
      Finset.univ.image (L.deform hi).b = Finset.univ.image L.b := by
  obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hk
  subst hi
  have hcl' : L.CloneAt j i := L.cloneAt_of_isCloneIn hcl
  exact ⟨i, hcl', rfl, L.image_deform_a hcl', rfl⟩

end EvenHoleLabeling

section HoleClasses

variable [DecidableEq V] {s t s' s'' : Finset V × Finset V}

/-! ### Facts (a), (b): hole-class states and even-hole carriers -/

/-- The two classes of a hole-class state are disjoint. -/
theorem IsHoleClasses.disjoint (hs : G.IsHoleClasses s) : Disjoint s.1 s.2 := by
  obtain ⟨k, L, -, h1, h2⟩ := hs
  rw [← h1, ← h2]
  exact L.disjoint_image_a_image_b

/-- Each class of a hole-class state is an independent set. -/
theorem IsHoleClasses.isIndepSet_fst (hs : G.IsHoleClasses s) :
    G.IsIndepSet (↑s.1 : Set V) := by
  obtain ⟨k, L, -, h1, -⟩ := hs
  rw [← h1]
  exact L.isIndepSet_image_a

/-- Each class of a hole-class state is an independent set. -/
theorem IsHoleClasses.isIndepSet_snd (hs : G.IsHoleClasses s) :
    G.IsIndepSet (↑s.2 : Set V) := by
  obtain ⟨k, L, -, -, h2⟩ := hs
  rw [← h2]
  exact L.isIndepSet_image_b

/-- (a) The carrier of a hole-class state is an even-hole carrier (v1 L313). -/
theorem IsHoleClasses.isEvenHoleCarrier (hs : G.IsHoleClasses s) :
    G.IsEvenHoleCarrier (↑(s.1 ∪ s.2) : Set V) := by
  obtain ⟨k, L, hL, h1, h2⟩ := hs
  rw [← h1, ← h2, L.coe_image_a_union_image_b]
  exact L.isEvenHoleCarrier_of_hasFullCyclicOrder hL

/-- (a) Swapping the two colouring classes of a hole-class state gives a hole-class state: the
colour swap `EvenHoleLabeling.swapColors` of a realising labelling realises `s.swap`. -/
theorem IsHoleClasses.swap (hs : G.IsHoleClasses s) : G.IsHoleClasses s.swap := by
  obtain ⟨k, L, hL, h1, h2⟩ := hs
  exact ⟨k, L.swapColors, hL.swapColors, h2, L.image_swapColors_b.trans h1⟩

/-- (a) Two hole-class states with the same carrier are equal or swapped (v1 L313: "the two unique
independent sets of size `k` in `C`, which are the coloring classes of `C`"). -/
theorem IsHoleClasses.eq_or_eq_swap (hs : G.IsHoleClasses s) (ht : G.IsHoleClasses t)
    (h : s.1 ∪ s.2 = t.1 ∪ t.2) : t = s ∨ t = s.swap := by
  obtain ⟨k, L, hL, h1, h2⟩ := hs
  obtain ⟨k', L', hL', h1', h2'⟩ := ht
  have hcar : L.carrier = L'.carrier := by
    rw [← L.coe_image_a_union_image_b, ← L'.coe_image_a_union_image_b, h1, h2, h1', h2', h]
  have hC := L.isEvenHoleCarrier_of_hasFullCyclicOrder hL
  rcases L.colorClasses_eq_or_swap L' hC hcar with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · left
    refine Prod.ext ?_ ?_
    · exact h1'.symm.trans
        ((EvenHoleLabeling.image_univ_eq_of_range_eq _ _ ha).symm.trans h1)
    · exact h2'.symm.trans
        ((EvenHoleLabeling.image_univ_eq_of_range_eq _ _ hb).symm.trans h2)
  · right
    refine Prod.ext ?_ ?_
    · exact h1'.symm.trans
        ((EvenHoleLabeling.image_univ_eq_of_range_eq _ _ hb.symm).trans h2)
    · exact h2'.symm.trans
        ((EvenHoleLabeling.image_univ_eq_of_range_eq _ _ ha.symm).trans h1)

/-- (b) Every even-hole carrier is the carrier of a hole-class state. -/
theorem exists_isHoleClasses {C : Set V} (hC : G.IsEvenHoleCarrier C) :
    ∃ s : Finset V × Finset V, G.IsHoleClasses s ∧ (↑(s.1 ∪ s.2) : Set V) = C := by
  obtain ⟨k, L, hL, rfl⟩ := (isEvenHoleCarrier_iff_exists_fullCyclic_labeling C).1 hC
  exact ⟨(Finset.univ.image L.a, Finset.univ.image L.b), ⟨k, L, hL, rfl, rfl⟩,
    L.coe_image_a_union_image_b⟩

/-! ### Fact (c): the labelling bridge -/

/-- (c) The labelling bridge.  A `ClassStep` out of a hole-class state is the deformation
`EvenHoleLabeling.deform` of a full-cyclic labelling `L` realising `s` (first disjunct) or, when the
clone-target `k` lies in the second class, realising `s.swap` (second disjunct); `L.a i = k` and
the clone `j` satisfies `L.CloneAt j i`. -/
theorem ClassStep.exists_cloneAt {j k : V} (hs : G.IsHoleClasses s)
    (h : G.ClassStep s (j, k) s') :
    ∃ (n : ℕ) (L : G.EvenHoleLabeling n) (i : Fin n) (hi : L.CloneAt j i),
      L.HasFullCyclicOrder ∧ L.a i = k ∧
      ((Finset.univ.image L.a = s.1 ∧ Finset.univ.image L.b = s.2 ∧
          Finset.univ.image (L.deform hi).a = s'.1 ∧
          Finset.univ.image (L.deform hi).b = s'.2) ∨
       (Finset.univ.image L.a = s.2 ∧ Finset.univ.image L.b = s.1 ∧
          Finset.univ.image (L.deform hi).a = s'.2 ∧
          Finset.univ.image (L.deform hi).b = s'.1)) := by
  obtain ⟨n, L, hL, h1, h2⟩ := hs
  cases h with
  | @a A B j k hcl hk =>
    have h1' : Finset.univ.image L.a = A := h1
    have h2' : Finset.univ.image L.b = B := h2
    subst h1' h2'
    obtain ⟨i, hi, hia, hid, hidb⟩ := L.exists_cloneAt_deform_a hcl hk
    exact ⟨n, L, i, hi, hL, hia, Or.inl ⟨rfl, rfl, hid, hidb⟩⟩
  | @b A B j k hcl hk =>
    have h1' : Finset.univ.image L.a = A := h1
    have h2' : Finset.univ.image L.b = B := h2
    subst h1' h2'
    have hU : Finset.univ.image L.swapColors.a ∪ Finset.univ.image L.swapColors.b =
        Finset.univ.image L.a ∪ Finset.univ.image L.b := by
      rw [L.image_swapColors_b]
      exact Finset.union_comm _ _
    have hcl' : G.IsCloneIn (↑(Finset.univ.image L.swapColors.a ∪
        Finset.univ.image L.swapColors.b) : Set V) j k := by
      rw [hU]
      exact hcl
    obtain ⟨i, hi, hia, hid, hidb⟩ := L.swapColors.exists_cloneAt_deform_a hcl' hk
    exact ⟨n, L.swapColors, i, hi, hL.swapColors, hia,
      Or.inr ⟨rfl, L.image_swapColors_b, hid, hidb.trans L.image_swapColors_b⟩⟩

/-- A step out of a hole-class state lands in a hole-class state. -/
theorem ClassStep.isHoleClasses {p : V × V} (hs : G.IsHoleClasses s) (h : G.ClassStep s p s') :
    G.IsHoleClasses s' := by
  obtain ⟨j, k⟩ := p
  obtain ⟨n, L, i, hi, hL, -, hcase⟩ := h.exists_cloneAt hs
  have hD := L.hasFullCyclicOrder_deform hi hL
  rcases hcase with ⟨-, -, h1, h2⟩ | ⟨-, -, h1, h2⟩
  · exact ⟨n, L.deform hi, hD, h1, h2⟩
  · have hswap : G.IsHoleClasses (s'.2, s'.1) := ⟨n, L.deform hi, hD, h1, h2⟩
    exact hswap.swap

/-- (c) A run out of a hole-class state stays among hole-class states. -/
theorem ClassRun.isHoleClasses {w : List (V × V)} (hs : G.IsHoleClasses s)
    (h : G.ClassRun s w s') : G.IsHoleClasses s' := by
  induction h with
  | nil => exact hs
  | cons hstep _ ih => exact ih (hstep.isHoleClasses hs)

/-! ### Fact (d): runs append, reverse and commute with swapping -/

/-- (d) Runs concatenate. -/
theorem ClassRun.append {w₁ w₂ : List (V × V)} (h₁ : G.ClassRun s w₁ s')
    (h₂ : G.ClassRun s' w₂ s'') : G.ClassRun s (w₁ ++ w₂) s'' := by
  induction h₁ with
  | nil => simpa using h₂
  | cons hstep _ ih => exact ClassRun.cons hstep (ih h₂)

/-- A single step is a run of length one. -/
theorem ClassRun.single {p : V × V} (h : G.ClassStep s p s') : G.ClassRun s [p] s' :=
  ClassRun.cons h (ClassRun.nil _)

/-- Core of the reversibility of a clone step (v1 L686): if `j ≺_{A ∪ B} k` with `k ∈ A`, then
`k ≺_{A' ∪ B} j` where `A' = (A ∖ {k}) ∪ {j}`.  The classes must be disjoint, so that `k ∉ B`. -/
theorem IsCloneIn.reverse_left {A B : Finset V} {j k : V} (hd : Disjoint A B)
    (hcl : G.IsCloneIn (↑(A ∪ B) : Set V) j k) (hk : k ∈ A) :
    G.IsCloneIn (↑(insert j (A.erase k) ∪ B) : Set V) k j := by
  obtain ⟨hj, -, hadj⟩ := hcl
  have hjA : j ∉ A := fun h => hj (by simp [h])
  have hjB : j ∉ B := fun h => hj (by simp [h])
  have hkB : k ∉ B := fun h => Finset.disjoint_left.1 hd hk h
  have hjk : j ≠ k := fun e => hjA (e ▸ hk)
  have hjk_adj : G.Adj j k := (hadj k (by simp [hk])).2 (Or.inl rfl)
  refine ⟨?_, ?_, ?_⟩
  · simp [hjk.symm, hkB]
  · simp
  · intro v hv
    simp only [Finset.coe_union, Finset.coe_insert, Finset.coe_erase, Set.mem_union,
      Set.mem_insert_iff, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff] at hv
    by_cases hvj : v = j
    · subst hvj
      exact ⟨fun _ => Or.inl rfl, fun _ => hjk_adj.symm⟩
    · have hvX : v ∈ (↑(A ∪ B) : Set V) := by
        simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
        rcases hv with (h | ⟨h, -⟩) | h
        · exact absurd h hvj
        · exact Or.inl h
        · exact Or.inr h
      have hvk : v ≠ k := by
        rintro rfl
        rcases hv with (h | ⟨-, h⟩) | h
        · exact hvj h
        · exact h rfl
        · exact hkB h
      constructor
      · intro hkv
        exact Or.inr ((hadj v hvX).2 (Or.inr hkv))
      · rintro (h | h)
        · exact absurd h hvj
        · rcases (hadj v hvX).1 h with h' | h'
          · exact absurd h' hvk
          · exact h'

/-- Erasing the introduced vertex and restoring the removed one undoes a replacement. -/
theorem insert_erase_insert_erase {A : Finset V} {j k : V} (hj : j ∉ A) (hk : k ∈ A) :
    insert k ((insert j (A.erase k)).erase j) = A := by
  rw [Finset.erase_insert (fun h => hj (Finset.mem_of_mem_erase h)), Finset.insert_erase hk]

/-- (d) Reversibility of one step (v1 L686: "if `j ≺_L k`, then `k ≺_{L'} j`"). -/
theorem ClassStep.reverse {j k : V} (hs : G.IsHoleClasses s) (h : G.ClassStep s (j, k) s') :
    G.ClassStep s' (k, j) s := by
  have hd := hs.disjoint
  cases h with
  | @a A B j k hcl hk =>
    have hjA : j ∉ A := fun h => hcl.1 (by simp [h])
    have hrev := IsCloneIn.reverse_left (G := G) hd hcl hk
    have hstep := ClassStep.a (G := G) (B := B) hrev (Finset.mem_insert_self j (A.erase k))
    rwa [insert_erase_insert_erase hjA hk] at hstep
  | @b A B j k hcl hk =>
    have hjB : j ∉ B := fun h => hcl.1 (by simp [h])
    have hrev := IsCloneIn.reverse_left (G := G) hd.symm (by rwa [Finset.union_comm]) hk
    rw [Finset.union_comm] at hrev
    have hstep := ClassStep.b (G := G) (A := A) hrev (Finset.mem_insert_self j (B.erase k))
    rwa [insert_erase_insert_erase hjB hk] at hstep

/-- (d) Runs reverse: `ClassRun s w s'` gives `ClassRun s' (reverseWord w) s`. -/
theorem ClassRun.reverse {w : List (V × V)} (hs : G.IsHoleClasses s) (h : G.ClassRun s w s') :
    G.ClassRun s' (reverseWord w) s := by
  induction h with
  | nil => exact ClassRun.nil _
  | @cons s₁ s₂ s₃ p w hstep _ ih =>
    obtain ⟨j, k⟩ := p
    rw [reverseWord_cons]
    exact (ih (hstep.isHoleClasses hs)).append
      (ClassRun.single (hstep.reverse hs))

/-- Swapping the two classes commutes with a step. -/
theorem ClassStep.swap {p : V × V} (h : G.ClassStep s p s') : G.ClassStep s.swap p s'.swap := by
  cases h with
  | @a A B j k hcl hk =>
    rw [Finset.union_comm] at hcl
    exact ClassStep.b (G := G) (A := B) (B := A) hcl hk
  | @b A B j k hcl hk =>
    rw [Finset.union_comm] at hcl
    exact ClassStep.a (G := G) (A := B) (B := A) hcl hk

theorem ClassStep.swap_iff {p : V × V} :
    G.ClassStep s.swap p s'.swap ↔ G.ClassStep s p s' :=
  ⟨fun h => by simpa using h.swap, ClassStep.swap⟩

/-- Swapping the two classes commutes with a run. -/
theorem ClassRun.swap {w : List (V × V)} (h : G.ClassRun s w s') :
    G.ClassRun s.swap w s'.swap := by
  induction h with
  | nil => exact ClassRun.nil _
  | cons hstep _ ih => exact ClassRun.cons hstep.swap ih

/-- (d) Runs commute with swapping the two classes. -/
theorem ClassRun.swap_iff {w : List (V × V)} :
    G.ClassRun s.swap w s'.swap ↔ G.ClassRun s w s' :=
  ⟨fun h => by simpa using h.swap, ClassRun.swap⟩

/-! ### Fact (e): runs stay in one deformation closure -/

/-- A step out of a hole-class state is a single-vertex deformation step between the carriers. -/
theorem ClassStep.evenHoleDeformationStep {p : V × V} (hs : G.IsHoleClasses s)
    (h : G.ClassStep s p s') :
    G.EvenHoleDeformationStep (↑(s.1 ∪ s.2) : Set V) (↑(s'.1 ∪ s'.2) : Set V) := by
  obtain ⟨j, k⟩ := p
  obtain ⟨n, L, i, hi, -, -, hcase⟩ := h.exists_cloneAt hs
  refine ⟨n, L, j, i, hi, Or.inl ⟨?_, ?_⟩⟩
  · rcases hcase with ⟨h1, h2, -, -⟩ | ⟨h1, h2, -, -⟩
    · rw [← h1, ← h2, L.coe_image_a_union_image_b]
    · rw [← h1, ← h2, Finset.union_comm, L.coe_image_a_union_image_b]
  · rw [← L.deform_carrier hi]
    rcases hcase with ⟨-, -, h1, h2⟩ | ⟨-, -, h1, h2⟩
    · rw [← h1, ← h2, (L.deform hi).coe_image_a_union_image_b]
    · rw [← h1, ← h2, Finset.union_comm, (L.deform hi).coe_image_a_union_image_b]

/-- (e) The carriers visited by a run lie in one deformation closure `⟨C⟩` (v1 Definition 12,
L700). -/
theorem ClassRun.inEvenHoleDeformationClosure {w : List (V × V)} (hs : G.IsHoleClasses s)
    (h : G.ClassRun s w s') :
    InEvenHoleDeformationClosure G (↑(s.1 ∪ s.2) : Set V) (↑(s'.1 ∪ s'.2) : Set V) := by
  induction h with
  | nil => exact InEvenHoleDeformationClosure.refl _
  | cons hstep _ ih =>
    exact (hstep.evenHoleDeformationStep hs).inClosure.trans (ih (hstep.isHoleClasses hs))

end HoleClasses

end SimpleGraph
