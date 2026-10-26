import FreeFermionGraphs.T3HoleClassRun
import FreeFermionGraphs.T3OddBlock

/-!
# Fixed-pairing-type deformations: definitions and run bookkeeping

This module formalises the fixed-pairing-type deformation `O = (P^{(r)})_{r=0}^m` of an even hole
`C` by vertices of an even hole `C'` (arXiv 2305.15625 v1, Definition 19
`definition:fixedpairingtypedeformation`, L978-994) as *data*, together with its word, its toggles,
and the palindromic condition (v1 L965-967, L1015-1021).  Both holes are presented by their
colouring classes, `s = (C_a, C_b)` and `s' = (C'_c, C'_d)` (`SimpleGraph.IsHoleClasses`), and the
pairing is fixed to `a ↔ c`, `b ↔ d`: the other pairing is the same notion for `s'.swap`.

* `SimpleGraph.SideBlock s s'` is an oriented odd block (`OddBlock`) of `G[C_a ⊕ C'_c]` (side 1) or
  of `G[C_b ⊕ C'_d]` (side 2), with `support`, `word`, `RunsFrom`, `RunsBack` and `reverse`.
* `SimpleGraph.FPDeformation s s'` is a list of side blocks with pairwise distinct supports
  (v1 Corollary 7, L1048).  Its `word` is the flattened block words, `toggle₁` / `toggle₂` are the
  `⊕` of the side-1 / side-2 supports, `toggle = toggle₁ ⊕ toggle₂`, and `fwdEnd`, `bwdEnd` are the
  states `(s.1 ⊕ toggle₁, s.2 ⊕ toggle₂)` and `(s'.1 ⊕ toggle₁, s'.2 ⊕ toggle₂)`.
* `FPDeformation.Palindromic D` says that the word of `D` runs from `s` and the reversed word runs
  from `s'`; `FPDeformation.IsOdd D` says that `c(T, C)` is odd, the parity which decides whether the
  commutator of the end carriers `C ⊕ T`, `C' ⊕ T` is the negative of that of `C`, `C'`; `single`
  and `cons` build deformations.

## Main results

* `FPDeformation.toggle₁_subset`, `toggle₂_subset`: the toggles lie in `C_a ⊕ C'_c` and `C_b ⊕ C'_d`.
* `FPDeformation.classRun_eq_fwdEnd`, `classRun_reverse_eq_bwdEnd`: a forward run of the word from
  `s` ends at `fwdEnd`, and a backward run of the reversed word from `s'` ends at `bwdEnd`.  The
  proof goes block by block (`SideBlock.eq_of_classRun_flatMap`): a side-1 block removes vertices of
  the first class, so each of its steps is a `ClassStep.a`, and changes that class by `⊕ support`.
* `FPDeformation.cross_fwd`, `cross_bwd`: if a vertex of a side-1 block lies in the second class of
  the start state, then a side-2 block toggles it (and symmetrically): a clone step cannot introduce
  a vertex which is still in the hole.
* `FPDeformation.carrier_fwdEnd`, `carrier_bwdEnd`: for a palindromic `D` the end carriers are
  `C ⊕ T` and `C' ⊕ T`, with `T = toggle₁ ⊕ toggle₂`.  This holds although a vertex can lie in two
  blocks (v1 Corollary 8, L1053-1064): it then lies in both toggles, hence not in `T`, and stays in
  the hole.  This is v1's bookkeeping `C^{(m)} = C ⊕ ⊕_r P^{(r)}` (Definition 19, L986; also L1220
  and L1787), now proved to be the carrier actually reached by the run.  The single-path formula
  `C̃ = C ⊕ P` (L966) must not be read with the union `∂O` (L990) in place of `P`, since a shared
  vertex lies in `∂O` but not in `T`.
* `FPDeformation.Palindromic.isHoleClasses_ends` and `Palindromic.inClosure`: the end states are
  hole-class states and the carriers `C ⊕ T`, `C' ⊕ T` lie in the deformation closures `⟨C⟩`,
  `⟨C'⟩` (v1 Definition 12, L700).

Claw-freeness is not used anywhere in this module.
-/

open scoped symmDiff

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- The vertices of a word, step by step: for each step `(j, k)` the introduced vertex `j`
followed by the removed vertex `k`. -/
def wordVertices (w : List (V × V)) : List V := w.flatMap fun p => [p.1, p.2]

@[simp]
theorem wordVertices_nil : wordVertices ([] : List (V × V)) = [] := rfl

@[simp]
theorem wordVertices_cons (p : V × V) (w : List (V × V)) :
    wordVertices (p :: w) = p.1 :: p.2 :: wordVertices w := by
  simp [wordVertices]

section RunLemmas

variable [DecidableEq V] {s t t' t'' : Finset V × Finset V}

/-- A run on the empty word does not move. -/
theorem ClassRun.eq_of_nil (h : G.ClassRun s [] t) : t = s := by
  cases h
  rfl

/-- Inversion of a run on a nonempty word. -/
theorem ClassRun.exists_of_cons {p : V × V} {w : List (V × V)}
    (h : G.ClassRun s (p :: w) t'') : ∃ t', G.ClassStep s p t' ∧ G.ClassRun t' w t'' := by
  cases h with
  | cons h₁ h₂ => exact ⟨_, h₁, h₂⟩

/-- A run on a concatenated word factors through an intermediate state. -/
theorem ClassRun.exists_of_append {w₁ w₂ : List (V × V)}
    (h : G.ClassRun s (w₁ ++ w₂) t'') : ∃ t, G.ClassRun s w₁ t ∧ G.ClassRun t w₂ t'' := by
  induction w₁ generalizing s with
  | nil => exact ⟨s, ClassRun.nil s, by simpa using h⟩
  | cons p w ih =>
    obtain ⟨t', hstep, hrun⟩ := ClassRun.exists_of_cons (by simpa using h)
    obtain ⟨t, h₁, h₂⟩ := ih hrun
    exact ⟨t, ClassRun.cons hstep h₁, h₂⟩

/-- A run whose removed vertices all lie in the first class, on a word without repeated
vertices, only changes the first class: it replaces the removed vertices by the introduced ones,
`t.1 ⊕ vertices`.  Moreover every introduced vertex was outside both classes at the start. -/
theorem ClassRun.eq_of_snd_mem_fst {w : List (V × V)} (h : G.ClassRun t w t')
    (ht : G.IsHoleClasses t) (hk : ∀ p ∈ w, p.2 ∈ t.1) (hnd : (wordVertices w).Nodup) :
    t' = (symmDiff t.1 (wordVertices w).toFinset, t.2) ∧
      ∀ p ∈ w, p.1 ∉ t.1 ∧ p.1 ∉ t.2 := by
  induction h with
  | nil s => exact ⟨Prod.ext (symmDiff_bot _).symm rfl, by simp⟩
  | @cons s s₁ s₂ p w hstep hrun ih =>
    obtain ⟨j, k⟩ := p
    have ht₁ := hstep.isHoleClasses ht
    have hnd' : (j :: k :: wordVertices w).Nodup := by simpa using hnd
    have hjk : j ∉ k :: wordVertices w := (List.nodup_cons.1 hnd').1
    have hkw : k ∉ wordVertices w := (List.nodup_cons.1 (List.nodup_cons.1 hnd').2).1
    have hnd'' : (wordVertices w).Nodup := (List.nodup_cons.1 (List.nodup_cons.1 hnd').2).2
    cases hstep with
    | b hcl hkB =>
      exfalso
      have hd := ht.disjoint
      exact Finset.disjoint_left.1 hd (hk (j, k) (List.mem_cons_self ..)) hkB
    | @a A B j k hcl hkA =>
      have hjA : j ∉ A := fun h => hcl.1 (by simp [h])
      have hjB : j ∉ B := fun h => hcl.1 (by simp [h])
      have hjw : j ∉ wordVertices w := fun h => hjk (List.mem_cons_of_mem _ h)
      have hjk' : j ≠ k := fun h => hjk (by simp [h])
      have hsnd : ∀ q ∈ w, q.2 ∈ wordVertices w := fun q hq => by
        simp only [wordVertices, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
        exact ⟨q, hq, Or.inr rfl⟩
      have hfst : ∀ q ∈ w, q.1 ∈ wordVertices w := fun q hq => by
        simp only [wordVertices, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
        exact ⟨q, hq, Or.inl rfl⟩
      have hk' : ∀ q ∈ w, q.2 ∈ (insert j (A.erase k), B).1 := fun q hq => by
        have hqA : q.2 ∈ A := hk q (List.mem_cons_of_mem _ hq)
        refine Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨?_, hqA⟩)
        rintro rfl
        exact hkw (hsnd q hq)
      obtain ⟨hend, hintro⟩ := ih ht₁ hk' hnd''
      refine ⟨?_, ?_⟩
      · rw [hend]
        refine Prod.ext ?_ rfl
        show symmDiff (insert j (A.erase k)) (wordVertices w).toFinset =
          symmDiff A (wordVertices ((j, k) :: w)).toFinset
        ext v
        by_cases hvj : v = j
        · subst hvj
          simp [Finset.mem_symmDiff, hjA, hjw, hjk']
        · by_cases hvk : v = k
          · subst hvk
            simp [Finset.mem_symmDiff, hkA, hkw, hjk'.symm]
          · simp [Finset.mem_symmDiff, hvj, hvk]
      · intro q hq
        rcases List.mem_cons.1 hq with rfl | hqw
        · exact ⟨fun h => hjA h, hjB⟩
        · obtain ⟨h1, h2⟩ := hintro q hqw
          refine ⟨fun h => h1 (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨?_, h⟩)), h2⟩
          intro hqk
          exact hkw (hqk ▸ hfst q hqw)
/-- The second-class version of `ClassRun.eq_of_snd_mem_fst`, by swapping the two classes. -/
theorem ClassRun.eq_of_snd_mem_snd {w : List (V × V)} (h : G.ClassRun t w t')
    (ht : G.IsHoleClasses t) (hk : ∀ p ∈ w, p.2 ∈ t.2) (hnd : (wordVertices w).Nodup) :
    t' = (t.1, symmDiff t.2 (wordVertices w).toFinset) ∧
      ∀ p ∈ w, p.1 ∉ t.1 ∧ p.1 ∉ t.2 := by
  obtain ⟨h₁, h₂⟩ := ClassRun.eq_of_snd_mem_fst h.swap ht.swap hk hnd
  refine ⟨?_, fun p hp => ⟨(h₂ p hp).2, (h₂ p hp).1⟩⟩
  have := congrArg Prod.swap h₁
  simpa using this

end RunLemmas

namespace OddBlock

variable [DecidableEq V] {X Y : Finset V}

theorem toFinset_wordVertices (P : G.OddBlock X Y) :
    (wordVertices P.word).toFinset = P.support := by
  ext v
  rw [List.mem_toFinset, mem_support_iff_exists_mem_word]
  simp only [wordVertices, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]

/-- The vertices of the word of a block are pairwise distinct (the path is injective). -/
theorem nodup_wordVertices (P : G.OddBlock X Y) : (wordVertices P.word).Nodup := by
  unfold wordVertices
  rw [List.nodup_flatMap]
  refine ⟨fun p hp => ?_, ?_⟩
  · have := (adj_of_mem_word hp).ne
    simp [this]
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    rw [getElem_word P i hi, getElem_word P j hj]
    have hne : ∀ a b : Fin P.path.card, a.val ≠ b.val → P.path.vertex a ≠ P.path.vertex b :=
      fun a b hab h => hab (congrArg Fin.val (P.path.injective h))
    intro a ha hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with hb | hb
    · exact hne _ _ (by simp; omega) hb.symm
    · exact hne _ _ (by simp; omega) hb.symm
    · exact hne _ _ (by simp; omega) hb.symm
    · exact hne _ _ (by simp; omega) hb.symm

variable {t t' : Finset V × Finset V}

/-- A block of `(X, Y)` run from a hole-class state whose first class contains the
removed vertices `X ∩ P.support` replaces its removed vertices by its introduced ones in the first
class, `t.1 ⊕ P.support`, and leaves the second class alone.  The vertices of the block are not in
the second class at the start. -/
theorem eq_of_classRun_fst (P : G.OddBlock X Y) (ht : G.IsHoleClasses t)
    (hX : ∀ v ∈ P.support, v ∈ X → v ∈ t.1) (h : G.ClassRun t P.word t') :
    t' = (symmDiff t.1 P.support, t.2) ∧ ∀ v ∈ P.support, v ∉ t.2 := by
  have hk : ∀ p ∈ P.word, p.2 ∈ t.1 := fun p hp =>
    hX _ (snd_mem_support hp) (Finset.mem_sdiff.1 (snd_mem hp)).1
  obtain ⟨h₁, h₂⟩ := ClassRun.eq_of_snd_mem_fst h ht hk P.nodup_wordVertices
  rw [toFinset_wordVertices] at h₁
  refine ⟨h₁, fun v hv => ?_⟩
  obtain ⟨p, hp, rfl | rfl⟩ := mem_support_iff_exists_mem_word.1 hv
  · exact (h₂ p hp).2
  · exact Finset.disjoint_left.1 ht.disjoint (hk p hp)

/-- The second-class version of `eq_of_classRun_fst`. -/
theorem eq_of_classRun_snd (P : G.OddBlock X Y) (ht : G.IsHoleClasses t)
    (hX : ∀ v ∈ P.support, v ∈ X → v ∈ t.2) (h : G.ClassRun t P.word t') :
    t' = (t.1, symmDiff t.2 P.support) ∧ ∀ v ∈ P.support, v ∉ t.1 := by
  have hk : ∀ p ∈ P.word, p.2 ∈ t.2 := fun p hp =>
    hX _ (snd_mem_support hp) (Finset.mem_sdiff.1 (snd_mem hp)).1
  obtain ⟨h₁, h₂⟩ := ClassRun.eq_of_snd_mem_snd h ht hk P.nodup_wordVertices
  rw [toFinset_wordVertices] at h₁
  refine ⟨h₁, fun v hv => ?_⟩
  obtain ⟨p, hp, rfl | rfl⟩ := mem_support_iff_exists_mem_word.1 hv
  · exact (h₂ p hp).1
  · exact Finset.disjoint_right.1 ht.disjoint (hk p hp)

end OddBlock

/-- A *side block* of a fixed-pairing deformation from `s = (C_a, C_b)` towards
`s' = (C'_c, C'_d)` with the pairing `a ↔ c`, `b ↔ d` (v1 Definition 19, L978-994): an odd block
of `G[C_a ⊕ C'_c]` (side 1) or of `G[C_b ⊕ C'_d]` (side 2).  The other pairing is the same
construction for `s'.swap`. -/
abbrev SideBlock (G : SimpleGraph V) [DecidableEq V] (s s' : Finset V × Finset V) :=
  G.OddBlock s.1 s'.1 ⊕ G.OddBlock s.2 s'.2

namespace SideBlock

variable [DecidableEq V] {s s' : Finset V × Finset V}

/-- The vertex set of a side block. -/
def support : G.SideBlock s s' → Finset V
  | .inl P => P.support
  | .inr P => P.support

/-- The word of a side block (the sequence of `(introduced, removed)` pairs). -/
def word : G.SideBlock s s' → List (V × V)
  | .inl P => P.word
  | .inr P => P.word

/-- The side block runs forward from `s` as one whole block. -/
def RunsFrom (B : G.SideBlock s s') : Prop := ∃ t, G.ClassRun s B.word t

/-- The reversed word of the side block is a run from `s'`: the block runs backward from `s'`. -/
def RunsBack (B : G.SideBlock s s') : Prop := ∃ t, G.ClassRun s' (reverseWord B.word) t

/-- The side block read backwards, as a side block from `s'` towards `s` (`OddBlock.reverse` on
the side that carries it). -/
def reverse : G.SideBlock s s' → G.SideBlock s' s
  | .inl P => .inl P.reverse
  | .inr P => .inr P.reverse

@[simp] theorem support_inl (P : G.OddBlock s.1 s'.1) :
    SideBlock.support (Sum.inl P : G.SideBlock s s') = P.support := rfl

@[simp] theorem support_inr (P : G.OddBlock s.2 s'.2) :
    SideBlock.support (Sum.inr P : G.SideBlock s s') = P.support := rfl

@[simp] theorem word_inl (P : G.OddBlock s.1 s'.1) :
    SideBlock.word (Sum.inl P : G.SideBlock s s') = P.word := rfl

@[simp] theorem word_inr (P : G.OddBlock s.2 s'.2) :
    SideBlock.word (Sum.inr P : G.SideBlock s s') = P.word := rfl

@[simp] theorem reverse_inl (P : G.OddBlock s.1 s'.1) :
    SideBlock.reverse (Sum.inl P : G.SideBlock s s') = Sum.inl P.reverse := rfl

@[simp] theorem reverse_inr (P : G.OddBlock s.2 s'.2) :
    SideBlock.reverse (Sum.inr P : G.SideBlock s s') = Sum.inr P.reverse := rfl

theorem support_reverse (B : G.SideBlock s s') : B.reverse.support = B.support := by
  cases B <;> simp [OddBlock.reverse_support]

theorem word_reverse (B : G.SideBlock s s') : B.reverse.word = reverseWord B.word := by
  cases B <;> simp [OddBlock.reverse_word]

@[simp] theorem reverse_reverse (B : G.SideBlock s s') : B.reverse.reverse = B := by
  cases B <;> simp

theorem runsFrom_reverse_iff (B : G.SideBlock s s') : B.reverse.RunsFrom ↔ B.RunsBack := by
  simp [RunsFrom, RunsBack, word_reverse]

theorem runsBack_reverse_iff (B : G.SideBlock s s') : B.reverse.RunsBack ↔ B.RunsFrom := by
  simp [RunsFrom, RunsBack, word_reverse]

/-- The support of a side block lies in the symmetric difference of the classes it connects. -/
theorem support_subset (B : G.SideBlock s s') :
    B.support ⊆ symmDiff s.1 s'.1 ∪ symmDiff s.2 s'.2 := by
  cases B with
  | inl P => exact fun v hv => Finset.mem_union_left _ (P.support_subset_symmDiff hv)
  | inr P => exact fun v hv => Finset.mem_union_right _ (P.support_subset_symmDiff hv)

/-! ### Toggles of a list of side blocks -/

/-- The toggle of the side-1 blocks of a list: the `⊕` of their supports. -/
def listToggle₁ (bs : List (G.SideBlock s s')) : Finset V :=
  bs.foldr (fun B T => match B with | .inl P => symmDiff P.support T | .inr _ => T) ∅

/-- The toggle of the side-2 blocks of a list: the `⊕` of their supports. -/
def listToggle₂ (bs : List (G.SideBlock s s')) : Finset V :=
  bs.foldr (fun B T => match B with | .inr P => symmDiff P.support T | .inl _ => T) ∅

@[simp] theorem listToggle₁_nil : listToggle₁ ([] : List (G.SideBlock s s')) = ∅ := rfl

@[simp] theorem listToggle₂_nil : listToggle₂ ([] : List (G.SideBlock s s')) = ∅ := rfl

theorem listToggle₁_cons_inl (P : G.OddBlock s.1 s'.1) (bs : List (G.SideBlock s s')) :
    listToggle₁ (Sum.inl P :: bs) = symmDiff P.support (listToggle₁ bs) := rfl

theorem listToggle₁_cons_inr (P : G.OddBlock s.2 s'.2) (bs : List (G.SideBlock s s')) :
    listToggle₁ (Sum.inr P :: bs) = listToggle₁ bs := rfl

theorem listToggle₂_cons_inl (P : G.OddBlock s.1 s'.1) (bs : List (G.SideBlock s s')) :
    listToggle₂ (Sum.inl P :: bs) = listToggle₂ bs := rfl

theorem listToggle₂_cons_inr (P : G.OddBlock s.2 s'.2) (bs : List (G.SideBlock s s')) :
    listToggle₂ (Sum.inr P :: bs) = symmDiff P.support (listToggle₂ bs) := rfl

theorem listToggle₁_subset (bs : List (G.SideBlock s s')) :
    listToggle₁ bs ⊆ symmDiff s.1 s'.1 := by
  induction bs with
  | nil => simp
  | cons B bs ih =>
    cases B with
    | inl P =>
      rw [listToggle₁_cons_inl]
      exact (symmDiff_le_sup (a := P.support) (b := listToggle₁ bs)).trans
        (Finset.union_subset P.support_subset_symmDiff ih)
    | inr P => exact ih

theorem listToggle₂_subset (bs : List (G.SideBlock s s')) :
    listToggle₂ bs ⊆ symmDiff s.2 s'.2 := by
  induction bs with
  | nil => simp
  | cons B bs ih =>
    cases B with
    | inl P => exact ih
    | inr P =>
      rw [listToggle₂_cons_inr]
      exact (symmDiff_le_sup (a := P.support) (b := listToggle₂ bs)).trans
        (Finset.union_subset P.support_subset_symmDiff ih)

/-- A side-1 block whose support is not the support of a block of the list is disjoint from the
side-1 toggle of the list (distinct components of `G[C_a ⊕ C'_c]` are disjoint). -/
theorem disjoint_listToggle₁ (P : G.OddBlock s.1 s'.1) (bs : List (G.SideBlock s s'))
    (h : P.support ∉ bs.map SideBlock.support) : Disjoint P.support (listToggle₁ bs) := by
  induction bs with
  | nil => simp
  | cons B bs ih =>
    rw [List.map_cons, List.mem_cons, not_or] at h
    cases B with
    | inl Q =>
      rw [listToggle₁_cons_inl]
      exact Disjoint.mono_right symmDiff_le_sup
        (disjoint_sup_right.2 ⟨OddBlock.disjoint_of_support_ne P Q h.1, ih h.2⟩)
    | inr Q => exact ih h.2

/-- The side-2 version of `disjoint_listToggle₁`. -/
theorem disjoint_listToggle₂ (P : G.OddBlock s.2 s'.2) (bs : List (G.SideBlock s s'))
    (h : P.support ∉ bs.map SideBlock.support) : Disjoint P.support (listToggle₂ bs) := by
  induction bs with
  | nil => simp
  | cons B bs ih =>
    rw [List.map_cons, List.mem_cons, not_or] at h
    cases B with
    | inl Q => exact ih h.2
    | inr Q =>
      rw [listToggle₂_cons_inr]
      exact Disjoint.mono_right symmDiff_le_sup
        (disjoint_sup_right.2 ⟨OddBlock.disjoint_of_support_ne P Q h.1, ih h.2⟩)

/-- For blocks with distinct supports the side-1 toggle is the union of the side-1 supports. -/
theorem mem_listToggle₁ {bs : List (G.SideBlock s s')} (hnd : (bs.map SideBlock.support).Nodup)
    {v : V} : v ∈ listToggle₁ bs ↔ ∃ P : G.OddBlock s.1 s'.1, (Sum.inl P : G.SideBlock s s') ∈ bs ∧
      v ∈ P.support := by
  induction bs with
  | nil => simp
  | cons B bs ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    cases B with
    | inl Q =>
      have hd := disjoint_listToggle₁ Q bs hnd.1
      rw [listToggle₁_cons_inl, Finset.mem_symmDiff, ih hnd.2]
      constructor
      · rintro (⟨hv, -⟩ | ⟨⟨P, hP, hv⟩, -⟩)
        · exact ⟨Q, List.mem_cons_self .., hv⟩
        · exact ⟨P, List.mem_cons_of_mem _ hP, hv⟩
      · rintro ⟨P, hP, hv⟩
        rcases List.mem_cons.1 hP with h | hP
        · cases h
          exact Or.inl ⟨hv, fun ⟨P', hP', hv'⟩ =>
            Finset.disjoint_left.1 hd hv ((ih hnd.2).2 ⟨P', hP', hv'⟩)⟩
        · refine Or.inr ⟨⟨P, hP, hv⟩, fun hvQ => ?_⟩
          exact Finset.disjoint_left.1 hd hvQ ((ih hnd.2).2 ⟨P, hP, hv⟩)
    | inr Q =>
      rw [listToggle₁_cons_inr, ih hnd.2]
      constructor
      · rintro ⟨P, hP, hv⟩
        exact ⟨P, List.mem_cons_of_mem _ hP, hv⟩
      · rintro ⟨P, hP, hv⟩
        rcases List.mem_cons.1 hP with h | hP
        · cases h
        · exact ⟨P, hP, hv⟩

/-- Run bookkeeping for a list of side blocks with distinct supports, from an arbitrary
hole-class state `t` which agrees with `s` on the blocks that have not yet run (each side-1 block
vertex of `s.1` is still in `t.1`, and likewise on side 2).

* the run ends at `(t.1 ⊕ toggle₁, t.2 ⊕ toggle₂)`: a side-1 block removes its `X ∖ Y` vertices
  from the first class (they are in the first class, hence not in the second, so every step is a
  `ClassStep.a`) and introduces its `Y ∖ X` vertices there; side-2 blocks do the same in the
  second class;
* a vertex of a side-1 block which is in the second class `t.2` must be toggled by a side-2 block
  (otherwise it would be introduced while still occupied, which a clone step forbids), and
  symmetrically for side-2 blocks.  This is the cross-vertex phenomenon: a vertex in two blocks is
  removed by one and introduced by the other. -/
theorem eq_of_classRun_flatMap (bs : List (G.SideBlock s s'))
    (hnd : (bs.map SideBlock.support).Nodup) {t tf : Finset V × Finset V}
    (ht : G.IsHoleClasses t)
    (h₁ : ∀ v ∈ listToggle₁ bs, v ∈ s.1 → v ∈ t.1)
    (h₂ : ∀ v ∈ listToggle₂ bs, v ∈ s.2 → v ∈ t.2)
    (h : G.ClassRun t (bs.flatMap SideBlock.word) tf) :
    tf = (symmDiff t.1 (listToggle₁ bs), symmDiff t.2 (listToggle₂ bs)) ∧
      (∀ v ∈ listToggle₁ bs, v ∈ t.2 → v ∈ listToggle₂ bs) ∧
      (∀ v ∈ listToggle₂ bs, v ∈ t.1 → v ∈ listToggle₁ bs) := by
  induction bs generalizing t with
  | nil =>
    have := ClassRun.eq_of_nil (by simpa using h)
    subst this
    exact ⟨Prod.ext (symmDiff_bot _).symm (symmDiff_bot _).symm, by simp, by simp⟩
  | cons B bs ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.flatMap_cons] at h
    obtain ⟨t₁, hB, hrest⟩ := ClassRun.exists_of_append h
    have ht₁ := hB.isHoleClasses ht
    cases B with
    | inl P =>
      have hd := disjoint_listToggle₁ P bs hnd.1
      have hmem : ∀ v, v ∈ listToggle₁ (Sum.inl P :: bs : List (G.SideBlock s s')) ↔
          v ∈ P.support ∨ v ∈ listToggle₁ bs := fun v => by
        rw [listToggle₁_cons_inl, Finset.mem_symmDiff]
        constructor
        · rintro (⟨hv, -⟩ | ⟨hv, -⟩)
          · exact Or.inl hv
          · exact Or.inr hv
        · rintro (hv | hv)
          · exact Or.inl ⟨hv, fun h' => Finset.disjoint_left.1 hd hv h'⟩
          · exact Or.inr ⟨hv, fun h' => Finset.disjoint_left.1 hd h' hv⟩
      obtain ⟨hteq, hdt⟩ := P.eq_of_classRun_fst ht
        (fun v hv => h₁ v ((hmem v).2 (Or.inl hv))) hB
      rw [hteq] at hrest ht₁
      obtain ⟨hend, hc₁, hc₂⟩ := ih hnd.2 ht₁
        (fun v hv hvs => by
          have hvP : v ∉ P.support := fun hvP => Finset.disjoint_left.1 hd hvP hv
          exact Finset.mem_symmDiff.2 (Or.inl ⟨h₁ v ((hmem v).2 (Or.inr hv)) hvs, hvP⟩))
        (fun v hv hvs => h₂ v (by rwa [listToggle₂_cons_inl]) hvs) hrest
      refine ⟨?_, ?_, ?_⟩
      · rw [hend, listToggle₁_cons_inl, listToggle₂_cons_inl, symmDiff_assoc]
      · intro v hv hvt
        rw [listToggle₂_cons_inl]
        rcases (hmem v).1 hv with hvP | hvL
        · exact absurd hvt (hdt v hvP)
        · exact hc₁ v hvL hvt
      · intro v hv hvt
        rw [listToggle₂_cons_inl] at hv
        by_cases hvP : v ∈ P.support
        · exact (hmem v).2 (Or.inl hvP)
        · refine (hmem v).2 (Or.inr (hc₂ v hv ?_))
          exact Finset.mem_symmDiff.2 (Or.inl ⟨hvt, hvP⟩)
    | inr P =>
      have hd := disjoint_listToggle₂ P bs hnd.1
      have hmem : ∀ v, v ∈ listToggle₂ (Sum.inr P :: bs : List (G.SideBlock s s')) ↔
          v ∈ P.support ∨ v ∈ listToggle₂ bs := fun v => by
        rw [listToggle₂_cons_inr, Finset.mem_symmDiff]
        constructor
        · rintro (⟨hv, -⟩ | ⟨hv, -⟩)
          · exact Or.inl hv
          · exact Or.inr hv
        · rintro (hv | hv)
          · exact Or.inl ⟨hv, fun h' => Finset.disjoint_left.1 hd hv h'⟩
          · exact Or.inr ⟨hv, fun h' => Finset.disjoint_left.1 hd h' hv⟩
      obtain ⟨hteq, hdt⟩ := P.eq_of_classRun_snd ht
        (fun v hv => h₂ v ((hmem v).2 (Or.inl hv))) hB
      rw [hteq] at hrest ht₁
      obtain ⟨hend, hc₁, hc₂⟩ := ih hnd.2 ht₁
        (fun v hv hvs => h₁ v (by rwa [listToggle₁_cons_inr]) hvs)
        (fun v hv hvs => by
          have hvP : v ∉ P.support := fun hvP => Finset.disjoint_left.1 hd hvP hv
          exact Finset.mem_symmDiff.2 (Or.inl ⟨h₂ v ((hmem v).2 (Or.inr hv)) hvs, hvP⟩)) hrest
      refine ⟨?_, ?_, ?_⟩
      · rw [hend, listToggle₁_cons_inr, listToggle₂_cons_inr, symmDiff_assoc]
      · intro v hv hvt
        rw [listToggle₁_cons_inr] at hv
        by_cases hvP : v ∈ P.support
        · exact (hmem v).2 (Or.inl hvP)
        · refine (hmem v).2 (Or.inr (hc₁ v hv ?_))
          exact Finset.mem_symmDiff.2 (Or.inl ⟨hvt, hvP⟩)
      · intro v hv hvt
        rw [listToggle₁_cons_inr]
        rcases (hmem v).1 hv with hvP | hvL
        · exact absurd hvt (hdt v hvP)
        · exact hc₂ v hvL hvt

/-- For blocks with distinct supports the side-2 toggle is the union of the side-2 supports. -/
theorem mem_listToggle₂ {bs : List (G.SideBlock s s')} (hnd : (bs.map SideBlock.support).Nodup)
    {v : V} : v ∈ listToggle₂ bs ↔ ∃ P : G.OddBlock s.2 s'.2, (Sum.inr P : G.SideBlock s s') ∈ bs ∧
      v ∈ P.support := by
  induction bs with
  | nil => simp
  | cons B bs ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    cases B with
    | inl Q =>
      rw [listToggle₂_cons_inl, ih hnd.2]
      constructor
      · rintro ⟨P, hP, hv⟩
        exact ⟨P, List.mem_cons_of_mem _ hP, hv⟩
      · rintro ⟨P, hP, hv⟩
        rcases List.mem_cons.1 hP with h | hP
        · cases h
        · exact ⟨P, hP, hv⟩
    | inr Q =>
      have hd := disjoint_listToggle₂ Q bs hnd.1
      rw [listToggle₂_cons_inr, Finset.mem_symmDiff, ih hnd.2]
      constructor
      · rintro (⟨hv, -⟩ | ⟨⟨P, hP, hv⟩, -⟩)
        · exact ⟨Q, List.mem_cons_self .., hv⟩
        · exact ⟨P, List.mem_cons_of_mem _ hP, hv⟩
      · rintro ⟨P, hP, hv⟩
        rcases List.mem_cons.1 hP with h | hP
        · cases h
          exact Or.inl ⟨hv, fun ⟨P', hP', hv'⟩ =>
            Finset.disjoint_left.1 hd hv ((ih hnd.2).2 ⟨P', hP', hv'⟩)⟩
        · refine Or.inr ⟨⟨P, hP, hv⟩, fun hvQ => ?_⟩
          exact Finset.disjoint_left.1 hd hvQ ((ih hnd.2).2 ⟨P, hP, hv⟩)

/-! ### Mirroring a list of side blocks -/

/-- The mirror of a list of side blocks (v1 L1015: "reversing the order of the paths"): reverse
the order of the list and read each block backwards. -/
def mirrorList (bs : List (G.SideBlock s s')) : List (G.SideBlock s' s) :=
  (bs.map SideBlock.reverse).reverse

theorem mirrorList_cons (B : G.SideBlock s s') (bs : List (G.SideBlock s s')) :
    mirrorList (B :: bs) = mirrorList bs ++ [B.reverse] := by
  simp [mirrorList]

/-- The word of the mirror list is the reversed word. -/
theorem flatMap_word_mirrorList (bs : List (G.SideBlock s s')) :
    (mirrorList bs).flatMap SideBlock.word = reverseWord (bs.flatMap SideBlock.word) := by
  induction bs with
  | nil => simp [mirrorList]
  | cons B bs ih =>
    rw [mirrorList_cons, List.flatMap_append, ih]
    simp [reverseWord_append, word_reverse]

theorem map_support_mirrorList (bs : List (G.SideBlock s s')) :
    (mirrorList bs).map SideBlock.support = (bs.map SideBlock.support).reverse := by
  simp [mirrorList, Function.comp_def, support_reverse]

theorem nodup_mirrorList {bs : List (G.SideBlock s s')} (hnd : (bs.map SideBlock.support).Nodup) :
    ((mirrorList bs).map SideBlock.support).Nodup := by
  rw [map_support_mirrorList]
  exact List.nodup_reverse.2 hnd

theorem inl_mem_mirrorList_iff (bs : List (G.SideBlock s s')) (P : G.OddBlock s'.1 s.1) :
    (Sum.inl P : G.SideBlock s' s) ∈ mirrorList bs ↔
      (Sum.inl P.reverse : G.SideBlock s s') ∈ bs := by
  simp only [mirrorList, List.mem_reverse, List.mem_map]
  constructor
  · rintro ⟨B, hB, hBP⟩
    have : B = SideBlock.reverse (Sum.inl P : G.SideBlock s' s) := by
      rw [← hBP, reverse_reverse]
    rw [this] at hB
    exact hB
  · intro h
    exact ⟨_, h, by simp⟩

theorem inr_mem_mirrorList_iff (bs : List (G.SideBlock s s')) (P : G.OddBlock s'.2 s.2) :
    (Sum.inr P : G.SideBlock s' s) ∈ mirrorList bs ↔
      (Sum.inr P.reverse : G.SideBlock s s') ∈ bs := by
  simp only [mirrorList, List.mem_reverse, List.mem_map]
  constructor
  · rintro ⟨B, hB, hBP⟩
    have : B = SideBlock.reverse (Sum.inr P : G.SideBlock s' s) := by
      rw [← hBP, reverse_reverse]
    rw [this] at hB
    exact hB
  · intro h
    exact ⟨_, h, by simp⟩

/-- Mirroring does not change the side-1 toggle. -/
theorem listToggle₁_mirrorList {bs : List (G.SideBlock s s')}
    (hnd : (bs.map SideBlock.support).Nodup) :
    listToggle₁ (mirrorList bs) = listToggle₁ bs := by
  ext v
  rw [mem_listToggle₁ (nodup_mirrorList hnd), mem_listToggle₁ hnd]
  constructor
  · rintro ⟨P, hP, hv⟩
    exact ⟨P.reverse, (inl_mem_mirrorList_iff bs P).1 hP, by rwa [OddBlock.reverse_support]⟩
  · rintro ⟨P, hP, hv⟩
    refine ⟨P.reverse, (inl_mem_mirrorList_iff bs _).2 (by simpa using hP), ?_⟩
    rwa [OddBlock.reverse_support]

/-- Mirroring does not change the side-2 toggle. -/
theorem listToggle₂_mirrorList {bs : List (G.SideBlock s s')}
    (hnd : (bs.map SideBlock.support).Nodup) :
    listToggle₂ (mirrorList bs) = listToggle₂ bs := by
  ext v
  rw [mem_listToggle₂ (nodup_mirrorList hnd), mem_listToggle₂ hnd]
  constructor
  · rintro ⟨P, hP, hv⟩
    exact ⟨P.reverse, (inr_mem_mirrorList_iff bs P).1 hP, by rwa [OddBlock.reverse_support]⟩
  · rintro ⟨P, hP, hv⟩
    refine ⟨P.reverse, (inr_mem_mirrorList_iff bs _).2 (by simpa using hP), ?_⟩
    rwa [OddBlock.reverse_support]

end SideBlock

/-- A *fixed-pairing-type deformation* of `s = (C_a, C_b)` by `s' = (C'_c, C'_d)` with the pairing
`a ↔ c`, `b ↔ d` (v1 Definition 19, L978-994): a finite sequence of odd blocks, each a component of
`G[C_a ⊕ C'_c]` or of `G[C_b ⊕ C'_d]`, with pairwise distinct vertex sets (v1 Corollary 7,
`corollary:pathcomponentsdistinct`, L1048-1051: "the path components of `O` are distinct
subsets").

This is the data of v1 Definition 19 *without* its run condition
`j_{s-1}^{(r)} ≺_{C^{(r,s-1)}} k_{s-1}^{(r)}` (L988-989).  That condition is the existence of a
clone run of the word from `s`, `∃ sf, G.ClassRun s D.word sf`, which is the first conjunct of
`Palindromic`; it is not part of the structure.  Likewise v1 derives the pairwise distinctness of the
supports from the run condition (Corollary 7), whereas here `nodup` is a structure field which every
constructor of an `FPDeformation` must prove.

The order of the list is the order of the blocks; v1's `P^{(0)}, …, P^{(m)}`.  Two blocks of
opposite sides may share a vertex (a vertex of `C_a ∩ C'_d` or `C_b ∩ C'_c`, v1 Corollary 8,
`corollary:vertextwopathcomponents`, L1053-1064): it is removed by one block and introduced by the
other.  The other pairing `a ↔ d`, `b ↔ c` is the same notion for `s'.swap`. -/
@[ext]
structure FPDeformation (G : SimpleGraph V) [DecidableEq V] (s s' : Finset V × Finset V) where
  /-- The blocks `P^{(0)}, …, P^{(m)}`, in order. -/
  blocks : List (G.SideBlock s s')
  /-- The blocks have pairwise distinct supports. -/
  nodup : (blocks.map SideBlock.support).Nodup

namespace FPDeformation

variable [DecidableEq V] {s s' : Finset V × Finset V}

/-- The word of the deformation: the flattened words of its blocks, in order (the sequence
`(j_{s-1}^{(r)}, k_{s-1}^{(r)})` of v1 Definition 19). -/
def word (D : G.FPDeformation s s') : List (V × V) := D.blocks.flatMap SideBlock.word

/-- The toggle of the side-1 blocks: the `⊕` of their supports. -/
def toggle₁ (D : G.FPDeformation s s') : Finset V :=
  D.blocks.foldr (fun B T => match B with | .inl P => symmDiff P.support T | .inr _ => T) ∅

/-- The toggle of the side-2 blocks: the `⊕` of their supports. -/
def toggle₂ (D : G.FPDeformation s s') : Finset V :=
  D.blocks.foldr (fun B T => match B with | .inr P => symmDiff P.support T | .inl _ => T) ∅

/-- The toggle `T = T₁ ⊕ T₂` of the deformation.  The deformed carrier of a palindromic
deformation is `C ⊕ T` (`carrier_fwdEnd`), which is v1's `C^{(m)} = C ⊕ ⊕_r P^{(r)}`
(Definition 19, L986).  It is not `C ⊕ ∂O`, with `∂O` the union of the block supports (v1 L990):
for a single path (v1 L966, `C̃ = C ⊕ P`) `∂O = T`, but a vertex shared by a side-1 and a side-2
block lies in `∂O` and not in `T`. -/
def toggle (D : G.FPDeformation s s') : Finset V := symmDiff D.toggle₁ D.toggle₂

/-- The class state reached by the forward run from `s`: the toggles are applied class by class. -/
def fwdEnd (D : G.FPDeformation s s') : Finset V × Finset V :=
  (symmDiff s.1 D.toggle₁, symmDiff s.2 D.toggle₂)

/-- The class state reached by the backward run from `s'`. -/
def bwdEnd (D : G.FPDeformation s s') : Finset V × Finset V :=
  (symmDiff s'.1 D.toggle₁, symmDiff s'.2 D.toggle₂)

/-- The deformation is *palindromic* (v1 L965-967 and the discussion at L1015-1021): its word is a
clone run out of `s`, and the reversed word is a clone run out of `s'` (the reversed deformation
`O⃖` is a fixed-pairing-type deformation of `C'` by vertices in `C`). -/
def Palindromic (D : G.FPDeformation s s') : Prop :=
  (∃ sf, G.ClassRun s D.word sf) ∧ ∃ s'f, G.ClassRun s' (reverseWord D.word) s'f

/-- The deformation is *odd* when `c(T, C)` is odd, where `c(X, Y) = #{(x, y) ∈ X × Y : x ~ y}` is
`SimpleGraph.crossCount` and `T` is the toggle.  By the frame sign lemma
(`PauliFrustrationRepresentation.commutator_toggle_holeClasses`) the commutator of the hole
operators of the end carriers `C ⊕ T`, `C' ⊕ T` is `(-1)^{c(T, C)}` times the commutator of those
of `C`, `C'`; so for an odd deformation the two terms cancel (v1 L1203-1241).  No sign statement
is used in this module. -/
def IsOdd (D : G.FPDeformation s s') : Prop := Odd (G.crossCount D.toggle (s.1 ∪ s.2))

/-- The deformation with a single block. -/
def single (B : G.SideBlock s s') : G.FPDeformation s s' := ⟨[B], List.nodup_singleton _⟩

/-- Prepend a block whose support is not that of an existing block. -/
def cons (B : G.SideBlock s s') (D : G.FPDeformation s s')
    (hB : B.support ∉ D.blocks.map SideBlock.support) : G.FPDeformation s s' :=
  ⟨B :: D.blocks, List.nodup_cons.2 ⟨hB, D.nodup⟩⟩

theorem toggle₁_eq (D : G.FPDeformation s s') : D.toggle₁ = SideBlock.listToggle₁ D.blocks := rfl

theorem toggle₂_eq (D : G.FPDeformation s s') : D.toggle₂ = SideBlock.listToggle₂ D.blocks := rfl

@[simp] theorem blocks_single (B : G.SideBlock s s') : (single B).blocks = [B] := rfl

@[simp] theorem blocks_cons (B : G.SideBlock s s') (D : G.FPDeformation s s')
    (hB : B.support ∉ D.blocks.map SideBlock.support) : (cons B D hB).blocks = B :: D.blocks := rfl

@[simp] theorem word_single (B : G.SideBlock s s') : (single B).word = B.word := by
  simp [word]

@[simp] theorem word_cons (B : G.SideBlock s s') (D : G.FPDeformation s s')
    (hB : B.support ∉ D.blocks.map SideBlock.support) :
    (cons B D hB).word = B.word ++ D.word := by
  simp [word]

theorem toggle₁_single_inl (P : G.OddBlock s.1 s'.1) :
    (single (Sum.inl P : G.SideBlock s s')).toggle₁ = P.support := by
  simp [toggle₁_eq, SideBlock.listToggle₁_cons_inl]

theorem toggle₁_single_inr (P : G.OddBlock s.2 s'.2) :
    (single (Sum.inr P : G.SideBlock s s')).toggle₁ = ∅ := by
  simp [toggle₁_eq, SideBlock.listToggle₁_cons_inr]

theorem toggle₂_single_inl (P : G.OddBlock s.1 s'.1) :
    (single (Sum.inl P : G.SideBlock s s')).toggle₂ = ∅ := by
  simp [toggle₂_eq, SideBlock.listToggle₂_cons_inl]

theorem toggle₂_single_inr (P : G.OddBlock s.2 s'.2) :
    (single (Sum.inr P : G.SideBlock s s')).toggle₂ = P.support := by
  simp [toggle₂_eq, SideBlock.listToggle₂_cons_inr]

theorem toggle₁_cons_inl (P : G.OddBlock s.1 s'.1) (D : G.FPDeformation s s')
    (hB : SideBlock.support (Sum.inl P : G.SideBlock s s') ∉ D.blocks.map SideBlock.support) :
    (cons (Sum.inl P) D hB).toggle₁ = symmDiff P.support D.toggle₁ := rfl

theorem toggle₁_cons_inr (P : G.OddBlock s.2 s'.2) (D : G.FPDeformation s s')
    (hB : SideBlock.support (Sum.inr P : G.SideBlock s s') ∉ D.blocks.map SideBlock.support) :
    (cons (Sum.inr P) D hB).toggle₁ = D.toggle₁ := rfl

theorem toggle₂_cons_inl (P : G.OddBlock s.1 s'.1) (D : G.FPDeformation s s')
    (hB : SideBlock.support (Sum.inl P : G.SideBlock s s') ∉ D.blocks.map SideBlock.support) :
    (cons (Sum.inl P) D hB).toggle₂ = D.toggle₂ := rfl

theorem toggle₂_cons_inr (P : G.OddBlock s.2 s'.2) (D : G.FPDeformation s s')
    (hB : SideBlock.support (Sum.inr P : G.SideBlock s s') ∉ D.blocks.map SideBlock.support) :
    (cons (Sum.inr P) D hB).toggle₂ = symmDiff P.support D.toggle₂ := rfl

/-! ### The toggles lie in the symmetric differences -/

/-- The side-1 toggle lies in `C_a ⊕ C'_c`. -/
theorem toggle₁_subset (D : G.FPDeformation s s') : D.toggle₁ ⊆ symmDiff s.1 s'.1 :=
  SideBlock.listToggle₁_subset D.blocks

/-- The side-2 toggle lies in `C_b ⊕ C'_d`. -/
theorem toggle₂_subset (D : G.FPDeformation s s') : D.toggle₂ ⊆ symmDiff s.2 s'.2 :=
  SideBlock.listToggle₂_subset D.blocks

/-- The toggle lies in `(C_a ⊕ C'_c) ∪ (C_b ⊕ C'_d)`. -/
theorem toggle_subset (D : G.FPDeformation s s') :
    D.toggle ⊆ symmDiff s.1 s'.1 ∪ symmDiff s.2 s'.2 :=
  (symmDiff_le_sup (a := D.toggle₁) (b := D.toggle₂)).trans
    (Finset.union_subset_union D.toggle₁_subset D.toggle₂_subset)

/-- A vertex is in the side-1 toggle iff it lies in a side-1 block (the supports of the blocks
are pairwise distinct, hence pairwise disjoint on each side). -/
theorem mem_toggle₁ (D : G.FPDeformation s s') {v : V} :
    v ∈ D.toggle₁ ↔ ∃ P : G.OddBlock s.1 s'.1,
      (Sum.inl P : G.SideBlock s s') ∈ D.blocks ∧ v ∈ P.support :=
  SideBlock.mem_listToggle₁ D.nodup

/-- A vertex is in the side-2 toggle iff it lies in a side-2 block. -/
theorem mem_toggle₂ (D : G.FPDeformation s s') {v : V} :
    v ∈ D.toggle₂ ↔ ∃ P : G.OddBlock s.2 s'.2,
      (Sum.inr P : G.SideBlock s s') ∈ D.blocks ∧ v ∈ P.support :=
  SideBlock.mem_listToggle₂ D.nodup

/-! ### Run bookkeeping -/

/-- A forward run of the word of `D` from `s` ends at `fwdEnd`. -/
theorem classRun_eq_fwdEnd (hs : G.IsHoleClasses s) (_hs' : G.IsHoleClasses s')
    (D : G.FPDeformation s s') {sf : Finset V × Finset V} (h : G.ClassRun s D.word sf) :
    sf = D.fwdEnd :=
  (SideBlock.eq_of_classRun_flatMap D.blocks D.nodup hs (fun _ _ hv => hv) (fun _ _ hv => hv)
    h).1

/-- A backward run of the reversed word of `D` from `s'` ends at `bwdEnd`: the run is a forward
run of the mirror list of blocks, whose toggles are those of `D`. -/
theorem classRun_reverse_eq_bwdEnd (_hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s')
    (D : G.FPDeformation s s') {s'f : Finset V × Finset V}
    (h : G.ClassRun s' (reverseWord D.word) s'f) : s'f = D.bwdEnd := by
  have h' : G.ClassRun s' ((SideBlock.mirrorList D.blocks).flatMap SideBlock.word) s'f := by
    rw [SideBlock.flatMap_word_mirrorList]
    exact h
  have := (SideBlock.eq_of_classRun_flatMap (SideBlock.mirrorList D.blocks)
    (SideBlock.nodup_mirrorList D.nodup) hs' (fun _ _ hv => hv) (fun _ _ hv => hv) h').1
  rw [SideBlock.listToggle₁_mirrorList D.nodup, SideBlock.listToggle₂_mirrorList D.nodup] at this
  exact this

/-- The cross vertices of a forward run: a vertex of a side-1 block which lies in `s.2` is toggled
by a side-2 block, and a vertex of a side-2 block which lies in `s.1` is toggled by a side-1 block
(a clone step cannot introduce a vertex which is still in the hole). -/
theorem cross_fwd (hs : G.IsHoleClasses s) (D : G.FPDeformation s s')
    {sf : Finset V × Finset V} (h : G.ClassRun s D.word sf) :
    (∀ v ∈ D.toggle₁, v ∈ s.2 → v ∈ D.toggle₂) ∧ (∀ v ∈ D.toggle₂, v ∈ s.1 → v ∈ D.toggle₁) :=
  (SideBlock.eq_of_classRun_flatMap D.blocks D.nodup hs (fun _ _ hv => hv) (fun _ _ hv => hv)
    h).2

/-- The cross vertices of a backward run: the same statement for `s'` and the reversed word. -/
theorem cross_bwd (hs' : G.IsHoleClasses s') (D : G.FPDeformation s s')
    {s'f : Finset V × Finset V} (h : G.ClassRun s' (reverseWord D.word) s'f) :
    (∀ v ∈ D.toggle₁, v ∈ s'.2 → v ∈ D.toggle₂) ∧
      (∀ v ∈ D.toggle₂, v ∈ s'.1 → v ∈ D.toggle₁) := by
  have h' : G.ClassRun s' ((SideBlock.mirrorList D.blocks).flatMap SideBlock.word) s'f := by
    rw [SideBlock.flatMap_word_mirrorList]
    exact h
  have := (SideBlock.eq_of_classRun_flatMap (SideBlock.mirrorList D.blocks)
    (SideBlock.nodup_mirrorList D.nodup) hs' (fun _ _ hv => hv) (fun _ _ hv => hv) h').2
  rw [SideBlock.listToggle₁_mirrorList D.nodup, SideBlock.listToggle₂_mirrorList D.nodup] at this
  exact this

/-! ### Palindromic deformations -/

/-- The forward run of a palindromic deformation ends at `fwdEnd`. -/
theorem Palindromic.classRun_fwdEnd {D : G.FPDeformation s s'} (hs : G.IsHoleClasses s)
    (hs' : G.IsHoleClasses s') (hD : D.Palindromic) : G.ClassRun s D.word D.fwdEnd := by
  obtain ⟨⟨sf, h⟩, -⟩ := hD
  have := D.classRun_eq_fwdEnd hs hs' h
  subst this
  exact h

/-- The backward run of a palindromic deformation ends at `bwdEnd`. -/
theorem Palindromic.classRun_bwdEnd {D : G.FPDeformation s s'} (hs : G.IsHoleClasses s)
    (hs' : G.IsHoleClasses s') (hD : D.Palindromic) :
    G.ClassRun s' (reverseWord D.word) D.bwdEnd := by
  obtain ⟨-, s'f, h⟩ := hD
  have := D.classRun_reverse_eq_bwdEnd hs hs' h
  subst this
  exact h

/-- The propositional core of the carrier computation.  Here `a, b` say that the vertex lies in
the first and second class of the start state, and `x, y` that it is toggled by the side-1 and the
side-2 blocks.  The classes are disjoint; a vertex toggled on both sides lies in the hole (`hxy`);
and a vertex toggled on one side which lies in the other class is also toggled on the other
side (`c₁`, `c₂`; the cross facts of a run). -/
theorem carrier_prop {a b x y : Prop} (hab : a → ¬b) (hxy : x → y → a ∨ b)
    (c₁ : x → b → y) (c₂ : y → a → x) :
    ((a ∧ ¬x ∨ x ∧ ¬a) ∨ (b ∧ ¬y ∨ y ∧ ¬b)) ↔
      ((a ∨ b) ∧ ¬(x ∧ ¬y ∨ y ∧ ¬x) ∨ (x ∧ ¬y ∨ y ∧ ¬x) ∧ ¬(a ∨ b)) := by
  classical
  by_cases ha : a <;> by_cases hb : b <;> by_cases hx : x <;> by_cases hy : y <;> simp_all

/-- The carrier of the forward end state of a palindromic deformation is `C ⊕ T`.

This agrees with v1's `⊕`-formula `C^{(m)} = C ⊕ ⊕_r P^{(r)}` (Definition 19, L986; also L1220 and
L1787).  What fails is the union reading `C ⊕ ∂O`, with `∂O` the union of the supports (L990), which
v1 does not use for carriers (L966 reads `C̃ = C ⊕ P` for a single path): when two blocks share a
vertex (v1 Corollary 8, L1053), that vertex lies in `∂O` but is toggled twice, once in each class,
so that it lies in the hole before and after.  Here `T = T₁ ⊕ T₂` and the vertex lies in
`T₁ ∩ T₂`, hence not in `T`.

The proof is a case check at each vertex `v`, using that the classes of `s` and of `s'` are
disjoint, that `T₁ ⊆ s.1 ⊕ s'.1`, `T₂ ⊆ s.2 ⊕ s'.2`, and the cross facts `cross_fwd` of the
forward run. -/
theorem carrier_fwdEnd (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s')
    (D : G.FPDeformation s s') (hD : D.Palindromic) :
    D.fwdEnd.1 ∪ D.fwdEnd.2 = symmDiff (s.1 ∪ s.2) D.toggle := by
  obtain ⟨c₁, c₂⟩ := cross_fwd hs D (hD.classRun_fwdEnd hs hs')
  have hd := hs.disjoint
  have hd' := hs'.disjoint
  ext v
  have e₁ : v ∈ D.toggle₁ → (v ∈ s.1 ∧ v ∉ s'.1) ∨ (v ∈ s'.1 ∧ v ∉ s.1) := fun h =>
    Finset.mem_symmDiff.1 (D.toggle₁_subset h)
  have e₂ : v ∈ D.toggle₂ → (v ∈ s.2 ∧ v ∉ s'.2) ∨ (v ∈ s'.2 ∧ v ∉ s.2) := fun h =>
    Finset.mem_symmDiff.1 (D.toggle₂_subset h)
  have hsd : v ∈ s.1 → v ∉ s.2 := fun h => Finset.disjoint_left.1 hd h
  have hsd' : v ∈ s'.1 → v ∉ s'.2 := fun h => Finset.disjoint_left.1 hd' h
  have hxy : v ∈ D.toggle₁ → v ∈ D.toggle₂ → v ∈ s.1 ∨ v ∈ s.2 := by
    intro hx hy
    by_contra hcon
    rw [not_or] at hcon
    rcases e₁ hx with ⟨h₁, -⟩ | ⟨h₁, -⟩
    · exact hcon.1 h₁
    rcases e₂ hy with ⟨h₂, -⟩ | ⟨h₂, -⟩
    · exact hcon.2 h₂
    exact hsd' h₁ h₂
  simp only [fwdEnd, toggle, Finset.mem_union, Finset.mem_symmDiff]
  exact carrier_prop hsd hxy (c₁ v) (c₂ v)

/-- The carrier of the backward end state of a palindromic deformation is `C' ⊕ T`. -/
theorem carrier_bwdEnd (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s')
    (D : G.FPDeformation s s') (hD : D.Palindromic) :
    D.bwdEnd.1 ∪ D.bwdEnd.2 = symmDiff (s'.1 ∪ s'.2) D.toggle := by
  obtain ⟨c₁, c₂⟩ := cross_bwd hs' D (hD.classRun_bwdEnd hs hs')
  have hd := hs.disjoint
  have hd' := hs'.disjoint
  ext v
  have e₁ : v ∈ D.toggle₁ → (v ∈ s.1 ∧ v ∉ s'.1) ∨ (v ∈ s'.1 ∧ v ∉ s.1) := fun h =>
    Finset.mem_symmDiff.1 (D.toggle₁_subset h)
  have e₂ : v ∈ D.toggle₂ → (v ∈ s.2 ∧ v ∉ s'.2) ∨ (v ∈ s'.2 ∧ v ∉ s.2) := fun h =>
    Finset.mem_symmDiff.1 (D.toggle₂_subset h)
  have hsd : v ∈ s.1 → v ∉ s.2 := fun h => Finset.disjoint_left.1 hd h
  have hsd' : v ∈ s'.1 → v ∉ s'.2 := fun h => Finset.disjoint_left.1 hd' h
  have hxy : v ∈ D.toggle₁ → v ∈ D.toggle₂ → v ∈ s'.1 ∨ v ∈ s'.2 := by
    intro hx hy
    by_contra hcon
    rw [not_or] at hcon
    rcases e₁ hx with ⟨h₁, -⟩ | ⟨h₁, -⟩
    swap
    · exact hcon.1 h₁
    rcases e₂ hy with ⟨h₂, -⟩ | ⟨h₂, -⟩
    swap
    · exact hcon.2 h₂
    exact hsd h₁ h₂
  simp only [bwdEnd, toggle, Finset.mem_union, Finset.mem_symmDiff]
  exact carrier_prop hsd' hxy (c₁ v) (c₂ v)

/-- The two end states of a palindromic deformation are hole-class states. -/
theorem Palindromic.isHoleClasses_ends {D : G.FPDeformation s s'} (hs : G.IsHoleClasses s)
    (hs' : G.IsHoleClasses s') (hD : D.Palindromic) :
    G.IsHoleClasses D.fwdEnd ∧ G.IsHoleClasses D.bwdEnd :=
  ⟨(hD.classRun_fwdEnd hs hs').isHoleClasses hs, (hD.classRun_bwdEnd hs hs').isHoleClasses hs'⟩

/-- The carriers `C ⊕ T` and `C' ⊕ T` of a palindromic deformation lie in the deformation
closures `⟨C⟩` and `⟨C'⟩` (v1 Definition 12, L700). -/
theorem Palindromic.inClosure {D : G.FPDeformation s s'} (hs : G.IsHoleClasses s)
    (hs' : G.IsHoleClasses s') (hD : D.Palindromic) :
    InEvenHoleDeformationClosure G (↑(s.1 ∪ s.2) : Set V)
        (symmDiff (↑(s.1 ∪ s.2) : Set V) ↑D.toggle) ∧
      InEvenHoleDeformationClosure G (↑(s'.1 ∪ s'.2) : Set V)
        (symmDiff (↑(s'.1 ∪ s'.2) : Set V) ↑D.toggle) := by
  have h₁ := (hD.classRun_fwdEnd hs hs').inEvenHoleDeformationClosure hs
  have h₂ := (hD.classRun_bwdEnd hs hs').inEvenHoleDeformationClosure hs'
  rw [carrier_fwdEnd hs hs' D hD, Finset.coe_symmDiff] at h₁
  rw [carrier_bwdEnd hs hs' D hD, Finset.coe_symmDiff] at h₂
  exact ⟨h₁, h₂⟩

end FPDeformation

end SimpleGraph
