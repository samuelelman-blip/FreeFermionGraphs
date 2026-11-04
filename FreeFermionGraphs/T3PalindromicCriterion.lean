import FreeFermionGraphs.T3InteractionSymm

/-!
# A step-condition criterion for palindromic deformations

This module proves that a fixed-pairing-type deformation `D : G.FPDeformation s s'` of hole-class
states (arXiv 2305.15625 v1, Definition 19 `definition:fixedpairingtypedeformation`, L978-994) is
palindromic if and only if its blocks satisfy the clone conditions of the block step lemma
(`FreeFermionGraphs.T3BlockStep`) at the time they run, in the forward run out of `s` and in the
backward run out of `s'`.  The direction `Palindromic → conditions` is the bookkeeping of
`FreeFermionGraphs.T3Interaction`; the direction `conditions → Palindromic` is new (the manuscript
checks the clone conditions block by block, L1808-1830, and never states a converse).  The
criterion is the tool for *constructing* palindromic deformations (toggle stability,
`FreeFermionGraphs.T3ToggleStable`).

## Definitions and main results

* `SimpleGraph.StepIndep G w Z`: no step `(j, k)` of the word `w` separates a vertex of `Z`, i.e.
  `j ~ v ↔ k ~ v` for all `v ∈ Z`.  This is the second-class clone condition of the block step lemma
  (`OddBlock.classRun_iff`) in a single statement: the clause `j ∉ Z` is implied, because `j ~ k`
  while `j` is not adjacent to itself.  It does not depend on the direction of the step, so it is
  also the backward condition (`stepIndep_reverseWord_iff`).
* `FPDeformation.not_interacts_iff`: `¬ Interacts P Q ↔ StepIndep G P.word Q.support`.
* `SideBlock.other t B bs`: the class against which the clone steps of the side block `B` are tested
  after the blocks `bs` have run from the state `t`: the second class `t.2 ⊕ T₂(bs)` for a side-1
  block, the first class `t.1 ⊕ T₁(bs)` for a side-2 block.
* `SideBlock.StepConds s s' bs`: for every cut `bs = pre ++ B :: post`, the steps of `B` are
  `StepIndep` against `other s B pre` (forward run) and `other s' B post` (backward run).
* `SideBlock.exists_classRun_of_stepIndep`: the existence of a clone run of the flattened words of a
  list of side blocks, from the forward conditions.
* `FPDeformation.palindromic_iff_stepConds`: **the criterion**, for hole-class states `s`, `s'`.

Claw-freeness is not used anywhere in this module.
-/

open scoped symmDiff

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- **No step of the word `w` separates a vertex of `Z`.**  Every step `(j, k)` of `w` and every
`v ∈ Z` satisfy `j ~ v ↔ k ~ v`.  For a block `P` this is the second-class clone condition of
the block step lemma (`OddBlock.classRun_iff`); it contains the clause `j ∉ Z` because `j ~ k`
and `j` is not adjacent to itself. -/
def StepIndep (G : SimpleGraph V) (w : List (V × V)) (Z : Finset V) : Prop :=
  ∀ p ∈ w, ∀ v ∈ Z, (G.Adj p.1 v ↔ G.Adj p.2 v)

/-- The symmetric difference with the empty finset (stated for `∅`, not `⊥`). -/
@[simp] theorem symmDiff_empty_right' [DecidableEq V] (A : Finset V) : symmDiff A ∅ = A :=
  symmDiff_bot A

namespace StepIndep

variable {w : List (V × V)} {Z Z' : Finset V}

theorem mono (h : StepIndep G w Z) (hZ : Z' ⊆ Z) : StepIndep G w Z' :=
  fun p hp v hv => h p hp v (hZ hv)

theorem empty : StepIndep G w ∅ := fun _ _ v hv => absurd hv (Finset.notMem_empty v)

theorem union [DecidableEq V] (h : StepIndep G w Z) (h' : StepIndep G w Z') :
    StepIndep G w (Z ∪ Z') := by
  intro p hp v hv
  rcases Finset.mem_union.1 hv with hv | hv
  · exact h p hp v hv
  · exact h' p hp v hv

theorem symmDiff' [DecidableEq V] (h : StepIndep G w Z) (h' : StepIndep G w Z') :
    StepIndep G w (symmDiff Z Z') :=
  (h.union h').mono symmDiff_le_sup

theorem iff_forall_singleton : StepIndep G w Z ↔ ∀ v ∈ Z, StepIndep G w {v} := by
  constructor
  · intro h v hv p hp u hu
    rw [Finset.mem_singleton] at hu
    subst hu
    exact h p hp u hv
  · intro h p hp v hv
    exact h v hv p hp v (Finset.mem_singleton_self v)

/-- Two sets which agree on the vertices separated by some step are interchangeable. -/
theorem congr (h : ∀ v, ¬ StepIndep G w {v} → (v ∈ Z ↔ v ∈ Z')) (hZ : StepIndep G w Z) :
    StepIndep G w Z' := by
  rw [iff_forall_singleton] at hZ ⊢
  intro v hv
  by_contra hn
  exact hn (hZ v ((h v hn).2 hv))

end StepIndep

/-- The steps of the reversed word separate the same vertices: `(j, k)` becomes `(k, j)`. -/
theorem stepIndep_reverseWord_iff {w : List (V × V)} {Z : Finset V} :
    StepIndep G (reverseWord w) Z ↔ StepIndep G w Z := by
  have hmem : ∀ p : V × V, p ∈ reverseWord w ↔ p.swap ∈ w := by
    intro p
    simp only [reverseWord, List.mem_reverse, List.mem_map]
    constructor
    · rintro ⟨q, hq, rfl⟩
      simpa using hq
    · intro h
      exact ⟨p.swap, h, by simp⟩
  constructor
  · intro h p hp v hv
    have := h p.swap ((hmem _).2 (by simpa using hp)) v hv
    exact this.symm
  · intro h p hp v hv
    have := h p.swap ((hmem p).1 hp) v hv
    exact this.symm

namespace OddBlock

variable [DecidableEq V] {X Y : Finset V}

/-- A block whose steps do not separate the vertices of `Z` is disjoint from `Z`: a vertex of the
block is the introduced or the removed vertex of a step, which separates itself. -/
theorem disjoint_of_stepIndep (P : G.OddBlock X Y) {Z : Finset V} (h : StepIndep G P.word Z) :
    Disjoint P.support Z := by
  rw [Finset.disjoint_left]
  intro v hv hvZ
  obtain ⟨p, hp, rfl | rfl⟩ := mem_support_iff_exists_mem_word.1 hv
  · exact (G.irrefl) ((h p hp _ hvZ).2 (adj_of_mem_word hp).symm)
  · exact (G.irrefl) ((h p hp _ hvZ).1 (adj_of_mem_word hp))

end OddBlock

namespace FPDeformation

variable [DecidableEq V] {s s' : Finset V × Finset V}

/-- **Non-interaction is a statement about separation.**  `P` does not interact with `Q` iff no step
of `P` separates a vertex of `Q`.  (A step `(j, k)` separates `j` and `k` themselves.) -/
theorem not_interacts_iff (P Q : G.SideBlock s s') :
    ¬ Interacts P Q ↔ StepIndep G P.word Q.support := by
  constructor
  · intro h p hp v hv
    by_contra hne
    apply h
    refine ⟨p, hp, ?_⟩
    by_cases h1 : v = p.1
    · subst h1
      exact Or.inl hv
    by_cases h2 : v = p.2
    · subst h2
      exact Or.inr (Or.inl hv)
    · exact Or.inr (Or.inr ⟨v, hv, h1, h2, hne⟩)
  · rintro h ⟨p, hp, h1 | h2 | ⟨v, hv, -, -, hne⟩⟩
    · have hadj : G.Adj p.1 p.2 := by
        cases P with
        | inl P => exact OddBlock.adj_of_mem_word hp
        | inr P => exact OddBlock.adj_of_mem_word hp
      exact G.irrefl ((h p hp _ h1).2 hadj.symm)
    · have hadj : G.Adj p.1 p.2 := by
        cases P with
        | inl P => exact OddBlock.adj_of_mem_word hp
        | inr P => exact OddBlock.adj_of_mem_word hp
      exact G.irrefl ((h p hp _ h2).1 hadj)
    · exact hne (h p hp v hv)

end FPDeformation

namespace SideBlock

variable [DecidableEq V] {s s' : Finset V × Finset V}

/-- The class against which the clone steps of the side block `B` are tested, after the blocks `bs`
have run from the state `t`: for a side-1 block the second class `t.2 ⊕ T₂(bs)`, for a side-2 block
the first class `t.1 ⊕ T₁(bs)` (the other side is toggled by the blocks of that side which ran). -/
def other (t : Finset V × Finset V) :
    G.SideBlock s s' → List (G.SideBlock s s') → Finset V
  | .inl _, bs => symmDiff t.2 (listToggle₂ bs)
  | .inr _, bs => symmDiff t.1 (listToggle₁ bs)

@[simp] theorem other_inl (t : Finset V × Finset V) (P : G.OddBlock s.1 s'.1)
    (bs : List (G.SideBlock s s')) :
    other t (Sum.inl P : G.SideBlock s s') bs = symmDiff t.2 (listToggle₂ bs) := rfl

@[simp] theorem other_inr (t : Finset V × Finset V) (P : G.OddBlock s.2 s'.2)
    (bs : List (G.SideBlock s s')) :
    other t (Sum.inr P : G.SideBlock s s') bs = symmDiff t.1 (listToggle₁ bs) := rfl

/-- **The step conditions of a list of side blocks** from the base states `s`, `s'`: cutting
`bs = pre ++ B :: post`, the steps of `B` do not separate a vertex of the class against which they
are tested after the blocks `pre` have run from `s` (forward run), nor after the blocks `post` have
run from `s'` (backward run, read backwards). -/
def StepConds (G : SimpleGraph V) (s s' : Finset V × Finset V) (bs : List (G.SideBlock s s')) :
    Prop :=
  ∀ pre B post, bs = pre ++ B :: post →
    StepIndep G B.word (other s B pre) ∧ StepIndep G B.word (other s' B post)

/-! ### Existence of a run from the forward conditions -/

/-- **Existence of a run.**  Let `bs` be a list of side blocks of the hole-class states `s`, `s'`
with pairwise distinct supports, and let `cur` be a hole-class state, agreeing with `s` on the
vertices of the blocks of `bs` (a vertex of a side-1 block is in `cur.1` iff it is in `s.1`, and
likewise on side 2) and contained in `s ∪ s'` classwise.  If for every cut
`bs = pre ++ B :: post` the steps of `B` are `StepIndep` against `other cur B pre`, then the
flattened words of `bs` form a clone run out of `cur`.

The proof is the induction on `bs`: the head block runs by the block step lemma
(`OddBlock.classRun_of_cond`), because it is untoggled in the class of `cur` which it modifies
(its vertices are not in the toggles of the other blocks of the same side).  The case of a side-2
block is the block step lemma for the swapped state. -/
theorem exists_classRun_of_stepIndep (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s') :
    ∀ (bs : List (G.SideBlock s s')), (bs.map SideBlock.support).Nodup →
    ∀ (cur : Finset V × Finset V), G.IsHoleClasses cur →
    (∀ v ∈ listToggle₁ bs, (v ∈ cur.1 ↔ v ∈ s.1)) →
    (∀ v ∈ listToggle₂ bs, (v ∈ cur.2 ↔ v ∈ s.2)) →
    cur.1 ⊆ s.1 ∪ s'.1 → cur.2 ⊆ s.2 ∪ s'.2 →
    (∀ pre B post, bs = pre ++ B :: post → StepIndep G B.word (other cur B pre)) →
    ∃ tf, G.ClassRun cur (bs.flatMap SideBlock.word) tf := by
  intro bs
  induction bs with
  | nil =>
    intro _ cur _ _ _ _ _ _
    exact ⟨cur, by simpa using ClassRun.nil cur⟩
  | cons B bs ih =>
    intro hnd cur hcur h₁ h₂ hA hB hc
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨A, Bc⟩ := cur
    cases B with
    | inl P =>
      have hd := disjoint_listToggle₁ P bs hnd.1
      have hPsub : ∀ v ∈ P.support,
          v ∈ listToggle₁ (Sum.inl P :: bs : List (G.SideBlock s s')) := fun v hv => by
        rw [listToggle₁_cons_inl, Finset.mem_symmDiff]
        exact Or.inl ⟨hv, fun h => Finset.disjoint_left.1 hd hv h⟩
      have hPA : A ∩ P.support = P.support ∩ s.1 := by
        ext v
        simp only [Finset.mem_inter]
        constructor
        · rintro ⟨hvA, hvP⟩
          exact ⟨hvP, (h₁ v (hPsub v hvP)).1 hvA⟩
        · rintro ⟨hvP, hvs⟩
          exact ⟨(h₁ v (hPsub v hvP)).2 hvs, hvP⟩
      have hS : StepIndep G P.word Bc := by
        have := hc [] (Sum.inl P) bs rfl
        simpa using this
      have hcond : ∀ p ∈ P.word, p.1 ∉ Bc ∧ ∀ v ∈ Bc, (G.Adj p.1 v ↔ G.Adj p.2 v) := by
        intro p hp
        refine ⟨fun hmem => ?_, fun v hv => hS p hp v hv⟩
        exact G.irrefl ((hS p hp _ hmem).2 (OddBlock.adj_of_mem_word hp).symm)
      have hrun1 : G.ClassRun (A, Bc) P.word (symmDiff A P.support, Bc) :=
        OddBlock.classRun_of_cond hs.isIndepSet_fst hs'.isIndepSet_fst hcur hA P hPA hcond
      have hnext : G.IsHoleClasses (symmDiff A P.support, Bc) := hrun1.isHoleClasses hcur
      have hsubP : P.support ⊆ symmDiff s.1 s'.1 := P.support_subset_symmDiff
      obtain ⟨tf, htf⟩ := ih hnd.2 (symmDiff A P.support, Bc) hnext
        (fun v hv => by
          have hvP : v ∉ P.support := fun h => Finset.disjoint_left.1 hd h hv
          have hv' : v ∈ listToggle₁ (Sum.inl P :: bs : List (G.SideBlock s s')) := by
            rw [listToggle₁_cons_inl, Finset.mem_symmDiff]
            exact Or.inr ⟨hv, hvP⟩
          have := h₁ v hv'
          simp only [Finset.mem_symmDiff]
          tauto)
        (fun v hv => h₂ v (by rwa [listToggle₂_cons_inl]))
        (fun v hv => by
          rcases Finset.mem_symmDiff.1 hv with ⟨h1, -⟩ | ⟨h1, -⟩
          · exact hA h1
          · rcases Finset.mem_symmDiff.1 (hsubP h1) with ⟨a, -⟩ | ⟨a, -⟩
            · exact Finset.mem_union_left _ a
            · exact Finset.mem_union_right _ a)
        hB
        (fun pre B' post hdec => by
          have := hc (Sum.inl P :: pre) B' post (by rw [hdec]; rfl)
          cases B' with
          | inl Q' => simpa [listToggle₂_cons_inl] using this
          | inr Q' =>
            simpa [listToggle₁_cons_inl, symmDiff_assoc] using this)
      refine ⟨tf, ?_⟩
      rw [List.flatMap_cons, SideBlock.word_inl]
      exact hrun1.append htf
    | inr Q =>
      have hd := disjoint_listToggle₂ Q bs hnd.1
      have hQsub : ∀ v ∈ Q.support,
          v ∈ listToggle₂ (Sum.inr Q :: bs : List (G.SideBlock s s')) := fun v hv => by
        rw [listToggle₂_cons_inr, Finset.mem_symmDiff]
        exact Or.inl ⟨hv, fun h => Finset.disjoint_left.1 hd hv h⟩
      have hQB : Bc ∩ Q.support = Q.support ∩ s.2 := by
        ext v
        simp only [Finset.mem_inter]
        constructor
        · rintro ⟨hvB, hvQ⟩
          exact ⟨hvQ, (h₂ v (hQsub v hvQ)).1 hvB⟩
        · rintro ⟨hvQ, hvs⟩
          exact ⟨(h₂ v (hQsub v hvQ)).2 hvs, hvQ⟩
      have hS : StepIndep G Q.word A := by
        have := hc [] (Sum.inr Q) bs rfl
        simpa using this
      have hcond : ∀ p ∈ Q.word, p.1 ∉ A ∧ ∀ v ∈ A, (G.Adj p.1 v ↔ G.Adj p.2 v) := by
        intro p hp
        refine ⟨fun hmem => ?_, fun v hv => hS p hp v hv⟩
        exact G.irrefl ((hS p hp _ hmem).2 (OddBlock.adj_of_mem_word hp).symm)
      have hrun1' : G.ClassRun (Bc, A) Q.word (symmDiff Bc Q.support, A) :=
        OddBlock.classRun_of_cond hs.isIndepSet_snd hs'.isIndepSet_snd hcur.swap hB Q hQB hcond
      have hrun1 : G.ClassRun (A, Bc) Q.word (A, symmDiff Bc Q.support) := by
        simpa using hrun1'.swap
      have hnext : G.IsHoleClasses (A, symmDiff Bc Q.support) := hrun1.isHoleClasses hcur
      have hsubQ : Q.support ⊆ symmDiff s.2 s'.2 := Q.support_subset_symmDiff
      obtain ⟨tf, htf⟩ := ih hnd.2 (A, symmDiff Bc Q.support) hnext
        (fun v hv => h₁ v (by rwa [listToggle₁_cons_inr]))
        (fun v hv => by
          have hvQ : v ∉ Q.support := fun h => Finset.disjoint_left.1 hd h hv
          have hv' : v ∈ listToggle₂ (Sum.inr Q :: bs : List (G.SideBlock s s')) := by
            rw [listToggle₂_cons_inr, Finset.mem_symmDiff]
            exact Or.inr ⟨hv, hvQ⟩
          have := h₂ v hv'
          simp only [Finset.mem_symmDiff]
          tauto)
        hA
        (fun v hv => by
          rcases Finset.mem_symmDiff.1 hv with ⟨h1, -⟩ | ⟨h1, -⟩
          · exact hB h1
          · rcases Finset.mem_symmDiff.1 (hsubQ h1) with ⟨a, -⟩ | ⟨a, -⟩
            · exact Finset.mem_union_left _ a
            · exact Finset.mem_union_right _ a)
        (fun pre B' post hdec => by
          have := hc (Sum.inr Q :: pre) B' post (by rw [hdec]; rfl)
          cases B' with
          | inl Q' =>
            simpa [listToggle₂_cons_inr, symmDiff_assoc] using this
          | inr Q' => simpa [listToggle₁_cons_inr] using this)
      refine ⟨tf, ?_⟩
      rw [List.flatMap_cons, SideBlock.word_inr]
      exact hrun1.append htf

/-! ### Mirroring the conditions -/

/-- Mirroring twice gives back the list of blocks. -/
@[simp] theorem mirrorList_mirrorList (bs : List (G.SideBlock s s')) :
    mirrorList (mirrorList bs) = bs := by
  simp [mirrorList, List.map_reverse, List.map_map, Function.comp_def]

theorem mirrorList_append (a b : List (G.SideBlock s s')) :
    mirrorList (a ++ b) = mirrorList b ++ mirrorList a := by
  simp [mirrorList]

/-- The forward conditions of the mirror list are the backward conditions of the list: if
`mirrorList bs = pre'' ++ B'' :: post''`, then
`bs = mirrorList post'' ++ B''.reverse :: mirrorList pre''`, and reading the steps of `B''.reverse`
backwards gives those of `B''`. -/
theorem stepIndep_of_stepConds_mirror {bs : List (G.SideBlock s s')}
    (hnd : (bs.map SideBlock.support).Nodup) (h : StepConds G s s' bs) :
    ∀ (pre'' : List (G.SideBlock s' s)) (B'' : G.SideBlock s' s) (post'' : List (G.SideBlock s' s)),
      mirrorList bs = pre'' ++ B'' :: post'' → StepIndep G B''.word (other s' B'' pre'') := by
  intro pre'' B'' post'' hdec
  have hnd'' : ((pre'' ++ B'' :: post'').map SideBlock.support).Nodup := by
    rw [← hdec]
    exact nodup_mirrorList hnd
  obtain ⟨hnpre, -, -, -⟩ := FPDeformation.nodup_split hnd''
  have hbs : bs = mirrorList post'' ++ B''.reverse :: mirrorList pre'' := by
    have := congrArg mirrorList hdec
    rw [mirrorList_mirrorList, mirrorList_append, mirrorList_cons] at this
    rw [this]
    simp
  have key := (h _ _ _ hbs).2
  rw [← stepIndep_reverseWord_iff, ← word_reverse]
  cases B'' with
  | inl P =>
    simp only [reverse_inl, other_inl] at key ⊢
    rw [listToggle₂_mirrorList hnpre] at key
    exact key
  | inr P =>
    simp only [reverse_inr, other_inr] at key ⊢
    rw [listToggle₁_mirrorList hnpre] at key
    exact key

end SideBlock

namespace FPDeformation

variable [DecidableEq V] {s s' : Finset V × Finset V}

/-- **Palindromic deformations satisfy the step conditions.**  This is the bookkeeping
`Palindromic.stepConds_inl` / `stepConds_inr` of `FreeFermionGraphs.T3Interaction` in the form
`SideBlock.StepConds`. -/
theorem Palindromic.stepConds (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s')
    {D : G.FPDeformation s s'} (hD : D.Palindromic) : SideBlock.StepConds G s s' D.blocks := by
  intro pre B post hdec
  cases B with
  | inl P =>
    obtain ⟨hF, hR⟩ := Palindromic.stepConds_inl hs hs' hD hdec
    refine ⟨fun p hp v hv => (hF p hp).2 v hv, fun p hp v hv => ((hR p hp).2 v hv).symm⟩
  | inr Q =>
    obtain ⟨hF, hR⟩ := Palindromic.stepConds_inr hs hs' hD hdec
    refine ⟨fun p hp v hv => (hF p hp).2 v hv, fun p hp v hv => ((hR p hp).2 v hv).symm⟩

/-- **The step conditions imply palindromicity.**  A deformation of hole-class states whose blocks
satisfy the step conditions (`SideBlock.StepConds`) is palindromic: the forward run is built block
by block (`SideBlock.exists_classRun_of_stepIndep`), and the backward run is the forward run of the
mirror deformation, whose forward conditions are the backward conditions of `D`. -/
theorem Palindromic.of_stepConds (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s')
    (D : G.FPDeformation s s') (h : SideBlock.StepConds G s s' D.blocks) : D.Palindromic := by
  refine ⟨?_, ?_⟩
  · obtain ⟨tf, htf⟩ := SideBlock.exists_classRun_of_stepIndep hs hs' D.blocks D.nodup s hs
      (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) Finset.subset_union_left Finset.subset_union_left
      (fun pre B post hdec => (h pre B post hdec).1)
    exact ⟨tf, htf⟩
  · obtain ⟨tf, htf⟩ := SideBlock.exists_classRun_of_stepIndep hs' hs
      (SideBlock.mirrorList D.blocks) (SideBlock.nodup_mirrorList D.nodup) s' hs'
      (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) Finset.subset_union_left Finset.subset_union_left
      (SideBlock.stepIndep_of_stepConds_mirror D.nodup h)
    refine ⟨tf, ?_⟩
    rw [FPDeformation.word, ← SideBlock.flatMap_word_mirrorList]
    exact htf

/-- **The criterion.**  A fixed-pairing-type deformation of hole-class states is palindromic if and
only if its blocks satisfy the step conditions of the block step lemma at the time they run, in the
forward run out of `s` and in the backward run out of `s'`. -/
theorem palindromic_iff_stepConds (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s')
    (D : G.FPDeformation s s') : D.Palindromic ↔ SideBlock.StepConds G s s' D.blocks :=
  ⟨fun hD => Palindromic.stepConds hs hs' hD, Palindromic.of_stepConds hs hs' D⟩

end FPDeformation

end SimpleGraph
