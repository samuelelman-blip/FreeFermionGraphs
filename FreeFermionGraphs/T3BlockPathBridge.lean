import FreeFermionGraphs.T3BlockStep
import FreeFermionGraphs.TheoremOneII

/-!
# Bridge: an untethered deformation path is a forward-running odd block

This module connects the deformation-along-a-set machinery of Theorem 1(ii)
(`EvenHoleLabeling.SetDeformationPath`, arXiv 2305.15625 v1 L753-766 and the proof L904-927) to the
block formalism of the Theorem 1(iii) route (`OddBlock`, `OddBlock.RunsFrom`; v1 Definition 19
`definition:fixedpairingtypedeformation`, L978-994, base case (i) of the proof, L1808-1811).

Let `L` be a full-cyclic labelling of an even hole with colour classes `s.1 = {a_i}` and
`s.2 = {b_i}`, let `s'.1 = S` be an independent set (the colour class of another hole), and let
`P = (s_j, i_j)_{j<ℓ}` be a deformation path of `L` along `S` which is *untethered*, i.e. whose
support `{s_j} ∪ {a_{i_j}}` is a whole component of `G[S ⊕ C_a]` (v1 L764).  Then the induced path

  `s_0 - a_{i_0} - s_1 - a_{i_1} - ⋯ - s_{ℓ-1} - a_{i_{ℓ-1}}`

(`2ℓ - 1` edges, v1 L764) is an `OddBlock s.1 s'.1`: its even positions `s_j` lie in `S ∖ C_a`, its
odd positions `a_{i_j}` lie in `C_a ∖ S`, and its vertex set is a component of
`G[C_a ⊕ S]`.  Its word is the list `[(s_j, a_{i_j})]` of (introduced, removed) pairs, and this word
is a clone run (`ClassRun`) out of the hole-class state `s`: the clone conditions on the `a`-class
are automatic (block step lemma `OddBlock.classRun_iff`), and the conditions on the `b`-class say
that `s_j` and `a_{i_j}` have the same neighbours in `C_b` and `s_j ∉ C_b`, which are facts of a
deformation path (`adj_s_iff_adj_a_of_mem_range_b`, `cloneSet_disjoint_image_b`).

## Main definitions and results

* `EvenHoleLabeling.SetDeformationPath.blockPath`: the induced path
  `s_0, a_{i_0}, s_1, a_{i_1}, …` as an `IndexedInducedPath` (for a claw-free graph and an
  independent `S`; the proof of the adjacency condition is `adj_s_a_iff`).
* `OddBlock.ofUntethered`: the `OddBlock s.1 s'.1` built from an untethered path;
  `ofUntethered_support`, `ofUntethered_first`, `ofUntethered_word` describe its data.
* `OddBlock.ofUntethered_runsFrom`: its word runs from the hole-class state `s`.
* `OddBlock.exists_of_untethered`: the bridge theorem of work package T3-18.

Hypotheses: claw-freeness is used (only) for the adjacency pattern `adj_s_a_iff` of the path.  The
full-cyclic hypothesis `hL` of the bridge theorem is not needed beyond the hole-class hypothesis
`hs`, which is its consequence; it is kept in the statement as recorded in the work package.
-/

open scoped symmDiff

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace EvenHoleLabeling

namespace SetDeformationPath

section BlockPath

variable {S : Finset V} {k : ℕ} {L : G.EvenHoleLabeling k}

/-- The vertex at position `m` of the path `s_0, a_{i_0}, s_1, a_{i_1}, …`: `s_{m/2}` for even `m`
and `a_{i_{m/2}}` for odd `m` (a junk value, `s_0`, outside the range `m < 2ℓ`). -/
def blockVtx (P : L.SetDeformationPath S) (m : ℕ) : V :=
  if h : m / 2 < P.len then
    (if m % 2 = 0 then P.s ⟨m / 2, h⟩ else L.a (P.idx ⟨m / 2, h⟩))
  else P.s P.first

@[simp]
theorem blockVtx_even (P : L.SetDeformationPath S) (j : Fin P.len) :
    P.blockVtx (2 * j.val) = P.s j := by
  have h1 : 2 * j.val / 2 < P.len := by have := j.isLt; omega
  have h2 : 2 * j.val % 2 = 0 := by omega
  rw [blockVtx, dif_pos h1, if_pos h2]
  exact congrArg P.s (Fin.ext (show 2 * j.val / 2 = j.val by omega))

@[simp]
theorem blockVtx_odd (P : L.SetDeformationPath S) (j : Fin P.len) :
    P.blockVtx (2 * j.val + 1) = L.a (P.idx j) := by
  have h1 : (2 * j.val + 1) / 2 < P.len := by have := j.isLt; omega
  have h2 : ¬(2 * j.val + 1) % 2 = 0 := by omega
  rw [blockVtx, dif_pos h1, if_neg h2]
  exact congrArg (fun i => L.a (P.idx i)) (Fin.ext (show (2 * j.val + 1) / 2 = j.val by omega))

/-- Every position `m < 2ℓ` is `2 j` or `2 j + 1` for some `j < ℓ`. -/
theorem blockVtx_cases (P : L.SetDeformationPath S) {m : ℕ} (hm : m < 2 * P.len) :
    ∃ j : Fin P.len, (m = 2 * j.val ∧ P.blockVtx m = P.s j) ∨
      (m = 2 * j.val + 1 ∧ P.blockVtx m = L.a (P.idx j)) := by
  rcases Nat.even_or_odd' m with ⟨c, rfl | rfl⟩
  · exact ⟨⟨c, by omega⟩, Or.inl ⟨rfl, blockVtx_even P ⟨c, by omega⟩⟩⟩
  · exact ⟨⟨c, by omega⟩, Or.inr ⟨rfl, blockVtx_odd P ⟨c, by omega⟩⟩⟩

/-- The positions of the path `s_0, a_{i_0}, s_1, …` are adjacent exactly when they are
consecutive: this is the adjacency pattern `adj_s_a_iff` of a deformation path together with the
independence of `S` and of the `a`-class (v1 L764). -/
theorem blockVtx_adj_iff (hclaw : G.IsClawFree) (hS : G.IsIndepSet (S : Set V))
    (P : L.SetDeformationPath S) {m m' : ℕ} (hm : m < 2 * P.len) (hm' : m' < 2 * P.len) :
    G.Adj (P.blockVtx m) (P.blockVtx m') ↔ m + 1 = m' ∨ m' + 1 = m := by
  obtain ⟨c, hc⟩ := P.blockVtx_cases hm
  obtain ⟨d, hd⟩ := P.blockVtx_cases hm'
  have hss : ∀ c d : Fin P.len, ¬G.Adj (P.s c) (P.s d) := fun c d hadj =>
    hS (Finset.mem_coe.2 (P.s_mem c)) (Finset.mem_coe.2 (P.s_mem d)) hadj.ne hadj
  rcases hc with ⟨rfl, hc⟩ | ⟨rfl, hc⟩ <;> rcases hd with ⟨rfl, hd⟩ | ⟨rfl, hd⟩ <;>
    rw [hc, hd]
  · exact iff_of_false (hss c d) (by omega)
  · rw [P.adj_s_a_iff hclaw hS c d]
    omega
  · rw [G.adj_comm, P.adj_s_a_iff hclaw hS d c]
    omega
  · exact iff_of_false (L.adj_aa _ _) (by omega)

variable [DecidableEq V]

/-- The vertices of `s_0, a_{i_0}, s_1, …` at distinct positions are distinct. -/
theorem blockVtx_injective (hS : G.IsIndepSet (S : Set V)) (P : L.SetDeformationPath S)
    {m m' : ℕ} (hm : m < 2 * P.len) (hm' : m' < 2 * P.len)
    (h : P.blockVtx m = P.blockVtx m') : m = m' := by
  obtain ⟨c, hc⟩ := P.blockVtx_cases hm
  obtain ⟨d, hd⟩ := P.blockVtx_cases hm'
  have hsa : ∀ c d : Fin P.len, P.s c ≠ L.a (P.idx d) := fun c d e =>
    P.s_not_mem_image_a hS c (Finset.mem_image.2 ⟨P.idx d, Finset.mem_univ _, e.symm⟩)
  rcases hc with ⟨rfl, hc⟩ | ⟨rfl, hc⟩ <;> rcases hd with ⟨rfl, hd⟩ | ⟨rfl, hd⟩ <;>
    rw [hc, hd] at h
  · have := congrArg Fin.val (P.s_injective h)
    omega
  · exact (hsa c d h).elim
  · exact (hsa d c h.symm).elim
  · have := congrArg Fin.val (P.idx_injective (L.a_injective h))
    omega

/-- The deformation path `s_0 - a_{i_0} - s_1 - a_{i_1} - ⋯ - s_{ℓ-1} - a_{i_{ℓ-1}}` of v1 L764 as
an induced path with its linear vertex order (`2ℓ` vertices, `2ℓ - 1` edges). -/
def blockPath (hclaw : G.IsClawFree) (hS : G.IsIndepSet (S : Set V))
    (P : L.SetDeformationPath S) : G.IndexedInducedPath where
  card := 2 * P.len
  nonempty := by have := P.len_pos; omega
  vertex := fun m => P.blockVtx m.val
  injective := fun m m' h => Fin.ext (P.blockVtx_injective hS m.isLt m'.isLt h)
  adj_iff := fun m m' => P.blockVtx_adj_iff hclaw hS m.isLt m'.isLt

@[simp]
theorem blockPath_card (hclaw : G.IsClawFree) (hS : G.IsIndepSet (S : Set V))
    (P : L.SetDeformationPath S) : (P.blockPath hclaw hS).card = 2 * P.len := rfl

@[simp]
theorem blockPath_vertex (hclaw : G.IsClawFree) (hS : G.IsIndepSet (S : Set V))
    (P : L.SetDeformationPath S) (m : Fin (P.blockPath hclaw hS).card) :
    (P.blockPath hclaw hS).vertex m = P.blockVtx m.val := rfl

/-- The vertex set of the path `s_0, a_{i_0}, …` is the support of the deformation path. -/
theorem range_blockPath (hclaw : G.IsClawFree) (hS : G.IsIndepSet (S : Set V))
    (P : L.SetDeformationPath S) :
    Set.range (P.blockPath hclaw hS).vertex = ↑P.support := by
  ext v
  rw [Finset.mem_coe, mem_support_iff]
  constructor
  · rintro ⟨m, rfl⟩
    obtain ⟨j, ⟨-, hj⟩ | ⟨-, hj⟩⟩ := P.blockVtx_cases m.isLt
    · exact ⟨j, Or.inl hj.symm⟩
    · exact ⟨j, Or.inr hj.symm⟩
  · rintro ⟨j, rfl | rfl⟩
    · exact ⟨⟨2 * j.val, by have := j.isLt; simp only [blockPath_card]; omega⟩,
        blockVtx_even P j⟩
    · exact ⟨⟨2 * j.val + 1, by have := j.isLt; simp only [blockPath_card]; omega⟩,
        blockVtx_odd P j⟩

end BlockPath

end SetDeformationPath

end EvenHoleLabeling

/-! ### The odd block of an untethered path -/

namespace OddBlock

variable [DecidableEq V]

/-- **The odd block of an untethered deformation path** (v1 L756-766, L764: "if `s₀` is
untethered … the path `P` has odd length `2ℓ - 1`", read as a component of `G[C_a ⊕ S]`).

Let `L` be a labelling with `{a_i} = s.1`, let `S = s'.1` be an independent set (a colour class of
another hole), and let `P = (s_j, i_j)` be an untethered deformation path of `L` along `S`.  Then the
induced path `s_0, a_{i_0}, s_1, a_{i_1}, …` is an `OddBlock s.1 s'.1`: the introduced vertices
`s_j` lie in `S ∖ C_a`, the removed vertices `a_{i_j}` lie in `C_a ∖ S`, and the vertex set is a
component of `G[C_a ⊕ S]` (it is the component `G[S ⊕ C_a]` of `Untethered`, with the symmetric
difference taken in the other order). -/
def ofUntethered (hclaw : G.IsClawFree) {s s' : Finset V × Finset V}
    (hs' : G.IsHoleClasses s') {n : ℕ} {L : G.EvenHoleLabeling n}
    (ha : Finset.univ.image L.a = s.1) (P : L.SetDeformationPath s'.1) (hP : P.Untethered) :
    G.OddBlock s.1 s'.1 where
  path := P.blockPath hclaw hs'.isIndepSet_fst
  even_card := even_two_mul P.len
  mem_Y := fun m hm => by
    obtain ⟨j, ⟨hj, hv⟩ | ⟨hj, hv⟩⟩ := P.blockVtx_cases m.isLt
    · refine Finset.mem_sdiff.2 ⟨?_, ?_⟩
      · rw [EvenHoleLabeling.SetDeformationPath.blockPath_vertex, hv]
        exact P.s_mem j
      · rw [EvenHoleLabeling.SetDeformationPath.blockPath_vertex, hv, ← ha]
        exact P.s_not_mem_image_a hs'.isIndepSet_fst j
    · exfalso
      have : Even (2 * j.val + 1) := hj ▸ hm
      exact (Nat.not_even_iff_odd.2 ⟨j.val, rfl⟩) this
  mem_X := fun m hm => by
    obtain ⟨j, ⟨hj, hv⟩ | ⟨hj, hv⟩⟩ := P.blockVtx_cases m.isLt
    · exfalso
      have : Odd (2 * j.val) := hj ▸ hm
      exact (Nat.not_odd_iff_even.2 ⟨j.val, two_mul _⟩) this
    · refine Finset.mem_sdiff.2 ⟨?_, ?_⟩
      · rw [EvenHoleLabeling.SetDeformationPath.blockPath_vertex, hv, ← ha]
        exact Finset.mem_image.2 ⟨P.idx j, Finset.mem_univ _, rfl⟩
      · rw [EvenHoleLabeling.SetDeformationPath.blockPath_vertex, hv]
        exact P.a_idx_not_mem hs'.isIndepSet_fst j
  component := by
    rw [P.range_blockPath hclaw hs'.isIndepSet_fst, symmDiff_comm, ← ha]
    exact hP

section Data

variable {hclaw : G.IsClawFree} {s s' : Finset V × Finset V} {hs' : G.IsHoleClasses s'}
  {n : ℕ} {L : G.EvenHoleLabeling n} {ha : Finset.univ.image L.a = s.1}
  {P : L.SetDeformationPath s'.1} {hP : P.Untethered}

/-- The support of the block of an untethered path is the support of the path. -/
theorem ofUntethered_support :
    (ofUntethered hclaw hs' ha P hP).support = P.support := by
  apply Finset.coe_injective
  rw [coe_support]
  exact P.range_blockPath hclaw hs'.isIndepSet_fst

/-- The first vertex of the block of an untethered path is `s_0`. -/
theorem ofUntethered_first :
    (ofUntethered hclaw hs' ha P hP).first = P.s P.first := by
  have h : P.blockVtx (2 * P.first.val) = P.s P.first :=
    EvenHoleLabeling.SetDeformationPath.blockVtx_even P P.first
  exact h

/-- The word of the block of an untethered path is `[(s_0, a_{i_0}), …, (s_{ℓ-1}, a_{i_{ℓ-1}})]`,
the (introduced, removed) pairs of the deformation path. -/
theorem ofUntethered_word :
    (ofUntethered hclaw hs' ha P hP).word = List.ofFn fun j => (P.s j, L.a (P.idx j)) := by
  apply List.ext_getElem
  · simp [length_word, ofUntethered]
  · intro i h1 h2
    have hi : i < P.len := by
      simpa [length_word, ofUntethered] using h1
    rw [getElem_word _ i h1, List.getElem_ofFn]
    refine Prod.ext ?_ ?_
    · exact EvenHoleLabeling.SetDeformationPath.blockVtx_even P ⟨i, hi⟩
    · exact EvenHoleLabeling.SetDeformationPath.blockVtx_odd P ⟨i, hi⟩

end Data

/-- **The word of the block of an untethered path runs from the hole-class state of its
labelling.**  Let `s = (C_a, C_b)` be the colour classes of `L` and `S = s'.1` an independent set.
The block step lemma `classRun_iff` reduces the run to the second-class conditions of each step
`(s_j, a_{i_j})`: `s_j ∉ C_b` and `s_j`, `a_{i_j}` have the same neighbours in `C_b`.  Both are
facts of a deformation path (`cloneSet_disjoint_image_b`, `adj_s_iff_adj_a_of_mem_range_b`). -/
theorem ofUntethered_runsFrom (hclaw : G.IsClawFree) {s s' : Finset V × Finset V}
    (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s') {n : ℕ} {L : G.EvenHoleLabeling n}
    (ha : Finset.univ.image L.a = s.1) (hb : Finset.univ.image L.b = s.2)
    (P : L.SetDeformationPath s'.1) (hP : P.Untethered) :
    (ofUntethered hclaw hs' ha P hP).RunsFrom s := by
  obtain ⟨A, B⟩ := s
  have hS := hs'.isIndepSet_fst
  have hX := hs.isIndepSet_fst
  change (ofUntethered hclaw hs' ha P hP).RunsFrom (A, B)
  have hA : A ∩ (ofUntethered hclaw hs' ha P hP).support =
      (ofUntethered hclaw hs' ha P hP).support ∩ A := Finset.inter_comm _ _
  rw [classRun_iff hX hS hs Finset.subset_union_left _ hA]
  intro p hp
  rw [ofUntethered_word, List.mem_ofFn] at hp
  obtain ⟨j, rfl⟩ := hp
  simp only at ha hb
  refine ⟨?_, ?_⟩
  · intro hjB
    rw [← hb] at hjB
    exact Finset.disjoint_left.1 (P.cloneSet_disjoint_image_b hS) (P.mem_cloneSet.2 ⟨j, rfl⟩) hjB
  · intro v hv
    rw [← hb] at hv
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hv
    exact P.adj_s_iff_adj_a_b j q

/-- **Bridge from Theorem 1(ii) to the block formalism** (work package T3-18; v1 L756-766, base
case (i) L1808-1811).

Let `L` be a full-cyclic labelling with colour classes `s.1 = {a_i}` and `s.2 = {b_i}`, let
`s'` be a hole-class state, and let `P` be an *untethered* deformation path of `L` along the
independent set `s'.1` (its support is a component of `G[s'.1 ⊕ s.1]`).  Then there is an
`OddBlock s.1 s'.1` with the support of `P`, whose first vertex is `s_0`, and whose word runs from
the hole-class state `s`.  (The block is `s_0, a_{i_0}, s_1, a_{i_1}, …`; its word is
`[(s_j, a_{i_j})]`, see `ofUntethered_word`.)

The hypothesis `hL` is implied by the hole-class hypothesis `hs` and is not used. -/
theorem exists_of_untethered (hclaw : G.IsClawFree) {s s' : Finset V × Finset V}
    (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s') {n : ℕ} {L : G.EvenHoleLabeling n}
    (_hL : L.HasFullCyclicOrder) (ha : Finset.univ.image L.a = s.1)
    (hb : Finset.univ.image L.b = s.2) (P : L.SetDeformationPath s'.1) (hP : P.Untethered) :
    ∃ Q : G.OddBlock s.1 s'.1, Q.support = P.support ∧ Q.first = P.s P.first ∧ Q.RunsFrom s :=
  ⟨ofUntethered hclaw hs' ha P hP, ofUntethered_support, ofUntethered_first,
    ofUntethered_runsFrom hclaw hs hs' ha hb P hP⟩

end OddBlock

end SimpleGraph
