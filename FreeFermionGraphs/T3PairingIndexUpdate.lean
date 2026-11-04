import FreeFermionGraphs.T3PairingIndexCount
import FreeFermionGraphs.T3BlockStep

/-!
# The pairing index after toggling a forward-running block

This module computes how the pairing index `Ψ` of `FreeFermionGraphs.T3PairingIndex` changes when
the source state is moved along one block of the side-1 graph (package T3-21).  It is the
bookkeeping behind the rerouting step of the obstruction search in the synthesised proof of
Theorem 1(iii) of the manuscript (arXiv 2305.15625 v1, label `theorem:conservedcharges`; the
search process and its rerouting are described at L1158-1191, and the source set of the
obstruction graph is v1 Definition 21, `definition:obstructiongraphcoloringclasses`, L1017).

Let `s = (A, B)` and `s' = (A', B')` be hole-class states and let `Q` be an oriented odd block of
`G[A ⊕ A']` (`OddBlock A A'`; v1 Definition 19, `definition:fixedpairingtypedeformation`,
L978-994) which *runs from* `s` (its word is a clone run out of `s`; the local criterion is the
forward block step lemma `OddBlock.classRun_iff`).  Such a run ends in the hole-class state
`(A ⊕ supp Q, B)` (`OddBlock.classRun_end`).

## Main results

* `SimpleGraph.matchedW_toggle_fst`, `SimpleGraph.crossedW_toggle_fst`: toggling a set `Q`
  contained in `s.1 ⊕ s'.1` in the first class of the *first* argument `s` of `matchedW` /
  `crossedW` (the argument that is read through the carrier of `s'`) removes exactly `Q`:
  `matchedW s' (s.1 ⊕ Q, s.2) = matchedW s' s ∖ Q`, and likewise for `crossedW`.  Only the
  disjointness of the two classes of `s` is used.  The new vertices of the toggled state lie in
  `s'.1` and so are never counted, the removed vertices disappear, and every other vertex keeps
  its class and its clone in the carrier of `s'`.
* `SimpleGraph.OddBlock.pairingIndex_fwdState` (the statement of the package): for a claw-free
  graph, hole-class states `s`, `s'` and a block `Q : OddBlock s.1 s'.1` which runs from `s`,
  `Ψ((s.1 ⊕ Q, s.2), s') = Ψ(s, s') + |Q ∩ matchedW s' s| - |Q ∩ crossedW s' s|`.
  In particular the pairing index is unchanged by a block which meets `matchedW s' s` and
  `crossedW s' s` in the same number of vertices, e.g. by one which meets neither
  (`OddBlock.pairingIndex_fwdState_of_card_eq`).

## Relation to v1

v1 has no counterpart of `Ψ`; the statement computes the effect of the rerouting on the count
`|crossed W| - |matched W|` of `FreeFermionGraphs.T3PairingIndexCount`
(`pairingIndex_eq_card_sub_card`).  The count formula is applied with the roles of the two states
exchanged, `Ψ(t, s') = Ψ(s', t)` (`pairingIndex_comm`), so the relevant sets are `matchedW s' s`
and `crossedW s' s`: the vertices of the first hole `C = s.1 ∪ s.2` anticommuting with `h_{C'}`
(v1 Definition 20, L996-1013, with the roles of `C` and `C'` exchanged), split by pairing type.
Claw-freeness enters only through the count formula; the identities for `matchedW` and
`crossedW` themselves are purely set-theoretic.
-/

open scoped symmDiff

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

section Toggle

variable [DecidableEq V] {s s' : Finset V × Finset V}

/-- Toggling a set `Q ⊆ s.1 ⊕ s'.1` in the first class of the first argument removes exactly
`Q` from the matched set: `matchedW s' (s.1 ⊕ Q, s.2) = matchedW s' s ∖ Q`.  The vertices of
`Q ∖ s.1` lie in `s'.1`, hence in the carrier of `s'`, where they are never counted, the vertices
of `Q ∩ s.1` are removed, and `Q` is disjoint from `s.2` outside the carrier of `s'` because
`s.2` is disjoint from `s.1`. -/
theorem matchedW_toggle_fst (hd : Disjoint s.1 s.2) {Q : Finset V} (hQ : Q ⊆ symmDiff s.1 s'.1) :
    G.matchedW s' (symmDiff s.1 Q, s.2) = G.matchedW s' s \ Q := by
  ext w
  rw [Finset.mem_sdiff, mem_matchedW, mem_matchedW]
  by_cases hC : w ∈ s'.1 ∪ s'.2
  · simp [hC]
  · have hQ1 : w ∈ Q → w ∈ s.1 := by
      intro hw
      rcases Finset.mem_symmDiff.1 (hQ hw) with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd (Finset.mem_union_left _ h) hC
    have hQ2 : w ∈ s.2 → w ∉ Q := fun h2 hw =>
      Finset.disjoint_left.1 hd (hQ1 hw) h2
    have hsd : w ∈ symmDiff s.1 Q ↔ w ∈ s.1 ∧ w ∉ Q := by
      rw [Finset.mem_symmDiff]
      constructor
      · rintro (⟨h, h'⟩ | ⟨h, h'⟩)
        · exact ⟨h, h'⟩
        · exact absurd (hQ1 h) h'
      · rintro ⟨h, h'⟩
        exact Or.inl ⟨h, h'⟩
    simp only [hC, hsd, not_false_eq_true, true_and]
    constructor
    · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨h1, h3⟩)
      · exact ⟨Or.inl ⟨h1, h3⟩, h2⟩
      · exact ⟨Or.inr ⟨h1, h3⟩, hQ2 h1⟩
    · rintro ⟨⟨h1, h3⟩ | ⟨h1, h3⟩, h2⟩
      · exact Or.inl ⟨⟨h1, h2⟩, h3⟩
      · exact Or.inr ⟨h1, h3⟩

/-- Toggling a set `Q ⊆ s.1 ⊕ s'.1` in the first class of the first argument removes exactly
`Q` from the crossed set: `crossedW s' (s.1 ⊕ Q, s.2) = crossedW s' s ∖ Q`.  See
`matchedW_toggle_fst`. -/
theorem crossedW_toggle_fst (hd : Disjoint s.1 s.2) {Q : Finset V} (hQ : Q ⊆ symmDiff s.1 s'.1) :
    G.crossedW s' (symmDiff s.1 Q, s.2) = G.crossedW s' s \ Q := by
  ext w
  rw [Finset.mem_sdiff, mem_crossedW, mem_crossedW]
  by_cases hC : w ∈ s'.1 ∪ s'.2
  · simp [hC]
  · have hQ1 : w ∈ Q → w ∈ s.1 := by
      intro hw
      rcases Finset.mem_symmDiff.1 (hQ hw) with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd (Finset.mem_union_left _ h) hC
    have hQ2 : w ∈ s.2 → w ∉ Q := fun h2 hw =>
      Finset.disjoint_left.1 hd (hQ1 hw) h2
    have hsd : w ∈ symmDiff s.1 Q ↔ w ∈ s.1 ∧ w ∉ Q := by
      rw [Finset.mem_symmDiff]
      constructor
      · rintro (⟨h, h'⟩ | ⟨h, h'⟩)
        · exact ⟨h, h'⟩
        · exact absurd (hQ1 h) h'
      · rintro ⟨h, h'⟩
        exact Or.inl ⟨h, h'⟩
    simp only [hC, hsd, not_false_eq_true, true_and]
    constructor
    · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨h1, h3⟩)
      · exact ⟨Or.inl ⟨h1, h3⟩, h2⟩
      · exact ⟨Or.inr ⟨h1, h3⟩, hQ2 h1⟩
    · rintro ⟨⟨h1, h3⟩ | ⟨h1, h3⟩, h2⟩
      · exact Or.inl ⟨⟨h1, h2⟩, h3⟩
      · exact Or.inr ⟨h1, h3⟩

end Toggle

namespace OddBlock

variable [DecidableEq V] {s s' : Finset V × Finset V}

/-- **The pairing index after toggling a forward-running block** (package T3-21; v1 rerouting
L1158-1191, blocks of Definition 19, L978-994).  Let `G` be claw-free, `s`, `s'` hole-class
states and `Q` a block of `G[s.1 ⊕ s'.1]` which runs from `s`.  Then the state
`(s.1 ⊕ supp Q, s.2)` reached by the run satisfies
`Ψ((s.1 ⊕ supp Q, s.2), s') = Ψ(s, s') + |supp Q ∩ matchedW s' s| - |supp Q ∩ crossedW s' s|`.

Proof: the end state `t = (s.1 ⊕ supp Q, s.2)` of the run is a hole-class state
(`OddBlock.classRun_end`, `ClassRun.isHoleClasses`).  By the symmetry of `Ψ` and the count formula
(`pairingIndex_eq_card_sub_card`, applied to `(s', t)` and `(s', s)`),
`Ψ(t, s') = |crossedW s' t| - |matchedW s' t|` and `Ψ(s, s') = |crossedW s' s| - |matchedW s' s|`,
and `matchedW s' t = matchedW s' s ∖ supp Q`, `crossedW s' t = crossedW s' s ∖ supp Q`
(`matchedW_toggle_fst`, `crossedW_toggle_fst`). -/
theorem pairingIndex_fwdState [Fintype V] (hclaw : G.IsClawFree) (hs : G.IsHoleClasses s)
    (hs' : G.IsHoleClasses s') (Q : G.OddBlock s.1 s'.1) (hQ : Q.RunsFrom s) :
    G.pairingIndex (symmDiff s.1 Q.support, s.2) s' =
      G.pairingIndex s s' + (Q.support ∩ G.matchedW s' s).card -
        (Q.support ∩ G.crossedW s' s).card := by
  obtain ⟨t', hrun⟩ := hQ
  have hend : t' = (symmDiff s.1 Q.support, s.2) :=
    classRun_end hs.isIndepSet_fst hs'.isIndepSet_fst hs Finset.subset_union_left Q
      (Finset.inter_comm _ _) hrun
  have ht : G.IsHoleClasses (symmDiff s.1 Q.support, s.2) := by
    rw [← hend]
    exact hrun.isHoleClasses hs
  have hsub : Q.support ⊆ symmDiff s.1 s'.1 := Q.support_subset_symmDiff
  rw [pairingIndex_comm, pairingIndex_eq_card_sub_card hclaw hs' ht,
    matchedW_toggle_fst hs.disjoint hsub, crossedW_toggle_fst hs.disjoint hsub,
    pairingIndex_comm (s := s) (s' := s'), pairingIndex_eq_card_sub_card hclaw hs' hs]
  have hm := Finset.card_sdiff_add_card_inter (G.matchedW s' s) Q.support
  have hc := Finset.card_sdiff_add_card_inter (G.crossedW s' s) Q.support
  rw [Finset.inter_comm (G.matchedW s' s)] at hm
  rw [Finset.inter_comm (G.crossedW s' s)] at hc
  omega

/-- A forward-running block which meets the matched and the crossed set of `(s', s)` in the same
number of vertices leaves the pairing index unchanged (this holds in particular if it meets
neither). -/
theorem pairingIndex_fwdState_of_card_eq [Fintype V] (hclaw : G.IsClawFree)
    (hs : G.IsHoleClasses s) (hs' : G.IsHoleClasses s') (Q : G.OddBlock s.1 s'.1)
    (hQ : Q.RunsFrom s)
    (hcard : (Q.support ∩ G.matchedW s' s).card = (Q.support ∩ G.crossedW s' s).card) :
    G.pairingIndex (symmDiff s.1 Q.support, s.2) s' = G.pairingIndex s s' := by
  rw [pairingIndex_fwdState hclaw hs hs' Q hQ, hcard]
  ring

end OddBlock

end SimpleGraph
