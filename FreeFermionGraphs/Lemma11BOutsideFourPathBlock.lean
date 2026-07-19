import FreeFermionGraphs.Lemma11BOutsidePredecessorAdjacency

/-!
# Lemma 11(b): the four-neighbor active-path block

The outside-path branch already forces the vertex removed at the preceding
step to neighbor the dependent vertex. If the preceding introduced vertex
is also a neighbor, the dependent vertex has three consecutive active-path
neighbors.

Commutation rules out the two-neighbor case, so Lemma 7 forces four path
neighbors. Claw-freeness then makes the fourth neighbor adjacent to the
three-vertex block. The current removed vertex is a prescribed nonneighbor,
so the fourth path index must extend the block on its left. This is the
paper's configuration
k_(s-3)-j_(s-2)-k_(s-2)-j_(s-1).
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- If an outside commuting dependent vertex also neighbors the preceding
introduced vertex, it has four path neighbors and a fourth neighbor directly
to the left of that preceding introduced vertex. -/
theorem four_path_neighbor_block_of_adj_previous_introduced
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    (horder : Definition19PathOrder M)
    (hopposite : D.BaseOppositeEndpointNonadjacency)
    {s t : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huOutside : u ∉ Set.range D.path.vertex)
    (hnotAnti : ¬D.path.AnticommutesWith u)
    (ht : t < D.deformation.stepCount)
    (hts : Nat.succ t = s)
    (huPreviousIntroduced :
      G.Adj u (D.deformation.step ⟨t, ht⟩).introduced) :
    1 < s ∧
      ∃ x : Fin D.path.card,
        x.val + 1 =
          (L.introducedPathIndex ⟨t, ht⟩).val ∧
        G.Adj u (D.path.vertex x) ∧
        (D.path.neighborIndexSet u).ncard = 4 := by
  have hs : s < D.deformation.stepCount :=
    D.index_lt_of_mem_dependentAt hu
  let previous : Fin D.deformation.stepCount := ⟨t, ht⟩
  let current : Fin D.deformation.stepCount := ⟨s, hs⟩
  let a : Fin D.path.card := L.introducedPathIndex previous
  let b : Fin D.path.card := L.removedPathIndex previous
  let c : Fin D.path.card := L.introducedPathIndex current
  have haval : a.val = 2 * t := by
    simpa [a, previous] using
      L.introduced_index_val previous
  have hbval : b.val = 2 * t + 1 := by
    simpa [b, previous] using
      L.removed_index_val previous
  have hcval : c.val = 2 * s := by
    simpa [c, current] using
      L.introduced_index_val current
  have hab : a ≠ b := by
    intro h
    have hval := congrArg Fin.val h
    omega
  have hac : a ≠ c := by
    intro h
    have hval := congrArg Fin.val h
    omega
  have hbc : b ≠ c := by
    intro h
    have hval := congrArg Fin.val h
    omega
  have hua : G.Adj u (D.path.vertex a) := by
    rw [L.introduced_eq previous]
    simpa [previous] using huPreviousIntroduced
  obtain ⟨t', ht', ht's, huPreviousRemoved'⟩ :=
    D.adj_previous_removed_of_outside_commuting
      M L hclaw horder hopposite hu huOutside hnotAnti
  have htt : t' = t := by omega
  subst t'
  have hub : G.Adj u (D.path.vertex b) := by
    rw [L.removed_eq previous]
    simpa [previous] using huPreviousRemoved'
  have huStep :
      u ∈ (D.deformation.step current).dependentSet := by
    simpa [current] using
      D.mem_step_dependentSet_of_mem_dependentAt hu
  have hmem :=
    (ConcreteDeformationStep.mem_dependentSet
      (D.deformation.step current)).1 huStep
  have huc : G.Adj u (D.path.vertex c) := by
    rw [L.introduced_eq current]
    exact hmem.2.1
  have hcount :=
    D.outside_path_neighbor_count_eq_two_or_four
      L hclaw hu huOutside hnotAnti
  have hfour :
      (D.path.neighborIndexSet u).ncard = 4 := by
    rcases hcount with htwo | hfour
    · have hsubset :
          ({a, b, c} : Set (Fin D.path.card)) ⊆
            D.path.neighborIndexSet u := by
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl
        · exact hua
        · exact hub
        · exact huc
      have hcard :
          ({a, b, c} : Set (Fin D.path.card)).ncard = 3 := by
        exact Set.ncard_eq_three.mpr
          ⟨a, b, c, hab, hac, hbc, rfl⟩
      have hle := Set.ncard_le_ncard hsubset
      rw [hcard, htwo] at hle
      omega
    · exact hfour
  have hextra :
      ∃ x : Fin D.path.card,
        x ∈ D.path.neighborIndexSet u ∧
        x ≠ a ∧ x ≠ b ∧ x ≠ c := by
    by_contra hno
    have hsubset :
        D.path.neighborIndexSet u ⊆
          ({a, b, c} : Set (Fin D.path.card)) := by
      intro y hy
      by_cases hya : y = a
      · simp [hya]
      by_cases hyb : y = b
      · simp [hyb]
      by_cases hyc : y = c
      · simp [hyc]
      exact (hno ⟨y, hy, hya, hyb, hyc⟩).elim
    have hcard :
        ({a, b, c} : Set (Fin D.path.card)).ncard = 3 := by
      exact Set.ncard_eq_three.mpr
        ⟨a, b, c, hab, hac, hbc, rfl⟩
    have hle := Set.ncard_le_ncard hsubset
    rw [hfour, hcard] at hle
    omega
  obtain ⟨x, hxmem, hxa, hxb, hxc⟩ := hextra
  have hux : G.Adj u (D.path.vertex x) := hxmem
  have hxaVertex : D.path.vertex x ≠ D.path.vertex a := by
    intro h
    exact hxa (D.path.injective h)
  have hxbVertex : D.path.vertex x ≠ D.path.vertex b := by
    intro h
    exact hxb (D.path.injective h)
  have hxcVertex : D.path.vertex x ≠ D.path.vertex c := by
    intro h
    exact hxc (D.path.injective h)
  have habVertex : D.path.vertex a ≠ D.path.vertex b := by
    intro h
    exact hab (D.path.injective h)
  have hacVertex : D.path.vertex a ≠ D.path.vertex c := by
    intro h
    exact hac (D.path.injective h)
  have hbcVertex : D.path.vertex b ≠ D.path.vertex c := by
    intro h
    exact hbc (D.path.injective h)
  have hxAdj :
      G.Adj (D.path.vertex x) (D.path.vertex a) ∨
      G.Adj (D.path.vertex x) (D.path.vertex b) ∨
      G.Adj (D.path.vertex x) (D.path.vertex c) :=
    hclaw.four_neighbors_no_isolated
      hux hua hub huc
      hxaVertex hxbVertex hxcVertex
      habVertex hacVertex hbcVertex
      (D.path.not_triangle a b c)
  have hends :
      x.val + 1 = a.val ∨ c.val + 1 = x.val := by
    rcases hxAdj with hxaAdj | hxbAdj | hxcAdj
    · rcases (D.path.adj_iff x a).1 hxaAdj with h | h
      · exact Or.inl h
      · right
        omega
    · rcases (D.path.adj_iff x b).1 hxbAdj with h | h
      · left
        omega
      · right
        omega
    · rcases (D.path.adj_iff x c).1 hxcAdj with h | h
      · left
        omega
      · exact Or.inr h
  let q : Fin D.path.card := L.removedPathIndex current
  have hqval : q.val = 2 * s + 1 := by
    simpa [q, current] using
      L.removed_index_val current
  have huqNotAdj : ¬G.Adj u (D.path.vertex q) := by
    rw [L.removed_eq current]
    exact hmem.2.2.2
  have hxleft : x.val + 1 = a.val := by
    rcases hends with hxleft | hxright
    · exact hxleft
    · have hxq : x = q := by
        apply Fin.ext
        omega
      subst x
      exact (huqNotAdj hux).elim
  have hsTwo : 1 < s := by
    omega
  refine ⟨hsTwo, x, ?_, hux, hfour⟩
  simpa [a, previous] using hxleft

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
