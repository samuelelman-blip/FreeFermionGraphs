import FreeFermionGraphs.Lemma11BOutsideDegreePropagation
import FreeFermionGraphs.Lemma11BOutsideFourPathBlock

/-!
# Lemma 11(b): later replacements in the ordinary outside branch

When an outside commuting dependent vertex neighbors the preceding
introduced vertex, its active-path neighbors are exactly the four-vertex
block ending at the current introduced vertex.  Every vertex used by a
strictly later replacement lies to the right of this block.  Consequently
the vertex neighbors neither member of any later introduced/removed pair,
which is the adjacency agreement needed to propagate degree four.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
variable {O : FixedPairingPathFamily G} {Cprime : Set V}

namespace ConcretePathDeformation

/-- The ordinary outside branch satisfies the later replacement adjacency
agreement (in fact, both adjacencies are false). -/
theorem laterReplacementAdjacencyAgreement_of_adj_previous_introduced
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
    D.LaterReplacementAdjacencyAgreement s u := by
  obtain ⟨hsTwo, x, hx, hux, hfour⟩ :=
    D.four_path_neighbor_block_of_adj_previous_introduced
      M L hclaw horder hopposite
      hu huOutside hnotAnti ht hts huPreviousIntroduced
  have hs : s < D.deformation.stepCount :=
    D.index_lt_of_mem_dependentAt hu
  let previous : Fin D.deformation.stepCount := ⟨t, ht⟩
  let current : Fin D.deformation.stepCount := ⟨s, hs⟩
  let a : Fin D.path.card := L.introducedPathIndex previous
  let b : Fin D.path.card := L.removedPathIndex previous
  let c : Fin D.path.card := L.introducedPathIndex current
  have hxval : x.val + 1 = a.val := by
    simpa [a, previous] using hx
  have haval : a.val = 2 * t := by
    simpa [a, previous] using L.introduced_index_val previous
  have hbval : b.val = 2 * t + 1 := by
    simpa [b, previous] using L.removed_index_val previous
  have hcval : c.val = 2 * s := by
    simpa [c, current] using L.introduced_index_val current
  have hxa : x ≠ a := by
    intro h
    have hval := congrArg Fin.val h
    omega
  have hxb : x ≠ b := by
    intro h
    have hval := congrArg Fin.val h
    omega
  have hxc : x ≠ c := by
    intro h
    have hval := congrArg Fin.val h
    omega
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
  have htt : t' = t := by
    omega
  have hpreviousFin :
      (⟨t', ht'⟩ : Fin D.deformation.stepCount) = previous := by
    apply Fin.ext
    change t' = previous.val
    simpa [previous] using htt
  have hub : G.Adj u (D.path.vertex b) := by
    rw [L.removed_eq previous]
    rw [hpreviousFin] at huPreviousRemoved'
    exact huPreviousRemoved'
  have huCurrent :
      u ∈ (D.deformation.step current).dependentSet := by
    simpa [current] using
      D.mem_step_dependentSet_of_mem_dependentAt hu
  have huc : G.Adj u (D.path.vertex c) := by
    rw [L.introduced_eq current]
    exact
      ((ConcreteDeformationStep.mem_dependentSet
        (D.deformation.step current)).1 huCurrent).2.1
  let known : Set (Fin D.path.card) := {x, a, b, c}
  have hknownSubset :
      known ⊆ D.path.neighborIndexSet u := by
    intro y hy
    simp only [known, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact hux
    · exact hua
    · exact hub
    · exact huc
  have hknownCard : known.ncard = 4 := by
    apply Set.ncard_eq_four.mpr
    exact
      ⟨x, a, b, c, hxa, hxb, hxc,
        hab, hac, hbc, rfl⟩
  have hneighborSet :
      D.path.neighborIndexSet u = known := by
    apply Set.Subset.antisymm
    · intro y hy
      by_contra hyKnown
      have hinsertSubset :
          Set.insert y known ⊆
            D.path.neighborIndexSet u := by
        intro z hz
        rcases Set.mem_insert_iff.1 hz with rfl | hz
        · exact hy
        · exact hknownSubset hz
      have hinsertCard :
          (Set.insert y known).ncard = 5 := by
        rw [Set.ncard_insert_of_notMem hyKnown, hknownCard]
      have hle := Set.ncard_le_ncard hinsertSubset
      rw [hinsertCard, hfour] at hle
      omega
    · exact hknownSubset
  intro j hsj
  have hnotIntroduced :
      ¬G.Adj u (D.deformation.step j).introduced := by
    intro huj
    have hjmem :
        L.introducedPathIndex j ∈
          D.path.neighborIndexSet u := by
      change G.Adj u
        (D.path.vertex (L.introducedPathIndex j))
      rw [L.introduced_eq j]
      exact huj
    rw [hneighborSet] at hjmem
    simp only [known, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hjmem
    have hjval := L.introduced_index_val j
    rcases hjmem with hjx | hja | hjb | hjc
    · have hval := congrArg Fin.val hjx
      omega
    · have hval := congrArg Fin.val hja
      omega
    · have hval := congrArg Fin.val hjb
      omega
    · have hval := congrArg Fin.val hjc
      omega
  have hnotRemoved :
      ¬G.Adj u
        ((D.deformation.step j).before.vertex
          (D.deformation.step j).removedIndex) := by
    intro huj
    have hjmem :
        L.removedPathIndex j ∈
          D.path.neighborIndexSet u := by
      change G.Adj u
        (D.path.vertex (L.removedPathIndex j))
      rw [L.removed_eq j]
      exact huj
    rw [hneighborSet] at hjmem
    simp only [known, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hjmem
    have hjval := L.removed_index_val j
    rcases hjmem with hjx | hja | hjb | hjc
    · have hval := congrArg Fin.val hjx
      omega
    · have hval := congrArg Fin.val hja
      omega
    · have hval := congrArg Fin.val hjb
      omega
    · have hval := congrArg Fin.val hjc
      omega
  exact iff_of_false hnotIntroduced hnotRemoved

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
