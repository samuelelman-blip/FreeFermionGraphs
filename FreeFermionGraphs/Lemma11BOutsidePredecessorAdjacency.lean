import FreeFermionGraphs.Lemma11BOutsidePathNeighborCount

/-!
# Lemma 11(b): the forced preceding path neighbor

In the outside-path branch of Lemma 11(b), a commuting dependent vertex
cannot occur at the first deformation step. In zero-based Lean indexing its
step therefore has a predecessor.

At a positive step, the current introduced path vertex lies between the
previous and current removed vertices. The dependent vertex neighbors the
introduced vertex and misses the current removed vertex. If it also missed
the previous removed vertex, those three vertices would be pairwise
nonadjacent neighbors of the introduced vertex, forming a claw. Hence the
previous removed vertex is a neighbor, as asserted in the paper.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- A commuting dependent vertex occurs strictly after the first step. -/
theorem step_pos_of_mem_dependentAt_of_not_anticommutes
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (hclaw : G.IsClawFree)
    (horder : Definition19PathOrder M)
    (hopposite : D.BaseOppositeEndpointNonadjacency)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (hnotAnti : ¬D.path.AnticommutesWith u) :
    0 < s := by
  by_contra hs
  have hzero : s = 0 := by omega
  subst s
  exact hnotAnti
    (D.baseDependentAnticommutes_of_baseParity
      M hclaw horder hopposite hu)

/-- The paper's forced previous-removed adjacency, in zero-based indexing:
an outside-path commuting dependent vertex at step s neighbors the vertex
removed at step s - 1. -/
theorem adj_previous_removed_of_outside_commuting
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    (horder : Definition19PathOrder M)
    (hopposite : D.BaseOppositeEndpointNonadjacency)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huOutside : u ∉ Set.range D.path.vertex)
    (hnotAnti : ¬D.path.AnticommutesWith u) :
    ∃ t : Nat, ∃ ht : t < D.deformation.stepCount,
      Nat.succ t = s ∧
      G.Adj u
        ((D.deformation.step ⟨t, ht⟩).before.vertex
          (D.deformation.step ⟨t, ht⟩).removedIndex) := by
  have hsPos : 0 < s :=
    D.step_pos_of_mem_dependentAt_of_not_anticommutes
      M hclaw horder hopposite hu hnotAnti
  have hs : s < D.deformation.stepCount :=
    D.index_lt_of_mem_dependentAt hu
  let t : Nat := s - 1
  have ht : t < D.deformation.stepCount := by
    dsimp [t]
    omega
  have hsucc : Nat.succ t = s := by
    dsimp [t]
    omega
  let previous : Fin D.deformation.stepCount := ⟨t, ht⟩
  let current : Fin D.deformation.stepCount := ⟨s, hs⟩
  let p : Fin D.path.card := L.removedPathIndex previous
  let j : Fin D.path.card := L.introducedPathIndex current
  let q : Fin D.path.card := L.removedPathIndex current
  have hpval : p.val = 2 * (s - 1) + 1 := by
    simpa [p, previous, t] using
      L.removed_index_val previous
  have hjval : j.val = 2 * s := by
    simpa [j, current] using
      L.introduced_index_val current
  have hqval : q.val = 2 * s + 1 := by
    simpa [q, current] using
      L.removed_index_val current
  have hpj : p.val + 1 = j.val := by
    omega
  have hjq : j.val + 1 = q.val := by
    omega
  have hjpAdj :
      G.Adj (D.path.vertex j) (D.path.vertex p) :=
    (D.path.adj_iff j p).2 (Or.inr hpj)
  have hjqAdj :
      G.Adj (D.path.vertex j) (D.path.vertex q) :=
    (D.path.adj_iff j q).2 (Or.inl hjq)
  have hpqNotAdj :
      ¬G.Adj (D.path.vertex p) (D.path.vertex q) := by
    intro hpq
    rcases (D.path.adj_iff p q).1 hpq with
      hpq | hqp <;> omega
  have huStep :
      u ∈ (D.deformation.step current).dependentSet := by
    simpa [current] using
      D.mem_step_dependentSet_of_mem_dependentAt hu
  have hmem :=
    (ConcreteDeformationStep.mem_dependentSet
      (D.deformation.step current)).1 huStep
  have huj :
      G.Adj u (D.path.vertex j) := by
    rw [L.introduced_eq current]
    exact hmem.2.1
  have huqNotAdj :
      ¬G.Adj u (D.path.vertex q) := by
    rw [L.removed_eq current]
    exact hmem.2.2.2
  have hupNe : u ≠ D.path.vertex p := by
    intro hup
    exact huOutside ⟨p, hup.symm⟩
  have huqNe : u ≠ D.path.vertex q := by
    intro huq
    exact huOutside ⟨q, huq.symm⟩
  have hpqNe : D.path.vertex p ≠ D.path.vertex q := by
    intro hpq
    have hpqIndex : p = q := D.path.injective hpq
    have hpqVal := congrArg Fin.val hpqIndex
    omega
  have hup :
      G.Adj u (D.path.vertex p) := by
    rcases hclaw huj.symm hjpAdj hjqAdj
        hupNe huqNe hpqNe with
      hup | huq | hpq
    · exact hup
    · exact (huqNotAdj huq).elim
    · exact (hpqNotAdj hpq).elim
  refine ⟨t, ht, hsucc, ?_⟩
  rw [← L.removed_eq previous]
  simpa [p] using hup

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
