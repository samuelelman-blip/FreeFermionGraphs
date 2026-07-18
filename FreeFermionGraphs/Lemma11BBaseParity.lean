import FreeFermionGraphs.Lemma11BBasePathOrder

/-!
# Lemma 11(b): base-step parity from Lemma 7

At the first deformation step a dependent vertex neighbors the initial
introduced endpoint and does not neighbor the following removed vertex.
Lemma 7 then rules out every even path-neighbor count except the
two-endpoint case.  Excluding adjacency to the opposite endpoint therefore
proves anticommutation directly.

This replaces the former assumption that the introduced endpoint is the
dependent vertex's unique path neighbor by the single endpoint nonedge
which is actually needed.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace IndexedInducedPath

/-- If an external vertex neighbors the first path vertex, misses the
second and last vertices, then Lemma 7 forces an odd number of path
neighbors. -/
theorem anticommutesWith_of_first_neighbor_not_second_not_last
    (P : IndexedInducedPath G)
    (hclaw : G.IsClawFree)
    {u : V}
    (huOutside : u ∉ Set.range P.vertex)
    {first second : Fin P.card}
    (hfirst : first.val = 0)
    (hsecond : second.val = 1)
    (huFirst : G.Adj u (P.vertex first))
    (huSecond : ¬G.Adj u (P.vertex second))
    (huLast : ∀ q : Fin P.card,
      q.val + 1 = P.card → ¬G.Adj u (P.vertex q)) :
    P.AnticommutesWith u := by
  apply (P.anticommutesWith_iff_not_commutesWith u).2
  intro hcomm
  rcases P.commutesWith_count_eq_zero_or_two_or_four
      hclaw huOutside hcomm with hzero | htwo | hfour
  · have hnonempty : (P.neighborIndexSet u).Nonempty := by
      exact ⟨first, huFirst⟩
    have hpos : 0 < (P.neighborIndexSet u).ncard :=
      Set.ncard_pos.mpr hnonempty
    omega
  · have twoImpossible
        (q : Fin P.card)
        (hfirstq : first ≠ q)
        (huq : G.Adj u (P.vertex q))
        (hexact : ∀ k : Fin P.card,
          G.Adj u (P.vertex k) → k = first ∨ k = q) : False := by
      rcases P.two_external_neighbors_classification
          hclaw huOutside hfirstq huFirst huq hexact with
        hpair | hendpoints | hendpoints
      · have hq : q.val = 1 := by
          rcases (P.adj_iff first q).1 hpair with h | h <;> omega
        have hqsecond : q = second := by
          apply Fin.ext
          omega
        subst q
        exact huSecond huq
      · exact huLast q hendpoints.2 huq
      · have hqfirst : q = first := by
          apply Fin.ext
          omega
        exact hfirstq hqfirst.symm
    obtain ⟨a, b, hab, hset⟩ := Set.ncard_eq_two.mp htwo
    have haMem : a ∈ P.neighborIndexSet u := by
      rw [hset]
      simp
    have hbMem : b ∈ P.neighborIndexSet u := by
      rw [hset]
      simp
    have hua : G.Adj u (P.vertex a) := haMem
    have hub : G.Adj u (P.vertex b) := hbMem
    have hfirstMem : first ∈ P.neighborIndexSet u := huFirst
    rw [hset] at hfirstMem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hfirstMem
    rcases hfirstMem with hfa | hfb
    · subst a
      apply twoImpossible b hab hub
      intro k huk
      have hk : k ∈ P.neighborIndexSet u := huk
      rw [hset] at hk
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hk
    · subst b
      apply twoImpossible a hab.symm hua
      intro k huk
      have hk : k ∈ P.neighborIndexSet u := huk
      rw [hset] at hk
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
      rcases hk with hka | hkfirst
      · exact Or.inr hka
      · exact Or.inl hkfirst
  · have noAdjFromFirst
        (q : Fin P.card)
        (huq : G.Adj u (P.vertex q)) :
        ¬G.Adj (P.vertex first) (P.vertex q) := by
      intro hfirstq
      have hq : q.val = 1 := by
        rcases (P.adj_iff first q).1 hfirstq with h | h <;> omega
      have hqsecond : q = second := by
        apply Fin.ext
        omega
      subst q
      exact huSecond huq
    have fourImpossible
        (q r s : Fin P.card)
        (hfirstq : first ≠ q)
        (hfirstr : first ≠ r)
        (hfirsts : first ≠ s)
        (hqr : q ≠ r)
        (hqs : q ≠ s)
        (hrs : r ≠ s)
        (huq : G.Adj u (P.vertex q))
        (hur : G.Adj u (P.vertex r))
        (hus : G.Adj u (P.vertex s)) : False := by
      have hfirstqv : P.vertex first ≠ P.vertex q :=
        fun h => hfirstq (P.injective h)
      have hfirstrv : P.vertex first ≠ P.vertex r :=
        fun h => hfirstr (P.injective h)
      have hfirstsv : P.vertex first ≠ P.vertex s :=
        fun h => hfirsts (P.injective h)
      have hqrv : P.vertex q ≠ P.vertex r :=
        fun h => hqr (P.injective h)
      have hqsv : P.vertex q ≠ P.vertex s :=
        fun h => hqs (P.injective h)
      have hrsv : P.vertex r ≠ P.vertex s :=
        fun h => hrs (P.injective h)
      have hqrAdj : G.Adj (P.vertex q) (P.vertex r) := by
        rcases hclaw huFirst huq hur
            hfirstqv hfirstrv hqrv with
          hfirstqAdj | hfirstrAdj | hqrAdj
        · exact (noAdjFromFirst q huq hfirstqAdj).elim
        · exact (noAdjFromFirst r hur hfirstrAdj).elim
        · exact hqrAdj
      have hqsAdj : G.Adj (P.vertex q) (P.vertex s) := by
        rcases hclaw huFirst huq hus
            hfirstqv hfirstsv hqsv with
          hfirstqAdj | hfirstsAdj | hqsAdj
        · exact (noAdjFromFirst q huq hfirstqAdj).elim
        · exact (noAdjFromFirst s hus hfirstsAdj).elim
        · exact hqsAdj
      have hrsAdj : G.Adj (P.vertex r) (P.vertex s) := by
        rcases hclaw huFirst hur hus
            hfirstrv hfirstsv hrsv with
          hfirstrAdj | hfirstsAdj | hrsAdj
        · exact (noAdjFromFirst r hur hfirstrAdj).elim
        · exact (noAdjFromFirst s hus hfirstsAdj).elim
        · exact hrsAdj
      exact P.not_triangle q r s ⟨hqrAdj, hrsAdj, hqsAdj⟩
    obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hset⟩ :=
      Set.ncard_eq_four.mp hfour
    have haMem : a ∈ P.neighborIndexSet u := by
      rw [hset]
      simp
    have hbMem : b ∈ P.neighborIndexSet u := by
      rw [hset]
      simp
    have hcMem : c ∈ P.neighborIndexSet u := by
      rw [hset]
      simp
    have hdMem : d ∈ P.neighborIndexSet u := by
      rw [hset]
      simp
    have hua : G.Adj u (P.vertex a) := haMem
    have hub : G.Adj u (P.vertex b) := hbMem
    have huc : G.Adj u (P.vertex c) := hcMem
    have hud : G.Adj u (P.vertex d) := hdMem
    have hfirstMem : first ∈ P.neighborIndexSet u := huFirst
    rw [hset] at hfirstMem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hfirstMem
    rcases hfirstMem with hfa | hfb | hfc | hfd
    · subst a
      exact fourImpossible b c d
        hab hac had hbc hbd hcd hub huc hud
    · subst b
      exact fourImpossible a c d
        hab.symm hbc hbd hac had hcd hua huc hud
    · subst c
      exact fourImpossible a b d
        hac.symm hbc.symm hcd hab had hbd hua hub hud
    · subst d
      exact fourImpossible a b c
        had.symm hbd.symm hcd.symm hab hac hbc hua hub huc

end IndexedInducedPath

namespace FixedPairingPathFamily

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- The remaining base geometry after Lemma 7: a first-step dependent
vertex is not adjacent to the endpoint opposite the introduced vertex. -/
def BaseOppositeEndpointNonadjacency
    (D : ConcretePathDeformation O Cprime) : Prop :=
  ∀ ⦃u : V⦄,
    u ∈ D.dependentAt 0 →
    ∀ q : Fin D.path.card,
      q.val + 1 = D.path.card →
      ¬G.Adj u (D.path.vertex q)

/-- The ordered first-step labels, dependent-set definition and Lemma 7
reduce the full base anticommutation theorem to the opposite-endpoint
nonedge. -/
theorem baseDependentAnticommutes_of_baseParity
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (hclaw : G.IsClawFree)
    (horder : Definition19PathOrder M)
    (hopposite : D.BaseOppositeEndpointNonadjacency)
    {u : V} (hu : u ∈ D.dependentAt 0) :
    D.path.AnticommutesWith u := by
  have huStep :
      u ∈ (D.deformation.step D.firstIndex).dependentSet := by
    simpa [firstIndex] using
      D.mem_step_dependentSet_of_mem_dependentAt hu
  have hmem :=
    (ConcreteDeformationStep.mem_dependentSet
      (D.deformation.step D.firstIndex)).1 huStep
  have huOutside :
      u ∉ Set.range D.path.vertex :=
    D.dependent_not_mem_path M.stepLabeling hu
  have huLast := hopposite hu
  rw [← D.activePath_eq D.firstIndex] at huOutside huLast ⊢
  refine
    (D.deformation.step D.firstIndex).activePath.
      anticommutesWith_of_first_neighbor_not_second_not_last
        hclaw huOutside
        (M.firstIntroducedIndex_val_eq_zero horder)
        (M.firstRemovedIndex_val_eq_one horder)
        ?_ ?_ huLast
  · rw [(M.stepLabeling D.firstIndex).introduced_eq]
    exact hmem.2.1
  · rw [(M.stepLabeling D.firstIndex).removed_eq]
    exact hmem.2.2.2

/-- The reduced base parity input and the one/two-step attachment rule give
the complete common-`C_b` predecessor rule. -/
theorem commonBPredecessorRule_of_baseParity_and_attachingPredecessors
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (hclaw : G.IsClawFree)
    (horder : Definition19PathOrder M)
    (hopposite : D.BaseOppositeEndpointNonadjacency)
    (hattach : D.OneOrTwoStepPredecessorAlongBNeighborsRule) :
    O.CommonBPredecessorRule
      .ac D.dependentAt D.path.AnticommutesWith := by
  have hlocal : D.OneOrTwoStepCommonBNeighborRule :=
    D.oneOrTwoStepCommonBNeighborRule_of_attachingPredecessors
      M hclaw hattach
  have htyped :
      O.OneOrTwoStepCommonBPredecessorRule
        .ac D.dependentAt D.path.AnticommutesWith :=
    D.oneOrTwoStepCommonBPredecessorRule_of_commonNeighbors
      M hlocal
  have hsucc :
      O.SuccessorCommonBPredecessorRule
        .ac D.dependentAt D.path.AnticommutesWith :=
    O.successorCommonBPredecessorRule_of_oneOrTwoStep
      .ac D.dependentAt D.path.AnticommutesWith htyped
  exact O.commonBPredecessorRule_of_base_and_successor
    .ac D.dependentAt D.path.AnticommutesWith
    (fun {_u} hu =>
      D.baseDependentAnticommutes_of_baseParity
        M hclaw horder hopposite hu)
    hsucc

/-- Concrete Lemma 11(b) with the strong base unique-neighbor assumption
replaced by the single opposite-endpoint nonadjacency. -/
theorem lemma11b_of_ccTriples_baseParity_and_attachingPredecessors
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (hclaw : G.IsClawFree)
    (hEven : Even D.finalHole.card)
    (htriple : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ D.dependentAt s →
      ¬D.path.AnticommutesWith u →
      D.HasCCIsolatedFinalTriple u)
    (horder : Definition19PathOrder M)
    (hopposite : D.BaseOppositeEndpointNonadjacency)
    (hattach : D.OneOrTwoStepPredecessorAlongBNeighborsRule)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (hcomm : ¬D.path.AnticommutesWith u) :
    D.finalDegree s u = 4 ∧
      O.EarlierAnticommutingWitnessInUniquePath
        D.dependentAt D.path.AnticommutesWith s u :=
  D.lemma11b_of_concretePathDeformation_of_ccIsolatedFinalTriples
    M hclaw hEven htriple
    (D.commonBPredecessorRule_of_baseParity_and_attachingPredecessors
      M hclaw horder hopposite hattach)
    hu hcomm

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
