import FreeFermionGraphs.Lemma11BComplete
import FreeFermionGraphs.Lemma11BExceptionalPathDescent
import FreeFermionGraphs.Lemma11BHalfLengthGtThree
import FreeFermionGraphs.Lemma11BHalfLengthTwo
import FreeFermionGraphs.Lemma11BOrdinaryPathDescent

/-!
# Lemma 11(b): complete Definition 19 path descent

The last recursive case in the paper does not always give a single common
`C_b` neighbor of the current vertex and its predecessor.  In the deepest
ordinary case it gives the displayed alternating chain instead.  Every
edge of that chain lies on the `C_b ∪ C'_d` side, so the exact invariant
needed by the well-founded proof is `SharesBDPath`.  This typed relation is
transitive even at vertices belonging to an overlap of the two holes.

This module combines the in-path prime-hole predecessor, the ordinary
outside branch, and the exceptional six-cycle branch into strict path
descent.  It then supplies the abstract local data and proves Lemma 11(b)
without a residual recursive-case assumption.  The base application of
Lemma 7 still receives its opposite-endpoint nonedge explicitly at the
Definition 19 integration boundary.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V} {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation

/-- Every commuting dependent vertex has a strictly earlier Definition 20
vertex in the same fixed-pairing path component. -/
def StrictDefinition20SharesBDPathRule
    (D : ConcretePathDeformation O Cprime) : Prop :=
  ∀ ⦃s : Nat⦄ ⦃u : V⦄,
    u ∈ D.dependentAt s →
    ¬D.path.AnticommutesWith u →
    ∃ s' : Nat, ∃ u' : V,
      s' < s ∧
      D.Definition20DependentAt s' u' ∧
      O.SharesBDPath u' u

/-- The alternating Definition 19 data and the unchanged prime hole prove
strict path descent in all in-path and outside-path cases. -/
theorem strictDefinition20SharesBDPathRule_of_alternating_primeHole
    {k kPrime : Nat}
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (A : D.AlternatingLabelingSequence k)
    (P : D.PrimeAlternatingHoleData kPrime)
    (hcycle : A.HasFullCyclicOrder)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    (hcolors : O.PrimeCarrierOverlapColored Cprime)
    (hopposite : D.BaseOppositeEndpointNonadjacency) :
    D.StrictDefinition20SharesBDPathRule := by
  let horder : Definition19PathOrder M :=
    D.definition19PathOrder_of_globalOverlapPathOrder M L
  intro s u hu hnotAnti
  by_cases huPath : u ∈ Set.range D.path.vertex
  · obtain ⟨t, _ht, hts, _huRemoved⟩ :=
      D.dependent_mem_path_eq_previous_removed L hu huPath
    obtain ⟨u', w, hu'Definition20, hwCb, hu'w, huw⟩ :=
      (D.inPathPreviousStepCommonNeighborRule_of_primeHole
        M P L hclaw) hu huPath hnotAnti
    have hu'Mem : u' ∈ D.dependentAt (s - 1) :=
      (D.mem_dependentAt_iff_definition20).2 hu'Definition20
    exact ⟨s - 1, u', by omega, hu'Definition20,
      M.sharesBDPath_of_common_cb
        (M.dependent_mem_cd hu'Mem) (M.dependent_mem_cd hu)
        hwCb hu'w huw⟩
  · cases s with
    | zero =>
        exact (hnotAnti
          (D.baseDependentAnticommutes_of_baseParity
            M hclaw horder hopposite hu)).elim
    | succ t =>
        have ordinaryDescent
            (previous : Fin D.deformation.stepCount)
            (hprevious : previous.val + 1 = Nat.succ t)
            (huPreviousIntroduced :
              G.Adj u (D.deformation.step previous).introduced) :
            ∃ s' : Nat, ∃ u' : V,
              s' < Nat.succ t ∧
              D.Definition20DependentAt s' u' ∧
              O.SharesBDPath u' u := by
          obtain hone | htwo :=
            D.ordinary_oneOrTwoStepDefinition20_sharesBDPath
              M A P L hclaw hcolors horder hopposite
              hu huPath hnotAnti previous.isLt
              (by omega) huPreviousIntroduced
          · obtain ⟨u', hu'Definition20, hu'Shares⟩ := hone
            exact ⟨previous.val, u', by omega,
              hu'Definition20, hu'Shares⟩
          · obtain ⟨e, he, u', hu'Definition20, hu'Shares⟩ := htwo
            exact ⟨e, u', by omega, hu'Definition20, hu'Shares⟩
        have hkTwo : 2 ≤ k := (A.labeling D.firstIndex).two_le
        by_cases hkEqTwo : k = 2
        · subst k
          obtain ⟨previous, hprevious,
              huPreviousIntroduced⟩ :=
            D.adj_previous_introduced_of_halfLength_two
              M A L hclaw horder hopposite hu huPath hnotAnti
          exact ordinaryDescent previous hprevious
            huPreviousIntroduced
        · by_cases hkEqThree : k = 3
          · subst k
            obtain ⟨r, hr, hrs, _huPreviousRemoved⟩ :=
              D.adj_previous_removed_of_outside_commuting
                M L hclaw horder hopposite hu huPath hnotAnti
            let previous : Fin D.deformation.stepCount := ⟨r, hr⟩
            have hprevious :
                previous.val + 1 = Nat.succ t := by
              dsimp [previous]
              omega
            by_cases huPreviousIntroduced :
                G.Adj u (D.deformation.step previous).introduced
            · exact ordinaryDescent previous hprevious
                huPreviousIntroduced
            · obtain ⟨v, hvDefinition20, hvShares⟩ :=
                D.exceptional_previousDefinition20_sharesBDPath
                  M A P L hclaw hcolors horder hopposite
                  hu huPath hnotAnti previous hprevious
                  huPreviousIntroduced
              exact ⟨previous.val, v, by omega,
                hvDefinition20, hvShares⟩
          · have hkLong : 3 < k := by omega
            obtain ⟨previous, hprevious,
                huPreviousIntroduced⟩ :=
              D.adj_previous_introduced_of_three_lt
                M A hcycle hkLong L hclaw horder hopposite
                hu huPath hnotAnti
            exact ordinaryDescent previous hprevious
              huPreviousIntroduced

/-- The path-descent rule supplies the abstract predecessor field used by
the well-founded Lemma 11(b) argument. -/
theorem dependentDescentRule_of_strictDefinition20SharesBDPath
    (D : ConcretePathDeformation O Cprime)
    (hdesc : D.StrictDefinition20SharesBDPathRule) :
    DependentDescentRule
      D.dependentAt D.path.AnticommutesWith O.SharesBDPath := by
  intro s u hu hnotAnti
  obtain ⟨s', u', hs', hu'Definition20, hu'Shares⟩ :=
    hdesc hu hnotAnti
  exact ⟨s', u', hs',
    (D.mem_dependentAt_iff_definition20).2 hu'Definition20,
    hu'Shares⟩

/-- Complete Lemma 11(b) from the transported alternating hole, its cyclic
order, and the unchanged prime hole.  No recursive local rule remains. -/
theorem lemma11b_of_alternatingLabelingSequence_and_primeHole
    {k kPrime : Nat}
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (A : D.AlternatingLabelingSequence k)
    (P : D.PrimeAlternatingHoleData kPrime)
    (hcycle : A.HasFullCyclicOrder)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    (hcolors : O.PrimeCarrierOverlapColored Cprime)
    (hopposite : D.BaseOppositeEndpointNonadjacency)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (hcomm : ¬D.path.AnticommutesWith u) :
    D.finalDegree s u = 4 ∧
      O.EarlierAnticommutingWitnessInUniqueBDPath
        D.dependentAt D.path.AnticommutesWith s u := by
  let horder : Definition19PathOrder M :=
    D.definition19PathOrder_of_globalOverlapPathOrder M L
  have hInitialEven : Even D.initialHole.card := A.initialHole_even
  refine ⟨D.finalDegreeFourRule_of_alternating
    M A hcycle L hclaw hInitialEven hcolors horder hopposite hu hcomm, ?_⟩
  have hdesc :
      DependentDescentRule D.dependentAt D.path.AnticommutesWith
        O.SharesBDPath :=
    D.dependentDescentRule_of_strictDefinition20SharesBDPath
      (D.strictDefinition20SharesBDPathRule_of_alternating_primeHole
        M A P hcycle L hclaw hcolors hopposite)
  obtain ⟨s', u', hs', hu', hanti', hsharesBD⟩ :=
    earlierAnticommutingWitness_of_descent hdesc
      (fun {_t} {_x} {_y} {_z} _hy hxy hyz =>
        O.sharesBDPath_trans hxy hyz)
      hu hcomm
  rcases hsharesBD with ⟨Q, hQ, hu'Q, huQ⟩
  exact ⟨s', u', Q, hs', hu', hanti',
    O.isUniqueContainingBDPath hQ hu'Q, huQ⟩

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
