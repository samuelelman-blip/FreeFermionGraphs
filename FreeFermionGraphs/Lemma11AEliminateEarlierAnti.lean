import FreeFermionGraphs.Lemma11AEarlierAnti

/-!
# Lemma 11(a.ii): eliminating all earlier anticommuting paths

This module performs the finite maximal-index argument from the manuscript.
Given Corollary 12's endpoint alternative for every earlier path, select the
last earlier path that anticommutes with `u`.  All following paths commute,
so the endpoint-parity contradiction rules it out.  Thus no earlier path
anticommutes with `u`.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- The Corollary-12 endpoint condition for an earlier path relative to
the current path block. -/
def EarlierAnticommutingEndpointRule
    (D : ConcretePathDeformation O Cprime)
    (H : PathBlockHistory (O := O) (Cprime := Cprime))
    (m : Nat) (u : V) : Prop :=
  ∀ r : Nat,
    r < m →
    (H.block r).path.AnticommutesWith u →
      u = ((H.block r).deformation.step (H.block r).firstIndex).introduced ∨
        u = (D.deformation.step D.firstIndex).introduced

/-- If the current dependent replacement has degree four, Corollary 12
rules out every anticommuting earlier path in the finite history. -/
theorem no_earlierAnticommutation_of_currentDegree_four
    (D : ConcretePathDeformation O Cprime)
    (u : V)
    (hcurrentStep :
      D.finalHole.externalDegree u =
        D.initialHole.externalDegree u + 1)
    (hcurrentNotFirst :
      u ≠ (D.deformation.step D.firstIndex).introduced)
    (hfour : D.finalHole.externalDegree u = 4)
    (H : PathBlockHistory (O := O) (Cprime := Cprime))
    (m : Nat)
    (hbeforeCurrent : 0 < m →
      Set.range (H.block (m - 1)).finalHole.vertex =
        Set.range D.initialHole.vertex)
    (hendpoint : D.EarlierAnticommutingEndpointRule H m u) :
    ∀ r : Nat, r < m → ¬(H.block r).path.AnticommutesWith u := by
  classical
  intro r hr hanti
  let S : Finset Nat :=
    (Finset.range m).filter (fun q => decide ((H.block q).path.AnticommutesWith u))
  have hrS : r ∈ S := by
    simp [S, hr, hanti]
  have hSnonempty : S.Nonempty := ⟨r, hrS⟩
  let q : Nat := S.max' hSnonempty
  have hqS : q ∈ S := by
    exact Finset.max'_mem S hSnonempty
  have hqLt : q < m := by
    have := (Finset.mem_filter.mp hqS).1
    simpa [S] using this
  have hqAnti : (H.block q).path.AnticommutesWith u := by
    have := (Finset.mem_filter.mp hqS).2
    simpa [S] using this
  have hmax : ∀ t : Nat, q < t → t < m →
      ¬(H.block t).path.AnticommutesWith u := by
    intro t hqt htm htanti
    have htS : t ∈ S := by
      simp [S, htm, htanti]
    have htLe : t ≤ q := Finset.le_max' S t htS
    omega
  rcases hendpoint q hqLt hqAnti with hqEndpoint | hcurrentEndpoint
  · have hqOne : q + 1 ≤ m := by omega
    by_cases hqLast : q + 1 = m
    · have hqLast' : q = m - 1 := by omega
      have hchain : Set.range (H.block q).finalHole.vertex =
          Set.range D.initialHole.vertex := by
        rw [hqLast']
        exact hbeforeCurrent (by omega)
      exact
        (D.finalDegree_ne_four_of_immediate_earlierEndpoint
          u hcurrentStep (H.block q) (H.pathOrder q)
          hqEndpoint hchain hfour).elim
    · have hqGap : q + 1 < m := by omega
      let K : PathBlockHistory (O := O) (Cprime := Cprime) :=
        { block := fun a => H.block (q + 1 + a)
          pathOrder := fun a => H.pathOrder (q + 1 + a)
          pathCard := fun a => H.pathCard (q + 1 + a)
          chain := fun a => by
            have hindex : q + 1 + (a + 1) = q + 1 + a + 1 := by omega
            rw [hindex]
            exact H.chain (q + 1 + a) }
      let n : Nat := m - q - 2
      have hnIndex : q + 1 + n = m - 1 := by
        dsimp [n]
        omega
      have hafter : Set.range (H.block q).finalHole.vertex =
          Set.range (K.block 0).initialHole.vertex := by
        simpa [K] using H.chain q
      have hbefore : Set.range (K.block n).finalHole.vertex =
          Set.range D.initialHole.vertex := by
        change Set.range (H.block (q + 1 + n)).finalHole.vertex = _
        rw [hnIndex]
        exact hbeforeCurrent (by omega)
      have hcomm : ∀ a : Nat, a ≤ n → (K.block a).path.CommutesWith u := by
        intro a ha
        have hqta : q < q + 1 + a := by omega
        have htm : q + 1 + a < m := by
          dsimp [n] at ha
          omega
        rcases (H.block (q + 1 + a)).path.commutesWith_or_anticommutesWith u with
          hcomm | hanti'
        · simpa [K] using hcomm
        · exact (hmax (q + 1 + a) hqta htm hanti').elim
      exact
        (D.finalDegree_ne_four_of_earlierEndpoint_then_commuting_through
          u hcurrentStep (H.block q) (H.pathOrder q) hqEndpoint
          K hafter n hcomm hbefore hfour).elim
  · exact (hcurrentNotFirst hcurrentEndpoint).elim

/-- The forward numerical implication in Lemma 11(a.ii): after Corollary
12 eliminates the earlier anticommuting paths, degree four in the current
hole forces degree three in the original hole. -/
theorem originalDegree_three_of_currentDegree_four
    (D : ConcretePathDeformation O Cprime)
    (F : D.FullDefinition19Lemma11AData)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPrime : u ∈ Cprime)
    (hanti : D.path.AnticommutesWith u)
    (H : PathBlockHistory (O := O) (Cprime := Cprime))
    (m : Nat)
    (hm : 0 < m)
    (hbeforeCurrent :
      Set.range (H.block (m - 1)).finalHole.vertex =
        Set.range D.initialHole.vertex)
    (hendpoint : D.EarlierAnticommutingEndpointRule H m u)
    (horiginalOutside :
      u ∉ Set.range (H.block 0).initialHole.vertex)
    (horiginalEven : Even (H.block 0).initialHole.card)
    (hfour : D.finalHole.externalDegree u = 4) :
    (H.block 0).initialHole.externalDegree u = 3 := by
  have hlocal :=
    (D.lemma11a_membership_iff_ne_first_and_degree
      F hclaw huPrime hanti).mp ⟨s, hu⟩
  have hno := D.no_earlierAnticommutation_of_currentDegree_four
    u hlocal.2 hlocal.1 hfour H m
    (fun _ => hbeforeCurrent) hendpoint
  let n : Nat := m - 1
  have hnLt : n < m := by
    dsimp [n]
    omega
  have hcomm : ∀ r : Nat, r ≤ n → (H.block r).path.CommutesWith u := by
    intro r hr
    have hrlt : r < m := by omega
    rcases (H.block r).path.commutesWith_or_anticommutesWith u with hcomm | hanti'
    · exact hcomm
    · exact (hno r hrlt hanti').elim
  have hhistory :=
    H.finalDegree_mod_two_eq_initial_of_commutes_through u n hcomm
  have hlink :
      (H.block n).finalHole.externalDegree u =
        D.initialHole.externalDegree u := by
    dsimp [n]
    exact (H.block (m - 1)).finalHole.externalDegree_eq_of_range_eq
      D.initialHole hbeforeCurrent
  have hcurrentThree : D.initialHole.externalDegree u = 3 := by
    omega
  have horiginalOdd :
      (H.block 0).initialHole.externalDegree u % 2 = 1 := by
    rw [← hhistory, hlink, hcurrentThree]
  exact (H.block 0).initialHole.externalDegree_eq_three_of_even_and_odd
    hclaw horiginalOutside horiginalEven horiginalOdd

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
