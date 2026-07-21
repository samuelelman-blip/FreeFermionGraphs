import FreeFermionGraphs.Lemma11ACorollary12
import FreeFermionGraphs.Lemma11AHistory
import FreeFermionGraphs.Lemma11AOddDegree

/-!
# Lemma 11(a.ii): original-hole degree transport

This is the numerical core of the global clause of Lemma 11(a.ii).  Once
all earlier paths commute with `u`, carrier-linked path blocks preserve
degree parity.  The current dependent replacement changes degree by one,
so degree four in the current hole is equivalent to degree three in the
original hole.

The remaining use of Corollary 12 is to rule out an earlier anticommuting
path and thereby establish the `hnoEarlierAnticommutation` hypothesis in
the concrete Definition 19 history.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- The degree-four/original-degree-three equivalence of Lemma 11(a.ii),
after the earlier Definition 19 blocks have been represented as a carrier
linked history with no anticommuting path for `u`. -/
theorem finalDegree_four_iff_originalDegree_three_of_noEarlierAnticommutation
    (D : ConcretePathDeformation O Cprime)
    (F : D.FullDefinition19Lemma11AData)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPrime : u ∈ Cprime)
    (hanti : D.path.AnticommutesWith u)
    (H : PathBlockHistory (O := O) (Cprime := Cprime))
    (n : Nat)
    (hcurrentInitial :
      Set.range (H.block n).finalHole.vertex =
        Set.range D.initialHole.vertex)
    (hnoEarlierAnticommutation : ∀ r : Nat,
      ¬(H.block r).path.AnticommutesWith u)
    (horiginalOutside :
      u ∉ Set.range (H.block 0).initialHole.vertex)
    (hcurrentInitialOutside : u ∉ Set.range D.initialHole.vertex)
    (horiginalEven : Even (H.block 0).initialHole.card)
    (hcurrentInitialEven : Even D.initialHole.card) :
    D.finalHole.externalDegree u = 4 ↔
      (H.block 0).initialHole.externalDegree u = 3 := by
  have hlocal :=
    (D.lemma11a_membership_iff_ne_first_and_degree
      F hclaw huPrime hanti).mp ⟨s, hu⟩
  have hstep :
      D.finalHole.externalDegree u =
        D.initialHole.externalDegree u + 1 := hlocal.2
  let HC : CommutingPathBlockHistory (O := O) (Cprime := Cprime) u :=
    H.toCommuting u hnoEarlierAnticommutation
  have hhistory := HC.finalDegree_mod_two_eq_initial n
  have hhistory' :
      (H.block n).finalHole.externalDegree u % 2 =
        (H.block 0).initialHole.externalDegree u % 2 := by
    simpa [HC, PathBlockHistory.toCommuting] using hhistory
  have hlink :
      (H.block n).finalHole.externalDegree u =
        D.initialHole.externalDegree u :=
    (H.block n).finalHole.externalDegree_eq_of_range_eq
      D.initialHole hcurrentInitial
  constructor
  · intro hfour
    have hcurrentThree : D.initialHole.externalDegree u = 3 := by
      omega
    have hhistoryThree : (H.block n).finalHole.externalDegree u = 3 := by
      rw [hlink]
      exact hcurrentThree
    have horiginalOdd :
        (H.block 0).initialHole.externalDegree u % 2 = 1 := by
      rw [← hhistory']
      omega
    exact (H.block 0).initialHole.externalDegree_eq_three_of_even_and_odd
      hclaw horiginalOutside horiginalEven horiginalOdd
  · intro horiginalThree
    have hcurrentOdd : D.initialHole.externalDegree u % 2 = 1 := by
      rw [← hlink, hhistory', horiginalThree]
    have hcurrentThree : D.initialHole.externalDegree u = 3 :=
      D.initialHole.externalDegree_eq_three_of_even_and_odd
        hclaw hcurrentInitialOutside hcurrentInitialEven hcurrentOdd
    omega

/-- Bounded-history form of the degree-four/original-degree-three
equivalence.  Only the path blocks preceding the current block are relevant,
so this version does not assume anything about an arbitrary infinite tail of
the history representation. -/
theorem finalDegree_four_iff_originalDegree_three_of_noEarlierAnticommutation_through
    (D : ConcretePathDeformation O Cprime)
    (F : D.FullDefinition19Lemma11AData)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPrime : u ∈ Cprime)
    (hanti : D.path.AnticommutesWith u)
    (H : PathBlockHistory (O := O) (Cprime := Cprime))
    (n : Nat)
    (hcurrentInitial :
      Set.range (H.block n).finalHole.vertex =
        Set.range D.initialHole.vertex)
    (hnoEarlierAnticommutation : ∀ r : Nat, r ≤ n →
      ¬(H.block r).path.AnticommutesWith u)
    (horiginalOutside :
      u ∉ Set.range (H.block 0).initialHole.vertex)
    (hcurrentInitialOutside : u ∉ Set.range D.initialHole.vertex)
    (horiginalEven : Even (H.block 0).initialHole.card)
    (hcurrentInitialEven : Even D.initialHole.card) :
    D.finalHole.externalDegree u = 4 ↔
      (H.block 0).initialHole.externalDegree u = 3 := by
  have hlocal :=
    (D.lemma11a_membership_iff_ne_first_and_degree
      F hclaw huPrime hanti).mp ⟨s, hu⟩
  have hstep :
      D.finalHole.externalDegree u =
        D.initialHole.externalDegree u + 1 := hlocal.2
  have hcomm : ∀ r : Nat, r ≤ n → (H.block r).path.CommutesWith u := by
    intro r hr
    rcases (H.block r).path.commutesWith_or_anticommutesWith u with hcomm | hanti'
    · exact hcomm
    · exact (hnoEarlierAnticommutation r hr hanti').elim
  have hhistory := H.finalDegree_mod_two_eq_initial_of_commutes_through
    u n hcomm
  have hlink :
      (H.block n).finalHole.externalDegree u =
        D.initialHole.externalDegree u :=
    (H.block n).finalHole.externalDegree_eq_of_range_eq
      D.initialHole hcurrentInitial
  constructor
  · intro hfour
    have hcurrentThree : D.initialHole.externalDegree u = 3 := by
      omega
    have horiginalOdd :
        (H.block 0).initialHole.externalDegree u % 2 = 1 := by
      rw [← hhistory, hlink, hcurrentThree]
    exact (H.block 0).initialHole.externalDegree_eq_three_of_even_and_odd
      hclaw horiginalOutside horiginalEven horiginalOdd
  · intro horiginalThree
    have hcurrentOdd : D.initialHole.externalDegree u % 2 = 1 := by
      rw [← hlink, hhistory, horiginalThree]
    have hcurrentThree : D.initialHole.externalDegree u = 3 :=
      D.initialHole.externalDegree_eq_three_of_even_and_odd
        hclaw hcurrentInitialOutside hcurrentInitialEven hcurrentOdd
    omega

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
