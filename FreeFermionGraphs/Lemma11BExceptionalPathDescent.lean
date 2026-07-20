import FreeFermionGraphs.Lemma11BPrimeHoleCoordinates

/-!
# Lemma 11(b): path descent in the exceptional six-cycle branch

When the current outside dependent vertex misses the preceding introduced
vertex, the ordinary argument has one exceptional case: the alternating
hole has half-length three.  The two prime-hole neighbors of the preceding
introduction cannot both meet its removed vertex.  A neighbor which misses
that vertex satisfies Definition 20.  Two short claw arguments then place
it in the same fixed-pairing path as the current vertex.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V} {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation

/-- The exceptional half-length-three branch has an immediate Definition 20
predecessor in the same fixed-pairing path component. -/
theorem exceptional_previousDefinition20_sharesPath
    {kPrime : Nat}
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (A : D.AlternatingLabelingSequence 3)
    (P : D.PrimeAlternatingHoleData kPrime)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    (hcolors : O.PrimeCarrierExactlyColored Cprime)
    (horder : Definition19PathOrder M)
    (hopposite : D.BaseOppositeEndpointNonadjacency)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huOutside : u ∉ Set.range D.path.vertex)
    (hnotAnti : ¬D.path.AnticommutesWith u)
    (previous : Fin D.deformation.stepCount)
    (hprevious : previous.val + 1 = s)
    (huNotPreviousIntroduced :
      ¬G.Adj u (D.deformation.step previous).introduced) :
    ∃ v : V,
      D.Definition20DependentAt previous.val v ∧
      O.SharesPath v u := by
  have hs : s < D.deformation.stepCount :=
    D.index_lt_of_mem_dependentAt hu
  let current : Fin D.deformation.stepCount := ⟨s, hs⟩
  have hpc : previous.val + 1 = current.val := by
    simpa [current] using hprevious
  obtain ⟨t, ht, hts, huPreviousRemoved'⟩ :=
    D.adj_previous_removed_of_outside_commuting
      M L hclaw horder hopposite hu huOutside hnotAnti
  have htval : t = previous.val := by omega
  have htprevious :
      (⟨t, ht⟩ : Fin D.deformation.stepCount) = previous := by
    apply Fin.ext
    exact htval
  have huPreviousRemoved :
      G.Adj u
        ((D.deformation.step previous).before.vertex
          (D.deformation.step previous).removedIndex) := by
    rw [← htprevious]
    exact huPreviousRemoved'
  let C : EvenHoleLabeling G 3 := A.labeling previous
  let r : Fin 3 := A.removedAIndex previous
  let hclone := A.cloneAt previous
  let C1 : EvenHoleLabeling G 3 := C.deform hclone
  have hcurrent :
      C1.CloneAt
        (D.deformation.step current).introduced
        (C1.next r) := by
    have h := A.cloneAt current
    rw [A.transport_eq hpc] at h
    rw [A.removed_index_next hpc] at h
    simpa [C, C1, r, hclone] using h
  have hcarrierCurrent :
      C1.carrier =
        Set.range (D.deformation.step current).before.vertex := by
    calc
      C1.carrier = (A.labeling current).carrier := by
        rw [A.transport_eq hpc]
      _ = _ := A.carrier_eq current
  have hCurrentRemoved :
      (D.deformation.step current).before.vertex
          (D.deformation.step current).removedIndex =
        C1.a (C1.next r) := by
    have h := A.removed_eq current
    rw [A.transport_eq hpc] at h
    rw [A.removed_index_next hpc] at h
    simpa [C, C1, r, hclone] using h
  have huStep :
      u ∈ (D.deformation.step current).dependentSet := by
    simpa [current] using
      D.mem_step_dependentSet_of_mem_dependentAt hu
  have humem :=
    (ConcreteDeformationStep.mem_dependentSet
      (D.deformation.step current)).1 huStep
  have huOutsideCurrent :
      u ∉ Set.insert (D.deformation.step current).introduced
        C1.carrier := by
    rw [hcarrierCurrent]
    exact M.outsideHole current huStep
  have huPreviousOriginal : G.Adj u (C.a r) := by
    rw [← A.removed_eq previous]
    exact huPreviousRemoved
  have huNotCurrentOriginal :
      ¬G.Adj u (C1.a (C1.next r)) := by
    rw [← hCurrentRemoved]
    exact humem.2.2.2
  have huNotCommon :
      ¬G.Adj u (C.b (C.next r)) := by
    intro huCommon
    apply huNotPreviousIntroduced
    apply D.adj_previous_introduced_of_adj_common
      L hclaw hs previous hprevious huOutside
    · simpa [C, C1, r, hclone] using hclone.adj_b_next
    · rw [hCurrentRemoved]
      simpa [C1] using C1.adj_a_b (C1.next r)
    · simpa [C1] using huCommon
    · simpa [current] using humem.2.2.2
  have hfour :=
    C.four_previous_neighbors_of_halfLength_three_of_not_common
      hclaw hclone hcurrent huOutsideCurrent
      huPreviousOriginal humem.2.1
      huNotCurrentOriginal (by simpa [C1] using huNotCommon)
  have huB0 : G.Adj u (C.b r) := hfour.2.1
  have huPrime : u ∈ Cprime := humem.1
  have huCd : u ∈ O.Cd := M.dependent_mem_cd hu
  obtain ⟨qu, huEqB⟩ :=
    P.eq_b_of_mem_prime_and_adj_introduced current huPrime humem.2.1
  let rp : Fin kPrime := P.introducedIndex previous
  let x : V := P.labeling.b rp
  let y : V := P.labeling.b (P.labeling.next rp)
  have hxPrime : x ∈ Cprime :=
    P.mem_prime_of_mem_carrier
      (by simpa [x, rp] using P.labeling.b_mem_carrier rp)
  have hyPrime : y ∈ Cprime :=
    P.mem_prime_of_mem_carrier
      (by simpa [y, rp] using
        P.labeling.b_mem_carrier (P.labeling.next rp))
  have hxIntroduced :
      G.Adj x (D.deformation.step previous).introduced := by
    rw [← P.introduced_eq previous]
    exact (P.labeling.adj_a_b rp).symm
  have hyIntroduced :
      G.Adj y (D.deformation.step previous).introduced := by
    rw [← P.introduced_eq previous]
    exact (P.labeling.adj_a_b_next rp).symm
  have hxCd : x ∈ O.Cd := by
    rcases (M.stepGeometry previous).prime_subset hxPrime with hxCc | hxCd
    · exact ((M.stepGeometry previous).base.cc_independent
        hxCc (M.stepGeometry previous).base.introduced_cc
        hxIntroduced).elim
    · exact hxCd
  have hyCd : y ∈ O.Cd := by
    rcases (M.stepGeometry previous).prime_subset hyPrime with hyCc | hyCd
    · exact ((M.stepGeometry previous).base.cc_independent
        hyCc (M.stepGeometry previous).base.introduced_cc
        hyIntroduced).elim
    · exact hyCd
  have hxy : x ≠ y := by
    exact fun h => P.labeling.b_ne_next rp h.symm
  have hxyNot : ¬G.Adj x y := by
    exact P.labeling.adj_bb rp (P.labeling.next rp)
  have hxuNot : ¬G.Adj x u := by
    rw [huEqB]
    exact P.labeling.adj_bb rp qu
  have hyuNot : ¬G.Adj y u := by
    rw [huEqB]
    exact P.labeling.adj_bb (P.labeling.next rp) qu
  have hxNeU : x ≠ u := by
    intro h
    apply huNotPreviousIntroduced
    rw [← h]
    exact hxIntroduced
  have hyNeU : y ≠ u := by
    intro h
    apply huNotPreviousIntroduced
    rw [← h]
    exact hyIntroduced
  have honeMisses :
      ¬G.Adj x
          ((D.deformation.step previous).before.vertex
            (D.deformation.step previous).removedIndex) ∨
        ¬G.Adj y
          ((D.deformation.step previous).before.vertex
            (D.deformation.step previous).removedIndex) := by
    by_cases hxRemoved :
        G.Adj x
          ((D.deformation.step previous).before.vertex
            (D.deformation.step previous).removedIndex)
    · by_cases hyRemoved :
          G.Adj y
            ((D.deformation.step previous).before.vertex
              (D.deformation.step previous).removedIndex)
      · exfalso
        rcases hclaw huPreviousRemoved.symm
            hxRemoved.symm hyRemoved.symm
            hxNeU.symm hyNeU.symm hxy with
          hux | huy | hxy'
        · exact hxuNot hux.symm
        · exact hyuNot huy.symm
        · exact hxyNot hxy'
      · exact Or.inr hyRemoved
    · exact Or.inl hxRemoved
  obtain ⟨v, z, hvPrime, hzPrime, hvCd, hzCd,
      hvIntroduced, hzIntroduced, hvNotRemoved,
      hvNeZ, hvzNot, hzuNot⟩ :
      ∃ v z : V,
        v ∈ Cprime ∧ z ∈ Cprime ∧
        v ∈ O.Cd ∧ z ∈ O.Cd ∧
        G.Adj v (D.deformation.step previous).introduced ∧
        G.Adj z (D.deformation.step previous).introduced ∧
        ¬G.Adj v
          ((D.deformation.step previous).before.vertex
            (D.deformation.step previous).removedIndex) ∧
        v ≠ z ∧ ¬G.Adj v z ∧ ¬G.Adj z u := by
    rcases honeMisses with hxMisses | hyMisses
    · exact ⟨x, y, hxPrime, hyPrime, hxCd, hyCd,
        hxIntroduced, hyIntroduced, hxMisses,
        hxy, hxyNot, hyuNot⟩
    · exact ⟨y, x, hyPrime, hxPrime, hyCd, hxCd,
        hyIntroduced, hxIntroduced, hyMisses,
        hxy.symm, (fun h => hxyNot h.symm), hxuNot⟩
  have hvNotCa : v ∉ O.Ca :=
    (ExactlyOneOfFour.not_mem_first_three_of_mem_fourth
      (hcolors hvPrime) hvCd).1
  have hvNotCb : v ∉ O.Cb :=
    (ExactlyOneOfFour.not_mem_first_three_of_mem_fourth
      (hcolors hvPrime) hvCd).2.1
  have hvNotCc : v ∉ O.Cc :=
    (ExactlyOneOfFour.not_mem_first_three_of_mem_fourth
      (hcolors hvPrime) hvCd).2.2
  have hzNotCa : z ∉ O.Ca :=
    (ExactlyOneOfFour.not_mem_first_three_of_mem_fourth
      (hcolors hzPrime) hzCd).1
  have hzNotCb : z ∉ O.Cb :=
    (ExactlyOneOfFour.not_mem_first_three_of_mem_fourth
      (hcolors hzPrime) hzCd).2.1
  have hvNeRemoved :
      v ≠
        (D.deformation.step previous).before.vertex
          (D.deformation.step previous).removedIndex := by
    intro h
    apply hvNotCa
    rw [h]
    exact (M.stepGeometry previous).removed_ca
  have hvDefinition20 :
      D.Definition20DependentAt previous.val v := by
    exact ⟨previous.isLt, hvPrime, hvIntroduced,
      hvNeRemoved, hvNotRemoved⟩
  have hb0Before :
      C.b r ∈ Set.range
        (D.deformation.step previous).before.vertex := by
    rw [← A.carrier_eq previous]
    exact C.b_mem_carrier r
  have hb1Before :
      C.b (C.next r) ∈ Set.range
        (D.deformation.step previous).before.vertex := by
    rw [← A.carrier_eq previous]
    exact C.b_mem_carrier (C.next r)
  have hb0Cb : C.b r ∈ O.Cb := by
    rcases (M.stepGeometry previous).before_subset hb0Before with
      hb0Ca | hb0Cb
    · exact ((M.stepGeometry previous).ca_independent
        (M.stepGeometry previous).removed_ca hb0Ca
        (by
          rw [A.removed_eq previous]
          exact C.adj_a_b r)).elim
    · exact hb0Cb
  have hb1Cb : C.b (C.next r) ∈ O.Cb := by
    rcases (M.stepGeometry previous).before_subset hb1Before with
      hb1Ca | hb1Cb
    · exact ((M.stepGeometry previous).ca_independent
        (M.stepGeometry previous).removed_ca hb1Ca
        (by
          rw [A.removed_eq previous]
          exact C.adj_a_b_next r)).elim
    · exact hb1Cb
  by_cases hvB0 : G.Adj v (C.b r)
  · exact ⟨v, hvDefinition20,
      M.sharesPath_of_common_cb hvCd huCd hb0Cb hvB0 huB0⟩
  · have hvOutsidePrevious :
        v ∉ Set.insert (D.deformation.step previous).introduced
          C.carrier := by
      intro hvInsert
      rcases Set.mem_insert_iff.1 hvInsert with hvEq | hvCarrier
      · apply hvNotCc
        rw [hvEq]
        exact (M.stepGeometry previous).base.introduced_cc
      · have hvBefore :
            v ∈ Set.range
              (D.deformation.step previous).before.vertex := by
          rw [← A.carrier_eq previous]
          exact hvCarrier
        rcases (M.stepGeometry previous).before_subset hvBefore with
          hvCa | hvCb
        · exact hvNotCa hvCa
        · exact hvNotCb hvCb
    have hvExact :
        (G.Adj v (D.deformation.step previous).introduced ∧
          ¬G.Adj v (C.a r)) ∨
        (¬G.Adj v (D.deformation.step previous).introduced ∧
          G.Adj v (C.a r)) := by
      left
      exact ⟨hvIntroduced, by
        simpa [C, r, A.removed_eq previous] using hvNotRemoved⟩
    have hvSide :=
      hclone.dependent_forces_side
        hclaw (by simpa [C, hclone] using hvOutsidePrevious)
        (by simpa [C, r, hclone] using hvExact)
    have hvB1 : G.Adj v (C.b (C.next r)) := by
      rcases hvSide with hleft | hright
      · exact (hvB0 hleft.1).elim
      · exact hright.1
    have hzB0 : G.Adj z (C.b r) := by
      have hzNeB0 : z ≠ C.b r := by
        intro h
        apply hzNotCb
        rw [h]
        exact hb0Cb
      have hvNeB0 : v ≠ C.b r := by
        intro h
        apply hvNotCb
        rw [h]
        exact hb0Cb
      rcases hclaw hvIntroduced.symm hzIntroduced.symm
          hclone.adj_b
          hvNeZ hvNeB0 hzNeB0 with
        hvz | hvb | hzb
      · exact (hvzNot hvz).elim
      · exact (hvB0 hvb).elim
      · exact hzb
    by_cases hzRemoved :
        G.Adj z
          ((D.deformation.step previous).before.vertex
            (D.deformation.step previous).removedIndex)
    · have hzB1 : G.Adj z (C.b (C.next r)) := by
        have hzNeU : z ≠ u := by
          intro h
          apply huNotPreviousIntroduced
          rw [← h]
          exact hzIntroduced
        have hzNeB1 : z ≠ C.b (C.next r) := by
          intro h
          apply hzNotCb
          rw [h]
          exact hb1Cb
        have huNotCb : u ∉ O.Cb :=
          (ExactlyOneOfFour.not_mem_first_three_of_mem_fourth
            (hcolors huPrime) huCd).2.1
        have huNeB1 : u ≠ C.b (C.next r) := by
          intro h
          apply huNotCb
          rw [h]
          exact hb1Cb
        have hremovedB1 :
            G.Adj
              ((D.deformation.step previous).before.vertex
                (D.deformation.step previous).removedIndex)
              (C.b (C.next r)) := by
          rw [A.removed_eq previous]
          exact C.adj_a_b_next r
        rcases hclaw hzRemoved.symm huPreviousRemoved.symm
            hremovedB1 hzNeU hzNeB1 huNeB1 with
          hzu | hzb | hub
        · exact (hzuNot hzu).elim
        · exact hzb
        · exact (huNotCommon hub).elim
      have hvzShares : O.SharesPath v z :=
        M.sharesPath_of_common_cb hvCd hzCd hb1Cb hvB1 hzB1
      have hzuShares : O.SharesPath z u :=
        M.sharesPath_of_common_cb hzCd huCd hb0Cb hzB0 huB0
      have hzUnique : O.AtMostOneContainingPath z :=
        O.atMostOneContainingPath_of_exactlyOne (hcolors hzPrime)
      exact ⟨v, hvDefinition20,
        O.sharesPath_trans_of_atMostOne hzUnique
          hvzShares hzuShares⟩
    · have hzNeRemoved :
          z ≠
            (D.deformation.step previous).before.vertex
              (D.deformation.step previous).removedIndex := by
        intro h
        apply hzNotCa
        rw [h]
        exact (M.stepGeometry previous).removed_ca
      have hzDefinition20 :
          D.Definition20DependentAt previous.val z :=
        ⟨previous.isLt, hzPrime, hzIntroduced,
          hzNeRemoved, hzRemoved⟩
      exact ⟨z, hzDefinition20,
        M.sharesPath_of_common_cb hzCd huCd hb0Cb hzB0 huB0⟩

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
