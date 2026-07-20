import FreeFermionGraphs.Lemma11BOrdinaryTwoStepPath

/-!
# Lemma 11(b): coordinates on the fixed prime hole

The recursive part of Lemma 11(b) repeatedly uses the following elementary
fact about the unchanged prime hole.  A prime vertex adjacent to one of the
introduced `a`-vertices is one of the two `b`-vertices beside it.  This file
records that fact separately so that the ordinary and exceptional descent
branches can use the prime-hole bipartition directly.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V} {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation

/-- A displayed `C_b` neighbor is enough to place two `C'_d` vertices in
the same `bdPaths` component.  Keeping the side in the conclusion makes
the recursive invariant transitive even when a path vertex lies in an
overlap of the two holes. -/
theorem MechanicalData.sharesBDPath_of_common_cb
    {D : ConcretePathDeformation O Cprime}
    (M : D.MechanicalData)
    {x y w : V}
    (hxCd : x ∈ O.Cd)
    (hyCd : y ∈ O.Cd)
    (hwCb : w ∈ O.Cb)
    (hxw : G.Adj x w)
    (hyw : G.Adj y w) :
    O.SharesBDPath x y := by
  obtain ⟨P, hP, hxP, hwP⟩ := M.edgeCoverage hxCd hwCb hxw
  obtain ⟨Q, hQ, hyQ, hwQ⟩ := M.edgeCoverage hyCd hwCb hyw
  have hPQ : P = Q :=
    O.eq_of_mem_bdPaths hP hQ hwP hwQ
  subst Q
  exact ⟨P, hP, hxP, hyQ⟩

/-- Untyped compatibility wrapper for arguments that only need membership
in some fixed-pairing component. -/
theorem MechanicalData.sharesPath_of_common_cb
    {D : ConcretePathDeformation O Cprime}
    (M : D.MechanicalData)
    {x y w : V}
    (hxCd : x ∈ O.Cd)
    (hyCd : y ∈ O.Cd)
    (hwCb : w ∈ O.Cb)
    (hxw : G.Adj x w)
    (hyw : G.Adj y w) :
    O.SharesPath x y :=
  O.sharesPath_of_sharesBDPath
    (M.sharesBDPath_of_common_cb hxCd hyCd hwCb hxw hyw)

/-- On an alternating hole of half-length greater than two, if `q` and
`q'` are the two `b`-neighbors of `a r` and `a c` is the other
`a`-neighbor of `b q`, then `a c` is not adjacent to `b q'`. -/
theorem other_b_not_adjacent_other_a
    {k : Nat} (C : EvenHoleLabeling G k)
    (hk : 2 < k)
    {r c q q' : Fin k}
    (hrc : r ≠ c)
    (hqAtR : q = r ∨ q = C.next r)
    (hq'AtR : q' = r ∨ q' = C.next r)
    (hqq' : q' ≠ q)
    (hqAtC : q = c ∨ q = C.next c) :
    ¬(q' = c ∨ q' = C.next c) := by
  have hnextInjective : Function.Injective C.next := by
    intro i j hij
    have h := congrArg C.prev hij
    simpa [C.prev_next] using h
  rcases hqAtR with hqr | hqr
  · subst q
    rcases hq'AtR with hq'r | hq'r
    · exact (hqq' hq'r).elim
    · subst q'
      rcases hqAtC with hrc' | hrc'
      · exact (hrc hrc').elim
      · intro hAdj
        rcases hAdj with hAdj | hAdj
        · apply C.next_next_ne hk c
          calc
            C.next (C.next c) = C.next r :=
              congrArg C.next hrc'.symm
            _ = c := hAdj
        · exact (hrc (hnextInjective hAdj)).elim
  · subst q
    rcases hq'AtR with hq'r | hq'r
    · subst q'
      rcases hqAtC with hrc' | hrc'
      · intro hAdj
        rcases hAdj with hAdj | hAdj
        · exact (hrc hAdj).elim
        · apply C.next_next_ne hk r
          calc
            C.next (C.next r) = C.next c :=
              congrArg C.next hrc'
            _ = r := hAdj.symm
      · exact (hrc (hnextInjective hrc')).elim
    · exact (hqq' hq'r).elim

namespace PrimeAlternatingHoleData

variable {D : ConcretePathDeformation O Cprime} {kPrime : Nat}

/-- A prime-hole vertex adjacent to an introduced `a`-vertex lies in the
`b`-part of the fixed prime-hole labeling. -/
theorem eq_b_of_mem_prime_and_adj_introduced
    (P : D.PrimeAlternatingHoleData kPrime)
    (i : Fin D.deformation.stepCount)
    {x : V}
    (hxPrime : x ∈ Cprime)
    (hxIntroduced :
      G.Adj x (D.deformation.step i).introduced) :
    ∃ q : Fin kPrime, x = P.labeling.b q := by
  have hxCarrier : x ∈ P.labeling.carrier :=
    P.mem_carrier_of_mem_prime hxPrime
  rcases hxCarrier with ⟨q, hq⟩ | ⟨q, hq⟩
  · subst x
    have haa :
        G.Adj (P.labeling.a q)
          (P.labeling.a (P.introducedIndex i)) := by
      rw [P.introduced_eq i]
      exact hxIntroduced
    exact (P.labeling.adj_aa q (P.introducedIndex i) haa).elim
  · exact ⟨q, hq.symm⟩

/-- Three consecutive introduced vertices occupy three distinct prime-hole
`a`-coordinates, so the prime half-length is greater than two. -/
theorem two_lt_halfLength_of_three_consecutive_introductions
    (P : D.PrimeAlternatingHoleData kPrime)
    (L : Definition19GlobalOverlapPathOrder D)
    {earlier previous current : Fin D.deformation.stepCount}
    (hep : earlier.val + 1 = previous.val)
    (hpc : previous.val + 1 = current.val) :
    2 < kPrime := by
  have hepIntro :
      (D.deformation.step earlier).introduced ≠
        (D.deformation.step previous).introduced :=
    D.introduced_ne_later_introduced L earlier previous (by omega)
  have hpcIntro :
      (D.deformation.step previous).introduced ≠
        (D.deformation.step current).introduced :=
    D.introduced_ne_later_introduced L previous current (by omega)
  have hecIntro :
      (D.deformation.step earlier).introduced ≠
        (D.deformation.step current).introduced :=
    D.introduced_ne_later_introduced L earlier current (by omega)
  have hepIndex :
      P.introducedIndex earlier ≠ P.introducedIndex previous := by
    intro h
    apply hepIntro
    rw [← P.introduced_eq earlier, ← P.introduced_eq previous, h]
  have hpcIndex :
      P.introducedIndex previous ≠ P.introducedIndex current := by
    intro h
    apply hpcIntro
    rw [← P.introduced_eq previous, ← P.introduced_eq current, h]
  have hecIndex :
      P.introducedIndex earlier ≠ P.introducedIndex current := by
    intro h
    apply hecIntro
    rw [← P.introduced_eq earlier, ← P.introduced_eq current, h]
  have hepVal :
      (P.introducedIndex earlier).val ≠
        (P.introducedIndex previous).val := by
    intro h
    exact hepIndex (Fin.ext h)
  have hpcVal :
      (P.introducedIndex previous).val ≠
        (P.introducedIndex current).val := by
    intro h
    exact hpcIndex (Fin.ext h)
  have hecVal :
      (P.introducedIndex earlier).val ≠
        (P.introducedIndex current).val := by
    intro h
    exact hecIndex (Fin.ext h)
  omega

end PrimeAlternatingHoleData

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
