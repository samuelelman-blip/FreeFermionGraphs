import FreeFermionGraphs.Lemma11BOrdinaryTwoStepConfiguration

/-!
# Lemma 11(b): path invariant for the ordinary two-step configuration

The residual candidate is a C'_d-vertex sharing a C_b-neighbor
with the current dependent vertex. The fixed-pairing edge coverage places
both vertices in one bd-path component; exact coloring makes that
component unique for each of them.

This discharges the path-component invariant needed by the recursive
two-step construction.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V} {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation

/-- A residual ordinary two-step candidate lies with the current dependent
vertex in one fixed-pairing path, uniquely for both endpoints. -/
theorem ordinaryTwoStepConfiguration_sameUniquePath
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (hcolors : O.PrimeCarrierExactlyColored Cprime)
    {s t : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (hconfig : D.OrdinaryTwoStepConfiguration t u) :
    ∃ u' w : V, ∃ Q : Set V,
      u' ∈ Cprime ∧
      u' ∈ O.Cd ∧
      G.Adj u' w ∧
      w ∈ O.Cb ∧
      G.Adj u w ∧
      Q ∈ O.paths ∧
      u ∈ Q ∧
      u' ∈ Q ∧
      O.IsUniqueContainingPath u Q ∧
      O.IsUniqueContainingPath u' Q := by
  obtain ⟨_ht, u', w, hu'Prime, hu'Cd, _hu'Introduced,
      _hu'NeU, _hu'NotU, _hu'Removed, hwCb, hu'w, huw⟩ :=
    hconfig
  have huCd : u ∈ O.Cd :=
    M.dependent_mem_cd hu
  obtain ⟨P, hP, hu'P, hwP⟩ :=
    M.edgeCoverage hu'Cd hwCb hu'w
  obtain ⟨Q, hQ, huQ, hwQ⟩ :=
    M.edgeCoverage huCd hwCb huw
  have hPQ : P = Q :=
    O.eq_of_mem_bdPaths hP hQ hwP hwQ
  subst Q
  have huUnique :
      O.IsUniqueContainingPath u P :=
    O.isUniqueContainingPath_of_pairingSideSeparated
      (Or.inr hP) huQ
      (O.pairingSideSeparated_of_exactlyOne
        (M.dependent_exactlyOne hcolors hu))
  have hu'Unique :
      O.IsUniqueContainingPath u' P :=
    O.isUniqueContainingPath_of_pairingSideSeparated
      (Or.inr hP) hu'P
      (O.pairingSideSeparated_of_exactlyOne
        (hcolors hu'Prime))
  exact ⟨u', w, P, hu'Prime, hu'Cd, hu'w, hwCb,
    huw, Or.inr hP, huQ, hu'P, huUnique, hu'Unique⟩

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
