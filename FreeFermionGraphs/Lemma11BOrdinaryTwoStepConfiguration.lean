import FreeFermionGraphs.Lemma11BThreeStepCoordinates

/-!
# Lemma 11(b): the residual ordinary two-step configuration

After the one-step branch is discharged, the only ordinary outside-path
case left by the paper has an additional prime-hole neighbor adjacent to the
preceding removed vertex.  This module names that exact configuration and
proves the dichotomy between it and an immediate Definition 20 predecessor.

The subsequent proof can therefore focus solely on eliminating this
configuration by the paper's two-step argument.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V} {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation

/-- The remaining ordinary obstruction after the immediate predecessor case.
The candidate is a prime (C'_d)-vertex adjacent to both the preceding
introduced and removed vertices, and it shares a named (C_b)-neighbor
with the current dependent vertex. -/
def OrdinaryTwoStepConfiguration
    (D : ConcretePathDeformation O Cprime)
    (t : Nat) (u : V) : Prop :=
  ∃ ht : t < D.deformation.stepCount, ∃ u' w : V,
    u' ∈ Cprime ∧
    u' ∈ O.Cd ∧
    G.Adj u' (D.deformation.step ⟨t, ht⟩).introduced ∧
    u' ≠ u ∧
    ¬G.Adj u' u ∧
    (u' =
        (D.deformation.step ⟨t, ht⟩).before.vertex
          (D.deformation.step ⟨t, ht⟩).removedIndex ∨
      G.Adj u'
        ((D.deformation.step ⟨t, ht⟩).before.vertex
          (D.deformation.step ⟨t, ht⟩).removedIndex)) ∧
    w ∈ O.Cb ∧
    G.Adj u' w ∧
    G.Adj u w

/-- For an ordinary outside dependent vertex, either the extra prime-hole
neighbor is already Definition 20 dependent at the preceding step, or the
precise residual two-step configuration occurs. -/
theorem ordinary_previousDefinition20_or_twoStepConfiguration
    {k kPrime : Nat}
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (A : D.AlternatingLabelingSequence k)
    (P : D.PrimeAlternatingHoleData kPrime)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    (hcolors : O.PrimeCarrierOverlapColored Cprime)
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
    (∃ u' w : V,
      D.Definition20DependentAt t u' ∧
      w ∈ O.Cb ∧
      G.Adj u' w ∧
      G.Adj u w) ∨
      D.OrdinaryTwoStepConfiguration t u := by
  obtain ⟨u', w, hu'Prime, hu'Cd, hu'Introduced,
      hu'NeU, hu'NotU, hwCb, hu'w, huw, hbranch⟩ :=
    D.ordinary_prime_neighbor_with_commonB_or_previousDefinition20
      M A P L hclaw hcolors horder hopposite
      hu huOutside hnotAnti ht hts huPreviousIntroduced
  rcases hbranch with hu'Removed | hu'Definition20
  · right
    exact ⟨ht, u', w, hu'Prime, hu'Cd, hu'Introduced,
      hu'NeU, hu'NotU, hu'Removed, hwCb, hu'w, huw⟩
  · left
    exact ⟨u', w, hu'Definition20, hwCb, hu'w, huw⟩

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
