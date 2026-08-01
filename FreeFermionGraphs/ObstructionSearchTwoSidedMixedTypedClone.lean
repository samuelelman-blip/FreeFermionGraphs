import FreeFermionGraphs.ObstructionSearchTwoSidedMixedLemma11AContext
import FreeFermionGraphs.Lemma11AExact

/-!
# Opposite typed clones under mixed-side reorientation

A manuscript `bd` path block is analysed after exchanging the two original-hole
colours and the two prime-hole colours.  This exchange preserves the opposite
pairing relation from Lemma 11(a.ii): an `.ad` clone relative to the exchanged
family is exactly an `.ad` clone relative to the original family.

This module proves that invariance and uses it to complete the zero-history
(first path block) typed-clone clause for either manuscript component side.  It
does not yet derive the typed clone through a positive mixed-side history or
construct any data from the obstruction-search loop.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

/-- Exchanging both original and prime colour pairs preserves the opposite
pairing type. -/
@[simp] theorem swapSides_hasPairingType_ad_iff
    (O : FixedPairingPathFamily G)
    (prime original : V) :
    O.swapSides.HasPairingType .ad prime original ↔
      O.HasPairingType .ad prime original := by
  constructor
  · intro h
    change
      ((original ∈ O.Cb ∧ prime ∈ O.Cc) ∨
        (original ∈ O.Ca ∧ prime ∈ O.Cd)) at h
    change
      ((original ∈ O.Ca ∧ prime ∈ O.Cd) ∨
        (original ∈ O.Cb ∧ prime ∈ O.Cc))
    exact h.elim Or.inr Or.inl
  · intro h
    change
      ((original ∈ O.Ca ∧ prime ∈ O.Cd) ∨
        (original ∈ O.Cb ∧ prime ∈ O.Cc)) at h
    change
      ((original ∈ O.Cb ∧ prime ∈ O.Cc) ∨
        (original ∈ O.Ca ∧ prime ∈ O.Cd))
    exact h.elim Or.inr Or.inl

/-- A typed clone of opposite pairing is unchanged by exchanging the two
component sides. -/
@[simp] theorem swapSides_hasTypedClone_ad_iff
    (O : FixedPairingPathFamily G)
    (C : IndexedInducedHole G)
    (prime : V) :
    O.swapSides.HasTypedClone .ad C prime ↔
      O.HasTypedClone .ad C prime := by
  constructor
  · rintro ⟨q, hclone, htyped⟩
    exact ⟨q, hclone,
      (O.swapSides_hasPairingType_ad_iff prime (C.vertex q)).mp htyped⟩
  · rintro ⟨q, hclone, htyped⟩
    exact ⟨q, hclone,
      (O.swapSides_hasPairingType_ad_iff prime (C.vertex q)).mpr htyped⟩

namespace DeformationSide

/-- The opposite pairing relation is independent of which Definition 19
component side is used to present the current block. -/
@[simp] theorem family_hasTypedClone_ad_iff
    (side : DeformationSide)
    (O : FixedPairingPathFamily G)
    (C : IndexedInducedHole G)
    (prime : V) :
    (side.family O).HasTypedClone .ad C prime ↔
      O.HasTypedClone .ad C prime := by
  cases side with
  | ac => exact Iff.rfl
  | bd => exact O.swapSides_hasTypedClone_ad_iff C prime

end DeformationSide

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

namespace ConcretePathDeformation

/-- Lemma 11(a.ii), including the oppositely typed clone, when the current
block is the first path in the deformation.  The block may lie on either the
`ac` or `bd` manuscript component side. -/
theorem lemma11aii_of_firstBlock_mixedSide
    (D : ConcretePathDeformation O Cprime)
    (side : DeformationSide)
    (F : (D.reorient side).FullDefinition19Lemma11AData)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPrime : u ∈ Cprime)
    (hanti : D.path.AnticommutesWith u) :
    D.finalHole.externalDegree u = 4 ↔
      D.initialHole.externalDegree u = 3 ∧
        O.HasTypedClone .ad D.initialHole u := by
  have huOriented : u ∈ (D.reorient side).dependentAt s := by
    rw [D.reorient_dependentAt side s]
    exact hu
  have hantiOriented :
      (D.reorient side).path.AnticommutesWith u := by
    simpa using hanti
  have horiented :=
    (D.reorient side).lemma11aii_of_firstBlock
      F hclaw huOriented huPrime hantiOriented
  have hcarrier :
      D.finalHole.externalDegree u = 4 ↔
        D.initialHole.externalDegree u = 3 ∧
          (side.family O).HasTypedClone .ad D.initialHole u := by
    simpa only [D.reorient_finalHole, D.reorient_initialHole] using horiented
  constructor
  · intro hfour
    obtain ⟨hthree, htyped⟩ := hcarrier.mp hfour
    exact ⟨hthree,
      (DeformationSide.family_hasTypedClone_ad_iff
        side O D.initialHole u).mp htyped⟩
  · rintro ⟨hthree, htyped⟩
    apply hcarrier.mpr
    exact ⟨hthree,
      (DeformationSide.family_hasTypedClone_ad_iff
        side O D.initialHole u).mpr htyped⟩

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
