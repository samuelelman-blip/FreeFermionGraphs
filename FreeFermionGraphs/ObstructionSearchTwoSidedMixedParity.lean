import FreeFermionGraphs.ObstructionSearchTwoSidedMixedHistory

/-!
# Parity transport through mixed-side Definition 19 histories

The parity part of Lemma 11(a.ii) depends only on the literal sequence of hole
carriers and on whether each path commutes with the fixed vertex.  It is
therefore independent of whether a block is locally presented on the `ac` or
`bd` side of the fixed-pairing family.

This module lifts the existing carrier-level parity theorems to
`MixedSidePathBlockHistory`.  No obstruction-search execution is constructed,
and no conclusion of Lemma 14 is assumed.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation

namespace MixedSidePathBlockHistory

/-- Reorientation does not change path commutation. -/
@[simp] theorem orientedBlock_commutesWith_iff
    (H : MixedSidePathBlockHistory (O := O) (Cprime := Cprime))
    (r : Nat) (u : V) :
    (H.orientedBlock r).path.CommutesWith u ↔
      (H.carrier.block r).path.CommutesWith u := by
  rfl

/-- Reorientation does not change path anticommutation. -/
@[simp] theorem orientedBlock_anticommutesWith_iff
    (H : MixedSidePathBlockHistory (O := O) (Cprime := Cprime))
    (r : Nat) (u : V) :
    (H.orientedBlock r).path.AnticommutesWith u ↔
      (H.carrier.block r).path.AnticommutesWith u := by
  rfl

/-- Absence of anticommutation in the side-oriented presentation gives
commutation of the literal carrier path. -/
theorem carrier_commutes_of_not_oriented_anticommutes
    (H : MixedSidePathBlockHistory (O := O) (Cprime := Cprime))
    (r : Nat) (u : V)
    (hnot : ¬(H.orientedBlock r).path.AnticommutesWith u) :
    (H.carrier.block r).path.CommutesWith u := by
  rcases (H.carrier.block r).path.commutesWith_or_anticommutesWith u with
    hcomm | hanti
  · exact hcomm
  · apply (hnot ?_).elim
    simpa using hanti

/-- A bounded prefix of side-oriented commuting blocks preserves degree parity
between the first initial hole and the final hole of the last block. -/
theorem finalDegree_mod_two_eq_initial_of_oriented_commutes_through
    (H : MixedSidePathBlockHistory (O := O) (Cprime := Cprime))
    (u : V) (n : Nat)
    (hcomm : ∀ r : Nat, r ≤ n →
      (H.orientedBlock r).path.CommutesWith u) :
    (H.carrier.block n).finalHole.externalDegree u % 2 =
      (H.carrier.block 0).initialHole.externalDegree u % 2 := by
  apply H.carrier.finalDegree_mod_two_eq_initial_of_commutes_through u n
  intro r hr
  simpa using hcomm r hr

/-- The manuscript form in which no block in the bounded prefix
anticommutes with the fixed vertex. -/
theorem finalDegree_mod_two_eq_initial_of_no_oriented_anticommuting_through
    (H : MixedSidePathBlockHistory (O := O) (Cprime := Cprime))
    (u : V) (n : Nat)
    (hnotAnti : ∀ r : Nat, r ≤ n →
      ¬(H.orientedBlock r).path.AnticommutesWith u) :
    (H.carrier.block n).finalHole.externalDegree u % 2 =
      (H.carrier.block 0).initialHole.externalDegree u % 2 := by
  apply H.finalDegree_mod_two_eq_initial_of_oriented_commutes_through u n
  intro r hr
  exact H.carrier_commutes_of_not_oriented_anticommutes
    r u (hnotAnti r hr)

end MixedSidePathBlockHistory

/-- If `u` is the first introduced endpoint of an earlier block, then a later
mixed-side commuting prefix leaves `u` with even final degree. -/
theorem finalDegree_mod_two_eq_zero_of_endpoint_then_mixed_commuting_through
    (A : ConcretePathDeformation O Cprime)
    (L : Definition19GlobalOverlapPathOrder A)
    (u : V)
    (huEndpoint :
      u = (A.deformation.step A.firstIndex).introduced)
    (H : MixedSidePathBlockHistory (O := O) (Cprime := Cprime))
    (hchain : Set.range A.finalHole.vertex =
      Set.range (H.carrier.block 0).initialHole.vertex)
    (n : Nat)
    (hcomm : ∀ r : Nat, r ≤ n →
      (H.orientedBlock r).path.CommutesWith u) :
    (H.carrier.block n).finalHole.externalDegree u % 2 = 0 := by
  apply A.finalDegree_mod_two_eq_zero_of_endpoint_then_commuting_through
    L u huEndpoint H.carrier hchain n
  intro r hr
  simpa using hcomm r hr

/-- Endpoint parity in the exact negative-anticommutation form used in the
finite-history contradiction of Lemma 11(a.ii). -/
theorem finalDegree_mod_two_eq_zero_of_endpoint_then_mixed_no_anticommuting_through
    (A : ConcretePathDeformation O Cprime)
    (L : Definition19GlobalOverlapPathOrder A)
    (u : V)
    (huEndpoint :
      u = (A.deformation.step A.firstIndex).introduced)
    (H : MixedSidePathBlockHistory (O := O) (Cprime := Cprime))
    (hchain : Set.range A.finalHole.vertex =
      Set.range (H.carrier.block 0).initialHole.vertex)
    (n : Nat)
    (hnotAnti : ∀ r : Nat, r ≤ n →
      ¬(H.orientedBlock r).path.AnticommutesWith u) :
    (H.carrier.block n).finalHole.externalDegree u % 2 = 0 := by
  apply A.finalDegree_mod_two_eq_zero_of_endpoint_then_mixed_commuting_through
    L u huEndpoint H hchain n
  intro r hr
  exact H.carrier_commutes_of_not_oriented_anticommutes
    r u (hnotAnti r hr)

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
