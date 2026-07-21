import FreeFermionGraphs.Lemma11AGlobalDegree

/-!
# Lemma 11(a.ii): excluding an earlier anticommuting path

After Corollary 12 identifies an earlier anticommuting vertex with the
first introduction of that path, its final degree is two.  A following
commuting history therefore has even degree parity, contradicting the
degree-three hole immediately before the current dependent replacement.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- An earlier Corollary-12 endpoint followed by commuting path blocks is
incompatible with degree four after the current dependent replacement. -/
theorem finalDegree_ne_four_of_earlierEndpoint_then_commuting
    (D : ConcretePathDeformation O Cprime)
    (u : V)
    (hcurrentStep :
      D.finalHole.externalDegree u =
        D.initialHole.externalDegree u + 1)
    (A : ConcretePathDeformation O Cprime)
    (L : Definition19GlobalOverlapPathOrder A)
    (huEndpoint : u = (A.deformation.step A.firstIndex).introduced)
    (H : CommutingPathBlockHistory (O := O) (Cprime := Cprime) u)
    (hafterA : Set.range A.finalHole.vertex =
      Set.range (H.block 0).initialHole.vertex)
    (n : Nat)
    (hbeforeCurrent : Set.range (H.block n).finalHole.vertex =
      Set.range D.initialHole.vertex) :
    D.finalHole.externalDegree u ≠ 4 := by
  intro hfour
  have hcurrentThree : D.initialHole.externalDegree u = 3 := by
    omega
  have hevenHistory :=
    A.finalDegree_mod_two_eq_zero_of_endpoint_then_commuting
      L u huEndpoint H hafterA n
  have hbridge :
      (H.block n).finalHole.externalDegree u =
        D.initialHole.externalDegree u :=
    (H.block n).finalHole.externalDegree_eq_of_range_eq
      D.initialHole hbeforeCurrent
  rw [hbridge, hcurrentThree] at hevenHistory
  omega

/-- Bounded-history form of the earlier-endpoint contradiction. -/
theorem finalDegree_ne_four_of_earlierEndpoint_then_commuting_through
    (D : ConcretePathDeformation O Cprime)
    (u : V)
    (hcurrentStep :
      D.finalHole.externalDegree u =
        D.initialHole.externalDegree u + 1)
    (A : ConcretePathDeformation O Cprime)
    (L : Definition19GlobalOverlapPathOrder A)
    (huEndpoint : u = (A.deformation.step A.firstIndex).introduced)
    (H : PathBlockHistory (O := O) (Cprime := Cprime))
    (hafterA : Set.range A.finalHole.vertex =
      Set.range (H.block 0).initialHole.vertex)
    (n : Nat)
    (hcomm : ∀ r : Nat, r ≤ n → (H.block r).path.CommutesWith u)
    (hbeforeCurrent : Set.range (H.block n).finalHole.vertex =
      Set.range D.initialHole.vertex) :
    D.finalHole.externalDegree u ≠ 4 := by
  intro hfour
  have hcurrentThree : D.initialHole.externalDegree u = 3 := by
    omega
  have hevenHistory :=
    A.finalDegree_mod_two_eq_zero_of_endpoint_then_commuting_through
      L u huEndpoint H hafterA n hcomm
  have hbridge :
      (H.block n).finalHole.externalDegree u =
        D.initialHole.externalDegree u :=
    (H.block n).finalHole.externalDegree_eq_of_range_eq
      D.initialHole hbeforeCurrent
  rw [hbridge, hcurrentThree] at hevenHistory
  omega

/-- The same contradiction when the earlier anticommuting block is
immediately followed by the current block. -/
theorem finalDegree_ne_four_of_immediate_earlierEndpoint
    (D : ConcretePathDeformation O Cprime)
    (u : V)
    (hcurrentStep :
      D.finalHole.externalDegree u =
        D.initialHole.externalDegree u + 1)
    (A : ConcretePathDeformation O Cprime)
    (L : Definition19GlobalOverlapPathOrder A)
    (huEndpoint : u = (A.deformation.step A.firstIndex).introduced)
    (hchain : Set.range A.finalHole.vertex =
      Set.range D.initialHole.vertex) :
    D.finalHole.externalDegree u ≠ 4 := by
  intro hfour
  have hendpoint : A.finalHole.externalDegree u = 2 := by
    rw [huEndpoint]
    exact A.firstIntroduced_finalDegree_eq_two L
  have hbridge : A.finalHole.externalDegree u =
      D.initialHole.externalDegree u :=
    A.finalHole.externalDegree_eq_of_range_eq D.initialHole hchain
  omega

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
