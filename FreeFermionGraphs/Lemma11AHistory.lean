import FreeFermionGraphs.Lemma11AEndpoints
import FreeFermionGraphs.Lemma11AParity

/-!
# Lemma 11(a): ordered path-block degree history

The original-hole clause of Lemma 11(a.ii) needs degree parity to travel
through the earlier Definition 19 path blocks.  This module gives that
transport for an explicit ordered history of consecutive commuting blocks.
It is deliberately carrier-based, so it does not assume a common indexing
for the intermediate holes.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- Consecutive Definition 19 path blocks, retaining the carrier links
between their intermediate holes. -/
structure PathBlockHistory where
  block : Nat → ConcretePathDeformation O Cprime
  pathOrder : ∀ r : Nat, Definition19GlobalOverlapPathOrder (block r)
  pathCard : ∀ r : Nat,
    (block r).path.card = 2 * (block r).deformation.stepCount
  chain : ∀ r : Nat,
    Set.range (block r).finalHole.vertex =
      Set.range (block (r + 1)).initialHole.vertex

/-- A path-block history whose paths all commute with a fixed vertex. -/
structure CommutingPathBlockHistory (u : V)
    extends PathBlockHistory (O := O) (Cprime := Cprime) where
  commutes : ∀ r : Nat, (block r).path.CommutesWith u

namespace PathBlockHistory

/-- If no path in a history anticommutes with `u`, path-parity dichotomy
turns it into a commuting history. -/
def toCommuting
    (H : PathBlockHistory (O := O) (Cprime := Cprime))
    (u : V)
    (hnotAnti : ∀ r : Nat, ¬(H.block r).path.AnticommutesWith u) :
    CommutingPathBlockHistory (O := O) (Cprime := Cprime) u where
  toPathBlockHistory := H
  commutes r := by
    rcases (H.block r).path.commutesWith_or_anticommutesWith u with hcomm | hanti
    · exact hcomm
    · exact (hnotAnti r hanti).elim

/-- A bounded prefix of commuting blocks preserves degree parity.  Unlike
`toCommuting`, this form is suited to the finite suffix after a maximal
earlier anticommuting path. -/
theorem finalDegree_mod_two_eq_initial_of_commutes_through
    (H : PathBlockHistory (O := O) (Cprime := Cprime))
    (u : V) (n : Nat)
    (hcomm : ∀ r : Nat, r ≤ n → (H.block r).path.CommutesWith u) :
    (H.block n).finalHole.externalDegree u % 2 =
      (H.block 0).initialHole.externalDegree u % 2 := by
  induction n with
  | zero =>
      exact (H.block 0).finalDegree_mod_two_eq_initial_of_commutes
        (H.pathOrder 0) (H.pathCard 0) u (hcomm 0 (by omega))
  | succ n ih =>
      have hcurrent :=
        (H.block (n + 1)).finalDegree_mod_two_eq_initial_of_commutes
          (H.pathOrder (n + 1)) (H.pathCard (n + 1)) u
          (hcomm (n + 1) (by omega))
      have hmiddle :
          (H.block n).finalHole.externalDegree u =
            (H.block (n + 1)).initialHole.externalDegree u :=
        (H.block n).finalHole.externalDegree_eq_of_range_eq
          (H.block (n + 1)).initialHole (H.chain n)
      calc
        (H.block (n + 1)).finalHole.externalDegree u % 2 =
            (H.block (n + 1)).initialHole.externalDegree u % 2 := hcurrent
        _ = (H.block n).finalHole.externalDegree u % 2 := by
            rw [hmiddle]
        _ = (H.block 0).initialHole.externalDegree u % 2 :=
            ih (fun r hr => hcomm r (by omega))

end PathBlockHistory

namespace CommutingPathBlockHistory

/-- Degree parity at the end of any finite commuting history agrees with
the degree parity before its first path block. -/
theorem finalDegree_mod_two_eq_initial
    (H : CommutingPathBlockHistory (O := O) (Cprime := Cprime) u)
    (n : Nat) :
    (H.block n).finalHole.externalDegree u % 2 =
      (H.block 0).initialHole.externalDegree u % 2 := by
  induction n with
  | zero =>
      exact (H.block 0).finalDegree_mod_two_eq_initial_of_commutes
        (H.pathOrder 0) (H.pathCard 0) u (H.commutes 0)
  | succ n ih =>
      have hcurrent :=
        (H.block (n + 1)).finalDegree_mod_two_eq_initial_of_commutes
          (H.pathOrder (n + 1)) (H.pathCard (n + 1)) u
          (H.commutes (n + 1))
      have hmiddle :
          (H.block n).finalHole.externalDegree u =
            (H.block (n + 1)).initialHole.externalDegree u :=
        (H.block n).finalHole.externalDegree_eq_of_range_eq
          (H.block (n + 1)).initialHole (H.chain n)
      calc
        (H.block (n + 1)).finalHole.externalDegree u % 2 =
            (H.block (n + 1)).initialHole.externalDegree u % 2 := hcurrent
        _ = (H.block n).finalHole.externalDegree u % 2 := by
            rw [hmiddle]
        _ = (H.block 0).initialHole.externalDegree u % 2 := ih

end CommutingPathBlockHistory

/-- If a vertex is the first introduced vertex of an earlier path block,
then every later commuting history leaves it with even degree.  This is the
parity contradiction used after Corollary 12 in Lemma 11(a.ii). -/
theorem finalDegree_mod_two_eq_zero_of_endpoint_then_commuting
    (A : ConcretePathDeformation O Cprime)
    (L : Definition19GlobalOverlapPathOrder A)
    (u : V)
    (huEndpoint : u = (A.deformation.step A.firstIndex).introduced)
    (H : CommutingPathBlockHistory (O := O) (Cprime := Cprime) u)
    (hchain : Set.range A.finalHole.vertex =
      Set.range (H.block 0).initialHole.vertex)
    (n : Nat) :
    (H.block n).finalHole.externalDegree u % 2 = 0 := by
  have hendpoint : A.finalHole.externalDegree u = 2 := by
    rw [huEndpoint]
    exact A.firstIntroduced_finalDegree_eq_two L
  have hbridge :
      A.finalHole.externalDegree u =
        (H.block 0).initialHole.externalDegree u :=
    A.finalHole.externalDegree_eq_of_range_eq
      (H.block 0).initialHole hchain
  calc
    (H.block n).finalHole.externalDegree u % 2 =
        (H.block 0).initialHole.externalDegree u % 2 :=
      H.finalDegree_mod_two_eq_initial n
    _ = A.finalHole.externalDegree u % 2 := by rw [hbridge]
    _ = 2 % 2 := by rw [hendpoint]
    _ = 0 := by decide

/-- Bounded-history version of the endpoint parity calculation. -/
theorem finalDegree_mod_two_eq_zero_of_endpoint_then_commuting_through
    (A : ConcretePathDeformation O Cprime)
    (L : Definition19GlobalOverlapPathOrder A)
    (u : V)
    (huEndpoint : u = (A.deformation.step A.firstIndex).introduced)
    (H : PathBlockHistory (O := O) (Cprime := Cprime))
    (hchain : Set.range A.finalHole.vertex =
      Set.range (H.block 0).initialHole.vertex)
    (n : Nat)
    (hcomm : ∀ r : Nat, r ≤ n → (H.block r).path.CommutesWith u) :
    (H.block n).finalHole.externalDegree u % 2 = 0 := by
  have hendpoint : A.finalHole.externalDegree u = 2 := by
    rw [huEndpoint]
    exact A.firstIntroduced_finalDegree_eq_two L
  have hbridge :
      A.finalHole.externalDegree u =
        (H.block 0).initialHole.externalDegree u :=
    A.finalHole.externalDegree_eq_of_range_eq
      (H.block 0).initialHole hchain
  calc
    (H.block n).finalHole.externalDegree u % 2 =
        (H.block 0).initialHole.externalDegree u % 2 :=
      H.finalDegree_mod_two_eq_initial_of_commutes_through u n hcomm
    _ = A.finalHole.externalDegree u % 2 := by rw [hbridge]
    _ = 2 % 2 := by rw [hendpoint]
    _ = 0 := by decide

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
