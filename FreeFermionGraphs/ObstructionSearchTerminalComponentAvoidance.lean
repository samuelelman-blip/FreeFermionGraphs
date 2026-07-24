import FreeFermionGraphs.ObstructionSearchTerminalHistoryPersistence

/-!
# Lemma 14(iv): same-family terminal component disjointness

A vertex may belong to one original-hole colour class and one prime-hole
colour class simultaneously.  Corollary 9 of the manuscript explicitly allows
such overlap vertices to lie on one `ac` path and one `bd` path.  Therefore a
`C_b` vertex of a terminal `bd` component cannot in general be declared absent
from every distinct fixed-pairing path.

The faithful component consequence is narrower: two distinct `bd` components
are disjoint.  This module records that statement and the finite-history notion
that a particular component does not occur among the represented blocks.  It
does not derive avoidance of all paths or terminal-hole persistence.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace FixedPairingPathFamily

/-- A vertex of one `bd` component cannot lie on a distinct `bd` component. -/
theorem not_mem_bdPath_of_mem_bdPath_of_ne
    (O : FixedPairingPathFamily G)
    {P Q : Set V} {x : V}
    (hP : P ∈ O.bdPaths)
    (hQ : Q ∈ O.bdPaths)
    (hxP : x ∈ P)
    (hne : Q ≠ P) :
    x ∉ Q := by
  intro hxQ
  have hEq : P = Q :=
    O.eq_of_mem_bdPaths hP hQ hxP hxQ
  exact hne hEq.symm

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}
  {D : ConcretePathDeformation O Cprime}

namespace Lemma11AHistoryContext

/-- The component `P` is distinct from the current path and, in the positive
history case, from every represented prior path.  This says nothing about
whether a vertex of `P` may also occur on a path of the opposite component
family. -/
def AvoidsComponent
    (X : D.Lemma11AHistoryContext) (P : Set V) : Prop :=
  match X with
  | .first _ => Set.range D.path.vertex ≠ P
  | .later H =>
      (∀ r : Nat, r < H.priorCount →
        Set.range (H.history.block r).path.vertex ≠ P) ∧
      Set.range D.path.vertex ≠ P

end Lemma11AHistoryContext

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
