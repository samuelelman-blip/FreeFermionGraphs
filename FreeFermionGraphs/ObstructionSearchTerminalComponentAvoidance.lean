import FreeFermionGraphs.ObstructionSearchTerminalHistoryPersistence

/-!
# Lemma 14(iv): terminal component vertices avoid the executed paths

In the remaining two-incoming branch, the terminal path `P` is a component of
`G[C_b \oplus C'_d]` which is not appended to the search deformation.  A vertex
of `P \cap C_b` therefore cannot lie on an executed path: a path of the other
component family has the wrong color type, while a path of the same family
meeting `P` must equal `P`.

This module formalizes that component argument independently of the terminal
search trace.  It then combines it with the finite-history persistence theorem.
No terminal-path provenance is introduced as data.  The remaining search-specific
obligation is to identify the terminal path as the unexecuted `bd` component and
to establish the original-hole membership of its `C_b` vertices.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace FixedPairingPathFamily

/-- A `C_b` vertex of one `bd` component cannot lie on a distinct path in the
same fixed-pairing family. -/
theorem not_mem_path_of_mem_bdPath_of_ne
    (O : FixedPairingPathFamily G)
    {P Q : Set V} {x : V}
    (hP : P ∈ O.bdPaths)
    (hQ : Q ∈ O.paths)
    (hxP : x ∈ P)
    (hxCb : x ∈ O.Cb)
    (hxExact : ExactlyOneOfFour x O.Ca O.Cb O.Cc O.Cd)
    (hne : Q ≠ P) :
    x ∉ Q := by
  intro hxQ
  change Q ∈ O.acPaths ∨ Q ∈ O.bdPaths at hQ
  rcases hQ with hQac | hQbd
  · exact hxExact.not_mem_ac_and_bd
      ⟨O.ac_subset Q hQac hxQ, Or.inl hxCb⟩
  · have hEq : P = Q :=
      O.eq_of_mem_bdPaths hP hQbd hxP hxQ
    exact hne hEq.symm

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}
  {D : ConcretePathDeformation O Cprime}

namespace Lemma11AHistoryContext

/-- The component `P` is distinct from the current path and, in the positive
history case, from every represented prior path. -/
def AvoidsComponent
    (X : D.Lemma11AHistoryContext) (P : Set V) : Prop :=
  match X with
  | .first _ => Set.range D.path.vertex ≠ P
  | .later H =>
      (∀ r : Nat, r < H.priorCount →
        Set.range (H.history.block r).path.vertex ≠ P) ∧
      Set.range D.path.vertex ≠ P

/-- Exact color and component uniqueness turn component distinctness into
avoidance of every path represented by the finite history context. -/
theorem avoidsAllPaths_of_mem_bdComponent
    (X : D.Lemma11AHistoryContext)
    {P : Set V} {x : V}
    (hP : P ∈ O.bdPaths)
    (hxP : x ∈ P)
    (hxCb : x ∈ O.Cb)
    (hxExact : ExactlyOneOfFour x O.Ca O.Cb O.Cc O.Cd)
    (hdistinct : X.AvoidsComponent P) :
    X.AvoidsAllPaths x := by
  cases X with
  | first F =>
      change Set.range D.path.vertex ≠ P at hdistinct
      change x ∉ Set.range D.path.vertex
      exact O.not_mem_path_of_mem_bdPath_of_ne
        hP D.path_range_mem hxP hxCb hxExact hdistinct
  | later H =>
      change
        (∀ r : Nat, r < H.priorCount →
          Set.range (H.history.block r).path.vertex ≠ P) ∧
        Set.range D.path.vertex ≠ P at hdistinct
      change
        (∀ r : Nat, r < H.priorCount →
          x ∉ Set.range (H.history.block r).path.vertex) ∧
        x ∉ Set.range D.path.vertex
      constructor
      · intro r hr
        exact O.not_mem_path_of_mem_bdPath_of_ne
          hP (H.history.block r).path_range_mem hxP hxCb hxExact
          (hdistinct.1 r hr)
      · exact O.not_mem_path_of_mem_bdPath_of_ne
          hP D.path_range_mem hxP hxCb hxExact hdistinct.2

end Lemma11AHistoryContext

end ConcretePathDeformation

variable {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ObstructionSearchInitialization

variable {I : ObstructionSearchInitialization families Cprime}

namespace OrderedOSExecution

/-- A `C_b` vertex of an unexecuted terminal `bd` component persists to the
exact positive manuscript terminal hole once its original-hole membership and
component distinctness from the recorded execution history are established. -/
theorem mem_manuscriptFinalHole_of_mem_bdComponent
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : OrderedOSExecution I source originalHole)
    (hpos : 0 < X.blockCount)
    {P : Set V} {x : V}
    (hP : P ∈ (families (I.pairing source)).bdPaths)
    (hxP : x ∈ P)
    (hxCb : x ∈ (families (I.pairing source)).Cb)
    (hxExact : ExactlyOneOfFour x
      (families (I.pairing source)).Ca
      (families (I.pairing source)).Cb
      (families (I.pairing source)).Cc
      (families (I.pairing source)).Cd)
    (hxOriginal : x ∈ Set.range originalHole.vertex)
    (hdistinct :
      (X.blockContext (X.lastBlockIndex hpos)).AvoidsComponent P) :
    x ∈ Set.range X.manuscriptFinalHole.vertex := by
  apply X.mem_manuscriptFinalHole_of_mem_originalHole_of_avoidsContext
    hpos hxOriginal
  exact
    (X.blockContext (X.lastBlockIndex hpos)).
      avoidsAllPaths_of_mem_bdComponent
        hP hxP hxCb hxExact hdistinct

end OrderedOSExecution

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
