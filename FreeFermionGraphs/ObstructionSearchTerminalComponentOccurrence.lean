import FreeFermionGraphs.ObstructionSearchTerminalComponentAvoidance

/-!
# Lemma 14(iv): a missing terminal-component vertex identifies an executed path

In the proof of Lemma 14(i), reused in Lemma 14(iv), the manuscript argues that
if a vertex of `P ∩ C_b` were absent from the current hole, then it must have
been removed by one of the preceding Definition 19 path blocks.  Since path
components of one fixed-pairing family are disjoint, that executed path must be
`P` itself.

The carrier-persistence and component-avoidance results already formalized give
this implication directly.  This module packages the conclusion at the finite
history-context level and then states it on the exact positive manuscript
terminal hole.  It introduces no terminal-path provenance or stopping
certificate.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace FixedPairingPathFamily

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}
  {D : ConcretePathDeformation O Cprime}

namespace Lemma11AHistoryContext

/-- A component occurs as the current path, or as one of the represented prior
paths in the positive-history case. -/
def ContainsComponent
    (X : D.Lemma11AHistoryContext) (P : Set V) : Prop :=
  match X with
  | .first _ => Set.range D.path.vertex = P
  | .later H =>
      (∃ r : Nat, r < H.priorCount ∧
        Set.range (H.history.block r).path.vertex = P) ∨
      Set.range D.path.vertex = P

/-- Component avoidance is exactly non-occurrence among the paths represented
by the finite history context. -/
theorem avoidsComponent_iff_not_containsComponent
    (X : D.Lemma11AHistoryContext) (P : Set V) :
    X.AvoidsComponent P ↔ ¬X.ContainsComponent P := by
  cases X with
  | first _ =>
      simp [AvoidsComponent, ContainsComponent]
  | later H =>
      change
        ((∀ r : Nat, r < H.priorCount →
            Set.range (H.history.block r).path.vertex ≠ P) ∧
          Set.range D.path.vertex ≠ P) ↔
        ¬((∃ r : Nat, r < H.priorCount ∧
            Set.range (H.history.block r).path.vertex = P) ∨
          Set.range D.path.vertex = P)
      constructor
      · rintro ⟨hprior, hcurrent⟩ hcontains
        rcases hcontains with ⟨r, hr, hEq⟩ | hEq
        · exact hprior r hr hEq
        · exact hcurrent hEq
      · intro hnot
        constructor
        · intro r hr hEq
          exact hnot (Or.inl ⟨r, hr, hEq⟩)
        · intro hEq
          exact hnot (Or.inr hEq)

/-- If an original-hole `C_b` vertex of a `bd` component is absent from the
current final hole, that component must occur among the represented executed
paths.

This is the carrier-level form of the manuscript sentence that such a vertex
would be a removed `k_(p-1)^(q)` for some preceding block `q`. -/
theorem containsComponent_of_mem_bdComponent_of_not_mem_currentFinalHole
    (X : D.Lemma11AHistoryContext)
    {P : Set V} {x : V}
    (hP : P ∈ O.bdPaths)
    (hxP : x ∈ P)
    (hxCb : x ∈ O.Cb)
    (hxExact : ExactlyOneOfFour x O.Ca O.Cb O.Cc O.Cd)
    (hxOriginal : x ∈ Set.range X.originalHole.vertex)
    (hxNotFinal : x ∉ Set.range D.finalHole.vertex) :
    X.ContainsComponent P := by
  by_contra hnot
  have havoidComponent : X.AvoidsComponent P :=
    (X.avoidsComponent_iff_not_containsComponent P).2 hnot
  have havoidAll : X.AvoidsAllPaths x :=
    X.avoidsAllPaths_of_mem_bdComponent
      hP hxP hxCb hxExact havoidComponent
  exact hxNotFinal
    (X.mem_currentFinalHole_of_mem_originalHole_of_avoids
      hxOriginal havoidAll)

end Lemma11AHistoryContext

end ConcretePathDeformation

variable {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ObstructionSearchInitialization

variable {I : ObstructionSearchInitialization families Cprime}

namespace OrderedOSExecution

/-- Positive-execution specialization on the manuscript terminal hole
`C_j^(m)`: a missing original-hole `C_b` vertex forces its terminal `bd`
component to occur in the finite history of the last concrete block. -/
theorem containsComponent_of_mem_bdComponent_of_not_mem_manuscriptFinalHole
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
    (hxNotFinal : x ∉ Set.range X.manuscriptFinalHole.vertex) :
    (X.blockContext (X.lastBlockIndex hpos)).ContainsComponent P := by
  have hxContext :
      x ∈ Set.range
        (X.blockContext (X.lastBlockIndex hpos)).originalHole.vertex := by
    rw [X.blockContext_originalHole (X.lastBlockIndex hpos)]
    exact hxOriginal
  have hxNotLastFinal :
      x ∉ Set.range
        (X.concreteBlock (X.lastBlockIndex hpos)).finalHole.vertex := by
    intro hxLast
    apply hxNotFinal
    rw [X.manuscriptFinalHole_eq_lastBlockFinalHole hpos]
    exact hxLast
  exact
    ConcretePathDeformation.Lemma11AHistoryContext.containsComponent_of_mem_bdComponent_of_not_mem_currentFinalHole
      (X.blockContext (X.lastBlockIndex hpos))
      hP hxP hxCb hxExact hxContext hxNotLastFinal

end OrderedOSExecution

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
