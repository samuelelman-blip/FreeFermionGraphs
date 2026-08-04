import FreeFermionGraphs.ObstructionSearchFiniteMixedTerminalAlternatingLabels

/-!
# Terminal parity from stepwise colour alternation

The terminal component used in manuscript Lemma 14 is written
`j₀-k₀-⋯-k_(ℓ-1)-j_ℓ`.  Rather than storing the conclusion that even indices
are precisely the `j`-side, this module records only the literal local fact
that membership in that colour side flips at every consecutive path step.
Parity of every path coordinate is then proved by induction.
-/

universe u

variable {V : Type u}

namespace SimpleGraph
namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

namespace IndexedInducedPath

/-- A path side containing the first vertex and flipping at every step is
exactly the even-index side. -/
theorem even_iff_mem_of_first_mem_and_step_flip
    (P : IndexedInducedPath G)
    (sameSide : Set V)
    (first_mem :
      P.vertex ⟨0, P.nonempty⟩ ∈ sameSide)
    (step_flip :
      ∀ (n : Nat) (hn : n + 1 < P.card),
        P.vertex ⟨n + 1, hn⟩ ∈ sameSide ↔
          ¬P.vertex ⟨n, by omega⟩ ∈ sameSide)
    (q : Fin P.card) :
    Even q.val ↔ P.vertex q ∈ sameSide := by
  have hindex :
      ∀ (n : Nat) (hn : n < P.card),
        Even n ↔ P.vertex ⟨n, hn⟩ ∈ sameSide := by
    intro n
    induction n with
    | zero =>
        intro hn
        constructor
        · intro _
          simpa using first_mem
        · intro _
          exact ⟨0, by omega⟩
    | succ n ih =>
        intro hn
        have hnPrevious : n < P.card := by omega
        have hflip := step_flip n hn
        constructor
        · intro hEvenSucc
          have hnotEven : ¬Even n := by
            rintro ⟨a, ha⟩
            obtain ⟨b, hb⟩ := hEvenSucc
            omega
          have hnotMem :
              ¬P.vertex ⟨n, hnPrevious⟩ ∈ sameSide := by
            intro hmem
            exact hnotEven ((ih hnPrevious).2 hmem)
          exact hflip.2 hnotMem
        · intro hmem
          have hnotMem :
              ¬P.vertex ⟨n, hnPrevious⟩ ∈ sameSide :=
            hflip.1 hmem
          have hnotEven : ¬Even n := by
            intro heven
            exact hnotMem ((ih hnPrevious).1 heven)
          rcases even_or_odd n with heven | hodd
          · exact (hnotEven heven).elim
          · obtain ⟨a, ha⟩ := hodd
            exact ⟨a + 1, by omega⟩
  simpa using hindex q.val q.isLt

end IndexedInducedPath

namespace ObstructionSearchInitialization

variable {I : ObstructionSearchInitialization families Cprime}

/-- Literal local alternation of each terminal path.

The colour side contains the first endpoint, the obstruction target, and the
last endpoint.  Consecutive path coordinates alternate membership in that
side. -/
structure FiniteMixedSideTerminalStepAlternationData
    (T : I.InitializationFiniteMixedSideTerminalCoreData) : Type (u + 1) where
  sameSide : I.Node → Set V
  first_mem :
    ∀ target : I.Node,
      (T.terminalPath target).vertex
          ⟨0, (T.terminalPath target).nonempty⟩ ∈ sameSide target
  step_flip :
    ∀ (target : I.Node) (n : Nat)
      (hn : n + 1 < (T.terminalPath target).card),
      (T.terminalPath target).vertex ⟨n + 1, hn⟩ ∈ sameSide target ↔
        ¬(T.terminalPath target).vertex ⟨n, by omega⟩ ∈ sameSide target
  target_mem :
    ∀ {source target : I.Node},
      I.graph.Arc source target → (target : V) ∈ sameSide target
  last_mem :
    ∀ {source target : I.Node},
      I.graph.Arc source target →
        (T.terminalPath target).obstructionEndpoint .last ∈ sameSide target

namespace FiniteMixedSideTerminalStepAlternationData

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}

/-- Stepwise alternation constructs the existing literal-label interface. -/
def toAlternatingLabelData
    (A : FiniteMixedSideTerminalStepAlternationData T) :
    FiniteMixedSideTerminalAlternatingLabelData T where
  sameSide := A.sameSide
  index_even_iff_mem_sameSide := by
    intro target q
    exact
      (T.terminalPath target).even_iff_mem_of_first_mem_and_step_flip
        (A.sameSide target) (A.first_mem target) (A.step_flip target) q
  target_mem_sameSide := A.target_mem
  lastEndpoint_mem_sameSide := A.last_mem

end FiniteMixedSideTerminalStepAlternationData

end ObstructionSearchInitialization
end FixedPairingPathFamily
end SimpleGraph
