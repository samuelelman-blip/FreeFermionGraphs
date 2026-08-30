import FreeFermionGraphs.PauliCliqueHamiltonianRootHoop

/-!
# Constructing the ordinary bubble-wand endpoint branch

For the non-root exceptional endpoint triple, the adjacent pair has positive
augmented indices and lies strictly before the terminal.  Shifting those
indices through the canonical original tail gives the split of a literal
`BubbleWand G` with the exact Definition 11 neighborhood.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace RootedInducedPath

variable {G : SimpleGraph V} {K : Set V}

/-- Exact positive consecutive-pair/terminal support constructs the ordinary
nonempty-handle bubble wand in the original graph. -/
theorem exists_bubbleWand_of_positive_pair_terminal
    (P : CliqueRootedInducedPath G K) {j : V}
    (hjOutside : some j ∉ Set.range P.path.vertex)
    {left right : Fin P.path.card}
    (hleftPos : 0 < left.val)
    (hconsecutive : left.val + 1 = right.val)
    (hgap : left.val + 3 < P.path.card)
    (hjLeft : (G.adjoinRootAt K).Adj (some j) (P.path.vertex left))
    (hjRight : (G.adjoinRootAt K).Adj (some j) (P.path.vertex right))
    (hjTerminal : (G.adjoinRootAt K).Adj (some j)
      (P.path.vertex P.terminalIndex))
    (hexact : ∀ q : Fin P.path.card,
      (G.adjoinRootAt K).Adj (some j) (P.path.vertex q) →
        q = left ∨ q = right ∨ q = P.terminalIndex) :
    ∃ B : BubbleWand G,
      P.originalCarrier = Set.range B.path.vertex ∧
      B.bubble = j ∧
      ∃ htail : 2 ≤ P.path.card, B.path = P.originalTail htail := by
  let htail : 2 ≤ P.path.card := by omega
  let T := P.originalTail htail
  let split : Fin T.card := ⟨left.val - 1, by
    change left.val - 1 < P.path.card - 1
    omega⟩
  let B : BubbleWand G :=
    { path := T
      bubble := j
      split := split
      gap := by
        change split.val + 3 < P.path.card - 1
        dsimp [split]
        omega
      outside := by
        rintro ⟨q, hq⟩
        apply hjOutside
        refine ⟨P.originalTailIndex htail q, ?_⟩
        rw [P.path_vertex_originalTailIndex htail q]
        exact congrArg some hq
      adj_iff := by
        intro q
        change G.Adj j (P.originalTailVertex htail q) ↔
          q.val = split.val ∨ q.val = split.val + 1 ∨
            q.val + 1 = P.path.card - 1
        rw [← G.adjoinRootAt_adj_some_some K]
        rw [← P.path_vertex_originalTailIndex htail q]
        constructor
        · intro hjq
          rcases hexact (P.originalTailIndex htail q) hjq with
            hqLeft | hqRight | hqTerminal
          · left
            have hval := congrArg Fin.val hqLeft
            dsimp [originalTailIndex, split] at hval ⊢
            omega
          · right
            left
            have hval := congrArg Fin.val hqRight
            dsimp [originalTailIndex, split] at hval ⊢
            omega
          · right
            right
            have hval := congrArg Fin.val hqTerminal
            dsimp [originalTailIndex, terminalIndex] at hval
            omega
        · rintro (hqLeft | hqRight | hqTerminal)
          · have hindex : P.originalTailIndex htail q = left := by
              apply Fin.ext
              dsimp [originalTailIndex, split] at hqLeft ⊢
              omega
            rw [hindex]
            exact hjLeft
          · have hindex : P.originalTailIndex htail q = right := by
              apply Fin.ext
              dsimp [originalTailIndex, split] at hqRight ⊢
              omega
            rw [hindex]
            exact hjRight
          · have hindex :
                P.originalTailIndex htail q = P.terminalIndex := by
              apply Fin.ext
              dsimp [originalTailIndex, terminalIndex]
              omega
            rw [hindex]
            exact hjTerminal }
  refine ⟨B, P.originalCarrier_eq_range_originalTail htail, rfl,
    htail, rfl⟩

end RootedInducedPath

end SimpleGraph
