import FreeFermionGraphs.IndexedPathClosure

/-!
# The artificial-root endpoint triple produces a hoop

If an original Hamiltonian vertex sees exactly the artificial root, the
first original path vertex, and the terminal, then deleting the artificial
root leaves a fresh vertex adjacent exactly to both endpoints of the
original tail.  The path-closure constructor therefore gives a literal
induced hole in the original graph.  This is the empty-handle boundary case
of the exceptional endpoint triple in Appendix E.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace RootedInducedPath

variable {G : SimpleGraph V} {K : Set V}

/-- The first original vertex of a clique-rooted path. -/
def firstOriginalIndex
    (P : CliqueRootedInducedPath G K) (hcard : 2 ≤ P.path.card) :
    Fin P.path.card :=
  ⟨1, by omega⟩

/-- The final augmented-path index. -/
def terminalIndex (P : CliqueRootedInducedPath G K) : Fin P.path.card :=
  ⟨P.path.card - 1, Nat.sub_lt P.path.nonempty (by decide)⟩

/-- Exact root/first/terminal adjacency becomes endpoint-closure data for
the original tail. -/
theorem originalTail_endpointClosureData_of_root_first_terminal
    (P : CliqueRootedInducedPath G K) {j : V}
    (hcard : 4 ≤ P.path.card)
    (hjOutside : some j ∉ Set.range P.path.vertex)
    (hjFirst : (G.adjoinRootAt K).Adj (some j)
      (P.path.vertex (P.firstOriginalIndex (by omega))))
    (hjTerminal : (G.adjoinRootAt K).Adj (some j)
      (P.path.vertex P.terminalIndex))
    (hexact : ∀ q : Fin P.path.card,
      (G.adjoinRootAt K).Adj (some j) (P.path.vertex q) →
        q = ⟨0, P.path.nonempty⟩ ∨
        q = P.firstOriginalIndex (by omega) ∨
        q = P.terminalIndex) :
    let htail : 2 ≤ P.path.card := by omega
    (P.originalTail htail).EndpointClosureData j := by
  let htail : 2 ≤ P.path.card := by omega
  change (P.originalTail htail).EndpointClosureData j
  have htailThree : 3 ≤ (P.originalTail htail).card := by
    change 3 ≤ P.path.card - 1
    omega
  refine
    { three_le := htailThree
      outside := ?_
      adj_iff := ?_ }
  · rintro ⟨q, hq⟩
    apply hjOutside
    refine ⟨P.originalTailIndex htail q, ?_⟩
    rw [P.path_vertex_originalTailIndex htail q]
    exact congrArg some hq
  · intro q
    change G.Adj j (P.originalTailVertex htail q) ↔
      q.val = 0 ∨ q.val + 1 = P.path.card - 1
    rw [← G.adjoinRootAt_adj_some_some K]
    rw [← P.path_vertex_originalTailIndex htail q]
    constructor
    · intro hjq
      rcases hexact (P.originalTailIndex htail q) hjq with
        hroot | hfirst | hlast
      · have hval := congrArg Fin.val hroot
        simp [originalTailIndex] at hval
      · left
        have hval := congrArg Fin.val hfirst
        dsimp [originalTailIndex, firstOriginalIndex] at hval
        omega
      · right
        have hval := congrArg Fin.val hlast
        dsimp [originalTailIndex, terminalIndex] at hval
        change q.val + 1 = P.path.card - 1
        omega
    · rintro (hqFirst | hqLast)
      · have hindex : P.originalTailIndex htail q =
            P.firstOriginalIndex (by omega) := by
          apply Fin.ext
          simp [originalTailIndex, firstOriginalIndex, hqFirst]
        rw [hindex]
        exact hjFirst
      · have hindex : P.originalTailIndex htail q = P.terminalIndex := by
          apply Fin.ext
          dsimp [originalTailIndex, terminalIndex]
          change q.val + 1 = P.path.card - 1
          exact hqLast
        rw [hindex]
        exact hjTerminal

/-- The root/first/terminal endpoint triple constructs its original-graph
hoop, with an explicit carrier equation. -/
theorem exists_rootHoop_of_root_first_terminal
    (P : CliqueRootedInducedPath G K) {j : V}
    (hcard : 4 ≤ P.path.card)
    (hjOutside : some j ∉ Set.range P.path.vertex)
    (hjFirst : (G.adjoinRootAt K).Adj (some j)
      (P.path.vertex (P.firstOriginalIndex (by omega))))
    (hjTerminal : (G.adjoinRootAt K).Adj (some j)
      (P.path.vertex P.terminalIndex))
    (hexact : ∀ q : Fin P.path.card,
      (G.adjoinRootAt K).Adj (some j) (P.path.vertex q) →
        q = ⟨0, P.path.nonempty⟩ ∨
        q = P.firstOriginalIndex (by omega) ∨
        q = P.terminalIndex) :
    ∃ C : IndexedInducedHole G,
      Set.range C.vertex = P.originalCarrier ∪ {j} := by
  let htail : 2 ≤ P.path.card := by omega
  let hclose := P.originalTail_endpointClosureData_of_root_first_terminal
    hcard hjOutside hjFirst hjTerminal hexact
  let C := (P.originalTail htail).closeToHole hclose
  refine ⟨C, ?_⟩
  rw [IndexedInducedPath.range_closeToHole]
  rw [P.originalCarrier_eq_range_originalTail htail]

end RootedInducedPath

end SimpleGraph
