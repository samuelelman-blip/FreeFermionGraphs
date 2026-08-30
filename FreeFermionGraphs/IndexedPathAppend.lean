import FreeFermionGraphs.WeightedHoppingMatrix

/-!
# Appending one terminal vertex to an indexed induced path

The rooted induced-path tree is defined by a one-vertex extension relation,
but its foundational layer did not yet provide the corresponding constructor.
This module constructs the longer induced path whenever a fresh vertex is
adjacent exactly to the old terminal, and proves the resulting rooted path is
a literal one-vertex extension.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace IndexedInducedPath

variable {G : SimpleGraph V}

/-- Exact data needed to append `s` after the terminal of `P`. -/
structure TerminalExtensionData
    (P : IndexedInducedPath G) (s : V) : Prop where
  outside : s ∉ Set.range P.vertex
  adj_iff : ∀ q : Fin P.card,
    G.Adj s (P.vertex q) ↔ q.val + 1 = P.card

/-- Append a fresh vertex adjacent exactly to the old terminal. -/
def appendTerminal
    (P : IndexedInducedPath G) {s : V}
    (h : P.TerminalExtensionData s) : IndexedInducedPath G where
  card := P.card + 1
  nonempty := by omega
  vertex := Fin.lastCases s P.vertex
  injective := by
    intro p
    refine Fin.lastCases ?_ (fun p => ?_) p
    · intro q
      refine Fin.lastCases ?_ (fun q => ?_) q
      · intro _
        rfl
      · intro hsq
        simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at hsq
        exact (h.outside ⟨q, hsq.symm⟩).elim
    · intro q
      refine Fin.lastCases ?_ (fun q => ?_) q
      · intro hps
        simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at hps
        exact (h.outside ⟨p, hps⟩).elim
      · intro hpq
        simp only [Fin.lastCases_castSucc] at hpq
        exact congrArg Fin.castSucc (P.injective hpq)
  adj_iff := by
    intro p
    refine Fin.lastCases ?_ (fun p => ?_) p
    · intro q
      refine Fin.lastCases ?_ (fun q => ?_) q
      · simp
      · simp only [Fin.lastCases_last, Fin.lastCases_castSucc,
          Fin.val_last, Fin.val_castSucc]
        rw [h.adj_iff q]
        omega
    · intro q
      refine Fin.lastCases ?_ (fun q => ?_) q
      · rw [G.adj_comm]
        simp only [Fin.lastCases_last, Fin.lastCases_castSucc,
          Fin.val_last, Fin.val_castSucc]
        rw [h.adj_iff p]
        omega
      · simpa only [Fin.lastCases_castSucc, Fin.val_castSucc] using
          P.adj_iff p q

@[simp]
theorem appendTerminal_vertex_last
    (P : IndexedInducedPath G) {s : V}
    (h : P.TerminalExtensionData s) :
    (P.appendTerminal h).vertex (Fin.last P.card) = s := by
  simp [appendTerminal]

@[simp]
theorem appendTerminal_vertex_castSucc
    (P : IndexedInducedPath G) {s : V}
    (h : P.TerminalExtensionData s) (q : Fin P.card) :
    (P.appendTerminal h).vertex (Fin.castSucc q) = P.vertex q := by
  simp [appendTerminal]

end IndexedInducedPath

namespace RootedInducedPath

variable {G : SimpleGraph V} {root : V}

/-- Append terminal-extension data to a rooted induced path. -/
def appendTerminal
    (P : RootedInducedPath G root) {s : V}
    (h : P.path.TerminalExtensionData s) : RootedInducedPath G root where
  path := P.path.appendTerminal h
  root_eq := by
    change Fin.lastCases s P.path.vertex
      (Fin.castSucc ⟨0, P.path.nonempty⟩) = root
    simp only [Fin.lastCases_castSucc]
    exact P.root_eq

/-- The constructed rooted path is definitionally a one-vertex extension. -/
theorem isOneVertexExtension_appendTerminal
    (P : RootedInducedPath G root) {s : V}
    (h : P.path.TerminalExtensionData s) :
    P.IsOneVertexExtension (P.appendTerminal h) := by
  refine ⟨rfl, ?_⟩
  intro q
  change Fin.lastCases s P.path.vertex
    (Fin.castSucc q) = P.path.vertex q
  simp

end RootedInducedPath

end SimpleGraph
