import FreeFermionGraphs.InducedPathDeformationReverse
import FreeFermionGraphs.InducedPathTree

/-!
# Prefix paths for a single induced-path deformation

This file formalises the prefix families `P_m` and `P̃_m` in manuscript
Eqs. (E3)-(E4).  Prefixes before the deformation index are unchanged; from
the deformation index onward, the clone occupies that same ordered position.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace IndexedInducedPath

/-- The prefix `P_m`, containing the vertices at indices `0, ..., m`. -/
def initialSegment (P : IndexedInducedPath G) (m : Fin P.card) :
    IndexedInducedPath G where
  card := m.val + 1
  nonempty := by omega
  vertex q := P.vertex ⟨q.val, by omega⟩
  injective := by
    intro p q hpq
    apply Fin.ext
    exact congrArg (fun x : Fin P.card => x.val) (P.injective hpq)
  adj_iff := by
    intro p q
    exact P.adj_iff ⟨p.val, by omega⟩ ⟨q.val, by omega⟩

@[simp]
theorem prefix_card (P : IndexedInducedPath G) (m : Fin P.card) :
    (P.initialSegment m).card = m.val + 1 :=
  rfl

@[simp]
theorem prefix_vertex (P : IndexedInducedPath G) (m : Fin P.card)
    (q : Fin (m.val + 1)) :
    (P.initialSegment m).vertex q = P.vertex ⟨q.val, by omega⟩ :=
  rfl

end IndexedInducedPath

namespace RootedInducedPath

variable {root : V}

/-- A prefix of a rooted induced path is rooted at the same vertex. -/
def initialSegment (P : RootedInducedPath G root) (m : Fin P.path.card) :
    RootedInducedPath G root where
  path := P.path.initialSegment m
  root_eq := by
    simpa [IndexedInducedPath.initialSegment] using P.root_eq

/-- Deform the underlying indexed path while retaining its root. -/
def deform (P : RootedInducedPath G root) {s : V}
    {i : Fin P.path.card}
    (h : P.path.SingleVertexDeformation s i) :
    RootedInducedPath G root where
  path := P.path.deform h
  root_eq := P.path.deform_first_endpoint h |>.trans P.root_eq

/-- The manuscript family `P̃_m` obtained by taking the corresponding prefix
of the deformed path. -/
def deformedPrefix (P : RootedInducedPath G root) {s : V}
    {i : Fin P.path.card}
    (h : P.path.SingleVertexDeformation s i)
    (m : Fin P.path.card) : RootedInducedPath G root :=
  (P.deform h).initialSegment m

/-- Reinterpret the deformation index as an index of `P_m` when `i ≤ m`. -/
def deformationPrefixIndex {P : RootedInducedPath G root}
    {i m : Fin P.path.card} (him : i.val ≤ m.val) : Fin (m.val + 1) :=
  ⟨i.val, by omega⟩

/-- Eq. (E4), first branch: every vertex of a prefix strictly before the
deformation index agrees with the original prefix. -/
theorem deformedPrefix_vertex_of_lt
    (P : RootedInducedPath G root) {s : V}
    {i : Fin P.path.card}
    (h : P.path.SingleVertexDeformation s i)
    {m : Fin P.path.card} (hmi : m.val < i.val)
    (q : Fin (m.val + 1)) :
    (P.deformedPrefix h m).path.vertex q =
      (P.initialSegment m).path.vertex q := by
  have hqi : (⟨q.val, by omega⟩ : Fin P.path.card) ≠ i := by
    intro hEq
    have hval : q.val = i.val := congrArg Fin.val hEq
    omega
  exact P.path.deform_vertex_away h hqi

/-- Eq. (E4), second branch at the changed index: once the prefix reaches
`i`, its vertex at `i` is the clone `s`. -/
theorem deformedPrefix_vertex_at
    (P : RootedInducedPath G root) {s : V}
    {i : Fin P.path.card}
    (h : P.path.SingleVertexDeformation s i)
    {m : Fin P.path.card} (him : i.val ≤ m.val) :
    (P.deformedPrefix h m).path.vertex (deformationPrefixIndex him) = s := by
  exact P.path.deform_vertex_at h

/-- Eq. (E4), second branch away from the changed index: every other ordered
vertex remains the corresponding vertex of `P_m`. -/
theorem deformedPrefix_vertex_away
    (P : RootedInducedPath G root) {s : V}
    {i : Fin P.path.card}
    (h : P.path.SingleVertexDeformation s i)
    {m : Fin P.path.card} (him : i.val ≤ m.val)
    (q : Fin (m.val + 1))
    (hqi : q ≠ deformationPrefixIndex him) :
    (P.deformedPrefix h m).path.vertex q =
      (P.initialSegment m).path.vertex q := by
  apply P.path.deform_vertex_away h
  intro hEq
  apply hqi
  apply Fin.ext
  exact congrArg (fun x : Fin P.path.card => x.val) hEq

/-- Consecutive manuscript prefixes are joined by a forward tree edge. -/
theorem prefix_isOneVertexExtension_succ
    (P : RootedInducedPath G root) (m : Nat)
    (hm : m + 1 < P.path.card) :
    (P.initialSegment ⟨m, by omega⟩).IsOneVertexExtension
      (P.initialSegment ⟨m + 1, hm⟩) := by
  refine ⟨?_, ?_⟩
  · rfl
  · intro q
    rfl

/-- Consecutive deformed prefixes are joined by the corresponding forward
tree edge as well. -/
theorem deformedPrefix_isOneVertexExtension_succ
    (P : RootedInducedPath G root) {s : V}
    {i : Fin P.path.card}
    (h : P.path.SingleVertexDeformation s i)
    (m : Nat) (hm : m + 1 < P.path.card) :
    (P.deformedPrefix h ⟨m, by omega⟩).IsOneVertexExtension
      (P.deformedPrefix h ⟨m + 1, hm⟩) := by
  exact prefix_isOneVertexExtension_succ (P.deform h) m hm

end RootedInducedPath

end SimpleGraph
