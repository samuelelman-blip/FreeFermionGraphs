import FreeFermionGraphs.Corollary10

/-!
# Lemma 11: one-step degree change

The degree-bookkeeping core of Lemma 11(a).  Replacing one hole vertex by a
clone changes the number of neighbors of an external vertex according only
to its adjacency to the introduced and removed vertices.  In particular,
membership in a dependent subset increases that degree by exactly one.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace IndexedInducedHole

/-- The paper's `Δ_C(u)`: the number of vertices of the indexed hole `C`
adjacent to `u`. -/
noncomputable def externalDegree (C : IndexedInducedHole G) (u : V) : Nat :=
  (C.neighborIndexSet u).ncard

/-- Introducing a neighbor in place of a nonneighbor increases external
degree by one. -/
theorem SingleVertexDeformation.externalDegree_deform_eq_add_one
    {C : IndexedInducedHole G} {introduced u : V} {i : Fin C.card}
    (h : C.SingleVertexDeformation introduced i)
    (huIntroduced : G.Adj u introduced)
    (huRemoved : ¬G.Adj u (C.vertex i)) :
    (C.deform h).externalDegree u = C.externalDegree u + 1 := by
  have hset :
      (C.deform h).neighborIndexSet u =
        Set.insert i (C.neighborIndexSet u) := by
    ext q
    by_cases hqi : q = i
    · subst q
      simp [huIntroduced]
    · simp [hqi]
  have hi : i ∉ C.neighborIndexSet u := by
    simpa using huRemoved
  change ((C.deform h).neighborIndexSet u).ncard =
    (C.neighborIndexSet u).ncard + 1
  rw [hset, Set.ncard_insert_of_notMem hi]

/-- Removing a neighbor and introducing a nonneighbor decreases external
degree by one, written without truncated subtraction. -/
theorem SingleVertexDeformation.externalDegree_eq_deform_add_one
    {C : IndexedInducedHole G} {introduced u : V} {i : Fin C.card}
    (h : C.SingleVertexDeformation introduced i)
    (huIntroduced : ¬G.Adj u introduced)
    (huRemoved : G.Adj u (C.vertex i)) :
    C.externalDegree u = (C.deform h).externalDegree u + 1 := by
  have hset :
      C.neighborIndexSet u =
        Set.insert i ((C.deform h).neighborIndexSet u) := by
    ext q
    by_cases hqi : q = i
    · subst q
      simp [huRemoved]
    · simp [hqi]
  have hi : i ∉ (C.deform h).neighborIndexSet u := by
    simpa using huIntroduced
  change (C.neighborIndexSet u).ncard =
    ((C.deform h).neighborIndexSet u).ncard + 1
  rw [hset, Set.ncard_insert_of_notMem hi]

/-- If adjacency to the introduced and removed vertices agrees, deformation
does not change external degree. -/
theorem SingleVertexDeformation.externalDegree_deform_eq
    {C : IndexedInducedHole G} {introduced u : V} {i : Fin C.card}
    (h : C.SingleVertexDeformation introduced i)
    (hu : G.Adj u introduced ↔ G.Adj u (C.vertex i)) :
    (C.deform h).externalDegree u = C.externalDegree u := by
  have hset :
      (C.deform h).neighborIndexSet u = C.neighborIndexSet u := by
    ext q
    by_cases hqi : q = i
    · subst q
      simpa using hu
    · simp [hqi]
  change ((C.deform h).neighborIndexSet u).ncard =
    (C.neighborIndexSet u).ncard
  exact congrArg Set.ncard hset

/-- The one-step degree conclusion of Lemma 11(a): every member of the
dependent subset gains exactly one neighbor under the deformation. -/
theorem SingleVertexDeformation.dependent_externalDegree_deform_eq_add_one
    {C : IndexedInducedHole G} {Cprime : Set V}
    {introduced u : V} {i : Fin C.card}
    (h : C.SingleVertexDeformation introduced i)
    (hu : u ∈ G.dependentSubset Cprime introduced (C.vertex i)) :
    (C.deform h).externalDegree u = C.externalDegree u + 1 :=
  h.externalDegree_deform_eq_add_one hu.2.1 hu.2.2.2

end IndexedInducedHole

end SimpleGraph
