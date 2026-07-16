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

/-- External degree after replacing `C.vertex i` by `introduced`, counted
on the original fixed index type. -/
noncomputable def externalDegreeAfterReplacement
    (C : IndexedInducedHole G) (introduced : V)
    (i : Fin C.card) (u : V) : Nat :=
  ({q : Fin C.card | G.Adj u (C.replaceVertex introduced i q)} :
    Set (Fin C.card)).ncard

/-- Introducing a neighbor in place of a nonneighbor increases external
degree by one. -/
theorem externalDegreeAfterReplacement_eq_add_one
    (C : IndexedInducedHole G) {introduced u : V} {i : Fin C.card}
    (huIntroduced : G.Adj u introduced)
    (huRemoved : ¬G.Adj u (C.vertex i)) :
    C.externalDegreeAfterReplacement introduced i u =
      C.externalDegree u + 1 := by
  have hset :
      ({q : Fin C.card | G.Adj u (C.replaceVertex introduced i q)} :
        Set (Fin C.card)) =
        Set.insert i (C.neighborIndexSet u) := by
    ext q
    by_cases hqi : q = i
    · subst q
      simp [replaceVertex, huIntroduced]
    · simp [replaceVertex, hqi]
  have hi : i ∉ C.neighborIndexSet u := by
    simpa using huRemoved
  unfold externalDegreeAfterReplacement externalDegree
  rw [hset, Set.ncard_insert_of_notMem hi]

/-- Removing a neighbor and introducing a nonneighbor decreases external
degree by one, written without truncated subtraction. -/
theorem externalDegree_eq_afterReplacement_add_one
    (C : IndexedInducedHole G) {introduced u : V} {i : Fin C.card}
    (huIntroduced : ¬G.Adj u introduced)
    (huRemoved : G.Adj u (C.vertex i)) :
    C.externalDegree u =
      C.externalDegreeAfterReplacement introduced i u + 1 := by
  have hset :
      C.neighborIndexSet u =
        Set.insert i
          ({q : Fin C.card |
            G.Adj u (C.replaceVertex introduced i q)} :
            Set (Fin C.card)) := by
    ext q
    by_cases hqi : q = i
    · subst q
      simp [replaceVertex, huRemoved]
    · simp [replaceVertex, hqi]
  have hi :
      i ∉ ({q : Fin C.card |
        G.Adj u (C.replaceVertex introduced i q)} :
        Set (Fin C.card)) := by
    simpa [replaceVertex] using huIntroduced
  unfold externalDegree externalDegreeAfterReplacement
  rw [hset, Set.ncard_insert_of_notMem hi]

/-- If adjacency to the introduced and removed vertices agrees, replacement
does not change external degree. -/
theorem externalDegreeAfterReplacement_eq
    (C : IndexedInducedHole G) {introduced u : V} {i : Fin C.card}
    (hu : G.Adj u introduced ↔ G.Adj u (C.vertex i)) :
    C.externalDegreeAfterReplacement introduced i u =
      C.externalDegree u := by
  have hset :
      ({q : Fin C.card | G.Adj u (C.replaceVertex introduced i q)} :
        Set (Fin C.card)) =
        C.neighborIndexSet u := by
    ext q
    by_cases hqi : q = i
    · subst q
      simpa [replaceVertex] using hu
    · simp [replaceVertex, hqi]
  unfold externalDegreeAfterReplacement externalDegree
  exact congrArg Set.ncard hset

/-- The fixed-index replacement count is definitionally the degree in the
deformed indexed hole. -/
theorem SingleVertexDeformation.externalDegree_deform_eq_afterReplacement
    {C : IndexedInducedHole G} {introduced u : V} {i : Fin C.card}
    (h : C.SingleVertexDeformation introduced i) :
    (C.deform h).externalDegree u =
      C.externalDegreeAfterReplacement introduced i u :=
  rfl

theorem SingleVertexDeformation.externalDegree_deform_eq_add_one
    {C : IndexedInducedHole G} {introduced u : V} {i : Fin C.card}
    (h : C.SingleVertexDeformation introduced i)
    (huIntroduced : G.Adj u introduced)
    (huRemoved : ¬G.Adj u (C.vertex i)) :
    (C.deform h).externalDegree u = C.externalDegree u + 1 := by
  calc
    (C.deform h).externalDegree u =
        C.externalDegreeAfterReplacement introduced i u :=
      h.externalDegree_deform_eq_afterReplacement
    _ = C.externalDegree u + 1 :=
      C.externalDegreeAfterReplacement_eq_add_one
        huIntroduced huRemoved

theorem SingleVertexDeformation.externalDegree_eq_deform_add_one
    {C : IndexedInducedHole G} {introduced u : V} {i : Fin C.card}
    (h : C.SingleVertexDeformation introduced i)
    (huIntroduced : ¬G.Adj u introduced)
    (huRemoved : G.Adj u (C.vertex i)) :
    C.externalDegree u = (C.deform h).externalDegree u + 1 := by
  rw [h.externalDegree_deform_eq_afterReplacement]
  exact C.externalDegree_eq_afterReplacement_add_one
    huIntroduced huRemoved

theorem SingleVertexDeformation.externalDegree_deform_eq
    {C : IndexedInducedHole G} {introduced u : V} {i : Fin C.card}
    (h : C.SingleVertexDeformation introduced i)
    (hu : G.Adj u introduced ↔ G.Adj u (C.vertex i)) :
    (C.deform h).externalDegree u = C.externalDegree u := by
  rw [h.externalDegree_deform_eq_afterReplacement]
  exact C.externalDegreeAfterReplacement_eq hu

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
