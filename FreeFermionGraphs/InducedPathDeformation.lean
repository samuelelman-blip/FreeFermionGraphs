import FreeFermionGraphs.InducedStructures

/-!
# Single-vertex deformations of induced paths

Manuscript Definition 10 applies the single-vertex deformation operation to
both holes and induced paths.  The existing deformation layer is hole-specific;
Lemma 18 instead needs the induced-path version and its finite closure from
Definition 12.

For an internal path vertex `P.vertex i`, a clone `s` has neighborhood in the
path equal to the three-vertex subpath consisting of the vertex at `i` and its
two path neighbours.  Replacing `P.vertex i` by `s` therefore preserves the
indexed induced path, its length, and its ordered endpoints.
-/

universe u
variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace IndexedInducedPath

/-- Manuscript Definition 10 for an indexed induced path.

The inequalities make `i` an internal path index.  The `adj_iff` field is the
indexed form of `Γ_P(s) = u-k-v`: the new vertex is adjacent to the clone
`P.vertex i` and exactly the path neighbours of that clone. -/
structure SingleVertexDeformation
    (P : IndexedInducedPath G) (s : V) (i : Fin P.card) : Prop where
  outside : s ∉ Set.range P.vertex
  internal_left : 0 < i.val
  internal_right : i.val + 1 < P.card
  adj_iff : ∀ q : Fin P.card,
    G.Adj s (P.vertex q) ↔
      q = i ∨ G.Adj (P.vertex i) (P.vertex q)

/-- Replace one indexed path vertex while retaining the linear order. -/
def replaceVertex (P : IndexedInducedPath G) (s : V) (i : Fin P.card) :
    Fin P.card → V :=
  fun q => if q = i then s else P.vertex q

@[simp]
theorem replaceVertex_at (P : IndexedInducedPath G) (s : V)
    (i : Fin P.card) :
    P.replaceVertex s i i = s := by
  simp [replaceVertex]

@[simp]
theorem replaceVertex_away (P : IndexedInducedPath G) (s : V)
    {i q : Fin P.card} (hqi : q ≠ i) :
    P.replaceVertex s i q = P.vertex q := by
  simp [replaceVertex, hqi]

/-- Replacing an internal path vertex by a Definition 10 clone gives another
indexed induced path with the same cardinality and linear indexing. -/
def deform (P : IndexedInducedPath G) {s : V} {i : Fin P.card}
    (h : P.SingleVertexDeformation s i) : IndexedInducedPath G where
  card := P.card
  nonempty := P.nonempty
  vertex := P.replaceVertex s i
  injective := by
    intro p q hpq
    by_cases hp : p = i
    · subst p
      by_cases hq : q = i
      · exact hq.symm
      · have hsq : s = P.vertex q := by
          simpa [replaceVertex, hq] using hpq
        exact (h.outside ⟨q, hsq.symm⟩).elim
    · by_cases hq : q = i
      · subst q
        have hps : P.vertex p = s := by
          simpa [replaceVertex, hp] using hpq
        exact (h.outside ⟨p, hps⟩).elim
      · exact P.injective (by
          simpa [replaceVertex, hp, hq] using hpq)
  adj_iff := by
    intro p q
    by_cases hp : p = i
    · subst p
      by_cases hq : q = i
      · subst q
        apply iff_of_false
        · simpa [replaceVertex] using G.loopless.irrefl s
        · omega
      · simp only [replaceVertex, if_pos, if_neg hq]
        rw [h.adj_iff q, P.adj_iff i q]
        simp [hq]
    · by_cases hq : q = i
      · subst q
        simp only [replaceVertex, if_neg hp, if_pos]
        have hs :
            G.Adj s (P.vertex p) ↔
              i.val + 1 = p.val ∨ p.val + 1 = i.val := by
          rw [h.adj_iff p, P.adj_iff i p]
          simp [hp]
        constructor
        · intro hps
          rcases hs.mp hps.symm with hip | hpi
          · exact Or.inr hip
          · exact Or.inl hpi
        · intro hlin
          apply (hs.mpr ?_).symm
          rcases hlin with hpi | hip
          · exact Or.inr hpi
          · exact Or.inl hip
      · simp only [replaceVertex, if_neg hp, if_neg hq]
        exact P.adj_iff p q

@[simp]
theorem deform_card (P : IndexedInducedPath G) {s : V}
    {i : Fin P.card} (h : P.SingleVertexDeformation s i) :
    (P.deform h).card = P.card :=
  rfl

@[simp]
theorem deform_vertex_at (P : IndexedInducedPath G) {s : V}
    {i : Fin P.card} (h : P.SingleVertexDeformation s i) :
    (P.deform h).vertex i = s := by
  simp [deform]

@[simp]
theorem deform_vertex_away (P : IndexedInducedPath G) {s : V}
    {i q : Fin P.card} (h : P.SingleVertexDeformation s i) (hqi : q ≠ i) :
    (P.deform h).vertex q = P.vertex q := by
  simp [deform, hqi]

/-- A Definition 10 path deformation does not alter the first endpoint. -/
theorem deform_first_endpoint (P : IndexedInducedPath G) {s : V}
    {i : Fin P.card} (h : P.SingleVertexDeformation s i) :
    (P.deform h).vertex ⟨0, P.nonempty⟩ =
      P.vertex ⟨0, P.nonempty⟩ := by
  apply deform_vertex_away
  intro hzero
  have hval : 0 = i.val := congrArg Fin.val hzero
  have hi : 0 < i.val := h.internal_left
  omega

/-- A Definition 10 path deformation does not alter the last endpoint. -/
theorem deform_last_endpoint (P : IndexedInducedPath G) {s : V}
    {i : Fin P.card} (h : P.SingleVertexDeformation s i) :
    (P.deform h).vertex
        ⟨P.card - 1, by
          change P.card - 1 < P.card
          exact Nat.sub_lt P.nonempty (by decide)⟩ =
      P.vertex
        ⟨P.card - 1, Nat.sub_lt P.nonempty (by decide)⟩ := by
  apply deform_vertex_away
  intro hlast
  have hval : P.card - 1 = i.val := congrArg Fin.val hlast
  have hi : i.val + 1 < P.card := h.internal_right
  have hcard : 0 < P.card := P.nonempty
  omega

end IndexedInducedPath

/-- One reversible-generator step of the induced-path deformation closure from
Definition 12.  The reversibility theorem is proved separately, rather than
built into the relation as an assumption. -/
def InducedPathDeformationStep
    (G : SimpleGraph V) (P Q : IndexedInducedPath G) : Prop :=
  ∃ (s : V) (i : Fin P.card)
      (h : P.SingleVertexDeformation s i),
    Q = P.deform h

/-- Finite closure generated by Definition 10 path deformations. -/
inductive InInducedPathDeformationClosure
    (G : SimpleGraph V) :
    IndexedInducedPath G → IndexedInducedPath G → Prop
  | refl (P : IndexedInducedPath G) :
      InInducedPathDeformationClosure G P P
  | tail {P Q R : IndexedInducedPath G} :
      InInducedPathDeformationClosure G P Q →
      InducedPathDeformationStep G Q R →
      InInducedPathDeformationClosure G P R

/-- A single path deformation belongs to the generated closure. -/
theorem InducedPathDeformationStep.inClosure
    {P Q : IndexedInducedPath G}
    (h : InducedPathDeformationStep G P Q) :
    InInducedPathDeformationClosure G P Q :=
  InInducedPathDeformationClosure.tail
    (InInducedPathDeformationClosure.refl P) h

/-- Every single deformation preserves path cardinality. -/
theorem InducedPathDeformationStep.card_eq
    {P Q : IndexedInducedPath G}
    (h : InducedPathDeformationStep G P Q) :
    Q.card = P.card := by
  rcases h with ⟨s, i, hdef, rfl⟩
  rfl

/-- Every finite deformation sequence preserves path cardinality, matching the
length part of manuscript Definition 12. -/
theorem InInducedPathDeformationClosure.card_eq
    {P Q : IndexedInducedPath G}
    (h : InInducedPathDeformationClosure G P Q) :
    Q.card = P.card := by
  induction h with
  | refl => rfl
  | tail hPQ hQR ih =>
      exact hQR.card_eq.trans ih

/-- Concatenate two finite induced-path deformation sequences. -/
theorem InInducedPathDeformationClosure.trans
    {P Q R : IndexedInducedPath G}
    (hPQ : InInducedPathDeformationClosure G P Q)
    (hQR : InInducedPathDeformationClosure G Q R) :
    InInducedPathDeformationClosure G P R := by
  induction hQR with
  | refl => exact hPQ
  | tail hQR hstep ih =>
      exact InInducedPathDeformationClosure.tail ih hstep

end SimpleGraph