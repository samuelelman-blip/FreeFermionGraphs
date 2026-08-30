import FreeFermionGraphs.BubbleWandHoop
import FreeFermionGraphs.PauliCliqueHamiltonianResolvedAction

/-!
# Constructing the even-hoop bubble-wand arc

Ordered bubble-wand provenance identifies the handle with a literal prefix
of the clique-rooted source path.  When the constructed hoop is even, its
alternating labeling then supplies the concrete Definition 18 arc.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace IndexedInducedPath

variable {G : SimpleGraph V}

/-- Transporting an index along equality of indexed paths transports its
vertex without changing the displayed vertex. -/
theorem vertex_cast_of_eq {P Q : IndexedInducedPath G}
    (h : P = Q) (i : Fin P.card) :
    Q.vertex (Fin.cast (congrArg IndexedInducedPath.card h) i) =
      P.vertex i := by
  subst Q
  rfl

end IndexedInducedPath

namespace RootedInducedPath

variable {G : SimpleGraph V} {K : Set V}

/-- The original carrier of a prefix ending at an original-tail index is
exactly the corresponding ordered prefix of the original tail. -/
theorem originalCarrier_initialSegment_originalTail
    (P : CliqueRootedInducedPath G K) (htail : 2 ≤ P.path.card)
    (q : Fin (P.originalTail htail).card) :
    (P.initialSegment (P.originalTailIndex htail q)).originalCarrier =
      {v | ∃ r : Fin (P.originalTail htail).card,
        r.val ≤ q.val ∧ (P.originalTail htail).vertex r = v} := by
  ext v
  constructor
  · rintro ⟨i, hi⟩
    have hiPositive : 0 < i.val := by
      by_contra hiZero
      have hiValZero : i.val = 0 := by omega
      change P.path.vertex ⟨i.val, by
          have hiLt := i.isLt
          change i.val < q.val + 2 at hiLt
          have hqLt := q.isLt
          change q.val < P.path.card - 1 at hqLt
          omega⟩ = some v at hi
      have hiEq :
          (⟨i.val, by
            have hiLt := i.isLt
            change i.val < q.val + 2 at hiLt
            have hqLt := q.isLt
            change q.val < P.path.card - 1 at hqLt
            omega⟩ : Fin P.path.card) =
          ⟨0, P.path.nonempty⟩ := by
        apply Fin.ext
        exact hiValZero
      rw [hiEq, P.root_eq] at hi
      simp at hi
    let r : Fin (P.originalTail htail).card :=
      ⟨i.val - 1, by
        change i.val - 1 < P.path.card - 1
        have hiLt := i.isLt
        change i.val < q.val + 2 at hiLt
        have hqLt := q.isLt
        change q.val < P.path.card - 1 at hqLt
        omega⟩
    refine ⟨r, ?_, ?_⟩
    · have hiLt := i.isLt
      change i.val < q.val + 2 at hiLt
      dsimp [r]
      omega
    · change P.path.vertex ⟨i.val, by
          have hiLt := i.isLt
          change i.val < q.val + 2 at hiLt
          have hqLt := q.isLt
          change q.val < P.path.card - 1 at hqLt
          omega⟩ = some v at hi
      have hindex :
          (⟨i.val, by
            have hiLt := i.isLt
            change i.val < q.val + 2 at hiLt
            have hqLt := q.isLt
            change q.val < P.path.card - 1 at hqLt
            omega⟩ : Fin P.path.card) =
            P.originalTailIndex htail r := by
        apply Fin.ext
        dsimp [r, originalTailIndex]
        omega
      rw [hindex, P.path_vertex_originalTailIndex htail r] at hi
      exact Option.some.inj hi
  · rintro ⟨r, hrq, hr⟩
    let i : Fin
        (P.initialSegment (P.originalTailIndex htail q)).path.card :=
      ⟨r.val + 1, by
        change r.val + 1 < q.val + 2
        omega⟩
    refine ⟨i, ?_⟩
    change P.path.vertex ⟨i.val, by
        have hiLt := i.isLt
        change i.val < q.val + 2 at hiLt
        have hqLt := q.isLt
        change q.val < P.path.card - 1 at hqLt
        omega⟩ = some v
    have hindex :
        (⟨i.val, by
          have hiLt := i.isLt
          change i.val < q.val + 2 at hiLt
          have hqLt := q.isLt
          change q.val < P.path.card - 1 at hqLt
          omega⟩ : Fin P.path.card) =
          P.originalTailIndex htail r := by
      apply Fin.ext
      dsimp [i, originalTailIndex]
    change P.originalTailVertex htail r = v at hr
    rw [hindex, P.path_vertex_originalTailIndex htail r]
    exact congrArg some hr

/-- Ordered provenance constructs the rooted handle target of a bubble wand. -/
theorem exists_bubbleWandHandleTarget
    (P : CliqueRootedInducedPath G K) (B : BubbleWand G)
    (hordered : ∃ htail : 2 ≤ P.path.card,
      B.path = P.originalTail htail) :
    ∃ Q : CliqueRootedInducedPath G K,
      Q.originalCarrier = B.handle := by
  obtain ⟨htail, hpath⟩ := hordered
  let split : Fin (P.originalTail htail).card :=
    Fin.cast (congrArg IndexedInducedPath.card hpath) B.split
  let Q := P.initialSegment (P.originalTailIndex htail split)
  refine ⟨Q, ?_⟩
  rw [P.originalCarrier_initialSegment_originalTail htail split]
  ext v
  constructor
  · rintro ⟨r, hrl, hr⟩
    let s : Fin B.path.card :=
      Fin.cast (congrArg IndexedInducedPath.card hpath).symm r
    refine ⟨s, ?_, ?_⟩
    · have hsplitVal : split.val = B.split.val := rfl
      change s.val ≤ B.split.val
      change r.val ≤ B.split.val
      omega
    · rw [← hr]
      exact IndexedInducedPath.vertex_cast_of_eq hpath.symm r
  · rintro ⟨s, hsl, hs⟩
    let r : Fin (P.originalTail htail).card :=
      Fin.cast (congrArg IndexedInducedPath.card hpath) s
    refine ⟨r, ?_, ?_⟩
    · have hsplitVal : split.val = B.split.val := rfl
      change r.val ≤ split.val
      change s.val ≤ B.split.val
      exact hsl
    · rw [← hs]
      exact IndexedInducedPath.vertex_cast_of_eq hpath s

end RootedInducedPath

/-- An even constructed hoop produces the literal Definition 18 arc from
the source path to its rooted handle. -/
theorem exists_evenHoopBubbleWandArc
    {G : SimpleGraph V} {K : Set V}
    (P : CliqueRootedInducedPath G K) (B : BubbleWand G)
    (hsource : P.originalCarrier = Set.range B.path.vertex)
    (hordered : ∃ htail : 2 ≤ P.path.card,
      B.path = P.originalTail htail)
    (hEven : Even B.hoopHole.card) :
    ∃ Q : CliqueRootedInducedPath G K,
      EvenHoopBubbleWandArc G K P Q := by
  obtain ⟨Q, htarget⟩ := P.exists_bubbleWandHandleTarget B hordered
  obtain ⟨k, E, hcarrier⟩ := B.hoopHole.exists_evenHoleLabeling hEven
  refine ⟨Q, B, hsource, htarget, k, E, ?_⟩
  exact hcarrier.trans B.range_hoopHole

end SimpleGraph
