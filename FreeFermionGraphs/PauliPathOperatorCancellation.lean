import FreeFermionGraphs.PauliCliqueHamiltonianExtension
import FreeFermionGraphs.InducedPathDeformation

/-!
# Pauli cancellation for a single path deformation

The first external-neighbour branch in Appendix E pairs a path term with the
term obtained by replacing one internal path vertex by its Definition 10
clone.  This file proves the underlying ordered-product cancellation.  The
two suffixes contribute the same crossing sign, while the clone and replaced
term anticommute, so the two products have opposite signs.
-/

universe u w

variable {V : Type u}

namespace SimpleGraph

namespace IndexedInducedPath

variable {G : SimpleGraph V}

/-- The ordered vertex list of a deformed path is the original list with the
deformation index replaced by the clone. -/
theorem vertexList_deform_eq_set
    (P : IndexedInducedPath G) {s : V} {i : Fin P.card}
    (h : P.SingleVertexDeformation s i) :
    List.ofFn (P.deform h).vertex =
      (List.ofFn P.vertex).set i.val s := by
  apply List.ext_getElem
  · simp
  · intro n hnDeform hnSet
    have hn : n < P.card := by simpa using hnDeform
    let q : Fin P.card := ⟨n, hn⟩
    by_cases hqi : q = i
    · have hni : n = i.val := congrArg Fin.val hqi
      subst n
      simp [deform, replaceVertex]
    · have hni : n ≠ i.val := by
        intro hEq
        apply hqi
        apply Fin.ext
        exact hEq
      have hindexNe :
          (⟨n, by simpa using hnDeform⟩ : Fin P.card) ≠ i := by
        intro hEq
        exact hni (congrArg Fin.val hEq)
      simp only [List.getElem_ofFn, deform, replaceVertex,
        if_neg hindexNe]
      rw [List.getElem_set_ne hni.symm hnSet]
      simp only [List.getElem_ofFn]

/-- On the unchanged suffix after a Definition 10 replacement, the clone and
the replaced path vertex have identical frustration-neighbour counts. -/
theorem SingleVertexDeformation.suffixNeighborCount_eq
    (P : IndexedInducedPath G) {s : V} {i : Fin P.card}
    (h : P.SingleVertexDeformation s i) :
    PauliFrustrationRepresentation.listNeighborCount G s
        ((List.ofFn P.vertex).drop (i.val + 1)) =
      PauliFrustrationRepresentation.listNeighborCount G (P.vertex i)
        ((List.ofFn P.vertex).drop (i.val + 1)) := by
  classical
  unfold PauliFrustrationRepresentation.listNeighborCount
  apply List.countP_congr
  intro x hx
  obtain ⟨j, hj, hx⟩ := (List.mem_drop_iff_getElem).1 hx
  simp only [List.length_ofFn] at hj
  let q : Fin P.card := ⟨i.val + 1 + j, by omega⟩
  have hqx : P.vertex q = x := by
    simpa only [List.getElem_ofFn, q] using hx
  have hqi : q ≠ i := by
    intro hEq
    have hval := congrArg Fin.val hEq
    dsimp [q] at hval
    omega
  have hadj : G.Adj s (P.vertex q) ↔
      G.Adj (P.vertex i) (P.vertex q) := by
    rw [h.adj_iff q]
    simp [hqi]
  simpa [hqx] using hadj

end IndexedInducedPath

namespace PauliFrustrationRepresentation

variable {G : SimpleGraph V} {A : Type w} [Ring A]

/-- Replacing one displayed factor by an adjacent term reverses the final
product sign, provided the two terms have the same crossing parity with the
unchanged suffix. -/
theorem listOperator_replacement_eq_neg
    (H : G.PauliFrustrationRepresentation A)
    (pre suffix : List V) {k s : V}
    (hks : G.Adj k s)
    (hcount : listNeighborCount G s suffix =
      listNeighborCount G k suffix) :
    H.listOperator (pre ++ k :: suffix) * H.term s =
      -(H.listOperator (pre ++ s :: suffix) * H.term k) := by
  let L := H.listOperator pre
  let Rop := H.listOperator suffix
  have hksAnti : H.term k * H.term s =
      -(H.term s * H.term k) :=
    H.adj_iff_anticommute.mp hks
  have hsCross := H.term_mul_listOperator s suffix
  have hkCross := H.term_mul_listOperator k suffix
  rw [H.listOperator_append pre (k :: suffix),
    H.listOperator_append pre (s :: suffix),
    H.listOperator_cons, H.listOperator_cons]
  change (L * (H.term k * Rop)) * H.term s =
    -((L * (H.term s * Rop)) * H.term k)
  rcases Nat.even_or_odd (listNeighborCount G s suffix) with heven | hodd
  · rw [heven.neg_one_pow] at hsCross
    rw [← hcount, heven.neg_one_pow] at hkCross
    simp only [one_mul] at hsCross hkCross
    calc
      (L * (H.term k * Rop)) * H.term s =
          L * H.term k * (Rop * H.term s) := by
            simp only [mul_assoc]
      _ = L * H.term k * (H.term s * Rop) := by rw [← hsCross]
      _ = L * (H.term k * H.term s) * Rop := by
            simp only [mul_assoc]
      _ = L * (-(H.term s * H.term k)) * Rop := by rw [hksAnti]
      _ = -(L * H.term s * (H.term k * Rop)) := by
            simp only [mul_assoc, mul_neg, neg_mul]
      _ = -(L * H.term s * (Rop * H.term k)) := by rw [hkCross]
      _ = -((L * (H.term s * Rop)) * H.term k) := by
            simp only [mul_assoc]
  · rw [hodd.neg_one_pow] at hsCross
    rw [← hcount, hodd.neg_one_pow] at hkCross
    simp only [neg_one_mul] at hsCross hkCross
    have hsReverse : Rop * H.term s =
        -(H.term s * Rop) := by
      simpa only [neg_neg] using
        (congrArg (fun x : A => -x) hsCross).symm
    have hkReverse : Rop * H.term k =
        -(H.term k * Rop) := by
      simpa only [neg_neg] using
        (congrArg (fun x : A => -x) hkCross).symm
    calc
      (L * (H.term k * Rop)) * H.term s =
          L * H.term k * (Rop * H.term s) := by
            simp only [mul_assoc]
      _ = L * H.term k * (-(H.term s * Rop)) := by rw [hsReverse]
      _ = -(L * (H.term k * H.term s) * Rop) := by
            simp only [mul_assoc, mul_neg]
      _ = -(L * (-(H.term s * H.term k)) * Rop) := by rw [hksAnti]
      _ = L * H.term s * (H.term k * Rop) := by
            simp only [mul_assoc, mul_neg, neg_mul, neg_neg]
      _ = -(L * H.term s * (-(H.term k * Rop))) := by simp
      _ = -(L * H.term s * (Rop * H.term k)) := by rw [← hkReverse]
      _ = -((L * (H.term s * Rop)) * H.term k) := by
            simp only [mul_assoc]

/-- Additive form of the replacement cancellation used in Eq. (E12). -/
theorem listOperator_replacement_add_eq_zero
    (H : G.PauliFrustrationRepresentation A)
    (pre suffix : List V) {k s : V}
    (hks : G.Adj k s)
    (hcount : listNeighborCount G s suffix =
      listNeighborCount G k suffix) :
    H.listOperator (pre ++ k :: suffix) * H.term s +
      H.listOperator (pre ++ s :: suffix) * H.term k = 0 := by
  rw [H.listOperator_replacement_eq_neg pre suffix hks hcount]
  simp

/-- Eq. (E12)'s raw operator cancellation for one literal Definition 10 path
deformation.  The deformed path replaces `P.vertex i` by `s`; multiplying the
two path operators by the opposite exchanged term gives a zero sum. -/
theorem pathOperator_deformation_add_eq_zero
    (H : G.PauliFrustrationRepresentation A)
    (P : IndexedInducedPath G) {s : V} {i : Fin P.card}
    (h : P.SingleVertexDeformation s i) :
    H.pathOperator P * H.term s +
      H.pathOperator (P.deform h) * H.term (P.vertex i) = 0 := by
  let vertices := List.ofFn P.vertex
  let pre := vertices.take i.val
  let suffix := vertices.drop (i.val + 1)
  have hi : i.val < vertices.length := by
    simp [vertices]
  have hOriginal : vertices = pre ++ P.vertex i :: suffix := by
    calc
      vertices = vertices.take i.val ++ vertices.drop i.val :=
        (List.take_append_drop i.val vertices).symm
      _ = vertices.take i.val ++
          vertices[i.val] :: vertices.drop (i.val + 1) := by
            rw [List.drop_eq_getElem_cons hi]
      _ = pre ++ P.vertex i :: suffix := by
            simp only [pre, suffix, List.getElem_ofFn, vertices]
  have hDeformed : List.ofFn (P.deform h).vertex =
      pre ++ s :: suffix := by
    rw [P.vertexList_deform_eq_set h]
    rw [List.set_eq_take_append_cons_drop]
    simp [vertices, pre, suffix]
  change H.listOperator vertices * H.term s +
    H.listOperator (List.ofFn (P.deform h).vertex) *
      H.term (P.vertex i) = 0
  rw [hOriginal, hDeformed]
  apply H.listOperator_replacement_add_eq_zero
  · exact (h.adj_iff i).2 (Or.inl rfl) |>.symm
  · exact h.suffixNeighborCount_eq P

end PauliFrustrationRepresentation
end SimpleGraph
