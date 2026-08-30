import FreeFermionGraphs.PauliPathOperator
import FreeFermionGraphs.InducedPathTree

/-!
# Pauli path operators under one-vertex extension

The tree part of the manuscript's one-step commutator calculation uses the
ordered product identity for appending one terminal vertex to an induced path.
This module proves that identity from the literal ordered-prefix definition of
`IsOneVertexExtension`.  No coupling-square or transition coefficient is
assumed here.
-/

universe u w

variable {V : Type u}

namespace SimpleGraph

namespace IndexedInducedPath

variable {G : SimpleGraph V}

/-- The final vertex in the displayed order of a nonempty indexed path. -/
def terminalVertex (P : IndexedInducedPath G) : V :=
  P.vertex ⟨P.card - 1, Nat.sub_lt P.nonempty (by decide)⟩

end IndexedInducedPath

namespace RootedInducedPath

variable {G : SimpleGraph V} {root : V}

/-- A literal one-vertex extension appends its terminal vertex to the complete
ordered vertex list of the shorter path. -/
theorem IsOneVertexExtension.vertexList_eq_concat
    {P Q : RootedInducedPath G root}
    (h : P.IsOneVertexExtension Q) :
    List.ofFn Q.path.vertex =
      (List.ofFn P.path.vertex).concat Q.path.terminalVertex := by
  rcases h with ⟨hcard, hprefix⟩
  rw [List.ofFn_congr hcard.symm Q.path.vertex, List.ofFn_succ']
  apply List.concat_inj.mpr
  constructor
  · apply congrArg List.ofFn
    funext i
    calc
      Q.path.vertex (Fin.cast hcard i.castSucc) =
          Q.path.vertex ⟨i.val, by omega⟩ := by
            apply congrArg Q.path.vertex
            apply Fin.ext
            rfl
      _ = P.path.vertex i := hprefix i
  · simp only [IndexedInducedPath.terminalVertex]
    apply congrArg Q.path.vertex
    apply Fin.ext
    simp only [Fin.val_cast, Fin.val_last]
    omega

end RootedInducedPath

namespace PauliFrustrationRepresentation

variable {G : SimpleGraph V} {A : Type w} [Ring A]

/-- Ordered term products turn list concatenation into multiplication. -/
theorem listOperator_append
    (H : G.PauliFrustrationRepresentation A)
    (left right : List V) :
    H.listOperator (left ++ right) =
      H.listOperator left * H.listOperator right := by
  simp [listOperator, List.map_append]

/-- Appending the terminal vertex to a rooted induced path appends its Pauli
term on the right of the shorter path operator. -/
theorem pathOperator_extension
    (H : G.PauliFrustrationRepresentation A)
    {root : V} {P Q : RootedInducedPath G root}
    (h : P.IsOneVertexExtension Q) :
    H.pathOperator Q.path =
      H.pathOperator P.path * H.term Q.path.terminalVertex := by
  change H.listOperator (List.ofFn Q.path.vertex) =
    H.listOperator (List.ofFn P.path.vertex) * H.term Q.path.terminalVertex
  rw [h.vertexList_eq_concat]
  simp [listOperator]

end PauliFrustrationRepresentation
end SimpleGraph
