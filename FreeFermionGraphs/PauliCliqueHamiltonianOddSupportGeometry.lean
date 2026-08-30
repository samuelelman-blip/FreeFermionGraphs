import FreeFermionGraphs.PauliCliqueHamiltonianOddSupport

/-!
# Geometry carried by the odd Pauli Krylov support

The ordinary cardinality-three branch of Lemma 7 says that the three path
neighbours of an external vertex induce a path of length two.  This module
turns that shape into the literal `SingleVertexDeformation` object required
by the Pauli cancellation theorem.  Thus the Definition 10 branch is derived
from the exhaustive odd-support classification rather than stored as extra
data.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace IndexedInducedPath

variable {G : SimpleGraph V}

/-- If two distinct path vertices both neighbor `center`, they exhaust all
path neighbours of `center`. -/
theorem eq_left_or_right_of_adjacent_to_two
    (P : IndexedInducedPath G)
    {left center right q : Fin P.card}
    (hlr : left ≠ right)
    (hleft : G.Adj (P.vertex center) (P.vertex left))
    (hright : G.Adj (P.vertex center) (P.vertex right))
    (hq : G.Adj (P.vertex center) (P.vertex q)) :
    q = left ∨ q = right := by
  have hlrVal : left.val ≠ right.val := by
    intro h
    exact hlr (Fin.ext h)
  have hl := (P.adj_iff center left).1 hleft
  have hr := (P.adj_iff center right).1 hright
  have hq' := (P.adj_iff center q).1 hq
  have hval : q.val = left.val ∨ q.val = right.val := by
    rcases hl with hl | hl <;>
      rcases hr with hr | hr <;>
      rcases hq' with hq' | hq' <;> omega
  exact hval.imp Fin.ext Fin.ext

/-- A path vertex with two distinct path neighbours is internal. -/
theorem isInteriorIndex_of_two_adjacent
    (P : IndexedInducedPath G)
    {left center right : Fin P.card}
    (hlr : left ≠ right)
    (hleft : G.Adj (P.vertex center) (P.vertex left))
    (hright : G.Adj (P.vertex center) (P.vertex right)) :
    0 < center.val ∧ center.val + 1 < P.card := by
  have hlrVal : left.val ≠ right.val := by
    intro h
    exact hlr (Fin.ext h)
  have hl := (P.adj_iff center left).1 hleft
  have hr := (P.adj_iff center right).1 hright
  rcases hl with hl | hl <;> rcases hr with hr | hr <;>
    constructor <;> omega

/-- An exact external induced-path triple is precisely a Definition 10
single-vertex deformation at its middle index. -/
theorem singleVertexDeformation_of_inducedPathTriple
    (P : IndexedInducedPath G) {j : V}
    (hjP : j ∉ Set.range P.vertex)
    {left center right : Fin P.card}
    (hlc : left ≠ center) (hlr : left ≠ right)
    (hcr : center ≠ right)
    (hjLeft : G.Adj j (P.vertex left))
    (hjCenter : G.Adj j (P.vertex center))
    (hjRight : G.Adj j (P.vertex right))
    (hexact : ∀ q : Fin P.card,
      G.Adj j (P.vertex q) →
        q = left ∨ q = center ∨ q = right)
    (hpath : G.IsInducedPathTriple
      (P.vertex left) (P.vertex center) (P.vertex right)) :
    P.SingleVertexDeformation j center := by
  have hleft : G.Adj (P.vertex center) (P.vertex left) :=
    hpath.1.symm
  have hright : G.Adj (P.vertex center) (P.vertex right) :=
    hpath.2.1
  have hinterior := P.isInteriorIndex_of_two_adjacent hlr hleft hright
  refine ⟨hjP, hinterior.1, hinterior.2, ?_⟩
  intro q
  constructor
  · intro hjq
    rcases hexact q hjq with hql | hqc | hqr
    · subst q
      exact Or.inr hleft
    · exact Or.inl hqc
    · subst q
      exact Or.inr hright
  · rintro (rfl | hcq)
    · exact hjCenter
    · rcases P.eq_left_or_right_of_adjacent_to_two hlr
          hleft hright hcq with rfl | rfl
      · exact hjLeft
      · exact hjRight

/-- The support cases after converting the ordinary path triple into a
literal deformation.  Only the endpoint branches remain to be treated by
tree extension and generalized-cycle geometry. -/
inductive ExternalKrylovGeometryCase
    (P : IndexedInducedPath G) (j : V) : Prop
  | endpoint
      (q : Fin P.card)
      (adjacent : G.Adj j (P.vertex q))
      (endpointIndex : P.IsEndpointIndex q)
      (exact : ∀ k : Fin P.card,
        G.Adj j (P.vertex k) → k = q) :
      ExternalKrylovGeometryCase P j
  | deformation
      (i : Fin P.card)
      (data : P.SingleVertexDeformation j i) :
      ExternalKrylovGeometryCase P j
  | endpointTriple
      (p q r : Fin P.card)
      (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
      (adjacentP : G.Adj j (P.vertex p))
      (adjacentQ : G.Adj j (P.vertex q))
      (adjacentR : G.Adj j (P.vertex r))
      (exact : ∀ k : Fin P.card,
        G.Adj j (P.vertex k) → k = p ∨ k = q ∨ k = r)
      (shape : P.ThreeNeighborEndpointCase p q r) :
      ExternalKrylovGeometryCase P j

/-- Refine the exhaustive external odd-neighbour classification into the
geometry used by the three one-step operator branches. -/
theorem ExternalOddNeighborCase.toKrylovGeometry
    (P : IndexedInducedPath G) {j : V}
    (hjP : j ∉ Set.range P.vertex)
    (h : P.ExternalOddNeighborCase j) :
    P.ExternalKrylovGeometryCase j := by
  rcases h with
    ⟨q, hq, hqEndpoint, hexact⟩ |
    ⟨p, q, r, hpq, hpr, hqr, hp, hq, hr, hexact, hshape⟩ |
    ⟨p, q, r, hpq, hpr, hqr, hp, hq, hr, hexact, hshape⟩
  · exact .endpoint q hq hqEndpoint hexact
  · rcases hshape with hpath | hpath | hpath
    · exact .deformation p
        (P.singleVertexDeformation_of_inducedPathTriple hjP
          hpq.symm hqr hpr hq hp hr
          (by intro k hk
              rcases hexact k hk with rfl | rfl | rfl
              · exact Or.inr (Or.inl rfl)
              · exact Or.inl rfl
              · exact Or.inr (Or.inr rfl)) hpath)
    · exact .deformation q
        (P.singleVertexDeformation_of_inducedPathTriple hjP
          hpq hpr hqr hp hq hr hexact hpath)
    · exact .deformation r
        (P.singleVertexDeformation_of_inducedPathTriple hjP
          hpr hpq hqr.symm hp hr hq
          (by intro k hk
              rcases hexact k hk with rfl | rfl | rfl
              · exact Or.inl rfl
              · exact Or.inr (Or.inr rfl)
              · exact Or.inr (Or.inl rfl)) hpath)
  · exact .endpointTriple p q r hpq hpr hqr hp hq hr hexact hshape

end IndexedInducedPath

end SimpleGraph
