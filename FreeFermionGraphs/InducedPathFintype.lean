import FreeFermionGraphs.InducedPathDeformationLocalWeights

/-!
# Finiteness of indexed induced paths

Matrix multiplication for the Eq. (E1) hopping matrix requires a finite index
type.  When the ambient graph has finitely many vertices, an indexed induced
path is encoded by its bounded cardinality together with its injective vertex
map.  This supplies the finite instances used by matrix powers and weighted
walk sums in manuscript Lemma 18.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace IndexedInducedPath

variable {G : SimpleGraph V}

/-- Equality of cardinalities and heterogeneous equality of vertex maps
determine an indexed induced path; the remaining fields are propositions. -/
theorem ext_card_vertex {P Q : IndexedInducedPath G}
    (hcard : P.card = Q.card) (hvertex : HEq P.vertex Q.vertex) :
    P = Q := by
  cases P with
  | mk pcard pnonempty pvertex pinjective padj =>
      cases Q with
      | mk qcard qnonempty qvertex qinjective qadj =>
          dsimp at hcard hvertex
          subst qcard
          have hv : pvertex = qvertex := eq_of_heq hvertex
          subst qvertex
          rfl

/-- A finite code for an indexed induced path.  Injectivity bounds the path
cardinality by the ambient vertex count. -/
noncomputable def finiteCode [Fintype V] (P : IndexedInducedPath G) :
    Σ n : Fin (Fintype.card V + 1), Fin n.val → V :=
  ⟨⟨P.card, by
      have hle : P.card ≤ Fintype.card V :=
        by simpa using Fintype.card_le_of_injective P.vertex P.injective
      omega⟩,
    P.vertex⟩

theorem finiteCode_injective [Fintype V] :
    Function.Injective (finiteCode (G := G)) := by
  intro P Q hcode
  have hparts := Sigma.mk.inj hcode
  have hcard : P.card = Q.card := congrArg Fin.val hparts.1
  apply ext_card_vertex hcard
  exact hparts.2

/-- There are finitely many indexed induced paths in a finite graph. -/
noncomputable instance [Fintype V] : Fintype (IndexedInducedPath G) :=
  Fintype.ofInjective (finiteCode (G := G)) finiteCode_injective

end IndexedInducedPath

/-- There are finitely many rooted induced paths in a finite graph. -/
noncomputable instance rootedInducedPathFintype
    {G : SimpleGraph V} [Fintype V] (root : V) :
    Fintype (RootedInducedPath G root) :=
  Fintype.ofInjective RootedInducedPath.path (by
    intro P Q hpath
    cases P
    cases Q
    cases hpath
    rfl)

end SimpleGraph
