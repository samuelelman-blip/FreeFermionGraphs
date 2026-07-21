import FreeFermionGraphs.Lemma11BInPathTwoNeighbors
import FreeFermionGraphs.Lemma11BHoleVertexDegree

/-!
# Lemma 11(a): endpoint degree

Corollary 12 identifies a repeated anticommuting vertex with the first
introduced vertex of an earlier path block.  That vertex remains on the
block's final hole, hence has degree two there.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- The first introduced vertex survives the complete path block and has
the two hole neighbors forced by inducedness. -/
theorem firstIntroduced_finalDegree_eq_two
    (D : ConcretePathDeformation O Cprime)
    (L : Definition19GlobalOverlapPathOrder D) :
    D.finalHole.externalDegree
        (D.deformation.step D.firstIndex).introduced = 2 := by
  obtain ⟨q, hq⟩ := D.introduced_mem_finalHole L D.firstIndex
  rw [← hq]
  exact D.finalHole.externalDegree_vertex_eq_two q

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
