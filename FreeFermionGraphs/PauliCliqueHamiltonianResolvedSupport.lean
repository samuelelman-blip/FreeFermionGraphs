import FreeFermionGraphs.PauliCliqueHamiltonianResolvedGeometry

/-!
# Constructive support classification for one physical Hamiltonian term

This module combines the exhaustive odd-support theorem with the constructed
Appendix E geometry.  Every original Hamiltonian vertex that anticommutes
with a clique-rooted path is either its terminal vertex or an external vertex
in one of the four resolved geometric cases.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace RootedInducedPath

variable {G : SimpleGraph V} {K : Set V}

/-- The fully constructed alternatives for one original vertex in the exact
anticommuting support of a clique-rooted path. -/
inductive ResolvedOriginalAnticommutingCase
    (P : CliqueRootedInducedPath G K) (j : V) : Prop
  | terminal
      (terminalVertex : P.path.terminalVertex = some j) :
      ResolvedOriginalAnticommutingCase P j
  | external
      (outside : some j ∉ Set.range P.path.vertex)
      (geometry : P.ResolvedExternalKrylovGeometryCase j) :
      ResolvedOriginalAnticommutingCase P j

/-- Every original Hamiltonian vertex that anticommutes with the path is
resolved into terminal contraction or literal Appendix E geometry. -/
theorem resolvedOriginalAnticommutingCase
    (P : CliqueRootedInducedPath G K)
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree)
    {j : V} (hanti : P.path.AnticommutesWith (some j)) :
    P.ResolvedOriginalAnticommutingCase j := by
  rcases P.originalAnticommutingCase hK hclaw hanti with
    hterminal | ⟨houtside, hodd⟩
  · exact .terminal hterminal
  · exact .external houtside
      (SimpleGraph.RootedInducedPath.IndexedInducedPath.ExternalKrylovGeometryCase.resolve
        P hK.isClique houtside
          (hodd.toKrylovGeometry P.path houtside))

end RootedInducedPath

end SimpleGraph
