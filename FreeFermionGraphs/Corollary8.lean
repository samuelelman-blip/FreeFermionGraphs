import FreeFermionGraphs.Corollary7

/-!
# Corollary 8

The path components of a fixed-pairing-type deformation are distinct vertex
subsets.  Corollary 7 justifies forgetting the original occurrence indices;
our representation of `O.paths` as a set of subsets then makes distinctness
an injectivity statement for subtype coercion.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

/-- A path component belonging to the fixed-pairing family `O`. -/
abbrev PathComponent (O : FixedPairingPathFamily G) :=
  {P : Set V // P ∈ O.paths}

/-- Corollary 8: path components of `O` are distinct as vertex subsets. -/
theorem corollary8 (O : FixedPairingPathFamily G) :
    Function.Injective (fun P : PathComponent O => (P : Set V)) := by
  intro P Q hPQ
  exact Subtype.ext hPQ

end FixedPairingPathFamily

end SimpleGraph
