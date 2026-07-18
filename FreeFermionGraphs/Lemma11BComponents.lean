import FreeFermionGraphs.Lemma11BPredecessor

/-!
# Lemma 11(b): fixed-pairing component coverage

For an `(a,c)` fixed-pairing deformation, the component family
`bdPaths` consists of the components in `C_b ∪ C'_d`.  Hence an edge
between `C_b` and `C'_d` is contained in one of those components.  Two
`C'_d` vertices with a common `C_b` neighbor must therefore belong to
the same path component.

This discharges the component-capture hypothesis introduced for the
predecessor argument in Lemma 11(b).
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

/-- Every edge from `C'_d` to `C_b` is covered by a `bdPaths`
component.  Definition 19 provides this property because those paths are
the connected components of the induced graph on `C_b ∪ C'_d`. -/
def CoversBDEdges (O : FixedPairingPathFamily G) : Prop :=
  ∀ ⦃x w : V⦄,
    x ∈ O.Cd →
    w ∈ O.Cb →
    G.Adj x w →
    ∃ P : Set V,
      P ∈ O.bdPaths ∧ x ∈ P ∧ w ∈ P

/-- Edge coverage of `bdPaths` implies the common-`C_b)-neighbor
component property for the `(a,c)` pairing. -/
theorem capturesClassConnections_ac_of_coversBDEdges
    (O : FixedPairingPathFamily G)
    (hcover : O.CoversBDEdges) :
    O.CapturesClassConnections .ac := by
  intro x y w hx hy hw hxw hyw
  change x ∈ O.Cd at hx
  change y ∈ O.Cd at hy
  obtain ⟨P, hP, hxP, hwP⟩ := hcover hx hw hxw
  obtain ⟨Q, hQ, hyQ, hwQ⟩ := hcover hy hw hyw
  have hPQ : P = Q :=
    O.eq_of_mem_bdPaths hP hQ hwP hwQ
  subst Q
  exact ⟨P, Or.inr hP, hxP, hyQ⟩

/-- Lemma 11(b) for an `(a,c)` deformation after deriving component
capture from the actual `bdPaths` edge coverage. -/
theorem lemma11b_of_bdEdgeCoverage
    (O : FixedPairingPathFamily G)
    (U : Nat → Set V) (Anticommutes : V → Prop)
    (degree : Nat → V → Nat)
    (hexact : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ U s → ExactlyOneOfFour u O.Ca O.Cb O.Cc O.Cd)
    (hcontained : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ U s →
      ∃ P : Set V, P ∈ O.paths ∧ u ∈ P)
    (hdegree : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ U s → ¬Anticommutes u → degree s u = 4)
    (hcover : O.CoversBDEdges)
    (hpred : O.CommonBPredecessorRule .ac U Anticommutes)
    {s : Nat} {u : V}
    (hu : u ∈ U s)
    (hcomm : ¬Anticommutes u) :
    degree s u = 4 ∧
      O.EarlierAnticommutingWitnessInUniquePath
        U Anticommutes s u := by
  exact O.lemma11b_of_commonBPredecessors
    .ac U Anticommutes degree hexact hcontained hdegree
    (O.capturesClassConnections_ac_of_coversBDEdges hcover)
    hpred hu hcomm

end FixedPairingPathFamily

end SimpleGraph
