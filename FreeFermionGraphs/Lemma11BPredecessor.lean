import FreeFermionGraphs.Lemma11BFourNeighbors

/-!
# Lemma 11(b): component-linked predecessors

In the local case analysis of Lemma 11(b), the earlier dependent vertex and
the current commuting vertex are repeatedly shown to share a neighbor in
`C_b`.  Because both lie in the complementary paired prime class, this
places them in the same fixed-pairing path component.

This module turns that concrete common-neighbor construction into the
strict component-linked descent rule used by the well-founded argument.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

/-- The path family captures two vertices in the prime class paired with
`C_b` whenever they share a neighbor in `C_b`.  This is the component
property used in the proof of Lemma 11(b). -/
def CapturesClassConnections
    (O : FixedPairingPathFamily G) (σ : PairingType) : Prop :=
  ∀ ⦃x y w : V⦄,
    x ∈ σ.classFromB O.Cc O.Cd →
    y ∈ σ.classFromB O.Cc O.Cd →
    w ∈ O.Cb →
    G.Adj x w →
    G.Adj y w →
    O.SharesPath x y

/-- A local predecessor rule expressed in the form produced by the paper's
claw-free case analysis: an earlier dependent vertex shares a `C_b`
neighbor with the current vertex. -/
def CommonBPredecessorRule
    (O : FixedPairingPathFamily G) (σ : PairingType)
    (U : Nat → Set V) (Anticommutes : V → Prop) : Prop :=
  ∀ ⦃s : Nat⦄ ⦃u : V⦄,
    u ∈ U s →
    ¬Anticommutes u →
    ∃ s' : Nat, ∃ u' w : V,
      s' < s ∧
      u' ∈ U s' ∧
      u' ∈ σ.classFromB O.Cc O.Cd ∧
      u ∈ σ.classFromB O.Cc O.Cd ∧
      w ∈ O.Cb ∧
      G.Adj u' w ∧
      G.Adj u w

/-- A shared `C_b` neighbor produces a common path-component witness. -/
theorem sharesPath_of_common_b_neighbor
    (O : FixedPairingPathFamily G) (σ : PairingType)
    (hcapture : O.CapturesClassConnections σ)
    {x y w : V}
    (hx : x ∈ σ.classFromB O.Cc O.Cd)
    (hy : y ∈ σ.classFromB O.Cc O.Cd)
    (hw : w ∈ O.Cb)
    (hxw : G.Adj x w)
    (hyw : G.Adj y w) :
    O.SharesPath x y :=
  hcapture hx hy hw hxw hyw

/-- Convert the concrete common-`C_b)-neighbor predecessor construction
into the abstract strict descent rule of Lemma 11(b). -/
theorem dependentDescentRule_of_commonBPredecessors
    (O : FixedPairingPathFamily G) (σ : PairingType)
    (U : Nat → Set V) (Anticommutes : V → Prop)
    (hcapture : O.CapturesClassConnections σ)
    (hpred : O.CommonBPredecessorRule σ U Anticommutes) :
    DependentDescentRule U Anticommutes O.SharesPath := by
  intro s u hu hcomm
  obtain ⟨s', u', w, hs', hu', huClass, huCurrentClass,
      hw, hu'w, huw⟩ := hpred hu hcomm
  refine ⟨s', u', hs', hu', ?_⟩
  exact O.sharesPath_of_common_b_neighbor
    σ hcapture huClass huCurrentClass hw hu'w huw

/-- Lemma 11(b) with the component descent discharged by the common-neighbor
construction.  The remaining local inputs are the degree-four rule and the
existence of the displayed earlier common-neighbor predecessor. -/
theorem lemma11b_of_commonBPredecessors
    (O : FixedPairingPathFamily G) (σ : PairingType)
    (U : Nat → Set V) (Anticommutes : V → Prop)
    (degree : Nat → V → Nat)
    (hexact : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ U s → ExactlyOneOfFour u O.Ca O.Cb O.Cc O.Cd)
    (hcontained : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ U s →
      ∃ P : Set V, P ∈ O.paths ∧ u ∈ P)
    (hdegree : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ U s → ¬Anticommutes u → degree s u = 4)
    (hcapture : O.CapturesClassConnections σ)
    (hpred : O.CommonBPredecessorRule σ U Anticommutes)
    {s : Nat} {u : V}
    (hu : u ∈ U s)
    (hcomm : ¬Anticommutes u) :
    degree s u = 4 ∧
      O.EarlierAnticommutingWitnessInUniquePath
        U Anticommutes s u := by
  exact O.lemma11b_of_coloring_and_localRules
    U Anticommutes degree hexact hcontained hdegree
    (O.dependentDescentRule_of_commonBPredecessors
      σ U Anticommutes hcapture hpred)
    hu hcomm

end FixedPairingPathFamily

end SimpleGraph
