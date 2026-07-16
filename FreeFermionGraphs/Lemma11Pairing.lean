import FreeFermionGraphs.PairingType

/-!
# Lemma 11(a.i): preservation of pairing type

This module formalizes the coloring-class argument at the end of
Lemma 11(a.i).  A deformation path starting in `Cₐ` introduces a vertex in
the corresponding paired prime class.  A dependent vertex lies in the other
paired prime class.  Any common neighbor of the removed, introduced, and
dependent vertices must therefore lie in `C_b`, since each coloring class
is independent.  The resulting clone pair has the same pairing type as the
fixed-pairing path family.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- A set containing no adjacent pair of vertices. -/
def IsIndependentClass (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ ⦃x y : V⦄, x ∈ S → y ∈ S → ¬G.Adj x y

namespace PairingType

/-- The prime coloring class paired with `Cₐ`. -/
def classFromA (σ : PairingType) (Cc Cd : Set V) : Set V :=
  match σ with
  | ac => Cc
  | ad => Cd

/-- The prime coloring class paired with `C_b`. -/
def classFromB (σ : PairingType) (Cc Cd : Set V) : Set V :=
  match σ with
  | ac => Cd
  | ad => Cc

@[simp]
theorem classFromA_ac (Cc Cd : Set V) :
    PairingType.ac.classFromA Cc Cd = Cc :=
  rfl

@[simp]
theorem classFromA_ad (Cc Cd : Set V) :
    PairingType.ad.classFromA Cc Cd = Cd :=
  rfl

@[simp]
theorem classFromB_ac (Cc Cd : Set V) :
    PairingType.ac.classFromB Cc Cd = Cd :=
  rfl

@[simp]
theorem classFromB_ad (Cc Cd : Set V) :
    PairingType.ad.classFromB Cc Cd = Cc :=
  rfl

end PairingType

namespace FixedPairingPathFamily

/-- The four coloring classes used by a fixed-pairing path family are
independent sets in the frustration graph. -/
structure ColorClassesIndependent
    (O : FixedPairingPathFamily G) : Prop where
  ca : IsIndependentClass G O.Ca
  cb : IsIndependentClass G O.Cb
  cc : IsIndependentClass G O.Cc
  cd : IsIndependentClass G O.Cd

/-- A vertex in `C_b` paired with a vertex in the corresponding prime
class has pairing type `σ`. -/
theorem hasPairingType_of_mem_b
    (O : FixedPairingPathFamily G) (σ : PairingType)
    {prime original : V}
    (horiginal : original ∈ O.Cb)
    (hprime : prime ∈ σ.classFromB O.Cc O.Cd) :
    O.HasPairingType σ prime original := by
  cases σ <;> exact Or.inr ⟨horiginal, hprime⟩

/-- The coloring-class exclusion used in Lemma 11(a.i).  The common
neighbor cannot share a class with any of the three vertices to which it
is adjacent, leaving only `C_b`. -/
theorem commonNeighbor_mem_cb
    (O : FixedPairingPathFamily G) (σ : PairingType)
    (hindep : O.ColorClassesIndependent)
    {introduced removed u v : V}
    (hremoved : removed ∈ O.Ca)
    (hintroduced : introduced ∈ σ.classFromA O.Cc O.Cd)
    (hu : u ∈ σ.classFromB O.Cc O.Cd)
    (hvExact : ExactlyOneOfFour v O.Ca O.Cb O.Cc O.Cd)
    (huv : G.Adj u v)
    (hintroducedv : G.Adj introduced v)
    (hremovedv : G.Adj removed v) :
    v ∈ O.Cb := by
  cases σ with
  | ac =>
      change introduced ∈ O.Cc at hintroduced
      change u ∈ O.Cd at hu
      rcases hvExact with hca | hcb | hcc | hcd
      · exact (hindep.ca hremoved hca.1 hremovedv).elim
      · exact hcb.1
      · exact (hindep.cc hintroduced hcc.1 hintroducedv).elim
      · exact (hindep.cd hu hcd.1 huv).elim
  | ad =>
      change introduced ∈ O.Cd at hintroduced
      change u ∈ O.Cc at hu
      rcases hvExact with hca | hcb | hcc | hcd
      · exact (hindep.ca hremoved hca.1 hremovedv).elim
      · exact hcb.1
      · exact (hindep.cc hu hcc.1 huv).elim
      · exact (hindep.cd hintroduced hcd.1 hintroducedv).elim

/-- Lemma 11(a.i), pairing-preservation core.  The persistent common
neighbor supplied by the dependent deformation lies on the original and
deformed holes and forms a clone pair of the same fixed pairing type.

The degree-three neighborhood analysis in the paper supplies the explicit
coloring hypotheses used here. -/
theorem lemma11ai_same_pairing
    (O : FixedPairingPathFamily G) (σ : PairingType)
    {C : IndexedInducedHole G} {Cprime : Set V}
    {introduced u : V} {i : Fin C.card}
    (hdeform : C.SingleVertexDeformation introduced i)
    (hclaw : G.IsClawFree)
    (huDependent :
      u ∈ G.dependentSubset Cprime introduced (C.vertex i))
    (huOutside :
      u ∉ Set.insert introduced (Set.range C.vertex))
    (hindep : O.ColorClassesIndependent)
    (hremoved : C.vertex i ∈ O.Ca)
    (hintroduced :
      introduced ∈ σ.classFromA O.Cc O.Cd)
    (huClass : u ∈ σ.classFromB O.Cc O.Cd)
    (hcommonExact : ∀ ⦃v : V⦄,
      v ∈ Set.range C.vertex →
      G.Adj u v →
      G.Adj introduced v →
      G.Adj (C.vertex i) v →
      ExactlyOneOfFour v O.Ca O.Cb O.Cc O.Cd) :
    ∃ v,
      v ∈ Set.range C.vertex ∧
      v ∈ Set.range (C.deform hdeform).vertex ∧
      G.Adj u v ∧
      G.Adj introduced v ∧
      G.Adj (C.vertex i) v ∧
      O.HasPairingType σ u v := by
  obtain ⟨v, hvC, hvDeformed, huv, hintroducedv, hremovedv⟩ :=
    hdeform.dependent_common_neighbor_persists
      hclaw huDependent huOutside
  have hvExact : ExactlyOneOfFour v O.Ca O.Cb O.Cc O.Cd :=
    hcommonExact hvC huv hintroducedv hremovedv
  have hvb : v ∈ O.Cb :=
    O.commonNeighbor_mem_cb σ hindep hremoved hintroduced huClass
      hvExact huv hintroducedv hremovedv
  exact ⟨v, hvC, hvDeformed, huv, hintroducedv, hremovedv,
    O.hasPairingType_of_mem_b σ hvb huClass⟩

end FixedPairingPathFamily

end SimpleGraph
