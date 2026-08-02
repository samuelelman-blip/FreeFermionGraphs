import FreeFermionGraphs.ObstructionSearchFiniteMixedContextExact
import FreeFermionGraphs.ObstructionSearchPairing

/-!
# Pairing labels from finite mixed-side obstruction-search executions

The two literal stopping branches are kept separate.  An initial tether
already supplies the opposite typed clone in the original hole.  A later
Definition 20 stop supplies a dependent anticommuting target in an actual
finite ordered block, where the exact finite Lemma 11(a.ii) theorem produces
that clone.

Consequently every obstruction arc crosses pairing types.  No relation
between an empty output and the final dependent vertex is assumed.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace FixedPairingPathFamily

variable {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ObstructionSearchInitialization

variable {I : ObstructionSearchInitialization families Cprime}

/-- The two literal ways a finite mixed-side initialized search can stop at
an obstruction target.

The initial-tether branch carries its immediate opposite typed clone.  The
later branch records the exact Definition 20 witness in one actual ordered
block. -/
inductive FiniteMixedSideObstructionPairingWitness
    (X : I.InitializationFiniteMixedSideOSExecutionData)
    (source target : I.Node) : Prop where
  | initialTether
      (typedClone :
        (families (I.pairing source)).HasTypedClone .ad
          X.originalHole (target : V)) :
      FiniteMixedSideObstructionPairingWitness X source target
  | laterDefinition20
      (q : Fin (X.ordered source).blockCount)
      (s : Nat)
      (target_prime : (target : V) ∈ Cprime)
      (target_dependent :
        (target : V) ∈
          ((X.ordered source).block q).dependentAt s)
      (target_anticommutes :
        ((X.ordered source).block q).path.AnticommutesWith
          (target : V))
      (target_finalDegree_four :
        ((X.ordered source).block q).finalHole.externalDegree
          (target : V) = 4) :
      FiniteMixedSideObstructionPairingWitness X source target

namespace FiniteMixedSideObstructionPairingWitness

/-- Both finite stopping branches yield an internally opposite typed clone
for the target in the initialized original hole. -/
theorem typedClone_ad
    {X : I.InitializationFiniteMixedSideOSExecutionData}
    {source target : I.Node}
    (B : FiniteMixedSideObstructionPairingWitness X source target)
    (hclaw : G.IsClawFree) :
    (families (I.pairing source)).HasTypedClone .ad
      X.originalHole (target : V) := by
  cases B with
  | initialTether htyped =>
      exact htyped
  | laterDefinition20 q s hprime hdependent hanti hfour =>
      exact
        ((X.orderedBlock_lemma11aii_exact source q hclaw
          hdependent hprime hanti).mp hfour).2

end FiniteMixedSideObstructionPairingWitness

/-- Pairing labels assigned at initialization are faithful to the typed
clones of the vertices of `W` in the original hole. -/
structure InitializationFiniteMixedSidePairingLabelData
    (I : ObstructionSearchInitialization families Cprime)
    (X : I.InitializationFiniteMixedSideOSExecutionData) : Prop where
  familyGeometry : PairingIndexedFamilyGeometry families
  initializer_typedClone : ∀ source : I.Node,
    (families (I.pairing source)).HasTypedClone .ac
      X.originalHole (source : V)

/-- The finite stopping branch selected by each actual obstruction arc. -/
structure InitializationFiniteMixedSideStoppingPairingData
    (I : ObstructionSearchInitialization families Cprime)
    (X : I.InitializationFiniteMixedSideOSExecutionData) : Prop where
  branch : ∀ ⦃source target : I.Node⦄,
    I.graph.Arc source target →
      FiniteMixedSideObstructionPairingWitness X source target

namespace InitializationFiniteMixedSidePairingLabelData

/-- Faithful initial labels and the literal finite stopping branch force every
obstruction arc to cross pairing types. -/
theorem obstructionOpposite
    {X : I.InitializationFiniteMixedSideOSExecutionData}
    (L : I.InitializationFiniteMixedSidePairingLabelData X)
    (S : I.InitializationFiniteMixedSideStoppingPairingData X)
    (hclaw : G.IsClawFree)
    ⦃source target : I.Node⦄
    (h : I.graph.Arc source target) :
    I.pairing target = (I.pairing source).opposite := by
  have htargetInternal := (S.branch h).typedClone_ad hclaw
  have htargetGlobal :=
    L.familyGeometry.globalize_ad (I.pairing source) htargetInternal
  have hlabelInternal := L.initializer_typedClone target
  have hlabelGlobal :=
    L.familyGeometry.globalize_ac (I.pairing target) hlabelInternal
  exact (families .ac).hasTypedClone_pairing_unique
    L.familyGeometry.ca_cb_disjoint
    L.familyGeometry.cc_cd_disjoint
    hlabelGlobal htargetGlobal

end InitializationFiniteMixedSidePairingLabelData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
