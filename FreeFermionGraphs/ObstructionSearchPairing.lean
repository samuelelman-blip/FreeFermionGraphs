import FreeFermionGraphs.ObstructionSearchExecutionTrace

/-!
# Pairing labels at obstruction-search termination

The obstruction graph is colored by the pairing type of the initialized
searches.  Its bipartiteness should not be primitive terminal data.  This
module derives the opposite-pairing conclusion from two pieces of concrete
geometry:

* every initializer has the pairing label determined by its typed clone in
  the original hole; and
* the literal stopping branch supplies an oppositely typed clone for the
  obstruction target.  In the later branch this is derived from the
  Definition 20 dependent-set witness by Lemma 11(a)(ii).

The two pairing-indexed path families use the same original coloring classes;
the prime coloring classes are exchanged for the opposite pairing.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace IndexedInducedHole

/-- A vertex cannot be a clone of two different vertices of one induced
hole. -/
theorem SingleVertexDeformation.center_eq
    {C : IndexedInducedHole G} {u : V} {i j : Fin C.card}
    (hi : C.SingleVertexDeformation u i)
    (hj : C.SingleVertexDeformation u j) :
    i = j := by
  by_contra hij
  have hijAdj : G.Adj (C.vertex i) (C.vertex j) := by
    have huj : G.Adj u (C.vertex j) := hj.adj_clone
    exact ((hi.adj_iff j).1 huj).resolve_left (fun hji => hij hji.symm)
  obtain ⟨a, b, hab, hia, hib, habNonadj⟩ :=
    C.exists_two_nonadjacent_neighbors i
  have hjCases : j = a ∨ j = b :=
    C.adjacent_index_eq_of_two_distinct_neighbors hab hia hib hijAdj
  rcases hjCases with rfl | rfl
  · have hub : G.Adj u (C.vertex b) := hi.adj_of_clone_adj hib
    rcases (hj.adj_iff b).1 hub with hba | habAdj
    · exact hab hba.symm
    · exact habNonadj habAdj
  · have hua : G.Adj u (C.vertex a) := hi.adj_of_clone_adj hia
    rcases (hj.adj_iff a).1 hua with hab' | hbaAdj
    · exact hab hab'
    · exact habNonadj hbaAdj.symm

end IndexedInducedHole

namespace FixedPairingPathFamily

/-- A typed clone has a unique pairing type once the two original and two
prime coloring classes are disjoint in pairs. -/
theorem hasTypedClone_pairing_unique
    (O : FixedPairingPathFamily G)
    (hCaCb : Disjoint O.Ca O.Cb)
    (hCcCd : Disjoint O.Cc O.Cd)
    {C : IndexedInducedHole G} {u : V} {p q : PairingType}
    (hp : O.HasTypedClone p C u)
    (hq : O.HasTypedClone q C u) :
    p = q := by
  rcases hp with ⟨i, hi, hp⟩
  rcases hq with ⟨j, hj, hq⟩
  have hij : i = j := hi.center_eq hj
  subst j
  cases p <;> cases q
  · rfl
  · change
      ((C.vertex i ∈ O.Ca ∧ u ∈ O.Cc) ∨
        (C.vertex i ∈ O.Cb ∧ u ∈ O.Cd)) at hp
    change
      ((C.vertex i ∈ O.Ca ∧ u ∈ O.Cd) ∨
        (C.vertex i ∈ O.Cb ∧ u ∈ O.Cc)) at hq
    exfalso
    rcases hp with hp | hp <;> rcases hq with hq | hq
    · exact (Set.disjoint_left.mp hCcCd) hp.2 hq.2
    · exact (Set.disjoint_left.mp hCaCb) hp.1 hq.1
    · exact (Set.disjoint_left.mp hCaCb) hq.1 hp.1
    · exact (Set.disjoint_left.mp hCcCd) hq.2 hp.2
  · change
      ((C.vertex i ∈ O.Ca ∧ u ∈ O.Cd) ∨
        (C.vertex i ∈ O.Cb ∧ u ∈ O.Cc)) at hp
    change
      ((C.vertex i ∈ O.Ca ∧ u ∈ O.Cc) ∨
        (C.vertex i ∈ O.Cb ∧ u ∈ O.Cd)) at hq
    exfalso
    rcases hp with hp | hp <;> rcases hq with hq | hq
    · exact (Set.disjoint_left.mp hCcCd) hq.2 hp.2
    · exact (Set.disjoint_left.mp hCaCb) hp.1 hq.1
    · exact (Set.disjoint_left.mp hCaCb) hq.1 hp.1
    · exact (Set.disjoint_left.mp hCcCd) hp.2 hq.2
  · rfl

/-- The two pairing-indexed path families represent one global four-coloring.
The original classes agree, while the two prime classes are exchanged for
the `(a,d)` family. -/
structure PairingIndexedFamilyGeometry
    (families : PairingType → FixedPairingPathFamily G) : Prop where
  ca_eq : ∀ p, (families p).Ca = (families .ac).Ca
  cb_eq : ∀ p, (families p).Cb = (families .ac).Cb
  cc_eq : ∀ p, (families p).Cc =
    p.classFromA (families .ac).Cc (families .ac).Cd
  cd_eq : ∀ p, (families p).Cd =
    p.classFromB (families .ac).Cc (families .ac).Cd
  ca_cb_disjoint : Disjoint (families .ac).Ca (families .ac).Cb
  cc_cd_disjoint : Disjoint (families .ac).Cc (families .ac).Cd

namespace PairingIndexedFamilyGeometry

variable {families : PairingType → FixedPairingPathFamily G}

/-- An internally `(a,c)` typed clone in family `p` has global pairing
label `p`. -/
theorem globalize_ac
    (F : PairingIndexedFamilyGeometry families)
    (p : PairingType) {C : IndexedInducedHole G} {u : V}
    (h : (families p).HasTypedClone .ac C u) :
    (families .ac).HasTypedClone p C u := by
  rcases h with ⟨i, hclone, hpair⟩
  refine ⟨i, hclone, ?_⟩
  cases p with
  | ac => exact hpair
  | ad =>
      rcases hpair with hpair | hpair
      · left
        constructor
        · rw [F.ca_eq .ad] at hpair
          exact hpair.1
        · rw [F.cc_eq .ad] at hpair
          exact hpair.2
      · right
        constructor
        · rw [F.cb_eq .ad] at hpair
          exact hpair.1
        · rw [F.cd_eq .ad] at hpair
          exact hpair.2

/-- An internally opposite typed clone in family `p` has global pairing
label `p.opposite`. -/
theorem globalize_ad
    (F : PairingIndexedFamilyGeometry families)
    (p : PairingType) {C : IndexedInducedHole G} {u : V}
    (h : (families p).HasTypedClone .ad C u) :
    (families .ac).HasTypedClone p.opposite C u := by
  rcases h with ⟨i, hclone, hpair⟩
  refine ⟨i, hclone, ?_⟩
  cases p with
  | ac => exact hpair
  | ad =>
      rcases hpair with hpair | hpair
      · left
        constructor
        · rw [F.ca_eq .ad] at hpair
          exact hpair.1
        · rw [F.cd_eq .ad] at hpair
          exact hpair.2
      · right
        constructor
        · rw [F.cb_eq .ad] at hpair
          exact hpair.1
        · rw [F.cc_eq .ad] at hpair
          exact hpair.2

end PairingIndexedFamilyGeometry

variable {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ObstructionSearchInitialization

variable {I : ObstructionSearchInitialization families Cprime}

namespace OrderedOSExecution

/-- The concrete Definition 19 block at execution index `i`. -/
def concreteBlock
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : OrderedOSExecution I source originalHole)
    (i : Fin X.blockCount) :
    ConcretePathDeformation (families (I.pairing source)) Cprime :=
  (X.history.witness (X.path_mem i)).block

/-- The finite Lemma 11 history attached to an execution block. -/
def blockContext
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : OrderedOSExecution I source originalHole)
    (i : Fin X.blockCount) :
    (X.concreteBlock i).Lemma11AHistoryContext :=
  (X.history.witness (X.path_mem i)).context

/-- Every execution block is rooted at the initialized original hole. -/
theorem blockContext_originalHole
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : OrderedOSExecution I source originalHole)
    (i : Fin X.blockCount) :
    (X.blockContext i).originalHole = originalHole :=
  (X.history.witness (X.path_mem i)).originalHole_eq

end OrderedOSExecution

/-- The two literal ways an initialized `OS` call can stop at an obstruction.

In the initial tether branch the opposite typed clone is immediate.  In the
later branch the target occurs in a Definition 20 dependent set of an output
block, anticommutes with that block, and has final degree four.  Lemma
11(a)(ii) then produces the opposite typed clone in the original hole. -/
inductive ObstructionPairingWitness
    (X : I.InitializationOSExecutionData)
    (source target : I.Node) : Prop where
  | initialTether
      (typedClone :
        (families (I.pairing source)).HasTypedClone .ad
          X.originalHole (target : V)) :
      ObstructionPairingWitness X source target
  | laterDefinition20
      (q : Fin (X.execution source).blockCount)
      (s : Nat)
      (target_prime : (target : V) ∈ Cprime)
      (target_dependent :
        (target : V) ∈
          ((X.execution source).concreteBlock q).dependentAt s)
      (target_anticommutes :
        ((X.execution source).concreteBlock q).path.AnticommutesWith
          (target : V))
      (target_finalDegree_four :
        ((X.execution source).concreteBlock q).finalHole.externalDegree
          (target : V) = 4) :
      ObstructionPairingWitness X source target

namespace ObstructionPairingWitness

/-- Both stopping branches yield an internally opposite typed clone for the
target in the initialized original hole. -/
theorem typedClone_ad
    {X : I.InitializationOSExecutionData}
    {source target : I.Node}
    (B : ObstructionPairingWitness X source target)
    (hclaw : G.IsClawFree) :
    (families (I.pairing source)).HasTypedClone .ad
      X.originalHole (target : V) := by
  cases B with
  | initialTether htyped => exact htyped
  | laterDefinition20 q s hprime hdependent hanti hfour =>
      let D := (X.execution source).concreteBlock q
      let H := (X.execution source).blockContext q
      have hcomplete := D.lemma11a_complete H hclaw hprime hanti
      have htyped :
          (families (I.pairing source)).HasTypedClone .ad
            H.originalHole (target : V) :=
        ((hcomplete.2.2 s hdependent).mp hfour).2
      rw [(X.execution source).blockContext_originalHole q] at htyped
      exact htyped

end ObstructionPairingWitness

/-- Pairing labels assigned at initialization are faithful to the typed
clones of the vertices of `W` in the original hole. -/
structure InitializationPairingLabelData
    (I : ObstructionSearchInitialization families Cprime)
    (X : I.InitializationOSExecutionData) : Prop where
  familyGeometry : PairingIndexedFamilyGeometry families
  initializer_typedClone : ∀ source : I.Node,
    (families (I.pairing source)).HasTypedClone .ac
      X.originalHole (source : V)

/-- The stopping branch selected by each actual obstruction arc. -/
structure InitializationStoppingPairingData
    (I : ObstructionSearchInitialization families Cprime)
    (X : I.InitializationOSExecutionData) : Prop where
  branch : ∀ ⦃source target : I.Node⦄,
    I.graph.Arc source target →
      ObstructionPairingWitness X source target

namespace InitializationPairingLabelData

/-- The faithful initial labels and literal stopping branch force every
obstruction arc to cross pairing types. -/
theorem obstructionOpposite
    {X : I.InitializationOSExecutionData}
    (L : I.InitializationPairingLabelData X)
    (S : I.InitializationStoppingPairingData X)
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

end InitializationPairingLabelData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
