import FreeFermionGraphs.Lemma12Palindromic

/-!
# Obstruction-search data

This module introduces the finite directed obstruction graph used by the
search process following Lemma 13.  It deliberately separates the generic
two-colour directed-graph argument from the graph-theoretic construction of
the initialization certificates.

A possibly empty search deformation is represented by an optional complete
Definition 19 deformation.  Consequently a present run already contains all
of the ordered single-vertex geometry used in Lemmas 11--13, while `none`
represents the empty deformation occurring in the initialization of `OS`.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

/-- The two orientations from which an obstruction search can enter the
terminal path component.  These are kept separate from `PairingType`: two
searches with the same pairing type can reach the same obstruction from the
two opposite endpoints of one path. -/
inductive ObstructionSlot where
  | first
  | last
deriving DecidableEq, Repr

namespace ObstructionSlot

/-- Among three values of a two-element obstruction slot, two are equal. -/
theorem three_eq (x y z : ObstructionSlot) :
    x = y ∨ x = z ∨ y = z := by
  cases x <;> cases y <;> cases z <;> simp

/-- Two distinct slots put any fixed slot on exactly one side. -/
theorem exactly_one_eq_of_ne
    {x y : ObstructionSlot} (hxy : x ≠ y) (z : ObstructionSlot) :
    (x = z ∧ y ≠ z) ∨ (x ≠ z ∧ y = z) := by
  cases x <;> cases y <;> cases z <;> simp_all

end ObstructionSlot

namespace ArcGraph

variable {α : Type*}

/-- A directed graph is bipartite with pairing-type coloring when every arc
crosses to the opposite pairing type. -/
def IsBipartiteByPairing
    (D : ArcGraph α) (pairing : α → PairingType) : Prop :=
  ∀ ⦃x y : α⦄, D.Arc x y → pairing y = (pairing x).opposite

/-- Carrier-level formulation of indegree at most two.  It avoids any
finiteness or decidable-equality assumption on the vertex type. -/
def AtMostTwoIncoming (D : ArcGraph α) (target : α) : Prop :=
  ∀ ⦃x y z : α⦄,
    D.Arc x target →
    D.Arc y target →
    D.Arc z target →
      x = y ∨ x = z ∨ y = z

end ArcGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

/-- A possibly empty fixed-pairing-type deformation returned by the
obstruction search.  A nonempty output is a complete Definition 19
deformation; the empty output is represented by `none`. -/
structure SearchDeformation
    (O : FixedPairingPathFamily G) (Cprime : Set V) where
  run : Option (FullDefinition19Deformation O Cprime)

namespace SearchDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- The active path components occurring in a possibly empty search
deformation. -/
def paths (S : SearchDeformation O Cprime) : Set (Set V) :=
  {P | ∃ F : FullDefinition19Deformation O Cprime,
    S.run = some F ∧
      ∃ i : Fin F.deformation.stepCount,
        Set.range (F.deformation.step i).activePath.vertex = P}

/-- Every active path of a search output belongs to its fixed-pairing path
family. -/
theorem paths_subset_family
    (S : SearchDeformation O Cprime) :
    S.paths ⊆ O.paths := by
  rintro P ⟨F, _hF, i, hi⟩
  rw [← hi]
  exact F.deformation.activePath_mem i

/-- Part (i)'s empty/nonempty alternative is intrinsic to the search-output
type. -/
theorem empty_or_complete
    (S : SearchDeformation O Cprime) :
    S.run = none ∨
      ∃ F : FullDefinition19Deformation O Cprime,
        S.run = some F := by
  cases S.run with
  | none => exact Or.inl rfl
  | some F => exact Or.inr ⟨F, rfl⟩

end SearchDeformation

/-- The initialized family of obstruction searches.

The construction has one source for every vertex of `W`, a pairing type,
an optional complete Definition 19 output, an optional obstruction target,
and an optional final dependent vertex.  The graph-geometric certificates
needed to prove Lemma 14 are kept in `InitializationGeometry` below. -/
structure ObstructionSearchInitialization
    (families : PairingType → FixedPairingPathFamily G)
    (Cprime : Set V) where
  W : Set V
  pairing : {v : V // v ∈ W} → PairingType
  output : ∀ j : {v : V // v ∈ W},
    SearchDeformation (families (pairing j)) Cprime
  obstruction : {v : V // v ∈ W} →
    Option {v : V // v ∈ W}
  dependent : {v : V // v ∈ W} → Option V

namespace ObstructionSearchInitialization

variable {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

abbrev Node (I : ObstructionSearchInitialization families Cprime) :=
  {v : V // v ∈ I.W}

/-- The directed obstruction graph: the unique optional target of a source
is its outgoing arc. -/
def graph (I : ObstructionSearchInitialization families Cprime) :
    ArcGraph I.Node where
  Arc source target := I.obstruction source = some target

@[simp]
theorem graph_arc_iff
    (I : ObstructionSearchInitialization families Cprime)
    (source target : I.Node) :
    I.graph.Arc source target ↔
      I.obstruction source = some target :=
  Iff.rfl

/-- The at-most-singleton set `U_j` returned by the obstruction search. -/
def dependentSet
    (I : ObstructionSearchInitialization families Cprime)
    (source : I.Node) : Set V :=
  {u | I.dependent source = some u}

@[simp]
theorem mem_dependentSet_iff
    (I : ObstructionSearchInitialization families Cprime)
    (source : I.Node) (u : V) :
    u ∈ I.dependentSet source ↔
      I.dependent source = some u :=
  Iff.rfl

/-- Every `U_j` contains at most one vertex. -/
theorem dependentSet_subsingleton
    (I : ObstructionSearchInitialization families Cprime)
    (source : I.Node) :
    (I.dependentSet source).Subsingleton := by
  intro u hu v hv
  change I.dependent source = some u at hu
  change I.dependent source = some v at hv
  rw [hu] at hv
  exact Option.some.inj hv

/-- An output dependent set is exactly `{u}` precisely when its optional
dependent vertex is `u`. -/
theorem dependentSet_eq_singleton_iff
    (I : ObstructionSearchInitialization families Cprime)
    (source : I.Node) (u : V) :
    I.dependentSet source = {u} ↔
      I.dependent source = some u := by
  constructor
  · intro h
    have hu : u ∈ I.dependentSet source := by
      rw [h]
      exact Set.mem_singleton u
    exact hu
  · intro h
    ext v
    constructor
    · intro hv
      have : some v = some u := by
        rw [← hv, h]
      exact Set.mem_singleton_iff.mpr (Option.some.inj this)
    · intro hv
      have hvu := Set.mem_singleton_iff.mp hv
      simpa [hvu] using h

/-- The local geometric facts extracted from initialization of `OS`.

`pathOwner` encodes the uniqueness of the closest source vertex for paths
traversed by searches of a fixed pairing type.  `incomingSlot` records the
one of the two endpoint orientations by which an obstruction target is met,
while `targetSlot` records which endpoint is the target itself.
Corollaries 9--11 are used in the concrete construction to prove slot
injectivity and the final dependent-slot equivalence; the generic Lemma 14
argument only consumes those consequences. -/
structure InitializationGeometry
    (I : ObstructionSearchInitialization families Cprime) where
  noSelfLoop : ∀ source : I.Node,
    I.obstruction source ≠ some source
  obstructionOpposite : ∀ ⦃source target : I.Node⦄,
    I.graph.Arc source target →
      I.pairing target = (I.pairing source).opposite
  pathOwner : PairingType → Set V → Option I.Node
  path_owner_eq : ∀ (source : I.Node) ⦃P : Set V⦄,
    P ∈ (I.output source).paths →
      pathOwner (I.pairing source) P = some source
  incomingSlot : I.Node → I.Node → ObstructionSlot
  targetSlot : I.Node → ObstructionSlot
  incomingSlot_injective : ∀ ⦃source source' target : I.Node⦄,
    I.graph.Arc source target →
    I.graph.Arc source' target →
    incomingSlot source target = incomingSlot source' target →
      source = source'
  dependent_target_iff_slot : ∀ ⦃source target : I.Node⦄,
    I.graph.Arc source target →
      (I.dependent source = some (target : V) ↔
        incomingSlot source target = targetSlot target)

namespace InitializationGeometry

variable {I : ObstructionSearchInitialization families Cprime}

/-- Every source has at most one outgoing obstruction arc. -/
theorem outgoing_functional
    (_X : I.InitializationGeometry)
    {source target target' : I.Node}
    (h : I.graph.Arc source target)
    (h' : I.graph.Arc source target') :
    target = target' := by
  change I.obstruction source = some target at h
  change I.obstruction source = some target' at h'
  rw [h] at h'
  exact Option.some.inj h'

/-- The initialized obstruction graph is bipartite, with the two pairing
types as its coloring classes. -/
theorem graph_isBipartiteByPairing
    (X : I.InitializationGeometry) :
    I.graph.IsBipartiteByPairing I.pairing := by
  intro source target h
  exact X.obstructionOpposite h

/-- Search outputs of the same pairing type and distinct sources have
disjoint collections of active paths. -/
theorem samePairing_paths_disjoint
    (X : I.InitializationGeometry)
    {source source' : I.Node}
    (hne : source ≠ source')
    (hpair : I.pairing source = I.pairing source') :
    Disjoint (I.output source).paths (I.output source').paths := by
  apply Set.disjoint_left.mpr
  intro P hP hP'
  have howner := X.path_owner_eq source hP
  have howner' := X.path_owner_eq source' hP'
  have hs : some source = some source' := by
    calc
      some source = X.pathOwner (I.pairing source) P := howner.symm
      _ = X.pathOwner (I.pairing source') P := by rw [hpair]
      _ = some source' := howner'
  exact hne (Option.some.inj hs)

/-- The two incoming slots force indegree at most two. -/
theorem atMostTwoIncoming
    (X : I.InitializationGeometry) (target : I.Node) :
    I.graph.AtMostTwoIncoming target := by
  intro source source' source'' h h' h''
  rcases ObstructionSlot.three_eq
      (X.incomingSlot source target)
      (X.incomingSlot source' target)
      (X.incomingSlot source'' target) with hslot | hslot | hslot
  · exact Or.inl (X.incomingSlot_injective h h' hslot)
  · exact Or.inr (Or.inl
      (X.incomingSlot_injective h h'' hslot))
  · exact Or.inr (Or.inr
      (X.incomingSlot_injective h' h'' hslot))

/-- If two distinct sources obstruct the same target, that target is the
unique dependent vertex returned by exactly one of the two searches. -/
theorem target_onlyDependent_of_twoIncoming
    (X : I.InitializationGeometry)
    {source source' target : I.Node}
    (hne : source ≠ source')
    (h : I.graph.Arc source target)
    (h' : I.graph.Arc source' target) :
    ((I.dependentSet source = {(target : V)} ∧
        I.dependentSet source' ≠ {(target : V)}) ∨
      (I.dependentSet source ≠ {(target : V)} ∧
        I.dependentSet source' = {(target : V)})) := by
  have hslots :
      X.incomingSlot source target ≠
        X.incomingSlot source' target := by
    intro hEq
    exact hne (X.incomingSlot_injective h h' hEq)
  rcases ObstructionSlot.exactly_one_eq_of_ne hslots
      (X.targetSlot target) with hleft | hright
  · left
    constructor
    · apply (I.dependentSet_eq_singleton_iff source (target : V)).2
      exact (X.dependent_target_iff_slot
        (source := source) (target := target) h).2 hleft.1
    · intro hset
      have hdep :=
        (I.dependentSet_eq_singleton_iff source' (target : V)).1 hset
      exact hleft.2 ((X.dependent_target_iff_slot
        (source := source') (target := target) h').1 hdep)
  · right
    constructor
    · intro hset
      have hdep :=
        (I.dependentSet_eq_singleton_iff source (target : V)).1 hset
      exact hright.1 ((X.dependent_target_iff_slot
        (source := source) (target := target) h).1 hdep)
    · apply (I.dependentSet_eq_singleton_iff source' (target : V)).2
      exact (X.dependent_target_iff_slot
        (source := source') (target := target) h').2 hright.2

end InitializationGeometry

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
