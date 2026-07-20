import FreeFermionGraphs.Lemma11OppositePairing

/-!
# Lemma 11(b): well-founded dependent-step descent

The proof of Lemma 11(b) repeatedly replaces a commuting dependent vertex
at step `s` by a vertex at a strictly earlier step `s'`.  The replacement
lies in the same fixed-pairing path component.  Since the step index strictly
decreases, this recursion terminates at an anticommuting dependent vertex.

This module isolates that global argument from the local claw-free case
analysis that constructs each descending step.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

/-- Two vertices occur in a common path component of `O`. -/
def SharesPath (O : FixedPairingPathFamily G) (x y : V) : Prop :=
  ∃ P : Set V, P ∈ O.paths ∧ x ∈ P ∧ y ∈ P

/-- Two vertices occur in a common component of the `C_b ∪ C'_d` side of
the fixed pairing.  Unlike `SharesPath`, this relation is transitive without
an exact-colouring hypothesis: members of `bdPaths` are pairwise disjoint by
construction.  This is the overlap-safe invariant used by the recursive
part of Lemma 11(b). -/
def SharesBDPath (O : FixedPairingPathFamily G) (x y : V) : Prop :=
  ∃ P : Set V, P ∈ O.bdPaths ∧ x ∈ P ∧ y ∈ P

theorem sharesBDPath_symm
    (O : FixedPairingPathFamily G) {x y : V}
    (h : O.SharesBDPath x y) :
    O.SharesBDPath y x := by
  rcases h with ⟨P, hP, hxP, hyP⟩
  exact ⟨P, hP, hyP, hxP⟩

/-- `bdPaths` are components of one induced side of the fixed pairing, so
sharing a `bdPath` composes through any common vertex, including a vertex in
an overlap of the two holes. -/
theorem sharesBDPath_trans
    (O : FixedPairingPathFamily G) {x y z : V}
    (hxy : O.SharesBDPath x y)
    (hyz : O.SharesBDPath y z) :
    O.SharesBDPath x z := by
  rcases hxy with ⟨P, hP, hxP, hyP⟩
  rcases hyz with ⟨Q, hQ, hyQ, hzQ⟩
  have hPQ : P = Q :=
    O.eq_of_mem_bdPaths hP hQ hyP hyQ
  subst Q
  exact ⟨P, hP, hxP, hzQ⟩

/-- Forgetting which side of the fixed pairing contains a component turns a
`SharesBDPath` witness into the paper's untyped path-component relation. -/
theorem sharesPath_of_sharesBDPath
    (O : FixedPairingPathFamily G) {x y : V}
    (h : O.SharesBDPath x y) :
    O.SharesPath x y := by
  rcases h with ⟨P, hP, hxP, hyP⟩
  exact ⟨P, Or.inr hP, hxP, hyP⟩

/-- A displayed `bdPaths` component is automatically the unique component
of that pairing type containing the vertex.  No assertion is made about a
possible component of the opposite pairing type through an overlap vertex. -/
def IsUniqueContainingBDPath
    (O : FixedPairingPathFamily G) (x : V) (P : Set V) : Prop :=
  P ∈ O.bdPaths ∧ x ∈ P ∧
    ∀ ⦃Q : Set V⦄, Q ∈ O.bdPaths → x ∈ Q → Q = P

theorem isUniqueContainingBDPath
    (O : FixedPairingPathFamily G) {x : V} {P : Set V}
    (hP : P ∈ O.bdPaths) (hxP : x ∈ P) :
    O.IsUniqueContainingBDPath x P := by
  refine ⟨hP, hxP, ?_⟩
  intro Q hQ hxQ
  exact O.eq_of_mem_bdPaths hQ hP hxQ hxP

theorem sharesPath_symm
    (O : FixedPairingPathFamily G) {x y : V}
    (h : O.SharesPath x y) :
    O.SharesPath y x := by
  rcases h with ⟨P, hP, hxP, hyP⟩
  exact ⟨P, hP, hyP, hxP⟩

/-- Sharing a path composes through a vertex that belongs to at most one
path component. -/
theorem sharesPath_trans_of_atMostOne
    (O : FixedPairingPathFamily G) {x y z : V}
    (hyUnique : O.AtMostOneContainingPath y)
    (hxy : O.SharesPath x y)
    (hyz : O.SharesPath y z) :
    O.SharesPath x z := by
  rcases hxy with ⟨P, hP, hxP, hyP⟩
  rcases hyz with ⟨Q, hQ, hyQ, hzQ⟩
  have hPQ : P = Q :=
    hyUnique ⟨hP, hyP⟩ ⟨hQ, hyQ⟩
  subst Q
  exact ⟨P, hP, hxP, hzQ⟩

/-- If `P` is the unique path containing `x`, every vertex sharing a path
with `x` belongs to `P`.  This is the final path-membership implication
used in Lemma 11(b). -/
theorem mem_of_isUniqueContainingPath_of_sharesPath
    (O : FixedPairingPathFamily G) {x y : V} {P : Set V}
    (hP : O.IsUniqueContainingPath x P)
    (hxy : O.SharesPath x y) :
    y ∈ P := by
  rcases hxy with ⟨Q, hQ, hxQ, hyQ⟩
  have hQP : Q = P := hP.2.2 hQ hxQ
  simpa [hQP] using hyQ

end FixedPairingPathFamily

/-- The conclusion sought in the recursive part of Lemma 11(b): an
anticommuting dependent vertex at a strictly earlier step, linked to the
original vertex by the chosen component relation. -/
def EarlierAnticommutingWitness
    (U : Nat → Set V) (Anticommutes : V → Prop)
    (SameComponent : V → V → Prop)
    (s : Nat) (u : V) : Prop :=
  ∃ s' : Nat, ∃ u' : V,
    s' < s ∧
    u' ∈ U s' ∧
    Anticommutes u' ∧
    SameComponent u' u

/-- Paper-faithful recursive conclusion for an `(a,c)` deformation: the
earlier anticommuting witness and the original vertex lie in the witness's
unique component of the same (`bd`) pairing type. -/
def FixedPairingPathFamily.EarlierAnticommutingWitnessInUniqueBDPath
    {G : SimpleGraph V} (O : FixedPairingPathFamily G)
    (U : Nat → Set V) (Anticommutes : V → Prop)
    (s : Nat) (u : V) : Prop :=
  ∃ s' : Nat, ∃ u' : V, ∃ P : Set V,
    s' < s ∧
    u' ∈ U s' ∧
    Anticommutes u' ∧
    O.IsUniqueContainingBDPath u' P ∧
    u ∈ P

/-- The local descent obligation in Lemma 11(b).  Every commuting dependent
vertex has a component-linked dependent predecessor at a smaller index. -/
def DependentDescentRule
    (U : Nat → Set V) (Anticommutes : V → Prop)
    (SameComponent : V → V → Prop) : Prop :=
  ∀ ⦃s : Nat⦄ ⦃u : V⦄,
    u ∈ U s →
    ¬Anticommutes u →
    ∃ s' : Nat, ∃ u' : V,
      s' < s ∧ u' ∈ U s' ∧ SameComponent u' u

/-- Strict descent of the step index must eventually produce an
anticommuting dependent vertex.  Component links compose at intermediate
dependent vertices via `hcompose`. -/
theorem earlierAnticommutingWitness_of_descent
    {U : Nat → Set V} {Anticommutes : V → Prop}
    {SameComponent : V → V → Prop}
    (hdesc : DependentDescentRule U Anticommutes SameComponent)
    (hcompose : ∀ ⦃s : Nat⦄ ⦃x y z : V⦄,
      y ∈ U s →
      SameComponent x y →
      SameComponent y z →
      SameComponent x z)
    {s : Nat} {u : V}
    (hu : u ∈ U s)
    (hcomm : ¬Anticommutes u) :
    EarlierAnticommutingWitness U Anticommutes SameComponent s u := by
  induction s using Nat.strong_induction_on generalizing u with
  | h s ih =>
      obtain ⟨s', u', hs', hu', hlink⟩ := hdesc hu hcomm
      by_cases hanti' : Anticommutes u'
      · exact ⟨s', u', hs', hu', hanti', hlink⟩
      · obtain ⟨t, w, ht, hw, hantiw, hwlink⟩ :=
          ih s' hs' hu' hanti'
        exact ⟨t, w, lt_trans ht hs', hw, hantiw,
          hcompose hu' hwlink hlink⟩

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

/-- The well-founded conclusion of Lemma 11(b), specialized to fixed-pairing
path components.  Corollary 10 supplies `hunique`; the local graph
analysis supplies `hdesc`. -/
theorem earlierAnticommutingWitness_sharesPath
    (O : FixedPairingPathFamily G)
    (U : Nat → Set V) (Anticommutes : V → Prop)
    (hunique : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ U s → O.AtMostOneContainingPath u)
    (hdesc : DependentDescentRule U Anticommutes O.SharesPath)
    {s : Nat} {u : V}
    (hu : u ∈ U s)
    (hcomm : ¬Anticommutes u) :
    EarlierAnticommutingWitness
      U Anticommutes O.SharesPath s u := by
  exact earlierAnticommutingWitness_of_descent hdesc
    (fun {_s} {_x} {_y} {_z} hy hxy hyz =>
      O.sharesPath_trans_of_atMostOne (hunique hy) hxy hyz)
    hu hcomm

end FixedPairingPathFamily

end SimpleGraph
