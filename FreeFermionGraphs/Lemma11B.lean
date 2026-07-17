import FreeFermionGraphs.Lemma11BDescent

/-!
# Lemma 11(b): assembly from local obligations

The proof of Lemma 11(b) has two logically separate parts.  The local
claw-free analysis proves degree four and constructs a component-linked
predecessor at a smaller deformation index.  The global argument iterates
that predecessor rule until it reaches an anticommuting vertex.

This module records the local obligations and assembles them using the
well-founded descent theorem.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

/-- The local graph-theoretic obligations needed to prove Lemma 11(b).

The remaining claw-free case analysis supplies these fields for the
dependent subsets and external degrees arising from a deformation path. -/
structure Lemma11BLocalData
    (O : FixedPairingPathFamily G)
    (U : Nat → Set V)
    (Anticommutes : V → Prop)
    (degree : Nat → V → Nat) : Prop where
  unique : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
    u ∈ U s → O.AtMostOneContainingPath u
  degree_four : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
    u ∈ U s → ¬Anticommutes u → degree s u = 4
  descend : DependentDescentRule U Anticommutes O.SharesPath

/-- The earlier anticommuting witness together with the unique path that
contains it and, consequently, the original commuting vertex. -/
def EarlierAnticommutingWitnessInUniquePath
    (O : FixedPairingPathFamily G)
    (U : Nat → Set V) (Anticommutes : V → Prop)
    (s : Nat) (u : V) : Prop :=
  ∃ s' : Nat, ∃ u' : V, ∃ P : Set V,
    s' < s ∧
    u' ∈ U s' ∧
    Anticommutes u' ∧
    O.IsUniqueContainingPath u' P ∧
    u ∈ P

/-- Lemma 11(b), up to the explicit local claw-free obligations: a commuting
dependent vertex has degree four and admits an earlier anticommuting
dependent witness in the same path component. -/
theorem lemma11b_of_localData
    (O : FixedPairingPathFamily G)
    (U : Nat → Set V) (Anticommutes : V → Prop)
    (degree : Nat → V → Nat)
    (hlocal : O.Lemma11BLocalData U Anticommutes degree)
    {s : Nat} {u : V}
    (hu : u ∈ U s)
    (hcomm : ¬Anticommutes u) :
    degree s u = 4 ∧
      EarlierAnticommutingWitness
        U Anticommutes O.SharesPath s u := by
  refine ⟨hlocal.degree_four hu hcomm, ?_⟩
  exact O.earlierAnticommutingWitness_sharesPath
    U Anticommutes hlocal.unique hlocal.descend hu hcomm

/-- The final clause of Lemma 11(b).  If each possible terminal
anticommuting witness has a unique containing path, the original commuting
vertex lies in that path. -/
theorem lemma11b_with_uniquePath
    (O : FixedPairingPathFamily G)
    (U : Nat → Set V) (Anticommutes : V → Prop)
    (degree : Nat → V → Nat)
    (hlocal : O.Lemma11BLocalData U Anticommutes degree)
    {s : Nat} {u : V}
    (hu : u ∈ U s)
    (hcomm : ¬Anticommutes u)
    (hpath : ∀ ⦃s' : Nat⦄ ⦃u' : V⦄,
      s' < s →
      u' ∈ U s' →
      Anticommutes u' →
      ∃ P : Set V, O.IsUniqueContainingPath u' P) :
    degree s u = 4 ∧
      O.EarlierAnticommutingWitnessInUniquePath
        U Anticommutes s u := by
  obtain ⟨hdegree, s', u', hs', hu', hanti', hshares⟩ :=
    O.lemma11b_of_localData U Anticommutes degree hlocal hu hcomm
  obtain ⟨P, hP⟩ := hpath hs' hu' hanti'
  refine ⟨hdegree, s', u', P, hs', hu', hanti', hP, ?_⟩
  exact O.mem_of_isUniqueContainingPath_of_sharesPath hP hshares

end FixedPairingPathFamily

end SimpleGraph
