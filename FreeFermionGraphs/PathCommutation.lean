import FreeFermionGraphs.Lemma11Degree

/-!
# Path commutation parity

For the frustration graph, a vertex term anticommutes with a product over a
path exactly when it is adjacent to an odd number of terms in that product.
This file records the parity model used by Lemma 11.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- Vertices of `S` adjacent to `u`. -/
def adjacentIn (G : SimpleGraph V) (u : V) (S : Set V) : Set V :=
  {v | v ∈ S ∧ G.Adj u v}

/-- The number of terms in `S` that anticommute with the term at `u`. -/
noncomputable def adjacencyCount (G : SimpleGraph V)
    (u : V) (S : Set V) : Nat :=
  (G.adjacentIn u S).ncard

/-- The term at `u` commutes with the product over `S` when the number of
adjacent factors is even. -/
def CommutesWithSet (G : SimpleGraph V) (u : V) (S : Set V) : Prop :=
  G.adjacencyCount u S % 2 = 0

/-- The term at `u` anticommutes with the product over `S` when the
number of adjacent factors is odd. -/
def AnticommutesWithSet (G : SimpleGraph V) (u : V) (S : Set V) : Prop :=
  G.adjacencyCount u S % 2 = 1

theorem commutesWithSet_or_anticommutesWithSet
    (G : SimpleGraph V) (u : V) (S : Set V) :
    G.CommutesWithSet u S ∨ G.AnticommutesWithSet u S := by
  unfold CommutesWithSet AnticommutesWithSet
  have hmod : G.adjacencyCount u S % 2 < 2 :=
    Nat.mod_lt _ (by omega)
  omega

theorem not_commutesWithSet_and_anticommutesWithSet
    (G : SimpleGraph V) (u : V) (S : Set V) :
    ¬(G.CommutesWithSet u S ∧ G.AnticommutesWithSet u S) := by
  rintro ⟨hcomm, hanti⟩
  unfold CommutesWithSet at hcomm
  unfold AnticommutesWithSet at hanti
  omega

theorem anticommutesWithSet_iff_not_commutesWithSet
    (G : SimpleGraph V) (u : V) (S : Set V) :
    G.AnticommutesWithSet u S ↔ ¬G.CommutesWithSet u S := by
  constructor
  · intro hanti hcomm
    exact G.not_commutesWithSet_and_anticommutesWithSet u S
      ⟨hcomm, hanti⟩
  · intro hnot
    rcases G.commutesWithSet_or_anticommutesWithSet u S with
      hcomm | hanti
    · exact (hnot hcomm).elim
    · exact hanti

theorem commutesWithSet_iff_not_anticommutesWithSet
    (G : SimpleGraph V) (u : V) (S : Set V) :
    G.CommutesWithSet u S ↔ ¬G.AnticommutesWithSet u S := by
  constructor
  · intro hcomm hanti
    exact G.not_commutesWithSet_and_anticommutesWithSet u S
      ⟨hcomm, hanti⟩
  · intro hnot
    rcases G.commutesWithSet_or_anticommutesWithSet u S with
      hcomm | hanti
    · exact hcomm
    · exact (hnot hanti).elim

namespace IndexedInducedPath

/-- Commutation of `h_u` with the product over an indexed induced path. -/
def CommutesWith (P : IndexedInducedPath G) (u : V) : Prop :=
  G.CommutesWithSet u (Set.range P.vertex)

/-- Anticommutation of `h_u` with the product over an indexed induced
path. -/
def AnticommutesWith (P : IndexedInducedPath G) (u : V) : Prop :=
  G.AnticommutesWithSet u (Set.range P.vertex)

theorem commutesWith_or_anticommutesWith
    (P : IndexedInducedPath G) (u : V) :
    P.CommutesWith u ∨ P.AnticommutesWith u :=
  G.commutesWithSet_or_anticommutesWithSet u (Set.range P.vertex)

theorem anticommutesWith_iff_not_commutesWith
    (P : IndexedInducedPath G) (u : V) :
    P.AnticommutesWith u ↔ ¬P.CommutesWith u :=
  G.anticommutesWithSet_iff_not_commutesWithSet
    u (Set.range P.vertex)

end IndexedInducedPath

end SimpleGraph
