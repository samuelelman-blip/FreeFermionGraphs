import FreeFermionGraphs.Lemma11CommonNeighbor

/-!
# Fixed pairing types

Definition 19 distinguishes the `(a,c)` pairing
`a ↔ c', b ↔ d'` from the opposite `(a,d)` pairing
`a ↔ d', b ↔ c'`.  Lemma 11(a.i–ii) compares the pairing type of a
deformation with that of a neighboring clone pair.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

/-- The two fixed pairing types from Definition 19. -/
inductive PairingType where
  | ac
  | ad
deriving DecidableEq, Repr

namespace PairingType

/-- Exchange the two possible fixed pairings. -/
def opposite : PairingType → PairingType
  | ac => ad
  | ad => ac

@[simp]
theorem opposite_ac : opposite ac = ad :=
  rfl

@[simp]
theorem opposite_ad : opposite ad = ac :=
  rfl

@[simp]
theorem opposite_opposite (σ : PairingType) :
    opposite (opposite σ) = σ := by
  cases σ <;> rfl

theorem opposite_ne (σ : PairingType) :
    opposite σ ≠ σ := by
  cases σ <;> simp

/-- A pair `(prime, original)` has pairing type `σ` relative to the four
coloring classes. -/
def Matches (σ : PairingType)
    (Ca Cb Cc Cd : Set V) (prime original : V) : Prop :=
  match σ with
  | ac =>
      (original ∈ Ca ∧ prime ∈ Cc) ∨
      (original ∈ Cb ∧ prime ∈ Cd)
  | ad =>
      (original ∈ Ca ∧ prime ∈ Cd) ∨
      (original ∈ Cb ∧ prime ∈ Cc)

end PairingType

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

/-- Pairing type of an introduced/original vertex pair relative to `O`'s
four coloring classes. -/
def HasPairingType (O : FixedPairingPathFamily G)
    (σ : PairingType) (prime original : V) : Prop :=
  σ.Matches O.Ca O.Cb O.Cc O.Cd prime original

@[simp]
theorem hasPairingType_ac_iff
    (O : FixedPairingPathFamily G) (prime original : V) :
    O.HasPairingType .ac prime original ↔
      ((original ∈ O.Ca ∧ prime ∈ O.Cc) ∨
       (original ∈ O.Cb ∧ prime ∈ O.Cd)) :=
  Iff.rfl

@[simp]
theorem hasPairingType_ad_iff
    (O : FixedPairingPathFamily G) (prime original : V) :
    O.HasPairingType .ad prime original ↔
      ((original ∈ O.Ca ∧ prime ∈ O.Cd) ∨
       (original ∈ O.Cb ∧ prime ∈ O.Cc)) :=
  Iff.rfl

end FixedPairingPathFamily

end SimpleGraph
