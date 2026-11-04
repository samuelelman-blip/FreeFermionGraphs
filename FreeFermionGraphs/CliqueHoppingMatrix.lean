import FreeFermionGraphs.CliqueBubbleWand
import FreeFermionGraphs.BubbleWandEventClassUnique
import FreeFermionGraphs.EvenHoleDeformationQuotient

/-!
# The corrected matrix of Eq. (decoratedtree): root-handle arcs, sign and
per-event normalisation

arXiv 2305.15625v1, Eq. (decoratedtree), L1434-1445, and the normalisation
sentence on L1445.  This file defines the matrix `A_λ = T + W` on the rooted
induced paths of `G* = G + j*` (`CliqueRootedInducedPath G K`) and proves its
entrywise properties.

* `T = cliqueTreeMatrix G K b` is the tree part (the first two cases of the
  printed equation: weight `1` for `P → P + x` and `b_x ^ 2` for `P + x → P`).
* `W = ` the even-hoop part (the third case): every bubble event `(P, j)`, that
  is, a `CliqueBubbleWand G K P` with bubble `j`, handle `Q` and an even hoop
  `C` of size `2k` in the deformation class `c`, contributes
  `(-1) ^ (k - 1) * λ_c / |c|` to the entry `W_{PQ}`, where `|c|` is the number
  of carriers of the class `c` (`evenHoleClassSize`).  Since all events of one
  arc `P → Q` lie in one class (claw-freeness,
  `evenHoleDeformationClassOf_hoopCarrier_eq`), the entry is
  `(-1) ^ (k - 1) * λ_c * m(P, Q) / |c|` with `m(P, Q)` the number of bubbles
  realising `P → Q` (`cliqueHoppingMatrix_hoop`).

## Deviations from the printed equation

The printed third case `λ_{⟨C₀⟩} / N_{P,P',⟨C₀⟩}` is not the matrix for which
the Krylov identity of Theorem 3 holds.  Three corrections are made.  Each was
checked numerically in dense Pauli representations (the fiducial
representation of Ref. `chapman2022free`, with exact sector projectors of the
generalized cycle symmetries; 6 hand-made graphs and 25 random claw-free
graphs with a simplicial clique, one of them with a class of two holes).  With
the weights of this file the operator identity
`ad^k χ · Π = Σ_P (-2i)^k (A_λ^k)_{{j*}, P} h_P · Π`
holds up to rounding error (at most `5e-15`).  It fails with the repo weights
(per-arc normalisation by the targets of one source, no sign, no root arcs),
with the corrected weights without the sign (errors up to `14`), and with the
signed weights under the literal normalisation (errors up to `5.6`).

1. *Missing sign.*  The printed weight carries no sign.  With v1's own
   convention `h_C = h_{C_a} h_{C_b}` (L313), reordering the product
   `h_{j_{s+1}} ⋯ h_{j_ℓ} h_j` of a hoop with `2k` vertices into the colour
   order takes `k - 1` transpositions of anticommuting factors, so
   `h_P h_j = (-1)^{k-1} h_{P_s} h_C`.  The weight is therefore
   `(-1)^{k-1} λ_c` (a `C₄` hoop, `k = 2`, has sign `-`; a `C₆` hoop has sign
   `+`; see `Example.hopping_root_entry`).  The sign is read off the carrier of
   each event (its hoop size, `ncard / 2`), so no class-level half-length
   function is needed.

2. *Root-handle arcs.*  The third case includes the arcs into the root path
   `P → {j*}` (split index `s = 0`): v1's labelling starts at `j₀ = j*`
   (L303, L692-698) and the proof of Theorem 3 uses `0 ≤ s` (L1520).  The
   repo's `EvenHoopBubbleWandArc` omits them (for `C₄` with `K` an edge the repo
   matrix has no hoop arc at all, and the Krylov identity fails with relative
   error `0.29` to `6.6`).  Here the events are `CliqueBubbleWand`s
   (`CliqueBubbleWand.lean`), whose handle is allowed to be the root path.

3. *Normalisation.*  v1 requires `(1/2) Σ_{P'} N_{P,P',⟨C₀⟩}^{-1} = 1`.  Read
   literally (fixed source `P`, sum over the targets `P'`) the resulting matrix
   violates Theorem 3 (for example a `C₄` attached after a handle) and the
   deformation lemma (`deformationclosurepathsrelation`, L1457-1465).
   Counterexample to the lemma: `G` on `{0, …, 6}` with edges `01 02 03 05 06
   12 14 25 34 35 36 46 56`, `K = {2, 5}`, `P = (j*, 2, 0)`, `P~ = (j*, 5, 0)`,
   `b² = (4, 4, 1, 3, 5, 4, 4)`, `λ = 3`.  The repo weights give
   `(A^6)_{j*,P} = 428` but `(A^6)_{j*,P~} = 422`; the signed weights under the
   literal normalisation give `380` and `386`; the weights of this file give
   `398` for both.  The cause is that the source `(j*, 5, 0, 1, 4)` reaches
   the handle `(j*, 5)` through two bubbles (`3` and `6`), a multiplicity that a
   per-arc normalisation ignores.  The reading consistent with the Krylov
   identity normalises per bubble event, `N_{P,Q,c} = |c| / m(P, Q)`: the sum
   runs over the *sources* of a fixed handle.  The column total over the
   sources is then `2 (-1)^{k-1} λ_c`, the factor `2` being the two directions
   around the hole, as in v1's own remark.  (That column identity needs the
   attachment uniformity of holes and is not part of this file.)

A further minor point: the printed second case "`P = P ∖ {j}`" is read as
`P' = P ∖ {j}`, with `j` the terminal vertex of the source `P`
(`cliqueTreeMatrix`).

The matrix is defined over any field `R` (division by `|c|`).  Being a matrix
over `R`, `A_λ` is real for real `b` and `λ`; `cliqueHoppingMatrix_map` records
that it commutes with ring homomorphisms (for example the inclusion of the
reals into the complex numbers).  Statements that use `|c| ≠ 0` need a field
of characteristic zero; the size itself is positive
(`evenHoleClassSize_pos`).

Main declarations.

* `evenHoleClassSize`: the number `|c|` of carriers in a deformation class;
* `evenHoleDeformationClassOf_hoopCarrier_eq`: the hoops of two wands on `P`
  with the same handle lie in one deformation class (claw-free graphs);
* `cliqueHoppingMatrix`: the matrix `A_λ`;
* `cliqueHoppingMatrix_of_evenHoleFree`: `A_λ = T` without even holes;
* `cliqueHoppingMatrix_eq_zero_of_not_arc`: support on the arcs of `Λ`;
* `cliqueHoppingMatrix_eq_zero_of_even`: bipartiteness;
* `cliqueHoppingMatrix_hoop`: the closed form of an arc entry.
-/

open scoped BigOperators

universe u v w

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V} {K : Set V}

/-! ### The size of a deformation class -/

section ClassSize

variable [Fintype V] [DecidableEq V]

/-- The number `|c|` of carriers in an even-hole deformation class `c`
(v1 L1445: the class `⟨C₀⟩`).  For the class of a carrier `C` this is the size
of its finite deformation closure `⟨C⟩` (`evenHoleClassSize_classOf`).  The
classes of the quotient `EvenHoleDeformationClass` range over all sets of
vertices; for the class of an even hole this is v1's `|⟨C₀⟩|` provided that
every carrier in the closure of a hole is again a hole carrier, which is not
needed or proved here. -/
noncomputable def evenHoleClassSize (c : EvenHoleDeformationClass G) : ℕ :=
  Quotient.liftOn c (fun C => (G.deformationClosureFinset C).card)
    (fun _ _ h => by
      rw [deformationClosureFinset_eq_of_mem (show InEvenHoleDeformationClosure G _ _ from h)])

/-- The size of the class of a carrier `C` is the size of its closure. -/
theorem evenHoleClassSize_classOf (C : Set V) :
    evenHoleClassSize (G.evenHoleDeformationClassOf C) =
      (G.deformationClosureFinset C).card :=
  rfl

/-- Every deformation class has at least one carrier. -/
theorem evenHoleClassSize_pos (c : EvenHoleDeformationClass G) :
    0 < evenHoleClassSize c := by
  induction c using Quotient.inductionOn with
  | _ C =>
    exact Finset.card_pos.2
      ⟨C, mem_deformationClosureFinset.2
        (InEvenHoleDeformationClosure.refl C)⟩

end ClassSize

/-! ### Hoops of wands with a common handle lie in one class -/

namespace EvenHoleLabeling

/-- Two even-hole labelings whose carriers are `X ∪ {j}` and `X ∪ {j'}` with
`j, j' ∉ X` lie in one deformation class when `G` is claw-free: the carriers
differ by one single-vertex deformation (`cloneAt_of_shared_deletion`).  This
is the carrier-level form of `bubbleWandEventClassUnique_of_isClawFree`,
stated without the event structure of `EvenHoopBubbleWandEvent`. -/
theorem evenHoleDeformationClassOf_eq_of_swap
    (hclaw : G.IsClawFree) {k l : Nat}
    (C : EvenHoleLabeling G k) (D : EvenHoleLabeling G l) {X : Set V}
    {j j' : V} (hj : j ∉ X) (hj' : j' ∉ X)
    (hC : C.carrier = X ∪ {j}) (hD : D.carrier = X ∪ {j'}) :
    G.evenHoleDeformationClassOf C.carrier =
      G.evenHoleDeformationClassOf D.carrier := by
  by_cases hjj : j = j'
  · subst hjj
    rw [hC, hD]
  have hjmem : j ∈ C.carrier := by
    rw [hC]
    exact Or.inr rfl
  have hj'out : j' ∉ C.carrier := by
    rw [hC]
    rintro (h | h)
    · exact hj' h
    · exact hjj (Set.mem_singleton_iff.1 h).symm
  rcases hjmem with ⟨i, hi⟩ | ⟨i, hi⟩
  · have hcarrier : D.carrier = C.deformedCarrier j' i := by
      rw [hD]
      unfold deformedCarrier
      rw [hC]
      ext v
      simp only [Set.mem_union, Set.mem_singleton_iff, hi]
      constructor
      · rintro (h | h)
        · right
          exact ⟨Or.inl h, fun hvj => hj (hvj ▸ h)⟩
        · left
          exact h
      · rintro (h | ⟨h | h, hne⟩)
        · right
          exact h
        · left
          exact h
        · exact absurd h hne
    have hclone := C.cloneAt_of_shared_deletion D j' i hclaw hj'out hcarrier
    rw [hcarrier]
    exact evenHoleDeformationClassOf_eq_of_step
      ⟨k, C, j', i, hclone, Or.inl ⟨rfl, rfl⟩⟩
  · let C' := C.swapColors
    have hi' : C'.a i = j := hi
    have hC' : C'.carrier = X ∪ {j} := by
      rw [swapColors_carrier]
      exact hC
    have hj'out' : j' ∉ C'.carrier := by
      rw [hC']
      rintro (h | h)
      · exact hj' h
      · exact hjj (Set.mem_singleton_iff.1 h).symm
    have hcarrier : D.carrier = C'.deformedCarrier j' i := by
      rw [hD]
      unfold deformedCarrier
      rw [hC']
      ext v
      simp only [Set.mem_union, Set.mem_singleton_iff, hi']
      constructor
      · rintro (h | h)
        · right
          exact ⟨Or.inl h, fun hvj => hj (hvj ▸ h)⟩
        · left
          exact h
      · rintro (h | ⟨h | h, hne⟩)
        · right
          exact h
        · left
          exact h
        · exact absurd h hne
    have hclone := C'.cloneAt_of_shared_deletion D j' i hclaw hj'out' hcarrier
    have hstep := evenHoleDeformationClassOf_eq_of_step
      (⟨k, C', j', i, hclone, Or.inl ⟨rfl, rfl⟩⟩ :
        EvenHoleDeformationStep G C'.carrier (C'.deformedCarrier j' i))
    rw [swapColors_carrier] at hstep
    rw [hstep, hcarrier]

end EvenHoleLabeling

namespace CliqueBubbleWand

variable {P : CliqueRootedInducedPath G K}

theorem hoopCarrier_eq (w : CliqueBubbleWand G K P) :
    w.hoopCarrier =
      (P.originalCarrier \ w.handle.originalCarrier) ∪ {w.bubble} :=
  rfl

/-- The bubble is not among the original vertices of the path. -/
theorem bubble_notMem_originalCarrier (w : CliqueBubbleWand G K P) :
    w.bubble ∉ P.originalCarrier := fun ⟨q, hq⟩ => w.outside ⟨q, hq⟩

/-- The hoop carrier has `ℓ - s + 1` elements. -/
theorem hoopCarrier_ncard (w : CliqueBubbleWand G K P) :
    w.hoopCarrier.ncard = w.hoopCard := by
  rw [← w.range_hoopHole, Set.ncard_range_of_injective w.hoopHole.injective,
    Nat.card_eq_fintype_card, Fintype.card_fin, w.hoopHole_card]

/-- A wand is determined, up to its split index, by its handle: two wands on
`P` with the same handle have the same hoop size. -/
theorem hoopCard_eq_of_handle_eq (w w' : CliqueBubbleWand G K P)
    (h : w.handle = w'.handle) : w.hoopCard = w'.hoopCard := by
  have h2 : w.handle.path.card = w'.handle.path.card := by rw [h]
  simp only [handle_card] at h2
  unfold hoopCard
  omega

/-- The bubble of a wand with handle `Q` lies outside the common part
`P ∖ Q` of the hoop carriers. -/
theorem bubble_notMem_diff (w : CliqueBubbleWand G K P) :
    w.bubble ∉ P.originalCarrier \ w.handle.originalCarrier :=
  fun h => w.bubble_notMem_originalCarrier h.1

/-- In a claw-free graph, the hoops of two bubble wands on `P` with the same
handle and an even hoop lie in one even-hole deformation class: their carriers
differ by one single-vertex deformation.  This is the version of
`bubbleWandEventClassUnique_of_isClawFree` for `CliqueBubbleWand` events
(root handle included), which the older lemma, stated for
`EvenHoopBubbleWandEvent`, does not cover. -/
theorem evenHoleDeformationClassOf_hoopCarrier_eq
    (hclaw : G.IsClawFree) (w w' : CliqueBubbleWand G K P)
    (h : w.handle = w'.handle) (he : Even w.hoopCard) :
    G.evenHoleDeformationClassOf w.hoopCarrier =
      G.evenHoleDeformationClassOf w'.hoopCarrier := by
  have he' : Even w'.hoopCard := (hoopCard_eq_of_handle_eq w w' h) ▸ he
  obtain ⟨k, E, hE⟩ := w.hoopHole.exists_evenHoleLabeling
    (by rw [w.hoopHole_card]; exact he)
  obtain ⟨l, E', hE'⟩ := w'.hoopHole.exists_evenHoleLabeling
    (by rw [w'.hoopHole_card]; exact he')
  have hcarr : E.carrier = (P.originalCarrier \ w.handle.originalCarrier) ∪
      {w.bubble} := by
    rw [hE, w.range_hoopHole]
    rfl
  have hcarr' : E'.carrier = (P.originalCarrier \ w.handle.originalCarrier) ∪
      {w'.bubble} := by
    rw [hE', w'.range_hoopHole, h]
    rfl
  have hj' : w'.bubble ∉ P.originalCarrier \ w.handle.originalCarrier := by
    rw [h]
    exact w'.bubble_notMem_diff
  have key := EvenHoleLabeling.evenHoleDeformationClassOf_eq_of_swap hclaw E E'
    w.bubble_notMem_diff hj' hcarr hcarr'
  have hw' : w'.hoopCarrier =
      (P.originalCarrier \ w.handle.originalCarrier) ∪ {w'.bubble} := by
    rw [w'.hoopCarrier_eq, h]
  rw [hcarr, hcarr'] at key
  rw [hw']
  exact key

end CliqueBubbleWand

/-! ### The matrix -/

/-- The corrected matrix `A_λ = T + W` of Eq. (decoratedtree) (v1 L1434-1445)
on the rooted induced paths of `G* = G + j*`, `K` the simplicial clique.

* `T = cliqueTreeMatrix G K b`: weight `1` for `P → P + x`, weight `b_x ^ 2`
  for `P + x → P`;
* `W_{PQ}` is the sum, over the bubbles `j` realising the arc `P → Q` (a
  `CliqueBubbleWand G K P` with bubble `j`, handle `Q` and an even hoop `C`),
  of `(-1) ^ (k - 1) * λ_c / |c|`, where `2k = |C|` is the size of the hoop
  carrier and `c ∋ C` is its deformation class.

Compared with the printed third case `λ / N`: a sign `(-1)^{k-1}` is added,
the root handle `Q = {j*}` is allowed, and the normalisation is `|c|` per
bubble event (see the module docstring).  Over any field `R`; `lam c` is the
eigenvalue of the generalized cycle symmetry of the class `c` on the
sector. -/
noncomputable def cliqueHoppingMatrix [Fintype V] [DecidableEq V]
    {R : Type w} [Field R]
    (G : SimpleGraph V) (K : Set V) (b : V → R)
    (lam : EvenHoleDeformationClass G → R) :
    Matrix (CliqueRootedInducedPath G K) (CliqueRootedInducedPath G K) R := by
  classical
  exact fun P Q => cliqueTreeMatrix G K b P Q + ∑ j : V,
    if ∃ w : CliqueBubbleWand G K P, w.bubble = j ∧ w.handle = Q ∧
        Even w.hoopCard then
      (-1 : R) ^ ((bubbleWandArcHoopCarrier P Q j).ncard / 2 - 1) *
        lam (G.evenHoleDeformationClassOf (bubbleWandArcHoopCarrier P Q j)) /
        (evenHoleClassSize
          (G.evenHoleDeformationClassOf (bubbleWandArcHoopCarrier P Q j)) : R)
    else 0

section Entries

variable [Fintype V] [DecidableEq V] {R : Type w} [Field R]
variable {b : V → R} {lam : EvenHoleDeformationClass G → R}

/-- Without an even-hoop arc `P → Q` the entry is the tree entry. -/
theorem cliqueHoppingMatrix_eq_tree_of_not_evenHoopArc
    {P Q : CliqueRootedInducedPath G K} (h : ¬EvenHoopArc G K P Q) :
    cliqueHoppingMatrix G K b lam P Q = cliqueTreeMatrix G K b P Q := by
  classical
  unfold cliqueHoppingMatrix
  rw [Finset.sum_eq_zero, add_zero]
  intro j _
  rw [if_neg]
  rintro ⟨w, _, hw, hev⟩
  exact h ⟨w, hw, hev⟩

/-- For graphs without even holes there are no even-hoop arcs, so `A_λ` is
the tree matrix `T` for every `λ`. -/
theorem cliqueHoppingMatrix_of_evenHoleFree
    (hfree : ∀ C : G.IndexedInducedHole, ¬Even C.card)
    (b : V → R) (lam : EvenHoleDeformationClass G → R) :
    cliqueHoppingMatrix G K b lam = cliqueTreeMatrix G K b := by
  ext P Q
  apply cliqueHoppingMatrix_eq_tree_of_not_evenHoopArc
  intro h
  obtain ⟨C, hC⟩ := h.exists_even_hole
  exact hfree C hC

/-- The entries vanish off the arcs of the directed hopping graph `Λ`:
the tree edges and the even-hoop arcs (root handle included). -/
theorem cliqueHoppingMatrix_eq_zero_of_not_arc (hK : G.IsClique K)
    {P Q : CliqueRootedInducedPath G K}
    (h : ¬(cliqueDirectedHoppingGraph G K hK).Arc P Q) :
    cliqueHoppingMatrix G K b lam P Q = 0 := by
  have h' : ¬((G.inducedPathTreeAtClique K hK).Adj P Q ∨ EvenHoopArc G K P Q) := h
  rw [cliqueHoppingMatrix_eq_tree_of_not_evenHoopArc (fun he => h' (Or.inr he))]
  exact cliqueTreeMatrix_eq_zero_of_not_treeAdjacent b
    (fun ht => h' (Or.inl ht))

/-- A nonzero entry is an arc of `Λ`. -/
theorem cliqueHoppingMatrix_ne_zero_imp_arc (hK : G.IsClique K)
    {P Q : CliqueRootedInducedPath G K}
    (h : cliqueHoppingMatrix G K b lam P Q ≠ 0) :
    (cliqueDirectedHoppingGraph G K hK).Arc P Q := by
  by_contra hnot
  exact h (cliqueHoppingMatrix_eq_zero_of_not_arc (b := b) (lam := lam) hK hnot)

omit [Fintype V] [DecidableEq V] in
/-- An even-hoop arc `P → Q` drops the cardinality by the hoop size minus
one, which is odd. -/
theorem EvenHoopArc.odd_card_add {P Q : CliqueRootedInducedPath G K}
    (h : EvenHoopArc G K P Q) : Odd (P.path.card + Q.path.card) := by
  obtain ⟨w, rfl, ⟨m, hm⟩⟩ := h
  have hgap := w.gap
  unfold CliqueBubbleWand.hoopCard at hm
  refine ⟨m + w.split.val, ?_⟩
  simp only [CliqueBubbleWand.handle_card]
  omega

/-- Bipartiteness: `A_λ` vanishes unless `|P| + |Q|` is odd. -/
theorem cliqueHoppingMatrix_eq_zero_of_even
    {P Q : CliqueRootedInducedPath G K}
    (h : Even (P.path.card + Q.path.card)) :
    cliqueHoppingMatrix G K b lam P Q = 0 := by
  by_cases hA : EvenHoopArc G K P Q
  · exact absurd h (Nat.not_even_iff_odd.mpr hA.odd_card_add)
  · rw [cliqueHoppingMatrix_eq_tree_of_not_evenHoopArc hA]
    exact cliqueTreeMatrix_eq_zero_of_even b h

/-- A nonzero entry joins paths of opposite cardinality parity. -/
theorem cliqueHoppingMatrix_ne_zero_imp_odd
    {P Q : CliqueRootedInducedPath G K}
    (h : cliqueHoppingMatrix G K b lam P Q ≠ 0) :
    Odd (P.path.card + Q.path.card) := by
  by_contra hodd
  exact h (cliqueHoppingMatrix_eq_zero_of_even (b := b) (lam := lam)
    (Nat.not_odd_iff_even.mp hodd))

/-- The closed form of an arc entry (claw-free `G`).  If a bubble wand `w`
on `P` has handle `Q` and an even hoop `C` of size `2k` in the deformation
class `c`, then
`A_λ(P, Q) = (-1)^{k-1} λ_c · m(P, Q) / |c|`,
where `m(P, Q)` is the number of bubbles `j` realising the arc `P → Q`.  The
arc `P → Q` is not an edge of the induced-path tree, so the tree part
vanishes.  (v1 Eq. (decoratedtree), third case, with the sign, the root
handle and the per-event normalisation of the module docstring.) -/
theorem cliqueHoppingMatrix_hoop (hclaw : G.IsClawFree)
    {P Q : CliqueRootedInducedPath G K} (w : CliqueBubbleWand G K P)
    (hQ : w.handle = Q) (he : Even w.hoopCard) :
    cliqueHoppingMatrix G K b lam P Q =
      (-1 : R) ^ (w.hoopCard / 2 - 1) *
        lam (G.evenHoleDeformationClassOf w.hoopCarrier) *
        (Nat.card {j : V // ∃ w' : CliqueBubbleWand G K P,
          w'.bubble = j ∧ w'.handle = Q} : R) /
        (evenHoleClassSize (G.evenHoleDeformationClassOf w.hoopCarrier) : R) := by
  classical
  subst hQ
  have htree : cliqueTreeMatrix G K b P w.handle = 0 :=
    cliqueTreeMatrix_eq_zero_of_not_treeAdjacent b
      (EvenHoopArc.not_treeAdjacent ⟨w, rfl, he⟩)
  set S : R := (-1 : R) ^ (w.hoopCard / 2 - 1) *
    lam (G.evenHoleDeformationClassOf w.hoopCarrier) /
      (evenHoleClassSize (G.evenHoleDeformationClassOf w.hoopCarrier) : R)
    with hS
  have hterm : ∀ j : V,
      (if ∃ w' : CliqueBubbleWand G K P, w'.bubble = j ∧
          w'.handle = w.handle ∧ Even w'.hoopCard then
        (-1 : R) ^ ((bubbleWandArcHoopCarrier P w.handle j).ncard / 2 - 1) *
          lam (G.evenHoleDeformationClassOf
            (bubbleWandArcHoopCarrier P w.handle j)) /
          (evenHoleClassSize (G.evenHoleDeformationClassOf
            (bubbleWandArcHoopCarrier P w.handle j)) : R)
       else 0) =
      if ∃ w' : CliqueBubbleWand G K P, w'.bubble = j ∧ w'.handle = w.handle
        then S else 0 := by
    intro j
    by_cases hj : ∃ w' : CliqueBubbleWand G K P,
        w'.bubble = j ∧ w'.handle = w.handle
    · obtain ⟨w', hb, hh⟩ := hj
      have hev : Even w'.hoopCard :=
        (CliqueBubbleWand.hoopCard_eq_of_handle_eq w w' hh.symm) ▸ he
      rw [if_pos ⟨w', hb, hh, hev⟩, if_pos ⟨w', hb, hh⟩]
      have hcar : bubbleWandArcHoopCarrier P w.handle j = w'.hoopCarrier := by
        unfold CliqueBubbleWand.hoopCarrier
        rw [hh, hb]
      rw [hcar, w'.hoopCarrier_ncard, hS,
        CliqueBubbleWand.hoopCard_eq_of_handle_eq w' w hh,
        CliqueBubbleWand.evenHoleDeformationClassOf_hoopCarrier_eq hclaw w' w hh
          (CliqueBubbleWand.hoopCard_eq_of_handle_eq w w' hh.symm ▸ he)]
    · rw [if_neg, if_neg hj]
      rintro ⟨w', hb, hh, _⟩
      exact hj ⟨w', hb, hh⟩
  unfold cliqueHoppingMatrix
  rw [htree, zero_add, Finset.sum_congr rfl (fun j _ => hterm j),
    ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    Nat.card_eq_fintype_card, Fintype.card_subtype, hS]
  ring

/-- The ring-homomorphism naturality of `A_λ`: mapping the data `b` and `λ`
along `f : R →+* S` maps the matrix entrywise.  In particular `A_λ` is real
for real `b` and `λ`, in the sense that its complex form is the image of its
real form under the inclusion `ℝ → ℂ`. -/
theorem cliqueHoppingMatrix_map {S : Type*} [Field S] (f : R →+* S) :
    (cliqueHoppingMatrix G K b lam).map f =
      cliqueHoppingMatrix G K (fun v => f (b v)) (fun c => f (lam c)) := by
  classical
  ext P Q
  have htree : f (cliqueTreeMatrix G K b P Q) =
      cliqueTreeMatrix G K (fun v => f (b v)) P Q := by
    unfold cliqueTreeMatrix
    split_ifs
    · exact map_one f
    · cases P.terminalVertex with
      | none => exact map_zero f
      | some j => exact map_pow f (b j) 2
    · exact map_zero f
  simp only [Matrix.map_apply]
  unfold cliqueHoppingMatrix
  simp only [map_add, map_sum, htree]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  split_ifs
  · simp [map_div₀, map_mul, map_pow, map_neg, map_one]
  · exact map_zero f

end Entries

/-! ### A worked example: the 4-cycle with an edge clique

The graph `G = C₄` (`0 - 1 - 2 - 3 - 0`) with the clique `K = {0, 1}` and the
path `P = (j*, 0, 3, 2)` has the root-handle arc `P → {j*}` of
`CliqueBubbleWand.Example`, realised by the single bubble `1`.  The hoop is the
whole 4-cycle, `k = 2`, so the sign is `-1`, the class `⟨C₄⟩` has the single
carrier `univ`, and `A_λ(P, {j*}) = -λ`.  This entry is exactly the one that
the repo matrix lacks (root handle) and that the unsigned printed formula has
with the wrong sign. -/

namespace CliqueBubbleWand

namespace Example

instance : DecidableRel fourCycle.Adj := fun a b =>
  inferInstanceAs (Decidable ((a.val + 1) % 4 = b.val ∨ (b.val + 1) % 4 = a.val))

set_option synthInstance.maxSize 512 in
theorem fourCycle_isClawFree : fourCycle.IsClawFree := by
  have h : ∀ c a b d : Fin 4, fourCycle.Adj c a → fourCycle.Adj c b →
      fourCycle.Adj c d → a ≠ b → a ≠ d → b ≠ d →
      fourCycle.Adj a b ∨ fourCycle.Adj a d ∨ fourCycle.Adj b d := by
    decide
  intro c a b d h1 h2 h3 h4 h5 h6
  exact h c a b d h1 h2 h3 h4 h5 h6

/-- The only bubble of a wand on `(j*, 0, 3, 2)` is `1`. -/
theorem bubble_eq_one (w' : CliqueBubbleWand fourCycle edgeClique path) :
    w'.bubble = 1 := by
  have h := w'.outside
  generalize w'.bubble = j at h ⊢
  fin_cases j
  · exact (h ⟨⟨1, by decide⟩, rfl⟩).elim
  · rfl
  · exact (h ⟨⟨3, by decide⟩, rfl⟩).elim
  · exact (h ⟨⟨2, by decide⟩, rfl⟩).elim

/-- The hoop carrier of the wand is the whole vertex set. -/
theorem wand_hoopCarrier : wand.hoopCarrier = Set.univ := by
  rw [wand.hoopCarrier_eq]
  ext v
  simp only [Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_univ,
    iff_true]
  by_cases hv : v = 1
  · exact Or.inr hv
  · left
    refine ⟨?_, ?_⟩
    · fin_cases v
      · exact ⟨⟨1, by decide⟩, rfl⟩
      · exact (hv rfl).elim
      · exact ⟨⟨3, by decide⟩, rfl⟩
      · exact ⟨⟨2, by decide⟩, rfl⟩
    · intro h
      obtain ⟨q, hq, hv'⟩ := (wand.mem_handle_originalCarrier_iff v).1 h
      have hq0 : q = ⟨0, path.path.nonempty⟩ := Fin.ext (by
        have : wand.split.val = 0 := rfl
        show q.val = 0
        omega)
      subst hq0
      exact absurd (path.root_eq.symm.trans hv') (by simp)

/-- The closure of the carrier `univ` is `{univ}`: no single-vertex
deformation starts or ends at the whole vertex set. -/
theorem closure_univ {B : Set (Fin 4)}
    (h : InEvenHoleDeformationClosure fourCycle Set.univ B) :
    B = Set.univ := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    subst ih
    exfalso
    obtain ⟨k, C, s, i, hclone, ⟨hA, _⟩ | ⟨hA, _⟩⟩ := hstep
    · exact hclone.outside (hA ▸ Set.mem_univ s)
    · have hai : C.a i ∈ C.deformedCarrier s i := hA ▸ Set.mem_univ (C.a i)
      rcases Set.mem_insert_iff.1 hai with h1 | ⟨_, h2⟩
      · exact hclone.outside (h1 ▸ C.a_mem_carrier i)
      · exact h2 rfl

theorem classSize_univ :
    evenHoleClassSize (fourCycle.evenHoleDeformationClassOf Set.univ) = 1 := by
  rw [evenHoleClassSize_classOf, Finset.card_eq_one]
  refine ⟨Set.univ, ?_⟩
  ext B
  rw [mem_deformationClosureFinset, Finset.mem_singleton]
  exact ⟨closure_univ, fun h => h ▸ InEvenHoleDeformationClosure.refl _⟩

/-- Exactly one bubble realises the root-handle arc `P → {j*}`. -/
theorem card_bubbles :
    Nat.card {j : Fin 4 // ∃ w' : CliqueBubbleWand fourCycle edgeClique path,
      w'.bubble = j ∧ w'.handle = cliqueRootPath fourCycle edgeClique} = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => ?_⟩, ⟨⟨1, wand, rfl, wand_handle⟩⟩⟩
  obtain ⟨a, w1, h1, _⟩ := a
  obtain ⟨b, w2, h2, _⟩ := b
  apply Subtype.ext
  change a = b
  rw [← h1, ← h2, bubble_eq_one w1, bubble_eq_one w2]

/-- The root-handle entry of the corrected matrix for the 4-cycle is `-λ`:
sign `(-1)^{k-1} = -1` for `k = 2`, one bubble, class size one. -/
theorem hopping_root_entry {R : Type} [Field R] (b : Fin 4 → R)
    (lam : EvenHoleDeformationClass fourCycle → R) :
    cliqueHoppingMatrix fourCycle edgeClique b lam path
        (cliqueRootPath fourCycle edgeClique) =
      -lam (fourCycle.evenHoleDeformationClassOf Set.univ) := by
  have h := cliqueHoppingMatrix_hoop (b := b) (lam := lam) fourCycle_isClawFree wand
    wand_handle (by decide)
  rw [wand_hoopCarrier, card_bubbles, classSize_univ] at h
  have h4 : wand.hoopCard = 4 := rfl
  rw [h4] at h
  simpa using h

end Example

end CliqueBubbleWand

end SimpleGraph
