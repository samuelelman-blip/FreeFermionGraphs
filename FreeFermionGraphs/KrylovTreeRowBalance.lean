import FreeFermionGraphs.KrylovRowClosedForm
import FreeFermionGraphs.PathClosedNeighborhood
import FreeFermionGraphs.CliqueBubbleWandReverse

/-!
# Balanced Krylov rows of the tree matrix

Manuscript reference: arXiv 2305.15625v1, Lemma 16 (label
`deformationclosurepathsrelation`; statement L1457-1464, proof L1465-1485),
Eq. (pathcircle) (L1520-1523) in case (b.iv) of the proof of Theorem 3, and
Eq. (decoratedtree) (L1434-1445).  (The repo numbers Lemma 16 of v1 as
"Lemma 18", following a revised manuscript that is not available.)

Let `G` be a finite claw-free graph, `K` a simplicial clique, `b : V → R` and
`T = cliqueTreeMatrix G K b`, the tree part of Eq. (decoratedtree), indexed by
the rooted induced paths of `G* = G.adjoinRootAt K`.  The closed form of
`KrylovRowClosedForm.lean`,

`(∑_n X^n (T^n)_{{j*},Q}) · I_V = X^{|Q|-1} · I_{V \ N(Q)}`,

depends on the rooted path `Q` only through `|Q|` and the closed neighbourhood
`N(Q)`.  Hence two paths of equal size and equal closed neighbourhood have the
same `{j*}`-row entries `(T^n)_{{j*},·}` for every `n`.  This gives, with no
walk-substitution argument:

* `cliqueTreeMatrix_pow_root_eq_of_closedNbhd_eq`: `|P| = |Q|` and
  `N(P) = N(Q)` imply `(T^n)_{{j*},P} = (T^n)_{{j*},Q}`;
* `cliqueTreeMatrix_pow_root_eq_of_closure`: this holds for every `P'` in the
  deformation closure `⟨P⟩` (v1 Definition `deformationclosure`), because a
  deformation preserves `|P|` and `N(P)` (`closedNbhd_eq_of_closure`);
* `cliqueTreeMatrix_pow_root_wandReverse`: this holds for the reversal `P*` of
  a bubble wand on `P`, whether the hoop has odd or even length.  This is the
  tree part of Eq. (pathcircle) (v1 L1520-1523), which asserts
  `(A^m)_{{j*},P} = (A^m)_{{j*},P*}` for the reversed path
  `P* = (P ∪ {j}) \ {j_{s+1}}` of case (b.iv); here it is proved for every
  hoop, not only even ones;
* `paperDeformationClosureLemma_of_evenHoleFree`: Lemma 16 of v1 (L1457-1464),
  literally, for the repo matrix `eqE1WeightedAdjacency` of Eq. (E1), in the
  case where `G` has no even hole.  Then no generalized cycle exists and
  Eq. (decoratedtree) is the tree matrix
  (`eqE1WeightedAdjacency_eq_cliqueTreeMatrix`).

Fidelity.  The name of the last theorem is qualified because of its extra
premise `hfree` (no indexed induced hole of even cardinality).  For graphs with
even holes the matrix `eqE1WeightedAdjacency` with the canonical weights of the
repo (`canonicalBubbleWandClassNormalization`) is *not* a valid witness for
this Lemma.  Counterexample (an exact-arithmetic computation, not formalised in
Lean): `G` on `{0, …, 6}` with edges `01, 02, 03, 05, 06, 12, 14, 25, 34, 35,
36, 46, 56`, simplicial clique `K = {2, 5}` (`G` is claw-free, and there is one
bubble-wand class `{0134, 0146}`), `P = (j*, 2, 0)`, its single-vertex
deformation `P~ = (j*, 5, 0)` (`5 ≺ 2`), squared couplings
`(b_0², …, b_6²) = (4, 4, 1, 3, 5, 4, 4)` and `λ = 3`.  Then
`(A^6)_{{j*},P} = 428` but `(A^6)_{{j*},P~} = 422`.  Moreover v1's own proof of
the Lemma (L1465-1485) has a gap: the last-crossing substitution of arcs is not
defined on every walk.  The statements above about `cliqueTreeMatrix` are
unconditional in the sense of the manuscript setup: they use only that `G` is
finite and claw-free and that `K` is a simplicial clique.

The hypothesis `3 ≤ |P|` of the final theorem is `ℓ ≥ 2` of v1 (L1457: the
Lemma is stated for induced paths `j* - j_1 - … - j_ℓ` with `ℓ ≥ 2`); it is not
needed by the proof.
-/

open scoped BigOperators

universe u w

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V} {K : Set V}

section Balance

variable [Fintype V] [DecidableEq V] {R : Type w} [CommRing R]
  [DecidableEq (CliqueRootedInducedPath G K)]

/-- **Balanced rows of the tree matrix.**  If two rooted induced paths `P`, `Q`
of `G*` have the same number of vertices and the same closed neighbourhood,
then `(T^n)_{{j*},P} = (T^n)_{{j*},Q}` for every `n`, where
`T = cliqueTreeMatrix G K b`.

Proof: by the closed form `krylovRow_mul_indepSeries` the series
`∑_n X^n (T^n)_{{j*},P}`, multiplied by the unit `I_V`, equals
`X^{|P|-1} I_{V \ N(P)}`, which depends only on `|P|` and `N(P)`; cancel the
unit and compare coefficients.  (Auxiliary statement behind v1 Lemma 16,
L1457-1464, for the tree part of Eq. (decoratedtree); the argument is new,
replacing the walk-substitution proof L1465-1485.) -/
theorem cliqueTreeMatrix_pow_root_eq_of_closedNbhd_eq
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree) (b : V → R)
    {P Q : CliqueRootedInducedPath G K}
    (hcard : P.path.card = Q.path.card) (hN : P.closedNbhd = Q.closedNbhd)
    (n : ℕ) :
    (cliqueTreeMatrix G K b ^ n) (cliqueRootPath G K) P =
      (cliqueTreeMatrix G K b ^ n) (cliqueRootPath G K) Q := by
  have hP := krylovRow_mul_indepSeries hK hclaw b P
  have hQ := krylovRow_mul_indepSeries hK hclaw b Q
  rw [hcard, hN, ← hQ] at hP
  have hunit := isUnit_indepSeries G (fun v => b v ^ 2) (Finset.univ : Finset V)
  have hser := (hunit.mul_left_inj).1 hP
  have hn := congrArg (PowerSeries.coeff n) hser
  simpa only [PowerSeries.coeff_mk] using hn

/-- **Balanced rows on a deformation closure** (v1 Lemma 16, label
`deformationclosurepathsrelation`, L1457-1464, for the tree matrix, without the
hypothesis `ℓ ≥ 2`): if `P'` lies in the deformation closure `⟨P⟩` of `P` in
`G*`, then
`(T^n)_{{j*},P} = (T^n)_{{j*},P'}` for every `n`.

A deformation preserves the number of vertices and the closed neighbourhood
(`InInducedPathDeformationClosure.card_eq`, `closedNbhd_eq_of_closure`), so
this is `cliqueTreeMatrix_pow_root_eq_of_closedNbhd_eq`. -/
theorem cliqueTreeMatrix_pow_root_eq_of_closure
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree) (b : V → R)
    {P P' : CliqueRootedInducedPath G K}
    (h : InInducedPathDeformationClosure (G.adjoinRootAt K) P.path P'.path)
    (n : ℕ) :
    (cliqueTreeMatrix G K b ^ n) (cliqueRootPath G K) P =
      (cliqueTreeMatrix G K b ^ n) (cliqueRootPath G K) P' :=
  cliqueTreeMatrix_pow_root_eq_of_closedNbhd_eq hK hclaw b
    h.card_eq.symm (RootedInducedPath.closedNbhd_eq_of_closure hK hclaw h).symm n

/-- **Balanced rows under a bubble-wand reversal**, the tree part of
Eq. (pathcircle) (v1 L1520-1523): for a bubble wand `w` on `P` (the hoop may have
odd or even length), `(T^n)_{{j*},P} = (T^n)_{{j*},P*}` for every `n`, where
`P* = w.reverse` traverses the hoop in the opposite direction.

The reversal preserves the number of vertices (`CliqueBubbleWand.reverse_card`)
and, for claw-free `G`, the closed neighbourhood
(`CliqueBubbleWand.closedNbhd_reverse`). -/
theorem cliqueTreeMatrix_pow_root_wandReverse
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree) (b : V → R)
    {P : CliqueRootedInducedPath G K} (w : CliqueBubbleWand G K P) (n : ℕ) :
    (cliqueTreeMatrix G K b ^ n) (cliqueRootPath G K) P =
      (cliqueTreeMatrix G K b ^ n) (cliqueRootPath G K) w.reverse :=
  cliqueTreeMatrix_pow_root_eq_of_closedNbhd_eq hK hclaw b
    w.reverse_card.symm (w.closedNbhd_reverse hclaw).symm n

end Balance

section PaperLemma

variable [Fintype V] [DecidableEq V] {R : Type w} [Field R]
  [DecidableEq (CliqueRootedInducedPath G K)]

/-- **The deformation-closure Lemma of v1 for graphs without even holes**
(v1 Lemma 16, label `deformationclosurepathsrelation`, statement L1457-1464,
proof L1465-1485).

Let `G` be a finite claw-free graph with no even hole, `K` a simplicial
clique, `W` the weight data of Eq. (E1) and `A = eqE1WeightedAdjacency G K W`
the weighted adjacency matrix of Eq. (decoratedtree) on the rooted induced
paths of `G*`.  If `P'` lies in the deformation closure `⟨P⟩` of a rooted path
`P` with `|P| ≥ 3` (that is, `ℓ ≥ 2`), then `(A^k)_{{j*},P} = (A^k)_{{j*},P'}`
for all `k ≥ 0`.

Since `G` has no even hole, no bubble-wand arc exists, so `A` is the tree
matrix with `b = W.coupling` (`eqE1WeightedAdjacency_eq_cliqueTreeMatrix`) and
the statement is `cliqueTreeMatrix_pow_root_eq_of_closure`.  The qualification
`_of_evenHoleFree` records the premise `hfree`, which is not a hypothesis of
the manuscript Lemma; for graphs with even holes the canonical `W` is not a
valid witness (see the file header), so no unqualified name is given.  The
hypothesis `hlen` is the literal `ℓ ≥ 2` and is not used. -/
theorem paperDeformationClosureLemma_of_evenHoleFree
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree)
    (hfree : ∀ C : G.IndexedInducedHole, ¬ Even C.card)
    (W : EqE1WeightData G K R)
    {P P' : CliqueRootedInducedPath G K} (hlen : 3 ≤ P.path.card)
    (h : InInducedPathDeformationClosure (G.adjoinRootAt K) P.path P'.path)
    (k : ℕ) :
    (eqE1WeightedAdjacency G K W ^ k) (cliqueRootPath G K) P =
      (eqE1WeightedAdjacency G K W ^ k) (cliqueRootPath G K) P' := by
  have _ := hlen
  rw [eqE1WeightedAdjacency_eq_cliqueTreeMatrix hfree W]
  exact cliqueTreeMatrix_pow_root_eq_of_closure hK hclaw W.coupling h k

end PaperLemma

end SimpleGraph
