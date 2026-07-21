import FreeFermionGraphs.Lemma11AFullDefinition19History
import FreeFermionGraphs.Lemma11ABackwardCarrier
import FreeFermionGraphs.ThreeNeighbors

/-!
# Lemma 11(a): recovery of the original hole

This file supplies the carrier and triangle arguments which are implicit in
the manuscript's notation `C`.  In particular, a common neighbour at a
dependent step is an original-hole vertex, and in the degree-three case the
clone centre cannot be the introduced path vertex.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace EvenHoleLabeling

/-- An alternating even-hole carrier contains no triangle. -/
theorem not_triangle_of_mem_carrier
    {k : Nat} (C : EvenHoleLabeling G k)
    {x y z : V}
    (hx : x ∈ C.carrier) (hy : y ∈ C.carrier)
    (hz : z ∈ C.carrier) :
    ¬(G.Adj x y ∧ G.Adj y z ∧ G.Adj x z) := by
  change x ∈ Set.range C.a ∪ Set.range C.b at hx
  change y ∈ Set.range C.a ∪ Set.range C.b at hy
  change z ∈ Set.range C.a ∪ Set.range C.b at hz
  rcases hx with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
    rcases hy with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
    rcases hz with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · rintro ⟨hij, _hjq, _hiq⟩
    exact C.adj_aa i j hij
  · rintro ⟨hij, _hjq, _hiq⟩
    exact C.adj_aa i j hij
  · rintro ⟨_hij, _hjq, hiq⟩
    exact C.adj_aa i q hiq
  · rintro ⟨_hij, hjq, _hiq⟩
    exact C.adj_bb j q hjq
  · rintro ⟨_hij, hjq, _hiq⟩
    exact C.adj_aa j q hjq
  · rintro ⟨_hij, _hjq, hiq⟩
    exact C.adj_bb i q hiq
  · rintro ⟨hij, _hjq, _hiq⟩
    exact C.adj_bb i j hij
  · rintro ⟨hij, _hjq, _hiq⟩
    exact C.adj_bb i j hij

end EvenHoleLabeling

namespace FixedPairingPathFamily

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

namespace ConcretePathDeformation

/-- A dependent anticommuting vertex is outside the hole immediately before
its path block.  This follows from exact fourth-class membership, rather
than being an additional hypothesis of Lemma 11(a). -/
theorem dependent_not_mem_initialHole_of_anticommutes
    (D : ConcretePathDeformation O Cprime)
    (F : D.FullDefinition19Lemma11AData)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPrime : u ∈ Cprime)
    (hanti : D.path.AnticommutesWith u) :
    u ∉ Set.range D.initialHole.vertex := by
  have hlocal :=
    (D.lemma11a_membership_iff_ne_first_and_degree
      F hclaw huPrime hanti).mp ⟨s, hu⟩
  have huOutsidePath : u ∉ Set.range D.path.vertex :=
    F.anticommuting_not_mem_path huPrime hlocal.1 hanti
  have huExact : ExactlyOneOfFour u O.Ca O.Cb O.Cc O.Cd :=
    F.neighborhood.mechanical.dependent_exactlyOne_of_outside
      F.neighborhood.overlapColoring hu huOutsidePath
  have huCd : u ∈ O.Cd :=
    F.neighborhood.mechanical.dependent_mem_cd hu
  have huNot : u ∉ O.Ca ∧ u ∉ O.Cb ∧ u ∉ O.Cc :=
    ExactlyOneOfFour.not_mem_first_three_of_mem_fourth huExact huCd
  intro huInitial
  have huBefore :
      u ∈ Set.range
        (D.deformation.step D.firstIndex).before.vertex := by
    simpa [ConcretePathDeformation.initialHole] using huInitial
  rcases
      (F.neighborhood.mechanical.stepGeometry D.firstIndex).before_subset
        huBefore with huCa | huCb
  · exact huNot.1 huCa
  · exact huNot.2.1 huCb

/-- A common neighbour of a dependent vertex and the introduced vertex
cannot itself lie on the unchanged prime hole, since that would form a
triangle in the prime hole. -/
theorem commonNeighbor_not_mem_prime
    (D : ConcretePathDeformation O Cprime)
    (P : D.PrimeAlternatingHoleData kPrime)
    (i : Fin D.deformation.stepCount)
    {u v : V}
    (huPrime : u ∈ Cprime)
    (huIntroduced : G.Adj u (D.deformation.step i).introduced)
    (huv : G.Adj u v)
    (hintroducedv : G.Adj (D.deformation.step i).introduced v) :
    v ∉ Cprime := by
  intro hvPrime
  apply P.labeling.not_triangle_of_mem_carrier
      (P.mem_carrier_of_mem_prime huPrime)
      (P.mem_carrier_of_mem_prime hvPrime)
      (P.mem_carrier_of_mem_prime (P.introduced_mem i))
  exact ⟨huv, hintroducedv.symm, huIntroduced⟩

/-- A vertex removed at any step of a path block was already present on
the block's initial hole.  Even introduced path indices and odd removed
path indices rule out every obstruction to backward transport. -/
theorem removed_mem_initialHole
    (D : ConcretePathDeformation O Cprime)
    (F : D.FullDefinition19Lemma11AData)
    (i : Fin D.deformation.stepCount) :
    (D.deformation.step i).before.vertex
        (D.deformation.step i).removedIndex ∈
      Set.range D.initialHole.vertex := by
  apply D.mem_initialHole_of_mem_before_at i.val i.isLt
  · intro j _hj hEq
    apply D.introducedPathIndex_ne_removedPathIndex
      F.neighborhood.pathOrder j i
    apply D.path.injective
    calc
      D.path.vertex
          (F.neighborhood.pathOrder.introducedPathIndex j) =
          (D.deformation.step j).introduced :=
        F.neighborhood.pathOrder.introduced_eq j
      _ = (D.deformation.step i).before.vertex
          (D.deformation.step i).removedIndex := hEq.symm
      _ = D.path.vertex
          (F.neighborhood.pathOrder.removedPathIndex i) :=
        (F.neighborhood.pathOrder.removed_eq i).symm
  · exact ⟨(D.deformation.step i).removedIndex, rfl⟩

/-- A current removed vertex also belongs to the globally original hole
when there is a nonempty prefix of earlier, distinct Definition 19 path
blocks. -/
theorem currentRemoved_mem_original_of_fullDefinition19History
    (D : ConcretePathDeformation O Cprime)
    (X : D.FullDefinition19Lemma11AHistoryData)
    (i : Fin D.deformation.stepCount) :
    (D.deformation.step i).before.vertex
        (D.deformation.step i).removedIndex ∈
      Set.range (X.history.block 0).initialHole.vertex := by
  let k : V := (D.deformation.step i).before.vertex
    (D.deformation.step i).removedIndex
  let last : Nat := X.priorCount - 1
  have hkCurrentInitial : k ∈ Set.range D.initialHole.vertex := by
    simpa [k] using D.removed_mem_initialHole X.current i
  have hkLast :
      k ∈ Set.range (X.history.block last).finalHole.vertex := by
    rw [X.final_before_current]
    exact hkCurrentInitial
  have hcurrentAc : Set.range D.path.vertex ∈ O.acPaths := by
    rw [← D.activePath_eq i]
    exact (X.current.neighborhood.mechanical.stepGeometry i).base.activePath_ac
  have hkCurrentPath : k ∈ Set.range D.path.vertex := by
    refine ⟨X.current.neighborhood.pathOrder.removedPathIndex i, ?_⟩
    simpa [k] using X.current.neighborhood.pathOrder.removed_eq i
  have hkOriginal :=
    X.history.mem_firstInitial_of_mem_final_through last hkLast (by
      intro r hr j hEq
      have hrPrior : r < X.priorCount := by
        dsimp [last] at hr
        have hpos := X.priorCount_pos
        omega
      have hpriorAc :
          Set.range (X.history.block r).path.vertex ∈ O.acPaths := by
        rw [← (X.history.block r).activePath_eq j]
        exact ((X.prior r).neighborhood.mechanical.stepGeometry j).base.activePath_ac
      have hpriorIntroduced :
          ((X.history.block r).deformation.step j).introduced ∈
            Set.range (X.history.block r).path.vertex := by
        rw [← (X.history.block r).activePath_eq j]
        exact ((X.history.block r).deformation.step j).introduced_mem_activePath
      have hcurrentIntroduced :
          ((X.history.block r).deformation.step j).introduced ∈
            Set.range D.path.vertex := by
        rw [← hEq]
        exact hkCurrentPath
      exact (X.priorPath_ne_current r hrPrior)
        (O.eq_of_mem_acPaths hpriorAc hcurrentAc
          hpriorIntroduced hcurrentIntroduced))
  simpa [k] using hkOriginal

/-- Coloring core of Lemma 11(a.ii).  If an original-hole clone centre
were in `C_b`, independence and the common `C_b` neighbour would identify
the two.  The adjacent `C_a` removed vertex would then also neighbor the
clone, contradicting Definition 20. -/
theorem cloneCenter_mem_ca_of_commonNeighbor
    (O : FixedPairingPathFamily G)
    (C : IndexedInducedHole G)
    (hindep : O.ColorClassesIndependent)
    {u v k : V} {q : Fin C.card}
    (hcarrier : Set.range C.vertex ⊆ O.Ca ∪ O.Cb)
    (hclone : C.SingleVertexDeformation u q)
    (hvC : v ∈ Set.range C.vertex)
    (hvCb : v ∈ O.Cb)
    (hkC : k ∈ Set.range C.vertex)
    (huv : G.Adj u v)
    (hkv : G.Adj k v)
    (huk : ¬G.Adj u k) :
    C.vertex q ∈ O.Ca := by
  rcases hcarrier ⟨q, rfl⟩ with hqCa | hqCb
  · exact hqCa
  · exfalso
    obtain ⟨p, hp⟩ := hvC
    have hpq : p = q := by
      rcases (hclone.adj_iff p).mp (by simpa [hp] using huv) with hpq | hqp
      · exact hpq
      · exact (hindep.cb hqCb hvCb (by simpa [hp] using hqp)).elim
    have hcenterV : C.vertex q = v := by
      rw [← hp, hpq]
    obtain ⟨r, hr⟩ := hkC
    have hcenterK : G.Adj (C.vertex q) (C.vertex r) := by
      rw [hcenterV, hr]
      exact hkv.symm
    apply huk
    rw [← hr]
    exact hclone.adj_of_clone_adj hcenterK

/-- The concrete common neighbour at a dependent step belongs to both the
initial and final holes of the path block, lies in `C_b`, and is not a
prime-hole vertex. -/
theorem lemma11ai_commonNeighbor_currentBlock
    (D : ConcretePathDeformation O Cprime)
    (F : D.FullDefinition19Lemma11AData)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s) :
    ∃ v : V,
      v ∈ Set.range D.initialHole.vertex ∧
      v ∈ Set.range D.finalHole.vertex ∧
      G.Adj u v ∧
      G.Adj
        (D.deformation.step
          ⟨s, D.index_lt_of_mem_dependentAt hu⟩).introduced v ∧
      G.Adj
        ((D.deformation.step
          ⟨s, D.index_lt_of_mem_dependentAt hu⟩).before.vertex
            (D.deformation.step
              ⟨s, D.index_lt_of_mem_dependentAt hu⟩).removedIndex) v ∧
      v ∈ O.Cb ∧ v ∉ Cprime := by
  let i : Fin D.deformation.stepCount :=
    ⟨s, D.index_lt_of_mem_dependentAt hu⟩
  have hui : u ∈ (D.deformation.step i).dependentSet :=
    D.mem_step_dependentSet_of_mem_dependentAt hu
  have humem := (D.deformation.step i).mem_dependentSet.mp hui
  obtain ⟨v, hvBefore, huv, hintroducedv, hremovedv, hvCb⟩ :=
    (D.deformation.step i).dependent_commonNeighbor_mem_cb
      (F.neighborhood.mechanical.stepGeometry i) hclaw hui
      (F.neighborhood.mechanical.outsideHole i hui)
  have hvNotPrime : v ∉ Cprime :=
    D.commonNeighbor_not_mem_prime F.neighborhood.primeHole i
      humem.1 humem.2.1 huv hintroducedv
  have hvNotCa : v ∉ O.Ca := by
    intro hvCa
    exact (F.neighborhood.mechanical.stepGeometry i).ca_independent
      (F.neighborhood.mechanical.stepGeometry i).removed_ca
      hvCa hremovedv
  have hvNotCc : v ∉ O.Cc := by
    intro hvCc
    exact (F.neighborhood.mechanical.stepGeometry i).base.cc_independent
      (F.neighborhood.mechanical.stepGeometry i).base.introduced_cc
      hvCc hintroducedv
  have hvOutsidePath : v ∉ Set.range D.path.vertex := by
    intro hvPath
    have hpathAc : Set.range D.path.vertex ∈ O.acPaths := by
      rw [← D.activePath_eq i]
      exact (F.neighborhood.mechanical.stepGeometry i).base.activePath_ac
    rcases O.ac_subset (Set.range D.path.vertex) hpathAc hvPath with
      hvCa | hvCc
    · exact hvNotCa hvCa
    · exact hvNotCc hvCc
  have hvInitial : v ∈ Set.range D.initialHole.vertex :=
    D.mem_initialHole_of_mem_before_at i.val i.isLt
      (fun j _hj hvj => hvNotPrime
        (hvj ▸ F.neighborhood.primeHole.introduced_mem j))
      hvBefore
  have hvFinal : v ∈ Set.range D.finalHole.vertex :=
    D.mem_finalHole_of_mem_initialHole_of_not_mem_path
      hvInitial hvOutsidePath
  exact ⟨v, hvInitial, hvFinal, huv, hintroducedv,
    hremovedv, hvCb, hvNotPrime⟩

/-- The original-hole clone centre in Lemma 11(a.ii) lies in `C_a` when
the current block is the first Definition 19 block. -/
theorem lemma11aii_cloneCenter_mem_ca_of_firstBlock
    (D : ConcretePathDeformation O Cprime)
    (F : D.FullDefinition19Lemma11AData)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    {q : Fin D.initialHole.card}
    (hclone : D.initialHole.SingleVertexDeformation u q) :
    D.initialHole.vertex q ∈ O.Ca := by
  let i : Fin D.deformation.stepCount :=
    ⟨s, D.index_lt_of_mem_dependentAt hu⟩
  obtain ⟨v, hvInitial, _hvFinal, huv, _hintroducedv,
      hremovedv, hvCb, _hvNotPrime⟩ :=
    D.lemma11ai_commonNeighbor_currentBlock F hclaw hu
  let k : V := (D.deformation.step i).before.vertex
    (D.deformation.step i).removedIndex
  have hkInitial : k ∈ Set.range D.initialHole.vertex := by
    simpa [k] using D.removed_mem_initialHole F i
  have hui : u ∈ (D.deformation.step i).dependentSet :=
    D.mem_step_dependentSet_of_mem_dependentAt hu
  have huk : ¬G.Adj u k := by
    simpa [k] using ((D.deformation.step i).mem_dependentSet.mp hui).2.2.2
  have hcarrier : Set.range D.initialHole.vertex ⊆ O.Ca ∪ O.Cb := by
    intro x hx
    apply (F.neighborhood.mechanical.stepGeometry D.firstIndex).before_subset
    simpa [ConcretePathDeformation.initialHole] using hx
  exact cloneCenter_mem_ca_of_commonNeighbor O D.initialHole
    F.neighborhood.colorClassesIndependent hcarrier hclone
    hvInitial hvCb hkInitial huv (by simpa [k] using hremovedv) huk

/-- The original-hole clone centre in Lemma 11(a.ii) lies in `C_a` through
a nonempty finite prefix of earlier Definition 19 blocks. -/
theorem lemma11aii_cloneCenter_mem_ca_of_fullDefinition19History
    (D : ConcretePathDeformation O Cprime)
    (X : D.FullDefinition19Lemma11AHistoryData)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    {q : Fin (X.history.block 0).initialHole.card}
    (hclone :
      (X.history.block 0).initialHole.SingleVertexDeformation u q) :
    (X.history.block 0).initialHole.vertex q ∈ O.Ca := by
  let i : Fin D.deformation.stepCount :=
    ⟨s, D.index_lt_of_mem_dependentAt hu⟩
  obtain ⟨v, hvCurrentInitial, _hvFinal, huv, _hintroducedv,
      hremovedv, hvCb, hvNotPrime⟩ :=
    D.lemma11ai_commonNeighbor_currentBlock X.current hclaw hu
  let k : V := (D.deformation.step i).before.vertex
    (D.deformation.step i).removedIndex
  let last : Nat := X.priorCount - 1
  have hvLast :
      v ∈ Set.range (X.history.block last).finalHole.vertex := by
    rw [X.final_before_current]
    exact hvCurrentInitial
  have hvOriginal :
      v ∈ Set.range (X.history.block 0).initialHole.vertex :=
    X.history.mem_firstInitial_of_mem_final_through last hvLast (by
      intro r _hr j hEq
      apply hvNotPrime
      rw [hEq]
      exact (X.prior r).neighborhood.primeHole.introduced_mem j)
  have hkOriginal :
      k ∈ Set.range (X.history.block 0).initialHole.vertex := by
    simpa [k] using
      D.currentRemoved_mem_original_of_fullDefinition19History X i
  have hui : u ∈ (D.deformation.step i).dependentSet :=
    D.mem_step_dependentSet_of_mem_dependentAt hu
  have huk : ¬G.Adj u k := by
    simpa [k] using ((D.deformation.step i).mem_dependentSet.mp hui).2.2.2
  have hcarrier :
      Set.range (X.history.block 0).initialHole.vertex ⊆ O.Ca ∪ O.Cb := by
    intro x hx
    apply ((X.prior 0).neighborhood.mechanical.stepGeometry
      (X.history.block 0).firstIndex).before_subset
    simpa [ConcretePathDeformation.initialHole] using hx
  exact cloneCenter_mem_ca_of_commonNeighbor O
    (X.history.block 0).initialHole
    X.current.neighborhood.colorClassesIndependent hcarrier hclone
    hvOriginal hvCb hkOriginal huv (by simpa [k] using hremovedv) huk

/-- In the final degree-three case, the clone centre cannot be the path
vertex introduced at the dependent step.  Otherwise the two nonadjacent
cycle neighbours of that introduced vertex would be the two neighbours of
`u` in the initial hole, contradicting Lemma 7. -/
theorem lemma11ai_cloneCenter_ne_currentIntroduced
    (D : ConcretePathDeformation O Cprime)
    (F : D.FullDefinition19Lemma11AData)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPrime : u ∈ Cprime)
    (hanti : D.path.AnticommutesWith u)
    (hthree : D.finalHole.externalDegree u = 3)
    {q : Fin D.finalHole.card}
    (hclone : D.finalHole.SingleVertexDeformation u q) :
    D.finalHole.vertex q ≠
      (D.deformation.step
        ⟨s, D.index_lt_of_mem_dependentAt hu⟩).introduced := by
  let i : Fin D.deformation.stepCount :=
    ⟨s, D.index_lt_of_mem_dependentAt hu⟩
  intro hcenter
  obtain ⟨p, r, hpr, hqp, hqr, hprNonadj⟩ :=
    D.finalHole.exists_two_nonadjacent_neighbors q
  have hup : G.Adj u (D.finalHole.vertex p) :=
    hclone.adj_of_clone_adj hqp
  have hur : G.Adj u (D.finalHole.vertex r) :=
    hclone.adj_of_clone_adj hqr
  have hjp : G.Adj (D.deformation.step i).introduced
      (D.finalHole.vertex p) := by
    rw [← hcenter]
    exact hqp
  have hjr : G.Adj (D.deformation.step i).introduced
      (D.finalHole.vertex r) := by
    rw [← hcenter]
    exact hqr
  have hpNotIntroduced : ∀ j : Fin D.deformation.stepCount,
      D.finalHole.vertex p ≠ (D.deformation.step j).introduced := by
    intro j hpj
    have hpCc : D.finalHole.vertex p ∈ O.Cc := by
      rw [hpj]
      exact (F.neighborhood.mechanical.stepGeometry j).base.introduced_cc
    exact (F.neighborhood.mechanical.stepGeometry i).base.cc_independent
      (F.neighborhood.mechanical.stepGeometry i).base.introduced_cc
      hpCc hjp
  have hrNotIntroduced : ∀ j : Fin D.deformation.stepCount,
      D.finalHole.vertex r ≠ (D.deformation.step j).introduced := by
    intro j hrj
    have hrCc : D.finalHole.vertex r ∈ O.Cc := by
      rw [hrj]
      exact (F.neighborhood.mechanical.stepGeometry j).base.introduced_cc
    exact (F.neighborhood.mechanical.stepGeometry i).base.cc_independent
      (F.neighborhood.mechanical.stepGeometry i).base.introduced_cc
      hrCc hjr
  have hpInitial :
      D.finalHole.vertex p ∈ Set.range D.initialHole.vertex :=
    D.mem_initialHole_of_mem_finalHole_of_ne_introduced
      ⟨p, rfl⟩ hpNotIntroduced
  have hrInitial :
      D.finalHole.vertex r ∈ Set.range D.initialHole.vertex :=
    D.mem_initialHole_of_mem_finalHole_of_ne_introduced
      ⟨r, rfl⟩ hrNotIntroduced
  obtain ⟨p₀, hp₀⟩ := hpInitial
  obtain ⟨r₀, hr₀⟩ := hrInitial
  have hp₀r₀ : p₀ ≠ r₀ := by
    intro hEq
    apply hpr
    apply D.finalHole.injective
    calc
      D.finalHole.vertex p = D.initialHole.vertex p₀ := hp₀.symm
      _ = D.initialHole.vertex r₀ := by rw [hEq]
      _ = D.finalHole.vertex r := hr₀
  have hup₀ : G.Adj u (D.initialHole.vertex p₀) := by
    rw [hp₀]
    exact hup
  have hur₀ : G.Adj u (D.initialHole.vertex r₀) := by
    rw [hr₀]
    exact hur
  have hp₀r₀Nonadj :
      ¬G.Adj (D.initialHole.vertex p₀) (D.initialHole.vertex r₀) := by
    rw [hp₀, hr₀]
    exact hprNonadj
  have hlocal :=
    (D.lemma11a_membership_iff_ne_first_and_degree
      F hclaw huPrime hanti).mp ⟨s, hu⟩
  have htwo : D.initialHole.externalDegree u = 2 := by omega
  change (D.initialHole.neighborIndexSet u).ncard = 2 at htwo
  have hpairSubset :
      ({p₀, r₀} : Set (Fin D.initialHole.card)) ⊆
        D.initialHole.neighborIndexSet u := by
    intro t ht
    rcases Set.mem_insert_iff.mp ht with rfl | ht
    · exact hup₀
    · have htr : t = r₀ := Set.mem_singleton_iff.mp ht
      subst t
      exact hur₀
  have hpairCard : ({p₀, r₀} : Set (Fin D.initialHole.card)).ncard = 2 := by
    simp [hp₀r₀]
  have hpairEq :
      ({p₀, r₀} : Set (Fin D.initialHole.card)) =
        D.initialHole.neighborIndexSet u :=
    Set.eq_of_subset_of_ncard_le hpairSubset (by
      rw [htwo, hpairCard])
  have hexact : ∀ t : Fin D.initialHole.card,
      G.Adj u (D.initialHole.vertex t) → t = p₀ ∨ t = r₀ := by
    intro t ht
    have htmem : t ∈ D.initialHole.neighborIndexSet u := ht
    rw [← hpairEq] at htmem
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using htmem
  have huOutsideInitial :=
    D.dependent_not_mem_initialHole_of_anticommutes
      F hclaw hu huPrime hanti
  rcases D.initialHole.lemma7 hclaw huOutsideInitial with
      hzero | htwoCase | hthreeCase | hfourCase | hfiveCase
  · omega
  · exact hp₀r₀Nonadj
      (htwoCase.2 p₀ r₀ hp₀r₀ hup₀ hur₀ hexact)
  · omega
  · omega
  · omega

/-- In the final degree-three case, the clone centre is the persistent
`C_b` common neighbour supplied by the dependent step. -/
theorem lemma11ai_cloneCenter_is_commonNeighbor
    (D : ConcretePathDeformation O Cprime)
    (F : D.FullDefinition19Lemma11AData)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPrime : u ∈ Cprime)
    (hanti : D.path.AnticommutesWith u)
    (hthree : D.finalHole.externalDegree u = 3)
    {q : Fin D.finalHole.card}
    (hclone : D.finalHole.SingleVertexDeformation u q) :
    ∃ v : V,
      v ∈ Set.range D.initialHole.vertex ∧
      v ∈ Set.range D.finalHole.vertex ∧
      D.finalHole.vertex q = v ∧
      G.Adj u v ∧
      v ∈ O.Cb ∧ v ∉ Cprime := by
  let i : Fin D.deformation.stepCount :=
    ⟨s, D.index_lt_of_mem_dependentAt hu⟩
  obtain ⟨v, hvInitial, hvFinal, huv, hintroducedv,
      _hremovedv, hvCb, hvNotPrime⟩ :=
    D.lemma11ai_commonNeighbor_currentBlock F hclaw hu
  obtain ⟨p, hp⟩ := hvFinal
  obtain ⟨j, hj⟩ :=
    D.introduced_mem_finalHole F.neighborhood.pathOrder i
  have hui : u ∈ (D.deformation.step i).dependentSet :=
    D.mem_step_dependentSet_of_mem_dependentAt hu
  have huIntroduced : G.Adj u (D.deformation.step i).introduced :=
    ((D.deformation.step i).mem_dependentSet.mp hui).2.1
  have hcenterNe :
      D.finalHole.vertex q ≠ (D.deformation.step i).introduced :=
    D.lemma11ai_cloneCenter_ne_currentIntroduced
      F hclaw hu huPrime hanti hthree hclone
  have hqj : q ≠ j := by
    intro hqj
    apply hcenterNe
    rw [hqj, hj]
  have hpq : p = q := by
    by_contra hpq
    have hqp : G.Adj (D.finalHole.vertex q) (D.finalHole.vertex p) := by
      rcases (hclone.adj_iff p).mp (by simpa [hp] using huv) with hpq' | hqp
      · exact (hpq hpq').elim
      · exact hqp
    have hqjAdj : G.Adj (D.finalHole.vertex q) (D.finalHole.vertex j) := by
      rcases (hclone.adj_iff j).mp (by simpa [hj] using huIntroduced) with
          hjq | hqjAdj
      · exact (hqj hjq.symm).elim
      · exact hqjAdj
    have hpj : G.Adj (D.finalHole.vertex p) (D.finalHole.vertex j) := by
      simpa [hp, hj] using hintroducedv.symm
    exact D.finalHole.not_triangle q p j ⟨hqp, hpj, hqjAdj⟩
  refine ⟨v, hvInitial, ⟨p, hp⟩, ?_, huv, hvCb, hvNotPrime⟩
  rw [← hp, hpq]

/-- Lemma 11(a.i) for the first Definition 19 path block: a final-hole
degree-three clone centre belongs to the block's original hole and has the
same fixed pairing as the path. -/
theorem lemma11ai_of_firstBlock
    (D : ConcretePathDeformation O Cprime)
    (F : D.FullDefinition19Lemma11AData)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPrime : u ∈ Cprime)
    (hanti : D.path.AnticommutesWith u)
    (hthree : D.finalHole.externalDegree u = 3)
    {q : Fin D.finalHole.card}
    (hclone : D.finalHole.SingleVertexDeformation u q) :
    D.finalHole.vertex q ∈ Set.range D.initialHole.vertex ∧
      O.HasPairingType .ac u (D.finalHole.vertex q) := by
  obtain ⟨v, hvInitial, _hvFinal, hqv, _huv, hvCb, _hvNotPrime⟩ :=
    D.lemma11ai_cloneCenter_is_commonNeighbor
      F hclaw hu huPrime hanti hthree hclone
  have hui : u ∈
      (D.deformation.step
        ⟨s, D.index_lt_of_mem_dependentAt hu⟩).dependentSet :=
    D.mem_step_dependentSet_of_mem_dependentAt hu
  have huCd : u ∈ O.Cd :=
    (D.deformation.step
      ⟨s, D.index_lt_of_mem_dependentAt hu⟩).dependent_mem_cd
        (F.neighborhood.mechanical.stepGeometry
          ⟨s, D.index_lt_of_mem_dependentAt hu⟩) hui
  rw [hqv]
  exact ⟨hvInitial, O.hasPairingType_of_mem_b .ac hvCb (by simpa using huCd)⟩

/-- Lemma 11(a.i) through a nonempty finite prefix of earlier Definition 19
blocks.  The common neighbour is never introduced by an earlier block,
because every introduced vertex lies on the prime hole while it does not. -/
theorem lemma11ai_of_fullDefinition19History
    (D : ConcretePathDeformation O Cprime)
    (X : D.FullDefinition19Lemma11AHistoryData)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPrime : u ∈ Cprime)
    (hanti : D.path.AnticommutesWith u)
    (hthree : D.finalHole.externalDegree u = 3)
    {q : Fin D.finalHole.card}
    (hclone : D.finalHole.SingleVertexDeformation u q) :
    D.finalHole.vertex q ∈
        Set.range (X.history.block 0).initialHole.vertex ∧
      O.HasPairingType .ac u (D.finalHole.vertex q) := by
  obtain ⟨v, hvCurrentInitial, _hvFinal, hqv, _huv, hvCb, hvNotPrime⟩ :=
    D.lemma11ai_cloneCenter_is_commonNeighbor
      X.current hclaw hu huPrime hanti hthree hclone
  let last : Nat := X.priorCount - 1
  have hlast : last < X.priorCount := by
    dsimp [last]
    have hpos := X.priorCount_pos
    omega
  have hvLast :
      v ∈ Set.range (X.history.block last).finalHole.vertex := by
    rw [X.final_before_current]
    exact hvCurrentInitial
  have hvOriginal :
      v ∈ Set.range (X.history.block 0).initialHole.vertex :=
    X.history.mem_firstInitial_of_mem_final_through last hvLast (by
      intro r hr j hvj
      apply hvNotPrime
      rw [hvj]
      exact (X.prior r).neighborhood.primeHole.introduced_mem j)
  have hui : u ∈
      (D.deformation.step
        ⟨s, D.index_lt_of_mem_dependentAt hu⟩).dependentSet :=
    D.mem_step_dependentSet_of_mem_dependentAt hu
  have huCd : u ∈ O.Cd :=
    (D.deformation.step
      ⟨s, D.index_lt_of_mem_dependentAt hu⟩).dependent_mem_cd
        (X.current.neighborhood.mechanical.stepGeometry
          ⟨s, D.index_lt_of_mem_dependentAt hu⟩) hui
  rw [hqv]
  exact ⟨hvOriginal,
    O.hasPairingType_of_mem_b .ac hvCb (by simpa using huCd)⟩

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
