import FreeFermionGraphs.Lemma11ACorollary11Concrete

/-!
# Proof of Corollary 11 for concrete Definition 19 blocks

This file proves the no-shared-dependent-witness statement used by
Lemma 11(a.ii).  Its inputs describe two distinct path blocks and their
common original hole; the forbidden witness is the conclusion.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace FixedPairingPathFamily

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- The base-step common neighbour of a path block, transported to a
specified original hole. -/
def BaseCommonNeighborOn
    (O : FixedPairingPathFamily G)
    {Cprime : Set V}
    (D : ConcretePathDeformation O Cprime)
    (C : IndexedInducedHole G) : Prop :=
  ∀ ⦃u : V⦄,
    u ∈ D.dependentAt 0 →
      ∃ v : V,
        v ∈ Set.range C.vertex ∧
        G.Adj u v ∧
        G.Adj (D.deformation.step D.firstIndex).introduced v ∧
        G.Adj
          ((D.deformation.step D.firstIndex).before.vertex
            (D.deformation.step D.firstIndex).removedIndex) v ∧
        v ∈ O.Cb

/-- With degree three on a bipartite original hole, two distinct `C_b`
neighbours have a common `C_a` neighbour which is the middle of the
three-neighbour path. -/
theorem degree_three_two_cb_neighbors_have_ca_center
    (O : FixedPairingPathFamily G)
    (C : IndexedInducedHole G)
    (hindep : O.ColorClassesIndependent)
    (hcarrier : Set.range C.vertex ⊆ O.Ca ∪ O.Cb)
    (hclaw : G.IsClawFree)
    {u v w : V}
    (huOutside : u ∉ Set.range C.vertex)
    (hthree : C.externalDegree u = 3)
    (hvC : v ∈ Set.range C.vertex)
    (hwC : w ∈ Set.range C.vertex)
    (hvCb : v ∈ O.Cb) (hwCb : w ∈ O.Cb)
    (huv : G.Adj u v) (huw : G.Adj u w)
    (hvw : v ≠ w) :
    ∃ x : V,
      x ∈ Set.range C.vertex ∧ x ∈ O.Ca ∧
        G.Adj u x ∧ G.Adj v x ∧ G.Adj w x := by
  classical
  obtain ⟨p, hp⟩ := hvC
  obtain ⟨q, hq⟩ := hwC
  have hpq : p ≠ q := by
    intro hpq
    apply hvw
    rw [← hp, ← hq, hpq]
  change (C.neighborIndexSet u).ncard = 3 at hthree
  have hpNeighbor : p ∈ C.neighborIndexSet u := by
    simpa [hp] using huv
  have hqNeighbor : q ∈ C.neighborIndexSet u := by
    simpa [hq] using huw
  have hpqSubset :
      ({p, q} : Set (Fin C.card)) ⊆ C.neighborIndexSet u := by
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact hpNeighbor
    · simpa using ha ▸ hqNeighbor
  have hpqNe :
      ({p, q} : Set (Fin C.card)) ≠ C.neighborIndexSet u := by
    intro heq
    have hcard := congrArg Set.ncard heq
    simp [hpq, hthree] at hcard
  have hstrict :
      ({p, q} : Set (Fin C.card)) ⊂ C.neighborIndexSet u :=
    Set.ssubset_iff_subset_ne.mpr ⟨hpqSubset, hpqNe⟩
  obtain ⟨_hsubset, r, hrNeighbor, hrNotPair⟩ :=
    Set.ssubset_iff_exists.mp hstrict
  have hrp : r ≠ p := by
    intro hrp
    apply hrNotPair
    simp [hrp]
  have hrq : r ≠ q := by
    intro hrq
    apply hrNotPair
    simp [hrq]
  have hknownSubset :
      ({p, q, r} : Set (Fin C.card)) ⊆ C.neighborIndexSet u := by
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact hpNeighbor
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact hqNeighbor
    · simpa using ha ▸ hrNeighbor
  have hknownCard :
      ({p, q, r} : Set (Fin C.card)).ncard = 3 := by
    simp [hpq, Ne.symm hrp, Ne.symm hrq]
  have hknownEq :
      ({p, q, r} : Set (Fin C.card)) = C.neighborIndexSet u :=
    Set.eq_of_subset_of_ncard_le hknownSubset (by
      rw [hthree, hknownCard])
  have hur : G.Adj u (C.vertex r) := hrNeighbor
  have hexact : ∀ a : Fin C.card,
      G.Adj u (C.vertex a) → a = p ∨ a = q ∨ a = r := by
    intro a hua
    have ha : a ∈ C.neighborIndexSet u := hua
    rw [← hknownEq] at ha
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ha
  have hshape := C.three_external_neighbors_induce_path
    hclaw huOutside hpq hrp.symm hrq.symm
    (by simpa [hp] using huv) (by simpa [hq] using huw) hur hexact
  have hpqNonadj : ¬G.Adj (C.vertex p) (C.vertex q) := by
    intro hpqAdj
    exact hindep.cb hvCb hwCb (by simpa [hp, hq] using hpqAdj)
  have hpr : G.Adj (C.vertex p) (C.vertex r) := by
    rcases hshape with hpCenter | hqCenter | hrCenter
    · exact (hpqNonadj hpCenter.1.symm).elim
    · exact (hpqNonadj hqCenter.1).elim
    · exact hrCenter.1
  have hqr : G.Adj (C.vertex q) (C.vertex r) := by
    rcases hshape with hpCenter | hqCenter | hrCenter
    · exact (hpqNonadj hpCenter.1.symm).elim
    · exact (hpqNonadj hqCenter.1).elim
    · exact hrCenter.2.1.symm
  have hrCa : C.vertex r ∈ O.Ca := by
    rcases hcarrier ⟨r, rfl⟩ with hrCa | hrCb
    · exact hrCa
    · exact (hindep.cb hvCb hrCb (by simpa [hp] using hpr)).elim
  exact ⟨C.vertex r, ⟨r, rfl⟩, hrCa, hur,
    by simpa [hp] using hpr, by simpa [hq] using hqr⟩

/-- Four original-hole neighbours include two distinct vertices in `C_a`.
Otherwise three of them lie in the independent class `C_b` and form a
claw with the external vertex. -/
theorem degree_four_has_two_ca_neighbors
    (O : FixedPairingPathFamily G)
    (C : IndexedInducedHole G)
    (hindep : O.ColorClassesIndependent)
    (hcarrier : Set.range C.vertex ⊆ O.Ca ∪ O.Cb)
    (hclaw : G.IsClawFree)
    {u : V}
    (hfour : C.externalDegree u = 4) :
    ∃ w w' : V,
      w ≠ w' ∧
        w ∈ Set.range C.vertex ∧ w' ∈ Set.range C.vertex ∧
        w ∈ O.Ca ∧ w' ∈ O.Ca ∧
        G.Adj u w ∧ G.Adj u w' := by
  classical
  change (C.neighborIndexSet u).ncard = 4 at hfour
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hset⟩ :=
    Set.ncard_eq_four.mp hfour
  have hua : G.Adj u (C.vertex a) := by
    change a ∈ C.neighborIndexSet u
    rw [hset]
    simp
  have hub : G.Adj u (C.vertex b) := by
    change b ∈ C.neighborIndexSet u
    rw [hset]
    simp
  have huc : G.Adj u (C.vertex c) := by
    change c ∈ C.neighborIndexSet u
    rw [hset]
    simp
  have hud : G.Adj u (C.vertex d) := by
    change d ∈ C.neighborIndexSet u
    rw [hset]
    simp
  have noThreeCb
      (x y z : Fin C.card)
      (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
      (hux : G.Adj u (C.vertex x))
      (huy : G.Adj u (C.vertex y))
      (huz : G.Adj u (C.vertex z))
      (hxCb : C.vertex x ∈ O.Cb)
      (hyCb : C.vertex y ∈ O.Cb)
      (hzCb : C.vertex z ∈ O.Cb) : False := by
    have hxyv : C.vertex x ≠ C.vertex y := fun h => hxy (C.injective h)
    have hxzv : C.vertex x ≠ C.vertex z := fun h => hxz (C.injective h)
    have hyzv : C.vertex y ≠ C.vertex z := fun h => hyz (C.injective h)
    rcases hclaw hux huy huz hxyv hxzv hyzv with hxyAdj | hxzAdj | hyzAdj
    · exact hindep.cb hxCb hyCb hxyAdj
    · exact hindep.cb hxCb hzCb hxzAdj
    · exact hindep.cb hyCb hzCb hyzAdj
  have haColor := hcarrier ⟨a, rfl⟩
  have hbColor := hcarrier ⟨b, rfl⟩
  have hcColor := hcarrier ⟨c, rfl⟩
  have hdColor := hcarrier ⟨d, rfl⟩
  rcases haColor with haCa | haCb
  · rcases hbColor with hbCa | hbCb
    · exact ⟨C.vertex a, C.vertex b,
        fun h => hab (C.injective h), ⟨a, rfl⟩, ⟨b, rfl⟩,
        haCa, hbCa, hua, hub⟩
    · rcases hcColor with hcCa | hcCb
      · exact ⟨C.vertex a, C.vertex c,
          fun h => hac (C.injective h), ⟨a, rfl⟩, ⟨c, rfl⟩,
          haCa, hcCa, hua, huc⟩
      · rcases hdColor with hdCa | hdCb
        · exact ⟨C.vertex a, C.vertex d,
            fun h => had (C.injective h), ⟨a, rfl⟩, ⟨d, rfl⟩,
            haCa, hdCa, hua, hud⟩
        · exact (noThreeCb b c d hbc hbd hcd hub huc hud
            hbCb hcCb hdCb).elim
  · rcases hbColor with hbCa | hbCb
    · rcases hcColor with hcCa | hcCb
      · exact ⟨C.vertex b, C.vertex c,
          fun h => hbc (C.injective h), ⟨b, rfl⟩, ⟨c, rfl⟩,
          hbCa, hcCa, hub, huc⟩
      · rcases hdColor with hdCa | hdCb
        · exact ⟨C.vertex b, C.vertex d,
            fun h => hbd (C.injective h), ⟨b, rfl⟩, ⟨d, rfl⟩,
            hbCa, hdCa, hub, hud⟩
        · exact (noThreeCb a c d hac had hcd hua huc hud
            haCb hcCb hdCb).elim
    · rcases hcColor with hcCa | hcCb
      · rcases hdColor with hdCa | hdCb
        · exact ⟨C.vertex c, C.vertex d,
            fun h => hcd (C.injective h), ⟨c, rfl⟩, ⟨d, rfl⟩,
            hcCa, hdCa, huc, hud⟩
        · exact (noThreeCb a b d hab had hbd hua hub hud
            haCb hbCb hdCb).elim
      · exact (noThreeCb a b c hab hac hbc hua hub huc
          haCb hbCb hcCb).elim

/-- Concrete Corollary 11 for two distinct `(a,c)` Definition 19 path
blocks sharing the same original hole. -/
theorem noSharedDependentAnticommutingWitness_of_concreteBlocks
    (D E : ConcretePathDeformation O Cprime)
    (F : D.FullDefinition19Lemma11AData)
    (H : E.FullDefinition19Lemma11AData)
    (C : IndexedInducedHole G)
    (hclaw : G.IsClawFree)
    (hEven : Even C.card)
    (hcarrier : Set.range C.vertex ⊆ O.Ca ∪ O.Cb)
    (hpathNe : Set.range D.path.vertex ≠ Set.range E.path.vertex)
    (hcommonD : O.BaseCommonNeighborOn D C)
    (hcommonE : O.BaseCommonNeighborOn E C) :
    ¬SharedDependentAnticommutingWitness
      D.path E.path D.dependentAt E.dependentAt := by
  rintro ⟨u, s, t, huD, huE, hantiD, hantiE⟩
  let iD : Fin D.deformation.stepCount :=
    ⟨s, D.index_lt_of_mem_dependentAt huD⟩
  let iE : Fin E.deformation.stepCount :=
    ⟨t, E.index_lt_of_mem_dependentAt huE⟩
  have huiD : u ∈ (D.deformation.step iD).dependentSet :=
    D.mem_step_dependentSet_of_mem_dependentAt huD
  have huiE : u ∈ (E.deformation.step iE).dependentSet :=
    E.mem_step_dependentSet_of_mem_dependentAt huE
  have huPrime : u ∈ Cprime :=
    ((D.deformation.step iD).mem_dependentSet.mp huiD).1
  have huIntroD : G.Adj u (D.deformation.step iD).introduced :=
    ((D.deformation.step iD).mem_dependentSet.mp huiD).2.1
  have huIntroE : G.Adj u (E.deformation.step iE).introduced :=
    ((E.deformation.step iE).mem_dependentSet.mp huiE).2.1
  have hDac : Set.range D.path.vertex ∈ O.acPaths := by
    rw [← D.activePath_eq iD]
    exact (F.neighborhood.mechanical.stepGeometry iD).base.activePath_ac
  have hEac : Set.range E.path.vertex ∈ O.acPaths := by
    rw [← E.activePath_eq iE]
    exact (H.neighborhood.mechanical.stepGeometry iE).base.activePath_ac
  have hcountD := D.introducedNeighborCount_eq_one_or_two
    F hclaw huD hantiD
  have hcountE := E.introducedNeighborCount_eq_one_or_two
    H hclaw huE hantiE
  have honeD :
      D.introducedNeighborCount u D.deformation.stepCount = 1 := by
    rcases hcountD with hone | htwo
    · exact hone
    · obtain ⟨a, b, hab, hua, hub, haPrime, hbPrime,
          _haCc, _hbCc, haPath, hbPath⟩ :=
        D.exists_two_distinct_introducedNeighbors F htwo
      let x := (D.deformation.step a).introduced
      let y := (D.deformation.step b).introduced
      let z := (E.deformation.step iE).introduced
      have hxy : x ≠ y := by
        intro hxy
        apply hab
        apply Fin.ext
        have hindices := D.path.injective (show
          D.path.vertex (F.neighborhood.pathOrder.introducedPathIndex a) =
            D.path.vertex (F.neighborhood.pathOrder.introducedPathIndex b) by
          calc
            _ = (D.deformation.step a).introduced :=
              F.neighborhood.pathOrder.introduced_eq a
            _ = (D.deformation.step b).introduced := hxy
            _ = _ := (F.neighborhood.pathOrder.introduced_eq b).symm)
        have hvals := congrArg Fin.val hindices
        rw [F.neighborhood.pathOrder.introduced_index_val,
          F.neighborhood.pathOrder.introduced_index_val] at hvals
        omega
      have hzPath : z ∈ Set.range E.path.vertex := by
        refine ⟨H.neighborhood.pathOrder.introducedPathIndex iE, ?_⟩
        simpa [z] using H.neighborhood.pathOrder.introduced_eq iE
      have hxz : x ≠ z := by
        intro hxz
        apply hpathNe
        exact O.eq_of_mem_acPaths hDac hEac
          (by simpa [x] using haPath) (by simpa [x, hxz] using hzPath)
      have hyz : y ≠ z := by
        intro hyz
        apply hpathNe
        exact O.eq_of_mem_acPaths hDac hEac
          (by simpa [y] using hbPath) (by simpa [y, hyz] using hzPath)
      obtain ⟨q, huq⟩ :=
        F.neighborhood.primeHole.eq_b_of_mem_prime_and_adj_introduced
          iD huPrime huIntroD
      exact (EvenHoleLabeling.not_three_distinct_carrier_neighbors_of_b
          F.neighborhood.primeHole.labeling q
          (F.neighborhood.primeHole.mem_carrier_of_mem_prime haPrime)
          (F.neighborhood.primeHole.mem_carrier_of_mem_prime hbPrime)
          (F.neighborhood.primeHole.mem_carrier_of_mem_prime
            (H.neighborhood.primeHole.introduced_mem iE))
          (by simpa [x, huq] using hua)
          (by simpa [y, huq] using hub)
          (by simpa [z, huq] using huIntroE)
          hxy hxz hyz).elim
  have honeE :
      E.introducedNeighborCount u E.deformation.stepCount = 1 := by
    rcases hcountE with hone | htwo
    · exact hone
    · obtain ⟨a, b, hab, hua, hub, haPrime, hbPrime,
          _haCc, _hbCc, haPath, hbPath⟩ :=
        E.exists_two_distinct_introducedNeighbors H htwo
      let x := (E.deformation.step a).introduced
      let y := (E.deformation.step b).introduced
      let z := (D.deformation.step iD).introduced
      have hxy : x ≠ y := by
        intro hxy
        apply hab
        apply Fin.ext
        have hindices := E.path.injective (show
          E.path.vertex (H.neighborhood.pathOrder.introducedPathIndex a) =
            E.path.vertex (H.neighborhood.pathOrder.introducedPathIndex b) by
          calc
            _ = (E.deformation.step a).introduced :=
              H.neighborhood.pathOrder.introduced_eq a
            _ = (E.deformation.step b).introduced := hxy
            _ = _ := (H.neighborhood.pathOrder.introduced_eq b).symm)
        have hvals := congrArg Fin.val hindices
        rw [H.neighborhood.pathOrder.introduced_index_val,
          H.neighborhood.pathOrder.introduced_index_val] at hvals
        omega
      have hzPath : z ∈ Set.range D.path.vertex := by
        refine ⟨F.neighborhood.pathOrder.introducedPathIndex iD, ?_⟩
        simpa [z] using F.neighborhood.pathOrder.introduced_eq iD
      have hxz : x ≠ z := by
        intro hxz
        apply hpathNe
        exact O.eq_of_mem_acPaths hDac hEac hzPath
          (by simpa [z, ← hxz] using haPath)
      have hyz : y ≠ z := by
        intro hyz
        apply hpathNe
        exact O.eq_of_mem_acPaths hDac hEac hzPath
          (by simpa [z, ← hyz] using hbPath)
      obtain ⟨q, huq⟩ :=
        F.neighborhood.primeHole.eq_b_of_mem_prime_and_adj_introduced
          iD huPrime huIntroD
      exact (EvenHoleLabeling.not_three_distinct_carrier_neighbors_of_b
          F.neighborhood.primeHole.labeling q
          (F.neighborhood.primeHole.mem_carrier_of_mem_prime haPrime)
          (F.neighborhood.primeHole.mem_carrier_of_mem_prime hbPrime)
          (F.neighborhood.primeHole.mem_carrier_of_mem_prime
            (F.neighborhood.primeHole.introduced_mem iD))
          (by simpa [x, huq] using hua)
          (by simpa [y, huq] using hub)
          (by simpa [z, huq] using huIntroD)
          hxy hxz hyz).elim
  have hsZero :=
    D.dependentStep_eq_zero_of_introducedNeighborCount_eq_one
      F hclaw huD hantiD honeD
  have htZero :=
    E.dependentStep_eq_zero_of_introducedNeighborCount_eq_one
      H hclaw huE hantiE honeE
  subst s
  subst t
  obtain ⟨vD, hvDC, huvD, hjDvD, hkDvD, hvDCb⟩ := hcommonD huD
  obtain ⟨vE, hvEC, huvE, hjEvE, hkEvE, hvECb⟩ := hcommonE huE
  let jD : V := (D.deformation.step D.firstIndex).introduced
  let jE : V := (E.deformation.step E.firstIndex).introduced
  let kD : V := (D.deformation.step D.firstIndex).before.vertex
    (D.deformation.step D.firstIndex).removedIndex
  let kE : V := (E.deformation.step E.firstIndex).before.vertex
    (E.deformation.step E.firstIndex).removedIndex
  have hujD : G.Adj u jD := by
    simpa [jD, iD, ConcretePathDeformation.firstIndex] using huIntroD
  have hujE : G.Adj u jE := by
    simpa [jE, iE, ConcretePathDeformation.firstIndex] using huIntroE
  have hukD : ¬G.Adj u kD := by
    simpa [kD, iD, ConcretePathDeformation.firstIndex] using
      ((D.deformation.step iD).mem_dependentSet.mp huiD).2.2.2
  have hukE : ¬G.Adj u kE := by
    simpa [kE, iE, ConcretePathDeformation.firstIndex] using
      ((E.deformation.step iE).mem_dependentSet.mp huiE).2.2.2
  have hukDNe : u ≠ kD := by
    simpa [kD, iD, ConcretePathDeformation.firstIndex] using
      ((D.deformation.step iD).mem_dependentSet.mp huiD).2.2.1
  have hukENe : u ≠ kE := by
    simpa [kE, iE, ConcretePathDeformation.firstIndex] using
      ((E.deformation.step iE).mem_dependentSet.mp huiE).2.2.1
  have hjDCc : jD ∈ O.Cc := by
    simpa [jD] using
      (F.neighborhood.mechanical.stepGeometry D.firstIndex).base.introduced_cc
  have hjECc : jE ∈ O.Cc := by
    simpa [jE] using
      (H.neighborhood.mechanical.stepGeometry E.firstIndex).base.introduced_cc
  have hjDPrime : jD ∈ Cprime := by
    simpa [jD] using F.neighborhood.primeHole.introduced_mem D.firstIndex
  have hjEPrime : jE ∈ Cprime := by
    simpa [jE] using H.neighborhood.primeHole.introduced_mem E.firstIndex
  have hjDNotCa : jD ∉ O.Ca :=
    (F.neighborhood.overlapColoring.not_mem_ca_cd_of_mem_cc
      hjDPrime hjDCc).1
  have hjENotCa : jE ∉ O.Ca :=
    (H.neighborhood.overlapColoring.not_mem_ca_cd_of_mem_cc
      hjEPrime hjECc).1
  have hkDCa : kD ∈ O.Ca := by
    simpa [kD] using
      (F.neighborhood.mechanical.stepGeometry D.firstIndex).removed_ca
  have hkECa : kE ∈ O.Ca := by
    simpa [kE] using
      (H.neighborhood.mechanical.stepGeometry E.firstIndex).removed_ca
  have hindep := F.neighborhood.colorClassesIndependent
  have huOutsidePath :=
    F.anticommuting_not_mem_path huPrime
      ((D.lemma11a_membership_iff_ne_first_and_degree
        F hclaw huPrime hantiD).mp ⟨0, huD⟩).1 hantiD
  have huExact : ExactlyOneOfFour u O.Ca O.Cb O.Cc O.Cd :=
    F.neighborhood.mechanical.dependent_exactlyOne_of_outside
      F.neighborhood.overlapColoring huD huOutsidePath
  have huCd : u ∈ O.Cd :=
    F.neighborhood.mechanical.dependent_mem_cd huD
  have huNot :=
    ExactlyOneOfFour.not_mem_first_three_of_mem_fourth huExact huCd
  have huOutsideC : u ∉ Set.range C.vertex := by
    intro huC
    rcases hcarrier huC with huCa | huCb
    · exact huNot.1 huCa
    · exact huNot.2.1 huCb
  have hjDPath : jD ∈ Set.range D.path.vertex := by
    refine ⟨F.neighborhood.pathOrder.introducedPathIndex D.firstIndex, ?_⟩
    simpa [jD] using F.neighborhood.pathOrder.introduced_eq D.firstIndex
  have hjEPath : jE ∈ Set.range E.path.vertex := by
    refine ⟨H.neighborhood.pathOrder.introducedPathIndex E.firstIndex, ?_⟩
    simpa [jE] using H.neighborhood.pathOrder.introduced_eq E.firstIndex
  have hjDNejE : jD ≠ jE := by
    intro hEq
    apply hpathNe
    exact O.eq_of_mem_acPaths hDac hEac hjDPath (by simpa [hEq] using hjEPath)
  have hvDEq : vD = vE := by
    by_contra hvDNe
    rcases C.lemma7 hclaw huOutsideC with
        hzero | htwo | hthree | hfour | hfive
    · obtain ⟨p, hp⟩ := hvDC
      have hpMem : p ∈ C.neighborIndexSet u := by simpa [hp] using huvD
      exact ((Set.ncard_ne_zero_of_mem hpMem) hzero).elim
    · obtain ⟨p, hp⟩ := hvDC
      obtain ⟨q, hq⟩ := hvEC
      have hpq : p ≠ q := by
        intro hpq
        apply hvDNe
        rw [← hp, ← hq, hpq]
      have hpMem : p ∈ C.neighborIndexSet u := by simpa [hp] using huvD
      have hqMem : q ∈ C.neighborIndexSet u := by simpa [hq] using huvE
      have hpairSubset :
          ({p, q} : Set (Fin C.card)) ⊆ C.neighborIndexSet u := by
        intro a ha
        rcases Set.mem_insert_iff.mp ha with rfl | ha
        · exact hpMem
        · simpa using ha ▸ hqMem
      have hpairCard : ({p, q} : Set (Fin C.card)).ncard = 2 := by
        simp [hpq]
      have hpairEq :
          ({p, q} : Set (Fin C.card)) = C.neighborIndexSet u :=
        Set.eq_of_subset_of_ncard_le hpairSubset (by
          rw [htwo.1, hpairCard])
      have hexact : ∀ a : Fin C.card,
          G.Adj u (C.vertex a) → a = p ∨ a = q := by
        intro a hua
        have ha : a ∈ C.neighborIndexSet u := hua
        rw [← hpairEq] at ha
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ha
      have hvDvE : G.Adj vD vE := by
        simpa [hp, hq] using htwo.2 p q hpq
          (by simpa [hp] using huvD) (by simpa [hq] using huvE) hexact
      exact (hindep.cb hvDCb hvECb hvDvE).elim
    · have hdegree : C.externalDegree u = 3 := hthree.1
      obtain ⟨w, hwC, hwCa, huw, hvDw, hvEw⟩ :=
        O.degree_three_two_cb_neighbors_have_ca_center C hindep hcarrier
          hclaw huOutsideC hdegree hvDC hvEC hvDCb hvECb huvD huvE hvDNe
      have hjDw : ¬G.Adj jD w := by
        intro hjDw
        have hwEq := D.firstIntroduced_unique_ca_neighbor F hwCa
          (by simpa [jD] using hjDw)
        apply hukD
        have : G.Adj u
            ((D.deformation.step D.firstIndex).before.vertex
              (D.deformation.step D.firstIndex).removedIndex) := by
          rw [← hwEq]
          exact huw
        simpa [kD] using this
      have hjEw : ¬G.Adj jE w := by
        intro hjEw
        have hwEq := E.firstIntroduced_unique_ca_neighbor H hwCa
          (by simpa [jE] using hjEw)
        apply hukE
        have : G.Adj u
            ((E.deformation.step E.firstIndex).before.vertex
              (E.deformation.step E.firstIndex).removedIndex) := by
          rw [← hwEq]
          exact huw
        simpa [kE] using this
      have hjDNeW : jD ≠ w := by
        intro hEq
        exact hjDNotCa (hEq ▸ hwCa)
      have hjENeW : jE ≠ w := by
        intro hEq
        exact hjENotCa (hEq ▸ hwCa)
      rcases hclaw hujD hujE huw hjDNejE hjDNeW hjENeW with
          hjDjE | hjDw' | hjEw'
      · exact hindep.cc hjDCc hjECc hjDjE
      · exact hjDw hjDw'
      · exact hjEw hjEw'
    · have hdegree : C.externalDegree u = 4 := hfour.1
      obtain ⟨w, w', hww', hwC, hw'C, hwCa, hw'Ca, huw, huw'⟩ :=
        O.degree_four_has_two_ca_neighbors C hindep hcarrier hclaw hdegree
      have hjDw : ¬G.Adj jD w := by
        intro hjDw
        have hwEq := D.firstIntroduced_unique_ca_neighbor F hwCa
          (by simpa [jD] using hjDw)
        apply hukD
        have : G.Adj u
            ((D.deformation.step D.firstIndex).before.vertex
              (D.deformation.step D.firstIndex).removedIndex) := by
          rw [← hwEq]
          exact huw
        simpa [kD] using this
      have hjDw' : ¬G.Adj jD w' := by
        intro hjDw'
        have hwEq := D.firstIntroduced_unique_ca_neighbor F hw'Ca
          (by simpa [jD] using hjDw')
        apply hukD
        have : G.Adj u
            ((D.deformation.step D.firstIndex).before.vertex
              (D.deformation.step D.firstIndex).removedIndex) := by
          rw [← hwEq]
          exact huw'
        simpa [kD] using this
      have hjDNeW : jD ≠ w := by
        intro hEq
        exact hjDNotCa (hEq ▸ hwCa)
      have hjDNeW' : jD ≠ w' := by
        intro hEq
        exact hjDNotCa (hEq ▸ hw'Ca)
      rcases hclaw hujD huw huw' hjDNeW hjDNeW' hww' with
          hjDwEdge | hjDw'Edge | hww'Edge
      · exact hjDw hjDwEdge
      · exact hjDw' hjDw'Edge
      · exact hindep.ca hwCa hw'Ca hww'Edge
    · rcases hEven with ⟨m, hm⟩
      omega
  subst vE
  have hkDPath : kD ∈ Set.range D.path.vertex := by
    refine ⟨F.neighborhood.pathOrder.removedPathIndex D.firstIndex, ?_⟩
    simpa [kD] using F.neighborhood.pathOrder.removed_eq D.firstIndex
  have hkEPath : kE ∈ Set.range E.path.vertex := by
    refine ⟨H.neighborhood.pathOrder.removedPathIndex E.firstIndex, ?_⟩
    simpa [kE] using H.neighborhood.pathOrder.removed_eq E.firstIndex
  have hkDNeK : kD ≠ kE := by
    intro hEq
    apply hpathNe
    exact O.eq_of_mem_acPaths hDac hEac hkDPath (by simpa [hEq] using hkEPath)
  have hkDNeU : kD ≠ u := hukDNe.symm
  have hkENeU : kE ≠ u := hukENe.symm
  rcases hclaw (by simpa [kD] using hkDvD.symm)
      (by simpa [kE] using hkEvE.symm) huvD.symm
      hkDNeK hkDNeU hkENeU with hkDkE | hkDu | hkEu
  · exact hindep.ca hkDCa hkECa hkDkE
  · exact hukD hkDu.symm
  · exact hukE hkEu.symm

end FixedPairingPathFamily

end SimpleGraph
