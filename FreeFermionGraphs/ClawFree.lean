import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Set.SymmDiff

/-!
# Claw-free graphs

Foundational graph-theoretic definitions for the formalisation of the paper.
-/

open Set
open scoped symmDiff

universe u

variable {V : Type u}

namespace SimpleGraph

/-- A graph is claw-free when no vertex has three pairwise nonadjacent neighbours. -/
def IsClawFree (G : SimpleGraph V) : Prop :=
  ∀ ⦃center a b c : V⦄,
    G.Adj center a → G.Adj center b → G.Adj center c →
    a ≠ b → a ≠ c → b ≠ c →
    G.Adj a b ∨ G.Adj a c ∨ G.Adj b c

variable {G : SimpleGraph V} {S T : Set V}

/-- The explicit bipartition of the subgraph induced by the symmetric difference of two
independent sets. This is the bipartite part of Lemma 6 in the paper. -/
theorem lemma6_isBipartiteWith (hS : G.IsIndepSet S) (hT : G.IsIndepSet T) :
    (G.induce (S ∆ T)).IsBipartiteWith
      {v | (v : V) ∈ S \ T} {v | (v : V) ∈ T \ S} := by
  constructor
  · rw [Set.disjoint_left]
    intro v hvS hvT
    exact hvT.2 hvS.1
  · intro v w hvw
    rcases Set.mem_symmDiff.mp v.property with hv | hv
    · left
      refine ⟨hv, ?_⟩
      rcases Set.mem_symmDiff.mp w.property with hw | hw
      · have hvw_ne : (v : V) ≠ (w : V) := by
          intro h
          exact hvw.ne (Subtype.ext h)
        exact (hS hv.1 hw.1 hvw_ne hvw).elim
      · exact hw
    · right
      refine ⟨hv, ?_⟩
      rcases Set.mem_symmDiff.mp w.property with hw | hw
      · exact hw
      · have hvw_ne : (v : V) ≠ (w : V) := by
          intro h
          exact hvw.ne (Subtype.ext h)
        exact (hT hv.1 hw.1 hvw_ne hvw).elim

/-- The graph induced by the symmetric difference of two independent sets is bipartite. -/
theorem lemma6_isBipartite (hS : G.IsIndepSet S) (hT : G.IsIndepSet T) :
    (G.induce (S ∆ T)).IsBipartite :=
  (lemma6_isBipartiteWith hS hT).isBipartite

/-- In a claw-free graph, the subgraph induced by the symmetric difference of two independent
sets has maximum degree at most two. This is the degree part of Lemma 6 in the paper. -/
theorem lemma6_degree_le_two [Finite V]
    (hclaw : G.IsClawFree) (hS : G.IsIndepSet S) (hT : G.IsIndepSet T)
    (v : ↥(S ∆ T)) : ((G.induce (S ∆ T)).neighborSet v).ncard ≤ 2 := by
  by_contra hdegree
  have hthree : 2 < ((G.induce (S ∆ T)).neighborSet v).ncard := Nat.lt_of_not_ge hdegree
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := (Set.two_lt_ncard_iff).mp hthree
  have hva : (G.induce (S ∆ T)).Adj v a := by simpa using ha
  have hvb : (G.induce (S ∆ T)).Adj v b := by simpa using hb
  have hvc : (G.induce (S ∆ T)).Adj v c := by simpa using hc
  have hab' : (a : V) ≠ (b : V) := by
    intro h
    exact hab (Subtype.ext h)
  have hac' : (a : V) ≠ (c : V) := by
    intro h
    exact hac (Subtype.ext h)
  have hbc' : (b : V) ≠ (c : V) := by
    intro h
    exact hbc (Subtype.ext h)
  rcases Set.mem_symmDiff.mp v.property with hvS | hvT
  · have neighbor_mem_T : ∀ {w : ↥(S ∆ T)}, (G.induce (S ∆ T)).Adj v w → (w : V) ∈ T := by
      intro w hvw
      rcases Set.mem_symmDiff.mp w.property with hwS | hwT
      · have hvw_ne : (v : V) ≠ (w : V) := by
          intro h
          exact hvw.ne (Subtype.ext h)
        exact (hS hvS.1 hwS.1 hvw_ne hvw).elim
      · exact hwT.1
    have haT := neighbor_mem_T hva
    have hbT := neighbor_mem_T hvb
    have hcT := neighbor_mem_T hvc
    rcases hclaw hva hvb hvc hab' hac' hbc' with hab_adj | hac_adj | hbc_adj
    · exact (hT haT hbT hab') hab_adj
    · exact (hT haT hcT hac') hac_adj
    · exact (hT hbT hcT hbc') hbc_adj
  · have neighbor_mem_S : ∀ {w : ↥(S ∆ T)}, (G.induce (S ∆ T)).Adj v w → (w : V) ∈ S := by
      intro w hvw
      rcases Set.mem_symmDiff.mp w.property with hwS | hwT
      · exact hwS.1
      · have hvw_ne : (v : V) ≠ (w : V) := by
          intro h
          exact hvw.ne (Subtype.ext h)
        exact (hT hvT.1 hwT.1 hvw_ne hvw).elim
    have haS := neighbor_mem_S hva
    have hbS := neighbor_mem_S hvb
    have hcS := neighbor_mem_S hvc
    rcases hclaw hva hvb hvc hab' hac' hbc' with hab_adj | hac_adj | hbc_adj
    · exact (hS haS hbS hab') hab_adj
    · exact (hS haS hcS hac') hac_adj
    · exact (hS hbS hcS hbc') hbc_adj

/-- Lemma 6 from the paper: the symmetric-difference subgraph of two independent sets in a
finite claw-free graph is bipartite and has maximum degree at most two. -/
theorem lemma6 [Finite V]
    (hclaw : G.IsClawFree) (hS : G.IsIndepSet S) (hT : G.IsIndepSet T) :
    (G.induce (S ∆ T)).IsBipartite ∧
      ∀ v : ↥(S ∆ T), ((G.induce (S ∆ T)).neighborSet v).ncard ≤ 2 :=
  ⟨lemma6_isBipartite hS hT, lemma6_degree_le_two hclaw hS hT⟩

end SimpleGraph
