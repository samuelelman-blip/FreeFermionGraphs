import FreeFermionGraphs.Lemma16Paper

/-!
# Vacuity audit of the Lemma 12 data and of the hypotheses of `paperLemma16`

This module is an audit, not a paper theorem.  It proves, inside Lean, that the
interface `Lemma12Definition19Data` (`Lemma12ReverseClone.lean`) is
uninhabited on every claw-free graph, and that it is also incompatible with the
criterion `F.dependentUnion ⊆ C^(m)` of Lemma 12 on an arbitrary graph.
Consequently the Lean theorems

* `SimpleGraph.FixedPairingPathFamily.FullDefinition19Deformation.lemma12`
  (repo Lemma 12, v1 Lemma 7 `solutioncriterion`, L1122, appendix proof
  L1757-1799),
* `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.PaperLemma16Trace.paperLemma16`
  (repo Lemma 16, v1 Lemma 10, L1192-1200), and
* `SimpleGraph.FixedPairingPathFamily.ConcretePathDeformation.FiniteMixedSideSearchTrace.paperLemma16_of_terminalPathTransport`
  (`Lemma16Unobstructed.lean`, L167)

are vacuous as currently stated: each takes `hclaw : G.IsClawFree` together
with a `Lemma12Definition19Data` (for `paperLemma16`, a `PaperLemma16Trace`,
from which `toLemma12Definition19Data` builds one), and no such pair exists.
They therefore carry no information about the manuscript's Lemmas 7 and 10.  The
manuscript statements themselves are not shown to be false; the defect is in how
the endpoint clause of v1's palindromic path (L957-966) was transcribed.

## Main results

* `FullDefinition19Deformation.lemma12Data_false_of_clawFree`: for every
  `F : FullDefinition19Deformation O C'`, every `L : Lemma12Definition19Data F`
  on a claw-free graph gives `False`.  No criterion and no unobstructedness is
  used.
* `FiniteMixedSideSearchTrace.paperLemma16Trace_false_of_clawFree`: the same for
  `PaperLemma16Trace` of a finite mixed side search trace; the structure is
  uninhabited in the manuscript's claw-free setting.
* `FullDefinition19Deformation.lemma12_data_inconsistent`: for every
  `F : FullDefinition19Deformation O C'` on an arbitrary graph, every
  `L : Lemma12Definition19Data F` and the criterion
  `F.dependentUnion ⊆ C^(m)` give `False`.
* `FullDefinition19Deformation.not_criterion_of_lemma12Data`: the same, as the
  statement that the criterion cannot hold once Lemma 12 data exist.
* `FiniteMixedSideSearchTrace.paperLemma16_hyps_inconsistent`: for every
  `Y : X.PaperLemma16Trace` on a claw-free graph, `X.IsUnobstructed` gives
  `False`.
* `FiniteMixedSideSearchTrace.not_isUnobstructed_of_paperLemma16Trace`: the
  same, as the statement that a trace carrying `PaperLemma16Trace` data is
  never unobstructed.

For `FullDefinition19Deformation` data, `lemma12Data_false_of_clawFree` and
`lemma12_data_inconsistent` are incomparable: the former needs `G.IsClawFree`
and no criterion, the latter needs the criterion and holds for arbitrary `G`.
The trace-level theorems `paperLemma16_hyps_inconsistent` and
`not_isUnobstructed_of_paperLemma16Trace` also take `hclaw`, because they go
through `PaperLemma16Trace.paperLemma16`.  They are therefore immediate
consequences of `paperLemma16Trace_false_of_clawFree`, kept as the originally
requested targets.

## The defect

Write `k` for the removed vertex and `j` for the introduced vertex of the last
step of a complete Definition 19 deformation `F` (so `k ∈ C`, `j ∈ C'`, and
`k`, `j` are consecutive vertices of the active path `P` of that step).

The cause is the endpoint alternative of
`Lemma12Definition19Data.endpoint_or_continuation` (`Lemma12ReverseClone.lean`,
L89-95) and, for traces, the field `PaperLemma16Trace.terminalEndpointMaximal`
(`Lemma16Paper.lean`, L62-70).  They demand that *every* neighbour `v ∈ C'` of
the last removed vertex `k` lies on the active path `P`.  The continuation
alternative is impossible at the last index, so at the last step the endpoint
alternative is forced.  Two arguments then reach `False`.

1. Claw-free route (`lemma12Data_false_of_clawFree`; no criterion, no Lemma 13,
   no unobstructedness).  At the last step there is no successor step, so
   `removedPrime_hasSuccessor` gives `k ∉ C'`, while `j ∈ C'` by
   `introduced_mem_prime`.  The prime hole has carrier `C'`, so `j` has two
   non-adjacent neighbours `p`, `p'` in the cycle `C'`
   (`exists_two_nonadjacent_neighbors`), and `k ≠ p, p'` because `k ∉ C'`.
   Claw-freeness at the centre `j` with leaves `k`, `p`, `p'` forces `k` to be
   adjacent to `p` or to `p'`; call that neighbour `d`, so `d ∈ C'`, `j ~ d`,
   `k ~ d`.  The endpoint alternative puts `d` on `P`.  Also `j, k ∈ P` and
   `j ~ k`.  Three pairwise adjacent vertices on the induced path `P` would
   need three indices of `ℕ` that pairwise differ by exactly one, which is
   impossible.
2. Criterion route (`lemma12_data_inconsistent`; arbitrary graph).
   `exists_reverse_deformation_of_endpoint`, applied to the prime hole,
   shows from the criterion that `k` is a clone of `j` on the reverse hole
   (at the last step this is the prime hole with carrier `C'`): `k` is
   adjacent to `j` and to a cycle neighbour `d ∈ C'` of `j`.  The endpoint
   alternative puts `d` on `P`, and the same triangle `j, k, d` on the induced
   path `P` is impossible.

So the endpoint clause, read as "all `C'`-neighbours of `k` are on `P`", cannot
hold together with the other fields of `Lemma12Definition19Data` when `G` is
claw-free: `k` then always has a `C'`-neighbour adjacent to `j`, and such a
vertex cannot lie on the induced path `P`.  In v1 the endpoint statement is weaker, and the
palindromic example (L957-966) exhibits exactly this configuration:
`Γ_{C'}(a_{ℓ-1}) = d_{ℓ-1} ◇ c_{ℓ-1} ◇ d_ℓ`, that is, the last removed vertex
`a_{ℓ-1}` genuinely has two neighbours `d_{ℓ-1}`, `d_ℓ` in the *other* colour
class `C'_d` of `C'`, both adjacent to `j = c_{ℓ-1}` and not on the path `P` (a
component of `G[C_a ⊕ C'_c]`).  The endpoint property of the manuscript
constrains only the neighbours of `k` in `C'` that are not adjacent to `j`: the
endpoint step of the appendix proof (L1795) is applied to a neighbour `v ∈ C'`
of the last removed vertex that is *not* adjacent to `j`.  The Lean
transcription quantifies over all of `C'`, and is therefore false in every
genuine palindromic situation, not only in the abstract.

Repair (not carried out here): weaken the endpoint alternative to those
`v ∈ C'` with `v ≠ j` and `¬ G.Adj j v`.  The proof of
`exists_reverse_deformation_of_endpoint` only applies the hypothesis to such
residual vertices (`hvj`, `hjv` are in scope there), so the reverse-clone
argument is unaffected.  The weakened clause is also consistent with the
claw-free mechanism above: the claw at `j` only produces neighbours `d` of `k`
with `G.Adj j d`, which the weakened clause excludes.  What has to be
re-derived is the weaker clause for `PaperLemma16Trace.terminalEndpointMaximal`
and `Lemma12Definition19Data`.

Until that is done, the README/`PAPER_FIDELITY.md` status "exact" for Lemma 16
and the "conditional on `Lemma12Definition19Data`" status of Lemma 12 should
both be read as vacuous.  The claw-free theorems justify this for exactly the
three declarations `lemma12`, `paperLemma16` and
`paperLemma16_of_terminalPathTransport` named above, each of which takes
`hclaw`.  No claim is made here about declarations that consume
`Lemma12Definition19Data` or `PaperLemma16Trace` without `hclaw` and without the
criterion.
-/
universe u

variable {V : Type u}

namespace SimpleGraph

open scoped symmDiff

variable {G : SimpleGraph V}

namespace FixedPairingPathFamily

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

namespace FullDefinition19Deformation

/-- Audit result: the Lemma 12 data and Lemma 12's criterion are jointly
inconsistent.

The last step has no continuation, so `endpoint_or_continuation` forces the
endpoint alternative.  The reverse clone produced from the criterion makes the
last removed vertex `k` adjacent to the introduced vertex `j` and to a
`C'`-cycle neighbour `d` of `j`; the endpoint alternative puts `d` on the
active path next to `j` and `k`, giving a triangle on an induced path.  See the
module docstring for the diagnosis and the intended weaker endpoint clause. -/
theorem lemma12_data_inconsistent (F : FullDefinition19Deformation O Cprime)
    (L : Lemma12Definition19Data F)
    (hcriterion : F.dependentUnion ⊆ Set.range F.terminalHole.vertex) :
    False := by
  rcases L.endpoint_or_continuation F.lastIndex with hend | hcont
  swap
  · obtain ⟨K⟩ := hcont
    have h1 := K.consecutive
    have h2 := K.next.isLt
    have h3 := F.nonempty
    simp only [lastIndex] at h1
    omega
  have hsymm : Set.range L.primeHole.vertex ∆
      Set.range (F.deformation.step F.lastIndex).after.vertex =
      Cprime ∆ Set.range F.terminalHole.vertex := by
    rw [L.primeHole_carrier]; rfl
  obtain ⟨q, hq, hdef⟩ :=
    F.exists_reverse_deformation_of_endpoint L hcriterion F.lastIndex
      L.primeHole hsymm hend
  obtain ⟨p, _p', _hpp', hqp, _hqp', _⟩ :=
    L.primeHole.exists_two_nonadjacent_neighbors q
  set S := F.deformation.step F.lastIndex with hS
  have hkd : G.Adj (S.before.vertex S.removedIndex) (L.primeHole.vertex p) :=
    (hdef.adj_iff p).2 (Or.inr hqp)
  have hkj : G.Adj (S.before.vertex S.removedIndex) (L.primeHole.vertex q) :=
    (hdef.adj_iff q).2 (Or.inl rfl)
  have hdPrime : L.primeHole.vertex p ∈ Cprime :=
    L.primeHole_carrier.subset ⟨p, rfl⟩
  have hdPath := hend hdPrime hkd
  have hjPath := S.introduced_mem_activePath
  have hkPath := S.removed_mem_activePath
  obtain ⟨a, ha⟩ := hjPath
  obtain ⟨b, hb⟩ := hkPath
  obtain ⟨c, hc⟩ := hdPath
  rw [hq] at hkj hqp
  have hab := (S.activePath.adj_iff b a).1 (by rw [ha, hb]; exact hkj)
  have hbc := (S.activePath.adj_iff b c).1 (by rw [hc, hb]; exact hkd)
  have hac := (S.activePath.adj_iff a c).1 (by rw [hc, ha]; exact hqp)
  omega

/-- Once `Lemma12Definition19Data` exists, Lemma 12's criterion
`F.dependentUnion ⊆ C^(m)` fails.  Restatement of
`lemma12_data_inconsistent`. -/
theorem not_criterion_of_lemma12Data (F : FullDefinition19Deformation O Cprime)
    (L : Lemma12Definition19Data F) :
    ¬ F.dependentUnion ⊆ Set.range F.terminalHole.vertex :=
  fun hcriterion => lemma12_data_inconsistent F L hcriterion

/-- Audit result: the Lemma 12 data cannot exist on a claw-free graph.

No criterion and no unobstructedness is used.  The last step has no
continuation, so the endpoint alternative is forced; there is no successor step,
so the last removed vertex `k` lies outside `C'`, while the introduced vertex
`j` lies in `C'`.  Claw-freeness at `j` with leaves `k` and the two
non-adjacent `C'`-cycle neighbours of `j` gives a `C'`-neighbour `d` of `k` with
`j ~ d`; the endpoint alternative puts `d` on the active path next to `j` and
`k`, giving a triangle on an induced path.  See the module docstring. -/
theorem lemma12Data_false_of_clawFree (F : FullDefinition19Deformation O Cprime)
    (L : Lemma12Definition19Data F) (hclaw : G.IsClawFree) :
    False := by
  rcases L.endpoint_or_continuation F.lastIndex with hend | hcont
  swap
  · obtain ⟨K⟩ := hcont
    have h1 := K.consecutive
    have h2 := K.next.isLt
    have h3 := F.nonempty
    simp only [lastIndex] at h1
    omega
  set S := F.deformation.step F.lastIndex with hS
  have hkNotPrime : S.before.vertex S.removedIndex ∉ Cprime := by
    intro hk
    obtain ⟨j, hj, _⟩ := F.removedPrime_hasSuccessor F.lastIndex hk
    have := j.isLt
    simp only [lastIndex] at hj
    have h3 := F.nonempty
    omega
  have hjPrime : S.introduced ∈ Cprime := F.introduced_mem_prime F.lastIndex
  have hjPrime' : S.introduced ∈ Set.range L.primeHole.vertex := by
    rw [L.primeHole_carrier]; exact hjPrime
  obtain ⟨q, hq⟩ := hjPrime'
  obtain ⟨p, p', hpp', hqp, hqp', hnpp'⟩ :=
    L.primeHole.exists_two_nonadjacent_neighbors q
  have hkj : G.Adj S.introduced (S.before.vertex S.removedIndex) :=
    S.deformation.adj_clone
  have hpPrime : L.primeHole.vertex p ∈ Cprime :=
    L.primeHole_carrier.subset ⟨p, rfl⟩
  have hp'Prime : L.primeHole.vertex p' ∈ Cprime :=
    L.primeHole_carrier.subset ⟨p', rfl⟩
  have hkp : S.before.vertex S.removedIndex ≠ L.primeHole.vertex p :=
    fun h => hkNotPrime (h ▸ hpPrime)
  have hkp' : S.before.vertex S.removedIndex ≠ L.primeHole.vertex p' :=
    fun h => hkNotPrime (h ▸ hp'Prime)
  have hpne : L.primeHole.vertex p ≠ L.primeHole.vertex p' :=
    fun h => hpp' (L.primeHole.injective h)
  rw [hq] at hqp hqp'
  have hclawAt := hclaw hkj hqp hqp' hkp hkp' hpne
  have tri : ∀ d, G.Adj S.introduced d →
      G.Adj (S.before.vertex S.removedIndex) d → d ∈ Cprime → False := by
    intro d hjd hkd hdPrime
    have hdPath := hend hdPrime hkd
    obtain ⟨a, ha⟩ := S.introduced_mem_activePath
    obtain ⟨b, hb⟩ := S.removed_mem_activePath
    obtain ⟨c, hc⟩ := hdPath
    have hab := (S.activePath.adj_iff b a).1 (by rw [ha, hb]; exact hkj.symm)
    have hbc := (S.activePath.adj_iff b c).1 (by rw [hc, hb]; exact hkd)
    have hac := (S.activePath.adj_iff a c).1 (by rw [hc, ha]; exact hjd)
    omega
  rcases hclawAt with h | h | h
  · exact tri _ hqp h hpPrime
  · exact tri _ hqp' h hp'Prime
  · exact hnpp' h

/-- The Lemma 12 data type is empty on a claw-free graph.  Restatement of
`lemma12Data_false_of_clawFree`. -/
theorem not_nonempty_lemma12Data_of_clawFree
    (F : FullDefinition19Deformation O Cprime) (hclaw : G.IsClawFree) :
    ¬ Nonempty (Lemma12Definition19Data F) :=
  fun ⟨L⟩ => lemma12Data_false_of_clawFree F L hclaw

end FullDefinition19Deformation

namespace ConcretePathDeformation

namespace FiniteMixedSideSearchTrace

variable {S : SearchDeformation O Cprime} {originalHole : IndexedInducedHole G}
  {X : FiniteMixedSideSearchTrace S originalHole}

/-- Audit result: the hypotheses of `paperLemma16` are jointly inconsistent.

`paperLemma16` produces the criterion `dependentUnion ⊆ C^(m)` for the
flattened trace, and `toLemma12Definition19Data` produces the Lemma 12 data
from `Y`; `lemma12_data_inconsistent` then gives `False`.  Hence
`paperLemma16` is vacuous as stated. -/
theorem paperLemma16_hyps_inconsistent (Y : X.PaperLemma16Trace)
    (hclaw : G.IsClawFree) (hunobstructed : X.IsUnobstructed) : False :=
  FullDefinition19Deformation.lemma12_data_inconsistent X.flattened
    Y.toLemma12Definition19Data (Y.paperLemma16 hclaw hunobstructed).1

/-- On a claw-free graph, a trace carrying `PaperLemma16Trace` data is never
unobstructed.  Restatement of `paperLemma16_hyps_inconsistent`. -/
theorem not_isUnobstructed_of_paperLemma16Trace (Y : X.PaperLemma16Trace)
    (hclaw : G.IsClawFree) : ¬ X.IsUnobstructed :=
  fun hunobstructed => paperLemma16_hyps_inconsistent Y hclaw hunobstructed

/-- Audit result: on a claw-free graph the `PaperLemma16Trace` structure is
uninhabited, independently of unobstructedness, of the criterion and of
Lemma 13.  It follows from `lemma12Data_false_of_clawFree` via
`toLemma12Definition19Data`.  Hence `paperLemma16` and
`paperLemma16_of_terminalPathTransport` (which both take `hclaw`) are vacuous
as stated. -/
theorem paperLemma16Trace_false_of_clawFree (Y : X.PaperLemma16Trace)
    (hclaw : G.IsClawFree) : False :=
  FullDefinition19Deformation.lemma12Data_false_of_clawFree X.flattened
    Y.toLemma12Definition19Data hclaw

/-- `PaperLemma16Trace` is empty on a claw-free graph.  Restatement of
`paperLemma16Trace_false_of_clawFree`. -/
theorem not_nonempty_paperLemma16Trace_of_clawFree (hclaw : G.IsClawFree) :
    ¬ Nonempty X.PaperLemma16Trace :=
  fun ⟨Y⟩ => paperLemma16Trace_false_of_clawFree Y hclaw

end FiniteMixedSideSearchTrace

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
