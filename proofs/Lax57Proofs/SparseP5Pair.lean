import Lax57.SparseHouseTools
import Lax57Proofs.ComponentTools
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Tactic

namespace Lax57Proofs

open Finset
open scoped SimpleGraph
open Lax57.GraphDefinitions

universe u

/-- Five vertices with precisely the consecutive path edges induce a `P5`. -/
theorem p5_isIndContained_of_vertices
    {V : Type u} {G : SimpleGraph V} {a b c d e : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hde : G.Adj d e)
    (hac : ¬ G.Adj a c) (had : ¬ G.Adj a d) (hae : ¬ G.Adj a e)
    (hbd : ¬ G.Adj b d) (hbe : ¬ G.Adj b e) (hce : ¬ G.Adj c e) :
    P5 ⊴ G := by
  let f : Fin 5 → V := ![a, b, c, d, e]
  have hinj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [f, G.adj_comm]
  refine ⟨{
    toFun := f
    inj' := hinj
    map_rel_iff' := ?_
  }⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp_all [f, P5, SimpleGraph.pathGraph_adj, SimpleGraph.Adj.ne,
      G.adj_comm]

/-- The all-vertices form of the sparse `P5` anticomplete-pair lemma. -/
theorem sparse_P5_anticomplete_pair_univ
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : IsP5Free G) (hcard : 2 ≤ Fintype.card V)
    (hdegree : ∀ v : V, 32 * G.degree v ≤ Fintype.card V) :
    ∃ B : Blockade (V := V) 2,
      B.IsAnticomplete G ∧
        ∀ i : Fin 2, Fintype.card V ≤ 32 * (B.block i).card := by
  classical
  let n := Fintype.card V
  by_cases hn32 : n < 32
  · obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp (by simpa [n] using hcard)
    have hdegzero (v : V) : G.degree v = 0 := by
      have := hdegree v
      omega
    have hantiAB : ∀ x ∈ ({a} : Finset V), ∀ y ∈ ({b} : Finset V),
        ¬ G.Adj x y := by
      intro x hx y hy
      simp only [Finset.mem_singleton] at hx hy
      subst x
      subst y
      exact (G.degree_eq_zero a |>.mp (hdegzero a)) b
    have hdisj : Disjoint ({a} : Finset V) {b} := by simp [hab]
    let B := pairBlockade ({a} : Finset V) {b} hdisj
    refine ⟨B, ?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [B, pairBlockade, G.adj_comm]
    · intro i
      fin_cases i <;> simp [B, n]
      all_goals omega
  · have hn : 32 ≤ n := Nat.le_of_not_gt hn32
    by_contra hresult
    push Not at hresult
    have hno (B : Blockade (V := V) 2) (hanti : B.IsAnticomplete G)
        (hwidth : ∀ i : Fin 2, n ≤ 32 * (B.block i).card) : False := by
      obtain ⟨i, hi⟩ := hresult B hanti
      exact (Nat.not_lt_of_ge (hwidth i)) hi
    have getComponent (T : Finset V) (hTlarge : n ≤ 8 * T.card) :
        ∃ J : Finset V, IsComponentIn G T J ∧ T.card ≤ 2 * J.card := by
      rcases component_in_or_anticomplete_pair G T with hcomp | hpair
      · exact hcomp
      · obtain ⟨B, _hinside, hanti, hwidth⟩ := hpair
        exfalso
        apply hno B hanti
        intro i
        calc
          n ≤ 8 * T.card := hTlarge
          _ ≤ 8 * (4 * (B.block i).card) :=
            Nat.mul_le_mul_left 8 (hwidth i)
          _ = 32 * (B.block i).card := by ring
    obtain ⟨F, hFcomp, hFsize⟩ := getComponent Finset.univ (by
      simp only [Finset.card_univ, n]
      nlinarith)
    have hnF : n ≤ 2 * F.card := by simpa [n] using hFsize
    obtain ⟨v, hvF⟩ := hFcomp.nonempty
    let A : Finset V := F.filter fun x ↦ G.Adj v x
    have hvnotA : v ∉ A := by simp [A]
    have hAsubF : A ⊆ F := Finset.filter_subset _ _
    have hAdegree : A.card ≤ G.degree v := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      apply Finset.card_le_card
      intro x hx
      exact (G.mem_neighborFinset v x).mpr (Finset.mem_filter.mp hx).2
    have hnA : 32 * A.card ≤ n :=
      (Nat.mul_le_mul_left 32 hAdegree).trans (by simpa [n] using hdegree v)
    let F' : Finset V := F \ insert v A
    have hFcover : F.card ≤ F'.card + A.card + 1 := by
      have hsubset : F ⊆ F' ∪ insert v A := by
        intro x hx
        by_cases hxVA : x ∈ insert v A
        · exact Finset.mem_union_right _ hxVA
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hxVA⟩)
      calc
        F.card ≤ (F' ∪ insert v A).card := Finset.card_le_card hsubset
        _ ≤ F'.card + (insert v A).card := Finset.card_union_le _ _
        _ = F'.card + A.card + 1 := by
          rw [Finset.card_insert_of_notMem hvnotA]
          omega
    have hnF' : n ≤ 3 * F'.card := by omega
    obtain ⟨J, hJcomp, hJsize⟩ := getComponent F' (hnF'.trans (by omega))
    have hnJ : n ≤ 6 * J.card := by omega
    have hJsubF : J ⊆ F := hJcomp.subset.trans (Finset.sdiff_subset.trans (by rfl))
    have hvnotJ : v ∉ J := by
      intro hvJ
      have hvF' := hJcomp.subset hvJ
      exact (Finset.mem_sdiff.mp hvF').2 (by simp)
    have hvOutside : v ∈ F \ J := Finset.mem_sdiff.mpr ⟨hvF, hvnotJ⟩
    obtain ⟨w₀, hw₀J, u, huFJ, hw₀u⟩ :=
      exists_adj_across G hFcomp.connected hJsubF hJcomp.nonempty ⟨v, hvOutside⟩
    have huA : u ∈ A := by
      have huF : u ∈ F := (Finset.mem_sdiff.mp huFJ).1
      have huNotJ : u ∉ J := (Finset.mem_sdiff.mp huFJ).2
      have huNotF' : u ∉ F' := by
        intro huF'
        exact hJcomp.closed w₀ hw₀J u
          (Finset.mem_sdiff.mpr ⟨huF', huNotJ⟩) hw₀u
      have huInsert : u ∈ insert v A := by
        by_contra huNotInsert
        exact huNotF' (Finset.mem_sdiff.mpr ⟨huF, huNotInsert⟩)
      rcases Finset.mem_insert.mp huInsert with rfl | huA
      · have hw₀F' := hJcomp.subset hw₀J
        have hw₀NotA : w₀ ∉ A := by
          exact fun h ↦ (Finset.mem_sdiff.mp hw₀F').2 (by simp [h])
        exact False.elim (hw₀NotA (Finset.mem_filter.mpr
          ⟨hJsubF hw₀J, G.adj_comm _ _ |>.mp hw₀u⟩))
      · exact huA
    have hvu : G.Adj v u := (Finset.mem_filter.mp huA).2
    let B : Finset V := J.filter fun x ↦ G.Adj u x
    have hw₀B : w₀ ∈ B := Finset.mem_filter.mpr
      ⟨hw₀J, G.adj_comm _ _ |>.mp hw₀u⟩
    have hBsubJ : B ⊆ J := Finset.filter_subset _ _
    have hBdegree : B.card ≤ G.degree u := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      apply Finset.card_le_card
      intro x hx
      exact (G.mem_neighborFinset u x).mpr (Finset.mem_filter.mp hx).2
    have hnB : 32 * B.card ≤ n :=
      (Nat.mul_le_mul_left 32 hBdegree).trans (by simpa [n] using hdegree u)
    let K : Finset V := J \ B
    have hJK : J.card = K.card + B.card := by
      have := Finset.card_sdiff_add_card J B
      rw [Finset.union_eq_left.mpr hBsubJ] at this
      simpa [K] using this.symm
    have hnK : n ≤ 8 * K.card := by omega
    obtain ⟨J', hJ'comp, hJ'size⟩ := getComponent K hnK
    have hnJ' : n ≤ 16 * J'.card := by omega
    have hJ'subJ : J' ⊆ J := hJ'comp.subset.trans (Finset.sdiff_subset.trans (by rfl))
    have hw₀notJ' : w₀ ∉ J' := by
      intro hw
      have hwK := hJ'comp.subset hw
      exact (Finset.mem_sdiff.mp hwK).2 hw₀B
    have hw₀Outside : w₀ ∈ J \ J' :=
      Finset.mem_sdiff.mpr ⟨hw₀J, hw₀notJ'⟩
    obtain ⟨z₀, hz₀J', w, hwJJ', hz₀w⟩ :=
      exists_adj_across G hJcomp.connected hJ'subJ hJ'comp.nonempty
        ⟨w₀, hw₀Outside⟩
    have hwB : w ∈ B := by
      have hwJ : w ∈ J := (Finset.mem_sdiff.mp hwJJ').1
      have hwNotJ' : w ∉ J' := (Finset.mem_sdiff.mp hwJJ').2
      by_contra hwNotB
      have hwK : w ∈ K := Finset.mem_sdiff.mpr ⟨hwJ, hwNotB⟩
      exact hJ'comp.closed z₀ hz₀J' w
        (Finset.mem_sdiff.mpr ⟨hwK, hwNotJ'⟩) hz₀w
    have huw : G.Adj u w := (Finset.mem_filter.mp hwB).2
    have hwdegree : 32 * G.degree w ≤ n := by simpa [n] using hdegree w
    have hdeglt : G.degree w < J'.card := by omega
    have hnsubset : ¬ J' ⊆ G.neighborFinset w := by
      intro hsub
      have := Finset.card_le_card hsub
      simpa [SimpleGraph.card_neighborFinset_eq_degree] using (not_le_of_gt hdeglt this)
    obtain ⟨t, htJ', htNonadj⟩ := Finset.not_subset.mp hnsubset
    let C : Finset V := J'.filter fun x ↦ G.Adj w x
    have hz₀C : z₀ ∈ C := Finset.mem_filter.mpr
      ⟨hz₀J', G.adj_comm _ _ |>.mp hz₀w⟩
    have htOutside : t ∈ J' \ C := by
      refine Finset.mem_sdiff.mpr ⟨htJ', ?_⟩
      intro htC
      exact htNonadj ((G.mem_neighborFinset w t).mpr (Finset.mem_filter.mp htC).2)
    obtain ⟨z, hzC, z', hz'Outside, hzz'⟩ :=
      exists_adj_across G hJ'comp.connected (Finset.filter_subset _ _)
        ⟨z₀, hz₀C⟩ ⟨t, htOutside⟩
    have hzJ' : z ∈ J' := (Finset.mem_filter.mp hzC).1
    have hz'J' : z' ∈ J' := (Finset.mem_sdiff.mp hz'Outside).1
    have hwz : G.Adj w z := (Finset.mem_filter.mp hzC).2
    have hwz' : ¬ G.Adj w z' := by
      intro hwz'
      exact (Finset.mem_sdiff.mp hz'Outside).2
        (Finset.mem_filter.mpr ⟨hz'J', hwz'⟩)
    have hzK : z ∈ K := hJ'comp.subset hzJ'
    have hz'K : z' ∈ K := hJ'comp.subset hz'J'
    have hzJ : z ∈ J := (Finset.mem_sdiff.mp hzK).1
    have hz'J : z' ∈ J := (Finset.mem_sdiff.mp hz'K).1
    have hzNotB : z ∉ B := (Finset.mem_sdiff.mp hzK).2
    have hz'NotB : z' ∉ B := (Finset.mem_sdiff.mp hz'K).2
    have hJtoF' (x : V) (hx : x ∈ J) : x ∈ F' := hJcomp.subset hx
    have hv_nonadj (x : V) (hx : x ∈ J) : ¬ G.Adj v x := by
      intro hvx
      have hxA : x ∈ A := Finset.mem_filter.mpr ⟨hJsubF hx, hvx⟩
      exact (Finset.mem_sdiff.mp (hJtoF' x hx)).2 (by simp [hxA])
    have hu_nonadj (x : V) (hxJ : x ∈ J) (hxB : x ∉ B) : ¬ G.Adj u x := by
      intro hux
      exact hxB (Finset.mem_filter.mpr ⟨hxJ, hux⟩)
    apply hfree
    exact p5_isIndContained_of_vertices hvu huw hwz hzz'
      (hv_nonadj w (Finset.mem_filter.mp hwB).1)
      (hv_nonadj z hzJ) (hv_nonadj z' hz'J)
      (hu_nonadj z hzJ hzNotB) (hu_nonadj z' hz'J hz'NotB) hwz'

/--
---
conclusion: Lax57.SparseHouseTools.sparse_P5_anticomplete_pair
---
Repeatedly choose a large connected component, producing nested connected
sets. Sparsity keeps the successive neighborhoods small. If no large
anticomplete pair exists, two applications of connectivity across a cut
produce five vertices that induce $P_5$.

# Attribution

Lemma 4.4 of Nguyen, Scott, and Seymour, with cleared denominators.
-/
theorem sparse_P5_anticomplete_pair :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V),
      IsP5Free G → 2 ≤ S.card → ESparse G 32 S →
        ∃ B : Blockade (V := V) 2,
          B.IsInside S ∧ B.IsAnticomplete G ∧
            ∀ i : Fin 2, S.card ≤ 32 * (B.block i).card := by
  classical
  intro V _ _ G _ S hfree hcard hsparse
  let H := G.induce (S : Set V)
  have hfreeH : IsP5Free H := by
    intro hp5
    apply hfree
    exact hp5.trans ⟨SimpleGraph.Embedding.induce (G := G) (S : Set V)⟩
  have hdegree : ∀ v : {x : V // x ∈ S},
      32 * H.degree v ≤ Fintype.card {x : V // x ∈ S} := by
    intro v
    simpa [H] using hsparse v
  obtain ⟨Bsub, hanti, hwidth⟩ := sparse_P5_anticomplete_pair_univ H hfreeH
    (by simpa using hcard) hdegree
  let e : {x : V // x ∈ S} ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  let B := mapBlockade e Bsub
  refine ⟨B, ?_, ?_, ?_⟩
  · intro i x hx
    change x ∈ (Bsub.block i).map e at hx
    obtain ⟨xS, _hx, rfl⟩ := Finset.mem_map.mp hx
    exact xS.property
  · intro i j hij x hxi y hyj hxy
    change x ∈ (Bsub.block i).map e at hxi
    change y ∈ (Bsub.block j).map e at hyj
    obtain ⟨xS, hxiS, rfl⟩ := Finset.mem_map.mp hxi
    obtain ⟨yS, hyjS, rfl⟩ := Finset.mem_map.mp hyj
    exact hanti hij xS hxiS yS hyjS hxy
  · intro i
    simpa [B, H] using hwidth i

end Lax57Proofs
