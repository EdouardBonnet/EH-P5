import Lax57.GraphDefinitions
import Lax54Proofs.GraphComplements
import Lax54Proofs.KappaBlocks
import Mathlib.Tactic

namespace Lax57Proofs

open Finset
open scoped BigOperators SimpleGraph
open Lax57.GraphDefinitions

universe u

/-- A maximum independent set and its closed neighborhoods cover a finite graph. -/
theorem card_le_indepNum_mul_succ_maxDegree
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fintype.card V ≤ G.indepNum * (G.maxDegree + 1) := by
  classical
  obtain ⟨I, hI⟩ := G.maximumIndepSet_exists
  let C : V → Finset V := fun v ↦ insert v (G.neighborFinset v)
  have hcover : (Finset.univ : Finset V) ⊆ I.biUnion C := by
    intro v _hvuniv
    by_cases hv : v ∈ I
    · exact Finset.mem_biUnion.mpr ⟨v, hv, by simp [C]⟩
    · have hadj : ∃ i ∈ I, G.Adj i v := by
        by_contra hnone
        push_neg at hnone
        have hinsert : G.IsIndepSet (insert v I : Finset V) := by
          intro x hx y hy hxy hxyadj
          simp only [Finset.coe_insert, Set.mem_insert_iff] at hx hy
          rcases hx with rfl | hx <;> rcases hy with rfl | hy
          · exact hxy rfl
          · exact hnone y hy (G.adj_comm x y |>.mp hxyadj)
          · exact hnone x hx hxyadj
          · exact hI.isIndepSet hx hy hxy hxyadj
        have hcard := hI.maximum (insert v I) hinsert
        simp [Finset.card_insert_of_notMem hv] at hcard
      obtain ⟨i, hi, hiv⟩ := hadj
      exact Finset.mem_biUnion.mpr ⟨i, hi, by
        simp only [C, Finset.mem_insert, SimpleGraph.mem_neighborFinset]
        exact Or.inr hiv⟩
  have hC (i : V) : (C i).card ≤ G.maxDegree + 1 := by
    calc
      (C i).card ≤ (G.neighborFinset i).card + 1 := by
        simpa [C, Nat.add_comm] using Finset.card_insert_le i (G.neighborFinset i)
      _ = G.degree i + 1 := rfl
      _ ≤ G.maxDegree + 1 := Nat.add_le_add_right (G.degree_le_maxDegree i) 1
  calc
    Fintype.card V = (Finset.univ : Finset V).card := by simp
    _ ≤ (I.biUnion C).card := Finset.card_le_card hcover
    _ ≤ ∑ i ∈ I, (C i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ I, (G.maxDegree + 1) :=
      Finset.sum_le_sum fun i _ ↦ hC i
    _ = I.card * (G.maxDegree + 1) := by simp
    _ = G.indepNum * (G.maxDegree + 1) := by
      rw [G.maximumIndepSet_card_eq_indepNum I hI]

/-- Taking a vertex-induced subgraph cannot increase the independence number. -/
theorem indepNum_induce_finset_le
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (B : Finset V) :
    (G.induce (B : Set V)).indepNum ≤ G.indepNum := by
  have h := Lax54Proofs.cliqueNum_induce_finset_le Gᶜ B
  simpa [← Lax54Proofs.compl_induce_eq_induce_compl] using h

/-- A maximum-degree sparse graph larger than `K` has independence number above `K`
when the reciprocal sparsity parameter is larger than `2K`. -/
theorem indepNum_gt_of_ESparse
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {E K : ℕ} (hK : 0 < K) (hEK : 2 * K < E)
    (hcard : K < Fintype.card V)
    (hsparse : ∀ v : V, E * G.degree v ≤ Fintype.card V) :
    K < G.indepNum := by
  by_contra hnot
  have halpha : G.indepNum ≤ K := Nat.le_of_not_gt hnot
  letI : Nonempty V := Fintype.card_pos_iff.mp (hK.trans hcard)
  obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
  have hdegree : E * G.maxDegree ≤ Fintype.card V := by
    rw [hv]
    exact hsparse v
  have hcover : Fintype.card V ≤ K * (G.maxDegree + 1) :=
    (card_le_indepNum_mul_succ_maxDegree G).trans
      (Nat.mul_le_mul_right (G.maxDegree + 1) halpha)
  by_cases hd : G.maxDegree = 0
  · simp [hd] at hcover
    omega
  · have hdpos : 0 < G.maxDegree := Nat.pos_of_ne_zero hd
    have htwice : K * (G.maxDegree + 1) ≤ (2 * K) * G.maxDegree := by
      nlinarith
    have hmul : E * G.maxDegree ≤ (2 * K) * G.maxDegree :=
      hdegree.trans (hcover.trans htwice)
    have : E ≤ 2 * K := Nat.le_of_mul_le_mul_right hmul hdpos
    omega

/-- Induced subgraphs of house-free graphs are house-free. -/
theorem IsHouseFree.induce_finset
    {V : Type u} {G : SimpleGraph V} (hfree : IsHouseFree G) (S : Finset V) :
    IsHouseFree (G.induce (S : Set V)) := by
  intro hhouse
  apply hfree
  exact hhouse.trans ⟨SimpleGraph.Embedding.induce (G := G) (S : Set V)⟩

/-- `kappa` is no larger than the square of the homogeneous number. -/
theorem kappa_le_homogeneousNumber_sq
    {V : Type u} (G : SimpleGraph V) :
    kappa G ≤ homogeneousNumber G ^ 2 := by
  unfold kappa homogeneousNumber Lax54.GraphDefinitions.kappa
    Lax54.GraphDefinitions.homogeneousNumber
  calc
    G.cliqueNum * G.indepNum ≤
        max G.cliqueNum G.indepNum * max G.cliqueNum G.indepNum :=
      Nat.mul_le_mul (le_max_left _ _) (le_max_right _ _)
    _ = max G.cliqueNum G.indepNum ^ 2 := by simp [pow_two]

/-- A critical finite graph with positive exponent has `kappa >= 2`. -/
theorem two_le_kappa_of_critical
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {q : ℕ} (hq : 0 < q)
    (hcritical : IsQCritical q G) : 2 ≤ kappa G := by
  classical
  have hVpos : 0 < Fintype.card V := Nat.zero_lt_of_lt hcritical.1
  let v : V := Classical.choice (Fintype.card_pos_iff.mp hVpos)
  have hclique : 1 ≤ G.cliqueNum := by
    have hs : G.IsClique ({v} : Finset V) := by simp
    simpa using hs.card_le_cliqueNum
  have hindep : 1 ≤ G.indepNum := by
    have hs : G.IsIndepSet ({v} : Finset V) := by simp
    simpa using hs.card_le_indepNum
  have hkappa : 1 ≤ kappa G := by
    simpa [kappa, Lax54.GraphDefinitions.kappa] using Nat.mul_le_mul hclique hindep
  have hVtwo : 1 < Fintype.card V := by
    have hpow : 1 ≤ kappa G ^ q := Nat.one_le_pow q _ hkappa
    exact lt_of_le_of_lt hpow hcritical.1
  obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp hVtwo
  by_cases hadj : G.Adj a b
  · have hpair : G.IsClique ({a, b} : Finset V) := by
      simpa [SimpleGraph.isClique_pair, hab] using hadj
    have htwo : 2 ≤ G.cliqueNum := by
      simpa [Finset.card_pair hab] using hpair.card_le_cliqueNum
    simpa [kappa, Lax54.GraphDefinitions.kappa] using Nat.mul_le_mul htwo hindep
  · have hpair : G.IsIndepSet ({a, b} : Finset V) := by
      intro x hx y hy hxy hxyadj
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact hxy rfl
      · exact hadj hxyadj
      · exact hadj (G.adj_comm _ _ |>.mp hxyadj)
      · exact hxy rfl
    have htwo : 2 ≤ G.indepNum := by
      simpa [Finset.card_pair hab] using hpair.card_le_indepNum
    simpa [kappa, Lax54.GraphDefinitions.kappa] using Nat.mul_le_mul hclique htwo

end Lax57Proofs
