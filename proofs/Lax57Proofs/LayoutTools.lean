import Lax57Proofs.LocalBlockade
import Lax57Proofs.ThinningTools
import Mathlib.Tactic

set_option maxHeartbeats 1200000
set_option maxRecDepth 3000

namespace Lax57Proofs

open Finset
open scoped BigOperators SimpleGraph
open Lax57.GraphDefinitions

universe u

/-- A pair of blocks is complete. -/
def CompletePair {V : Type u} [DecidableEq V] (G : SimpleGraph V)
    {k : ℕ} (B : Blockade (V := V) k) (i j : Fin k) : Prop :=
  ∀ x ∈ B.block i, ∀ y ∈ B.block j, G.Adj x y

/-- The graph recording exactly the complete pairs of a blockade. -/
noncomputable def completePattern {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) {k : ℕ} (B : Blockade (V := V) k) :
    SimpleGraph (Fin k) where
  Adj i j := i ≠ j ∧ CompletePair G B i j
  symm := by
    intro i j h
    refine ⟨h.1.symm, ?_⟩
    intro x hx y hy
    exact G.adj_comm _ _ |>.mpr (h.2 y hy x hx)
  loopless := ⟨by
    intro i h
    exact h.1 rfl⟩

/-- Ordered edges between distinct blocks whose pair is not complete. These
are the exceptional pairs introduced when a layout block is refined. -/
noncomputable def internalWrongPairs
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (B : Blockade (V := V) k) : Finset (V × V) := by
  classical
  exact (Finset.univ : Finset (Fin k)).biUnion fun i ↦
    ((Finset.univ : Finset (Fin k)).erase i).biUnion fun j ↦
      if CompletePair G B i j then ∅ else G.interedges (B.block i) (B.block j)

/-- Directed sparsity implies weak sparsity. -/
theorem WeaklyESparse.of_ESparseTo
    {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {P : ℕ} {A B : Finset V} (h : ESparseTo G P B A) :
    WeaklyESparse G P B A := by
  calc
    P * (G.interedges B A).card =
        ∑ b ∈ B, P * (neighborsIn G A b).card := by
      rw [← sum_card_neighborsIn_eq_card_interedges, Finset.mul_sum]
    _ ≤ ∑ _b ∈ B, A.card := by
      exact Finset.sum_le_sum fun b hb ↦ h b hb
    _ = B.card * A.card := by simp

private theorem internalWrongPairs_eq_empty_of_pure
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} {B : Blockade (V := V) k} (h : B.IsPure G) :
    internalWrongPairs G B = ∅ := by
  classical
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨p, hp⟩
  obtain ⟨i, _hi, hp⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨j, hj, hp⟩ := Finset.mem_biUnion.mp hp
  have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
  split at hp <;> rename_i hcomplete
  · simp at hp
  · rcases h hij with hc | ha
    · exact hcomplete hc
    · rw [SimpleGraph.mem_interedges_iff] at hp
      exact ha p.1 hp.1 p.2 hp.2.1 hp.2.2

private theorem sum_block_cards_le_ambient
    {V : Type u} [Fintype V] [DecidableEq V]
    {k : ℕ} (B : Blockade (V := V) k) {S : Finset V}
    (hinside : B.IsInside S) :
    (∑ i, (B.block i).card) ≤ S.card := by
  classical
  let U := (Finset.univ : Finset (Fin k)).biUnion B.block
  have hU : U ⊆ S := by
    intro x hx
    obtain ⟨i, _hi, hxi⟩ := Finset.mem_biUnion.mp hx
    exact hinside i hxi
  have hcard : U.card = ∑ i, (B.block i).card := by
    change ((Finset.univ : Finset (Fin k)).biUnion B.block).card = _
    rw [Finset.card_biUnion]
    intro i _hi j _hj hij
    exact B.disjoint hij
  rw [← hcard]
  exact Finset.card_le_card hU

/-- A pure or directed `P`-sparse blockade introduces at most a `1/P`
fraction of all ordered ambient pairs as exceptional pairs. -/
theorem internalWrongPairs_bound
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k P : ℕ} (B : Blockade (V := V) k) (S : Finset V)
    (hinside : B.IsInside S) (hkind : B.IsPure G ∨ B.IsESparse G P) :
    P * (internalWrongPairs G B).card ≤ S.card ^ 2 := by
  classical
  rcases hkind with hpure | hsparse
  · rw [internalWrongPairs_eq_empty_of_pure G hpure]
    simp
  · have hcardUnion : (internalWrongPairs G B).card ≤
        ∑ i : Fin k, ∑ j ∈ (Finset.univ : Finset (Fin k)).erase i,
          (G.interedges (B.block i) (B.block j)).card := by
      calc
        (internalWrongPairs G B).card ≤
            ∑ i ∈ (Finset.univ : Finset (Fin k)),
              (((Finset.univ : Finset (Fin k)).erase i).biUnion fun j ↦
                if CompletePair G B i j then ∅
                else G.interedges (B.block i) (B.block j)).card := by
          change ((Finset.univ : Finset (Fin k)).biUnion fun i ↦
              (((Finset.univ : Finset (Fin k)).erase i).biUnion fun j ↦
                if CompletePair G B i j then ∅
                else G.interedges (B.block i) (B.block j))).card ≤ _
          exact Finset.card_biUnion_le
        _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin k)),
              ∑ j ∈ (Finset.univ : Finset (Fin k)).erase i,
                (G.interedges (B.block i) (B.block j)).card := by
          apply Finset.sum_le_sum
          intro i _hi
          calc
            (((Finset.univ : Finset (Fin k)).erase i).biUnion fun j ↦
                if CompletePair G B i j then ∅
                else G.interedges (B.block i) (B.block j)).card ≤
              ∑ j ∈ (Finset.univ : Finset (Fin k)).erase i,
                (if CompletePair G B i j then ∅
                 else G.interedges (B.block i) (B.block j)).card :=
              Finset.card_biUnion_le
            _ ≤ ∑ j ∈ (Finset.univ : Finset (Fin k)).erase i,
                (G.interedges (B.block i) (B.block j)).card := by
              apply Finset.sum_le_sum
              intro j _hj
              split <;> simp
        _ = ∑ i : Fin k, ∑ j ∈ (Finset.univ : Finset (Fin k)).erase i,
              (G.interedges (B.block i) (B.block j)).card := by simp
    have hpairs : ∀ (i j : Fin k), i ≠ j →
        P * (G.interedges (B.block i) (B.block j)).card ≤
          (B.block i).card * (B.block j).card := by
      intro i j hij
      rcases lt_or_gt_of_ne hij with hijlt | hjilt
      · have hweak := WeaklyESparse.of_ESparseTo G (hsparse hijlt)
        exact WeaklyESparse.symm G hweak
      · have hweak := WeaklyESparse.of_ESparseTo G (hsparse hjilt)
        exact hweak
    have hsum : P * (internalWrongPairs G B).card ≤
        (∑ i, (B.block i).card) ^ 2 := by
      calc
        P * (internalWrongPairs G B).card ≤
            P * (∑ i : Fin k, ∑ j ∈ (Finset.univ : Finset (Fin k)).erase i,
              (G.interedges (B.block i) (B.block j)).card) :=
          Nat.mul_le_mul_left P hcardUnion
        _ = ∑ i : Fin k, ∑ j ∈ (Finset.univ : Finset (Fin k)).erase i,
              P * (G.interedges (B.block i) (B.block j)).card := by
          simp_rw [Finset.mul_sum]
        _ ≤ ∑ i : Fin k, ∑ j ∈ (Finset.univ : Finset (Fin k)).erase i,
              (B.block i).card * (B.block j).card := by
          apply Finset.sum_le_sum
          intro i _hi
          apply Finset.sum_le_sum
          intro j hj
          exact hpairs i j (Finset.ne_of_mem_erase hj).symm
        _ ≤ ∑ i : Fin k, ∑ j : Fin k,
              (B.block i).card * (B.block j).card := by
          apply Finset.sum_le_sum
          intro i _hi
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            fun _ _ _ ↦ Nat.zero_le _
        _ = (∑ i, (B.block i).card) ^ 2 := by
          simp_rw [← Finset.mul_sum]
          rw [← Finset.sum_mul, pow_two]
    exact hsum.trans (Nat.pow_le_pow_left
      (sum_block_cards_le_ambient B hinside) 2)

/-- Ordered edges between blocks not declared complete by the layout. -/
noncomputable def wrongPairs
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {I : Type u} [Fintype I] [DecidableEq I]
    (A : I → Finset V) (J : SimpleGraph I) : Finset (V × V) := by
  classical
  exact ((Finset.univ : Finset V).product Finset.univ).filter fun p ↦
    ∃ i j : I, i ≠ j ∧ p.1 ∈ A i ∧ p.2 ∈ A j ∧
      G.Adj p.1 p.2 ∧ ¬ J.Adj i j

/-- A layout records complete pairs, a conserved rational weight, uniform
polynomial width, and a bound on exceptional ordered edges. -/
structure PolynomialLayout
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (E P d : ℕ) where
  Index : Type u
  [fintypeIndex : Fintype Index]
  [decidableEqIndex : DecidableEq Index]
  block : Index → Finset V
  disjoint : ∀ {i j}, i ≠ j → Disjoint (block i) (block j)
  pattern : SimpleGraph Index
  pattern_complete : ∀ {i j}, pattern.Adj i j →
    ∀ x ∈ block i, ∀ y ∈ block j, G.Adj x y
  weight : Index → ℚ
  weight_nonneg : ∀ i, 0 ≤ weight i
  weight_capacity : ∀ i,
    weight i ^ d * (Fintype.card V : ℚ) ≤ ((block i).card : ℚ)
  weight_total : 1 ≤ ∑ i, weight i
  wide : ∀ i, Fintype.card V ≤ E ^ (2 * d) * (block i).card
  wrong_budget : P * (wrongPairs G block pattern).card ≤
    (Fintype.card Index - 1) * Fintype.card V ^ 2

/-- Number of blocks in a layout. -/
def PolynomialLayout.card
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {E P d : ℕ}
    (L : PolynomialLayout G E P d) : ℕ :=
  @Fintype.card L.Index L.fintypeIndex

end Lax57Proofs
