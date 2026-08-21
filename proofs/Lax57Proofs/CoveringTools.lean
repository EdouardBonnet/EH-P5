import Lax57Proofs.ThinningTools
import Mathlib.Tactic

namespace Lax57Proofs

open Finset
open scoped BigOperators SimpleGraph
open Lax57.GraphDefinitions

universe u

/-- The vertices of `B` which have a neighbor in `S`. -/
def coveredBy {V : Type u} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S B : Finset V) : Finset V :=
  B.filter fun b ↦ ∃ a ∈ S, G.Adj a b

theorem coveredBy_subset {V : Type u} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S B : Finset V) : coveredBy G S B ⊆ B :=
  Finset.filter_subset _ _

theorem coveredBy_empty {V : Type u} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (B : Finset V) : coveredBy G ∅ B = ∅ := by
  ext b
  simp [coveredBy]

/-- Double counting finds one vertex which covers at least a reciprocal
`R`-fraction of a prescribed set. -/
theorem exists_vertex_covering_fraction
    {V : Type u} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (A B : Finset V) (R : ℕ)
    (hA : A.Nonempty)
    (hrich : ∀ b ∈ B, A.card ≤ R * (neighborsIn G A b).card) :
    ∃ a ∈ A, B.card ≤ R * (neighborsIn G B a).card := by
  classical
  by_contra hnone
  push_neg at hnone
  have hlower : A.card * B.card ≤
      R * (G.interedges B A).card := by
    calc
      A.card * B.card = ∑ b ∈ B, A.card := by simp [Nat.mul_comm]
      _ ≤ ∑ b ∈ B, R * (neighborsIn G A b).card := by
        exact Finset.sum_le_sum fun b hb ↦ hrich b hb
      _ = R * ∑ b ∈ B, (neighborsIn G A b).card := by
        rw [Finset.mul_sum]
      _ = R * (G.interedges B A).card := by
        rw [sum_card_neighborsIn_eq_card_interedges]
  have hupper : R * (G.interedges A B).card < A.card * B.card := by
    calc
      R * (G.interedges A B).card =
          R * ∑ a ∈ A, (neighborsIn G B a).card := by
        rw [sum_card_neighborsIn_eq_card_interedges]
      _ = ∑ a ∈ A, R * (neighborsIn G B a).card := by
        rw [Finset.mul_sum]
      _ < ∑ _a ∈ A, B.card := by
        exact Finset.sum_lt_sum_of_nonempty hA fun a ha ↦ hnone a ha
      _ = A.card * B.card := by simp
  have hinter : (G.interedges B A).card = (G.interedges A B).card := by
    exact (Rel.card_interedges_comm G.symm A B).symm
  exact (not_lt_of_ge (by simpa [hinter] using hlower)) hupper

/-- Adding a vertex to the covering set adds precisely its neighbors which
were not covered before. -/
theorem card_coveredBy_insert
    {V : Type u} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S B : Finset V) (a : V) :
    (coveredBy G (insert a S) B).card =
      (coveredBy G S B).card +
        (neighborsIn G (B \ coveredBy G S B) a).card := by
  classical
  let C := coveredBy G S B
  let N := neighborsIn G (B \ C) a
  have hset : coveredBy G (insert a S) B =
      coveredBy G S B ∪ neighborsIn G (B \ coveredBy G S B) a := by
    ext b
    constructor
    · intro hb
      rw [coveredBy, Finset.mem_filter] at hb
      obtain ⟨hbB, x, hx, hxb⟩ := hb
      by_cases hbC : b ∈ coveredBy G S B
      · exact Finset.mem_union_left _ hbC
      · apply Finset.mem_union_right
        rw [neighborsIn, Finset.mem_filter]
        refine ⟨Finset.mem_sdiff.mpr ⟨hbB, hbC⟩, ?_⟩
        rcases Finset.mem_insert.mp hx with rfl | hxS
        · exact hxb
        · exact False.elim (hbC (Finset.mem_filter.mpr
            ⟨hbB, x, hxS, hxb⟩))
    · intro hb
      rw [Finset.mem_union] at hb
      rw [coveredBy, Finset.mem_filter]
      rcases hb with hbC | hbN
      · rw [coveredBy, Finset.mem_filter] at hbC
        obtain ⟨hbB, x, hxS, hxb⟩ := hbC
        exact ⟨hbB, x, Finset.mem_insert_of_mem hxS, hxb⟩
      · rw [neighborsIn, Finset.mem_filter] at hbN
        exact ⟨(Finset.mem_sdiff.mp hbN.1).1, a,
          Finset.mem_insert_self _ _, hbN.2⟩
  rw [hset, Finset.card_union_of_disjoint]
  rw [Finset.disjoint_left]
  intro b hbC hbN
  rw [neighborsIn, Finset.mem_filter] at hbN
  exact (Finset.mem_sdiff.mp hbN.1).2 hbC

/-- If every vertex of `B` sees at least a reciprocal `R`-fraction of `A`,
then at most `R` vertices of `A` cover at least half of `B`.

This is the elementary bounded-cover argument used before applying the
bipartite comb lemma. The proof greedily adds a vertex. Until half of `B`
is covered, each addition covers enough new vertices that after `R` additions
the desired conclusion is forced. -/
theorem exists_bounded_half_cover
    {V : Type u} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (A B : Finset V) (R : ℕ)
    (hR : 0 < R) (hA : A.Nonempty)
    (hrich : ∀ b ∈ B, A.card ≤ R * (neighborsIn G A b).card) :
    ∃ S : Finset V, S ⊆ A ∧ S.card ≤ R ∧
      B.card ≤ 2 * (coveredBy G S B).card := by
  classical
  let P : ℕ → Prop := fun m ↦
    ∃ S : Finset V, S ⊆ A ∧ S.card ≤ m ∧
      (B.card ≤ 2 * (coveredBy G S B).card ∨
        m * B.card ≤ 2 * R * (coveredBy G S B).card)
  have hP : ∀ m : ℕ, P m := by
    intro m
    induction m with
    | zero =>
        refine ⟨∅, Finset.empty_subset _, by simp,
          Or.inr ?_⟩
        simp [coveredBy_empty]
    | succ m ih =>
        obtain ⟨S, hSA, hSm, hdone | hbudget⟩ := ih
        · exact ⟨S, hSA, hSm.trans (Nat.le_succ _), Or.inl hdone⟩
        · by_cases hdone : B.card ≤ 2 * (coveredBy G S B).card
          · exact ⟨S, hSA, hSm.trans (Nat.le_succ _), Or.inl hdone⟩
          · let C := coveredBy G S B
            let U := B \ C
            have hCsub : C ⊆ B := coveredBy_subset G S B
            have hsplit : B.card = C.card + U.card := by
              have hpart := Finset.card_sdiff_add_card_eq_card hCsub
              change (B \ C).card + C.card = B.card at hpart
              change B.card = C.card + (B \ C).card
              omega
            have hBtwoU : B.card ≤ 2 * U.card := by
              have hlt : 2 * C.card < B.card := Nat.lt_of_not_ge hdone
              omega
            have hrichU : ∀ b ∈ U,
                A.card ≤ R * (neighborsIn G A b).card := by
              intro b hb
              exact hrich b (Finset.mem_sdiff.mp hb).1
            obtain ⟨a, haA, ha⟩ :=
              exists_vertex_covering_fraction G A U R hA hrichU
            let S' := insert a S
            have hS'A : S' ⊆ A := by
              intro x hx
              rcases Finset.mem_insert.mp hx with rfl | hxS
              · exact haA
              · exact hSA hxS
            have hS'card : S'.card ≤ m + 1 := by
              calc
                S'.card ≤ S.card + 1 := Finset.card_insert_le _ _
                _ ≤ m + 1 := Nat.add_le_add_right hSm 1
            have hcovercard : (coveredBy G S' B).card =
                C.card + (neighborsIn G U a).card := by
              simpa [S', C, U] using card_coveredBy_insert G S B a
            refine ⟨S', hS'A, by simpa using hS'card, Or.inr ?_⟩
            rw [hcovercard]
            have hnew : B.card ≤
                2 * R * (neighborsIn G U a).card := by
              calc
                B.card ≤ 2 * U.card := hBtwoU
                _ ≤ 2 * (R * (neighborsIn G U a).card) :=
                  Nat.mul_le_mul_left 2 ha
                _ = 2 * R * (neighborsIn G U a).card := by ring
            calc
              (m + 1) * B.card = m * B.card + B.card := by ring
              _ ≤ 2 * R * C.card +
                    2 * R * (neighborsIn G U a).card :=
                Nat.add_le_add hbudget hnew
              _ = 2 * R *
                    (C.card + (neighborsIn G U a).card) := by ring
  obtain ⟨S, hSA, hSR, hdone | hbudget⟩ := hP R
  · exact ⟨S, hSA, hSR, hdone⟩
  · refine ⟨S, hSA, hSR, ?_⟩
    apply Nat.le_of_mul_le_mul_left (c := R) (hc := hR)
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hbudget

end Lax57Proofs
