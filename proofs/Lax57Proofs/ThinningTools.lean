import Lax57.BlockadeThinning
import Mathlib.Tactic

namespace Lax57Proofs

open Finset
open scoped BigOperators SimpleGraph
open Lax57.GraphDefinitions

universe u

/-- Counting an oriented edge by its first endpoint gives the corresponding
sum of neighbor counts. -/
theorem sum_card_neighborsIn_eq_card_interedges
    {V : Type u} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (A B : Finset V) :
    ∑ x ∈ A, (neighborsIn G B x).card = (G.interedges A B).card := by
  classical
  change _ = (Rel.interedges G.Adj A B).card
  rw [Rel.interedges_eq_biUnion, Finset.card_biUnion]
  · simp [neighborsIn]
  · intro x hx y hy hxy
    change Disjoint
      ((neighborsIn G B x).map ⟨(x, ·), Prod.mk_right_injective x⟩)
      ((neighborsIn G B y).map ⟨(y, ·), Prod.mk_right_injective y⟩)
    rw [Finset.disjoint_left]
    intro p hpx hpy
    obtain ⟨a, _ha, ha⟩ := Finset.mem_map.mp hpx
    obtain ⟨b, _hb, hb⟩ := Finset.mem_map.mp hpy
    exact hxy (congrArg Prod.fst (ha.trans hb.symm))

/-- Weak sparsity is symmetric for an undirected graph. -/
theorem WeaklyESparse.symm
    {V : Type u} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {P : ℕ} {A B : Finset V}
    (h : WeaklyESparse G P A B) : WeaklyESparse G P B A := by
  change P * (Rel.interedges G.Adj B A).card ≤ B.card * A.card
  rw [← Rel.card_interedges_comm G.symm A B, Nat.mul_comm B.card A.card]
  exact h

/-- Integer Markov inequality in the form used twice in blockade cleaning.
If total score is at most `|Z| M`, the vertices whose score exceeds `c M`
occupy at most a `1/c` fraction. -/
theorem mul_card_filter_lt_le
    {V : Type u} [DecidableEq V] (Z : Finset V) (score : V → ℕ)
    (c M : ℕ) (hM : 0 < M)
    (htotal : ∑ x ∈ Z, score x ≤ Z.card * M) :
    c * (Z.filter fun x ↦ c * M < score x).card ≤ Z.card := by
  classical
  let D := Z.filter fun x ↦ c * M < score x
  by_cases hD : D.Nonempty
  · have hlower : D.card * (c * M) < ∑ x ∈ D, score x := by
      calc
        D.card * (c * M) = ∑ _x ∈ D, c * M := by simp
        _ < ∑ x ∈ D, score x :=
          Finset.sum_lt_sum_of_nonempty hD fun x hx ↦
            (Finset.mem_filter.mp hx).2
    have hsub : D ⊆ Z := Finset.filter_subset _ _
    have hsumsub : ∑ x ∈ D, score x ≤ ∑ x ∈ Z, score x :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ Nat.zero_le _
    apply Nat.le_of_mul_le_mul_right (c := M) ?_ hM
    calc
      (c * D.card) * M = D.card * (c * M) := by ring
      _ ≤ ∑ x ∈ D, score x := Nat.le_of_lt hlower
      _ ≤ ∑ x ∈ Z, score x := hsumsub
      _ ≤ Z.card * M := htotal
  · have hDeq : D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hD
    simp [D, hDeq]

/-- A union of `k` exceptional sets, each of cleared size at most `|Z|/c`,
has cleared size at most `k|Z|`. -/
theorem mul_card_biUnion_le
    {I : Type u} [Fintype I] [DecidableEq I]
    {V : Type*} [DecidableEq V] (Z : Finset V) (D : I → Finset V)
    (c : ℕ) (hD : ∀ i, c * (D i).card ≤ Z.card) :
    c * ((Finset.univ : Finset I).biUnion D).card ≤ Fintype.card I * Z.card := by
  calc
    c * ((Finset.univ : Finset I).biUnion D).card
        ≤ c * ∑ i : I, (D i).card :=
      Nat.mul_le_mul_left c Finset.card_biUnion_le
    _ = ∑ i : I, c * (D i).card := by rw [Finset.mul_sum]
    _ ≤ ∑ _i : I, Z.card := by
      apply Finset.sum_le_sum
      intro i hi
      exact hD i
    _ = Fintype.card I * Z.card := by simp

end Lax57Proofs
