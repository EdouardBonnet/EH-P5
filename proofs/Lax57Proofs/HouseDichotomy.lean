import Lax57.HouseDichotomy
import Lax57.SparseHouseTools
import Lax57Proofs.SparseHouseAcceleration
import Lax57Proofs.SparseP5Pair
import Lax57Proofs.Iteration
import Lax54.MaximumDegreeReduction
import Mathlib.Tactic

namespace Lax57Proofs

open Finset
open scoped SimpleGraph
open Lax57.GraphDefinitions

universe u

/-- The complement of a house-free graph is `P5`-free. -/
theorem IsHouseFree.compl_isP5Free
    {V : Type u} {G : SimpleGraph V} (hfree : IsHouseFree G) :
    IsP5Free Gᶜ := by
  intro hp5
  apply hfree
  simpa [House] using hp5.compl

/-- Anticompleteness in the complement is completeness in the graph. -/
theorem Blockade.IsAnticomplete.compl_to_complete
    {V : Type u} [DecidableEq V] {G : SimpleGraph V} {k : ℕ}
    {B : Blockade (V := V) k} (hanti : B.IsAnticomplete Gᶜ) :
    B.IsComplete G := by
  intro i j hij x hx y hy
  by_contra hxy
  apply hanti hij x hx y hy
  rw [SimpleGraph.compl_adj]
  refine ⟨?_, hxy⟩
  intro heq
  subst y
  exact Finset.disjoint_left.mp (B.disjoint hij) hx hy

/--
---
conclusion: Lax57.HouseDichotomy.house_dichotomy
assumptions:
  - Lax54.AveragingLemma.sparse_graph_thinning
  - Lax54.BipartiteCombLemma.bipartite_comb_lemma
  - Lax54.MaximumDegreeReduction.maximum_degree_reduction
  - Lax54.RodlTheorem.rodl_theorem
---
Rödl's maximum-degree reduction gives a linearly large induced set on which
one of the two complementary graphs is $1/64^2$-sparse. In the direct
orientation, iterate the sparse-house acceleration lemma until the requested
parameter is reached. In the complementary orientation, the graph is
$P_5$-free, so the sparse anticomplete-pair lemma gives a complete two-block
blockade in the original graph. A single exponent absorbs the fixed and
polynomial losses.

# Attribution

This packages the iteration in the proof of Lemma 7.3 of
Nguyen, Scott, and Seymour, using their Lemmas 4.4 and 7.2 and the
maximum-degree form of Rödl's theorem already formalized in Lax 54.
-/
theorem house_dichotomy :
    ∃ a : ℕ, 1 ≤ a ∧
      ∀ E : ℕ, 3 ≤ E →
        ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
          [DecidableRel G.Adj],
          IsHouseFree G →
            (∃ X : Finset V,
                Fintype.card V ≤ E ^ a * X.card ∧ ERestricted G E X) ∨
              HasUniformBlockade G E a := by
  obtain ⟨d, hd, hstep⟩ := Lax57Proofs.sparse_house_acceleration
  let A := 32 * d ^ 3
  let Bexp := 36 * d ^ 3
  obtain ⟨D, hDpos, hmax⟩ :=
    Lax54.MaximumDegreeReduction.maximum_degree_reduction House (64 ^ 2)
      (by norm_num)
  obtain ⟨c, hc⟩ :=
    pow_unbounded_of_one_lt (D * (64 ^ A + 33)) (by norm_num : (1 : ℕ) < 2)
  have hconstant : D * (64 ^ A + 33) ≤ 2 ^ c := hc.le
  let a := c + d * A + Bexp
  have hca : c ≤ a := by simp only [a]; omega
  have ha : 1 ≤ a := by
    have hBpos : 0 < Bexp := by simp [Bexp]; positivity
    simp only [a]
    omega
  refine ⟨a, ha, ?_⟩
  intro E hE V _ _ G _ hfree
  obtain ⟨X, hsize, hside⟩ := hmax G hfree
  rcases hside with hlow | hlowCompl
  · have hsparse : ESparse G (64 ^ 2) X := fun v ↦ (hlow v).le
    have hiter := iterate_sparse_house d c D hd
      (by simpa [A] using hconstant) hstep E hE G X hfree hsize hsparse
    simpa [a, A, Bexp] using hiter
  · have hsparseCompl : ESparse Gᶜ (64 ^ 2) X := fun v ↦ (hlowCompl v).le
    have hD2 : D ≤ 2 ^ c := by
      calc
        D = D * 1 := by simp
        _ ≤ D * (64 ^ A + 33) := Nat.mul_le_mul_left D <| (by
          exact (by norm_num : 1 ≤ 33).trans (Nat.le_add_left 33 (64 ^ A)))
        _ ≤ 2 ^ c := hconstant
    by_cases hX : 2 ≤ X.card
    · obtain ⟨B, _hinside, hanti, hwidth⟩ :=
        Lax57Proofs.sparse_P5_anticomplete_pair Gᶜ X
          (IsHouseFree.compl_isP5Free hfree) hX
          (ESparse.mono_parameter Gᶜ (by norm_num) hsparseCompl)
      apply Or.inr
      refine ⟨2, B, by omega, by omega,
        Or.inl (Blockade.IsAnticomplete.compl_to_complete hanti), ?_⟩
      intro i
      have hD32 : D * 32 ≤ 2 ^ c := by
        calc
          D * 32 ≤ D * (64 ^ A + 33) :=
            Nat.mul_le_mul_left D (by
              exact (Nat.le_add_left 33 (64 ^ A)).trans' (by norm_num))
          _ ≤ 2 ^ c := hconstant
      have h2ca : 2 ^ c ≤ 2 ^ a := Nat.pow_le_pow_right (by omega) hca
      calc
        Fintype.card V ≤ D * X.card := hsize
        _ ≤ D * (32 * (B.block i).card) :=
          Nat.mul_le_mul_left D (hwidth i)
        _ = (D * 32) * (B.block i).card := by ring
        _ ≤ 2 ^ c * (B.block i).card :=
          Nat.mul_le_mul_right (B.block i).card hD32
        _ ≤ 2 ^ a * (B.block i).card :=
          Nat.mul_le_mul_right (B.block i).card h2ca
    · apply Or.inl
      have hXlt : X.card < 2 := Nat.lt_of_not_ge hX
      have hcardSub : Fintype.card {x : V // x ∈ X} ≤ 1 := by
        simpa only [Fintype.card_coe] using (Nat.le_of_lt_succ hXlt)
      letI : Subsingleton {x : V // x ∈ X} :=
        ⟨Fintype.card_le_one_iff.mp hcardSub⟩
      have hzero : ESparse Gᶜ E X := by
        intro v
        simp [SimpleGraph.degree_eq_zero_of_subsingleton]
      refine ⟨X, ?_, Or.inr hzero⟩
      have hDE : D ≤ E ^ a := by
        exact hD2.trans <| (Nat.pow_le_pow_left (by omega) c).trans
          (Nat.pow_le_pow_right (by omega) hca)
      exact hsize.trans (Nat.mul_le_mul_right X.card hDE)

end Lax57Proofs
