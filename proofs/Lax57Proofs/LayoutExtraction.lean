import Lax57Proofs.LayoutRefinement
import Mathlib.Tactic

set_option maxHeartbeats 1200000
set_option maxRecDepth 3000

namespace Lax57Proofs

open Finset
open scoped SimpleGraph
open Lax57.GraphDefinitions

universe u

/-- Once a polynomial layout has reached `E` blocks, any `E` of them form a
semisparse blockade. The exceptional-edge bound controls every pair not
declared complete by the layout pattern. -/
theorem PolynomialLayout.extract_semisparse
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {E P Q d : ℕ} (L : PolynomialLayout G E P d)
    (hE : 2 ≤ E) (hreached : E ≤ L.card) (hshort : L.card < 2 * E)
    (hscale : Q * (2 * E) * E ^ (4 * d) ≤ P) :
    ∃ B : Blockade (V := V) E,
      B.IsSemisparse G Q ∧ B.HasWidthLoss (E ^ (2 * d)) := by
  classical
  letI : Fintype L.Index := L.fintypeIndex
  letI : DecidableEq L.Index := L.decidableEqIndex
  have hcard : Fintype.card (Fin E) ≤ Fintype.card L.Index := by
    simpa [PolynomialLayout.card] using hreached
  let f : Fin E ↪ L.Index :=
    (Function.Embedding.nonempty_of_card_le hcard).some
  let B : Blockade (V := V) E :=
    { block := fun i ↦ L.block (f i)
      disjoint := by
        intro i j hij
        exact L.disjoint (fun h ↦ hij (f.injective h)) }
  refine ⟨B, ?_, ?_⟩
  · intro i j hij
    by_cases hp : L.pattern.Adj (f i) (f j)
    · exact Or.inl (L.pattern_complete hp)
    · apply Or.inr
      have hsub : G.interedges (B.block i) (B.block j) ⊆
          wrongPairs G L.block L.pattern := by
        intro z hz
        rw [SimpleGraph.mem_interedges_iff] at hz
        rw [wrongPairs, Finset.mem_filter]
        refine ⟨by simp, f i, f j, ?_, hz.1, hz.2.1, hz.2.2, hp⟩
        exact fun h ↦ hij (f.injective h)
      have hedge : (G.interedges (B.block i) (B.block j)).card ≤
          (wrongPairs G L.block L.pattern).card := Finset.card_le_card hsub
      have hnprod : Fintype.card V ^ 2 ≤
          E ^ (4 * d) * ((B.block i).card * (B.block j).card) := by
        calc
          Fintype.card V ^ 2 = Fintype.card V * Fintype.card V := by
            rw [pow_two]
          _ ≤ (E ^ (2 * d) * (B.block i).card) *
                (E ^ (2 * d) * (B.block j).card) :=
            Nat.mul_le_mul (L.wide (f i)) (L.wide (f j))
          _ = E ^ (4 * d) * ((B.block i).card * (B.block j).card) := by
            rw [show 4 * d = 2 * d + 2 * d by omega, pow_add]
            ring
      have hcoefficient : L.card - 1 ≤ 2 * E := by omega
      have hCpos : 0 < 2 * E * E ^ (4 * d) := by positivity
      apply Nat.le_of_mul_le_mul_left (c := 2 * E * E ^ (4 * d)) ?_ hCpos
      calc
        (2 * E * E ^ (4 * d)) *
              (Q * (G.interedges (B.block i) (B.block j)).card) ≤
            (2 * E * E ^ (4 * d)) *
              (Q * (wrongPairs G L.block L.pattern).card) := by
          gcongr
        _ = (Q * (2 * E) * E ^ (4 * d)) *
              (wrongPairs G L.block L.pattern).card := by ring
        _ ≤ P * (wrongPairs G L.block L.pattern).card :=
          Nat.mul_le_mul_right _ hscale
        _ ≤ (L.card - 1) * Fintype.card V ^ 2 := L.wrong_budget
        _ ≤ (2 * E) * Fintype.card V ^ 2 :=
          Nat.mul_le_mul_right _ hcoefficient
        _ ≤ (2 * E) *
              (E ^ (4 * d) * ((B.block i).card * (B.block j).card)) :=
          Nat.mul_le_mul_left _ hnprod
        _ = (2 * E * E ^ (4 * d)) *
              ((B.block i).card * (B.block j).card) := by ring
  · intro i
    exact L.wide (f i)

end Lax57Proofs
