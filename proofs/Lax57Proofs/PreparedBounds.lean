import Mathlib.Tactic

namespace Lax57Proofs

/-- Multiplying two powers costs the sum of their exponents. -/
theorem mul_pow_le_pow {Q a b c : ℕ} (hQ : 0 < Q) (h : a + b ≤ c) :
    Q ^ a * Q ^ b ≤ Q ^ c := by
  rw [← pow_add]
  exact Nat.pow_le_pow_right hQ h

/-- All numerical reserves used in the preparation of the long blockade.
The deliberately generous rescaling `d = 100 d₀` keeps the graph argument
free of fragile constant calculations. -/
theorem prepared_exponent_bounds {d₀ : ℕ} (hd₀ : 40 ≤ d₀) :
    let d := 100 * d₀
    40 ≤ d ∧
      ∀ Q : ℕ, 8 ≤ Q →
        let L := Q ^ (4 * d)
        let W := L ^ (10 * d₀ ^ 2)
        2 ≤ L ∧ 0 < W ∧
          2 * W * (4 * Q ^ 2) ≤ Q ^ (30 * d ^ 3) ∧
          2 * W * (2 * L) ≤ Q ^ (30 * d ^ 3) ∧
          128 * L ^ 3 * (2 * Q ^ 2 * L) ≤ L ^ d₀ ∧
          Q * L ≤ W ∧
          32 * W * Q ^ 3 ≤ Q ^ (33 * d ^ 3) ∧
          32 * W * Q ^ 2 ≤ Q ^ (30 * d ^ 3) := by
  dsimp only
  let d := 100 * d₀
  refine ⟨by omega, ?_⟩
  intro Q hQ
  let L := Q ^ (4 * d)
  let W := L ^ (10 * d₀ ^ 2)
  have hQpos : 0 < Q := by omega
  have hQone : 1 < Q := by omega
  have hdpos : 0 < d := by simp [d]; omega
  have hL : L = Q ^ (4 * d) := rfl
  have hW : W = Q ^ ((4 * d) * (10 * d₀ ^ 2)) := by
    change (Q ^ (4 * d)) ^ (10 * d₀ ^ 2) = _
    exact (pow_mul Q (4 * d) (10 * d₀ ^ 2)).symm
  have h32 : 32 ≤ Q ^ 2 := by nlinarith
  have h8 : 8 ≤ Q := hQ
  have h4 : 4 ≤ Q := by omega
  have h2 : 2 ≤ Q := by omega
  have hExpSmall :
      (4 * d) * (10 * d₀ ^ 2) + 4 ≤ 30 * d ^ 3 := by
    simp only [d]
    nlinarith [show 1 ≤ d₀ from by omega]
  have hExpL :
      (4 * d) * (10 * d₀ ^ 2) + (4 * d + 1) ≤ 30 * d ^ 3 := by
    simp only [d]
    nlinarith [show 1 ≤ d₀ from by omega]
  have hThinExp : 4 * (4 * d) + 6 ≤ (4 * d) * d₀ := by
    nlinarith
  have hQLExp : 4 * d + 1 ≤ (4 * d) * (10 * d₀ ^ 2) := by
    nlinarith
  have hWidth33 :
      (4 * d) * (10 * d₀ ^ 2) + 5 ≤ 33 * d ^ 3 := by
    simp only [d]
    nlinarith [show 1 ≤ d₀ from by omega]
  have hWidth30 :
      (4 * d) * (10 * d₀ ^ 2) + 4 ≤ 30 * d ^ 3 := hExpSmall
  refine ⟨?_, by positivity, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change 2 ≤ L
    calc
      2 ≤ Q := h2
      _ ≤ L := by
        change Q ≤ Q ^ (4 * d)
        exact Nat.le_pow (by positivity)
  · change 2 * W * (4 * Q ^ 2) ≤ Q ^ (30 * d ^ 3)
    rw [hW]
    calc
      2 * Q ^ ((4 * d) * (10 * d₀ ^ 2)) * (4 * Q ^ 2)
          = Q ^ ((4 * d) * (10 * d₀ ^ 2)) * (8 * Q ^ 2) := by ring
      _
          ≤ Q ^ ((4 * d) * (10 * d₀ ^ 2)) * (Q ^ 2 * Q ^ 2) := by
            gcongr
            omega
      _ = Q ^ ((4 * d) * (10 * d₀ ^ 2)) * Q ^ 4 := by
        rw [← pow_add]
      _ ≤ Q ^ (30 * d ^ 3) := mul_pow_le_pow hQpos hExpSmall
  · change 2 * W * (2 * L) ≤ Q ^ (30 * d ^ 3)
    rw [hW, hL]
    calc
      2 * Q ^ ((4 * d) * (10 * d₀ ^ 2)) * (2 * Q ^ (4 * d))
          = Q ^ ((4 * d) * (10 * d₀ ^ 2)) * (4 * Q ^ (4 * d)) := by ring
      _
          ≤ Q ^ ((4 * d) * (10 * d₀ ^ 2)) *
              (Q * Q ^ (4 * d)) := by gcongr
      _ = Q ^ ((4 * d) * (10 * d₀ ^ 2)) * Q ^ (4 * d + 1) := by
        congr 1
        exact (pow_succ' Q (4 * d)).symm
      _ ≤ Q ^ (30 * d ^ 3) := mul_pow_le_pow hQpos hExpL
  · change 128 * L ^ 3 * (2 * Q ^ 2 * L) ≤ L ^ d₀
    rw [hL]
    calc
      128 * (Q ^ (4 * d)) ^ 3 * (2 * Q ^ 2 * Q ^ (4 * d))
          ≤ Q ^ 3 * (Q ^ (4 * d)) ^ 3 * (Q * Q ^ 2 * Q ^ (4 * d)) := by
            gcongr
            nlinarith
      _ = Q ^ (4 * (4 * d) + 6) := by
        rw [show (Q ^ (4 * d)) ^ 3 = Q ^ ((4 * d) * 3) by
          rw [← pow_mul]]
        rw [show Q * Q ^ 2 * Q ^ (4 * d) = Q ^ (4 * d + 3) by
          rw [show Q * Q ^ 2 = Q ^ 3 by ring, ← pow_add]
          congr 1 <;> omega]
        rw [show Q ^ 3 * Q ^ ((4 * d) * 3) = Q ^ ((4 * d) * 3 + 3) by
          rw [← pow_add]
          congr 1 <;> omega]
        rw [← pow_add]
        congr 1 <;> omega
      _ ≤ Q ^ ((4 * d) * d₀) := Nat.pow_le_pow_right hQpos hThinExp
      _ = (Q ^ (4 * d)) ^ d₀ := by rw [pow_mul]
  · change Q * L ≤ W
    rw [hL, hW]
    calc
      Q * Q ^ (4 * d) = Q ^ (4 * d + 1) :=
        (pow_succ' Q (4 * d)).symm
      _ ≤ Q ^ ((4 * d) * (10 * d₀ ^ 2)) :=
        Nat.pow_le_pow_right hQpos hQLExp
  · change 32 * W * Q ^ 3 ≤ Q ^ (33 * d ^ 3)
    rw [hW]
    calc
      32 * Q ^ ((4 * d) * (10 * d₀ ^ 2)) * Q ^ 3
          ≤ Q ^ 2 * Q ^ ((4 * d) * (10 * d₀ ^ 2)) * Q ^ 3 := by
            gcongr
      _ = Q ^ ((4 * d) * (10 * d₀ ^ 2) + 5) := by
        rw [show Q ^ 2 * Q ^ ((4 * d) * (10 * d₀ ^ 2)) =
            Q ^ ((4 * d) * (10 * d₀ ^ 2) + 2) by
          rw [← pow_add]
          congr 1 <;> omega]
        rw [← pow_add]
      _ ≤ Q ^ (33 * d ^ 3) := Nat.pow_le_pow_right hQpos hWidth33
  · change 32 * W * Q ^ 2 ≤ Q ^ (30 * d ^ 3)
    rw [hW]
    calc
      32 * Q ^ ((4 * d) * (10 * d₀ ^ 2)) * Q ^ 2
          ≤ Q ^ 2 * Q ^ ((4 * d) * (10 * d₀ ^ 2)) * Q ^ 2 := by
            gcongr
      _ = Q ^ ((4 * d) * (10 * d₀ ^ 2) + 4) := by
        rw [show Q ^ 2 * Q ^ ((4 * d) * (10 * d₀ ^ 2)) =
            Q ^ ((4 * d) * (10 * d₀ ^ 2) + 2) by
          rw [← pow_add]
          congr 1 <;> omega]
        rw [← pow_add]
      _ ≤ Q ^ (30 * d ^ 3) := Nat.pow_le_pow_right hQpos hWidth30

end Lax57Proofs
