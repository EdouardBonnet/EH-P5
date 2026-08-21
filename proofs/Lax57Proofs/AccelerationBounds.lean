import Mathlib.Tactic

namespace Lax57Proofs

/-- The integer scale `R² / 2` is still at least `R` and has enough slack
for `R` successive peels. -/
theorem half_square_bounds {R : ℕ} (hR : 64 ≤ R) :
    let Q := R ^ 2 / 2
    8 ≤ Q ∧ R ≤ Q ∧ 6 * R ≤ Q ∧
      2 * Q ≤ R ^ 2 ∧ R ^ 3 ≤ Q ^ 2 := by
  dsimp only
  let Q := R ^ 2 / 2
  have hRpos : 0 < R := by omega
  have hR2 : 2 ≤ R ^ 2 := by nlinarith
  have hQpos : 0 < Q := Nat.div_pos hR2 (by omega)
  have hdivlt : R ^ 2 < Q * 2 + 2 := by
    simpa [Q] using Nat.lt_div_mul_add (a := R ^ 2) (b := 2) (by omega)
  have hR2Q : R ^ 2 ≤ 3 * Q := by omega
  have h18 : 18 * R ≤ R ^ 2 := by nlinarith
  have h6 : 6 * R ≤ Q := by
    have : 3 * (6 * R) ≤ 3 * Q := by
      calc
        3 * (6 * R) = 18 * R := by ring
        _ ≤ R ^ 2 := h18
        _ ≤ 3 * Q := hR2Q
    exact Nat.le_of_mul_le_mul_left this (by omega)
  have h2Q : 2 * Q ≤ R ^ 2 := by
    simpa [Q, Nat.mul_comm] using Nat.div_mul_le_self (R ^ 2) 2
  have hsquare : R ^ 4 ≤ 9 * Q ^ 2 := by
    have := Nat.pow_le_pow_left hR2Q 2
    nlinarith
  have h9 : 9 * R ^ 3 ≤ R ^ 4 := by
    calc
      9 * R ^ 3 ≤ R * R ^ 3 := Nat.mul_le_mul_right (R ^ 3) (by omega)
      _ = R ^ 4 := by ring
  have hcubic : R ^ 3 ≤ Q ^ 2 := by
    apply Nat.le_of_mul_le_mul_left (c := 9) (by
      calc
        9 * R ^ 3 ≤ R ^ 4 := h9
        _ ≤ 9 * Q ^ 2 := hsquare) (by omega)
  refine ⟨?_, h6.trans' (by omega), h6, h2Q, hcubic⟩
  exact (by omega : 8 ≤ 6 * R).trans h6

/-- Rescaling `d₀` by a factor of three halves leaves room both for the
square change of scale and for all polynomial width losses. -/
theorem acceleration_exponent_bounds {d₀ : ℕ} (hd₀ : 40 ≤ d₀) :
    let d := 3 * d₀ / 2
    2 ≤ d ∧ 2 * d ≤ 3 * d₀ ∧
      60 * d₀ ^ 3 + 1 ≤ 32 * d ^ 3 ∧
      66 * d₀ ^ 3 + 1 ≤ 36 * d ^ 3 := by
  dsimp only
  let d := 3 * d₀ / 2
  change 2 ≤ d ∧ 2 * d ≤ 3 * d₀ ∧
    60 * d₀ ^ 3 + 1 ≤ 32 * d ^ 3 ∧
    66 * d₀ ^ 3 + 1 ≤ 36 * d ^ 3
  have hdUpper : 2 * d ≤ 3 * d₀ := by
    simpa [d, Nat.mul_comm] using Nat.div_mul_le_self (3 * d₀) 2
  have hdivlt : 3 * d₀ < d * 2 + 2 := by
    simpa [d] using Nat.lt_div_mul_add (a := 3 * d₀) (b := 2) (by omega)
  have hdLower : 4 * d₀ ≤ 3 * d := by omega
  have hcube0 := Nat.pow_le_pow_left hdLower 3
  have hcube : 64 * d₀ ^ 3 ≤ 27 * d ^ 3 := by
    nlinarith
  have hd03 : 1 ≤ d₀ ^ 3 := Nat.one_le_pow 3 d₀ (by omega)
  refine ⟨by omega, hdUpper, ?_, ?_⟩ <;> nlinarith

/-- Conversion of the improved sparsity parameter from scale `Q` back to
scale `R`. -/
theorem acceleration_sparsity_bound
    {R Q d₀ d : ℕ} (hR : 0 < R) (hcubic : R ^ 3 ≤ Q ^ 2)
    (hexp : 2 * d ≤ 3 * d₀) :
    R ^ (2 * d) ≤ Q ^ (2 * d₀) := by
  calc
    R ^ (2 * d) ≤ R ^ (3 * d₀) := Nat.pow_le_pow_right hR hexp
    _ = (R ^ 3) ^ d₀ := by rw [pow_mul]
    _ ≤ (Q ^ 2) ^ d₀ := Nat.pow_le_pow_left hcubic d₀
    _ = Q ^ (2 * d₀) := by rw [pow_mul]

/-- A factor two and a power of `Q ≤ R²` are absorbed by one spare
power of `R`. -/
theorem two_mul_scale_power
    {R Q a b : ℕ} (hR : 2 ≤ R) (hQR : Q ≤ R ^ 2)
    (hab : 2 * a + 1 ≤ b) :
    2 * Q ^ a ≤ R ^ b := by
  have hRpos : 0 < R := by omega
  calc
    2 * Q ^ a ≤ 2 * (R ^ 2) ^ a :=
      Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hQR a)
    _ ≤ R * (R ^ 2) ^ a := Nat.mul_le_mul_right ((R ^ 2) ^ a) hR
    _ = R ^ (2 * a + 1) := by
      rw [show R * (R ^ 2) ^ a = R ^ 1 * (R ^ 2) ^ a by simp,
        ← pow_mul, ← pow_add]
      congr 1
      omega
    _ ≤ R ^ b := Nat.pow_le_pow_right hRpos hab

end Lax57Proofs
