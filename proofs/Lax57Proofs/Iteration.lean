import Lax57.SparseHouseAcceleration
import Mathlib.Tactic

namespace Lax57Proofs

open Finset
open scoped SimpleGraph
open Lax57.GraphDefinitions

universe u

/-- Sparsity is monotone in the cleared reciprocal parameter. -/
theorem ESparse.mono_parameter
    {V : Type u} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {E E' : ℕ} {S : Finset V}
    (hEE' : E' ≤ E) (h : ESparse G E S) : ESparse G E' S := by
  intro v
  exact (Nat.mul_le_mul_right _ hEE').trans (h v)

/-- Iterating the reciprocal-square sparse-house step either reaches the
requested sparsity or produces a polynomial-width uniform blockade. -/
theorem iterate_sparse_house
    (d c D : ℕ) (hd : 2 ≤ d)
    (hconstant : D * (64 ^ (32 * d ^ 3) + 33) ≤ 2 ^ c)
    (hstep : ∀ R : ℕ, 64 ≤ R →
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V),
        IsHouseFree G → ESparse G (R ^ 2) S →
          (∃ T : Finset V, T ⊆ S ∧
              S.card ≤ R ^ (32 * d ^ 3) * T.card ∧
                ESparse G (R ^ (2 * d)) T) ∨
            (∃ B : Blockade (V := V) R,
              B.IsInside S ∧ B.IsUniform G ∧
                ∀ i : Fin R,
                  S.card ≤ R ^ (36 * d ^ 3) * (B.block i).card)) :
    let a := c + d * (32 * d ^ 3) + 36 * d ^ 3
    ∀ E : ℕ, 3 ≤ E →
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V),
        IsHouseFree G → Fintype.card V ≤ D * S.card →
          ESparse G (64 ^ 2) S →
            (∃ X : Finset V,
                Fintype.card V ≤ E ^ a * X.card ∧ ERestricted G E X) ∨
              HasUniformBlockade G E a := by
  dsimp only
  intro E hE V _ _ G _ S hfree hsize hsparse
  let A := 32 * d ^ 3
  let Bexp := 36 * d ^ 3
  let a := c + d * A + Bexp
  have hEpos : 0 < E := by omega
  have hRpos : 0 < (64 : ℕ) := by omega
  have hc_le_a : c ≤ a := by simp only [a]; omega
  have hA_le_dA : A ≤ d * A := by nlinarith
  have hcAB_le_a : c + A + Bexp ≤ a := by
    simp only [a]
    omega
  have hD64 : D * 64 ^ A ≤ 2 ^ c := by
    have hle : D * 64 ^ A ≤ D * (64 ^ A + 33) :=
      Nat.mul_le_mul_left D (Nat.le_add_right _ _)
    exact hle.trans (by simpa [A] using hconstant)
  let Outcome : Prop :=
    (∃ X : Finset V,
        Fintype.card V ≤ E ^ a * X.card ∧ ERestricted G E X) ∨
      HasUniformBlockade G E a
  let P : ℕ → Prop := fun m ↦
    ∀ (R : ℕ) (T : Finset V), E - R = m → 64 ≤ R →
      (R = 64 ∨ R < E ^ d) →
      Fintype.card V ≤ D * R ^ A * T.card →
      ESparse G (R ^ 2) T → Outcome
  have hP : ∀ m : ℕ, P m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro R T hm hR hRorigin hsizeT hsparseT
        by_cases htarget : E ≤ R ^ 2
        · apply Or.inl
          refine ⟨T, ?_, Or.inl (ESparse.mono_parameter G htarget hsparseT)⟩
          apply hsizeT.trans
          apply Nat.mul_le_mul_right T.card
          rcases hRorigin with rfl | hREd
          · have htwoE : 2 ^ c ≤ E ^ c := Nat.pow_le_pow_left (by omega) c
            have hcoeff : D * 64 ^ A ≤ E ^ c := hD64.trans htwoE
            exact hcoeff.trans <| Nat.pow_le_pow_right hEpos hc_le_a
          · have hD : D ≤ E ^ c := by
              have hD2 : D ≤ 2 ^ c := by
                calc
                  D = D * 1 := by simp
                  _ ≤ D * (64 ^ A + 33) :=
                    Nat.mul_le_mul_left D <| (by
                      exact (by norm_num : 1 ≤ 33).trans (Nat.le_add_left 33 (64 ^ A)))
                  _ ≤ 2 ^ c := by simpa [A] using hconstant
              exact hD2.trans (Nat.pow_le_pow_left (by omega) c)
            have hRA : R ^ A ≤ E ^ (d * A) := by
              calc
                R ^ A ≤ (E ^ d) ^ A := Nat.pow_le_pow_left hREd.le A
                _ = E ^ (d * A) := by rw [← pow_mul]
            calc
              D * R ^ A ≤ E ^ c * E ^ (d * A) := Nat.mul_le_mul hD hRA
              _ = E ^ (c + d * A) := (pow_add E c (d * A)).symm
              _ ≤ E ^ a := Nat.pow_le_pow_right hEpos (by simp [a])
        · have hR2E : R ^ 2 < E := Nat.lt_of_not_ge htarget
          have hRE : R < E := by
            have hRR2 : R ≤ R ^ 2 := by nlinarith
            exact hRR2.trans_lt hR2E
          rcases hstep R hR G T hfree hsparseT with hrefine | hblock
          · obtain ⟨T', _hsub, hloss, hsparse'⟩ := hrefine
            have hRRd : R < R ^ d := by
              calc
                R = R ^ 1 := by simp
                _ < R ^ d := Nat.pow_lt_pow_right (by omega) (by omega)
            have hmeasure : E - R ^ d < m := by
              rw [← hm]
              exact Nat.sub_lt_sub_left hRE hRRd
            apply ih (E - R ^ d) hmeasure (R ^ d) T' rfl
            · exact hR.trans (by
                simpa using Nat.pow_le_pow_right (by omega : 0 < R) (show 1 ≤ d by omega))
            · exact Or.inr (Nat.pow_lt_pow_left hRE (by omega))
            · apply hsizeT.trans
              calc
                D * R ^ A * T.card ≤
                    D * R ^ A * (R ^ A * T'.card) :=
                  Nat.mul_le_mul_left (D * R ^ A) hloss
                _ = D * R ^ (2 * A) * T'.card := by
                  rw [show 2 * A = A + A by omega, pow_add]
                  ring
                _ ≤ D * R ^ (d * A) * T'.card := by
                  have hp : R ^ (2 * A) ≤ R ^ (d * A) :=
                    Nat.pow_le_pow_right (by omega : 0 < R)
                      (Nat.mul_le_mul_right A hd)
                  exact Nat.mul_le_mul_right T'.card (Nat.mul_le_mul_left D hp)
                _ = D * (R ^ d) ^ A * T'.card := by rw [← pow_mul]
            · simpa [mul_comm, pow_mul] using hsparse'
          · obtain ⟨C, _hinside, huniform, hwidth⟩ := hblock
            apply Or.inr
            refine ⟨R, C, by omega, hRE.le, huniform, ?_⟩
            intro i
            have hDpow : D ≤ R ^ c := by
              have hD2 : D ≤ 2 ^ c := by
                calc
                  D = D * 1 := by simp
                  _ ≤ D * (64 ^ A + 33) :=
                    Nat.mul_le_mul_left D <| (by
                      exact (by norm_num : 1 ≤ 33).trans (Nat.le_add_left 33 (64 ^ A)))
                  _ ≤ 2 ^ c := by simpa [A] using hconstant
              exact hD2.trans (Nat.pow_le_pow_left (by omega) c)
            calc
              Fintype.card V ≤ D * R ^ A * T.card := hsizeT
              _ ≤ D * R ^ A *
                    (R ^ Bexp * (C.block i).card) :=
                Nat.mul_le_mul_left (D * R ^ A) (hwidth i)
              _ = (D * R ^ (A + Bexp)) * (C.block i).card := by
                rw [pow_add]
                ring
              _ ≤ (R ^ c * R ^ (A + Bexp)) * (C.block i).card := by
                gcongr
              _ = R ^ (c + A + Bexp) * (C.block i).card := by
                simp only [pow_add]
                ring
              _ ≤ R ^ a * (C.block i).card := by
                exact Nat.mul_le_mul_right (C.block i).card
                  (Nat.pow_le_pow_right (by omega : 0 < R) hcAB_le_a)
  have hstartSize : Fintype.card V ≤ D * 64 ^ A * S.card := by
    apply hsize.trans
    have hpow : 1 ≤ 64 ^ A := Nat.one_le_pow A 64 (by omega)
    calc
      D * S.card = D * 1 * S.card := by simp
      _ ≤ D * 64 ^ A * S.card := by
        exact Nat.mul_le_mul_right S.card (Nat.mul_le_mul_left D hpow)
  exact hP (E - 64) 64 S rfl (by omega) (Or.inl rfl) hstartSize
    (by simpa [A] using hsparse)

end Lax57Proofs
