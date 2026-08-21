import Lax57Proofs.CombPeeling
import Lax57Proofs.Helpers
import Lax57Proofs.InducedMapTools
import Lax57Proofs.SparseCombStep
import Mathlib.Tactic

set_option maxHeartbeats 800000
set_option maxRecDepth 2000

namespace Lax57Proofs

open Finset
open scoped SimpleGraph
open Lax57.GraphDefinitions

universe u

/-- A half-sized induced subgraph at the improved degree scale. -/
def HasCombFinerSet {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (R : ℕ) : Prop :=
  ∃ S : Finset V, Fintype.card V ≤ 2 * S.card ∧
    ∀ v : {x : V // x ∈ S},
      2 * R ^ 24 * (G.induce (S : Set V)).degree v ≤ S.card

/-- The local pure-or-directed-sparse blockade conclusion used by the
layout amplification. -/
def HasLocalBlockade {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (R X : ℕ) : Prop :=
  ∃ (k : ℕ) (B : Blockade (V := V) k),
    2 ≤ k ∧ k ≤ X ^ 2 ∧ R ≤ 17 * k ∧
      (B.IsPure G ∨ B.IsESparse G X) ∧
      ∀ i : Fin k, Fintype.card V ≤ k ^ 100 * (B.block i).card

private theorem final_peeling_coefficient
    {R : ℕ} (hR : 256 ≤ R) :
    let L := R / 16
    2 ≤ L ∧ L ≤ R ∧ R ≤ 17 * L ∧
      8 * R ^ 24 ≤ L ^ 100 := by
  dsimp only
  let L := R / 16
  have h16 : 0 < (16 : ℕ) := by omega
  have hL16 : 16 ≤ L := by
    rw [show L = R / 16 by rfl, Nat.le_div_iff_mul_le h16]
    omega
  have hLR : L ≤ R := Nat.div_le_self _ _
  have hRlt : R < 16 * (L + 1) := by
    simpa [L, Nat.mul_comm] using Nat.lt_mul_div_succ R h16
  have hR17 : R ≤ 17 * L := by omega
  have hconst : 8 * 17 ^ 24 ≤ 16 ^ 30 := by norm_num
  have hconstL : 8 * 17 ^ 24 ≤ L ^ 30 :=
    hconst.trans (Nat.pow_le_pow_left hL16 30)
  refine ⟨by omega, hLR, hR17, ?_⟩
  calc
    8 * R ^ 24 ≤ 8 * (17 * L) ^ 24 := by gcongr
    _ = (8 * 17 ^ 24) * L ^ 24 := by ring
    _ ≤ L ^ 30 * L ^ 24 := Nat.mul_le_mul_right _ hconstL
    _ = L ^ 54 := by ring
    _ ≤ L ^ 100 := Nat.pow_le_pow_right (by omega) (by omega)

/-- Iterating the sparse-pair alternative of `sparse_comb_step` produces a
long directed-sparse blockade unless the graph first becomes substantially
sparser or a pure blockade appears. -/
theorem iterate_sparse_comb
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (R X : ℕ)
    (hR : 256 ≤ R) (hRX : R ≤ X)
    (hsize : 2 * R ^ 100 ≤ Fintype.card V)
    (hfree : IsHouseFree G)
    (hsparse : ∀ v : V,
      2 * R ^ 12 * G.degree v ≤ Fintype.card V) :
    HasCombFinerSet G R ∨ HasLocalBlockade G R X := by
  classical
  let n := Fintype.card V
  let L := R / 16
  have hRpos : 0 < R := by omega
  have hXpos : 0 < X := hRpos.trans_le hRX
  have hL : 2 ≤ L := (final_peeling_coefficient hR).1
  let Outcome : Prop := HasCombFinerSet G R ∨ HasLocalBlockade G R X
  let P : ℕ → Prop := fun q ↦
    ∀ (m : ℕ), L - m = q → m ≤ L →
      CombPeeling G R X m → Outcome
  have hP : ∀ q : ℕ, P q := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
        intro m hqm hmL Peeling
        by_cases hmEq : m = L
        · subst m
          apply Or.inr
          refine ⟨L, Peeling.blocks, hL,
            (final_peeling_coefficient hR).2.1.trans
              (hRX.trans (Nat.le_pow (by norm_num : 0 < (2 : ℕ)))),
            (final_peeling_coefficient hR).2.2.1,
            Or.inr Peeling.blocks_sparse, ?_⟩
          intro i
          exact (Peeling.blocks_wide i).trans
            (Nat.mul_le_mul_right _ (final_peeling_coefficient hR).2.2.2)
        · have hmLt : m < L := lt_of_le_of_ne hmL hmEq
          have hm16 : 16 * m < R := by
            have h16L : 16 * L ≤ R := by
              simpa [L] using Nat.mul_div_le R 16
            omega
          have hnpos : 0 < n := by
            have : 0 < 2 * R ^ 100 := by positivity
            exact this.trans_le hsize
          have hhalf : n ≤ 2 * Peeling.remainder.card := by
            by_contra hnot
            have htwo : 2 * Peeling.remainder.card < n := Nat.lt_of_not_ge hnot
            have hnrem : n ≤ 2 * (n - Peeling.remainder.card) := by
              have hrem : Peeling.remainder.card ≤ n := by
                simpa [n] using Finset.card_le_card
                  (Finset.subset_univ Peeling.remainder)
              omega
            have hmul : R * n ≤ 8 * m * n := by
              calc
                R * n ≤ R * (2 * (n - Peeling.remainder.card)) :=
                  Nat.mul_le_mul_left _ hnrem
                _ = 2 * (R * (n - Peeling.remainder.card)) := by ring
                _ ≤ 2 * (4 * m * n) :=
                  Nat.mul_le_mul_left 2 Peeling.removed_small
                _ = 8 * m * n := by ring
            have hRm : R ≤ 8 * m :=
              Nat.le_of_mul_le_mul_right hmul hnpos
            omega
          have hremSize : R ^ 100 ≤ Peeling.remainder.card := by
            apply Nat.le_of_mul_le_mul_left (c := 2) (hc := by omega)
            exact hsize.trans hhalf
          let H := G.induce (Peeling.remainder : Set V)
          have hsparseH : ∀ v : {x : V // x ∈ Peeling.remainder},
              R ^ 12 * H.degree v ≤ Fintype.card {x : V // x ∈ Peeling.remainder} := by
            intro v
            have hdeg := degree_induce_finset_le G Peeling.remainder v
            have hglobal := hsparse v.1
            have hdouble : 2 * (R ^ 12 * H.degree v) ≤ n := by
              calc
                2 * (R ^ 12 * H.degree v) ≤
                    2 * (R ^ 12 * G.degree v.1) := by gcongr
                _ = 2 * R ^ 12 * G.degree v.1 := by ring
                _ ≤ n := by simpa [n] using hglobal
            apply Nat.le_of_mul_le_mul_left (c := 2) (hc := by omega)
            simpa [H] using hdouble.trans hhalf
          rcases sparse_comb_step H R X hR hRX (by simpa [H] using hremSize)
              (IsHouseFree.induce_finset hfree Peeling.remainder) hsparseH with
            hfiner | hpure | hpeel
          · apply Or.inl
            refine ⟨Peeling.remainder, hhalf, ?_⟩
            intro v
            simpa [H] using hfiner v
          · apply Or.inr
            obtain ⟨k, B₀, hkLower, hkUpper, hpureB, hwidth⟩ := hpure
            let e : {x : V // x ∈ Peeling.remainder} ↪ V :=
              ⟨Subtype.val, Subtype.val_injective⟩
            let B := mapBlockade e B₀
            have hk2 : 2 ≤ k := by
              exact (show 2 ≤ R ^ 3 by
                exact (by omega : 2 ≤ R).trans
                  (Nat.le_pow (by norm_num : 0 < (3 : ℕ)))).trans hkLower
            have hRk : R ≤ 17 * k := by
              calc
                R ≤ R ^ 3 := Nat.le_pow (by norm_num : 0 < (3 : ℕ))
                _ ≤ k := hkLower
                _ ≤ 17 * k := by omega
            refine ⟨k, B, hk2, hkUpper, hRk, Or.inl ?_, ?_⟩
            · exact Blockade.IsPure.map_induce G Peeling.remainder hpureB
            · intro i
              have htwoPow : 2 * k ^ 40 ≤ k ^ 100 := by
                calc
                  2 * k ^ 40 ≤ k * k ^ 40 := Nat.mul_le_mul_right _ hk2
                  _ = k ^ 41 := by ring
                  _ ≤ k ^ 100 := Nat.pow_le_pow_right (by omega) (by omega)
              calc
                n ≤ 2 * Peeling.remainder.card := hhalf
                _ ≤ 2 * (k ^ 40 * (B₀.block i).card) :=
                  Nat.mul_le_mul_left 2 (by simpa [H] using hwidth i)
                _ = (2 * k ^ 40) * (B.block i).card := by simp [B]; ring
                _ ≤ k ^ 100 * (B.block i).card :=
                  Nat.mul_le_mul_right _ htwoPow
          · obtain ⟨Z₀, Y₀, hdisj₀, hwidth₀, hremoved₀, hsparse₀⟩ := hpeel
            let e : {x : V // x ∈ Peeling.remainder} ↪ V :=
              ⟨Subtype.val, Subtype.val_injective⟩
            let Z : Finset V := Z₀.map e
            let Y : Finset V := Y₀.map e
            have hZ : Z ⊆ Peeling.remainder := by
              intro z hz
              obtain ⟨zR, _hz, rfl⟩ := Finset.mem_map.mp hz
              exact zR.property
            have hY : Y ⊆ Peeling.remainder := by
              intro y hy
              obtain ⟨yR, _hy, rfl⟩ := Finset.mem_map.mp hy
              exact yR.property
            have hdisj : Disjoint Z Y := by
              rw [Finset.disjoint_left]
              intro z hzZ hzY
              obtain ⟨zR, hzR, rfl⟩ := Finset.mem_map.mp hzZ
              obtain ⟨yR, hyR, heq⟩ := Finset.mem_map.mp hzY
              have : zR = yR := e.injective heq.symm
              subst yR
              exact Finset.disjoint_left.mp hdisj₀ hzR hyR
            have hwidth' : Peeling.remainder.card ≤
                4 * R ^ 24 * Z.card := by
              simpa [H, Z] using hwidth₀
            have hremoved' : R * (Peeling.remainder.card - Y.card) ≤
                4 * Peeling.remainder.card := by
              simpa [H, Y] using hremoved₀
            have hsparse' : ESparseTo G X Y Z := by
              exact ESparseTo.map_induce G Peeling.remainder hsparse₀
            let Peeling' := Peeling.snoc Z Y hZ hY hdisj hhalf
              hwidth' hremoved' hsparse'
            have hmeasure : L - (m + 1) < q := by
              rw [← hqm]
              exact Nat.sub_lt_sub_left hmLt (by omega)
            exact ih (L - (m + 1)) hmeasure (m + 1) rfl (by omega) Peeling'
  exact hP L 0 (by simp) (Nat.zero_le _) (CombPeeling.nil G R X)

end Lax57Proofs
