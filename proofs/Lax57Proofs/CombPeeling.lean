import Lax57Proofs.BlockadeOperations
import Mathlib.Tactic

namespace Lax57Proofs

open Finset
open scoped SimpleGraph
open Lax57.GraphDefinitions

universe u

/-- Data accumulated by repeatedly taking the sparse-pair outcome of the
comb step. -/
structure CombPeeling {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (R X m : ℕ) where
  blocks : Blockade (V := V) m
  remainder : Finset V
  blocks_sparse : blocks.IsESparse G X
  blocks_remainder_disjoint :
    ∀ i : Fin m, Disjoint (blocks.block i) remainder
  remainder_sparse_to_blocks :
    ∀ i : Fin m, ESparseTo G X remainder (blocks.block i)
  blocks_wide : ∀ i : Fin m,
    Fintype.card V ≤ 8 * R ^ 24 * (blocks.block i).card
  removed_small :
    R * (Fintype.card V - remainder.card) ≤
      4 * m * Fintype.card V

/-- The empty peeling has the entire graph as remainder. -/
def CombPeeling.nil {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (R X : ℕ) :
    CombPeeling G R X 0 where
  blocks := ⟨Fin.elim0, fun {i j : Fin 0} _ ↦ Fin.elim0 i⟩
  remainder := Finset.univ
  blocks_sparse := fun {i j : Fin 0} _ ↦ Fin.elim0 i
  blocks_remainder_disjoint := fun i ↦ Fin.elim0 i
  remainder_sparse_to_blocks := fun i ↦ Fin.elim0 i
  blocks_wide := fun i ↦ Fin.elim0 i
  removed_small := by simp

/-- Add one sparse peel to an existing sequence. -/
noncomputable def CombPeeling.snoc
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {R X m : ℕ} (P : CombPeeling G R X m)
    (Z Y : Finset V) (hZ : Z ⊆ P.remainder) (hY : Y ⊆ P.remainder)
    (hZY : Disjoint Z Y)
    (hhalf : Fintype.card V ≤ 2 * P.remainder.card)
    (hwidth : P.remainder.card ≤ 4 * R ^ 24 * Z.card)
    (hremoved : R * (P.remainder.card - Y.card) ≤
      4 * P.remainder.card)
    (hsparse : ESparseTo G X Y Z) :
    CombPeeling G R X (m + 1) := by
  classical
  have hOldZ : ∀ i : Fin m, Disjoint (P.blocks.block i) Z := by
    intro i
    exact (P.blocks_remainder_disjoint i).mono_right hZ
  let B := snocBlockade P.blocks Z hOldZ
  refine ⟨B, Y, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    revert hij
    refine Fin.lastCases ?_ (fun i' ↦ ?_) i
    · intro hij
      exfalso
      have hj : j.val < m + 1 := j.isLt
      have hi : (Fin.last m).val = m := by simp
      omega
    · refine Fin.lastCases ?_ (fun j' ↦ ?_) j
      · intro _
        intro z hz
        simpa [B] using
          P.remainder_sparse_to_blocks i' z (hZ (by simpa [B] using hz))
      · intro hij
        have hij' : i' < j' := by
          simpa using hij
        simpa [B] using P.blocks_sparse hij'
  · intro i
    refine Fin.lastCases ?_ (fun i' ↦ ?_) i
    · simpa [B] using hZY
    · simpa [B] using (P.blocks_remainder_disjoint i').mono_right hY
  · intro i
    refine Fin.lastCases ?_ (fun i' ↦ ?_) i
    · simpa [B] using hsparse
    · intro y hy
      simpa [B] using P.remainder_sparse_to_blocks i' y (hY hy)
  · intro i
    refine Fin.lastCases ?_ (fun i' ↦ ?_) i
    · calc
        Fintype.card V ≤ 2 * P.remainder.card := hhalf
        _ ≤ 2 * (4 * R ^ 24 * Z.card) := Nat.mul_le_mul_left 2 hwidth
        _ = 8 * R ^ 24 * (B.block (Fin.last m)).card := by simp [B]; ring
    · simpa [B] using P.blocks_wide i'
  · have hYcard : Y.card ≤ P.remainder.card := Finset.card_le_card hY
    have hRcard : P.remainder.card ≤ Fintype.card V := by
      simpa using Finset.card_le_card (Finset.subset_univ P.remainder)
    have hsplit : Fintype.card V - Y.card =
        (Fintype.card V - P.remainder.card) +
          (P.remainder.card - Y.card) := by omega
    rw [hsplit, Nat.mul_add]
    calc
      R * (Fintype.card V - P.remainder.card) +
          R * (P.remainder.card - Y.card) ≤
          4 * m * Fintype.card V + 4 * P.remainder.card :=
        Nat.add_le_add P.removed_small hremoved
      _ ≤ 4 * m * Fintype.card V + 4 * Fintype.card V := by gcongr
      _ = 4 * (m + 1) * Fintype.card V := by ring

end Lax57Proofs
