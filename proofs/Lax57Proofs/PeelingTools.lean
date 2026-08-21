import Lax57.SparseHouseTrichotomy
import Lax57Proofs.BlockadeOperations
import Lax57Proofs.InducedMapTools
import Mathlib.Tactic

namespace Lax57Proofs

open Finset
open scoped SimpleGraph
open Lax57.GraphDefinitions

universe u

/-- Data accumulated while repeatedly taking the anticomplete-peel outcome. -/
structure AnticompletePeeling {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (Q loss n : ℕ) where
  blocks : Blockade (V := V) n
  remainder : Finset V
  blocks_inside : blocks.IsInside S
  remainder_subset : remainder ⊆ S
  blocks_anticomplete : blocks.IsAnticomplete G
  blocks_remainder_disjoint :
    ∀ i : Fin n, Disjoint (blocks.block i) remainder
  blocks_remainder_anticomplete :
    ∀ i : Fin n, ∀ x ∈ blocks.block i, ∀ y ∈ remainder, ¬ G.Adj x y
  blocks_wide : ∀ i : Fin n,
    S.card ≤ 2 * Q ^ loss * (blocks.block i).card
  removed_small : Q * (S.card - remainder.card) ≤ 3 * n * S.card

/-- The empty peeling starts with the whole ambient set as its remainder. -/
def AnticompletePeeling.nil {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (Q loss : ℕ) :
    AnticompletePeeling G S Q loss 0 where
  blocks := ⟨Fin.elim0, fun {i j : Fin 0} _ ↦ Fin.elim0 i⟩
  remainder := S
  blocks_inside := fun i ↦ Fin.elim0 i
  remainder_subset := Finset.Subset.rfl
  blocks_anticomplete := fun {i j : Fin 0} _ ↦ Fin.elim0 i
  blocks_remainder_disjoint := fun i ↦ Fin.elim0 i
  blocks_remainder_anticomplete := fun i ↦ Fin.elim0 i
  blocks_wide := fun i ↦ Fin.elim0 i
  removed_small := by simp

/-- Add one anticomplete peel to an existing sequence. -/
noncomputable def AnticompletePeeling.snoc
    {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    {S : Finset V} {Q loss n : ℕ}
    (P : AnticompletePeeling G S Q loss n)
    (X Y : Finset V) (hX : X ⊆ P.remainder) (hY : Y ⊆ P.remainder)
    (hXY : Disjoint X Y)
    (hanti : ∀ x ∈ X, ∀ y ∈ Y, ¬ G.Adj x y)
    (hhalf : S.card ≤ 2 * P.remainder.card)
    (hwide : P.remainder.card ≤ Q ^ loss * X.card)
    (hremoved : Q * (P.remainder.card - Y.card) ≤
      3 * P.remainder.card) :
    AnticompletePeeling G S Q loss (n + 1) := by
  have holdX : ∀ i : Fin n, Disjoint (P.blocks.block i) X := by
    intro i
    apply Finset.disjoint_left.mpr
    intro x hxb hxX
    exact Finset.disjoint_left.mp (P.blocks_remainder_disjoint i) hxb (hX hxX)
  let B := snocBlockade P.blocks X holdX
  refine ⟨B, Y, ?_, hY.trans P.remainder_subset, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa [B] using hX.trans P.remainder_subset
    · simpa [B] using P.blocks_inside j
  · intro i j hij x hxi y hyj
    revert hij hxi hyj
    refine Fin.lastCases ?_ (fun i' ↦ ?_) i
    · refine Fin.lastCases ?_ (fun j' ↦ ?_) j
      · intro hij _ _
        exact False.elim (hij rfl)
      · intro _ hxi hyj hxy
        have hxX : x ∈ X := by simpa [B] using hxi
        have hyold : y ∈ P.blocks.block j' := by simpa [B] using hyj
        exact P.blocks_remainder_anticomplete j' y hyold x (hX hxX)
          (G.adj_comm _ _ |>.mp hxy)
    · refine Fin.lastCases ?_ (fun j' ↦ ?_) j
      · intro _ hxi hyj
        exact P.blocks_remainder_anticomplete i' x
          (by simpa [B] using hxi) y (hX (by simpa [B] using hyj))
      · intro hij hxi hyj
        exact P.blocks_anticomplete
          (fun heq ↦ hij (by apply Fin.ext; simpa using congrArg Fin.val heq)) x
          (by simpa [B] using hxi) y (by simpa [B] using hyj)
  · intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa [B] using hXY
    · apply Finset.disjoint_left.mpr
      intro x hxold hxY
      exact Finset.disjoint_left.mp (P.blocks_remainder_disjoint j)
        (by simpa [B] using hxold) (hY hxY)
  · intro i x hxi y hy
    revert hxi
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · intro hxi
      exact hanti x (by simpa [B] using hxi) y hy
    · intro hxi
      exact P.blocks_remainder_anticomplete j x (by simpa [B] using hxi)
          y (hY hy)
  · intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · have hw : S.card ≤ 2 * Q ^ loss * X.card := by
        calc
          S.card ≤ 2 * P.remainder.card := hhalf
          _ ≤ 2 * (Q ^ loss * X.card) := Nat.mul_le_mul_left 2 hwide
          _ = 2 * Q ^ loss * X.card := by ring
      simpa [B] using hw
    · simpa [B] using P.blocks_wide j
  · have hYsubS : Y ⊆ S := hY.trans P.remainder_subset
    have hcardYR : Y.card ≤ P.remainder.card := Finset.card_le_card hY
    have hcardRS : P.remainder.card ≤ S.card :=
      Finset.card_le_card P.remainder_subset
    have hcardSplit : S.card - Y.card =
        (S.card - P.remainder.card) + (P.remainder.card - Y.card) := by
      omega
    rw [hcardSplit, Nat.mul_add]
    calc
      Q * (S.card - P.remainder.card) +
          Q * (P.remainder.card - Y.card)
          ≤ 3 * n * S.card + 3 * P.remainder.card :=
            Nat.add_le_add P.removed_small hremoved
      _ ≤ 3 * n * S.card + 3 * S.card := by
            gcongr
      _ = 3 * (n + 1) * S.card := by ring

end Lax57Proofs
