import Lax57.GraphDefinitions
import Mathlib.Tactic

namespace Lax57Proofs

open Finset
open Lax57.GraphDefinitions

universe u

/-- Restrict a blockade to an initial segment of its indices. -/
def takeBlockade {V : Type u} [DecidableEq V] {k r : ℕ}
    (B : Blockade (V := V) k) (h : r ≤ k) : Blockade (V := V) r where
  block i := B.block ⟨i, i.isLt.trans_le h⟩
  disjoint := by
    intro i j hij
    apply B.disjoint
    intro heq
    apply hij
    apply Fin.ext
    exact congrArg (fun z : Fin k ↦ z.val) heq

@[simp] theorem Blockade.take_block {V : Type u} [DecidableEq V]
    {k r : ℕ} (B : Blockade (V := V) k) (h : r ≤ k) (i : Fin r) :
    (takeBlockade B h).block i = B.block ⟨i, i.isLt.trans_le h⟩ := rfl

/-- Append one last block to a blockade. -/
def snocBlockade {V : Type u} [DecidableEq V] {k : ℕ}
    (B : Blockade (V := V) k) (X : Finset V)
    (hX : ∀ i : Fin k, Disjoint (B.block i) X) :
    Blockade (V := V) (k + 1) where
  block := Fin.snoc B.block X
  disjoint := by
    intro i j hij
    cases i using Fin.lastCases with
    | last =>
        cases j using Fin.lastCases with
        | last =>
            exfalso
            apply hij
            apply Fin.ext
            simp
        | cast j' => simpa only [Fin.snoc_last, Fin.snoc_castSucc] using (hX j').symm
    | cast i' =>
        cases j using Fin.lastCases with
        | last => simpa only [Fin.snoc_last, Fin.snoc_castSucc] using hX i'
        | cast j' =>
            simpa only [Fin.snoc_castSucc] using B.disjoint (by
              intro heq
              apply hij
              apply Fin.ext
              simpa using congrArg (fun z : Fin k ↦ z.val) heq)

@[simp] theorem Blockade.snoc_castSucc {V : Type u} [DecidableEq V]
    {k : ℕ} (B : Blockade (V := V) k) (X : Finset V)
    (hX : ∀ i : Fin k, Disjoint (B.block i) X) (i : Fin k) :
    (snocBlockade B X hX).block i.castSucc = B.block i := by
  simp [snocBlockade]

@[simp] theorem Blockade.snoc_last {V : Type u} [DecidableEq V]
    {k : ℕ} (B : Blockade (V := V) k) (X : Finset V)
    (hX : ∀ i : Fin k, Disjoint (B.block i) X) :
    (snocBlockade B X hX).block (Fin.last k) = X := by
  simp [snocBlockade]

end Lax57Proofs
