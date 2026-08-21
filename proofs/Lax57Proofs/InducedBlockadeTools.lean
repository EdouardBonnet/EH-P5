import Lax57.SemisparseBlockade
import Lax57Proofs.InducedMapTools
import Lax57Proofs.Helpers
import Mathlib.Tactic

namespace Lax57Proofs

open Finset
open scoped SimpleGraph
open Lax57.GraphDefinitions

universe u

/-- The semisparse-blockade theorem in a prescribed induced vertex set. -/
theorem semisparse_house_blockade_inside
    (d₀ : ℕ)
    (hsemi : ∀ E : ℕ, 2 ≤ E →
      ∀ {W : Type u} [Fintype W] [DecidableEq W]
        (H : SimpleGraph W) [DecidableRel H.Adj],
        IsHouseFree H → E ^ (10 * d₀ ^ 2) ≤ Fintype.card W →
          ∃ B : Blockade (V := W) E,
            B.IsSemisparse H (E ^ d₀) ∧
              B.HasWidthLoss (E ^ (10 * d₀ ^ 2)))
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (E : ℕ) (hE : 2 ≤ E) (hfree : IsHouseFree G)
    (hsize : E ^ (10 * d₀ ^ 2) ≤ S.card) :
    ∃ B : Blockade (V := V) E,
      B.IsInside S ∧ B.IsSemisparse G (E ^ d₀) ∧
        ∀ i, S.card ≤ E ^ (10 * d₀ ^ 2) * (B.block i).card := by
  classical
  let H := G.induce (S : Set V)
  obtain ⟨B₀, hsemiB, hwidth⟩ := hsemi E hE H
    (IsHouseFree.induce_finset hfree S) (by simpa [H] using hsize)
  let e : {x : V // x ∈ S} ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  let B := mapBlockade e B₀
  refine ⟨B, ?_, ?_, ?_⟩
  · intro i x hx
    change x ∈ (B₀.block i).map e at hx
    obtain ⟨xS, hxB, rfl⟩ := Finset.mem_map.mp hx
    exact xS.property
  · intro i j hij
    rcases hsemiB hij with hcomp | hsparse
    · apply Or.inl
      intro x hx y hy
      change x ∈ (B₀.block i).map e at hx
      change y ∈ (B₀.block j).map e at hy
      obtain ⟨xS, hxB, rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨yS, hyB, rfl⟩ := Finset.mem_map.mp hy
      exact hcomp xS hxB yS hyB
    · exact Or.inr (WeaklyESparse.map_induce G S hsparse)
  · intro i
    simpa [B, H] using hwidth i

end Lax57Proofs
