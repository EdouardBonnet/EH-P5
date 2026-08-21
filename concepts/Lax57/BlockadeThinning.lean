import Lax57.GraphDefinitions

/-!
---
title: Simultaneous thinning of a semisparse blockade
type: theorem
---
This finite greedy lemma is the sampling-and-cleaning step in Claim 7.1.1.
Subblocks are selected in order so that every weakly sparse pair has a
controlled edge count. Removing vertices of excessive cross-degree then
gives vertexwise sparsity in both directions while retaining at least half
of each sample.
-/

namespace Lax57.BlockadeThinning

open Lax57.GraphDefinitions

universe u

/-- Thin every block simultaneously and convert weak pair density to
vertexwise sparsity. -/
axiom semisparse_blockade_thinning :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj]
      (k P E t : ℕ) (B : Blockade (V := V) k),
      2 ≤ k → 2 * k ≤ t → 128 * k ^ 3 * E ≤ P →
      (∀ i, 2 * t ≤ (B.block i).card) → B.IsSemisparse G P →
        ∃ C : Blockade (V := V) k,
          (∀ i, C.block i ⊆ B.block i) ∧
          (∀ i, t ≤ 2 * (C.block i).card ∧ (C.block i).card ≤ t) ∧
          (∀ {i j}, i ≠ j →
            ((∀ x ∈ C.block i, ∀ y ∈ C.block j, G.Adj x y) ∨
              (ESparseTo G E (C.block i) (C.block j) ∧
               ESparseTo G E (C.block j) (C.block i))))

end Lax57.BlockadeThinning
