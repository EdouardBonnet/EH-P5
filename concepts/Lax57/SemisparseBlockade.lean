import Lax57.GraphDefinitions

/-!
---
title: Polynomial semisparse blockades for the house
type: theorem
---
This is the denominator-cleared form of Lemma 6.2 of Nguyen, Scott, and
Seymour. A sufficiently large house-free graph contains $E$ disjoint
polynomially large blocks, and every pair of blocks is either complete or
has edge density at most $E^{-d}$.
-/

namespace Lax57.SemisparseBlockade

open Lax57.GraphDefinitions

universe u

/-- Polynomial semisparse blockades in house-free graphs. -/
axiom semisparse_house_blockade :
    ∃ d : ℕ, 40 ≤ d ∧
      ∀ E : ℕ, 2 ≤ E →
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) [DecidableRel G.Adj],
          IsHouseFree G → E ^ (10 * d ^ 2) ≤ Fintype.card V →
            ∃ B : Blockade (V := V) E,
              B.IsSemisparse G (E ^ d) ∧
                B.HasWidthLoss (E ^ (10 * d ^ 2))

end Lax57.SemisparseBlockade
