import Lax57.GraphDefinitions

/-!
---
title: Sparse-house acceleration
type: theorem
---
For some integer $d\geq 2$, a house-free graph that is $1/R^2$-sparse on a
set $S$, where $R\geq 64$, either becomes $1/R^{2d}$-sparse on a subset of
size at least $|S|/R^{32d^3}$, or has a complete or anticomplete $R$-blockade
whose blocks have size at least $|S|/R^{36d^3}$. This is a reciprocal-square
form of Lemma 7.2 of Nguyen, Scott, and Seymour.
-/

namespace Lax57.SparseHouseAcceleration

open Lax57.GraphDefinitions

universe u

/-- The sparse-house acceleration step, in reciprocal-square form. -/
axiom sparse_house_acceleration :
    ∃ d : ℕ, 2 ≤ d ∧
      ∀ R : ℕ, 64 ≤ R →
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V),
          IsHouseFree G → ESparse G (R ^ 2) S →
            (∃ T : Finset V, T ⊆ S ∧
                S.card ≤ R ^ (32 * d ^ 3) * T.card ∧
                  ESparse G (R ^ (2 * d)) T) ∨
              (∃ B : Blockade (V := V) R,
                B.IsInside S ∧ B.IsUniform G ∧
                  ∀ i : Fin R,
                    S.card ≤ R ^ (36 * d ^ 3) * (B.block i).card)

end Lax57.SparseHouseAcceleration
