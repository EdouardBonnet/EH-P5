import Lax57.GraphDefinitions

/-!
---
title: The sparse-house trichotomy
type: theorem
---
This is a denominator-cleared form of Lemma 7.1 of Nguyen, Scott, and
Seymour. At scale $Q$, a sparse house-free graph either becomes polynomially
sparser on a polynomial fraction of its vertices, contains a long complete
blockade, or admits an anticomplete peel. In the last alternative, the set
$Y$ omits at most a $3/Q$ fraction of the current vertex set.
-/

namespace Lax57.SparseHouseTrichotomy

open Lax57.GraphDefinitions

universe u

/-- Sparse refinement, a complete blockade, or an anticomplete peel. -/
axiom sparse_house_trichotomy :
    ∃ d : ℕ, 40 ≤ d ∧
      ∀ Q : ℕ, 8 ≤ Q →
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V),
          IsHouseFree G → ESparse G Q S →
            ( (∃ T : Finset V, T ⊆ S ∧
                  S.card ≤ Q ^ (30 * d ^ 3) * T.card ∧
                    ESparse G (Q ^ (2 * d)) T) ∨
              (∃ B : Blockade (V := V) Q,
                  B.IsInside S ∧ B.IsComplete G ∧
                    ∀ i : Fin Q,
                      S.card ≤ Q ^ (33 * d ^ 3) * (B.block i).card) ∨
              (∃ X Y : Finset V,
                  X ⊆ S ∧ Y ⊆ S ∧ Disjoint X Y ∧
                    (∀ x ∈ X, ∀ y ∈ Y, ¬ G.Adj x y) ∧
                    S.card ≤ Q ^ (33 * d ^ 3) * X.card ∧
                    Q * (S.card - Y.card) ≤ 3 * S.card) )

end Lax57.SparseHouseTrichotomy
