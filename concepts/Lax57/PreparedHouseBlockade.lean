import Lax57.GraphDefinitions

/-!
---
title: Prepared sparse-or-complete house blockades
type: theorem
---
This is the denominator-cleared preparation carried out in Claim 7.1.1 of
Nguyen, Scott, and Seymour. Starting from the semisparse blockade of Lemma 6.2,
one samples equal-sized subblocks, removes high cross-degree vertices, and
takes large anticonnected components. Failure to find such a component
already gives the complete-blockade alternative.
-/

namespace Lax57.PreparedHouseBlockade

open Finset
open scoped SimpleGraph
open Lax57.GraphDefinitions

universe u

/-- A very long equal-width blockade whose noncomplete pairs are sparse in
both vertexwise directions, or the desired complete blockade already. -/
axiom prepared_house_blockade :
    ∃ d : ℕ, 40 ≤ d ∧
      ∀ Q : ℕ, 8 ≤ Q →
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V),
          IsHouseFree G → Q ^ (30 * d ^ 3) ≤ S.card →
            ( (∃ C : Blockade (V := V) Q,
                  C.IsInside S ∧ C.IsComplete G ∧
                    ∀ i : Fin Q,
                      S.card ≤ Q ^ (33 * d ^ 3) * (C.block i).card) ∨
              (∃ (m : ℕ) (B : Blockade (V := V) (Q ^ (4 * d))),
                  0 < m ∧ B.IsInside S ∧
                    (∀ i, m ≤ (B.block i).card ∧
                      (B.block i).card ≤ 8 * Q ^ 2 * m) ∧
                    (∀ i, (Gᶜ.induce (B.block i : Set V)).Connected) ∧
                    (∀ {i j}, i ≠ j →
                      ((∀ x ∈ B.block i, ∀ y ∈ B.block j, G.Adj x y) ∨
                        (ESparseTo G (Q ^ (4 * d)) (B.block i) (B.block j) ∧
                         ESparseTo G (Q ^ (4 * d)) (B.block j) (B.block i)))) ∧
                    Q * (∑ i, (B.block i).card) ≤ S.card ∧
                    S.card ≤ Q ^ (30 * d ^ 3) * m) )

end Lax57.PreparedHouseBlockade
