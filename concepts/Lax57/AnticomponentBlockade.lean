import Lax57.GraphDefinitions

/-!
---
title: Anticomponent or complete blockade
type: theorem
---
This denominator-cleared form of Lemma 4.1 groups the connected components
of the complement. Either one anticonnected component has size at least
$|T|/Q^2$, or there are $Q$ pairwise complete groups, each of size at least
$|T|/(4Q^3)$.
-/

namespace Lax57.AnticomponentBlockade

open Lax57.GraphDefinitions

universe u

/-- A large anticonnected component or a long complete blockade. -/
axiom anticomponent_or_complete_blockade :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) (Q : ℕ),
      2 ≤ Q →
        ( (∃ J : Finset V, J ⊆ T ∧
              (Gᶜ.induce (J : Set V)).Connected ∧
                T.card ≤ Q ^ 2 * J.card) ∨
          (∃ C : Blockade (V := V) Q,
              C.IsInside T ∧ C.IsComplete G ∧
                ∀ i : Fin Q,
                  T.card ≤ 4 * Q ^ 3 * (C.block i).card) )

end Lax57.AnticomponentBlockade
