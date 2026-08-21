import Lax57.GraphDefinitions

/-!
---
title: Restricted set or uniform blockade in a house-free graph
type: theorem
---
There is an integer $a\geq 1$ such that, for every $E\geq 3$, every finite
house-free graph $G$ has one of two outcomes. Either an induced subgraph on
$X$ is $1/E$-restricted and $|G|\leq E^a|X|$, or $G$ has a complete or
anticomplete blockade of length $k$, where $2\leq k\leq E$, whose blocks all
have size at least $|G|/k^a$.

This is the denominator-cleared form of Lemma 7.3 of Nguyen, Scott, and
Seymour. The structural argument is stated for the house, the complement of
the five-vertex path.
-/

namespace Lax57.HouseDichotomy

open Lax57.GraphDefinitions

universe u

/-- The structural dichotomy for finite house-free graphs. -/
axiom house_dichotomy :
    ∃ a : ℕ, 1 ≤ a ∧
      ∀ E : ℕ, 3 ≤ E →
        ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
          [DecidableRel G.Adj],
          IsHouseFree G →
            (∃ X : Finset V,
                Fintype.card V ≤ E ^ a * X.card ∧ ERestricted G E X) ∨
              HasUniformBlockade G E a

end Lax57.HouseDichotomy
