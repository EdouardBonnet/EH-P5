import Lax57.GraphDefinitions

/-!
---
title: Erdős–Hajnal theorem for the five-vertex path
type: theorem
---
The five-vertex path $P_5$ has the Erdős–Hajnal property: there is a positive
integer $q$ such that every finite graph $G$ with no induced copy of $P_5$
satisfies

$$
|V(G)| \leq \max\{\alpha(G),\omega(G)\}^{q}.
$$
-/

namespace Lax57.ErdosHajnalP5

open Lax57.GraphDefinitions

universe u

/-- The Erdős–Hajnal conjecture for the five-vertex path. -/
axiom erdos_hajnal_P5 :
    ∃ q : ℕ, 0 < q ∧
      ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
        IsP5Free G → Fintype.card V ≤ homogeneousNumber G ^ q

end Lax57.ErdosHajnalP5
