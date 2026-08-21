import Lax57.GraphDefinitions

/-!
---
title: Anticomplete pairs in sparse $P_5$-free graphs
type: theorem
---
A $1/32$-sparse $P_5$-free graph on a set $S$ of at least two vertices
has two anticomplete sets, each of size at least $|S|/32$. This is Lemma 4.4
of Nguyen, Scott, and Seymour.
-/

namespace Lax57.SparseHouseTools

open Lax57.GraphDefinitions

universe u

/-- The linear anticomplete-pair lemma for sparse `P5`-free graphs. -/
axiom sparse_P5_anticomplete_pair :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V),
      IsP5Free G → 2 ≤ S.card → ESparse G 32 S →
        ∃ B : Blockade (V := V) 2,
          B.IsInside S ∧ B.IsAnticomplete G ∧
            ∀ i : Fin 2, S.card ≤ 32 * (B.block i).card

end Lax57.SparseHouseTools
