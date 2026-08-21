import Lax57.GraphDefinitions
import Mathlib.Tactic

namespace Lax57Proofs

open Finset
open Lax57.GraphDefinitions

universe u

/-- A finite set of size at least `k * t` contains `k` pairwise-disjoint
subsets of size exactly `t`. -/
theorem exists_equal_blockade
    {V : Type u} [Fintype V] [DecidableEq V]
    (S : Finset V) (k t : ℕ) (hkt : k * t ≤ S.card) :
    ∃ B : Blockade (V := V) k,
      B.IsInside S ∧ ∀ i : Fin k, (B.block i).card = t := by
  classical
  obtain ⟨f, hf⟩ :=
    Function.Embedding.exists_of_card_le_finset
      (show Fintype.card (Fin k × Fin t) ≤ S.card by simpa using hkt)
  let e : Fin k → Fin t → V := fun i j ↦ f (i, j)
  have he (i : Fin k) : Function.Injective (e i) := by
    intro a b hab
    have hp : (i, a) = (i, b) := f.injective hab
    exact congrArg Prod.snd hp
  let B : Blockade (V := V) k :=
    { block := fun i ↦ (Finset.univ : Finset (Fin t)).map ⟨e i, he i⟩
      disjoint := by
        intro i j hij
        rw [Finset.disjoint_left]
        intro x hxi hxj
        obtain ⟨a, _ha, hax⟩ := Finset.mem_map.mp hxi
        obtain ⟨b, _hb, hbx⟩ := Finset.mem_map.mp hxj
        have hp : (i, a) = (j, b) := f.injective (hax.trans hbx.symm)
        exact hij (congrArg Prod.fst hp) }
  refine ⟨B, ?_, ?_⟩
  · intro i x hx
    change x ∈ (Finset.univ : Finset (Fin t)).map ⟨e i, he i⟩ at hx
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_map.mp hx
    exact hf ⟨(i, j), rfl⟩
  · intro i
    simp [B]

end Lax57Proofs
