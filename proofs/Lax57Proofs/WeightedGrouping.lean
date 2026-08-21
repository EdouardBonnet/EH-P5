import Mathlib.Tactic

namespace Lax57Proofs

open Finset
open scoped BigOperators

universe u

/-- A family of pairwise disjoint subfamilies of a finite set, each carrying
at least a prescribed amount of an integer weight. -/
structure WeightedGroups {A : Type u} [DecidableEq A]
    (atoms : Finset A) (weight : A → ℕ) (r n : ℕ) where
  group : Fin n → Finset A
  inside : ∀ i, group i ⊆ atoms
  disjoint : ∀ {i j}, i ≠ j → Disjoint (group i) (group j)
  heavy : ∀ i, r ≤ ∑ a ∈ group i, weight a

/-- A minimal subfamily reaching weight `r` overshoots by at most the
largest individual weight. -/
theorem exists_weighted_chunk
    {A : Type u} [DecidableEq A] (atoms : Finset A) (weight : A → ℕ)
    (r M : ℕ) (hr : 0 < r) (hweight : ∀ a ∈ atoms, weight a ≤ M)
    (htotal : r ≤ ∑ a ∈ atoms, weight a) :
    ∃ X : Finset A, X ⊆ atoms ∧
      r ≤ ∑ a ∈ X, weight a ∧ ∑ a ∈ X, weight a ≤ r + M := by
  classical
  let good := atoms.powerset.filter fun X ↦ r ≤ ∑ a ∈ X, weight a
  have hgood : good.Nonempty := by
    refine ⟨atoms, ?_⟩
    simp [good, htotal]
  obtain ⟨X, hXgood, hmin⟩ :=
    Finset.exists_min_image good Finset.card hgood
  have hXsub : X ⊆ atoms := by
    simpa [good] using (Finset.mem_filter.mp hXgood).1
  have hXlower : r ≤ ∑ a ∈ X, weight a := by
    simpa [good] using (Finset.mem_filter.mp hXgood).2
  have hXnonempty : X.Nonempty := by
    by_contra hne
    have hXempty : X = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst X
    simp at hXlower
    omega
  obtain ⟨a, haX⟩ := hXnonempty
  have hEraseSub : X.erase a ⊆ atoms := (Finset.erase_subset _ _).trans hXsub
  have hEraseSmall : ∑ x ∈ X.erase a, weight x < r := by
    by_contra hnot
    have hEraseLower : r ≤ ∑ x ∈ X.erase a, weight x := Nat.le_of_not_gt hnot
    have hEraseGood : X.erase a ∈ good := by
      simp [good, hEraseSub, hEraseLower]
    have hcards := hmin (X.erase a) hEraseGood
    exact (not_lt_of_ge hcards) (Finset.card_erase_lt_of_mem haX)
  have hsplit := Finset.sum_erase_add X weight haX
  refine ⟨X, hXsub, hXlower, ?_⟩
  have haM : weight a ≤ M := hweight a (hXsub haX)
  omega

/-- Greedy weighted bin-packing: if the total weight pays `r + M` for each
requested bin and no atom weighs more than `M`, there are that many disjoint
bins of weight at least `r`. -/
theorem exists_weighted_groups
    {A : Type u} [DecidableEq A] (atoms : Finset A) (weight : A → ℕ)
    (r M n : ℕ) (hr : 0 < r) (hweight : ∀ a ∈ atoms, weight a ≤ M)
    (hcapacity : n * (r + M) ≤ ∑ a ∈ atoms, weight a) :
    Nonempty (WeightedGroups atoms weight r n) := by
  classical
  induction n generalizing atoms with
  | zero =>
      exact ⟨
        { group := Fin.elim0
          inside := fun i ↦ Fin.elim0 i
          disjoint := fun {i j : Fin 0} _ ↦ Fin.elim0 i
          heavy := fun i ↦ Fin.elim0 i }⟩
  | succ n ih =>
      have hrTotal : r ≤ ∑ a ∈ atoms, weight a := by
        calc
          r ≤ r + M := Nat.le_add_right _ _
          _ ≤ (n + 1) * (r + M) := by
            have hmul := Nat.mul_le_mul_right (r + M) (show 1 ≤ n + 1 by omega)
            simpa [Nat.mul_comm] using hmul
          _ ≤ ∑ a ∈ atoms, weight a := hcapacity
      obtain ⟨X, hXsub, hXheavy, hXupper⟩ :=
        exists_weighted_chunk atoms weight r M hr hweight hrTotal
      let R := atoms \ X
      have hsum : (∑ a ∈ R, weight a) + (∑ a ∈ X, weight a) =
          ∑ a ∈ atoms, weight a := by
        simpa [R] using Finset.sum_sdiff hXsub
      have hcapacityR : n * (r + M) ≤ ∑ a ∈ R, weight a := by
        have hcap := hcapacity
        rw [Nat.add_mul] at hcap
        simp only [one_mul] at hcap
        omega
      have hweightR : ∀ a ∈ R, weight a ≤ M := by
        intro a ha
        exact hweight a ((Finset.mem_sdiff.mp ha).1)
      obtain ⟨H⟩ := ih R hweightR hcapacityR
      let groups : Fin (n + 1) → Finset A := Fin.snoc H.group X
      refine ⟨
        { group := groups
          inside := ?_
          disjoint := ?_
          heavy := ?_ }⟩
      · intro i
        refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · simpa [groups] using hXsub
        · intro a ha
          exact (Finset.mem_sdiff.mp (H.inside j (by simpa [groups] using ha))).1
      · intro i j hij
        revert hij
        refine Fin.lastCases ?_ (fun i' ↦ ?_) i
        · refine Fin.lastCases ?_ (fun j' ↦ ?_) j
          · exact fun h ↦ False.elim (h rfl)
          · intro _
            apply Finset.disjoint_left.mpr
            intro a haX haOld
            have haR : a ∈ R := H.inside j' (by simpa [groups] using haOld)
            exact (Finset.mem_sdiff.mp haR).2 (by simpa [groups] using haX)
        · refine Fin.lastCases ?_ (fun j' ↦ ?_) j
          · intro _
            apply Finset.disjoint_left.mpr
            intro a haOld haX
            have haR : a ∈ R := H.inside i' (by simpa [groups] using haOld)
            exact (Finset.mem_sdiff.mp haR).2 (by simpa [groups] using haX)
          · intro hij'
            simpa [groups] using H.disjoint (by
              intro heq
              apply hij'
              apply Fin.ext
              simpa using congrArg Fin.val heq)
      · intro i
        refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · simpa [groups] using hXheavy
        · simpa [groups] using H.heavy j

end Lax57Proofs
