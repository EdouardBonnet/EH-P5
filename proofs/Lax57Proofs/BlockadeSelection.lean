import Lax57Proofs.ThinningTools
import Mathlib.Tactic

namespace Lax57Proofs

open Finset
open scoped BigOperators SimpleGraph
open Lax57.GraphDefinitions

universe u

/-- The invariant used while selecting equal-sized subblocks in index order.
Selected blocks have controlled edge count to every later original block,
and every already selected sparse pair has controlled edge count. -/
structure PartialBlockSelection
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (B : Blockade (V := V) k) (P t n : ℕ) where
  selected : ∀ i : Fin k, i.val < n → Finset V
  subset : ∀ i hi, selected i hi ⊆ B.block i
  card_eq : ∀ i hi, (selected i hi).card = t
  forward : ∀ (i j : Fin k) (hi : i.val < n), i.val < j.val →
    WeaklyESparse G P (B.block i) (B.block j) →
      P * (G.interedges (selected i hi) (B.block j)).card ≤
        4 * k * t * (B.block j).card
  pair_bound : ∀ (i j : Fin k) (hi : i.val < n) (hj : j.val < n), i ≠ j →
    WeaklyESparse G P (B.block i) (B.block j) →
      P * (G.interedges (selected i hi) (selected j hj)).card ≤
        16 * k ^ 2 * t ^ 2

/-- Ordered deterministic selection of equal-sized subblocks. -/
theorem exists_partial_block_selection
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k P t : ℕ} (B : Blockade (V := V) k)
    (hk : 2 ≤ k) (ht : 2 * k ≤ t)
    (hblocks : ∀ i, 2 * t ≤ (B.block i).card) :
    ∀ n, n ≤ k → Nonempty (PartialBlockSelection G B P t n) := by
  classical
  have hkpos : 0 < k := by omega
  have htpos : 0 < t := (Nat.mul_pos (by omega) hkpos).trans_le ht
  intro n hn
  induction n with
  | zero =>
      exact ⟨
        { selected := fun i hi ↦ False.elim (by omega)
          subset := fun i hi ↦ False.elim (by omega)
          card_eq := fun i hi ↦ False.elim (by omega)
          forward := fun i j hi ↦ False.elim (by omega)
          pair_bound := fun i j hi ↦ False.elim (by omega) }⟩
  | succ n ih =>
      have hnlt : n < k := by omega
      have hnle : n ≤ k := by omega
      obtain ⟨H⟩ := ih hnle
      let c : Fin k := ⟨n, hnlt⟩
      let bad : Fin k → Finset V := fun j ↦
        if hsp : WeaklyESparse G P (B.block c) (B.block j) then
          if hj : j.val < n then
            (B.block c).filter fun y ↦
              (4 * k) * (4 * k * t) <
                P * (neighborsIn G (H.selected j hj) y).card
          else if hcj : n < j.val then
            (B.block c).filter fun y ↦
              (4 * k) * (B.block j).card <
                P * (neighborsIn G (B.block j) y).card
          else ∅
        else ∅
      have hbad (j : Fin k) :
          4 * k * (bad j).card ≤ (B.block c).card := by
        dsimp only [bad]
        split_ifs with hsp hj hcj
        · have hforward := H.forward j c hj (by simp [c]; omega)
            (WeaklyESparse.symm G hsp)
          have htotal :
              ∑ y ∈ B.block c,
                  P * (neighborsIn G (H.selected j hj) y).card ≤
                (B.block c).card * (4 * k * t) := by
            calc
              (∑ y ∈ B.block c,
                  P * (neighborsIn G (H.selected j hj) y).card) =
                  P * (G.interedges (B.block c) (H.selected j hj)).card := by
                    rw [← sum_card_neighborsIn_eq_card_interedges,
                      Finset.mul_sum]
              _ = P * (G.interedges (H.selected j hj) (B.block c)).card := by
                congr 1
                exact Rel.card_interedges_comm G.symm _ _
              _ ≤ 4 * k * t * (B.block c).card := hforward
              _ = (B.block c).card * (4 * k * t) := by ring
          exact mul_card_filter_lt_le (B.block c)
            (fun y ↦ P * (neighborsIn G (H.selected j hj) y).card)
            (4 * k) (4 * k * t) (by positivity) htotal
        · have hBjpos : 0 < (B.block j).card := by
            exact (Nat.mul_pos (by omega) htpos).trans_le (hblocks j)
          have htotal :
              ∑ y ∈ B.block c,
                  P * (neighborsIn G (B.block j) y).card ≤
                (B.block c).card * (B.block j).card := by
            calc
              (∑ y ∈ B.block c,
                  P * (neighborsIn G (B.block j) y).card) =
                  P * (G.interedges (B.block c) (B.block j)).card := by
                    rw [← sum_card_neighborsIn_eq_card_interedges,
                      Finset.mul_sum]
              _ ≤ (B.block c).card * (B.block j).card := hsp
          exact mul_card_filter_lt_le (B.block c)
            (fun y ↦ P * (neighborsIn G (B.block j) y).card)
            (4 * k) (B.block j).card hBjpos htotal
        · simp
        · simp
      let D := (Finset.univ : Finset (Fin k)).biUnion bad
      have hDbound : 4 * D.card ≤ (B.block c).card := by
        have hall := mul_card_biUnion_le (B.block c) bad (4 * k) hbad
        apply Nat.le_of_mul_le_mul_left (c := k) ?_ hkpos
        calc
          k * (4 * D.card) = (4 * k) * D.card := by ring
          _ ≤ k * (B.block c).card := by simpa [D] using hall
      have hDsub : D ⊆ B.block c := by
        intro x hx
        obtain ⟨j, _hj, hxj⟩ := Finset.mem_biUnion.mp hx
        dsimp only [bad] at hxj
        split_ifs at hxj <;> simp_all
      let Z := B.block c \ D
      have hZcard : t ≤ Z.card := by
        have hcardD : D.card ≤ (B.block c).card :=
          Finset.card_le_card hDsub
        have hcard : Z.card = (B.block c).card - D.card := by
          simpa [Z] using Finset.card_sdiff_of_subset hDsub
        rw [hcard]
        have hcwide := hblocks c
        omega
      obtain ⟨A, hAZ, hAcard⟩ := Finset.exists_subset_card_eq hZcard
      have hAB : A ⊆ B.block c := hAZ.trans Finset.sdiff_subset
      have hAnot (j : Fin k) : Disjoint A (bad j) := by
        rw [Finset.disjoint_left]
        intro x hxA hxBad
        have hxZ := hAZ hxA
        exact (Finset.mem_sdiff.mp hxZ).2
          (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hxBad⟩)
      have hnewForward (j : Fin k) (hcj : n < j.val)
          (hsp : WeaklyESparse G P (B.block c) (B.block j)) :
          P * (G.interedges A (B.block j)).card ≤
            4 * k * t * (B.block j).card := by
        have hpoint : ∀ x ∈ A,
            P * (neighborsIn G (B.block j) x).card ≤
              (4 * k) * (B.block j).card := by
          intro x hxA
          have hxnot := Finset.disjoint_left.mp (hAnot j) hxA
          dsimp only [bad] at hxnot
          simp only [dif_pos hsp] at hxnot
          have hjnot : ¬j.val < n := by omega
          simp only [dif_neg hjnot, dif_pos hcj, Finset.mem_filter, not_and,
            not_lt] at hxnot
          exact hxnot (hAB hxA)
        calc
          P * (G.interedges A (B.block j)).card =
              ∑ x ∈ A, P * (neighborsIn G (B.block j) x).card := by
                rw [← sum_card_neighborsIn_eq_card_interedges,
                  Finset.mul_sum]
          _ ≤ ∑ _x ∈ A, (4 * k) * (B.block j).card := by
            apply Finset.sum_le_sum
            intro x hx
            exact hpoint x hx
          _ = 4 * k * t * (B.block j).card := by simp [hAcard]; ring
      have hnewPair (j : Fin k) (hj : j.val < n)
          (hsp : WeaklyESparse G P (B.block c) (B.block j)) :
          P * (G.interedges A (H.selected j hj)).card ≤
            16 * k ^ 2 * t ^ 2 := by
        have hpoint : ∀ y ∈ A,
            P * (neighborsIn G (H.selected j hj) y).card ≤
              (4 * k) * (4 * k * t) := by
          intro y hyA
          have hynot := Finset.disjoint_left.mp (hAnot j) hyA
          dsimp only [bad] at hynot
          simp only [dif_pos hsp, dif_pos hj, Finset.mem_filter, not_and,
            not_lt] at hynot
          exact hynot (hAB hyA)
        calc
          P * (G.interedges A (H.selected j hj)).card =
              ∑ y ∈ A, P * (neighborsIn G (H.selected j hj) y).card := by
                rw [← sum_card_neighborsIn_eq_card_interedges,
                  Finset.mul_sum]
          _ ≤ ∑ _y ∈ A, (4 * k) * (4 * k * t) := by
            apply Finset.sum_le_sum
            intro y hy
            exact hpoint y hy
          _ = 16 * k ^ 2 * t ^ 2 := by simp [hAcard]; ring
      let selected' : ∀ i : Fin k, i.val < n + 1 → Finset V := fun i hi ↦
        if hiOld : i.val < n then H.selected i hiOld else A
      refine ⟨
        { selected := selected'
          subset := ?_
          card_eq := ?_
          forward := ?_
          pair_bound := ?_ }⟩
      · intro i hi
        dsimp only [selected']
        split_ifs with hiOld
        · exact H.subset i hiOld
        · have hic : i = c := Fin.ext (by simp [c]; omega)
          subst i
          exact hAB
      · intro i hi
        dsimp only [selected']
        split_ifs with hiOld
        · exact H.card_eq i hiOld
        · exact hAcard
      · intro i j hi hij hsp
        dsimp only [selected']
        split_ifs with hiOld
        · exact H.forward i j hiOld hij hsp
        · have hic : i = c := Fin.ext (by simp [c]; omega)
          subst i
          exact hnewForward j (by simpa [c] using hij) hsp
      · intro i j hi hj hij hsp
        by_cases hiOld : i.val < n
        · by_cases hjOld : j.val < n
          · simp only [selected', dif_pos hiOld, dif_pos hjOld]
            exact H.pair_bound i j hiOld hjOld hij hsp
          · simp only [selected', dif_pos hiOld, dif_neg hjOld]
            have hjc : j = c := Fin.ext (by simp [c]; omega)
            subst j
            have hb := hnewPair i hiOld (WeaklyESparse.symm G hsp)
            calc
              P * (G.interedges (H.selected i hiOld) A).card =
                  P * (G.interedges A (H.selected i hiOld)).card := by
                    congr 1
                    exact Rel.card_interedges_comm G.symm _ _
              _ ≤ 16 * k ^ 2 * t ^ 2 := hb
        · by_cases hjOld : j.val < n
          · simp only [selected', dif_neg hiOld, dif_pos hjOld]
            have hic : i = c := Fin.ext (by simp [c]; omega)
            subst i
            exact hnewPair j hjOld hsp
          · have hic : i = c := Fin.ext (by simp [c]; omega)
            have hjc : j = c := Fin.ext (by simp [c]; omega)
            exact False.elim (hij (hic.trans hjc.symm))

end Lax57Proofs
