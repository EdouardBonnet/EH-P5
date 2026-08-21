import Lax57.BlockadeThinning
import Lax57Proofs.BlockadeSelection
import Mathlib.Tactic

namespace Lax57Proofs

open Finset
open scoped BigOperators SimpleGraph
open Lax57.GraphDefinitions

universe u

/-- The high-degree vertices of one sampled sparse pair occupy at most a
`1/(4k)` fraction of the sample. -/
private theorem clean_bad_pair_bound
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k P E t : ℕ} (hk : 0 < k) (hP : 0 < P) (hE : 0 < E) (ht : 0 < t)
    (hreserve : 128 * k ^ 3 * E ≤ P)
    {A B : Finset V} (hAcard : A.card = t)
    (hedges : P * (G.interedges A B).card ≤ 16 * k ^ 2 * t ^ 2) :
    4 * k * (A.filter fun x ↦
      t < 2 * E * (neighborsIn G B x).card).card ≤ t := by
  classical
  let D := A.filter fun x ↦ t < 2 * E * (neighborsIn G B x).card
  by_cases hD : D.Nonempty
  · have hlower : D.card * t <
        ∑ x ∈ D, 2 * E * (neighborsIn G B x).card := by
      calc
        D.card * t = ∑ _x ∈ D, t := by simp
        _ < ∑ x ∈ D, 2 * E * (neighborsIn G B x).card :=
          Finset.sum_lt_sum_of_nonempty hD fun x hx ↦
            (Finset.mem_filter.mp hx).2
    have hsumsub :
        ∑ x ∈ D, (neighborsIn G B x).card ≤
          ∑ x ∈ A, (neighborsIn G B x).card :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun _ _ _ ↦ Nat.zero_le _
    have hdegree :
        ∑ x ∈ D, 2 * E * (neighborsIn G B x).card ≤
          2 * E * (G.interedges A B).card := by
      calc
        (∑ x ∈ D, 2 * E * (neighborsIn G B x).card) =
            2 * E * ∑ x ∈ D, (neighborsIn G B x).card := by
              rw [Finset.mul_sum]
        _ ≤ 2 * E * ∑ x ∈ A, (neighborsIn G B x).card :=
          Nat.mul_le_mul_left _ hsumsub
        _ = 2 * E * (G.interedges A B).card := by
          rw [sum_card_neighborsIn_eq_card_interedges]
    have hbase : P * (D.card * t) < 32 * k ^ 2 * E * t ^ 2 := by
      calc
        P * (D.card * t) < P *
            (∑ x ∈ D, 2 * E * (neighborsIn G B x).card) :=
          Nat.mul_lt_mul_of_pos_left hlower hP
        _ ≤ P * (2 * E * (G.interedges A B).card) :=
          Nat.mul_le_mul_left P hdegree
        _ = 2 * E * (P * (G.interedges A B).card) := by ring
        _ ≤ 2 * E * (16 * k ^ 2 * t ^ 2) :=
          Nat.mul_le_mul_left (2 * E) hedges
        _ = 32 * k ^ 2 * E * t ^ 2 := by ring
    have hcancel : (P * t) * (4 * k * D.card) < (P * t) * t := by
      calc
        (P * t) * (4 * k * D.card) = 4 * k * (P * (D.card * t)) := by ring
        _ < 4 * k * (32 * k ^ 2 * E * t ^ 2) :=
          Nat.mul_lt_mul_of_pos_left hbase (by positivity)
        _ = (128 * k ^ 3 * E) * t ^ 2 := by ring
        _ ≤ P * t ^ 2 := Nat.mul_le_mul_right (t ^ 2) hreserve
        _ = (P * t) * t := by ring
    have : 4 * k * D.card < t := Nat.lt_of_mul_lt_mul_left hcancel
    exact this.le
  · have hDeq : D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hD
    simp [D, hDeq]

/--
---
conclusion: Lax57.BlockadeThinning.semisparse_blockade_thinning
---
Select $t$ vertices from each block in index order. Integer Markov bounds
control all pairs involving earlier samples and later blocks. Delete from
each sample the vertices whose degree to another sample exceeds $t/(2E)$.
The hypothesis $P\geq 128k^3E$ ensures that at least half of every sample
remains, and the surviving noncomplete pairs are $1/E$-sparse in both
directions.
-/
theorem semisparse_blockade_thinning :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj]
      (k P E t : ℕ) (B : Blockade (V := V) k),
      2 ≤ k → 2 * k ≤ t → 128 * k ^ 3 * E ≤ P →
      (∀ i, 2 * t ≤ (B.block i).card) → B.IsSemisparse G P →
        ∃ C : Blockade (V := V) k,
          (∀ i, C.block i ⊆ B.block i) ∧
          (∀ i, t ≤ 2 * (C.block i).card ∧ (C.block i).card ≤ t) ∧
          (∀ {i j}, i ≠ j →
            ((∀ x ∈ C.block i, ∀ y ∈ C.block j, G.Adj x y) ∨
              (ESparseTo G E (C.block i) (C.block j) ∧
               ESparseTo G E (C.block j) (C.block i)))) := by
  intro V _ _ G _ k P E t B hk ht hreserve hblocks hsemi
  classical
  have hkpos : 0 < k := by omega
  have htpos : 0 < t :=
    (Nat.mul_pos (by omega) hkpos).trans_le ht
  by_cases hE0 : E = 0
  · subst E
    have hchoose (i : Fin k) : ∃ A ⊆ B.block i, A.card = t :=
      Finset.exists_subset_card_eq ((show t ≤ 2 * t by omega).trans (hblocks i))
    let A : Fin k → Finset V := fun i ↦ Classical.choose (hchoose i)
    have hAspec (i : Fin k) : A i ⊆ B.block i ∧ (A i).card = t :=
      Classical.choose_spec (hchoose i)
    let C : Blockade (V := V) k :=
      { block := A
        disjoint := fun {i j} hij ↦ (B.disjoint hij).mono (hAspec i).1 (hAspec j).1 }
    refine ⟨C, ?_, ?_, ?_⟩
    · exact fun i ↦ (hAspec i).1
    · intro i
      change t ≤ 2 * (A i).card ∧ (A i).card ≤ t
      rw [(hAspec i).2]
      omega
    · intro i j hij
      rcases hsemi hij with hcomp | hsparse
      · apply Or.inl
        intro x hx y hy
        exact hcomp x ((hAspec i).1 hx) y ((hAspec j).1 hy)
      · apply Or.inr
        constructor <;> intro x hx <;> simp [ESparseTo]
  have hEpos : 0 < E := Nat.pos_of_ne_zero hE0
  have hPpos : 0 < P := by
    have : 0 < 128 * k ^ 3 * E := by positivity
    exact this.trans_le hreserve
  obtain ⟨H⟩ := exists_partial_block_selection G (P := P) B hk ht hblocks
    k (Nat.le_refl k)
  let A : Fin k → Finset V := fun i ↦ H.selected i i.isLt
  have hAsub (i : Fin k) : A i ⊆ B.block i := H.subset i i.isLt
  have hAcard (i : Fin k) : (A i).card = t := H.card_eq i i.isLt
  let bad : Fin k → Fin k → Finset V := fun i j ↦
    if hij : i ≠ j then
      if hsp : WeaklyESparse G P (B.block i) (B.block j) then
        (A i).filter fun x ↦ t < 2 * E * (neighborsIn G (A j) x).card
      else ∅
    else ∅
  have hbad (i j : Fin k) : 4 * k * (bad i j).card ≤ t := by
    dsimp only [bad]
    split_ifs with hij hsp
    · exact clean_bad_pair_bound G hkpos hPpos hEpos htpos hreserve
        (hAcard i) (H.pair_bound i j i.isLt j.isLt hij hsp)
    · simp
    · simp
  let D : Fin k → Finset V := fun i ↦
    (Finset.univ : Finset (Fin k)).biUnion (bad i)
  have hDbound (i : Fin k) : 4 * (D i).card ≤ t := by
    have hall := mul_card_biUnion_le (A i) (bad i) (4 * k)
      (fun j ↦ by simpa [hAcard i] using hbad i j)
    apply Nat.le_of_mul_le_mul_left (c := k) ?_ hkpos
    calc
      k * (4 * (D i).card) = (4 * k) * (D i).card := by ring
      _ ≤ k * t := by simpa [D, hAcard i] using hall
  have hDsub (i : Fin k) : D i ⊆ A i := by
    intro x hx
    obtain ⟨j, _hj, hxj⟩ := Finset.mem_biUnion.mp hx
    dsimp only [bad] at hxj
    split_ifs at hxj <;> simp_all
  let C : Blockade (V := V) k :=
    { block := fun i ↦ A i \ D i
      disjoint := fun {i j} hij ↦
        (B.disjoint hij).mono
          (Finset.sdiff_subset.trans (hAsub i))
          (Finset.sdiff_subset.trans (hAsub j)) }
  have hCcard (i : Fin k) :
      t ≤ 2 * (C.block i).card ∧ (C.block i).card ≤ t := by
    have hcardD : (D i).card ≤ (A i).card := Finset.card_le_card (hDsub i)
    have hcard : (C.block i).card = t - (D i).card := by
      change (A i \ D i).card = _
      rw [Finset.card_sdiff_of_subset (hDsub i), hAcard]
    rw [hcard]
    have hbound := hDbound i
    constructor
    · omega
    · omega
  have hsparseDir {i j : Fin k} (hij : i ≠ j)
      (hsp : WeaklyESparse G P (B.block i) (B.block j)) :
      ESparseTo G E (C.block i) (C.block j) := by
    intro x hxCi
    have hxAi : x ∈ A i := (Finset.mem_sdiff.mp hxCi).1
    have hxnotD : x ∉ D i := (Finset.mem_sdiff.mp hxCi).2
    have hxnotBad : x ∉ bad i j := by
      intro hx
      exact hxnotD (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hx⟩)
    have hdegreeA : 2 * E * (neighborsIn G (A j) x).card ≤ t := by
      dsimp only [bad] at hxnotBad
      simp only [dif_pos hij, dif_pos hsp, Finset.mem_filter, hxAi,
        true_and, not_lt] at hxnotBad
      exact hxnotBad
    have hnsub : neighborsIn G (C.block j) x ⊆ neighborsIn G (A j) x := by
      intro y hy
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_sdiff.mp (Finset.mem_filter.mp hy).1).1,
          (Finset.mem_filter.mp hy).2⟩
    have htwice : 2 * (E * (neighborsIn G (C.block j) x).card) ≤
        2 * (C.block j).card := by
      calc
        2 * (E * (neighborsIn G (C.block j) x).card) =
            2 * E * (neighborsIn G (C.block j) x).card := by ring
        _ ≤ 2 * E * (neighborsIn G (A j) x).card :=
          Nat.mul_le_mul_left _ (Finset.card_le_card hnsub)
        _ ≤ t := hdegreeA
        _ ≤ 2 * (C.block j).card := (hCcard j).1
    omega
  refine ⟨C, ?_, hCcard, ?_⟩
  · intro i
    exact Finset.sdiff_subset.trans (hAsub i)
  · intro i j hij
    rcases hsemi hij with hcomp | hsp
    · apply Or.inl
      intro x hx y hy
      exact hcomp x (hAsub i (Finset.sdiff_subset hx))
        y (hAsub j (Finset.sdiff_subset hy))
    · exact Or.inr ⟨hsparseDir hij hsp,
        hsparseDir (Ne.symm hij) (WeaklyESparse.symm G hsp)⟩

end Lax57Proofs
