import Lax57.PreparedHouseBlockade
import Lax57.BlockadeThinning
import Lax57.AnticomponentBlockade
import Lax57Proofs.AnticomponentBlockade
import Lax57Proofs.BlockadeThinning
import Lax57Proofs.InducedBlockadeTools
import Lax57Proofs.PreparedBounds
import Lax57Proofs.SemisparseBlockade
import Mathlib.Tactic

namespace Lax57Proofs

open Finset
open scoped BigOperators SimpleGraph
open Lax57.GraphDefinitions

universe u

/-- Restricting both sides of a very sparse pair and paying the available
quadratic size reserve gives the desired weaker reciprocal parameter. -/
private theorem sparse_restrict_prepared
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {Q L : ℕ} (hQ : 0 < Q)
    {A A' B B' : Finset V}
    (hAA : A' ⊆ A) (hBB : B' ⊆ B)
    (hBsize : B.card ≤ Q ^ 2 * B'.card)
    (hsparse : ESparseTo G (2 * Q ^ 2 * L) A B) :
    ESparseTo G L A' B' := by
  intro x hxA'
  have hnsub : neighborsIn G B' x ⊆ neighborsIn G B x := by
    intro y hy
    exact Finset.mem_filter.mpr
      ⟨hBB (Finset.mem_filter.mp hy).1, (Finset.mem_filter.mp hy).2⟩
  have hbase := hsparse x (hAA hxA')
  have hfactor : 0 < 2 * Q ^ 2 := by positivity
  apply Nat.le_of_mul_le_mul_left (c := 2 * Q ^ 2) ?_ hfactor
  calc
    (2 * Q ^ 2) * (L * (neighborsIn G B' x).card) =
        (2 * Q ^ 2 * L) * (neighborsIn G B' x).card := by ring
    _ ≤ (2 * Q ^ 2 * L) * (neighborsIn G B x).card :=
      Nat.mul_le_mul_left _ (Finset.card_le_card hnsub)
    _ ≤ B.card := hbase
    _ ≤ Q ^ 2 * B'.card := hBsize
    _ ≤ (2 * Q ^ 2) * B'.card := by gcongr <;> omega

/--
---
conclusion: Lax57.PreparedHouseBlockade.prepared_house_blockade
assumptions:
  - Lax54.AveragingLemma.sparse_graph_thinning
  - Lax54.BipartiteCombLemma.bipartite_comb_lemma
  - Lax54.RodlTheorem.rodl_theorem
---
Apply the semisparse-blockade theorem at scale $L=Q^{4d}$ and sample each
block to a common size. Simultaneous cleaning retains at least half of every
sample and makes each noncomplete pair sparse in both directions. In each
cleaned block, either the complement has a large connected component, or its
components yield the required complete $Q$-blockade. Choosing a large
component in every block preserves the relations between blocks.

# Attribution

Claim 7.1.1 of Nguyen, Scott, and Seymour, with reciprocal parameters and
rounding expressed over the natural numbers.
-/
theorem prepared_house_blockade :
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
                    S.card ≤ Q ^ (30 * d ^ 3) * m) ) := by
  obtain ⟨d₀, hd₀, hsemi⟩ :=
    Lax57Proofs.semisparse_house_blockade
  let d := 100 * d₀
  obtain ⟨hd, hbounds⟩ := prepared_exponent_bounds hd₀
  refine ⟨d, hd, ?_⟩
  intro Q hQ V _ _ G _ S hfree hsize
  classical
  let L := Q ^ (4 * d)
  let W := L ^ (10 * d₀ ^ 2)
  obtain ⟨hL2, hWpos, hsmall, hlong, hthin, hQLW, hwidth33, hwidth30⟩ :=
    hbounds Q hQ
  have hQpos : 0 < Q := by omega
  have hWsize : W ≤ S.card := by
    calc
      W ≤ 2 * W := by omega
      _ ≤ 2 * W * (4 * Q ^ 2) :=
        Nat.le_mul_of_pos_right _ (by positivity)
      _ ≤ Q ^ (30 * d ^ 3) := hsmall
      _ ≤ S.card := hsize
  obtain ⟨B₀, hBinside, hBsemi, hBwidth⟩ :=
    semisparse_house_blockade_inside d₀ hsemi G S L hL2 hfree hWsize
  let Z := 2 * W
  have hZpos : 0 < Z := by positivity
  let t := S.card / Z
  have hZt : Z * t ≤ S.card := by
    simpa [t] using Nat.mul_div_le S.card Z
  have hSlt : S.card < Z * (t + 1) := by
    simpa [t] using Nat.lt_mul_div_succ S.card hZpos
  have h2Lt : 2 * L ≤ t := by
    rw [Nat.le_div_iff_mul_le hZpos]
    change 2 * L * Z ≤ S.card
    calc
      2 * L * Z = 2 * W * (2 * L) := by simp [Z]; ring
      _ ≤ Q ^ (30 * d ^ 3) := hlong
      _ ≤ S.card := hsize
  have h4Qt : 4 * Q ^ 2 ≤ t := by
    rw [Nat.le_div_iff_mul_le hZpos]
    change 4 * Q ^ 2 * Z ≤ S.card
    calc
      4 * Q ^ 2 * Z = 2 * W * (4 * Q ^ 2) := by simp [Z]; ring
      _ ≤ Q ^ (30 * d ^ 3) := hsmall
      _ ≤ S.card := hsize
  have hLpos : 0 < L := (by omega : 0 < 2).trans_le hL2
  have htpos : 0 < t :=
    (Nat.mul_pos (by omega) hLpos).trans_le h2Lt
  have htblocks : ∀ i, 2 * t ≤ (B₀.block i).card := by
    intro i
    apply Nat.le_of_mul_le_mul_left (c := W) ?_ hWpos
    calc
      W * (2 * t) = Z * t := by simp [Z]; ring
      _ ≤ S.card := hZt
      _ ≤ W * (B₀.block i).card := by
        convert hBwidth i using 1 <;> simp [W, Nat.mul_comm]
  obtain ⟨C, hCsub, hCcard, hCpairs⟩ :=
    Lax57Proofs.semisparse_blockade_thinning G L (L ^ d₀)
      (2 * Q ^ 2 * L) t B₀ hL2 h2Lt hthin htblocks hBsemi
  have hCinside : C.IsInside S := fun i ↦ (hCsub i).trans (hBinside i)
  by_cases hcomplete : ∃ (i : Fin L) (D : Blockade (V := V) Q),
      D.IsInside (C.block i) ∧ D.IsComplete G ∧
        ∀ j : Fin Q, (C.block i).card ≤ 4 * Q ^ 3 * (D.block j).card
  · obtain ⟨i, D, hDinside, hDcomplete, hDwidth⟩ := hcomplete
    apply Or.inl
    refine ⟨D, ?_, hDcomplete, ?_⟩
    · intro j x hx
      exact hCinside i (hDinside j hx)
    · intro j
      have htdouble : t + 1 ≤ 2 * t := by omega
      have hraw : S.card ≤ 32 * W * Q ^ 3 * (D.block j).card := by
        calc
          S.card ≤ Z * (t + 1) := Nat.le_of_lt hSlt
          _ ≤ Z * (2 * t) := Nat.mul_le_mul_left Z htdouble
          _ ≤ Z * (4 * (C.block i).card) := by
            apply Nat.mul_le_mul_left
            calc
              2 * t ≤ 2 * (2 * (C.block i).card) :=
                Nat.mul_le_mul_left 2 (hCcard i).1
              _ = 4 * (C.block i).card := by ring
          _ ≤ Z * (4 * (4 * Q ^ 3 * (D.block j).card)) := by
            gcongr
            exact hDwidth j
          _ = 32 * W * Q ^ 3 * (D.block j).card := by simp [Z]; ring
      calc
        S.card ≤ 32 * W * Q ^ 3 * (D.block j).card := hraw
        _ ≤ Q ^ (33 * d ^ 3) * (D.block j).card :=
          Nat.mul_le_mul_right _ hwidth33
  · have hlarge : ∀ i : Fin L, ∃ J : Finset V,
        J ⊆ C.block i ∧ (Gᶜ.induce (J : Set V)).Connected ∧
          (C.block i).card ≤ Q ^ 2 * J.card := by
      intro i
      rcases Lax57Proofs.anticomponent_or_complete_blockade
          G (C.block i) Q (by omega) with hJ | hD
      · exact hJ
      · obtain ⟨D, hDinside, hDcomplete, hDwidth⟩ := hD
        exact False.elim (hcomplete ⟨i, D, hDinside, hDcomplete, hDwidth⟩)
    let J : Fin L → Finset V := fun i ↦ Classical.choose (hlarge i)
    have hJspec (i : Fin L) :
        J i ⊆ C.block i ∧ (Gᶜ.induce (J i : Set V)).Connected ∧
          (C.block i).card ≤ Q ^ 2 * (J i).card :=
      Classical.choose_spec (hlarge i)
    let B : Blockade (V := V) L :=
      { block := J
        disjoint := by
          intro i j hij
          exact (C.disjoint hij).mono (hJspec i).1 (hJspec j).1 }
    let m := t / (4 * Q ^ 2)
    have hm : 0 < m := Nat.div_pos h4Qt (by positivity)
    have hmJ (i : Fin L) : m ≤ (J i).card := by
      apply Nat.div_le_of_le_mul
      calc
        t ≤ 2 * (C.block i).card := (hCcard i).1
        _ ≤ 2 * (Q ^ 2 * (J i).card) :=
          Nat.mul_le_mul_left 2 (hJspec i).2.2
        _ = (2 * Q ^ 2) * (J i).card := by ring
        _ ≤ (4 * Q ^ 2) * (J i).card := by
          apply Nat.mul_le_mul_right
          nlinarith
    have htM : t ≤ 8 * Q ^ 2 * m := by
      have hdiv := Nat.lt_mul_div_succ t (by positivity : 0 < 4 * Q ^ 2)
      have hmone : m + 1 ≤ 2 * m := by omega
      calc
        t ≤ 4 * Q ^ 2 * (m + 1) := Nat.le_of_lt (by simpa [m] using hdiv)
        _ ≤ 4 * Q ^ 2 * (2 * m) := Nat.mul_le_mul_left _ hmone
        _ = 8 * Q ^ 2 * m := by ring
    have hJcard (i : Fin L) :
        m ≤ (J i).card ∧ (J i).card ≤ 8 * Q ^ 2 * m := by
      exact ⟨hmJ i,
        (Finset.card_le_card (hJspec i).1).trans (hCcard i).2 |>.trans htM⟩
    have hJpairs : ∀ {i j : Fin L}, i ≠ j →
        ((∀ x ∈ J i, ∀ y ∈ J j, G.Adj x y) ∨
          (ESparseTo G L (J i) (J j) ∧ ESparseTo G L (J j) (J i))) := by
      intro i j hij
      rcases hCpairs hij with hcomp | hsparse
      · apply Or.inl
        intro x hx y hy
        exact hcomp x ((hJspec i).1 hx) y ((hJspec j).1 hy)
      · apply Or.inr
        exact ⟨sparse_restrict_prepared G hQpos
            (hJspec i).1 (hJspec j).1 (hJspec j).2.2 hsparse.1,
          sparse_restrict_prepared G hQpos
            (hJspec j).1 (hJspec i).1 (hJspec i).2.2 hsparse.2⟩
    have hsum : (∑ i, (J i).card) ≤ L * t := by
      calc
        (∑ i, (J i).card) ≤ ∑ _i : Fin L, t := by
          apply Finset.sum_le_sum
          intro i hi
          exact (Finset.card_le_card (hJspec i).1).trans (hCcard i).2
        _ = L * t := by simp
    have htotal : Q * (∑ i, (J i).card) ≤ S.card := by
      calc
        Q * (∑ i, (J i).card) ≤ Q * (L * t) :=
          Nat.mul_le_mul_left Q hsum
        _ = (Q * L) * t := by ring
        _ ≤ W * t := Nat.mul_le_mul_right t hQLW
        _ ≤ Z * t := Nat.mul_le_mul_right t (by simp only [Z]; omega)
        _ ≤ S.card := hZt
    have hfinalWidth : S.card ≤ Q ^ (30 * d ^ 3) * m := by
      have htdouble : t + 1 ≤ 2 * t := by omega
      have hraw : S.card ≤ 32 * W * Q ^ 2 * m := by
        calc
          S.card ≤ Z * (t + 1) := Nat.le_of_lt hSlt
          _ ≤ Z * (2 * t) := Nat.mul_le_mul_left Z htdouble
          _ ≤ Z * (2 * (8 * Q ^ 2 * m)) := by gcongr
          _ = 32 * W * Q ^ 2 * m := by simp [Z]; ring
      calc
        S.card ≤ 32 * W * Q ^ 2 * m := hraw
        _ ≤ Q ^ (30 * d ^ 3) * m :=
          Nat.mul_le_mul_right m hwidth30
    apply Or.inr
    refine ⟨m, B, hm, ?_, ?_, ?_, ?_, ?_, hfinalWidth⟩
    · intro i
      change J i ⊆ S
      exact (hJspec i).1.trans (hCinside i)
    · intro i
      change m ≤ (J i).card ∧ (J i).card ≤ 8 * Q ^ 2 * m
      exact hJcard i
    · intro i
      change (Gᶜ.induce (J i : Set V)).Connected
      exact (hJspec i).2.1
    · intro i j hij
      change _
      exact hJpairs hij
    · change Q * (∑ i, (J i).card) ≤ S.card
      exact htotal

end Lax57Proofs
