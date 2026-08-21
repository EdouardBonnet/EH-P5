import Lax57.SparseHouseTrichotomy
import Lax57.PreparedHouseBlockade
import Lax57Proofs.PreparedBlockadeTools
import Mathlib.Tactic

namespace Lax57Proofs

open Finset
open scoped BigOperators SimpleGraph
open Lax57.GraphDefinitions

universe u

/--
---
conclusion: Lax57.SparseHouseTrichotomy.sparse_house_trichotomy
assumptions:
  - Lax57.PreparedHouseBlockade.prepared_house_blockade
---
Use the prepared blockade from Claim 7.1.1. A vertex mixed on at least a
$1/Q$ fraction of the blocks cannot meet a complete pair among them, because
anticonnectivity would supply four vertices that, together with it, induce a
house. Their union gives the sparser outcome. Otherwise, double-counting
mixed incidences finds a block with few mixed outside vertices. The original
sparsity bound and the size of the prepared blockade leave a large set
anticomplete to that block, giving the peel outcome.

# Attribution

Lemma 7.1 of Nguyen, Scott, and Seymour, including the house construction
shown in their Figure 2.
-/
theorem sparse_house_trichotomy :
    ∃ d : ℕ, 40 ≤ d ∧
      ∀ Q : ℕ, 8 ≤ Q →
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V),
          IsHouseFree G → ESparse G Q S →
            ( (∃ T : Finset V, T ⊆ S ∧
                  S.card ≤ Q ^ (30 * d ^ 3) * T.card ∧
                    ESparse G (Q ^ (2 * d)) T) ∨
              (∃ B : Blockade (V := V) Q,
                  B.IsInside S ∧ B.IsComplete G ∧
                    ∀ i : Fin Q,
                      S.card ≤ Q ^ (33 * d ^ 3) * (B.block i).card) ∨
              (∃ X Y : Finset V,
                  X ⊆ S ∧ Y ⊆ S ∧ Disjoint X Y ∧
                    (∀ x ∈ X, ∀ y ∈ Y, ¬ G.Adj x y) ∧
                    S.card ≤ Q ^ (33 * d ^ 3) * X.card ∧
                    Q * (S.card - Y.card) ≤ 3 * S.card) ) := by
  obtain ⟨d, hd, hprepare⟩ :=
    Lax57.PreparedHouseBlockade.prepared_house_blockade
  refine ⟨d, hd, ?_⟩
  intro Q hQ V _ _ G _ S hfree hsparse
  classical
  have hQpos : 0 < Q := by omega
  by_cases hsize : Q ^ (30 * d ^ 3) ≤ S.card
  swap
  · apply Or.inl
    by_cases hS : S.Nonempty
    · obtain ⟨v, hvS⟩ := hS
      refine ⟨{v}, by simpa using hvS, ?_, ESparse.singleton G _ v⟩
      simpa using Nat.le_of_lt (Nat.lt_of_not_ge hsize)
    · have hSem : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      subst S
      refine ⟨∅, Finset.Subset.rfl, by simp, ?_⟩
      intro v
      haveI : Subsingleton {x : V // x ∈ (∅ : Finset V)} := by infer_instance
      simp [SimpleGraph.degree_eq_zero_of_subsingleton]
  rcases hprepare Q hQ G S hfree hsize with hcomplete | hprepared
  · exact Or.inr (Or.inl hcomplete)
  obtain ⟨m, B, hm, hinside, hcard, hantiConn, hpairs, htotal, hwidth⟩ :=
    hprepared
  let L := Q ^ (4 * d)
  let U := blockUnion B (Finset.univ : Finset (Fin L))
  let O := S \ U
  have hLpos : 0 < L := by positivity
  have hUS : U ⊆ S := blockUnion_subset B _ hinside
  have hUcard : U.card = ∑ i, (B.block i).card := by
    change (blockUnion B (Finset.univ : Finset (Fin L))).card = _
    rw [blockUnion, Finset.card_biUnion]
    intro i hi j hj hij
    exact B.disjoint hij
  have hUtotal : Q * U.card ≤ S.card := by simpa [hUcard] using htotal
  by_cases hheavy : ∃ v ∈ O, L ≤ Q * (mixedIndices G B v).card
  · obtain ⟨v, hvO, hvheavy⟩ := hheavy
    let I := mixedIndices G B v
    let T := blockUnion B I
    have hvnot (i : Fin L) : v ∉ B.block i := by
      intro hvBi
      exact (Finset.mem_sdiff.mp hvO).2
        (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hvBi⟩)
    have hmixed {i : Fin L} (hi : i ∈ I) : IsMixedOn G v (B.block i) := by
      simpa [I, mixedIndices] using (Finset.mem_filter.mp hi).2
    have hsparsePairs : ∀ {i j : Fin L}, i ∈ I → j ∈ I → i ≠ j →
        ESparseTo G (Q ^ (4 * d)) (B.block i) (B.block j) := by
      intro i j hi hj hij
      rcases hpairs hij with hcomp | hs
      · exfalso
        apply hfree
        exact house_of_mixed_complete_blocks G (hvnot i) (hvnot j) hcomp
          (hantiConn i) (hantiConn j) (hmixed hi) (hmixed hj)
      · exact hs.1
    have hIpos : 0 < I.card := by
      by_contra hz
      have : I.card = 0 := by omega
      rw [this, Nat.mul_zero] at hvheavy
      omega
    have hTlower : I.card * m ≤ T.card :=
      mul_le_card_blockUnion B I fun i ↦ (hcard i).1
    apply Or.inl
    refine ⟨T, blockUnion_subset B I hinside, ?_, ?_⟩
    · calc
        S.card ≤ Q ^ (30 * d ^ 3) * m := hwidth
        _ ≤ Q ^ (30 * d ^ 3) * T.card := by
          apply Nat.mul_le_mul_left
          exact (Nat.le_mul_of_pos_left m hIpos).trans hTlower
    · exact ESparse_blockUnion_of_heavy_sparse_range G hQ (by omega) hcard I
        (by simpa [L, I] using hvheavy) hsparsePairs
  · have hrow : ∀ v ∈ O,
        Q * ((Finset.univ : Finset (Fin L)).filter fun i ↦
          IsMixedOn G v (B.block i)).card ≤ L := by
      intro v hv
      have hvnot : ¬ L ≤ Q * (mixedIndices G B v).card := by
        intro hh
        exact hheavy ⟨v, hv, hh⟩
      have := Nat.le_of_lt (Nat.lt_of_not_ge hvnot)
      simpa [mixedIndices, L] using this
    obtain ⟨i, himixed⟩ := exists_column_with_small_fiber O
      (fun i v ↦ IsMixedOn G v (B.block i)) hLpos
      (Finset.card_le_card (Finset.sdiff_subset)) hrow
    let X := B.block i
    let M := O.filter fun v ↦ IsMixedOn G v X
    let C := O.filter fun v ↦ ∀ x ∈ X, G.Adj v x
    let Y := O.filter fun v ↦ ∀ x ∈ X, ¬ G.Adj v x
    have hMbound : Q * M.card ≤ S.card := by simpa [M, X] using himixed
    have hXlower : m ≤ X.card := (hcard i).1
    have hXnonempty : X.Nonempty := Finset.card_pos.mp (hm.trans_le hXlower)
    obtain ⟨x₀, hx₀X⟩ := hXnonempty
    have hx₀S : x₀ ∈ S := hinside i hx₀X
    let xS : {x : V // x ∈ S} := ⟨x₀, hx₀S⟩
    have hCsubN : C ⊆ neighborsIn G S x₀ := by
      intro v hvC
      have hc := Finset.mem_filter.mp hvC
      exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hc.1).1,
        G.adj_comm _ _ |>.mp (hc.2 x₀ hx₀X)⟩
    have hCbound : Q * C.card ≤ S.card := by
      calc
        Q * C.card ≤ Q * (neighborsIn G S x₀).card :=
          Nat.mul_le_mul_left Q (Finset.card_le_card hCsubN)
        _ = Q * (G.induce (S : Set V)).degree xS := by
          change Q * (neighborsIn G S xS.1).card = _
          rw [card_neighborsIn_eq_degree G S xS]
        _ ≤ S.card := hsparse xS
    have hcover : O ⊆ M ∪ C ∪ Y := by
      intro v hvO
      by_cases hmix : IsMixedOn G v X
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hvO, hmix⟩))
      · by_cases hall : ∀ x ∈ X, G.Adj v x
        · exact Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨hvO, hall⟩))
        · apply Finset.mem_union_right
          apply Finset.mem_filter.mpr
          refine ⟨hvO, ?_⟩
          intro x hxX hvx
          apply hall
          intro y hyX
          by_contra hvy
          exact hmix ⟨⟨x, hxX, hvx⟩, ⟨y, hyX, hvy⟩⟩
    have hYsubO : Y ⊆ O := Finset.filter_subset _ _
    have hYsubS : Y ⊆ S := hYsubO.trans Finset.sdiff_subset
    have hdiffsub : S \ Y ⊆ U ∪ M ∪ C := by
      intro v hv
      have hvS := (Finset.mem_sdiff.mp hv).1
      have hvnotY := (Finset.mem_sdiff.mp hv).2
      by_cases hvU : v ∈ U
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hvU)
      · have hvO : v ∈ O := Finset.mem_sdiff.mpr ⟨hvS, hvU⟩
        rcases Finset.mem_union.mp (hcover hvO) with hvMC | hvY
        · rcases Finset.mem_union.mp hvMC with hvM | hvC
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ hvM)
          · exact Finset.mem_union_right _ hvC
        · exact False.elim (hvnotY hvY)
    have hremoved : Q * (S.card - Y.card) ≤ 3 * S.card := by
      have hdiffcard : S.card - Y.card = (S \ Y).card := by
        exact (Finset.card_sdiff_of_subset hYsubS).symm
      rw [hdiffcard]
      calc
        Q * (S \ Y).card ≤ Q * (U ∪ M ∪ C).card :=
          Nat.mul_le_mul_left Q (Finset.card_le_card hdiffsub)
        _ ≤ Q * (U.card + M.card + C.card) :=
          Nat.mul_le_mul_left Q (by
            calc
              (U ∪ M ∪ C).card ≤ (U ∪ M).card + C.card :=
                Finset.card_union_le _ _
              _ ≤ (U.card + M.card) + C.card :=
                Nat.add_le_add_right (Finset.card_union_le _ _) C.card
              _ = U.card + M.card + C.card := rfl)
        _ = Q * U.card + Q * M.card + Q * C.card := by ring
        _ ≤ S.card + S.card + S.card := by
          exact Nat.add_le_add (Nat.add_le_add hUtotal hMbound) hCbound
        _ = 3 * S.card := by ring
    apply Or.inr
    apply Or.inr
    refine ⟨X, Y, hinside i, hYsubS, ?_, ?_, ?_, hremoved⟩
    · apply Finset.disjoint_left.mpr
      intro x hxX hxY
      have hxO := hYsubO hxY
      exact (Finset.mem_sdiff.mp hxO).2
        (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hxX⟩)
    · intro x hxX y hyY hxy
      exact (Finset.mem_filter.mp hyY).2 x hxX (G.adj_comm _ _ |>.mp hxy)
    · have hpow : Q ^ (30 * d ^ 3) ≤ Q ^ (33 * d ^ 3) :=
        Nat.pow_le_pow_right hQpos (by omega)
      calc
        S.card ≤ Q ^ (30 * d ^ 3) * m := hwidth
        _ ≤ Q ^ (33 * d ^ 3) * m := Nat.mul_le_mul_right m hpow
        _ ≤ Q ^ (33 * d ^ 3) * X.card :=
          Nat.mul_le_mul_left _ hXlower

end Lax57Proofs
