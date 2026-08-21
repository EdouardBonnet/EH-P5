import Lax54Proofs.MaximumDegreeReduction
import Lax57Proofs.CombIteration
import Lax57Proofs.EqualBlockade
import Lax57Proofs.InducedMapTools
import Lax57Proofs.SparseP5Pair
import Mathlib.Tactic

set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

namespace Lax57Proofs

open Finset
open scoped SimpleGraph
open Lax57.GraphDefinitions

universe u

/-- The polynomial local input used to amplify a blockade: its length is
between two and `X²`, and it is pure or directed `1/X`-sparse. -/
def HasPolynomialLocalBlockade
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X d : ℕ) : Prop :=
  ∃ (k : ℕ) (B : Blockade (V := V) k),
    2 ≤ k ∧ k ≤ X ^ 2 ∧ (B.IsPure G ∨ B.IsESparse G X) ∧
      ∀ i : Fin k, Fintype.card V ≤ k ^ d * (B.block i).card

private theorem nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      by_cases hn : n = 0
      · subst n
        norm_num
      · have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
        omega

private theorem housefree_compl_p5free
    {V : Type u} {G : SimpleGraph V} (hfree : IsHouseFree G) :
    IsP5Free Gᶜ := by
  intro hp5
  apply hfree
  simpa [House] using hp5.compl

private theorem anticomplete_compl_is_complete
    {V : Type u} [DecidableEq V] {G : SimpleGraph V} {k : ℕ}
    {B : Blockade (V := V) k} (hanti : B.IsAnticomplete Gᶜ) :
    B.IsComplete G := by
  intro i j hij x hx y hy
  by_contra hxy
  apply hanti hij x hx y hy
  rw [SimpleGraph.compl_adj]
  refine ⟨?_, hxy⟩
  intro heq
  subst y
  exact Finset.disjoint_left.mp (B.disjoint hij) hx hy

private theorem card_neighbors_induce
    {V : Type u} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (v : {x : V // x ∈ S}) :
    (neighborsIn G S v.1).card = (G.induce (S : Set V)).degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← Finset.card_map
      (f := Function.Embedding.subtype (fun x ↦ x ∈ S))]
  congr 1
  ext y
  simp [neighborsIn, G.adj_comm, and_comm]

/-- A sufficiently fine sparse set can be cut into many equal blocks; the
large reserve in the degree parameter makes every forward pair sparse. -/
private theorem equal_sparse_blockade
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (R X : ℕ) (hR : 256 ≤ R) (hXR : X < R ^ 2)
    (hsize : R ^ 100 ≤ S.card)
    (hsparse : ESparse G (2 * R ^ 24) S) :
    ∃ B : Blockade (V := V) R,
      B.IsInside S ∧ B.IsESparse G X ∧
        ∀ i : Fin R, S.card ≤ 4 * R * (B.block i).card := by
  classical
  have hRpos : 0 < R := by omega
  let t := S.card / (2 * R)
  have h2Rpos : 0 < 2 * R := by positivity
  have h2Rpow : 2 * R ≤ R ^ 100 := by
    calc
      2 * R ≤ R * R := by nlinarith
      _ = R ^ 2 := by ring
      _ ≤ R ^ 100 := Nat.pow_le_pow_right hRpos (by omega)
  have htpos : 0 < t := by
    exact Nat.div_pos (h2Rpow.trans hsize) h2Rpos
  have hcap : R * t ≤ S.card := by
    have := Nat.mul_div_le S.card (2 * R)
    calc
      R * t ≤ (2 * R) * t := by gcongr <;> omega
      _ ≤ S.card := by simpa [t] using this
  obtain ⟨B, hinside, hcard⟩ := exists_equal_blockade S R t hcap
  have hupper : S.card < (2 * R) * (t + 1) := by
    simpa [t] using Nat.lt_mul_div_succ S.card h2Rpos
  have hwidth : ∀ i : Fin R, S.card ≤ 4 * R * (B.block i).card := by
    intro i
    rw [hcard i]
    have ht : t + 1 ≤ 2 * t := by omega
    calc
      S.card ≤ (2 * R) * (t + 1) := hupper.le
      _ ≤ (2 * R) * (2 * t) := Nat.mul_le_mul_left _ ht
      _ = 4 * R * t := by ring
  refine ⟨B, hinside, ?_, hwidth⟩
  intro i j hij
  intro v hv
  let vS : {x : V // x ∈ S} := ⟨v, hinside j hv⟩
  have hnsub : neighborsIn G (B.block i) v ⊆ neighborsIn G S v := by
    intro z hz
    exact Finset.mem_filter.mpr
      ⟨hinside i (Finset.mem_filter.mp hz).1, (Finset.mem_filter.mp hz).2⟩
  have hneighbors : (neighborsIn G (B.block i) v).card ≤
      (G.induce (S : Set V)).degree vS := by
    rw [← card_neighbors_induce G S vS]
    exact Finset.card_le_card hnsub
  have hcoeff : 2 * R * X ≤ 2 * R ^ 24 := by
    calc
      2 * R * X ≤ 2 * R * (R ^ 2) :=
        Nat.mul_le_mul_left (2 * R) hXR.le
      _ = 2 * R ^ 3 := by ring
      _ ≤ 2 * R ^ 24 :=
        Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right hRpos (by omega))
  have hmul : (2 * R) *
      (X * (neighborsIn G (B.block i) v).card) ≤ S.card := by
    calc
      (2 * R) * (X * (neighborsIn G (B.block i) v).card) =
          (2 * R * X) * (neighborsIn G (B.block i) v).card := by ring
      _ ≤ (2 * R ^ 24) * (G.induce (S : Set V)).degree vS :=
        Nat.mul_le_mul hcoeff hneighbors
      _ ≤ S.card := hsparse vS
  rw [hcard i]
  have hlt : (2 * R) *
      (X * (neighborsIn G (B.block i) v).card) <
        (2 * R) * (t + 1) := hmul.trans_lt hupper
  exact Nat.le_of_lt_succ (Nat.lt_of_mul_lt_mul_left hlt)

/-- The sparse-comb iteration plus a single fixed-parameter application of
Rödl's theorem supplies the polynomial local blockade input at every scale. -/
theorem polynomial_local_blockade :
    ∃ d₀ : ℕ, 200 ≤ d₀ ∧
      ∀ X : ℕ, 256 ≤ X →
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) [DecidableRel G.Adj],
          IsHouseFree G → X ^ d₀ ≤ Fintype.card V →
            HasPolynomialLocalBlockade G X d₀ := by
  let R₀ := 256
  let P₀ := 2 * R₀ ^ 12
  obtain ⟨D, hD, hreduce⟩ :=
    Lax54Proofs.maximum_degree_reduction House P₀ (by positivity)
  let d₀ := 200 + 20 * D
  refine ⟨d₀, by simp [d₀], ?_⟩
  intro X hX V _ _ G _ hfree hglobal
  classical
  let n := Fintype.card V
  have hXpos : 0 < X := by omega
  have hDpow (A : ℕ) (hA : 2 ≤ A) : D ≤ A ^ D := by
    exact (nat_le_two_pow D).trans (Nat.pow_le_pow_left hA D)
  have hdlarge : D + 106 ≤ d₀ := by simp [d₀]; omega
  have hdsize : D + 102 ≤ d₀ := by simp [d₀]; omega
  let Outcome : Prop := HasPolynomialLocalBlockade G X d₀
  have sparse_start (S : Finset V)
      (hstart : n ≤ D * R₀ * S.card)
      (hs : ESparse G (2 * R₀ ^ 12) S) : Outcome := by
    let P : ℕ → Prop := fun q ↦
      ∀ (R : ℕ) (T : Finset V), X - R = q → 256 ≤ R → R ≤ X →
        n ≤ D * R * T.card → ESparse G (2 * R ^ 12) T → Outcome
    have hP : ∀ q : ℕ, P q := by
      intro q
      induction q using Nat.strong_induction_on with
      | h q ih =>
          intro R T hq hR hRX hambient hsparseT
          have hcoef : D * R ≤ X ^ (D + 1) := by
            calc
              D * R ≤ X ^ D * X := Nat.mul_le_mul (hDpow X (by omega)) hRX
              _ = X ^ (D + 1) := by rw [pow_succ]
          have hpowGlobal : X ^ (D + 102) ≤ n := by
            exact (Nat.pow_le_pow_right hXpos hdsize).trans (by simpa [n] using hglobal)
          have hTlarge : X ^ 101 ≤ T.card := by
            apply Nat.le_of_mul_le_mul_left (c := X ^ (D + 1))
              (hc := pow_pos hXpos _)
            calc
              X ^ (D + 1) * X ^ 101 = X ^ (D + 102) := by
                rw [← pow_add]
              _ ≤ n := hpowGlobal
              _ ≤ D * R * T.card := hambient
              _ ≤ X ^ (D + 1) * T.card := Nat.mul_le_mul_right _ hcoef
          have hcombSize : 2 * R ^ 100 ≤ T.card := by
            calc
              2 * R ^ 100 ≤ X * X ^ 100 :=
                Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hRX 100)
              _ = X ^ 101 := by rw [pow_succ]; ring
              _ ≤ T.card := hTlarge
          let H := G.induce (T : Set V)
          have hfreeH : IsHouseFree H := IsHouseFree.induce_finset hfree T
          have hsparseH : ∀ v : {x : V // x ∈ T},
              2 * R ^ 12 * H.degree v ≤ Fintype.card {x : V // x ∈ T} := by
            intro v
            simpa [H] using hsparseT v
          rcases iterate_sparse_comb H R X hR hRX (by simpa [H] using hcombSize)
              hfreeH hsparseH with hfiner | hlocal
          · obtain ⟨T₀, hhalf₀, hfine₀⟩ := hfiner
            let e : {x : V // x ∈ T} ↪ V :=
              ⟨Subtype.val, Subtype.val_injective⟩
            let U : Finset V := T₀.map e
            have hhalf : T.card ≤ 2 * U.card := by simpa [H, U] using hhalf₀
            have hfine : ESparse G (2 * R ^ 24) U := by
              exact ESparse.map_induce G T hfine₀
            by_cases hnext : R ^ 2 ≤ X
            · have hRlt : R < R ^ 2 := by
                calc R = R ^ 1 := by simp
                     _ < R ^ 2 := Nat.pow_lt_pow_right (by omega) (by omega)
              have hmeasure : X - R ^ 2 < q := by
                rw [← hq]
                exact Nat.sub_lt_sub_left (hRlt.trans_le hnext) hRlt
              apply ih (X - R ^ 2) hmeasure (R ^ 2) U rfl
              · exact hR.trans (Nat.le_pow (by norm_num : 0 < (2 : ℕ)))
              · exact hnext
              · calc
                  n ≤ D * R * T.card := hambient
                  _ ≤ D * R * (2 * U.card) := Nat.mul_le_mul_left _ hhalf
                  _ = D * (2 * R) * U.card := by ring
                  _ ≤ D * (R ^ 2) * U.card := by
                    gcongr
                    nlinarith
              · convert hfine using 1 <;> ring
            · have hXR2 : X < R ^ 2 := Nat.lt_of_not_ge hnext
              have hUsize : R ^ 100 ≤ U.card := by
                apply Nat.le_of_mul_le_mul_left (c := 2) (hc := by omega)
                exact hcombSize.trans hhalf
              obtain ⟨B, _hinside, hsparseB, hwidth⟩ :=
                equal_sparse_blockade G U R X hR hXR2 hUsize hfine
              refine ⟨R, B, by omega, ?_, Or.inr hsparseB, ?_⟩
              · exact hRX.trans (Nat.le_pow (by norm_num : 0 < (2 : ℕ)))
              · intro i
                have hD_R : D ≤ R ^ D := hDpow R (by omega)
                have h8 : 8 ≤ R ^ 3 := by
                  exact (by norm_num : 8 ≤ 256 ^ 3).trans
                    (Nat.pow_le_pow_left hR 3)
                have hcoeffWidth : 8 * D * R ^ 2 ≤ R ^ d₀ := by
                  calc
                    8 * D * R ^ 2 ≤ R ^ 3 * R ^ D * R ^ 2 := by gcongr
                    _ = R ^ (D + 5) := by ring
                    _ ≤ R ^ d₀ := Nat.pow_le_pow_right (by omega) (by
                      simp [d₀]; omega)
                calc
                  n ≤ D * R * T.card := hambient
                  _ ≤ D * R * (2 * U.card) := Nat.mul_le_mul_left _ hhalf
                  _ ≤ D * R * (2 * (4 * R * (B.block i).card)) :=
                    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2 (hwidth i))
                  _ = (8 * D * R ^ 2) * (B.block i).card := by ring
                  _ ≤ R ^ d₀ * (B.block i).card :=
                    Nat.mul_le_mul_right _ hcoeffWidth
          · obtain ⟨k, B₀, hk, hkX, hRk, hpure, hwidth⟩ := hlocal
            let e : {x : V // x ∈ T} ↪ V :=
              ⟨Subtype.val, Subtype.val_injective⟩
            let B := mapBlockade e B₀
            refine ⟨k, B, hk, hkX, ?_, ?_⟩
            · rcases hpure with hpure | hsparseB
              · exact Or.inl (Blockade.IsPure.map_induce G T hpure)
              · exact Or.inr (Blockade.IsESparse.map_induce G T hsparseB)
            · intro i
              have hDk : D ≤ k ^ D := hDpow k hk
              have h17 : 17 ≤ k ^ 5 := by
                exact (by norm_num : 17 ≤ 2 ^ 5).trans (Nat.pow_le_pow_left hk 5)
              have hcoeffWidth : D * R * k ^ 100 ≤ k ^ d₀ := by
                calc
                  D * R * k ^ 100 ≤ k ^ D * (17 * k) * k ^ 100 := by gcongr
                  _ ≤ k ^ D * (k ^ 5 * k) * k ^ 100 := by gcongr
                  _ = k ^ (D + 106) := by ring
                  _ ≤ k ^ d₀ := Nat.pow_le_pow_right (by omega) hdlarge
              calc
                n ≤ D * R * T.card := hambient
                _ ≤ D * R * (k ^ 100 * (B₀.block i).card) :=
                  Nat.mul_le_mul_left _ (by simpa [H] using hwidth i)
                _ = (D * R * k ^ 100) * (B.block i).card := by simp [B]; ring
                _ ≤ k ^ d₀ * (B.block i).card :=
                  Nat.mul_le_mul_right _ hcoeffWidth
    exact hP (X - R₀) R₀ S rfl (by simp [R₀]) (by simpa [R₀] using hX)
      hstart (by simpa [R₀] using hs)
  rcases hreduce G hfree with ⟨S, hSwide, hsparse | hsparse⟩
  · apply sparse_start S
      (by
        calc
          n ≤ D * S.card := by simpa [n] using hSwide
          _ ≤ D * R₀ * S.card := by
            apply Nat.mul_le_mul_right S.card
            simpa using Nat.mul_le_mul_left D (show 1 ≤ R₀ by simp [R₀]))
      (by
        intro v
        exact Nat.le_of_lt (by simpa [P₀, R₀] using hsparse v))
  · have hS2 : 2 ≤ S.card := by
      by_contra hnot
      have hSle : S.card ≤ 1 := by omega
      have hDle : D ≤ X ^ D := hDpow X (by omega)
      have hnle : n ≤ D := by
        calc
          n ≤ D * S.card := by simpa [n] using hSwide
          _ ≤ D * 1 := Nat.mul_le_mul_left D hSle
          _ = D := by simp
      have hDlt : D < d₀ := by simp [d₀]; omega
      have hpowlt : X ^ D < X ^ d₀ :=
        Nat.pow_lt_pow_right (by omega) hDlt
      have hglobaln : X ^ d₀ ≤ n := by simpa [n] using hglobal
      exact Nat.not_le_of_lt (hDle.trans_lt hpowlt)
        (hglobaln.trans hnle)
    have hs32 : ESparse Gᶜ 32 S := by
      intro v
      have h32P : 32 ≤ P₀ := by norm_num [P₀, R₀]
      exact (Nat.mul_le_mul_right _ h32P).trans (Nat.le_of_lt (hsparse v))
    obtain ⟨B, _hinside, hanti, hwidth⟩ :=
      sparse_P5_anticomplete_pair Gᶜ S (housefree_compl_p5free hfree) hS2 hs32
    have hcomplete : B.IsComplete G := anticomplete_compl_is_complete hanti
    refine ⟨2, B, by norm_num, ?_, Or.inl ?_, ?_⟩
    · exact (by omega : 2 ≤ X).trans (Nat.le_pow (by norm_num : 0 < (2 : ℕ)))
    · intro i j hij
      exact Or.inl (hcomplete hij)
    · intro i
      have hD2 : D ≤ 2 ^ D := nat_le_two_pow D
      have hcoeff : 32 * D ≤ 2 ^ d₀ := by
        calc
          32 * D ≤ 2 ^ 5 * 2 ^ D := Nat.mul_le_mul (by norm_num) hD2
          _ = 2 ^ (D + 5) := by
            simpa [Nat.add_comm] using (pow_add 2 5 D).symm
          _ ≤ 2 ^ d₀ := Nat.pow_le_pow_right (by omega) (by simp [d₀]; omega)
      calc
        n ≤ D * S.card := by simpa [n] using hSwide
        _ ≤ D * (32 * (B.block i).card) := Nat.mul_le_mul_left D (hwidth i)
        _ = (32 * D) * (B.block i).card := by ring
        _ ≤ 2 ^ d₀ * (B.block i).card := Nat.mul_le_mul_right _ hcoeff

end Lax57Proofs
