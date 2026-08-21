import Lax54.BipartiteCombLemma
import Lax57.AnticomponentBlockade
import Lax57Proofs.CoveringTools
import Lax57Proofs.MixedTools
import Mathlib.Tactic

set_option maxHeartbeats 800000
set_option maxRecDepth 2000

namespace Lax57Proofs

open Finset
open scoped BigOperators SimpleGraph
open Lax57.GraphDefinitions
open Lax54.BipartiteCombLemma

universe u

/-- The pure-blockade outcome of the sparse comb step. -/
def HasCombPureBlockade {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (R X : ℕ) : Prop :=
  ∃ (k : ℕ) (B : Blockade (V := V) k),
    R ^ 3 ≤ k ∧ k ≤ X ^ 2 ∧ B.IsPure G ∧
      ∀ i : Fin k, Fintype.card V ≤ k ^ 40 * (B.block i).card

/-- The sparse-pair outcome of the sparse comb step. The set `Y` is the
large remainder and is `1/X`-sparse to the peeled block `Z`. -/
def HasCombSparsePeel {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (R X : ℕ) : Prop :=
  ∃ Z Y : Finset V, Disjoint Z Y ∧
    Fintype.card V ≤ 4 * R ^ 24 * Z.card ∧
    R * (Fintype.card V - Y.card) ≤ 4 * Fintype.card V ∧
    ESparseTo G X Y Z

private theorem card_high_to_set
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (P Q : ℕ) (hT : T.Nonempty)
    (hsparse : ∀ v : V, P * Q * G.degree v ≤ Fintype.card V) :
    P * ((Finset.univ : Finset V).filter fun v ↦
      T.card < Q * (neighborsIn G T v).card).card < Fintype.card V := by
  classical
  by_cases hPzero : P = 0
  · subst P
    have hnpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨hT.choose⟩
    simpa using hnpos
  have hPpos : 0 < P := Nat.pos_of_ne_zero hPzero
  let H := (Finset.univ : Finset V).filter fun v ↦
    T.card < Q * (neighborsIn G T v).card
  by_cases hH : H.Nonempty
  · have hlower : H.card * T.card <
        Q * ∑ v ∈ H, (neighborsIn G T v).card := by
      calc
        H.card * T.card = ∑ _v ∈ H, T.card := by simp
        _ < ∑ v ∈ H, Q * (neighborsIn G T v).card := by
          exact Finset.sum_lt_sum_of_nonempty hH fun v hv ↦
            (Finset.mem_filter.mp hv).2
        _ = Q * ∑ v ∈ H, (neighborsIn G T v).card := by
          rw [Finset.mul_sum]
    have hsumsub : ∑ v ∈ H, (neighborsIn G T v).card ≤
        ∑ v ∈ (Finset.univ : Finset V),
          (neighborsIn G T v).card := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ H)
      exact fun _ _ _ ↦ Nat.zero_le _
    have hinter : ∑ v ∈ (Finset.univ : Finset V),
          (neighborsIn G T v).card = ∑ v ∈ T, G.degree v := by
      rw [sum_card_neighborsIn_eq_card_interedges]
      have hc : (G.interedges Finset.univ T).card =
          (G.interedges T Finset.univ).card :=
        Rel.card_interedges_comm G.symm Finset.univ T
      rw [hc]
      rw [← sum_card_neighborsIn_eq_card_interedges]
      apply Finset.sum_congr rfl
      intro v hv
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      congr 1
      ext x
      simp [neighborsIn]
    have hdegreeSum : P * Q * (∑ v ∈ T, G.degree v) ≤
        T.card * Fintype.card V := by
      calc
        P * Q * (∑ v ∈ T, G.degree v) =
            ∑ v ∈ T, P * Q * G.degree v := by
          rw [Finset.mul_sum]
        _ ≤ ∑ _v ∈ T, Fintype.card V := by
          exact Finset.sum_le_sum fun v _ ↦ hsparse v
        _ = T.card * Fintype.card V := by simp
    have hmul : (P * H.card) * T.card <
        Fintype.card V * T.card := by
      calc
        (P * H.card) * T.card = P * (H.card * T.card) := by ring
        _ < P * (Q * ∑ v ∈ H, (neighborsIn G T v).card) :=
          (Nat.mul_lt_mul_left hPpos).2 hlower
        _ ≤ P * Q * (∑ v ∈ T, G.degree v) := by
          rw [hinter] at hsumsub
          simpa [Nat.mul_assoc] using Nat.mul_le_mul_left (P * Q) hsumsub
        _ ≤ T.card * Fintype.card V := hdegreeSum
        _ = Fintype.card V * T.card := by ring
    exact Nat.lt_of_mul_lt_mul_right hmul
  · have hHeq : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hH
    have hnpos : 0 < Fintype.card V := by
      exact Fintype.card_pos_iff.mpr ⟨hT.choose⟩
    simpa [H, hHeq] using hnpos

private theorem card_bad_from_low_columns
    {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A Z : Finset V) (X : ℕ) (hX : 0 < X) (hZ : Z.Nonempty)
    (hlow : ∀ z ∈ Z, X ^ 2 * (neighborsIn G A z).card < A.card) :
    X * (A.filter fun a ↦ Z.card < X * (neighborsIn G Z a).card).card
      ≤ A.card := by
  classical
  let D := A.filter fun a ↦ Z.card < X * (neighborsIn G Z a).card
  by_cases hD : D.Nonempty
  · have hlower : D.card * Z.card <
        X * ∑ a ∈ D, (neighborsIn G Z a).card := by
      calc
        D.card * Z.card = ∑ _a ∈ D, Z.card := by simp
        _ < ∑ a ∈ D, X * (neighborsIn G Z a).card := by
          exact Finset.sum_lt_sum_of_nonempty hD fun a ha ↦
            (Finset.mem_filter.mp ha).2
        _ = X * ∑ a ∈ D, (neighborsIn G Z a).card := by
          rw [Finset.mul_sum]
    have hsumsub : ∑ a ∈ D, (neighborsIn G Z a).card ≤
        (G.interedges A Z).card := by
      calc
        ∑ a ∈ D, (neighborsIn G Z a).card ≤
            ∑ a ∈ A, (neighborsIn G Z a).card :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun _ _ _ ↦ Nat.zero_le _
        _ = (G.interedges A Z).card :=
          sum_card_neighborsIn_eq_card_interedges G A Z
    have hupper : X ^ 2 * (G.interedges A Z).card < Z.card * A.card := by
      have hc : (G.interedges A Z).card = (G.interedges Z A).card :=
        Rel.card_interedges_comm G.symm A Z
      rw [hc, ← sum_card_neighborsIn_eq_card_interedges]
      calc
        X ^ 2 * ∑ z ∈ Z, (neighborsIn G A z).card =
            ∑ z ∈ Z, X ^ 2 * (neighborsIn G A z).card := by
          rw [Finset.mul_sum]
        _ < ∑ _z ∈ Z, A.card := by
          exact Finset.sum_lt_sum_of_nonempty hZ fun z hz ↦ hlow z hz
        _ = Z.card * A.card := by simp
    have hmul : (X * D.card) * Z.card < A.card * Z.card := by
      calc
        (X * D.card) * Z.card = X * (D.card * Z.card) := by ring
        _ < X * (X * ∑ a ∈ D, (neighborsIn G Z a).card) :=
          (Nat.mul_lt_mul_left hX).2 hlower
        _ = X ^ 2 * ∑ a ∈ D, (neighborsIn G Z a).card := by ring
        _ ≤ X ^ 2 * (G.interedges A Z).card :=
          Nat.mul_le_mul_left (X ^ 2) hsumsub
        _ < Z.card * A.card := hupper
        _ = A.card * Z.card := by ring
    exact Nat.le_of_lt (Nat.lt_of_mul_lt_mul_right hmul)
  · have hDeq : D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hD
    simp [D, hDeq]

private theorem fin_card_le_of_injective_into
    {V : Type u} [Fintype V] {t : ℕ} {S : Finset V}
    (f : Fin t → V) (hf : Function.Injective f)
    (hmem : ∀ i, f i ∈ S) : t ≤ S.card := by
  let g : Fin t → {x : V // x ∈ S} := fun i ↦ ⟨f i, hmem i⟩
  have hg : Function.Injective g := fun _ _ h ↦ hf (congrArg Subtype.val h)
  simpa using Fintype.card_le_of_injective g hg

/-- The integer form of Lemma 5.2: a moderately sparse house-free graph can
be sparsified, yields a polynomial pure blockade, or admits one large
`1/X`-sparse peel. -/
theorem sparse_comb_step
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (R X : ℕ)
    (hR : 256 ≤ R) (hRX : R ≤ X)
    (hsize : R ^ 100 ≤ Fintype.card V)
    (hfree : IsHouseFree G)
    (hsparse : ∀ v : V, R ^ 12 * G.degree v ≤ Fintype.card V) :
    (∀ v : V, 2 * R ^ 24 * G.degree v ≤ Fintype.card V) ∨
      HasCombPureBlockade G R X ∨ HasCombSparsePeel G R X := by
  classical
  let n := Fintype.card V
  by_cases hfiner : ∀ v : V, 2 * R ^ 24 * G.degree v ≤ Fintype.card V
  · exact Or.inl hfiner
  right
  have hRpos : 0 < R := by omega
  have hXpos : 0 < X := hRpos.trans_le hRX
  push Not at hfiner
  obtain ⟨v, hv⟩ := hfiner
  let v₀ : V := v
  let N := G.neighborFinset v₀
  have hNcard : N.card = G.degree v₀ := rfl
  have hNlarge : n < 2 * R ^ 24 * N.card := by
    simpa [n, v₀, N] using hv
  have hNnonempty : N.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hN
    simp [hN] at hNlarge
  have hsparseV (x : V) : R ^ 12 * G.degree x ≤ n := by
    simpa [n] using hsparse x
  have hNsmall : R ^ 12 * N.card ≤ n := by
    simpa [hNcard] using hsparseV v₀
  let A' := (Finset.univ : Finset V).filter fun a ↦
    N.card < R ^ 8 * (neighborsIn G N a).card
  have hA'small : R ^ 4 * A'.card < n := by
    have h := card_high_to_set G N (R ^ 4) (R ^ 8) hNnonempty (by
      intro x
      convert hsparseV x using 1 <;> ring)
    simpa [A', n] using h
  let A := (Finset.univ : Finset V) \ (insert v₀ N ∪ A')
  have hNsub : N ⊆ (Finset.univ : Finset V) := Finset.subset_univ _
  have hvnotN : v₀ ∉ N := by simp [N]
  have hremoved : R ^ 4 * (n - A.card) ≤ 3 * n := by
    have hAc : n - A.card = (insert v₀ N ∪ A').card := by
      have hsub : insert v₀ N ∪ A' ⊆ (Finset.univ : Finset V) :=
        Finset.subset_univ _
      have hcard := Finset.card_sdiff_of_subset hsub
      change A.card = n - (insert v₀ N ∪ A').card at hcard
      have hle : (insert v₀ N ∪ A').card ≤ n := by
        simpa [n] using Finset.card_le_card hsub
      omega
    rw [hAc]
    calc
      R ^ 4 * (insert v₀ N ∪ A').card ≤
          R ^ 4 * ((insert v₀ N).card + A'.card) :=
        Nat.mul_le_mul_left _ (Finset.card_union_le _ _)
      _ = R ^ 4 + R ^ 4 * N.card + R ^ 4 * A'.card := by
        rw [Finset.card_insert_of_notMem hvnotN]
        ring
      _ ≤ n + n + n := by
        have hR4n : R ^ 4 ≤ n := by
          exact (Nat.pow_le_pow_right hRpos (by omega)).trans hsize
        have hN' : R ^ 4 * N.card ≤ n :=
          (Nat.mul_le_mul_right N.card
            (Nat.pow_le_pow_right hRpos (by omega))).trans hNsmall
        omega
      _ = 3 * n := by ring
  have hAhalf : n ≤ 2 * A.card := by
    have hR4 : 6 ≤ R ^ 4 := by
      calc
        6 ≤ 256 ^ 4 := by norm_num
        _ ≤ R ^ 4 := Nat.pow_le_pow_left hR 4
    have hAcard : A.card ≤ n := by
      simpa [n] using Finset.card_le_card (Finset.subset_univ A)
    have hlinear : 6 * (n - A.card) ≤ 3 * n :=
      (Nat.mul_le_mul_right (n - A.card) hR4).trans hremoved
    omega
  have hAnonempty : A.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hA
    have hnpos : 0 < n := (Nat.pow_pos hRpos).trans_le hsize
    have : A.card = 0 := by simp [hA]
    omega
  have hAdisjN : Disjoint A N := by
    rw [Finset.disjoint_left]
    intro a haA haN
    exact (Finset.mem_sdiff.mp haA).2
      (Finset.mem_union_left _ (Finset.mem_insert_of_mem haN))
  have hAsparseN : ∀ a ∈ A,
      R ^ 8 * (neighborsIn G N a).card ≤ N.card := by
    intro a haA
    have haNot : a ∉ A' := by
      intro ha'
      exact (Finset.mem_sdiff.mp haA).2 (Finset.mem_union_right _ ha')
    have := not_lt.mp (show ¬ N.card < R ^ 8 * (neighborsIn G N a).card by
      simpa [A'] using haNot)
    exact this
  let N' := N.filter fun b ↦
    X ^ 2 * (neighborsIn G A b).card < A.card
  by_cases hN'large : N.card ≤ 2 * N'.card
  · apply Or.inr
    let D := A.filter fun a ↦
      N'.card < X * (neighborsIn G N' a).card
    let Y := A \ D
    have hN'nonempty : N'.Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro hN'eq
      have hNpos : 0 < N.card := Finset.card_pos.mpr hNnonempty
      have hN'zero : N'.card = 0 := by simp [hN'eq]
      omega
    have hDsmall : X * D.card ≤ A.card := by
      apply card_bad_from_low_columns G A N' X hXpos hN'nonempty
      intro z hz
      exact (Finset.mem_filter.mp hz).2
    have hYdef : Y = A \ D := rfl
    have hYsubA : Y ⊆ A := Finset.sdiff_subset
    have hdisj : Disjoint N' Y := by
      apply Finset.disjoint_left.mpr
      intro z hzN' hzY
      exact Finset.disjoint_left.mp hAdisjN (hYsubA hzY)
        ((Finset.filter_subset _ _) hzN')
    refine ⟨N', Y, hdisj, ?_, ?_, ?_⟩
    · exact Nat.le_of_lt <| hNlarge.trans_le <| by
        calc
          2 * R ^ 24 * N.card ≤ 2 * R ^ 24 * (2 * N'.card) :=
            Nat.mul_le_mul_left _ hN'large
          _ = 4 * R ^ 24 * N'.card := by ring
    · have hDsub : D ⊆ A := Finset.filter_subset _ _
      have hYcard : A.card = Y.card + D.card := by
        have := Finset.card_sdiff_add_card_eq_card hDsub
        change (A \ D).card + D.card = A.card at this
        change A.card = (A \ D).card + D.card
        omega
      have hAcard : A.card ≤ n := by
        simpa [n] using Finset.card_le_card (Finset.subset_univ A)
      have hsplit : n - Y.card = (n - A.card) + D.card := by omega
      have hRR4 : R ≤ R ^ 4 := by
        calc
          R = R ^ 1 := by simp
          _ ≤ R ^ 4 := Nat.pow_le_pow_right hRpos (by omega)
      rw [hsplit, Nat.mul_add]
      calc
        R * (n - A.card) + R * D.card ≤
            R ^ 4 * (n - A.card) + X * D.card := by
          exact Nat.add_le_add
            (Nat.mul_le_mul_right (n - A.card) hRR4)
            (Nat.mul_le_mul_right _ hRX)
        _ ≤ 3 * n + A.card := Nat.add_le_add hremoved hDsmall
        _ ≤ 4 * n := by
          omega
    · intro y hy
      have hyA : y ∈ A := hYsubA hy
      have hyNotD : y ∉ D := (Finset.mem_sdiff.mp hy).2
      apply not_lt.mp
      intro hbad
      exact hyNotD (Finset.mem_filter.mpr ⟨hyA, hbad⟩)
  · apply Or.inl
    have hN'lt : 2 * N'.card < N.card := Nat.lt_of_not_ge hN'large
    let B := N \ N'
    have hN'sub : N' ⊆ N := Finset.filter_subset _ _
    have hNB : N.card = B.card + N'.card := by
      have h := Finset.card_sdiff_add_card_eq_card hN'sub
      change (N \ N').card + N'.card = N.card at h
      simpa [B] using h.symm
    have hNBtwo : N.card ≤ 2 * B.card := by omega
    have hBnonempty : B.Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro hBeq
      have hNpos : 0 < N.card := Finset.card_pos.mpr hNnonempty
      have hBzero : B.card = 0 := by simp [hBeq]
      omega
    have hBsubN : B ⊆ N := Finset.sdiff_subset
    have hABdisj : Disjoint A B := hAdisjN.mono_right hBsubN
    have hrichB : ∀ b ∈ B,
        A.card ≤ X ^ 2 * (neighborsIn G A b).card := by
      intro b hb
      have hbN : b ∈ N := (Finset.mem_sdiff.mp hb).1
      have hbNot : b ∉ N' := (Finset.mem_sdiff.mp hb).2
      exact not_lt.mp (show ¬ X ^ 2 * (neighborsIn G A b).card < A.card by
        simpa [N', hbN] using hbNot)
    have hAsparseB : ESparseTo G (R ^ 7) A B := by
      intro a ha
      have hmono : (neighborsIn G B a).card ≤ (neighborsIn G N a).card := by
        apply Finset.card_le_card
        intro z hz
        rw [neighborsIn, Finset.mem_filter] at hz ⊢
        exact ⟨hBsubN hz.1, hz.2⟩
      have htwo : 2 * R ^ 7 ≤ R ^ 8 := by
        calc
          2 * R ^ 7 ≤ R * R ^ 7 := Nat.mul_le_mul_right _ (by omega)
          _ = R ^ 8 := by ring
      have hs := hAsparseN a ha
      calc
        R ^ 7 * (neighborsIn G B a).card ≤
            R ^ 7 * (neighborsIn G N a).card := Nat.mul_le_mul_left _ hmono
        _ ≤ B.card := by
          have htwodeg : 2 * (R ^ 7 * (neighborsIn G N a).card) ≤ N.card := by
            calc
              2 * (R ^ 7 * (neighborsIn G N a).card) =
                  (2 * R ^ 7) * (neighborsIn G N a).card := by ring
              _ ≤ R ^ 8 * (neighborsIn G N a).card :=
                Nat.mul_le_mul_right _ htwo
              _ ≤ N.card := hs
          omega
    obtain ⟨S, hSA, hScard, hcover⟩ :=
      exists_bounded_half_cover G A B (X ^ 2) (Nat.pow_pos hXpos)
        hAnonempty hrichB
    let Cset := coveredBy G S B
    change B.card ≤ 2 * Cset.card at hcover
    have hCsubB : Cset ⊆ B := coveredBy_subset G S B
    have hCnonempty : Cset.Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro hCeq
      have hBpos : 0 < B.card := Finset.card_pos.mpr hBnonempty
      have hCzero : Cset.card = 0 := by simp [hCeq]
      omega
    have hSBdisj : Disjoint S Cset :=
      (hABdisj.mono_left hSA).mono_right hCsubB
    let Delta := B.card / R ^ 7
    have hDelta : ∀ a ∈ S,
        (Cset.filter fun b ↦ G.Adj a b).card ≤ Delta := by
      intro a ha
      rw [Nat.le_div_iff_mul_le (Nat.pow_pos hRpos)]
      have hsub : Cset.filter (fun b ↦ G.Adj a b) ⊆ neighborsIn G B a := by
        intro b hb
        rw [Finset.mem_filter] at hb
        rw [neighborsIn, Finset.mem_filter]
        exact ⟨hCsubB hb.1, hb.2⟩
      simpa [Nat.mul_comm] using
        ((Nat.mul_le_mul_left (R ^ 7) (Finset.card_le_card hsub)).trans
          (hAsparseB a (hSA ha)))
    have hcovered : ∀ b ∈ Cset, ∃ a ∈ S, G.Adj a b := by
      intro b hb
      exact (Finset.mem_filter.mp hb).2
    rcases Lax54.BipartiteCombLemma.bipartite_comb_lemma
        G S Cset B.card Delta hSBdisj (Finset.card_pos.mpr hBnonempty)
        hcovered hDelta with hcomb | hsmall
    · obtain ⟨t, Cmb, htpos, hwide⟩ := hcomb
      have htupper : t ≤ X ^ 2 :=
        (fin_card_le_of_injective_into Cmb.tooth Cmb.tooth_injective
          Cmb.tooth_mem).trans hScard
      have hblockpos (i : Fin t) : 0 < (Cmb.block i).card := by
        have hw := hwide i
        have hBpos : 0 < B.card := Finset.card_pos.mpr hBnonempty
        by_contra hz
        have hzero : (Cmb.block i).card = 0 := Nat.eq_zero_of_not_pos hz
        have hBzero : B.card ≤ 0 := by simpa [hzero] using hw
        omega
      have htSq : R ^ 7 ≤ t ^ 2 := by
        let i : Fin t := ⟨0, htpos⟩
        have hs := hAsparseB (Cmb.tooth i) (hSA (Cmb.tooth_mem i))
        have hneigh : (Cmb.block i).card ≤
            (neighborsIn G B (Cmb.tooth i)).card := by
          apply Finset.card_le_card
          intro z hz
          rw [neighborsIn, Finset.mem_filter]
          exact ⟨hCsubB (Cmb.block_subset i hz), Cmb.tooth_adj_block i z hz⟩
        have hmul : R ^ 7 * (Cmb.block i).card ≤
            t ^ 2 * (Cmb.block i).card := by
          exact (Nat.mul_le_mul_left _ hneigh |>.trans hs).trans (hwide i)
        exact Nat.le_of_mul_le_mul_right hmul (hblockpos i)
      have htLower : R ^ 3 ≤ t := by
        have hsquares : (R ^ 3) ^ 2 ≤ t ^ 2 := by
          calc
            (R ^ 3) ^ 2 = R ^ 6 := by ring
            _ ≤ R ^ 7 := Nat.pow_le_pow_right hRpos (by omega)
            _ ≤ t ^ 2 := htSq
        nlinarith
      have ht2 : 2 ≤ t := (by
        calc
          2 ≤ R := by omega
          _ ≤ R ^ 3 := by
            exact Nat.le_pow (by norm_num : 0 < (3 : ℕ))
          _ ≤ t := htLower)
      have hR24t8 : R ^ 24 ≤ t ^ 8 := by
        calc
          R ^ 24 = (R ^ 3) ^ 8 := by ring
          _ ≤ t ^ 8 := Nat.pow_le_pow_left htLower 8
      have hbaseWidth (i : Fin t) : n ≤
          4 * R ^ 24 * t ^ 2 * (Cmb.block i).card := by
        calc
          n ≤ 2 * R ^ 24 * N.card := Nat.le_of_lt hNlarge
          _ ≤ 2 * R ^ 24 * (2 * B.card) := Nat.mul_le_mul_left _ hNBtwo
          _ = 4 * R ^ 24 * B.card := by ring
          _ ≤ 4 * R ^ 24 * (t ^ 2 * (Cmb.block i).card) :=
            Nat.mul_le_mul_left _ (hwide i)
          _ = 4 * R ^ 24 * t ^ 2 * (Cmb.block i).card := by ring
      by_cases hcomplete : ∃ i : Fin t,
          ∃ D : Blockade (V := V) t, D.IsInside (Cmb.block i) ∧
            D.IsComplete G ∧ ∀ j : Fin t,
              (Cmb.block i).card ≤ 4 * t ^ 3 * (D.block j).card
      · obtain ⟨i, D, hinside, hcompD, hwidthD⟩ := hcomplete
        refine ⟨t, D, htLower, htupper, ?_, ?_⟩
        · intro i j hij
          exact Or.inl (hcompD hij)
        · intro j
          have hcoef : 16 * R ^ 24 * t ^ 5 ≤ t ^ 40 := by
            have h16 : 16 ≤ t ^ 4 := by
              calc
                16 = 2 ^ 4 := by norm_num
                _ ≤ t ^ 4 := Nat.pow_le_pow_left ht2 4
            calc
              16 * R ^ 24 * t ^ 5 ≤ t ^ 4 * t ^ 8 * t ^ 5 := by gcongr
              _ = t ^ 17 := by ring
              _ ≤ t ^ 40 := Nat.pow_le_pow_right (by omega) (by omega)
          calc
            n ≤ 4 * R ^ 24 * t ^ 2 * (Cmb.block i).card := hbaseWidth i
            _ ≤ 4 * R ^ 24 * t ^ 2 *
                (4 * t ^ 3 * (D.block j).card) :=
              Nat.mul_le_mul_left _ (hwidthD j)
            _ = (16 * R ^ 24 * t ^ 5) * (D.block j).card := by ring
            _ ≤ t ^ 40 * (D.block j).card := Nat.mul_le_mul_right _ hcoef
      · have hantiChoice : ∀ i : Fin t,
            ∃ J : Finset V, J ⊆ Cmb.block i ∧
              (Gᶜ.induce (J : Set V)).Connected ∧
              (Cmb.block i).card ≤ t ^ 2 * J.card := by
          intro i
          rcases Lax57.AnticomponentBlockade.anticomponent_or_complete_blockade
              G (Cmb.block i) t ht2 with hanti | hcomp
          · exact hanti
          · exfalso
            exact hcomplete ⟨i, hcomp⟩
        choose J hJsub hJconn hJwide using hantiChoice
        let D : Blockade (V := V) t :=
          { block := J
            disjoint := by
              intro i j hij
              exact (Cmb.blocks_disjoint hij).mono (hJsub i) (hJsub j) }
        have hpure : D.IsPure G := upside_down_comb_subblocks_pure G Cmb v₀
          hfree
          (by intro x hx; exact (G.mem_neighborFinset v₀ x).mp (hBsubN (hCsubB hx)))
          (by
            intro x hxS
            have hxA := hSA hxS
            have hxNot : x ∉ insert v₀ N := by
              intro hx
              exact (Finset.mem_sdiff.mp hxA).2 (Finset.mem_union_left _ hx)
            have hxv : x ≠ v₀ := by
              intro h; exact hxNot (by simp [h])
            have hxN : x ∉ N := by
              intro h; exact hxNot (Finset.mem_insert_of_mem h)
            exact fun hadj ↦ hxN ((G.mem_neighborFinset v₀ x).mpr hadj))
          D (fun i ↦ hJsub i) hJconn
        refine ⟨t, D, htLower, htupper, hpure, ?_⟩
        intro i
        have hcoef : 4 * R ^ 24 * t ^ 4 ≤ t ^ 40 := by
          have h4 : 4 ≤ t ^ 2 := by
            calc
              4 = 2 ^ 2 := by norm_num
              _ ≤ t ^ 2 := Nat.pow_le_pow_left ht2 2
          calc
            4 * R ^ 24 * t ^ 4 ≤ t ^ 2 * t ^ 8 * t ^ 4 := by
              gcongr
            _ = t ^ 14 := by ring
            _ ≤ t ^ 40 := Nat.pow_le_pow_right (by omega) (by omega)
        calc
          n ≤ 4 * R ^ 24 * t ^ 2 * (Cmb.block i).card := hbaseWidth i
          _ ≤ 4 * R ^ 24 * t ^ 2 * (t ^ 2 * (D.block i).card) := by
            gcongr
            exact hJwide i
          _ = (4 * R ^ 24 * t ^ 4) * (D.block i).card := by ring
          _ ≤ t ^ 40 * (D.block i).card := Nat.mul_le_mul_right _ hcoef
    · exfalso
      unfold SmallSideBound at hsmall
      have hDeltaMul : R ^ 7 * Delta ≤ B.card := by
        simpa [Delta] using Nat.mul_div_le B.card (R ^ 7)
      have hBsq : B.card ^ 2 ≤ 4 * Cset.card ^ 2 := by nlinarith
      have hBpos : 0 < B.card := Finset.card_pos.mpr hBnonempty
      have hcancel : R ^ 7 * B.card ^ 2 ≤
          (4 * 128 ^ 2) * B.card ^ 2 := by
        calc
          R ^ 7 * B.card ^ 2 ≤ R ^ 7 * (4 * Cset.card ^ 2) := by gcongr
          _ ≤ R ^ 7 * (4 * (128 ^ 2 * B.card * Delta)) := by gcongr
          _ = 4 * 128 ^ 2 * B.card * (R ^ 7 * Delta) := by ring
          _ ≤ 4 * 128 ^ 2 * B.card * B.card := by gcongr
          _ = (4 * 128 ^ 2) * B.card ^ 2 := by ring
      have hRbound : R ^ 7 ≤ 4 * 128 ^ 2 :=
        Nat.le_of_mul_le_mul_right hcancel (Nat.pow_pos hBpos)
      have : 4 * 128 ^ 2 < R ^ 7 := by
        calc
          4 * 128 ^ 2 < 256 ^ 7 := by norm_num
          _ ≤ R ^ 7 := Nat.pow_le_pow_left hR 7
      omega

end Lax57Proofs
