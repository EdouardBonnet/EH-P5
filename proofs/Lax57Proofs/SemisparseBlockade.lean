import Lax57.SemisparseBlockade
import Lax57Proofs.BlockadeOperations
import Lax57Proofs.LayoutExtraction
import Mathlib.Tactic

set_option maxHeartbeats 1600000
set_option maxRecDepth 4000

namespace Lax57Proofs

open Finset
open scoped SimpleGraph
open Lax57.GraphDefinitions

universe u

private theorem weaklyESparse_mono
    {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {Q P : ℕ} {A B : Finset V} (hQP : Q ≤ P)
    (h : WeaklyESparse G P A B) : WeaklyESparse G Q A B := by
  calc
    Q * (G.interedges A B).card ≤ P * (G.interedges A B).card :=
      Nat.mul_le_mul_right _ hQP
    _ ≤ A.card * B.card := h

private theorem weaklyESparse_of_anticomplete
    {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {Q : ℕ} {A B : Finset V}
    (h : ∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y) :
    WeaklyESparse G Q A B := by
  have hempty : G.interedges A B = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨z, hz⟩
    rw [SimpleGraph.mem_interedges_iff] at hz
    exact h z.1 hz.1 z.2 hz.2.1 hz.2.2
  simp [WeaklyESparse, hempty]

/-- A long enough pure or directed-sparse local blockade can be truncated to
the requested length; purity and directed sparsity both imply semisparsity. -/
private theorem take_local_semisparse
    {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k E P Q : ℕ} (B : Blockade (V := V) k)
    (hEk : E ≤ k) (hQP : Q ≤ P)
    (hkind : B.IsPure G ∨ B.IsESparse G P) :
    (takeBlockade B hEk).IsSemisparse G Q := by
  intro i j hij
  let i' : Fin k := ⟨i, i.isLt.trans_le hEk⟩
  let j' : Fin k := ⟨j, j.isLt.trans_le hEk⟩
  have hij' : i' ≠ j' := by
    intro heq
    apply hij
    apply Fin.ext
    exact congrArg (fun z : Fin k ↦ z.val) heq
  rcases hkind with hpure | hsparse
  · rcases hpure hij' with hcomplete | hanti
    · exact Or.inl hcomplete
    · exact Or.inr (weaklyESparse_of_anticomplete G hanti)
  · apply Or.inr
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · have hs := hsparse (show i' < j' by exact hijlt)
      exact weaklyESparse_mono G hQP
        (WeaklyESparse.symm G (WeaklyESparse.of_ESparseTo G hs))
    · have hs := hsparse (show j' < i' by exact hjilt)
      exact weaklyESparse_mono G hQP
        (WeaklyESparse.of_ESparseTo G hs)

/--
---
conclusion: Lax57.SemisparseBlockade.semisparse_house_blockade
assumptions:
  - Lax54.AveragingLemma.sparse_graph_thinning
  - Lax54.BipartiteCombLemma.bipartite_comb_lemma
  - Lax54.RodlTheorem.rodl_theorem
---
Start with the one-block layout and choose a maximal layout with fewer than
$E$ blocks. Its conserved weight identifies a block containing a polynomial
fraction of the graph. The local blockade theorem either gives at least $E$
blocks at once or refines the layout to a larger one, which must cross the
$E$-block threshold. The bound on exceptional ordered edges then gives the
required semisparsity.
-/
theorem semisparse_house_blockade :
    ∃ d : ℕ, 40 ≤ d ∧
      ∀ E : ℕ, 2 ≤ E →
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) [DecidableRel G.Adj],
          IsHouseFree G → E ^ (10 * d ^ 2) ≤ Fintype.card V →
            ∃ B : Blockade (V := V) E,
              B.IsSemisparse G (E ^ d) ∧
                B.HasWidthLoss (E ^ (10 * d ^ 2)) := by
  obtain ⟨d₀, hd₀, hlocal⟩ := polynomial_local_blockade
  let d := 100 * d₀
  refine ⟨d, by simp [d]; omega, ?_⟩
  intro E hE V _ _ G _ hfree hsize
  classical
  let aexp := d + 2 + 4 * d₀
  let P := E ^ aexp
  let Q := E ^ d
  have hEpos : 0 < E := by omega
  have haexp8 : 8 ≤ aexp := by simp [aexp, d]; omega
  have hdle : d ≤ aexp := by dsimp [aexp]; omega
  have hP256 : 256 ≤ P := by
    calc
      256 = 2 ^ 8 := by norm_num
      _ ≤ E ^ 8 := Nat.pow_le_pow_left hE 8
      _ ≤ E ^ aexp := Nat.pow_le_pow_right hEpos haexp8
      _ = P := rfl
  have hQP : Q ≤ P := by
    exact Nat.pow_le_pow_right hEpos hdle
  have hscale : Q * (2 * E) * E ^ (4 * d₀) ≤ P := by
    have h2E : 2 * E ≤ E ^ 2 := by nlinarith
    calc
      Q * (2 * E) * E ^ (4 * d₀) ≤
          E ^ d * E ^ 2 * E ^ (4 * d₀) := by
        simp only [Q]
        gcongr
      _ = E ^ (d + 2 + 4 * d₀) := by
        rw [← pow_add, ← pow_add]
      _ = P := rfl
  have hlocalExp : d₀ + aexp * d₀ ≤ 10 * d ^ 2 := by
    simp only [aexp, d]
    nlinarith
  have hwideExp : d₀ + aexp * 2 * d₀ ≤ 10 * d ^ 2 := by
    simp only [aexp, d]
    nlinarith
  have hextractExp : 2 * d₀ ≤ 10 * d ^ 2 := by
    simp only [d]
    nlinarith
  let L₀ := initialPolynomialLayout G E P d₀ (by omega)
  let LayoutAt : ℕ → Prop := fun q ↦
    ∃ L : PolynomialLayout G E P d₀, L.card = q
  have hinitial : LayoutAt 1 := by
    refine ⟨L₀, ?_⟩
    simp [L₀, initialPolynomialLayout, PolynomialLayout.card]
  let q := Nat.findGreatest LayoutAt (E - 1)
  have honeBound : 1 ≤ E - 1 := by omega
  have hqBound : q ≤ E - 1 := Nat.findGreatest_le _
  have hqpos : 1 ≤ q := by
    exact Nat.le_findGreatest honeBound hinitial
  have hqLayout : LayoutAt q :=
    Nat.findGreatest_spec honeBound hinitial
  obtain ⟨L, hLcard⟩ := hqLayout
  have hLlt : L.card < E := by omega
  obtain ⟨a, hheavy⟩ := L.exists_heavy_block hLlt
  have hreserve : E ^ d₀ * P ^ d₀ ≤ Fintype.card V := by
    calc
      E ^ d₀ * P ^ d₀ = E ^ d₀ * E ^ (aexp * d₀) := by
        simp only [P]
        rw [pow_mul]
      _ = E ^ (d₀ + aexp * d₀) := by rw [pow_add]
      _ ≤ E ^ (10 * d ^ 2) :=
        Nat.pow_le_pow_right hEpos hlocalExp
      _ ≤ Fintype.card V := hsize
  have hlocalSize : P ^ d₀ ≤ (L.block a).card := by
    apply Nat.le_of_mul_le_mul_left (c := E ^ d₀) ?_ (pow_pos hEpos _)
    exact hreserve.trans hheavy
  let H := G.induce (L.block a : Set V)
  have hlocalSizeH : P ^ d₀ ≤ Fintype.card {x : V // x ∈ L.block a} := by
    simpa using hlocalSize
  obtain ⟨k, B₀, hk, hkP, hkind₀, hwidth₀⟩ :=
    hlocal P hP256 H (IsHouseFree.induce_finset hfree (L.block a)) hlocalSizeH
  let e : {x : V // x ∈ L.block a} ↪ V :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let B : Blockade (V := V) k := mapBlockade e B₀
  have hBinside : B.IsInside (L.block a) := by
    intro i x hx
    change x ∈ (B₀.block i).map e at hx
    obtain ⟨xA, _hx, rfl⟩ := Finset.mem_map.mp hx
    exact xA.property
  have hBkind : B.IsPure G ∨ B.IsESparse G P := by
    rcases hkind₀ with hpure | hsparse
    · exact Or.inl (Blockade.IsPure.map_induce G (L.block a) hpure)
    · exact Or.inr (Blockade.IsESparse.map_induce G (L.block a) hsparse)
  have hBwidth : ∀ i : Fin k,
      (L.block a).card ≤ k ^ d₀ * (B.block i).card := by
    intro i
    simpa [H, B] using hwidth₀ i
  by_cases hkE : E ≤ k
  · let C := takeBlockade B hkE
    refine ⟨C, take_local_semisparse G B hkE hQP hBkind, ?_⟩
    have hPpow : (P ^ 2) ^ d₀ = E ^ (aexp * 2 * d₀) := by
      simp only [P]
      rw [← pow_mul, ← pow_mul]
      simp [Nat.mul_assoc]
    have hcoeff : E ^ d₀ * k ^ d₀ ≤ E ^ (10 * d ^ 2) := by
      calc
        E ^ d₀ * k ^ d₀ ≤ E ^ d₀ * (P ^ 2) ^ d₀ := by
          gcongr
        _ = E ^ (d₀ + aexp * 2 * d₀) := by
          rw [hPpow, pow_add]
        _ ≤ E ^ (10 * d ^ 2) :=
          Nat.pow_le_pow_right hEpos hwideExp
    intro i
    let i' : Fin k := ⟨i, i.isLt.trans_le hkE⟩
    calc
      Fintype.card V ≤ E ^ d₀ * (L.block a).card := hheavy
      _ ≤ E ^ d₀ * (k ^ d₀ * (B.block i').card) :=
        Nat.mul_le_mul_left _ (hBwidth i')
      _ = (E ^ d₀ * k ^ d₀) * (B.block i').card := by ring
      _ ≤ E ^ (10 * d ^ 2) * (B.block i').card :=
        Nat.mul_le_mul_right _ hcoeff
      _ = E ^ (10 * d ^ 2) * (C.block i).card := rfl
  · have hklt : k < E := Nat.lt_of_not_ge hkE
    obtain ⟨L', hL'card⟩ :=
      L.refine a B hk hklt hBinside hBkind hBwidth hheavy
    by_cases hreached : E ≤ L'.card
    · have hshort : L'.card < 2 * E := by omega
      obtain ⟨C, hCsemi, hCwidth⟩ :=
        L'.extract_semisparse hE hreached hshort hscale
      refine ⟨C, hCsemi, ?_⟩
      have hloss : E ^ (2 * d₀) ≤ E ^ (10 * d ^ 2) :=
        Nat.pow_le_pow_right hEpos hextractExp
      intro i
      exact (hCwidth i).trans (Nat.mul_le_mul_right _ hloss)
    · have hL'lt : L'.card < E := Nat.lt_of_not_ge hreached
      have hL'max : L'.card ≤ q := by
        change L'.card ≤ Nat.findGreatest LayoutAt (E - 1)
        exact Nat.le_findGreatest (by omega) ⟨L', rfl⟩
      omega

end Lax57Proofs
