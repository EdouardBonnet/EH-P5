import Lax57Proofs.LayoutTools
import Mathlib.Tactic

set_option maxHeartbeats 1200000
set_option maxRecDepth 3000

namespace Lax57Proofs

open Finset
open scoped BigOperators SimpleGraph
open Lax57.GraphDefinitions

universe u

/-- The one-block layout from which the maximal-layout argument starts. -/
noncomputable def initialPolynomialLayout
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (E P d : ℕ) (hE : 1 ≤ E) : PolynomialLayout G E P d where
  Index := ULift.{u} (Fin 1)
  block := fun _ ↦ Finset.univ
  disjoint := by
    intro i j hij
    exfalso
    exact hij (Subsingleton.elim _ _)
  pattern := ⊥
  pattern_complete := by simp
  weight := fun _ ↦ 1
  weight_nonneg := by simp
  weight_capacity := by simp
  weight_total := by simp
  wide := by
    intro i
    simp only [Finset.card_univ]
    exact Nat.le_mul_of_pos_left _ (pow_pos (by omega) _)
  wrong_budget := by
    have hempty : wrongPairs G
        (fun _ : ULift.{u} (Fin 1) ↦ Finset.univ) ⊥ = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨p, hp⟩
      rw [wrongPairs, Finset.mem_filter] at hp
      obtain ⟨i, j, hij, -⟩ := hp.2
      exact hij (Subsingleton.elim _ _)
    simp [hempty]

/-- Before a layout reaches `E` blocks, its conserved weight potential
identifies a block containing at least an `E^{-d}` fraction of the graph. -/
theorem PolynomialLayout.exists_heavy_block
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {E P d : ℕ} (L : PolynomialLayout G E P d)
    (hcard : L.card < E) :
    ∃ a : L.Index,
      Fintype.card V ≤ E ^ d * (L.block a).card := by
  classical
  letI : Fintype L.Index := L.fintypeIndex
  letI : DecidableEq L.Index := L.decidableEqIndex
  let q := L.card
  have hqpos : 0 < q := by
    by_contra hq
    have hq0 : q = 0 := by omega
    have hempty : IsEmpty L.Index := Fintype.card_eq_zero_iff.mp (by simpa [q, PolynomialLayout.card] using hq0)
    letI := hempty
    exact (by norm_num : ¬(1 : ℚ) ≤ 0) (by simpa using L.weight_total)
  have hqE : q ≤ E := by omega
  have ha : ∃ a : L.Index, (1 : ℚ) ≤ (q : ℚ) * L.weight a := by
    by_contra hnot
    push Not at hnot
    have hlt : ∑ a : L.Index, (q : ℚ) * L.weight a <
        ∑ _a : L.Index, (1 : ℚ) := by
      apply Finset.sum_lt_sum_of_nonempty
      · have hcardpos : 0 < Fintype.card L.Index := by
          simpa [q, PolynomialLayout.card] using hqpos
        obtain ⟨a⟩ := Fintype.card_pos_iff.mp hcardpos
        exact ⟨a, Finset.mem_univ a⟩
      · intro a _ha
        exact hnot a
    have hleft : ∑ a : L.Index, (q : ℚ) * L.weight a =
        (q : ℚ) * ∑ a, L.weight a := by
      exact (Finset.mul_sum Finset.univ (fun a ↦ L.weight a) (q : ℚ)).symm
    have hright : ∑ _a : L.Index, (1 : ℚ) = q := by
      simp [q, PolynomialLayout.card]
    rw [hleft, hright] at hlt
    have hqnonneg : (0 : ℚ) ≤ q := by positivity
    have hcontra : (q : ℚ) ≤ (q : ℚ) * ∑ a, L.weight a := by
      calc
        (q : ℚ) = (q : ℚ) * 1 := by ring
        _ ≤ (q : ℚ) * ∑ a, L.weight a :=
          mul_le_mul_of_nonneg_left L.weight_total hqnonneg
    exact (not_lt_of_ge hcontra) hlt
  obtain ⟨a, ha⟩ := ha
  refine ⟨a, ?_⟩
  have hqw : (1 : ℚ) ≤ ((q : ℚ) * L.weight a) ^ d :=
    one_le_pow₀ ha
  have hcap := L.weight_capacity a
  have hqposQ : (0 : ℚ) < q := by exact_mod_cast hqpos
  have hmainQ : (Fintype.card V : ℚ) ≤
      (q : ℚ) ^ d * ((L.block a).card : ℚ) := by
    calc
      (Fintype.card V : ℚ) ≤
          ((q : ℚ) * L.weight a) ^ d * Fintype.card V := by
        simpa using mul_le_mul_of_nonneg_right hqw (by positivity : (0 : ℚ) ≤ Fintype.card V)
      _ = (q : ℚ) ^ d *
          (L.weight a ^ d * Fintype.card V) := by ring
      _ ≤ (q : ℚ) ^ d * (L.block a).card :=
        mul_le_mul_of_nonneg_left hcap (by positivity)
  have hmain : Fintype.card V ≤ q ^ d * (L.block a).card := by exact_mod_cast hmainQ
  exact hmain.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hqE d))

/-- Index type obtained by replacing one old layout block by `k` children. -/
abbrev RefinedLayoutIndex
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {E P d : ℕ}
    (L : PolynomialLayout G E P d) (a : L.Index) (k : ℕ) :=
  {i : L.Index // i ≠ a} ⊕ ULift.{u} (Fin k)

/-- Blocks in the refined layout. -/
def refinedLayoutBlock
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {E P d k : ℕ}
    (L : PolynomialLayout G E P d) (a : L.Index)
    (B : Blockade (V := V) k) : RefinedLayoutIndex L a k → Finset V
  | Sum.inl i => L.block i.1
  | Sum.inr p => B.block p.down

/-- The old pattern is retained between different parent blocks, while the
children are adjacent exactly when their pair is complete. -/
noncomputable def refinedLayoutPattern
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {E P d k : ℕ}
    (L : PolynomialLayout G E P d) (a : L.Index)
    (B : Blockade (V := V) k) : SimpleGraph (RefinedLayoutIndex L a k) where
  Adj x y := match x, y with
    | Sum.inl i, Sum.inl j => L.pattern.Adj i.1 j.1
    | Sum.inl i, Sum.inr _ => L.pattern.Adj i.1 a
    | Sum.inr _, Sum.inl j => L.pattern.Adj a j.1
    | Sum.inr p, Sum.inr q => (completePattern G B).Adj p.down q.down
  symm := by
    intro x y h
    cases x <;> cases y
    · exact L.pattern.symm h
    · exact L.pattern.symm h
    · exact L.pattern.symm h
    · exact (completePattern G B).symm h
  loopless := ⟨by
    intro x h
    cases x with
    | inl i => exact L.pattern.loopless.irrefl _ h
    | inr p => exact (completePattern G B).loopless.irrefl _ h⟩

/-- Replacing one heavy layout block by a short local blockade preserves all
layout invariants and increases the number of blocks by `k-1`. -/
theorem PolynomialLayout.refine
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {E P d k : ℕ} (L : PolynomialLayout G E P d) (a : L.Index)
    (B : Blockade (V := V) k)
    (hk : 2 ≤ k) (hkE : k < E)
    (hinside : B.IsInside (L.block a))
    (hkind : B.IsPure G ∨ B.IsESparse G P)
    (hwidth : ∀ i : Fin k, (L.block a).card ≤ k ^ d * (B.block i).card)
    (hheavy : Fintype.card V ≤ E ^ d * (L.block a).card) :
    ∃ L' : PolynomialLayout G E P d,
      L'.card = L.card - 1 + k := by
  classical
  letI : Fintype L.Index := L.fintypeIndex
  letI : DecidableEq L.Index := L.decidableEqIndex
  let New := RefinedLayoutIndex L a k
  let A : New → Finset V := refinedLayoutBlock L a B
  let J : SimpleGraph New := refinedLayoutPattern L a B
  let w : New → ℚ
    | Sum.inl i => L.weight i.1
    | Sum.inr _ => L.weight a / k
  have hdisjoint : ∀ {i j : New}, i ≠ j → Disjoint (A i) (A j) := by
    intro i j hij
    cases i with
    | inl i =>
        cases j with
        | inl j =>
            exact L.disjoint (by
              intro heq
              apply hij
              exact congrArg Sum.inl (Subtype.ext heq))
        | inr p =>
            apply Finset.disjoint_left.mpr
            intro x hxi hxj
            exact Finset.disjoint_left.mp (L.disjoint i.2) hxi
              (hinside p.down hxj)
    | inr p =>
        cases j with
        | inl j =>
            apply Finset.disjoint_left.mpr
            intro x hxi hxj
            exact Finset.disjoint_left.mp (L.disjoint j.2) hxj
              (hinside p.down hxi)
        | inr q =>
            apply B.disjoint
            intro hpq
            apply hij
            apply congrArg Sum.inr
            apply ULift.ext
            exact hpq
  have hcomplete : ∀ {i j : New}, J.Adj i j →
      ∀ x ∈ A i, ∀ y ∈ A j, G.Adj x y := by
    intro i j hij x hxi y hyj
    cases i with
    | inl i =>
        cases j with
        | inl j => exact L.pattern_complete hij x hxi y hyj
        | inr p => exact L.pattern_complete hij x hxi y (hinside p.down hyj)
    | inr p =>
        cases j with
        | inl j => exact L.pattern_complete hij x (hinside p.down hxi) y hyj
        | inr q => exact hij.2 x hxi y hyj
  have hw_nonneg : ∀ i : New, 0 ≤ w i := by
    intro i
    cases i with
    | inl i => exact L.weight_nonneg i.1
    | inr p => exact div_nonneg (L.weight_nonneg a) (by positivity)
  have hw_capacity : ∀ i : New,
      w i ^ d * (Fintype.card V : ℚ) ≤ ((A i).card : ℚ) := by
    intro i
    cases i with
    | inl i => exact L.weight_capacity i.1
    | inr p =>
        have hkQ : (0 : ℚ) < k := by exact_mod_cast (by omega : 0 < k)
        have hcap := L.weight_capacity a
        have hwidthQ : ((L.block a).card : ℚ) ≤
            (k : ℚ) ^ d * (B.block p.down).card := by exact_mod_cast hwidth p.down
        rw [show w (Sum.inr p) = L.weight a / k by rfl, div_pow]
        rw [show (L.weight a ^ d / (k : ℚ) ^ d) * Fintype.card V =
            (L.weight a ^ d * Fintype.card V) / (k : ℚ) ^ d by ring]
        apply (div_le_iff₀ (pow_pos hkQ d)).2
        calc
          L.weight a ^ d * (Fintype.card V : ℚ) ≤
              ((L.block a).card : ℚ) := hcap
          _ ≤ ((B.block p.down).card : ℚ) * (k : ℚ) ^ d := by
            rw [mul_comm]
            exact hwidthQ
  have hw_total : (1 : ℚ) ≤ ∑ i : New, w i := by
    have hchild : ∑ _p : ULift.{u} (Fin k), L.weight a / (k : ℚ) =
        L.weight a := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_ulift, Fintype.card_fin,
        nsmul_eq_mul]
      field_simp
    have hsplit := Fintype.sum_eq_add_sum_subtype_ne L.weight a
    calc
      (1 : ℚ) ≤ ∑ i : L.Index, L.weight i := L.weight_total
      _ = (∑ i : {i : L.Index // i ≠ a}, L.weight i.1) + L.weight a := by
        rw [hsplit]
        ring
      _ = (∑ i : {i : L.Index // i ≠ a}, w (Sum.inl i)) +
          ∑ p : ULift.{u} (Fin k), w (Sum.inr p) := by
        simp only [w, hchild]
      _ = ∑ i : New, w i := (Fintype.sum_sum_type w).symm
  have hwide : ∀ i : New,
      Fintype.card V ≤ E ^ (2 * d) * (A i).card := by
    intro i
    cases i with
    | inl i => exact L.wide i.1
    | inr p =>
        calc
          Fintype.card V ≤ E ^ d * (L.block a).card := hheavy
          _ ≤ E ^ d * (k ^ d * (B.block p.down).card) :=
            Nat.mul_le_mul_left _ (hwidth p.down)
          _ ≤ E ^ d * (E ^ d * (B.block p.down).card) := by
            gcongr
          _ = E ^ (2 * d) * (A (Sum.inr p)).card := by
            simp only [A, refinedLayoutBlock]
            rw [show 2 * d = d + d by omega, pow_add]
            ring
  have hwrongSub : wrongPairs G A J ⊆
      wrongPairs G L.block L.pattern ∪ internalWrongPairs G B := by
    intro z hz
    rw [wrongPairs, Finset.mem_filter] at hz
    obtain ⟨r, s, hrs, hzr, hzs, hzadj, hzpat⟩ := hz.2
    cases r with
    | inl r =>
        cases s with
        | inl s =>
            apply Finset.mem_union_left
            rw [wrongPairs, Finset.mem_filter]
            refine ⟨by simp, r.1, s.1, ?_, hzr, hzs, hzadj, hzpat⟩
            intro heq
            apply hrs
            exact congrArg Sum.inl (Subtype.ext heq)
        | inr s =>
            apply Finset.mem_union_left
            rw [wrongPairs, Finset.mem_filter]
            exact ⟨by simp, r.1, a, r.2, hzr, hinside s.down hzs, hzadj, hzpat⟩
    | inr r =>
        cases s with
        | inl s =>
            apply Finset.mem_union_left
            rw [wrongPairs, Finset.mem_filter]
            exact ⟨by simp, a, s.1, s.2.symm, hinside r.down hzr, hzs, hzadj, hzpat⟩
        | inr s =>
            apply Finset.mem_union_right
            have hrs' : r.down ≠ s.down := by
              intro heq
              apply hrs
              apply congrArg Sum.inr
              apply ULift.ext
              exact heq
            have hncomplete : ¬ CompletePair G B r.down s.down := by
              intro hc
              exact hzpat ⟨hrs', hc⟩
            apply Finset.mem_biUnion.mpr
            refine ⟨r.down, Finset.mem_univ _, ?_⟩
            apply Finset.mem_biUnion.mpr
            refine ⟨s.down, Finset.mem_erase.mpr ⟨hrs'.symm, Finset.mem_univ _⟩, ?_⟩
            simp only [if_neg hncomplete]
            rw [SimpleGraph.mem_interedges_iff]
            exact ⟨hzr, hzs, hzadj⟩
  have hinternal := internalWrongPairs_bound G B (L.block a) hinside hkind
  have hwrong : P * (wrongPairs G A J).card ≤
      (Fintype.card New - 1) * Fintype.card V ^ 2 := by
    have hcardWrong : (wrongPairs G A J).card ≤
        (wrongPairs G L.block L.pattern).card + (internalWrongPairs G B).card := by
      exact (Finset.card_le_card hwrongSub).trans (Finset.card_union_le _ _)
    have hrough : P * (wrongPairs G A J).card ≤
        ((L.card - 1) + 1) * Fintype.card V ^ 2 := by
      calc
        P * (wrongPairs G A J).card ≤
            P * ((wrongPairs G L.block L.pattern).card +
              (internalWrongPairs G B).card) := Nat.mul_le_mul_left P hcardWrong
        _ = P * (wrongPairs G L.block L.pattern).card +
              P * (internalWrongPairs G B).card := by ring
        _ ≤ (L.card - 1) * Fintype.card V ^ 2 +
              (L.block a).card ^ 2 := Nat.add_le_add L.wrong_budget hinternal
        _ ≤ (L.card - 1) * Fintype.card V ^ 2 +
              Fintype.card V ^ 2 := by
          gcongr
          exact Finset.card_le_card (Finset.subset_univ _)
        _ = ((L.card - 1) + 1) * Fintype.card V ^ 2 := by ring
    apply hrough.trans
    apply Nat.mul_le_mul_right
    change L.card - 1 + 1 ≤ Fintype.card New - 1
    simp only [New, RefinedLayoutIndex, Fintype.card_sum, Fintype.card_ulift,
      Fintype.card_fin]
    have hLpos : 0 < L.card := by
      have : 0 < Fintype.card L.Index := Fintype.card_pos_iff.mpr ⟨a⟩
      simpa [PolynomialLayout.card] using this
    have hsubcard : Fintype.card {i : L.Index // i ≠ a} = L.card - 1 := by
      rw [Fintype.card_subtype_compl (p := fun i : L.Index ↦ i = a)]
      simp [PolynomialLayout.card]
    rw [hsubcard]
    omega
  let L' : PolynomialLayout G E P d :=
    { Index := New
      block := A
      disjoint := hdisjoint
      pattern := J
      pattern_complete := hcomplete
      weight := w
      weight_nonneg := hw_nonneg
      weight_capacity := hw_capacity
      weight_total := hw_total
      wide := hwide
      wrong_budget := hwrong }
  refine ⟨L', ?_⟩
  change Fintype.card New = L.card - 1 + k
  simp only [New, RefinedLayoutIndex, Fintype.card_sum, Fintype.card_ulift,
    Fintype.card_fin]
  rw [Fintype.card_subtype_compl (p := fun i : L.Index ↦ i = a)]
  simp [PolynomialLayout.card]

end Lax57Proofs
