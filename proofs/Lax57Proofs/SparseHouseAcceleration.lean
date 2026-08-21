import Lax57.SparseHouseAcceleration
import Lax57.SparseHouseTrichotomy
import Lax57Proofs.AccelerationBounds
import Lax57Proofs.PeelingTools
import Lax57Proofs.Iteration
import Mathlib.Tactic

namespace Lax57Proofs

open Finset
open scoped SimpleGraph
open Lax57.GraphDefinitions

universe u

/-- Sparsity inherited by a large subset, using a factor-two reserve in the
original reciprocal parameter. -/
theorem ESparse.on_large_subset
    {V : Type u} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {E Q : ℕ} {S U : Finset V}
    (hUS : U ⊆ S) (hlarge : S.card ≤ 2 * U.card)
    (hreserve : 2 * Q ≤ E) (hsparse : ESparse G E S) :
    ESparse G Q U := by
  intro v
  let vS : {x : V // x ∈ S} := ⟨v.1, hUS v.2⟩
  have hdeg := degree_induce_finset_mono G hUS v
  have hbase := hsparse vS
  have htwice : 2 * (Q * (G.induce (U : Set V)).degree v) ≤
      2 * U.card := by
    calc
      2 * (Q * (G.induce (U : Set V)).degree v) =
          (2 * Q) * (G.induce (U : Set V)).degree v := by ring
      _ ≤ E * (G.induce (U : Set V)).degree v :=
        Nat.mul_le_mul_right _ hreserve
      _ ≤ E * (G.induce (S : Set V)).degree vS :=
        Nat.mul_le_mul_left E hdeg
      _ ≤ S.card := hbase
      _ ≤ 2 * U.card := hlarge
  omega

/-- The cumulative loss bound in a peeling sequence keeps its remainder at
least half as large as the original set for the first `R` steps. -/
theorem AnticompletePeeling.remainder_large
    {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    {S : Finset V} {Q loss n R : ℕ}
    (P : AnticompletePeeling G S Q loss n)
    (hnR : n ≤ R) (hRpos : 0 < R) (hslack : 6 * R ≤ Q) :
    S.card ≤ 2 * P.remainder.card := by
  have h6n : 6 * n ≤ Q := (Nat.mul_le_mul_left 6 hnR).trans hslack
  have hmul : Q * (2 * (S.card - P.remainder.card)) ≤ Q * S.card := by
    calc
      Q * (2 * (S.card - P.remainder.card)) =
          2 * (Q * (S.card - P.remainder.card)) := by ring
      _ ≤ 2 * (3 * n * S.card) := Nat.mul_le_mul_left 2 P.removed_small
      _ = (6 * n) * S.card := by ring
      _ ≤ Q * S.card := Nat.mul_le_mul_right S.card h6n
  have hQpos : 0 < Q := (by positivity : 0 < 6 * R).trans_le hslack
  have hremoved : 2 * (S.card - P.remainder.card) ≤ S.card :=
    Nat.le_of_mul_le_mul_left hmul hQpos
  have hcard : P.remainder.card ≤ S.card :=
    Finset.card_le_card P.remainder_subset
  omega

/-- Taking an initial segment preserves all blockade predicates needed by
the acceleration argument. -/
theorem takeBlockade_inside_complete
    {V : Type u} [DecidableEq V] {G : SimpleGraph V} {r k : ℕ}
    (B : Blockade (V := V) k) (h : r ≤ k) {S : Finset V}
    (hinside : B.IsInside S) (hcomplete : B.IsComplete G) :
    (takeBlockade B h).IsInside S ∧ (takeBlockade B h).IsComplete G := by
  constructor
  · intro i
    exact hinside ⟨i, i.isLt.trans_le h⟩
  · intro i j hij x hxi y hyj
    apply hcomplete
      (fun heq ↦ hij (by apply Fin.ext; simpa using congrArg Fin.val heq))
      x hxi y hyj

/--
---
conclusion: Lax57.SparseHouseAcceleration.sparse_house_acceleration
assumptions:
  - Lax57.SparseHouseTrichotomy.sparse_house_trichotomy
---
Apply the sparse-house trichotomy at $Q=R^2/2$. Its sparse and complete
outcomes give the required alternatives after rescaling. In the peel
outcome, repeatedly remove the anticomplete piece. Each removal loses at
most a $3/Q$ fraction of the current set, so after $R$ steps at least half
of the original set remains. The removed pieces form the required
anticomplete $R$-blockade.

# Attribution

This is the maximal-peeling proof of Lemma 7.2 of
Nguyen, Scott, and Seymour, stated with square reciprocal parameters and
cleared denominators.
-/
theorem sparse_house_acceleration :
    ∃ d : ℕ, 2 ≤ d ∧
      ∀ R : ℕ, 64 ≤ R →
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V),
          IsHouseFree G → ESparse G (R ^ 2) S →
            (∃ T : Finset V, T ⊆ S ∧
                S.card ≤ R ^ (32 * d ^ 3) * T.card ∧
                  ESparse G (R ^ (2 * d)) T) ∨
              (∃ B : Blockade (V := V) R,
                B.IsInside S ∧ B.IsUniform G ∧
                  ∀ i : Fin R,
                    S.card ≤ R ^ (36 * d ^ 3) * (B.block i).card) := by
  obtain ⟨d₀, hd₀, htri⟩ :=
    Lax57.SparseHouseTrichotomy.sparse_house_trichotomy
  let d := 3 * d₀ / 2
  obtain ⟨hd, hdscale, hrefineExp, hblockExp⟩ :=
    acceleration_exponent_bounds hd₀
  refine ⟨d, by simpa [d] using hd, ?_⟩
  intro R hR V _ _ G _ S hfree hsparse
  let Q := R ^ 2 / 2
  obtain ⟨hQ8, hRQ, hslack, hreserve, hcubic⟩ := half_square_bounds hR
  have hQR2 : Q ≤ R ^ 2 := (Nat.div_le_self _ _)
  have hsparsity : R ^ (2 * d) ≤ Q ^ (2 * d₀) :=
    acceleration_sparsity_bound (by omega) hcubic (by simpa [d] using hdscale)
  have hrefineCoeff : 2 * Q ^ (30 * d₀ ^ 3) ≤ R ^ (32 * d ^ 3) := by
    apply two_mul_scale_power (by omega) hQR2
    have heq : 2 * (30 * d₀ ^ 3) + 1 = 60 * d₀ ^ 3 + 1 := by ring
    rw [heq]
    simpa [d] using hrefineExp
  have hblockCoeff : 2 * Q ^ (33 * d₀ ^ 3) ≤ R ^ (36 * d ^ 3) := by
    apply two_mul_scale_power (by omega) hQR2
    have heq : 2 * (33 * d₀ ^ 3) + 1 = 66 * d₀ ^ 3 + 1 := by ring
    rw [heq]
    simpa [d] using hblockExp
  let Outcome : Prop :=
    (∃ T : Finset V, T ⊆ S ∧
        S.card ≤ R ^ (32 * d ^ 3) * T.card ∧
          ESparse G (R ^ (2 * d)) T) ∨
      (∃ B : Blockade (V := V) R,
        B.IsInside S ∧ B.IsUniform G ∧
          ∀ i : Fin R,
            S.card ≤ R ^ (36 * d ^ 3) * (B.block i).card)
  by_contra hOutcome
  have hpeel : ∀ n : ℕ, n ≤ R →
      ∃ P : AnticompletePeeling G S Q (33 * d₀ ^ 3) n, True := by
    intro n hnR
    induction n with
    | zero => exact ⟨AnticompletePeeling.nil G S Q (33 * d₀ ^ 3), trivial⟩
    | succ n ih =>
        have hnR' : n ≤ R := by omega
        obtain ⟨P, -⟩ := ih hnR'
        have hlarge := P.remainder_large hnR' (by omega) hslack
        have hsparseRem : ESparse G Q P.remainder :=
          ESparse.on_large_subset G P.remainder_subset hlarge hreserve hsparse
        rcases htri Q hQ8 G P.remainder hfree hsparseRem with
          hrefine | hcomplete | hnext
        · obtain ⟨T, hTrem, hTcard, hTsparse⟩ := hrefine
          exfalso
          apply hOutcome
          apply Or.inl
          refine ⟨T, hTrem.trans P.remainder_subset, ?_,
            ESparse.mono_parameter G hsparsity hTsparse⟩
          calc
            S.card ≤ 2 * P.remainder.card := hlarge
            _ ≤ 2 * (Q ^ (30 * d₀ ^ 3) * T.card) :=
              Nat.mul_le_mul_left 2 hTcard
            _ = (2 * Q ^ (30 * d₀ ^ 3)) * T.card := by ring
            _ ≤ R ^ (32 * d ^ 3) * T.card :=
              Nat.mul_le_mul_right T.card hrefineCoeff
        · obtain ⟨B, hinside, hcomplete, hwidth⟩ := hcomplete
          exfalso
          apply hOutcome
          apply Or.inr
          let C := takeBlockade B hRQ
          obtain ⟨hCinside, hCcomplete⟩ :=
            takeBlockade_inside_complete B hRQ hinside hcomplete
          have hCinsideS : C.IsInside S := fun i ↦
            (hCinside i).trans P.remainder_subset
          refine ⟨C, hCinsideS, Or.inl hCcomplete, ?_⟩
          intro i
          have hBi := hwidth ⟨i, i.isLt.trans_le hRQ⟩
          calc
            S.card ≤ 2 * P.remainder.card := hlarge
            _ ≤ 2 * (Q ^ (33 * d₀ ^ 3) *
                (B.block ⟨i, i.isLt.trans_le hRQ⟩).card) :=
              Nat.mul_le_mul_left 2 hBi
            _ = (2 * Q ^ (33 * d₀ ^ 3)) * (C.block i).card := by
              simp only [C, Blockade.take_block]
              ring
            _ ≤ R ^ (36 * d ^ 3) * (C.block i).card :=
              Nat.mul_le_mul_right (C.block i).card hblockCoeff
        · obtain ⟨X, Y, hX, hY, hXY, hanti, hXwide, hremoved⟩ := hnext
          refine ⟨P.snoc X Y hX hY hXY hanti hlarge hXwide hremoved, trivial⟩
  obtain ⟨P, -⟩ := hpeel R le_rfl
  apply hOutcome
  apply Or.inr
  refine ⟨P.blocks, P.blocks_inside, Or.inr P.blocks_anticomplete, ?_⟩
  intro i
  exact (P.blocks_wide i).trans <|
    Nat.mul_le_mul_right (P.blocks.block i).card hblockCoeff

end Lax57Proofs
