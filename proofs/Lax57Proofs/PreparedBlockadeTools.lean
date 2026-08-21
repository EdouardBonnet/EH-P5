import Lax57.PreparedHouseBlockade
import Lax57Proofs.MixedTools
import Mathlib.Tactic

namespace Lax57Proofs

open Finset
open scoped BigOperators SimpleGraph
open Lax57.GraphDefinitions

universe u

/-- The indices of blocks on which a vertex is mixed. -/
noncomputable def mixedIndices {V : Type u} [DecidableEq V] {k : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Blockade (V := V) k) (v : V) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter fun i ↦ IsMixedOn G v (B.block i)

/-- The union of a selected set of blocks. -/
def blockUnion {V : Type u} [DecidableEq V] {k : ℕ}
    (B : Blockade (V := V) k) (I : Finset (Fin k)) : Finset V :=
  I.biUnion B.block

theorem blockUnion_subset {V : Type u} [DecidableEq V] {k : ℕ}
    (B : Blockade (V := V) k) (I : Finset (Fin k)) {S : Finset V}
    (hinside : B.IsInside S) : blockUnion B I ⊆ S := by
  rw [blockUnion, Finset.biUnion_subset_iff_forall_subset]
  exact fun i _ ↦ hinside i

theorem card_blockUnion_of_eq {V : Type u} [DecidableEq V] {k m : ℕ}
    (B : Blockade (V := V) k) (I : Finset (Fin k))
    (hcard : ∀ i, (B.block i).card = m) :
    (blockUnion B I).card = I.card * m := by
  rw [blockUnion, Finset.card_biUnion]
  · simp [hcard]
  · intro i hi j hj hij
    exact B.disjoint hij

/-- A vertex mixed on two complete anticonnected blocks creates an induced
house. -/
theorem house_of_mixed_complete_blocks
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {v : V} {A B : Finset V}
    (hvA : v ∉ A) (hvB : v ∉ B)
    (hAB : ∀ x ∈ A, ∀ y ∈ B, G.Adj x y)
    (hantiA : (Gᶜ.induce (A : Set V)).Connected)
    (hantiB : (Gᶜ.induce (B : Set V)).Connected)
    (hmixA : IsMixedOn G v A) (hmixB : IsMixedOn G v B) :
    House ⊴ G := by
  obtain ⟨a, haA, a', ha'A, hva, hva', haa'⟩ :=
    exists_nonadj_pair_of_anticonnected_mixed G v A hantiA hmixA
  obtain ⟨b, hbB, b', hb'B, hvb, hvb', hbb'⟩ :=
    exists_nonadj_pair_of_anticonnected_mixed G v B hantiB hmixB
  have hcomp (x y : V) (hxy : x ≠ y) (hn : ¬ G.Adj x y) : Gᶜ.Adj x y := by
    simp only [SimpleGraph.compl_adj]
    exact ⟨hxy, hn⟩
  have hncomp (x y : V) (hxy : G.Adj x y) : ¬ Gᶜ.Adj x y := by
    intro hc
    exact hc.2 hxy
  have hp : P5 ⊴ Gᶜ := p5_isIndContained_of_vertices
      (G := Gᶜ)
      haa'
      (hcomp a' v (fun h ↦ hvA (h ▸ ha'A)) (by simpa [G.adj_comm] using hva'))
      (hcomp v b' (fun h ↦ hvB (h.symm ▸ hb'B)) hvb')
      (Gᶜ.adj_comm _ _ |>.mp hbb')
      (hncomp a v (G.adj_comm _ _ |>.mp hva))
      (hncomp a b' (hAB a haA b' hb'B))
      (hncomp a b (hAB a haA b hbB))
      (hncomp a' b' (hAB a' ha'A b' hb'B))
      (hncomp a' b (hAB a' ha'A b hbB))
      (hncomp v b hvb)
  simpa [House] using hp.compl

/-- A heavy mixed-index set is long enough to absorb both the internal-block
degree and the cross-block degree. -/
theorem heavy_index_bounds {Q d r : ℕ} (hQ : 8 ≤ Q) (hd : 1 ≤ d)
    (hheavy : Q ^ (4 * d) ≤ Q * r) :
    4 * Q ^ (2 * d) ≤ r ∧ 4 * Q ^ (2 * d) ≤ Q ^ (4 * d) := by
  have hQpos : 0 < Q := by omega
  have hexp : 2 * d + 2 ≤ 4 * d := by omega
  have hfour : 4 * Q ^ (2 * d) * Q ≤ Q ^ (4 * d) := by
    calc
      4 * Q ^ (2 * d) * Q ≤ Q * Q ^ (2 * d) * Q := by
        gcongr
        omega
      _ = Q ^ (2 * d + 2) := by
        rw [show Q * Q ^ (2 * d) * Q = Q ^ (2 * d) * Q ^ 2 by ring,
          ← pow_add]
      _ ≤ Q ^ (4 * d) := Nat.pow_le_pow_right hQpos hexp
  constructor
  · apply Nat.le_of_mul_le_mul_left (c := Q)
    · calc
        Q * (4 * Q ^ (2 * d)) = 4 * Q ^ (2 * d) * Q := by ring
        _ ≤ Q ^ (4 * d) := hfour
        _ ≤ Q * r := hheavy
    · exact hQpos
  · calc
      4 * Q ^ (2 * d) ≤ Q * Q ^ (2 * d) := by gcongr <;> omega
      _ = Q ^ (2 * d + 1) := by rw [pow_succ']
      _ ≤ Q ^ (4 * d) := Nat.pow_le_pow_right hQpos (by omega)

/-- The degree in a union of equal blocks is bounded by one whole block plus
the sparse contributions from all other blocks. -/
theorem degree_blockUnion_bound
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k P m : ℕ}
    (B : Blockade (V := V) k) (I : Finset (Fin k))
    (hcard : ∀ i, (B.block i).card = m)
    (hsparse : ∀ {i j : Fin k}, i ∈ I → j ∈ I → i ≠ j →
      ESparseTo G P (B.block i) (B.block j))
    (x : {v : V // v ∈ blockUnion B I}) :
    P * (G.induce (blockUnion B I : Set V)).degree x ≤
      P * m + I.card * m := by
  classical
  have hdeg : (G.induce (blockUnion B I : Set V)).degree x =
      (neighborsIn G (blockUnion B I) x.1).card := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
      ← Finset.card_map
        (f := Function.Embedding.subtype (fun v ↦ v ∈ blockUnion B I))]
    congr 1
    ext y
    simp [neighborsIn, G.adj_comm, and_comm]
  obtain ⟨i, hiI, hxi⟩ := Finset.mem_biUnion.mp x.2
  have hneighbors : neighborsIn G (blockUnion B I) x.1 =
      I.biUnion fun j ↦ neighborsIn G (B.block j) x.1 := by
    ext y
    simp only [neighborsIn, Finset.mem_filter, blockUnion, Finset.mem_biUnion]
    aesop
  rw [hdeg, hneighbors]
  calc
    P * (I.biUnion fun j ↦ neighborsIn G (B.block j) x.1).card
        ≤ P * ∑ j ∈ I, (neighborsIn G (B.block j) x.1).card :=
      Nat.mul_le_mul_left P Finset.card_biUnion_le
    _ = ∑ j ∈ I, P * (neighborsIn G (B.block j) x.1).card := by
      rw [Finset.mul_sum]
    _ ≤ ∑ j ∈ I, (m + if j = i then P * m else 0) := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hji : j = i
      · subst j
        have hncard : (neighborsIn G (B.block i) x.1).card ≤ m := by
          rw [← hcard i]
          apply Finset.card_le_card
          exact Finset.filter_subset _ _
        simp only [if_pos rfl]
        exact (Nat.mul_le_mul_left P hncard).trans (Nat.le_add_left _ _)
      · simp only [if_neg hji, add_zero]
        simpa [hcard j] using hsparse hiI hj (Ne.symm hji) x.1 hxi
    _ = I.card * m + P * m := by simp [hiI, Finset.sum_add_distrib]
    _ = P * m + I.card * m := by omega

/-- A heavy set of pairwise noncomplete mixed blocks has a much sparser
union. -/
theorem ESparse_blockUnion_of_heavy_sparse
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {Q d m : ℕ}
    (hQ : 8 ≤ Q) (hd : 1 ≤ d)
    {B : Blockade (V := V) (Q ^ (4 * d))}
    (hcard : ∀ i, (B.block i).card = m)
    (I : Finset (Fin (Q ^ (4 * d))))
    (hheavy : Q ^ (4 * d) ≤ Q * I.card)
    (hsparse : ∀ {i j}, i ∈ I → j ∈ I → i ≠ j →
      ESparseTo G (Q ^ (4 * d)) (B.block i) (B.block j)) :
    ESparse G (Q ^ (2 * d)) (blockUnion B I) := by
  intro x
  let E := Q ^ (2 * d)
  let P := Q ^ (4 * d)
  have hPpos : 0 < P := by positivity
  obtain ⟨h4Er, h4EP⟩ := heavy_index_bounds hQ hd hheavy
  have h2Er : 2 * E ≤ I.card := by simpa [E] using h4Er.trans' (by omega)
  have h2EP : 2 * E ≤ P := by simpa [E, P] using h4EP.trans' (by omega)
  have hdeg := degree_blockUnion_bound G B I hcard hsparse x
  have htwice : 2 * (P * (E * (G.induce (blockUnion B I : Set V)).degree x)) ≤
      2 * (P * (I.card * m)) := by
    calc
      2 * (P * (E * (G.induce (blockUnion B I : Set V)).degree x)) =
          2 * E * (P * (G.induce (blockUnion B I : Set V)).degree x) := by ring
      _ ≤ 2 * E * (P * m + I.card * m) :=
        Nat.mul_le_mul_left (2 * E) hdeg
      _ = (2 * E) * P * m + (2 * E) * I.card * m := by ring
      _ ≤ I.card * P * m + P * I.card * m := by
        exact Nat.add_le_add
          (Nat.mul_le_mul_right m (Nat.mul_le_mul_right P h2Er))
          (Nat.mul_le_mul_right m (Nat.mul_le_mul_right I.card h2EP))
      _ = 2 * (P * (I.card * m)) := by ring
  have hcancel2 : P * (E * (G.induce (blockUnion B I : Set V)).degree x) ≤
      P * (I.card * m) := by omega
  have hcancelP : E * (G.induce (blockUnion B I : Set V)).degree x ≤
      I.card * m := Nat.le_of_mul_le_mul_left hcancel2 hPpos
  simpa [E, card_blockUnion_of_eq B I hcard] using hcancelP

/-- Cardinality lower bound for a union of disjoint blocks of common minimum
size. -/
theorem mul_le_card_blockUnion
    {V : Type u} [DecidableEq V] {k m : ℕ}
    (B : Blockade (V := V) k) (I : Finset (Fin k))
    (hmin : ∀ i, m ≤ (B.block i).card) :
    I.card * m ≤ (blockUnion B I).card := by
  rw [blockUnion, Finset.card_biUnion]
  · simpa using Finset.sum_le_sum fun i (_ : i ∈ I) ↦ hmin i
  · intro i hi j hj hij
    exact B.disjoint hij

/-- The heavy-index numerical estimate with the factor `8Q²` allowed between
the smallest and largest prepared blocks. -/
theorem heavy_index_bounds_scaled {Q d r : ℕ} (hQ : 8 ≤ Q) (hd : 3 ≤ d)
    (hheavy : Q ^ (4 * d) ≤ Q * r) :
    16 * Q ^ 2 * Q ^ (2 * d) ≤ r ∧
      16 * Q ^ 2 * Q ^ (2 * d) ≤ Q ^ (4 * d) := by
  have hQpos : 0 < Q := by omega
  have h16 : 16 ≤ Q ^ 2 := by nlinarith
  have hbase : 16 * Q ^ 2 * Q ^ (2 * d) ≤ Q ^ (2 * d + 4) := by
    calc
      16 * Q ^ 2 * Q ^ (2 * d) ≤ Q ^ 2 * Q ^ 2 * Q ^ (2 * d) := by gcongr
      _ = Q ^ (2 * d + 4) := by rw [pow_add]; ring
  have hexpP : 2 * d + 4 ≤ 4 * d := by omega
  have htoP : 16 * Q ^ 2 * Q ^ (2 * d) ≤ Q ^ (4 * d) :=
    hbase.trans (Nat.pow_le_pow_right hQpos hexpP)
  constructor
  · apply Nat.le_of_mul_le_mul_left (c := Q)
    · calc
        Q * (16 * Q ^ 2 * Q ^ (2 * d)) ≤ Q ^ (2 * d + 5) := by
          calc
            Q * (16 * Q ^ 2 * Q ^ (2 * d)) ≤
                Q * (Q ^ 2 * Q ^ 2 * Q ^ (2 * d)) := Nat.mul_le_mul_left Q (by gcongr)
            _ = Q ^ (2 * d + 5) := by rw [pow_add]; ring
        _ ≤ Q ^ (4 * d) := Nat.pow_le_pow_right hQpos (by omega)
        _ ≤ Q * r := hheavy
    · exact hQpos
  · exact htoP

/-- Sparse-union estimate when all prepared block sizes lie between `m` and
`8Q²m`. -/
theorem ESparse_blockUnion_of_heavy_sparse_range
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {Q d m : ℕ}
    (hQ : 8 ≤ Q) (hd : 3 ≤ d)
    {B : Blockade (V := V) (Q ^ (4 * d))}
    (hsize : ∀ i, m ≤ (B.block i).card ∧ (B.block i).card ≤ 8 * Q ^ 2 * m)
    (I : Finset (Fin (Q ^ (4 * d))))
    (hheavy : Q ^ (4 * d) ≤ Q * I.card)
    (hsparse : ∀ {i j}, i ∈ I → j ∈ I → i ≠ j →
      ESparseTo G (Q ^ (4 * d)) (B.block i) (B.block j)) :
    ESparse G (Q ^ (2 * d)) (blockUnion B I) := by
  intro x
  let E := Q ^ (2 * d)
  let P := Q ^ (4 * d)
  let C := 8 * Q ^ 2
  have hPpos : 0 < P := by positivity
  obtain ⟨hscaledR, hscaledP⟩ := heavy_index_bounds_scaled hQ hd hheavy
  have h2CEr : 2 * C * E ≤ I.card := by
    change 2 * (8 * Q ^ 2) * Q ^ (2 * d) ≤ I.card
    nlinarith
  have h2CEP : 2 * C * E ≤ P := by
    change 2 * (8 * Q ^ 2) * Q ^ (2 * d) ≤ Q ^ (4 * d)
    nlinarith
  have hdeg : P * (G.induce (blockUnion B I : Set V)).degree x ≤
      P * (C * m) + I.card * (C * m) := by
    classical
    have hdegEq : (G.induce (blockUnion B I : Set V)).degree x =
        (neighborsIn G (blockUnion B I) x.1).card := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree,
        ← Finset.card_map
          (f := Function.Embedding.subtype (fun v ↦ v ∈ blockUnion B I))]
      congr 1
      ext y
      simp [neighborsIn, G.adj_comm, and_comm]
    obtain ⟨i, hiI, hxi⟩ := Finset.mem_biUnion.mp x.2
    have hneighbors : neighborsIn G (blockUnion B I) x.1 =
        I.biUnion fun j ↦ neighborsIn G (B.block j) x.1 := by
      ext y
      simp only [neighborsIn, Finset.mem_filter, blockUnion, Finset.mem_biUnion]
      aesop
    rw [hdegEq, hneighbors]
    calc
      P * (I.biUnion fun j ↦ neighborsIn G (B.block j) x.1).card
          ≤ P * ∑ j ∈ I, (neighborsIn G (B.block j) x.1).card :=
        Nat.mul_le_mul_left P Finset.card_biUnion_le
      _ = ∑ j ∈ I, P * (neighborsIn G (B.block j) x.1).card := by
        rw [Finset.mul_sum]
      _ ≤ ∑ j ∈ I, (C * m + if j = i then P * (C * m) else 0) := by
        apply Finset.sum_le_sum
        intro j hj
        by_cases hji : j = i
        · subst j
          have hncard : (neighborsIn G (B.block i) x.1).card ≤ C * m :=
            (Finset.card_le_card (Finset.filter_subset _ _)).trans (hsize i).2
          simp only [if_pos rfl]
          exact (Nat.mul_le_mul_left P hncard).trans (Nat.le_add_left _ _)
        · simp only [if_neg hji, add_zero]
          exact (hsparse hiI hj (Ne.symm hji) x.1 hxi).trans (hsize j).2
      _ = I.card * (C * m) + P * (C * m) := by simp [hiI, Finset.sum_add_distrib]
      _ = P * (C * m) + I.card * (C * m) := by omega
  have htwice : 2 * (P * (E * (G.induce (blockUnion B I : Set V)).degree x)) ≤
      2 * (P * (I.card * m)) := by
    calc
      2 * (P * (E * (G.induce (blockUnion B I : Set V)).degree x)) =
          2 * E * (P * (G.induce (blockUnion B I : Set V)).degree x) := by ring
      _ ≤ 2 * E * (P * (C * m) + I.card * (C * m)) :=
        Nat.mul_le_mul_left (2 * E) hdeg
      _ = (2 * C * E) * P * m + (2 * C * E) * I.card * m := by ring
      _ ≤ I.card * P * m + P * I.card * m := by
        exact Nat.add_le_add
          (Nat.mul_le_mul_right m (Nat.mul_le_mul_right P h2CEr))
          (Nat.mul_le_mul_right m (Nat.mul_le_mul_right I.card h2CEP))
      _ = 2 * (P * (I.card * m)) := by ring
  have hcancel2 : P * (E * (G.induce (blockUnion B I : Set V)).degree x) ≤
      P * (I.card * m) := by omega
  have hcancelP : E * (G.induce (blockUnion B I : Set V)).degree x ≤
      I.card * m := Nat.le_of_mul_le_mul_left hcancel2 hPpos
  exact hcancelP.trans (mul_le_card_blockUnion B I fun i ↦ (hsize i).1)

/-- Double-counting a finite incidence relation: if every row has at most
`L/Q` incidences, some column has at most `N/Q` incidences. -/
theorem exists_column_with_small_fiber
    {W : Type u} [DecidableEq W] {L Q N : ℕ}
    (O : Finset W) (p : Fin L → W → Prop)
    [∀ v, DecidablePred fun i ↦ p i v]
    [∀ i, DecidablePred fun v ↦ p i v]
    (hL : 0 < L) (hON : O.card ≤ N)
    (hrow : ∀ v ∈ O,
      Q * ((Finset.univ : Finset (Fin L)).filter fun i ↦ p i v).card ≤ L) :
    ∃ i : Fin L, Q * (O.filter fun v ↦ p i v).card ≤ N := by
  classical
  let total := ∑ i : Fin L, (O.filter fun v ↦ p i v).card
  have hdouble : total = ∑ v ∈ O,
      ((Finset.univ : Finset (Fin L)).filter fun i ↦ p i v).card := by
    simp_rw [total, Finset.card_filter]
    rw [Finset.sum_comm]
  by_contra hnone
  push_neg at hnone
  have hlower : L * (N + 1) ≤ Q * total := by
    calc
      L * (N + 1) = ∑ _i : Fin L, (N + 1) := by simp
      _ ≤ ∑ i : Fin L, Q * (O.filter fun v ↦ p i v).card := by
        apply Finset.sum_le_sum
        intro i hi
        have := hnone i
        omega
      _ = Q * total := by rw [Finset.mul_sum]
  have hupper : Q * total ≤ L * N := by
    rw [hdouble, Finset.mul_sum]
    calc
      ∑ v ∈ O,
          Q * ((Finset.univ : Finset (Fin L)).filter fun i ↦ p i v).card
          ≤ ∑ _v ∈ O, L := by
            apply Finset.sum_le_sum
            intro v hv
            exact hrow v hv
      _ = O.card * L := by simp
      _ ≤ N * L := Nat.mul_le_mul_right L hON
      _ = L * N := by ring
  have hstrict : L * N < L * (N + 1) := by nlinarith
  exact (not_lt_of_ge (hlower.trans hupper)) hstrict

/-- The cleared neighbor count in an induced set is exactly its induced
degree. -/
theorem card_neighborsIn_eq_degree
    {V : Type u} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (v : {x : V // x ∈ S}) :
    (neighborsIn G S v.1).card = (G.induce (S : Set V)).degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← Finset.card_map
      (f := Function.Embedding.subtype (fun x ↦ x ∈ S))]
  congr 1
  ext y
  simp [neighborsIn, G.adj_comm, and_comm]

/-- Every reciprocal parameter is sparse on a singleton. -/
theorem ESparse.singleton
    {V : Type u} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (E : ℕ) (v : V) : ESparse G E {v} := by
  intro x
  have hsub : Subsingleton {z : V // z ∈ ({v} : Finset V)} := by infer_instance
  letI := hsub
  simp [SimpleGraph.degree_eq_zero_of_subsingleton]

end Lax57Proofs
