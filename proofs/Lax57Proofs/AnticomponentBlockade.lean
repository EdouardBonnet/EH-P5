import Lax57.AnticomponentBlockade
import Lax57Proofs.ComponentTools
import Lax57Proofs.WeightedGrouping
import Mathlib.Tactic

namespace Lax57Proofs

open Finset
open scoped BigOperators SimpleGraph
open Lax57.GraphDefinitions

universe u

/-- The elementary numerical reserve for grouping small components. -/
private theorem component_grouping_capacity {N Q : ℕ}
    (hQ : 2 ≤ Q) (hN : Q ^ 2 < N) :
    Q * (N / (4 * Q ^ 3) + 1 + N / Q ^ 2) ≤ N := by
  let a := N / (4 * Q ^ 3)
  let b := N / Q ^ 2
  have hQpos : 0 < Q := by omega
  have hQ2pos : 0 < Q ^ 2 := by positivity
  have hKpos : 0 < 4 * Q ^ 3 := by positivity
  have ha : 4 * Q ^ 3 * a ≤ N := by
    simpa [a] using Nat.mul_div_le N (4 * Q ^ 3)
  have hb : Q ^ 2 * b ≤ N := by
    simpa [b] using Nat.mul_div_le N (Q ^ 2)
  have hbpos : 0 < b := Nat.div_pos hN.le hQ2pos
  have hab : a + 1 ≤ b := by
    rw [Nat.le_div_iff_mul_le hQ2pos]
    by_cases ha0 : a = 0
    · rw [ha0]
      simpa using hN.le
    · have hapos : 0 < a := Nat.pos_of_ne_zero ha0
      calc
        (a + 1) * Q ^ 2 ≤ (4 * Q * a) * Q ^ 2 := by
          apply Nat.mul_le_mul_right
          nlinarith
        _ = 4 * Q ^ 3 * a := by ring
        _ ≤ N := ha
  have hab' : a + 1 ≤ (Q - 1) * b := by
    calc
      a + 1 ≤ b := hab
      _ ≤ (Q - 1) * b := by
        apply Nat.le_mul_of_pos_left
        omega
  change Q * (a + 1 + b) ≤ N
  calc
    Q * (a + 1 + b) = Q * (a + 1) + Q * b := by ring
    _ ≤ Q * ((Q - 1) * b) + Q * b := by gcongr
    _ = Q ^ 2 * b := by
      calc
        Q * ((Q - 1) * b) + Q * b = Q * (((Q - 1 + 1) * b)) := by ring
        _ = Q ^ 2 * b := by
          rw [Nat.sub_add_cancel (show 1 ≤ Q by omega)]
          ring
    _ ≤ N := hb

/-- The component supports of a finite graph partition its vertices. -/
private theorem sum_component_support_cards
    {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [Fintype H.ConnectedComponent]
    [∀ C : H.ConnectedComponent, Fintype C.supp] :
    ∑ C : H.ConnectedComponent, C.supp.toFinset.card = Fintype.card W := by
  classical
  have hdisj : ∀ C ∈ (Finset.univ : Finset H.ConnectedComponent),
      ∀ D ∈ (Finset.univ : Finset H.ConnectedComponent), C ≠ D →
        Disjoint C.supp.toFinset D.supp.toFinset := by
    intro C _ D _ hCD
    rw [Finset.disjoint_left]
    intro x hxC hxD
    exact Set.disjoint_left.mp (H.pairwise_disjoint_supp_connectedComponent hCD)
      (by simpa using hxC) (by simpa using hxD)
  have hcover : (Finset.univ : Finset H.ConnectedComponent).biUnion
      (fun C ↦ C.supp.toFinset) = (Finset.univ : Finset W) := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · exact fun _ ↦ trivial
    · intro _
      exact ⟨H.connectedComponentMk x, by
        simpa using H.ConnectedComponent.connectedComponentMk_mem (v := x)⟩
  rw [← show (Finset.univ : Finset W).card = Fintype.card W by simp,
    ← hcover, Finset.card_biUnion]
  intro C _ D _ hCD
  change Disjoint C.supp.toFinset D.supp.toFinset
  exact hdisj C (Finset.mem_univ _) D (Finset.mem_univ _) hCD

/-- Map the support of a component of an induced graph back to the ambient
vertex type; it remains connected. -/
private theorem mapped_component_connected
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V)
    (C : (G.induce (T : Set V)).ConnectedComponent) :
    let e : {x : V // x ∈ T} ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
    (G.induce ((C.supp.toFinset.map e : Finset V) : Set V)).Connected := by
  classical
  let H := G.induce (T : Set V)
  let e : {x : V // x ∈ T} ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  let J : Finset V := C.supp.toFinset.map e
  let φfun : C → {z : V // z ∈ (J : Set V)} := fun x ↦
    ⟨x.1.1, by
      change x.1.1 ∈ J
      exact Finset.mem_map.mpr ⟨x.1, by simpa using x.2, rfl⟩⟩
  let φ : C.toSimpleGraph →g G.induce (J : Set V) :=
    ⟨φfun, by intro x y hxy; exact hxy⟩
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨xT, hxC, hxy⟩ := Finset.mem_map.mp y.property
    refine ⟨⟨xT, by simpa using hxC⟩, ?_⟩
    exact Subtype.ext hxy
  exact C.connected_toSimpleGraph.map φ hsurj

/--
---
conclusion: Lax57.AnticomponentBlockade.anticomponent_or_complete_blockade
---
Consider the connected components of the complement induced on $T$. A
component of size at least $|T|/Q^2$ gives the first outcome. Otherwise,
greedily group whole components into $Q$ disjoint families, each of size at
least $|T|/(4Q^3)$. Distinct families are anticomplete in the complement and
therefore complete in $G$.
-/
theorem anticomponent_or_complete_blockade :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) (Q : ℕ),
      2 ≤ Q →
        ( (∃ J : Finset V, J ⊆ T ∧
              (Gᶜ.induce (J : Set V)).Connected ∧
                T.card ≤ Q ^ 2 * J.card) ∨
          (∃ C : Blockade (V := V) Q,
              C.IsInside T ∧ C.IsComplete G ∧
                ∀ i : Fin Q,
                  T.card ≤ 4 * Q ^ 3 * (C.block i).card) ) := by
  intro V _ _ G _ T Q hQ
  classical
  by_cases hT : T = ∅
  · subst T
    apply Or.inr
    let C : Blockade (V := V) Q :=
      { block := fun _ ↦ ∅
        disjoint := by simp }
    refine ⟨C, ?_, ?_, ?_⟩ <;> simp [C, Blockade.IsInside, Blockade.IsComplete]
  let H := Gᶜ.induce (T : Set V)
  let e : {x : V // x ∈ T} ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  letI : Fintype H.ConnectedComponent := Fintype.ofFinite _
  let weight : H.ConnectedComponent → ℕ := fun C ↦ C.supp.toFinset.card
  have hsum : ∑ C : H.ConnectedComponent, weight C = T.card := by
    change (∑ C : H.ConnectedComponent, C.supp.toFinset.card) = T.card
    simpa [H] using sum_component_support_cards H
  by_cases hlarge : ∃ C : H.ConnectedComponent, T.card ≤ Q ^ 2 * weight C
  · obtain ⟨C, hCwide⟩ := hlarge
    apply Or.inl
    let J : Finset V := C.supp.toFinset.map e
    refine ⟨J, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨xT, _hxC, rfl⟩ := Finset.mem_map.mp hx
      exact xT.property
    · change (Gᶜ.induce (J : Set V)).Connected
      simpa [H, J, e] using mapped_component_connected Gᶜ T C
    · simpa [J, weight] using hCwide
  · have hsmall (C : H.ConnectedComponent) :
        weight C ≤ T.card / Q ^ 2 := by
      rw [Nat.le_div_iff_mul_le (by positivity : 0 < Q ^ 2)]
      have := Nat.lt_of_not_ge (show ¬ T.card ≤ Q ^ 2 * weight C from
        fun h ↦ hlarge ⟨C, h⟩)
      simpa [Nat.mul_comm] using this.le
    have hNlarge : Q ^ 2 < T.card := by
      obtain ⟨v, hvT⟩ : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hT
      let vT : {x : V // x ∈ T} := ⟨v, hvT⟩
      let C := H.connectedComponentMk vT
      have hCpos : 0 < weight C := by
        rw [Finset.card_pos]
        exact ⟨vT, by
          simpa [weight, C] using
            H.ConnectedComponent.connectedComponentMk_mem (v := vT)⟩
      have := Nat.lt_of_not_ge (show ¬ T.card ≤ Q ^ 2 * weight C from
        fun h ↦ hlarge ⟨C, h⟩)
      nlinarith
    let r := T.card / (4 * Q ^ 3) + 1
    let M := T.card / Q ^ 2
    have hr : 0 < r := by simp [r]
    have hcapacity : Q * (r + M) ≤ ∑ C : H.ConnectedComponent, weight C := by
      rw [hsum]
      simpa [r, M] using component_grouping_capacity hQ hNlarge
    obtain ⟨K⟩ := exists_weighted_groups
      (Finset.univ : Finset H.ConnectedComponent) weight r M Q hr
      (fun C _ ↦ hsmall C) hcapacity
    let U : Fin Q → Finset {x : V // x ∈ T} := fun i ↦
      (K.group i).biUnion fun C ↦ C.supp.toFinset
    have hUcard (i : Fin Q) : (U i).card = ∑ C ∈ K.group i, weight C := by
      change ((K.group i).biUnion fun C ↦ C.supp.toFinset).card = _
      rw [Finset.card_biUnion]
      · intro C hC D hD hCD
        change Disjoint C.supp.toFinset D.supp.toFinset
        rw [Finset.disjoint_left]
        intro x hxC hxD
        exact Set.disjoint_left.mp (H.pairwise_disjoint_supp_connectedComponent hCD)
          (by simpa using hxC) (by simpa using hxD)
    have hUdisj {i j : Fin Q} (hij : i ≠ j) : Disjoint (U i) (U j) := by
      rw [Finset.disjoint_left]
      intro x hxi hxj
      obtain ⟨C, hCi, hxC⟩ := Finset.mem_biUnion.mp hxi
      obtain ⟨D, hDj, hxD⟩ := Finset.mem_biUnion.mp hxj
      have hCD : C = D := SimpleGraph.ConnectedComponent.eq_of_common_vertex
        (by simpa using hxC) (by simpa using hxD)
      subst D
      exact Finset.disjoint_left.mp (K.disjoint hij) hCi hDj
    let C : Blockade (V := V) Q :=
      mapBlockade e
        { block := U
          disjoint := fun {i j} hij ↦ hUdisj hij }
    apply Or.inr
    refine ⟨C, ?_, ?_, ?_⟩
    · intro i x hx
      change x ∈ (U i).map e at hx
      obtain ⟨xT, _hxU, rfl⟩ := Finset.mem_map.mp hx
      exact xT.property
    · intro i j hij x hxi y hyj
      change x ∈ (U i).map e at hxi
      change y ∈ (U j).map e at hyj
      obtain ⟨xT, hxU, rfl⟩ := Finset.mem_map.mp hxi
      obtain ⟨yT, hyU, rfl⟩ := Finset.mem_map.mp hyj
      by_contra hxy
      have hne : xT ≠ yT := by
        intro heq
        subst yT
        exact Finset.disjoint_left.mp (hUdisj hij) hxU hyU
      have hHad : H.Adj xT yT := by
        change Gᶜ.Adj xT.1 yT.1
        rw [SimpleGraph.compl_adj]
        refine ⟨fun heq ↦ hne (Subtype.ext heq), ?_⟩
        simpa [e] using hxy
      obtain ⟨Cx, hCxi, hxCx⟩ := Finset.mem_biUnion.mp hxU
      obtain ⟨Cy, hCyj, hyCy⟩ := Finset.mem_biUnion.mp hyU
      have hCxCy : Cx = Cy := by
        apply SimpleGraph.ConnectedComponent.eq_of_common_vertex
          (v := yT) (by
            have hxmem : xT ∈ Cx.supp := by simpa using hxCx
            exact (Cx.mem_supp_congr_adj hHad).mp hxmem) (by simpa using hyCy)
      subst Cy
      exact Finset.disjoint_left.mp (K.disjoint hij) hCxi hCyj
    · intro i
      have htarget : T.card ≤ 4 * Q ^ 3 * r := by
        exact Nat.le_of_lt (by
          simpa [r] using Nat.lt_mul_div_succ T.card
            (by positivity : 0 < 4 * Q ^ 3))
      calc
        T.card ≤ 4 * Q ^ 3 * r := htarget
        _ ≤ 4 * Q ^ 3 * (U i).card := by
          rw [hUcard]
          exact Nat.mul_le_mul_left _ (K.heavy i)
        _ = 4 * Q ^ 3 * (C.block i).card := by
          simp [C, mapBlockade]

end Lax57Proofs
