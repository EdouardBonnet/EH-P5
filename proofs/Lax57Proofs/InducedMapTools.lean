import Lax57Proofs.ComponentTools
import Mathlib.Tactic

namespace Lax57Proofs

open Finset
open scoped SimpleGraph
open Lax57.GraphDefinitions

universe u

/-- Degrees can only decrease when the inducing vertex set is shrunk. -/
theorem degree_induce_finset_mono
    {V : Type u} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {A B : Finset V} (hAB : A ⊆ B)
    (v : {x : V // x ∈ A}) :
    (G.induce (A : Set V)).degree v ≤
      (G.induce (B : Set V)).degree ⟨v.1, hAB v.2⟩ := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree]
  rw [← Finset.card_map (f := Function.Embedding.subtype (fun x ↦ x ∈ A)),
    ← Finset.card_map (f := Function.Embedding.subtype (fun x ↦ x ∈ B))]
  apply Finset.card_le_card
  intro z hz
  obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hz
  let wB : {x : V // x ∈ B} := ⟨w.1, hAB w.2⟩
  refine Finset.mem_map.mpr ⟨wB, ?_, rfl⟩
  rw [SimpleGraph.mem_neighborFinset] at hw ⊢
  exact hw

/-- An induced degree is at most the corresponding ambient degree. -/
theorem degree_induce_finset_le
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (A : Finset V) (v : {x : V // x ∈ A}) :
    (G.induce (A : Set V)).degree v ≤ G.degree v.1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree]
  rw [← Finset.card_map
    (f := Function.Embedding.subtype (fun x ↦ x ∈ A))]
  apply Finset.card_le_card
  intro z hz
  obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hz
  rw [SimpleGraph.mem_neighborFinset] at hw ⊢
  exact hw

/-- Interedge counts are unchanged when an induced-subgraph blockade is
mapped back to the ambient vertex type. -/
theorem card_interedges_map_induce
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (A B : Finset {x : V // x ∈ S}) :
    (G.interedges (A.map ⟨Subtype.val, Subtype.val_injective⟩)
      (B.map ⟨Subtype.val, Subtype.val_injective⟩)).card =
      ((G.induce (S : Set V)).interedges A B).card := by
  classical
  let H := G.induce (S : Set V)
  let e : {x : V // x ∈ S} ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  symm
  refine Finset.card_bij
    (fun p (_ : p ∈ H.interedges A B) ↦ (p.1.1, p.2.1)) ?_ ?_ ?_
  · intro p hp
    rw [SimpleGraph.mem_interedges_iff] at hp ⊢
    exact ⟨Finset.mem_map.mpr ⟨p.1, hp.1, rfl⟩,
      Finset.mem_map.mpr ⟨p.2, hp.2.1, rfl⟩, hp.2.2⟩
  · intro a ha b hb hab
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst hab
    · exact congrArg Prod.snd hab
  · intro p hp
    rw [SimpleGraph.mem_interedges_iff] at hp
    obtain ⟨a, haA, ha⟩ := Finset.mem_map.mp hp.1
    obtain ⟨b, hbB, hb⟩ := Finset.mem_map.mp hp.2.1
    have ha' : a.1 = p.1 := by simpa [e] using ha
    have hb' : b.1 = p.2 := by simpa [e] using hb
    refine ⟨(a, b), ?_, ?_⟩
    rw [SimpleGraph.mem_interedges_iff]
    exact ⟨haA, hbB, by
      change G.Adj a.1 b.1
      rw [ha', hb']
      exact hp.2.2⟩
    exact Prod.ext ha' hb'

/-- Directed neighbor sparsity transfers from an induced subtype to the
ambient graph. -/
theorem ESparseTo.map_induce
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    {E : ℕ} {A B : Finset {x : V // x ∈ S}}
    (h : ESparseTo (G.induce (S : Set V)) E B A) :
    ESparseTo G E
      (B.map ⟨Subtype.val, Subtype.val_injective⟩)
      (A.map ⟨Subtype.val, Subtype.val_injective⟩) := by
  intro b hb
  obtain ⟨bS, hbB, rfl⟩ := Finset.mem_map.mp hb
  have hn : (neighborsIn G
      (A.map ⟨Subtype.val, Subtype.val_injective⟩) bS.1).card =
      (neighborsIn (G.induce (S : Set V)) A bS).card := by
    rw [← Finset.card_map
      (f := Function.Embedding.subtype (fun x ↦ x ∈ S))]
    congr 1
    ext x
    simp [neighborsIn, G.adj_comm]
  simpa [hn] using h bS hbB

/-- Weak pair sparsity transfers from an induced subtype to the ambient
graph. -/
theorem WeaklyESparse.map_induce
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    {E : ℕ} {A B : Finset {x : V // x ∈ S}}
    (h : WeaklyESparse (G.induce (S : Set V)) E A B) :
    WeaklyESparse G E
      (A.map ⟨Subtype.val, Subtype.val_injective⟩)
      (B.map ⟨Subtype.val, Subtype.val_injective⟩) := by
  simpa [WeaklyESparse, card_interedges_map_induce G S A B] using h

/-- Maximum-degree sparsity transfers from an induced subtype to the
corresponding mapped finite set in the ambient graph. -/
theorem ESparse.map_induce
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    {E : ℕ} {T : Finset {x : V // x ∈ S}}
    (h : ESparse (G.induce (S : Set V)) E T) :
    ESparse G E
      (T.map ⟨Subtype.val, Subtype.val_injective⟩) := by
  classical
  intro v
  obtain ⟨vS, hvT, hv⟩ := Finset.mem_map.mp v.2
  let v' : {x : V // x ∈
      T.map ⟨Subtype.val, Subtype.val_injective⟩} :=
    ⟨vS.1, Finset.mem_map.mpr ⟨vS, hvT, rfl⟩⟩
  have hv' : v = v' := Subtype.ext hv.symm
  subst v
  let w : {x : {x : V // x ∈ S} // x ∈ T} := ⟨vS, hvT⟩
  have hdeg :
      (G.induce
          (T.map ⟨Subtype.val, Subtype.val_injective⟩ : Set V)).degree
          ⟨vS.1, Finset.mem_map.mpr ⟨vS, hvT, rfl⟩⟩ =
        ((G.induce (S : Set V)).induce (T : Set {x : V // x ∈ S})).degree w := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
      ← SimpleGraph.card_neighborFinset_eq_degree]
    let e : {x : {x : V // x ∈ S} // x ∈ T} ↪
        {x : V // x ∈ T.map ⟨Subtype.val, Subtype.val_injective⟩} :=
      ⟨fun x ↦ ⟨x.1.1, Finset.mem_map.mpr ⟨x.1, x.2, rfl⟩⟩, by
        intro x y hxy
        have hval : (x.1.1 : V) = y.1.1 := congrArg
          (fun z : {z : V // z ∈
            T.map ⟨Subtype.val, Subtype.val_injective⟩} ↦ z.1) hxy
        apply Subtype.ext
        apply Subtype.ext
        exact hval⟩
    rw [← Finset.card_map (f := e)]
    congr 1
    ext x
    constructor
    · intro hx
      rw [SimpleGraph.mem_neighborFinset] at hx
      obtain ⟨xS, hxT, hxval⟩ := Finset.mem_map.mp x.2
      let y : {z : {z : V // z ∈ S} // z ∈ T} := ⟨xS, hxT⟩
      apply Finset.mem_map.mpr
      refine ⟨y, ?_, ?_⟩
      · rw [SimpleGraph.mem_neighborFinset]
        change G.Adj vS.1 xS.1
        change G.Adj vS.1 x.1 at hx
        have hxval' : xS.1 = x.1 := hxval
        rw [hxval']
        exact hx
      · apply Subtype.ext
        exact hxval
    · intro hx
      obtain ⟨y, hy, hxy⟩ := Finset.mem_map.mp hx
      rw [SimpleGraph.mem_neighborFinset] at hy ⊢
      change G.Adj vS.1 y.1.1 at hy
      change G.Adj vS.1 x.1
      have hval : y.1.1 = x.1 := congrArg Subtype.val hxy
      simpa [hval] using hy
  rw [hdeg]
  simpa using h w

/-- Purity transfers from an induced subtype to the ambient graph. -/
theorem Blockade.IsPure.map_induce
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) {k : ℕ}
    {B : Blockade (V := {x : V // x ∈ S}) k}
    (h : B.IsPure (G.induce (S : Set V))) :
    (mapBlockade ⟨Subtype.val, Subtype.val_injective⟩ B).IsPure G := by
  intro i j hij
  rcases h hij with hc | ha
  · apply Or.inl
    intro x hx y hy
    obtain ⟨xS, hxB, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨yS, hyB, rfl⟩ := Finset.mem_map.mp hy
    exact hc xS hxB yS hyB
  · apply Or.inr
    intro x hx y hy
    obtain ⟨xS, hxB, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨yS, hyB, rfl⟩ := Finset.mem_map.mp hy
    exact ha xS hxB yS hyB

/-- Directed blockade sparsity transfers from an induced subtype. -/
theorem Blockade.IsESparse.map_induce
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    {k E : ℕ} {B : Blockade (V := {x : V // x ∈ S}) k}
    (h : B.IsESparse (G.induce (S : Set V)) E) :
    (mapBlockade ⟨Subtype.val, Subtype.val_injective⟩ B).IsESparse G E := by
  intro i j hij
  exact ESparseTo.map_induce G S (h hij)

end Lax57Proofs
