import Lax57.GraphDefinitions
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Tactic

namespace Lax57Proofs

open Finset
open scoped SimpleGraph
open Lax57.GraphDefinitions

universe u v

/-- The two-set blockade associated with a disjoint pair. -/
def pairBlockade {V : Type u} [DecidableEq V]
    (A B : Finset V) (hdisj : Disjoint A B) : Blockade (V := V) 2 where
  block := ![A, B]
  disjoint := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [hdisj, hdisj.symm]

@[simp] lemma pairBlockade_block_zero
    {V : Type u} [DecidableEq V] (A B : Finset V) (hdisj : Disjoint A B) :
    (pairBlockade A B hdisj).block 0 = A := rfl

@[simp] lemma pairBlockade_block_one
    {V : Type u} [DecidableEq V] (A B : Finset V) (hdisj : Disjoint A B) :
    (pairBlockade A B hdisj).block 1 = B := rfl

/-- Map every block along an embedding of the vertex types. -/
def mapBlockade {W : Type u} {V : Type v} [DecidableEq W] [DecidableEq V]
    {k : ℕ} (f : W ↪ V) (B : Blockade (V := W) k) : Blockade (V := V) k where
  block i := (B.block i).map f
  disjoint := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    obtain ⟨xi, hxiB, rfl⟩ := Finset.mem_map.mp hxi
    obtain ⟨xj, hxjB, heq⟩ := Finset.mem_map.mp hxj
    have : xi = xj := f.injective heq.symm
    subst xj
    exact Finset.disjoint_left.mp (B.disjoint hij) hxiB hxjB

@[simp] theorem Blockade.map_block
    {W : Type u} {V : Type v} [DecidableEq W] [DecidableEq V]
    {k : ℕ} (f : W ↪ V) (B : Blockade (V := W) k) (i : Fin k) :
    (mapBlockade f B).block i = (B.block i).map f := rfl

theorem Blockade.map_block_card
    {W : Type u} {V : Type v} [DecidableEq W] [DecidableEq V]
    {k : ℕ} (f : W ↪ V) (B : Blockade (V := W) k) (i : Fin k) :
    ((mapBlockade f B).block i).card = (B.block i).card := by simp [mapBlockade]

/-- In a finite graph, either one connected component contains at least half
the vertices, or there are two anticomplete sets each containing at least a
quarter of the vertices. -/
theorem large_component_or_anticomplete_pair
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∃ C : G.ConnectedComponent,
        Fintype.card V ≤ 2 * C.supp.toFinset.card) ∨
      (∃ A B : Finset V, Disjoint A B ∧
        (∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y) ∧
        Fintype.card V ≤ 4 * A.card ∧
        Fintype.card V ≤ 4 * B.card) := by
  classical
  by_cases hlarge : ∃ C : G.ConnectedComponent,
      Fintype.card V ≤ 2 * C.supp.toFinset.card
  · exact Or.inl hlarge
  · push Not at hlarge
    let vertices : Finset G.ConnectedComponent → Finset V := fun T ↦
      T.biUnion fun C ↦ C.supp.toFinset
    let good : Finset (Finset G.ConnectedComponent) :=
      (Finset.univ.powerset).filter fun T ↦
        4 * (vertices T).card ≤ 3 * Fintype.card V
    have hgood : good.Nonempty := by
      refine ⟨∅, ?_⟩
      simp [good, vertices]
    obtain ⟨T, hTgood, hmax⟩ := Finset.exists_max_image good
      (fun U ↦ (vertices U).card) hgood
    have hTsub : T ⊆ (Finset.univ : Finset G.ConnectedComponent) := by
      simpa [good] using (Finset.mem_filter.mp hTgood).1
    have hTupper : 4 * (vertices T).card ≤ 3 * Fintype.card V := by
      simpa [good] using (Finset.mem_filter.mp hTgood).2
    have hTlower : Fintype.card V ≤ 4 * (vertices T).card := by
      by_contra hnot
      have hsmallT : 4 * (vertices T).card < Fintype.card V :=
        Nat.lt_of_not_ge hnot
      have hcardT : (vertices T).card < Fintype.card V := by omega
      have hproper : vertices T ⊂ (Finset.univ : Finset V) := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, ?_⟩
        intro heq
        have : (vertices T).card = Fintype.card V := by simpa [heq]
        omega
      obtain ⟨x, _hxuniv, hxnot⟩ := Finset.exists_of_ssubset hproper
      let C := G.connectedComponentMk x
      have hCnot : C ∉ T := by
        intro hCT
        apply hxnot
        exact Finset.mem_biUnion.mpr ⟨C, hCT, by
          simpa [C] using G.ConnectedComponent.connectedComponentMk_mem (v := x)⟩
      have hdisj : Disjoint (vertices T) C.supp.toFinset := by
        rw [Finset.disjoint_left]
        intro y hyT hyC
        obtain ⟨D, hDT, hyD⟩ := Finset.mem_biUnion.mp hyT
        have hDC : D = C :=
          SimpleGraph.ConnectedComponent.eq_of_common_vertex
            (by simpa using hyD) (by simpa using hyC)
        exact hCnot (hDC ▸ hDT)
      have hCsmall : 2 * C.supp.toFinset.card < Fintype.card V := hlarge C
      have hcardInsert : (vertices (insert C T)).card =
          (vertices T).card + C.supp.toFinset.card := by
        rw [show vertices (insert C T) = vertices T ∪ C.supp.toFinset by
          ext y
          simp [vertices, or_comm]]
        exact Finset.card_union_of_disjoint hdisj
      have hInsertGood : insert C T ∈ good := by
        rw [Finset.mem_filter]
        refine ⟨by simp [hTsub], ?_⟩
        rw [hcardInsert]
        omega
      have hle := hmax (insert C T) hInsertGood
      rw [hcardInsert] at hle
      have hCpos : 0 < C.supp.toFinset.card := by
        rw [Finset.card_pos]
        simpa using C.nonempty_supp
      omega
    let A := vertices T
    let B := (Finset.univ : Finset V) \ A
    have hdisjAB : Disjoint A B := Finset.disjoint_sdiff
    have hanti : ∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y := by
      intro x hxA y hyB hxy
      obtain ⟨C, hCT, hxC⟩ := Finset.mem_biUnion.mp hxA
      have hyC : y ∈ C.supp.toFinset := by
        have := (C.mem_supp_congr_adj hxy).mp (by simpa using hxC)
        simpa using this
      have hyA : y ∈ A := Finset.mem_biUnion.mpr ⟨C, hCT, hyC⟩
      exact (Finset.mem_sdiff.mp hyB).2 hyA
    have hcardB : B.card = Fintype.card V - A.card := by
      simpa [B] using Finset.card_sdiff_of_subset (Finset.subset_univ A)
    refine Or.inr ⟨A, B, hdisjAB, hanti, ?_, ?_⟩
    · simpa [A] using hTlower
    · rw [hcardB]
      simpa [A] using (show Fintype.card V ≤
          4 * (Fintype.card V - (vertices T).card) by omega)

/-- A vertex set which is a connected component inside an induced subgraph. -/
structure IsComponentIn {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (T J : Finset V) : Prop where
  subset : J ⊆ T
  nonempty : J.Nonempty
  connected : (G.induce (J : Set V)).Connected
  closed : ∀ x ∈ J, ∀ y ∈ T \ J, ¬ G.Adj x y

/-- The component dichotomy transported from `G[T]` back to the ambient
vertex type. -/
theorem component_in_or_anticomplete_pair
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) :
    (∃ J : Finset V, IsComponentIn G T J ∧ T.card ≤ 2 * J.card) ∨
      (∃ B : Blockade (V := V) 2,
        B.IsInside T ∧ B.IsAnticomplete G ∧
          ∀ i : Fin 2, T.card ≤ 4 * (B.block i).card) := by
  classical
  let H := G.induce (T : Set V)
  let e : {x : V // x ∈ T} ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  rcases large_component_or_anticomplete_pair H with hcomponent | hpair
  · obtain ⟨C, hCsize⟩ := hcomponent
    let J : Finset V := C.supp.toFinset.map e
    have hJsubset : J ⊆ T := by
      intro x hx
      obtain ⟨xT, _hxC, rfl⟩ := Finset.mem_map.mp hx
      exact xT.property
    have hJnonempty : J.Nonempty := by
      obtain ⟨xT, hxC⟩ := C.nonempty_supp
      exact ⟨xT.1, Finset.mem_map.mpr ⟨xT, by simpa using hxC, rfl⟩⟩
    have hJconnected : (G.induce (J : Set V)).Connected := by
      let φfun : C → {z : V // z ∈ (J : Set V)} := fun x ↦
        ⟨x.1.1, by
          change x.1.1 ∈ J
          exact Finset.mem_map.mpr ⟨x.1, by simpa using x.2, rfl⟩⟩
      let φ : C.toSimpleGraph →g G.induce (J : Set V) :=
        ⟨φfun, by
          intro x y hxy
          exact hxy⟩
      have hsurj : Function.Surjective φ := by
        intro y
        have hyJ : y.1 ∈ J := y.property
        obtain ⟨xT, hxC, hxy⟩ := Finset.mem_map.mp hyJ
        refine ⟨⟨xT, by simpa using hxC⟩, ?_⟩
        exact Subtype.ext hxy
      exact C.connected_toSimpleGraph.map φ hsurj
    have hJclosed : ∀ x ∈ J, ∀ y ∈ T \ J, ¬ G.Adj x y := by
      intro x hxJ y hyTJ hxy
      obtain ⟨xT, hxC, hxeq⟩ := Finset.mem_map.mp hxJ
      have hyT : y ∈ T := (Finset.mem_sdiff.mp hyTJ).1
      let yT : {z : V // z ∈ T} := ⟨y, hyT⟩
      have hadjH : H.Adj xT yT := by
        have hxval : xT.1 = x := hxeq
        simpa [H, yT, hxval] using hxy
      have hyC : yT ∈ C.supp :=
        (C.mem_supp_congr_adj hadjH).mp (by simpa using hxC)
      have hyJ : y ∈ J :=
        Finset.mem_map.mpr ⟨yT, by simpa using hyC, rfl⟩
      exact (Finset.mem_sdiff.mp hyTJ).2 hyJ
    refine Or.inl ⟨J, ⟨hJsubset, hJnonempty, hJconnected, hJclosed⟩, ?_⟩
    simpa [J, H] using hCsize
  · obtain ⟨A, B, hdisj, hanti, hA, hB⟩ := hpair
    let Csub : Blockade (V := {x : V // x ∈ T}) 2 := pairBlockade A B hdisj
    let C : Blockade (V := V) 2 := mapBlockade e Csub
    have hinside : C.IsInside T := by
      intro i x hx
      change x ∈ (Csub.block i).map e at hx
      obtain ⟨xT, _hx, rfl⟩ := Finset.mem_map.mp hx
      exact xT.property
    have hantiC : C.IsAnticomplete G := by
      intro i j hij x hxi y hyj hxy
      change x ∈ (Csub.block i).map e at hxi
      change y ∈ (Csub.block j).map e at hyj
      obtain ⟨xT, hxiT, rfl⟩ := Finset.mem_map.mp hxi
      obtain ⟨yT, hyjT, rfl⟩ := Finset.mem_map.mp hyj
      fin_cases i <;> fin_cases j
      · exact hij rfl
      · exact hanti xT hxiT yT hyjT hxy
      · exact hanti yT hyjT xT hxiT (G.adj_comm _ _ |>.mp hxy)
      · exact hij rfl
    refine Or.inr ⟨C, hinside, hantiC, ?_⟩
    intro i
    fin_cases i
    · simpa [C, Csub, H] using hA
    · simpa [C, Csub, H] using hB

/-- A connected induced graph has an edge crossing every nontrivial vertex
cut. -/
theorem exists_adj_across
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {F A : Finset V} (hconn : (G.induce (F : Set V)).Connected)
    (hsub : A ⊆ F) (hA : A.Nonempty) (houtside : (F \ A).Nonempty) :
    ∃ x ∈ A, ∃ y ∈ F \ A, G.Adj x y := by
  classical
  by_contra hnone
  push Not at hnone
  obtain ⟨x, hxA⟩ := hA
  obtain ⟨y, hyFA⟩ := houtside
  have hxF : x ∈ F := hsub hxA
  have hyF : y ∈ F := (Finset.mem_sdiff.mp hyFA).1
  have hyNot : y ∉ A := (Finset.mem_sdiff.mp hyFA).2
  let walk : (G.induce (F : Set V)).Walk ⟨x, hxF⟩ ⟨y, hyF⟩ :=
    Classical.choice (hconn ⟨x, hxF⟩ ⟨y, hyF⟩)
  have hpreserve : ∀ {p q : {z : V // z ∈ F}}
      (w : (G.induce (F : Set V)).Walk p q), p.1 ∈ A → q.1 ∈ A := by
    intro p q w
    induction w with
    | nil => exact fun hp ↦ hp
    | @cons p r q hpr w ih =>
        intro hpA
        apply ih
        by_contra hrA
        exact hnone p.1 hpA r.1 (Finset.mem_sdiff.mpr ⟨r.2, hrA⟩) hpr
  exact hyNot (hpreserve walk hxA)

end Lax57Proofs
