import Lax54.BipartiteCombLemma
import Lax57Proofs.ComponentTools
import Lax57Proofs.SparseP5Pair
import Mathlib.Tactic

namespace Lax57Proofs

open Finset
open scoped SimpleGraph
open Lax57.GraphDefinitions
open Lax54.BipartiteCombLemma

universe u

/-- A vertex has both a neighbor and a nonneighbor in a set. -/
def IsMixedOn {V : Type u} (G : SimpleGraph V) (v : V) (A : Finset V) : Prop :=
  (∃ x ∈ A, G.Adj v x) ∧ (∃ y ∈ A, ¬ G.Adj v y)

/-- In an anticonnected block, a mixed outside vertex has a neighboring and
a nonneighboring vertex which themselves are nonadjacent. -/
theorem exists_nonadj_pair_of_anticonnected_mixed
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (A : Finset V)
    (hantiConn : (Gᶜ.induce (A : Set V)).Connected)
    (hmixed : IsMixedOn G v A) :
    ∃ a ∈ A, ∃ b ∈ A,
      G.Adj v a ∧ ¬ G.Adj v b ∧ Gᶜ.Adj a b := by
  classical
  let N := A.filter fun x ↦ G.Adj v x
  obtain ⟨a₀, ha₀A, hva₀⟩ := hmixed.1
  obtain ⟨b₀, hb₀A, hvb₀⟩ := hmixed.2
  have hN : N.Nonempty := ⟨a₀, Finset.mem_filter.mpr ⟨ha₀A, hva₀⟩⟩
  have hAN : (A \ N).Nonempty := by
    refine ⟨b₀, Finset.mem_sdiff.mpr ⟨hb₀A, ?_⟩⟩
    intro hbN
    exact hvb₀ (Finset.mem_filter.mp hbN).2
  obtain ⟨a, haN, b, hbAN, hab⟩ :=
    exists_adj_across Gᶜ hantiConn (Finset.filter_subset _ _) hN hAN
  have ha := Finset.mem_filter.mp haN
  have hbA := (Finset.mem_sdiff.mp hbAN).1
  have hvb : ¬ G.Adj v b := by
    intro hvb
    exact (Finset.mem_sdiff.mp hbAN).2 (Finset.mem_filter.mpr ⟨hbA, hvb⟩)
  exact ⟨a, ha.1, b, hbA, ha.2, hvb, hab⟩

/-- A nonconstant bipartite adjacency relation has a mixed vertex on one
of its two sides. -/
theorem exists_mixed_vertex_of_nonpure_pair
    {V : Type u} (G : SimpleGraph V) {A B : Finset V}
    (hnotComplete : ¬ (∀ a ∈ A, ∀ b ∈ B, G.Adj a b))
    (hnotAnticomplete : ¬ (∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)) :
    (∃ b ∈ B, IsMixedOn G b A) ∨
      (∃ a ∈ A, IsMixedOn G a B) := by
  classical
  push Not at hnotComplete hnotAnticomplete
  obtain ⟨a₀, ha₀A, b₀, hb₀B, ha₀b₀⟩ := hnotAnticomplete
  obtain ⟨a₁, ha₁A, b₁, hb₁B, ha₁b₁⟩ := hnotComplete
  by_cases hb₀mixed : IsMixedOn G b₀ A
  · exact Or.inl ⟨b₀, hb₀B, hb₀mixed⟩
  by_cases hb₁mixed : IsMixedOn G b₁ A
  · exact Or.inl ⟨b₁, hb₁B, hb₁mixed⟩
  apply Or.inr
  refine ⟨a₀, ha₀A, ⟨⟨b₀, hb₀B, by simpa [G.adj_comm] using ha₀b₀⟩,
    ⟨b₁, hb₁B, ?_⟩⟩⟩
  intro ha₀b₁'
  apply hb₁mixed
  exact ⟨⟨a₀, ha₀A, G.adj_comm _ _ |>.mp ha₀b₁'⟩,
    ⟨a₁, ha₁A, by simpa [G.adj_comm] using ha₁b₁⟩⟩

/-- The five vertices furnished by an upside-down comb and a vertex mixed
on an anticonnected tooth block induce a house. -/
theorem house_of_upside_down_mixed
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {v a u : V} {D : Finset V}
    (hvD : ∀ x ∈ D, G.Adj v x)
    (haD : ∀ x ∈ D, G.Adj a x)
    (hvu : G.Adj v u) (hvuA : ¬ G.Adj a u)
    (hva : ¬ G.Adj v a) (huD : u ∉ D)
    (hanti : (Gᶜ.induce (D : Set V)).Connected)
    (hmix : IsMixedOn G u D) : House ⊴ G := by
  obtain ⟨w, hwD, z, hzD, huw, huz, hwz⟩ :=
    exists_nonadj_pair_of_anticonnected_mixed G u D hanti hmix
  have hcomp (x y : V) (hxy : x ≠ y) (hn : ¬ G.Adj x y) : Gᶜ.Adj x y := by
    simp only [SimpleGraph.compl_adj]
    exact ⟨hxy, hn⟩
  have hncomp (x y : V) (hxy : G.Adj x y) : ¬ Gᶜ.Adj x y := by
    intro hc
    exact hc.2 hxy
  have hzu : z ≠ u := by
    intro h
    apply huD
    simpa [h] using hzD
  have hua : u ≠ a := by
    intro h
    apply hva
    simpa [h, G.adj_comm] using hvu
  have hav : a ≠ v := by
    intro h
    apply hvuA
    simpa [h, G.adj_comm] using hvu
  have hp : P5 ⊴ Gᶜ := p5_isIndContained_of_vertices
      (G := Gᶜ)
      hwz
      (hcomp z u hzu (by simpa [G.adj_comm] using huz))
      (hcomp u a hua (by simpa [G.adj_comm] using hvuA))
      (hcomp a v hav (by simpa [G.adj_comm] using hva))
      (hncomp w u (G.adj_comm _ _ |>.mp huw))
      (hncomp w a (G.adj_comm _ _ |>.mp (haD w hwD)))
      (hncomp w v (G.adj_comm _ _ |>.mp (hvD w hwD)))
      (hncomp z a (G.adj_comm _ _ |>.mp (haD z hzD)))
      (hncomp z v (G.adj_comm _ _ |>.mp (hvD z hzD)))
      (hncomp u v (G.adj_comm _ _ |>.mp hvu))
  simpa [House] using hp.compl

/-- Anticonnected subblocks of an upside-down comb form a pure blockade in
a house-free graph. -/
theorem upside_down_comb_subblocks_pure
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} {t : ℕ} (C : CombBetween G A B t)
    (v : V) (hfree : IsHouseFree G)
    (hvB : ∀ x ∈ B, G.Adj v x)
    (hvA : ∀ x ∈ A, ¬ G.Adj v x)
    (D : Blockade (V := V) t)
    (hsub : ∀ i : Fin t, D.block i ⊆ C.block i)
    (hanti : ∀ i : Fin t, (Gᶜ.induce (D.block i : Set V)).Connected) :
    D.IsPure G := by
  intro i j hij
  by_cases hcomp : ∀ x ∈ D.block i, ∀ y ∈ D.block j, G.Adj x y
  · exact Or.inl hcomp
  by_cases hantiPair : ∀ x ∈ D.block i, ∀ y ∈ D.block j, ¬ G.Adj x y
  · exact Or.inr hantiPair
  exfalso
  rcases exists_mixed_vertex_of_nonpure_pair G hcomp hantiPair with
    ⟨u, huj, hmix⟩ | ⟨u, hui, hmix⟩
  · apply hfree
    apply house_of_upside_down_mixed G
        (v := v) (a := C.tooth i) (u := u) (D := D.block i)
    · intro x hx
      exact hvB x (C.block_subset i (hsub i hx))
    · intro x hx
      exact C.tooth_adj_block i x (hsub i hx)
    · exact hvB u (C.block_subset j (hsub j huj))
    · exact C.tooth_nonadj_other hij u (hsub j huj)
    · exact hvA (C.tooth i) (C.tooth_mem i)
    · intro hu
      exact Finset.disjoint_left.mp (C.blocks_disjoint hij)
        (hsub i hu) (hsub j huj)
    · exact hanti i
    · exact hmix
  · apply hfree
    apply house_of_upside_down_mixed G
        (v := v) (a := C.tooth j) (u := u) (D := D.block j)
    · intro x hx
      exact hvB x (C.block_subset j (hsub j hx))
    · intro x hx
      exact C.tooth_adj_block j x (hsub j hx)
    · exact hvB u (C.block_subset i (hsub i hui))
    · exact C.tooth_nonadj_other (Ne.symm hij) u (hsub i hui)
    · exact hvA (C.tooth j) (C.tooth_mem j)
    · intro hu
      exact Finset.disjoint_left.mp (C.blocks_disjoint (Ne.symm hij))
        (hsub j hu) (hsub i hui)
    · exact hanti j
    · exact hmix

end Lax57Proofs
