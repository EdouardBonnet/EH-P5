import Lax54.GraphDefinitions
import Mathlib.Combinatorics.SimpleGraph.Density
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
---
title: Finite graph notions for the five-vertex path theorem
type: definition
---
This module defines the five-vertex path $P_5$, its complement (the house),
and the notions of sparsity, restrictedness, and blockades used throughout
the formalization. For a positive integer $E$, `ESparse` means maximum degree
at most $|G|/E$, while `WeaklyESparse` is the corresponding edge-density
condition with its denominator cleared.
-/

open Finset
open scoped SimpleGraph

namespace Lax57.GraphDefinitions

universe u

/-- The path on five vertices. -/
abbrev P5 : SimpleGraph (Fin 5) := SimpleGraph.pathGraph 5

/-- The house graph, namely the complement of the five-vertex path. -/
abbrev House : SimpleGraph (Fin 5) := P5ᶜ

/-- A graph has no induced copy of the five-vertex path. -/
def IsP5Free {V : Type u} (G : SimpleGraph V) : Prop :=
  ¬ P5 ⊴ G

/-- A graph has no induced copy of the house. -/
def IsHouseFree {V : Type u} (G : SimpleGraph V) : Prop :=
  ¬ House ⊴ G

/-- The largest cardinality of a clique or stable set. -/
noncomputable abbrev homogeneousNumber {V : Type u} (G : SimpleGraph V) : ℕ :=
  Lax54.GraphDefinitions.homogeneousNumber G

/-- The product of the clique and independence numbers. -/
noncomputable abbrev kappa {V : Type u} (G : SimpleGraph V) : ℕ :=
  Lax54.GraphDefinitions.kappa G

/-- `q`-criticality for the product `ω(G)α(G)`. -/
abbrev IsQCritical {V : Type u} [Fintype V] (q : ℕ) (G : SimpleGraph V) : Prop :=
  Lax54.GraphDefinitions.IsQCritical q G

/-- The neighbors of `v` lying in a prescribed finite set. -/
def neighborsIn {V : Type u} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (A : Finset V) (v : V) : Finset V :=
  A.filter fun x ↦ G.Adj v x

/-- `B` is `1/E`-sparse to `A`, with the denominator cleared. -/
def ESparseTo {V : Type u} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (E : ℕ) (B A : Finset V) : Prop :=
  ∀ b ∈ B, E * (neighborsIn G A b).card ≤ A.card

/-- The pair `(A,B)` has edge density at most `1/E`. -/
def WeaklyESparse {V : Type u} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (E : ℕ) (A B : Finset V) : Prop :=
  E * (G.interedges A B).card ≤ A.card * B.card

/-- The graph induced by `A` has maximum degree at most `|A|/E`. -/
def ESparse {V : Type u} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (E : ℕ) (A : Finset V) : Prop :=
  ∀ v : {x : V // x ∈ A}, E * (G.induce (A : Set V)).degree v ≤ A.card

/-- One of the two complementary graphs induced by `A` is `1/E`-sparse. -/
def ERestricted {V : Type u} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (E : ℕ) (A : Finset V) : Prop :=
  ESparse G E A ∨ ESparse Gᶜ E A

/-- A sequence of pairwise disjoint vertex blocks. -/
structure Blockade {V : Type u} [DecidableEq V] (k : ℕ) where
  block : Fin k → Finset V
  disjoint : ∀ {i j : Fin k}, i ≠ j → Disjoint (block i) (block j)

/-- Every two different blocks are complete to one another. -/
def Blockade.IsComplete {V : Type u} [DecidableEq V] {k : ℕ}
    (G : SimpleGraph V) (B : Blockade (V := V) k) : Prop :=
  ∀ {i j : Fin k}, i ≠ j →
    ∀ x ∈ B.block i, ∀ y ∈ B.block j, G.Adj x y

/-- Every two different blocks are anticomplete to one another. -/
def Blockade.IsAnticomplete {V : Type u} [DecidableEq V] {k : ℕ}
    (G : SimpleGraph V) (B : Blockade (V := V) k) : Prop :=
  ∀ {i j : Fin k}, i ≠ j →
    ∀ x ∈ B.block i, ∀ y ∈ B.block j, ¬ G.Adj x y

/-- Each pair of blocks is either complete or anticomplete. -/
def Blockade.IsPure {V : Type u} [DecidableEq V] {k : ℕ}
    (G : SimpleGraph V) (B : Blockade (V := V) k) : Prop :=
  ∀ {i j : Fin k}, i ≠ j →
    ((∀ x ∈ B.block i, ∀ y ∈ B.block j, G.Adj x y) ∨
     (∀ x ∈ B.block i, ∀ y ∈ B.block j, ¬ G.Adj x y))

/-- A complete or anticomplete blockade. -/
def Blockade.IsUniform {V : Type u} [DecidableEq V] {k : ℕ}
    (G : SimpleGraph V) (B : Blockade (V := V) k) : Prop :=
  B.IsComplete G ∨ B.IsAnticomplete G

/-- The directed vertexwise sparsity condition of the paper. -/
def Blockade.IsESparse {V : Type u} [DecidableEq V] {k : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj] (E : ℕ)
    (B : Blockade (V := V) k) : Prop :=
  ∀ {i j : Fin k}, i < j → ESparseTo G E (B.block j) (B.block i)

/-- Each pair is complete or weakly `1/E`-sparse. -/
def Blockade.IsSemisparse {V : Type u} [DecidableEq V] {k : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj] (E : ℕ)
    (B : Blockade (V := V) k) : Prop :=
  ∀ {i j : Fin k}, i ≠ j →
    ((∀ x ∈ B.block i, ∀ y ∈ B.block j, G.Adj x y) ∨
      WeaklyESparse G E (B.block i) (B.block j))

/-- All blocks have size at least `|V(G)| / loss`. -/
def Blockade.HasWidthLoss {V : Type u} [Fintype V] [DecidableEq V]
    {k : ℕ} (B : Blockade (V := V) k) (loss : ℕ) : Prop :=
  ∀ i : Fin k, Fintype.card V ≤ loss * (B.block i).card

/-- Every block lies in a prescribed ambient vertex set. -/
def Blockade.IsInside {V : Type u} [DecidableEq V] {k : ℕ}
    (B : Blockade (V := V) k) (S : Finset V) : Prop :=
  ∀ i : Fin k, B.block i ⊆ S

/-- A uniform blockade with polynomial width and controlled length. -/
def HasUniformBlockade {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (E a : ℕ) : Prop :=
  ∃ (k : ℕ) (B : Blockade (V := V) k),
    2 ≤ k ∧ k ≤ E ∧ B.IsUniform G ∧ B.HasWidthLoss (k ^ a)

end Lax57.GraphDefinitions
