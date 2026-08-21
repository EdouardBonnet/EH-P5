import Lax57.ErdosHajnalP5
import Lax57Proofs.HouseDichotomy
import Lax57Proofs.Helpers
import Mathlib.Tactic

namespace Lax57Proofs

open Finset
open scoped BigOperators SimpleGraph
open Lax57.GraphDefinitions

universe u

/-- The sum of `kappa` over the blocks of a uniform blockade is at most
`kappa` of the ambient graph. -/
theorem sum_kappa_uniform_le
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {k : ℕ} (B : Blockade (V := V) k)
    (huniform : B.IsUniform G) :
    ∑ i : Fin k, kappa (G.induce (B.block i : Set V)) ≤ kappa G := by
  classical
  rcases huniform with hcomplete | hanti
  · have hantiCompl : ∀ {i j : Fin k}, i ≠ j →
        ∀ x ∈ B.block i, ∀ y ∈ B.block j, ¬ Gᶜ.Adj x y := by
      intro i j hij x hx y hy hxy
      rw [SimpleGraph.compl_adj] at hxy
      exact hxy.2 (hcomplete hij x hx y hy)
    have hsum := Lax54Proofs.sum_kappa_induce_le
      (G := Gᶜ) B.block B.disjoint hantiCompl
    simpa [← Lax54Proofs.compl_induce_eq_induce_compl] using hsum
  · exact Lax54Proofs.sum_kappa_induce_le B.block B.disjoint hanti

/-- A uniform polynomial-width blockade is incompatible with criticality once
the critical exponent dominates the blockade exponent. -/
theorem not_isQCritical_of_uniform_blockade
    (a q E : ℕ) (haq : a ≤ q)
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hblockade : HasUniformBlockade G E a) :
    ¬ IsQCritical q G := by
  classical
  intro hcritical
  obtain ⟨k, B, hk2, _hkE, huniform, hwidth⟩ := hblockade
  have hkpos : 0 < k := by omega
  have hsum : ∑ i : Fin k, kappa (G.induce (B.block i : Set V)) ≤ kappa G :=
    sum_kappa_uniform_le B huniform
  let f : Fin k → ℕ := fun i ↦ kappa (G.induce (B.block i : Set V))
  have huniv : (Finset.univ : Finset (Fin k)).Nonempty :=
    ⟨⟨0, hkpos⟩, Finset.mem_univ _⟩
  obtain ⟨i₀, _hi₀, hmin⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Fin k)) f huniv
  let r : ℕ := f i₀
  have hr_le (i : Fin k) : r ≤ f i := hmin i (Finset.mem_univ i)
  have hkr_le_sum : k * r ≤ ∑ i : Fin k, f i := by
    calc
      k * r = ∑ _i : Fin k, r := by simp
      _ ≤ ∑ i : Fin k, f i := Finset.sum_le_sum fun i _ ↦ hr_le i
  have hkr_le : k * r ≤ kappa G :=
    hkr_le_sum.trans (by simpa [f] using hsum)
  letI : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk2
  obtain ⟨j, hji⟩ := exists_ne i₀
  have hnpos : 0 < Fintype.card V := Nat.zero_lt_of_lt hcritical.1
  have hjpos : 0 < (B.block j).card := by
    by_contra hz
    have hz' : (B.block j).card = 0 := Nat.eq_zero_of_not_pos hz
    have := hwidth j
    simp [hz'] at this
    omega
  obtain ⟨v, hvj⟩ := Finset.card_pos.mp hjpos
  have hvnot : v ∉ B.block i₀ := by
    intro hvi
    exact Finset.disjoint_left.mp (B.disjoint hji) hvj hvi
  have hproper : (B.block i₀).card < Fintype.card V :=
    Finset.card_lt_univ_of_notMem hvnot
  have hcriticalBlock : (B.block i₀).card ≤ r ^ q := by
    simpa [r, f] using hcritical.2 (B.block i₀) hproper
  have hn_le : Fintype.card V ≤ k ^ a * r ^ q :=
    (hwidth i₀).trans (Nat.mul_le_mul_left (k ^ a) hcriticalBlock)
  have hkaq : k ^ a ≤ k ^ q := Nat.pow_le_pow_right hkpos haq
  have hpow_le : k ^ a * r ^ q ≤ kappa G ^ q := by
    calc
      k ^ a * r ^ q ≤ k ^ q * r ^ q := Nat.mul_le_mul_right _ hkaq
      _ = (k * r) ^ q := (Nat.mul_pow k r q).symm
      _ ≤ kappa G ^ q := Nat.pow_le_pow_left hkr_le q
  exact Nat.not_lt_of_ge (hn_le.trans hpow_le) hcritical.1

/-- The restricted-set outcome contradicts criticality at exponent
`3*a+2` when it is applied with reciprocal parameter `kappa(G)^3`. -/
theorem not_isQCritical_of_restricted
    (a : ℕ) {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcritical : IsQCritical (3 * a + 2) G)
    (X : Finset V)
    (hlarge : Fintype.card V ≤ (kappa G ^ 3) ^ a * X.card)
    (hrestricted : ERestricted G (kappa G ^ 3) X) : False := by
  let K := kappa G
  have hK2 : 2 ≤ K := two_le_kappa_of_critical G (by omega) hcritical
  have hKpos : 0 < K := by omega
  have hKX : K < X.card := by
    have hmul : K ^ (3 * a) * K ^ 2 < K ^ (3 * a) * X.card := by
      calc
      K ^ (3 * a) * K ^ 2 = K ^ (3 * a + 2) := (pow_add K (3 * a) 2).symm
      _ < Fintype.card V := hcritical.1
      _ ≤ (K ^ 3) ^ a * X.card := by simpa [K] using hlarge
      _ = K ^ (3 * a) * X.card := by rw [← pow_mul]
    have hKsqX : K ^ 2 < X.card := Nat.lt_of_mul_lt_mul_left hmul
    have hKsq : K ≤ K ^ 2 := by nlinarith
    exact hKsq.trans_lt hKsqX
  have hKX' : K < Fintype.card {x : V // x ∈ X} := by
    simpa only [Fintype.card_coe] using hKX
  have hEK : 2 * K < K ^ 3 := by
    nlinarith [show K ^ 2 ≤ K ^ 3 from Nat.pow_le_pow_right hKpos (by omega : 2 ≤ 3)]
  rcases hrestricted with hsparse | hsparseCompl
  · let H := G.induce (X : Set V)
    have hdeg : ∀ v : {x : V // x ∈ X},
        K ^ 3 * H.degree v ≤ Fintype.card {x : V // x ∈ X} := by
      intro v
      simpa [H] using hsparse v
    have hgt : K < H.indepNum := by
      exact indepNum_gt_of_ESparse H hKpos hEK hKX' hdeg
    have hmono : H.indepNum ≤ G.indepNum := by
      simpa [H] using indepNum_induce_finset_le G X
    have homega : 1 ≤ G.cliqueNum := by
      have hnpos : 0 < Fintype.card V := Nat.zero_lt_of_lt hcritical.1
      let v : V := Classical.choice (Fintype.card_pos_iff.mp hnpos)
      have hs : G.IsClique ({v} : Finset V) := by simp
      simpa using hs.card_le_cliqueNum
    have halpha : G.indepNum ≤ K := by
      simpa [K, kappa, Lax54.GraphDefinitions.kappa] using
        Nat.mul_le_mul_right G.indepNum homega
    exact (hgt.trans_le (hmono.trans halpha)).false
  · let H := Gᶜ.induce (X : Set V)
    have hdeg : ∀ v : {x : V // x ∈ X},
        K ^ 3 * H.degree v ≤ Fintype.card {x : V // x ∈ X} := by
      intro v
      simpa [H] using hsparseCompl v
    have hgt : K < H.indepNum := by
      exact indepNum_gt_of_ESparse H hKpos hEK hKX' hdeg
    have hmono : H.indepNum ≤ Gᶜ.indepNum := by
      simpa [H] using indepNum_induce_finset_le Gᶜ X
    have halpha : 1 ≤ G.indepNum := by
      have hnpos : 0 < Fintype.card V := Nat.zero_lt_of_lt hcritical.1
      let v : V := Classical.choice (Fintype.card_pos_iff.mp hnpos)
      have hs : G.IsIndepSet ({v} : Finset V) := by simp
      simpa using hs.card_le_indepNum
    have homega : Gᶜ.indepNum ≤ K := by
      simp only [SimpleGraph.indepNum_compl]
      simpa [K, kappa, Lax54.GraphDefinitions.kappa] using
        Nat.mul_le_mul_left G.cliqueNum halpha
    exact (hgt.trans_le (hmono.trans homega)).false

/-- Strong induction reduces the house-free Erdős–Hajnal bound to the
restricted-set/uniform-blockade dichotomy. -/
theorem kappa_pow_bound_of_house_dichotomy
    (a : ℕ) (ha : 1 ≤ a)
    (hdichotomy : ∀ E : ℕ, 3 ≤ E →
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
        [DecidableRel G.Adj],
        IsHouseFree G →
          (∃ X : Finset V,
              Fintype.card V ≤ E ^ a * X.card ∧ ERestricted G E X) ∨
            HasUniformBlockade G E a) :
    ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
      IsHouseFree G → Fintype.card V ≤ kappa G ^ (3 * a + 2) := by
  classical
  let q := 3 * a + 2
  let P : ℕ → Prop := fun n ↦
    ∀ (V : Type u) [Fintype V] (G : SimpleGraph V),
      Fintype.card V = n → IsHouseFree G → Fintype.card V ≤ kappa G ^ q
  have hP : ∀ n : ℕ, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro V _ G hcard hfree
        by_contra hbound
        have hbad : kappa G ^ q < Fintype.card V := Nat.lt_of_not_ge hbound
        have hproper : ∀ S : Finset V, S.card < Fintype.card V →
            S.card ≤ kappa (G.induce (S : Set V)) ^ q := by
          intro S hS
          have hSn : S.card < n := by simpa [hcard] using hS
          have hsub := ih S.card hSn
          simpa only [Fintype.card_coe] using
            hsub {x : V // x ∈ S} (G.induce (S : Set V))
              (by simp) (IsHouseFree.induce_finset hfree S)
        have hcritical : IsQCritical q G := ⟨hbad, hproper⟩
        letI : DecidableRel G.Adj := Classical.decRel G.Adj
        have hK2 : 2 ≤ kappa G :=
          two_le_kappa_of_critical G (by simp [q]) hcritical
        have hE3 : 3 ≤ kappa G ^ 3 := by
          exact (by norm_num : 3 ≤ 2 ^ 3).trans (Nat.pow_le_pow_left hK2 3)
        rcases hdichotomy (kappa G ^ 3) hE3 G hfree with hrestricted | hblockade
        · obtain ⟨X, hlarge, hrest⟩ := hrestricted
          exact not_isQCritical_of_restricted a G
            (by simpa [q] using hcritical) X hlarge hrest
        · exact (not_isQCritical_of_uniform_blockade a q (kappa G ^ 3)
            (by simp [q]; omega) G hblockade) hcritical
  intro V _ G hfree
  simpa [q] using hP (Fintype.card V) V G rfl hfree

/-- The complement of a `P5`-free graph is house-free. -/
theorem IsP5Free.compl_isHouseFree
    {V : Type u} {G : SimpleGraph V} (hfree : IsP5Free G) :
    IsHouseFree Gᶜ := by
  intro hhouse
  apply hfree
  simpa [House] using hhouse.compl

/-- The homogeneous number is invariant under graph complementation. -/
@[simp] theorem homogeneousNumber_compl
    {V : Type u} (G : SimpleGraph V) :
    homogeneousNumber Gᶜ = homogeneousNumber G := by
  simp [homogeneousNumber, Lax54.GraphDefinitions.homogeneousNumber, max_comm]

/--
---
conclusion: Lax57.ErdosHajnalP5.erdos_hajnal_P5
assumptions:
  - Lax54.AveragingLemma.sparse_graph_thinning
  - Lax54.BipartiteCombLemma.bipartite_comb_lemma
  - Lax54.MaximumDegreeReduction.maximum_degree_reduction
  - Lax54.RodlTheorem.rodl_theorem
---
Apply the structural dichotomy to the complement of a $P_5$-free graph.
Strong induction reduces the proof to a critical graph. A large restricted
set and a uniform blockade each contradict criticality, the latter by
summing the blockwise values of $\kappa$. Finally,
$\kappa(G)\leq \max\{\alpha(G),\omega(G)\}^2$ gives the stated
Erdős–Hajnal bound.

# Attribution

The structural input is Lemma 7.3 of Nguyen, Scott, and Seymour. The
critical-graph argument is an integral reformulation specific to this
formalization.
-/
theorem erdos_hajnal_P5 :
    ∃ q : ℕ, 0 < q ∧
      ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
        IsP5Free G → Fintype.card V ≤ homogeneousNumber G ^ q := by
  obtain ⟨a, ha, hdichotomy⟩ := Lax57Proofs.house_dichotomy
  let q := 3 * a + 2
  refine ⟨2 * q, ?_, ?_⟩
  · simp [q]
  intro V _ G hfree
  have hkappa : Fintype.card V ≤ kappa Gᶜ ^ q :=
    kappa_pow_bound_of_house_dichotomy a ha hdichotomy Gᶜ
      (IsP5Free.compl_isHouseFree hfree)
  calc
    Fintype.card V ≤ kappa Gᶜ ^ q := hkappa
    _ ≤ (homogeneousNumber Gᶜ ^ 2) ^ q :=
      Nat.pow_le_pow_left (kappa_le_homogeneousNumber_sq Gᶜ) q
    _ = homogeneousNumber G ^ (2 * q) := by
      rw [pow_mul, homogeneousNumber_compl]

end Lax57Proofs
