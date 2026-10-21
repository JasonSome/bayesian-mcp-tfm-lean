import FCAppendix.Affine.UniformFinite.WeightedContinuation
import FCAppendix.Affine.ResidualPotential

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory Filter Topology Game
open scoped BigOperators

namespace Literal

def ramp (x : ℝ) : ℝ := max 0 (min 1 x)

theorem ramp_bounds (x : ℝ) : 0 ≤ ramp x ∧ ramp x ≤ 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem continuous_ramp : Continuous ramp := by
  unfold ramp
  fun_prop

theorem ramp_zero {x : ℝ} (hx : x ≤ 0) : ramp x = 0 := by
  rw [ramp, min_eq_right (hx.trans zero_le_one), max_eq_left hx]

theorem ramp_one {x : ℝ} (hx : 1 ≤ x) : ramp x = 1 := by
  simp [ramp, min_eq_left hx]

theorem ramp_pos_iff (x : ℝ) : 0 < ramp x ↔ 0 < x := by
  constructor
  · intro h
    by_contra hn
    rw [ramp_zero (le_of_not_gt hn)] at h
    exact (lt_irrefl 0) h
  · intro h
    exact lt_max_of_lt_right (lt_min zero_lt_one h)

def guardWeight {κ : Type*} [Fintype κ] (outer inner : ℝ) (s : κ → ℝ) : ℝ :=
  ∏ k, ramp ((s k - outer) / (inner - outer))

theorem guardWeight_bounds {κ : Type*} [Fintype κ]
    (outer inner : ℝ) (s : κ → ℝ) :
    0 ≤ guardWeight outer inner s ∧ guardWeight outer inner s ≤ 1 := by
  constructor
  · exact Finset.prod_nonneg (fun k _ => (ramp_bounds _).1)
  · exact Finset.prod_le_one (fun k _ => (ramp_bounds _).1)
      (fun k _ => (ramp_bounds _).2)

theorem continuous_guardWeight {κ : Type*} [Fintype κ] (outer inner : ℝ) :
    Continuous (guardWeight (κ := κ) outer inner) := by
  unfold guardWeight
  apply continuous_finsetProd
  intro k _
  exact continuous_ramp.comp (((continuous_apply k).sub continuous_const).div_const _)

theorem guardWeight_one {κ : Type*} [Fintype κ]
    {outer inner : ℝ} (hgap : outer < inner) (s : κ → ℝ)
    (hs : ∀ k, inner ≤ s k) : guardWeight outer inner s = 1 := by
  unfold guardWeight
  apply Finset.prod_eq_one
  intro k _
  apply ramp_one
  apply (le_div_iff₀ (sub_pos.mpr hgap)).2
  linarith [hs k]

theorem guardWeight_zero {κ : Type*} [Fintype κ]
    {outer inner : ℝ} (hgap : outer < inner) (s : κ → ℝ)
    (k : κ) (hs : s k ≤ outer) : guardWeight outer inner s = 0 := by
  classical
  unfold guardWeight
  apply Finset.prod_eq_zero (Finset.mem_univ k)
  exact ramp_zero (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs)
    (sub_pos.mpr hgap).le)

theorem guardWeight_pos_outer {κ : Type*} [Fintype κ]
    {outer inner : ℝ} (hgap : outer < inner) (s : κ → ℝ)
    (ha : 0 < guardWeight outer inner s) : ∀ k, outer < s k := by
  intro k
  by_contra hn
  rw [guardWeight_zero hgap s k (le_of_not_gt hn)] at ha
  exact (lt_irrefl 0) ha

theorem guard_times_bounded_tendsto_zero {X : Type*} {l : Filter X}
    (α f : X → ℝ) (C : ℝ) (_hC : 0 ≤ C)
    (hα : Tendsto α l (𝓝 0)) (hf : ∀ᶠ x in l, |f x| ≤ C) :
    Tendsto (fun x => α x * f x) l (𝓝 0) := by
  have habs : Tendsto (fun x => |α x| * C) l (𝓝 0) := by
    simpa using hα.abs.mul_const C
  apply squeeze_zero_norm' _ habs
  filter_upwards [hf] with x hx
  simpa only [Real.norm_eq_abs, abs_mul] using
    mul_le_mul_of_nonneg_left hx (abs_nonneg (α x))

def rejectionStatistic (d₀ z b : ℝ) : ℝ :=
  max 0 (b - z) / (d₀ + max 0 (b - z))

theorem rejectionStatistic_zero {d₀ z b : ℝ} (hb : b ≤ z) :
    rejectionStatistic d₀ z b = 0 := by
  simp [rejectionStatistic, max_eq_left (sub_nonpos.mpr hb)]

theorem rejectionStatistic_bounds {d₀ z b : ℝ} (hd : 0 < d₀) :
    0 ≤ rejectionStatistic d₀ z b ∧ rejectionStatistic d₀ z b ≤ 1 := by
  have hm : 0 ≤ max 0 (b - z) := le_max_left _ _
  have hden : 0 < d₀ + max 0 (b - z) := by linarith
  refine ⟨div_nonneg hm hden.le, ?_⟩
  apply (div_le_one hden).2
  linarith

theorem rejection_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    {d₀ z : ℝ} (hd : 0 < d₀) (b : ι → ℝ) :
    (∑ i, rejectionStatistic d₀ z (b i)) ≤
      ((Finset.univ.filter (fun i => z < b i)).card : ℝ) := by
  classical
  have he : ((Finset.univ.filter (fun i => z < b i)).card : ℝ) =
      ∑ i, if z < b i then (1 : ℝ) else 0 := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro j _
    split <;> norm_num
  rw [he]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : z < b i
  · simpa only [if_pos hi] using (rejectionStatistic_bounds (z := z) (b := b i) hd).2
  · simp only [if_neg hi, rejectionStatistic_zero (le_of_not_gt hi)]
    exact le_rfl

private theorem score_le_bid {m : ℕ} {κ : ℝ} (hκ1 : κ ≤ 1)
    (L : LocalList m) (i : Fin m) (T : Finset (Fin m)) :
    (if i ∈ T then κ * ResidualPotential.bid L i else ResidualPotential.bid L i) ≤
      ResidualPotential.bid L i := by
  split
  · exact mul_le_of_le_one_left (le_max_right _ _) hκ1
  · exact le_rfl

private theorem bestReply_rejects_low {m : ℕ} {κ z : ℝ} (hκ1 : κ ≤ 1)
    (L : LocalList m) (r₀ r₁ : ℕ) (S T : Finset (Fin m))
    (hS : LocallyFeasible L r₀ S) (hT : LocallyFeasible L r₁ T)
    (hhigh : r₀ + r₁ <
      (Finset.univ.filter (fun i => L i ≠ none ∧ z < ResidualPotential.bid L i)).card)
    (hN : ∀ D, LocallyFeasible L r₀ D →
      LowBody.CompleteInformation.revenue κ (ResidualPotential.bid L) D T ≤
        LowBody.CompleteInformation.revenue κ (ResidualPotential.bid L) S T)
    (i : Fin m) (hi : ResidualPotential.bid L i ≤ z) : i ∉ S := by
  classical
  intro hiS
  let A := Finset.univ.filter (fun j => L j ≠ none ∧ z < ResidualPotential.bid L j)
  have hcard : (S ∪ T).card < A.card := by
    have hST : (S ∪ T).card ≤ S.card + T.card := Finset.card_union_le S T
    exact (hST.trans (Nat.add_le_add hS.1 hT.1)).trans_lt hhigh
  obtain ⟨j, hjA, hjST⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hjL : L j ≠ none := (Finset.mem_filter.mp hjA).2.1
  have hjb : z < ResidualPotential.bid L j := (Finset.mem_filter.mp hjA).2.2
  have hjS : j ∉ S := fun hj => hjST (Finset.mem_union_left _ hj)
  have hjT : j ∉ T := fun hj => hjST (Finset.mem_union_right _ hj)
  have hjE : j ∉ S.erase i := fun hj => hjS (Finset.mem_of_mem_erase hj)
  let D := insert j (S.erase i)
  have hD : LocallyFeasible L r₀ D := by
    constructor
    · dsimp [D]
      rw [Finset.card_insert_of_notMem hjE, Finset.card_erase_of_mem hiS]
      have hic : 0 < S.card := Finset.card_pos.mpr ⟨i, hiS⟩
      have hScard := hS.1
      omega
    · intro k hk
      rcases Finset.mem_insert.mp hk with hk | hk
      · exact hk ▸ hjL
      · exact hS.2 k (Finset.mem_of_mem_erase hk)
  have hdev := hN D hD
  have herase := Finset.sum_erase_add S
    (fun k => if k ∈ T then κ * ResidualPotential.bid L k else ResidualPotential.bid L k) hiS
  unfold LowBody.CompleteInformation.revenue at hdev
  dsimp only [D] at hdev
  rw [Finset.sum_insert hjE, if_neg hjT] at hdev
  have hreceipt := score_le_bid hκ1 L i T
  linarith

theorem pure_selection_rejects {m : ℕ} {κ z : ℝ}
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (L : LocalList m) (r₀ r₁ : ℕ)
    (hhigh : r₀ + r₁ <
      (Finset.univ.filter (fun i => L i ≠ none ∧ z < ResidualPotential.bid L i)).card)
    (i : Fin m) (hi : ResidualPotential.bid L i ≤ z) :
    i ∉ (ResidualPotential.selection κ L r₀ r₁).1 ∧
      i ∉ (ResidualPotential.selection κ L r₀ r₁).2 := by
  have hf := ResidualPotential.selection_feasible κ hκ0 L r₀ r₁
  have hn := ResidualPotential.selection_nash κ hκ0 L r₀ r₁
  exact ⟨bestReply_rejects_low hκ1 L r₀ r₁ _ _ hf.1 hf.2 hhigh hn.1 i hi,
    bestReply_rejects_low hκ1 L r₁ r₀ _ _ hf.2 hf.1
      (by simpa only [Nat.add_comm] using hhigh) hn.2 i hi⟩

theorem pure_selection_rejects_of_statistic {m : ℕ} {κ z d₀ slack : ℝ}
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hz : 0 ≤ z) (hd : 0 < d₀)
    (hs : 0 ≤ slack) (L : LocalList m) (r₀ r₁ : ℕ)
    (hg : ((r₀ + r₁ : ℕ) : ℝ) + slack <
      ∑ i, rejectionStatistic d₀ z (ResidualPotential.bid L i))
    (i : Fin m) (hi : ResidualPotential.bid L i ≤ z) :
    i ∉ (ResidualPotential.selection κ L r₀ r₁).1 ∧
      i ∉ (ResidualPotential.selection κ L r₀ r₁).2 := by
  have hc := rejection_count (z := z) hd (ResidualPotential.bid L)
  have he : Finset.univ.filter (fun j => z < ResidualPotential.bid L j) =
      Finset.univ.filter (fun j => L j ≠ none ∧ z < ResidualPotential.bid L j) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hj
      refine ⟨?_, hj⟩
      intro hjL
      have hb : ResidualPotential.bid L j = 0 := by
        simp [ResidualPotential.bid, hjL, Bayes.entryBid]
      rw [hb] at hj
      exact (not_lt_of_ge hz) hj
    · exact And.right
  rw [he] at hc
  apply pure_selection_rejects hκ0 hκ1 L r₀ r₁ _ i hi
  have hc' : ((r₀ + r₁ : ℕ) : ℝ) <
      ((Finset.univ.filter (fun j => L j ≠ none ∧ z < ResidualPotential.bid L j)).card : ℝ) :=
    by linarith
  exact_mod_cast hc'

def signalLaw {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (w : WeightedSampling.Weights ι) (Δ : ℕ) (α : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    FiniteLaw (Option (WeightedSampling.Path ι Δ)) :=
  FiniteLaw.mixture ((WeightedSampling.pathLaw w Δ ∅).map some)
    (FiniteLaw.dirac none) α hα0 hα1

theorem signalLaw_expect {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (w : WeightedSampling.Weights ι) (Δ : ℕ) (α : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (f : Option (WeightedSampling.Path ι Δ) → ℝ) :
    (signalLaw w Δ α hα0 hα1).expect f =
      α * (WeightedSampling.pathLaw w Δ ∅).expect (fun p => f (some p)) +
        (1 - α) * f none := by
  rw [signalLaw, FiniteLaw.expect_mixture, FiniteLaw.expect_map, FiniteLaw.expect_dirac]

theorem signal_dependent_comparison {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (w : WeightedSampling.Weights ι) (Δ : ℕ) (α : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (inc dev : Option (WeightedSampling.Path ι Δ) → ℝ)
    (hnone : dev none ≤ inc none)
    (hsome : ∀ p, 0 < (WeightedSampling.pathLaw w Δ ∅).mass p →
      dev (some p) ≤ inc (some p)) :
    (signalLaw w Δ α hα0 hα1).expect dev ≤
      (signalLaw w Δ α hα0 hα1).expect inc := by
  rw [signalLaw_expect, signalLaw_expect]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (WeightedSampling.expect_le_of_support _ _ _ hsome) hα0)
    (mul_le_mul_of_nonneg_left hnone (sub_nonneg.mpr hα1))

end Literal
end FCAppendix.Affine.UniformFinite
