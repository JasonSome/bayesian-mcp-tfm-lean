import FCAppendix.Affine.Uniform06.LiteralExperiment
import FCAppendix.Affine.Uniform06.EqualCanonicalRegularity

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.SourceGuardGeometry
open Set MeasureTheory LowBody
open FCAppendix.Affine.ClippedResidual FCAppendix.Affine.WeightedSampling
open LiteralExperiment FiniteGuards
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
theorem positive_guard_slacks {ξ : ℝ} (g : GuardData) (T : PureTemplate ι)
    (b : ι → ℝ) (hε : 0 < g.margin) (hM : 0 < g.population)
    (hα : 0 < guardAlpha ξ g T b) :
    seeded g T b ∧ ∀ k : Fin 5, g.margin*g.population < slackVector ξ g T b k := by
  classical
  have hseed : seeded g T b := by
    by_contra hs
    simp [guardAlpha,FiniteGuards.alpha,hs] at hα
  refine ⟨hseed,?_⟩
  intro k
  have hp : 0 < ramp (2*g.margin*g.population) (g.margin*g.population)
      (slackVector ξ g T b k) := by
    by_contra hk
    have hz : ramp (2*g.margin*g.population) (g.margin*g.population)
        (slackVector ξ g T b k)=0 :=
      le_antisymm (le_of_not_gt hk) (ramp_bounds _ _ _).1
    have hzprod : (∏ l : Fin 5, ramp (2*g.margin*g.population) (g.margin*g.population)
        (slackVector ξ g T b l))=0 :=
      Finset.prod_eq_zero (Finset.mem_univ k) hz
    simp only [guardAlpha,FiniteGuards.alpha,if_pos hseed,hzprod] at hα
    exact lt_irrefl _ hα
  exact ramp_positive_slack
    (show g.margin*g.population < 2*g.margin*g.population by nlinarith [mul_pos hε hM]) hp

omit [Nonempty ι] in
theorem positive_guard_weight {ξ : ℝ} (g : GuardData) (T : PureTemplate ι)
    (b : ι → ℝ) (hε : 0 < g.margin) (hM : 0 < g.population)
    (hα : 0 < guardAlpha ξ g T b) :
    (imbalance T : ℝ)+g.margin*g.population < totalWeight (weights ξ g T b) := by
  have hh := (positive_guard_slacks g T b hε hM hα).2 (2:Fin 5)
  change g.margin*g.population < totalWeight (weights ξ g T b) - (imbalance T : ℝ) at hh
  linarith

omit [Nonempty ι] in
theorem positive_guard_lower_demand {ξ : ℝ} (g : GuardData) (T : PureTemplate ι)
    (b : ι → ℝ) (hε : 0 < g.margin) (hM : 0 < g.population)
    (hα : 0 < guardAlpha ξ g T b) :
    (small T : ℝ)+imbalance T+g.margin*g.population <
      demand ξ T b (g.multiplier-g.radius) := by
  have hh := (positive_guard_slacks g T b hε hM hα).2 (0:Fin 5)
  simp only [slackVector,Matrix.cons_val_zero] at hh
  linarith

omit [Nonempty ι] in
theorem positive_guard_rejection {ξ : ℝ} (g : GuardData) (T : PureTemplate ι)
    (b : ι → ℝ) (hε : 0 < g.margin) (hM : 0 < g.population)
    (hα : 0 < guardAlpha ξ g T b) :
    (T.residual₀ : ℝ)+T.residual₁ <
      ∑ j ∈ T.support, PrefixRoot.psi g.rejectionScale g.rejectionRoot (b j) := by
  have hh := (positive_guard_slacks g T b hε hM hα).2 (3:Fin 5)
  change g.margin*g.population <
    (∑ j ∈ T.support, PrefixRoot.psi g.rejectionScale g.rejectionRoot (b j)) -
      (T.residual₀ : ℝ) - T.residual₁ at hh
  nlinarith [mul_pos hε hM]

omit [DecidableEq ι] [Nonempty ι] in
theorem psi_sum_le_higher_count (T : PureTemplate ι) (b : ι → ℝ)
    {d z x : ℝ} (hd : 0 < d) (hxz : x ≤ z) :
    (∑ j ∈ T.support, PrefixRoot.psi d z (b j)) ≤
      ((Finset.univ.filter (fun j => x < b j)).card : ℝ) := by
  have hterm (j : ι) : PrefixRoot.psi d z (b j) ≤ if x < b j then 1 else 0 := by
    by_cases hx : x < b j
    · simpa [hx] using (PrefixRoot.psi_bounds (z := z) (b := b j) hd).2
    · have hz : b j ≤ z := (le_of_not_gt hx).trans hxz
      simp [hx,PrefixRoot.psi,max_eq_left (sub_nonpos.mpr hz)]
  calc
    _ ≤ ∑ j ∈ T.support, if x < b j then (1:ℝ) else 0 :=
      Finset.sum_le_sum (fun j _ => hterm j)
    _ ≤ ∑ j : ι, if x < b j then (1:ℝ) else 0 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro j _ _
      split_ifs <;> norm_num
    _ = _ := by simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one ]

omit [Nonempty ι] in

theorem pure_rejects_under_positive_guard {ξ κ : ℝ} (hκ1 : κ ≤ 1)
    (g : GuardData) (T : PureTemplate ι) (b : ι → ℝ)
    (hε : 0 < g.margin) (hM : 0 < g.population) (hd : 0 < g.rejectionScale)
    (hz : ∀ j, j ∉ T.support → b j=0) (j : ι)
    (hb : 0 ≤ b j) (hbz : b j ≤ g.rejectionRoot)
    (hα : 0 < guardAlpha ξ g T b) : j ∉ (T.selection κ b).1 ∪ (T.selection κ b).2 := by
  intro hj
  have hcount := PureRankSelector.selected_implies_fewer_high_bids_than_total_residual
    T hκ1 b hz j hb hj
  have hcountR : ((Finset.univ.filter (fun k => b j < b k)).card : ℝ) <
      (T.residual₀ : ℝ)+T.residual₁ := by exact_mod_cast hcount
  have hψ := psi_sum_le_higher_count T b hd hbz
  have hguard := positive_guard_rejection g T b hε hM hα
  linarith

omit [Fintype ι] [Nonempty ι] in
theorem masked_zero_outside (T : PureTemplate ι) (b : ι → ℝ) (E : Finset ι)
    (j : ι) (hj : j ∉ T.support) : maskedBids T b E j=0 := by simp [maskedBids,hj]

omit [DecidableEq ι] [Nonempty ι] in
theorem demand_eq_full {ξ z : ℝ} (hz : 0 < z)
    (T : PureTemplate ι) (b : ι → ℝ)
    (hout : ∀ j, j ∉ T.support → b j=0) :
    demand ξ T b z=∑ j, exposure ξ z (b j) := by
  unfold demand
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j _ hj
  rw [hout j hj,exposure_zero hz.le]

omit [Nonempty ι] in
theorem masked_exposure_sum {ξ z : ℝ} (hz : 0 < z)
    (T : PureTemplate ι) (b : ι → ℝ) (E : Finset ι)
    (hout : ∀ j, j ∉ T.support → b j=0) :
    (∑ j, exposure ξ z (maskedBids T b E j))=remainingDemand ξ b E z := by
  apply Finset.sum_congr rfl
  intro j _
  by_cases hjE : j ∈ E
  · simp [maskedBids,hjE,exposure_zero hz.le]
  · by_cases hjT : j ∈ T.support
    · simp [maskedBids,hjE,hjT]
    · simp [maskedBids,hjE,hjT,hout j hjT,exposure_zero hz.le]

omit [Nonempty ι] in

theorem complement_rejects_below_lower_guard {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (g : GuardData) (T : PureTemplate ι) (b : ι → ℝ)
    (hε : 0 < g.margin) (hM : 0 < g.population)
    (hlo : 0 < g.multiplier-g.radius)
    (hout : ∀ j, j ∉ T.support → b j=0)
    (hα : 0 < guardAlpha ξ g T b)
    (E : Finset ι) (hE : E.card ≤ imbalance T) (j : ι)
    (hb : b j ≤ g.multiplier-g.radius) : complementMarginal ξ T b E j=0 := by
  let B := maskedBids T b E
  have hp := EqualCapacity.positiveMarginal_spec ξ (small T) hξ hξ1 B
  apply le_antisymm _ (hp.1 j)
  by_contra hnot
  have hpos : 0 < EqualCapacity.positiveMarginal ξ (small T) B j := lt_of_not_ge hnot
  have hBj0 : 0 < B j := by
    by_contra hB
    have hnone : j ∉ Existence.PayOnceBounded.positiveSupport B := by
      simpa only [Existence.PayOnceBounded.mem_positiveSupport] using hB
    have hzB := EqualCapacity.onSupport_outside ξ (small T)
      (Existence.PayOnceBounded.positiveSupport B) B j hnone
    change EqualCapacity.positiveMarginal ξ (small T) B j=0 at hzB
    rw [hzB] at hpos
    exact lt_irrefl _ hpos
  have hBj : B j ≤ g.multiplier-g.radius := by
    dsimp [B,maskedBids]
    split_ifs
    · exact hb
    · exact hlo.le
  have hle := EqualCanonicalRegularity.actual_rival_exposures_le_marginals
    hξ hξ1 hlo (small T) B j hBj0 hBj hpos
  have hs := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset ι)) => hle k)
  have hsum : (∑ k, EqualCapacity.positiveMarginal ξ (small T) B k) ≤ (small T : ℝ) := by
    rw [hp.2.2]
    exact_mod_cast (Nat.min_le_left (small T) (Existence.PayOnceBounded.positiveSupport B).card)
  have hlow := positive_guard_lower_demand g T b hε hM hα
  rw [demand_eq_full hlo T b hout] at hlow
  have hremove := (removal_changes_demand_by_at_most_card ξ (g.multiplier-g.radius)
    b hξ hlo E).1
  have hER : (E.card : ℝ) ≤ imbalance T := by exact_mod_cast hE
  have hmasked := masked_exposure_sum (ξ := ξ) hlo T b E hout
  change (∑ k, exposure ξ (g.multiplier-g.radius) (B k))=remainingDemand ξ b E
    (g.multiplier-g.radius) at hmasked
  rw [hmasked] at hs
  nlinarith [mul_pos hε hM]

omit [Fintype ι] [Nonempty ι] in
theorem low_focal_weight_zero {ξ : ℝ} (g : GuardData) (T : PureTemplate ι)
    (b : ι → ℝ) (j : ι) (hr : 0 < g.requiredDemand)
    (hb : b j ≤ g.multiplier) : (weights ξ g T b).1 j=0 := by
  unfold weights
  dsimp only
  split_ifs
  · apply FiniteGuards.eligibility_zero hr
    rw [exposure_zero hb]
    positivity
  · rfl

theorem canonical_low_focal_zero {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (g : GuardData) (T : PureTemplate ι) (b : ι → ℝ)
    (hε : 0 < g.margin) (hM : 0 < g.population) (ha : 0 ≤ g.radius)
    (hr : 0 < g.requiredDemand) (hlo : 0 < g.multiplier-g.radius)
    (hout : ∀ j, j ∉ T.support → b j=0) (j : ι)
    (hb : b j ≤ g.multiplier-g.radius) :
    guardAlpha ξ g T b*(canonicalLaw ξ g T b).expect (first j)=0 ∧
      guardAlpha ξ g T b*(canonicalLaw ξ g T b).expect (duplicate j)=0 := by
  by_cases hα : 0 < guardAlpha ξ g T b
  · have hW : (imbalance T : ℝ) < totalWeight (weights ξ g T b) := by
      nlinarith [positive_guard_weight g T b hε hM hα,mul_pos hε hM]
    have hw := low_focal_weight_zero (ξ := ξ) g T b j hr (by linarith)
    have hfirst : (canonicalLaw ξ g T b).expect (first j)=0 := by
      rw [canonical_path_first hξ hξ1]
      apply le_antisymm
      · apply expect_le_const
        intro path hp
        have hc := finalSet_card (weights ξ g T b) (imbalance T) ∅ (by simpa using hW) path hp
        have hcard : (finalSet (imbalance T) ∅ path).card ≤ imbalance T := by simpa using hc.le
        have hz := complement_rejects_below_lower_guard hξ hξ1 g T b hε hM hlo
          hout hα _ hcard j hb
        rw [if_neg (focal_not_sampled_of_zero_weight ξ g T b j hW hw path hp),hz]
        norm_num
      · apply expect_nonneg
        intro path
        dsimp only
        split_ifs
        · norm_num
        · have hp := EqualCapacity.positiveMarginal_spec ξ (small T) hξ hξ1
            (maskedBids T b (finalSet (imbalance T) ∅ path))
          change 0 ≤ 2*complementMarginal ξ T b _ j-(complementMarginal ξ T b _ j)^2
          have hp0 : 0 ≤ complementMarginal ξ T b _ j := hp.1 j
          have hp1 : complementMarginal ξ T b _ j ≤ 1 := hp.2.1 j
          nlinarith
    have hdup : (canonicalLaw ξ g T b).expect (duplicate j)=0 := by
      rw [canonical_path_duplicate hξ hξ1]
      apply le_antisymm
      · apply expect_le_const
        intro path hp
        have hc := finalSet_card (weights ξ g T b) (imbalance T) ∅ (by simpa using hW) path hp
        have hz := complement_rejects_below_lower_guard hξ hξ1 g T b hε hM hlo
          hout hα _ (by simpa using hc.le) j hb
        rw [hz]
        norm_num
      · exact expect_nonneg _ _ (fun _ => sq_nonneg _)
    simp [hfirst,hdup]
  · have hz : guardAlpha ξ g T b=0 := le_antisymm (le_of_not_gt hα)
      (guardAlpha_bounds ξ g T b).1
    simp [hz]

theorem unequal_low_full_eq_pure {ξ κ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hκ1 : κ ≤ 1) (g : GuardData) (T : PureTemplate ι) (b : ι → ℝ)
    (hε : 0 < g.margin) (hM : 0 < g.population) (ha : 0 ≤ g.radius)
    (hr : 0 < g.requiredDemand) (hd : 0 < g.rejectionScale)
    (hlo : 0 < g.multiplier-g.radius)
    (hout : ∀ j, j ∉ T.support → b j=0) (j : ι)
    (hb0 : 0 ≤ b j) (hb : b j ≤ g.multiplier-g.radius)
    (hbz : b j ≤ g.rejectionRoot) (hne : T.residual₀ ≠ T.residual₁) :
    (continuationLaw ξ κ g T b).expect (first j)=first j (T.selection κ b) ∧
      (continuationLaw ξ κ g T b).expect (duplicate j)=duplicate j (T.selection κ b) := by
  have hzC := canonical_low_focal_zero hξ hξ1 g T b hε hM ha hr hlo hout j hb
  have hzP : guardAlpha ξ g T b*first j (T.selection κ b)=0 ∧
      guardAlpha ξ g T b*duplicate j (T.selection κ b)=0 := by
    by_cases hα : 0 < guardAlpha ξ g T b
    · have hrj := pure_rejects_under_positive_guard hκ1 g T b hε hM hd hout j hb0 hbz hα
      have h0 : j ∉ (T.selection κ b).1 := fun h => hrj (Finset.mem_union_left _ h)
      have h1 : j ∉ (T.selection κ b).2 := fun h => hrj (Finset.mem_union_right _ h)
      simp [first,duplicate,LiteralExperiment.indicator,h0,h1]
    · have hz : guardAlpha ξ g T b=0 := le_antisymm (le_of_not_gt hα)
        (guardAlpha_bounds ξ g T b).1
      simp [hz]
  simp only [continuationLaw,if_neg hne,FiniteLaw.expect_mixture,FiniteLaw.expect_dirac]
  constructor <;> nlinarith [hzC.1,hzC.2,hzP.1,hzP.2]

end FCAppendix.Affine.Uniform06.SourceGuardGeometry
