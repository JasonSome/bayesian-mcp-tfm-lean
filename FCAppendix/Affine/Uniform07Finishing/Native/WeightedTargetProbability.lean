import FCAppendix.Affine.Uniform07Finishing.Native.SourceGuards
import FCAppendix.Affine.Uniform07Finishing.Native.SeedValueInvariance
import FCAppendix.Probability.FinitePushforward

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Set Classical
open FCAppendix.Affine
open scoped BigOperators

namespace WeightedSampling
open FCAppendix.Affine.WeightedSampling
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Fintype ι] [Nonempty ι] in
lemma indicator_finalSet_le_draw_count (i : ι) (n : ℕ) (S : Finset ι)
    (p : Path ι n) :
    indicator i (finalSet n S p) ≤ indicator i S +
      selectedSum (fun k => if k = i then (1 : ℝ) else 0) n p := by
  induction n generalizing S with
  | zero => simp [finalSet, selectedSum]
  | succ n ih =>
      have ht := ih (insert p.1 S) p.2
      have hs : indicator i (insert p.1 S) ≤ indicator i S +
          (if p.1 = i then (1 : ℝ) else 0) := by
        by_cases hp : p.1 = i
        · subst i
          by_cases hi : p.1 ∈ S <;> simp [FCAppendix.Affine.WeightedSampling.indicator, hi]
        · have hn : i ≠ p.1 := Ne.symm hp
          by_cases hi : i ∈ S <;> simp [FCAppendix.Affine.WeightedSampling.indicator, hi, hp, hn]
      change indicator i (finalSet n (insert p.1 S) p.2) ≤
        indicator i S + ((if p.1 = i then (1 : ℝ) else 0) +
          selectedSum (fun k => if k = i then (1 : ℝ) else 0) n p.2)
      linarith

lemma oneDraw_target_le (w : Weights ι) (D : ℕ) (S : Finset ι)
    (hS : S.card ≤ D) (hW : (D : ℝ) < totalWeight w) (i : ι) :
    (oneDraw w S).expect (fun k => if k = i then (1 : ℝ) else 0) ≤
      1 / (totalWeight w - D) := by
  have hC : 0 < totalWeight w - D := sub_pos.mpr hW
  have hcard : (S.card : ℝ) ≤ D := by exact_mod_cast hS
  have hden : totalWeight w - D ≤ remainingWeight w S := by
    linarith [denominator_lower w S]
  have hrem : 0 < remainingWeight w S := hC.trans_le hden
  have he : (oneDraw w S).expect (fun k => if k = i then (1 : ℝ) else 0) =
      (oneDraw w S).mass i := by
    simp [FiniteLaw.expect]
  rw [he, oneDraw_mass w S hrem]
  by_cases hi : i ∈ S
  · simp only [if_pos hi, zero_div]
    exact div_nonneg zero_le_one hC.le
  · simp only [if_neg hi]
    calc
      w.1 i / remainingWeight w S ≤ 1 / remainingWeight w S :=
        div_le_div_of_nonneg_right (w.2 i).2 hrem.le
      _ ≤ 1 / (totalWeight w - D) := one_div_le_one_div_of_le hC hden

lemma expected_target_draw_count_le (w : Weights ι) (D n : ℕ) (S : Finset ι)
    (hsize : S.card + n ≤ D) (hW : (D : ℝ) < totalWeight w) (i : ι) :
    (pathLaw w n S).expect
      (selectedSum (fun k => if k = i then (1 : ℝ) else 0) n) ≤
        (n : ℝ) / (totalWeight w - D) := by
  induction n generalizing S with
  | zero => simp [selectedSum, FiniteLaw.expect_const]
  | succ n ih =>
      have hS : S.card ≤ D := by omega
      have hC : 0 < totalWeight w - D := sub_pos.mpr hW
      have hrem : 0 < remainingWeight w S := by
        have hcard : (S.card : ℝ) ≤ D := by exact_mod_cast hS
        linarith [denominator_lower w S]
      rw [expect_path_succ]
      calc
        (oneDraw w S).expect (fun j =>
            (pathLaw w n (insert j S)).expect (fun p =>
              selectedSum (fun k => if k = i then (1 : ℝ) else 0) (n+1) (j,p))) ≤
          (oneDraw w S).expect (fun j =>
            (if j = i then (1 : ℝ) else 0) + (n : ℝ) / (totalWeight w - D)) := by
              apply FCAppendix.Affine.WeightedSampling.expect_le_of_support
              intro j hj
              have hjS := (oneDraw_support w S hrem hj).1
              have hnext : (insert j S).card + n ≤ D := by
                rw [Finset.card_insert_of_notMem hjS]
                omega
              have hh := ih (insert j S) hnext
              by_cases hji : j=i
              · simpa only [selectedSum, if_pos hji, FiniteLaw.expect_add, FiniteLaw.expect_const]
                  using add_le_add (le_refl (1:ℝ)) hh
              · simpa only [selectedSum, if_neg hji, FiniteLaw.expect_add, FiniteLaw.expect_const]
                  using add_le_add (le_refl (0:ℝ)) hh
        _ = (oneDraw w S).expect (fun j => if j = i then (1 : ℝ) else 0) +
              (n : ℝ) / (totalWeight w - D) := by
              rw [FiniteLaw.expect_add, FiniteLaw.expect_const]
        _ ≤ 1 / (totalWeight w - D) + (n : ℝ) / (totalWeight w - D) :=
              add_le_add (oneDraw_target_le w D S hS hW i) (le_refl _)
        _ = ((n+1 : ℕ) : ℝ) / (totalWeight w - D) := by push_cast; ring

theorem fixed_target_probability_le (w : Weights ι) (d : ℕ)
    (hW : (d : ℝ) < totalWeight w) (i : ι) :
    (pathLaw w d ∅).expect (fun p => indicator i (finalSet d ∅ p)) ≤
      (d : ℝ) / (totalWeight w - d) := by
  have hfirst : (pathLaw w d ∅).expect (fun p => indicator i (finalSet d ∅ p)) ≤
      (pathLaw w d ∅).expect
        (selectedSum (fun k => if k = i then (1 : ℝ) else 0) d) := by
    apply FCAppendix.Affine.WeightedSampling.expect_le_of_support
    intro p _
    simpa only [FCAppendix.Affine.WeightedSampling.indicator, Finset.notMem_empty, if_false, zero_add]
      using indicator_finalSet_le_draw_count i d ∅ p
  exact hfirst.trans (expected_target_draw_count_le w d d ∅ (by simp) hW i)

theorem fixed_target_probability_le_linear_slack (w : Weights ι) (d : ℕ)
    {ε M : ℝ} (hε : 0 < ε) (hM : 0 < M)
    (hW : ε*M ≤ totalWeight w - d) (i : ι) :
    (pathLaw w d ∅).expect (fun p => indicator i (finalSet d ∅ p)) ≤
      (d : ℝ) / (ε*M) := by
  have hslack : 0 < ε*M := mul_pos hε hM
  have hd : (d : ℝ) < totalWeight w := by linarith
  exact (fixed_target_probability_le w d hd i).trans
    (div_le_div_of_nonneg_left (Nat.cast_nonneg d) hslack hW)

end WeightedSampling

namespace Weighted
variable {m : ℕ} [Nonempty (Fin m)]

local instance : DiscreteMeasurableSpace (Option (Finset (Fin m))) :=
  ⟨fun s => by
    change MeasurableSet ((some : Finset (Fin m) → Option (Finset (Fin m))) ⁻¹' s)
    exact MeasurableSet.of_discrete⟩

def planTargetIndicator (i : Fin m) : Option (Finset (Fin m)) → ℝ
  | none => 0
  | some E => FCAppendix.Affine.WeightedSampling.indicator i E

lemma planLaw_none_mass (d : ℕ) (α : unitInterval)
    (w : FCAppendix.Affine.WeightedSampling.Weights (Fin m)) :
    (planLaw d α w).mass none = 1-(α : ℝ) := by
  simp [planLaw, FiniteLaw.mixture, FiniteLaw.map, FiniteLaw.dirac]

lemma planSampler_one_isSome (d : ℕ) (w : FCAppendix.Affine.WeightedSampling.Weights (Fin m))
    (s : unitInterval) : ∃ E, planSampler d (1,w) s = some E := by
  cases he : planSampler d (1,w) s with
  | some E => exact ⟨E,rfl⟩
  | none =>
      have hp := planSampler_support d (1,w) s
      rw [he,planLaw_none_mass] at hp
      norm_num at hp

lemma planLaw_target_expect (d : ℕ) (α : unitInterval)
    (w : FCAppendix.Affine.WeightedSampling.Weights (Fin m)) (i : Fin m) :
    (planLaw d α w).expect (planTargetIndicator i) =
      (α : ℝ)*(FCAppendix.Affine.WeightedSampling.pathLaw w d ∅).expect
        (fun p => FCAppendix.Affine.WeightedSampling.indicator i (FCAppendix.Affine.WeightedSampling.finalSet d ∅ p)) := by
  rw [planLaw_expect]
  simp only [planTargetIndicator, mul_zero, add_zero]

theorem planLaw_target_expect_le (d : ℕ) (α : unitInterval)
    (w : FCAppendix.Affine.WeightedSampling.Weights (Fin m))
    (hW : (d : ℝ) < FCAppendix.Affine.WeightedSampling.totalWeight w) (i : Fin m) :
    (planLaw d α w).expect (planTargetIndicator i) ≤
      (d : ℝ) / (FCAppendix.Affine.WeightedSampling.totalWeight w - d) := by
  rw [planLaw_target_expect]
  have hn : 0 ≤ (FCAppendix.Affine.WeightedSampling.pathLaw w d ∅).expect
      (fun p => FCAppendix.Affine.WeightedSampling.indicator i (FCAppendix.Affine.WeightedSampling.finalSet d ∅ p)) := by
    apply FiniteLaw.expect_nonneg
    intro p
    unfold FCAppendix.Affine.WeightedSampling.indicator
    split_ifs <;> norm_num
  exact (mul_le_of_le_one_left hn α.2.2).trans
    (WeightedSampling.fixed_target_probability_le w d hW i)

theorem planSampler_target_integral_le (d : ℕ) (α : unitInterval)
    (w : FCAppendix.Affine.WeightedSampling.Weights (Fin m))
    (hW : (d : ℝ) < FCAppendix.Affine.WeightedSampling.totalWeight w) (i : Fin m) :
    (∫ s : unitInterval, planTargetIndicator i (planSampler d (α,w) s)) ≤
      (d : ℝ) / (FCAppendix.Affine.WeightedSampling.totalWeight w - d) := by
  have hs : Measurable (planSampler d (α,w)) :=
    (measurable_planSampler d).comp (measurable_const.prodMk measurable_id)
  have hf : Measurable (planTargetIndicator i) := measurable_of_countable _
  have hflaw : FiniteLaw.ofMeasure (volume : Measure unitInterval)
      (planSampler d (α,w)) hs = planLaw d α w :=
    FiniteLaw.ofMeasure_eq_of_map_eq_probabilityMeasure _ _ hs _ (planSampler_law d (α,w))
  rw [← FiniteLaw.expect_ofMeasure _ _ hs, hflaw]
  exact planLaw_target_expect_le d α w hW i

theorem sourcePlan_omits_zero_weight (ξ Λ r U zs : ℝ) (c : ℕ) (μseed : Measure ℝ)
    (α : StrictNative.ClassifiedContext m → unitInterval)
    (X : StrictNative.ClassifiedContext m) (E : Finset (Fin m))
    (hE : sourcePlan ξ Λ r U zs c μseed α X = some E)
    (i : Fin m) (hi : (sourceWeights ξ Λ r U X.1).1 i = 0) : i ∉ E := by
  dsimp only [sourcePlan] at hE
  split_ifs at hE with hg
  · cases hs : sourceSeed μseed zs X with
    | none => simp [hs,sampleSeedOption] at hE
    | some s =>
        have he : planSampler
            (max (budget c 0 X) (budget c 1 X)-commonBudget c X)
            (α X,sourceWeights ξ Λ r U X.1) s = some E := by
          simpa only [hs,sampleSeedOption] using hE
        exact planSampler_omits_zero_weight _ _ hg.2 s E he i hi

theorem sourcePlan_omits_seed (ξ Λ r U zs : ℝ) (hr : 0 < r) (hseed : zs ≤ Λ)
    (c : ℕ) (μseed : Measure ℝ) (α : StrictNative.ClassifiedContext m → unitInterval)
    (X : StrictNative.ClassifiedContext m) (E : Finset (Fin m))
    (hE : sourcePlan ξ Λ r U zs c μseed α X = some E)
    (i : Fin m) (b : ℝ) (hi : X.1 i = some b) (hb : b ≤ zs) : i ∉ E :=
  sourcePlan_omits_zero_weight ξ Λ r U zs c μseed α X E hE i
    (sourceWeights_seed ξ Λ r U zs b hr hseed X.1 i hi hb)

lemma measurable_sourcePlanFromSeed (ξ Λ r U : ℝ) (hξ : 0 < ξ) (hΛ : 0 < Λ)
    (c : ℕ) (α : StrictNative.ClassifiedContext m → unitInterval) (hα : Measurable α) :
    Measurable (fun x : StrictNative.ClassifiedContext m × Option unitInterval =>
      sourcePlanFromSeed ξ Λ r U c α x.1 x.2) := by
  have hΔ : Measurable (fun X : StrictNative.ClassifiedContext m =>
      max (budget c 0 X) (budget c 1 X)-commonBudget c X) :=
    ((measurable_budget c 0).max (measurable_budget c 1)).sub
      ((measurable_budget c 0).min (measurable_budget c 1))
  have hw : Measurable (fun X : StrictNative.ClassifiedContext m => sourceWeights ξ Λ r U X.1) :=
    (measurable_sourceWeights ξ Λ r U hξ hΛ).comp measurable_fst
  have hc : Measurable (fun X : StrictNative.ClassifiedContext m =>
      (exceptionalSet U X.1).card) :=
    (measurable_of_countable Finset.card).comp
      ((measurable_exceptionalSet U).comp measurable_fst)
  have hW := FCAppendix.Affine.WeightedSampling.continuous_totalWeight.measurable.comp hw
  have hΔR : Measurable (fun X : StrictNative.ClassifiedContext m =>
      ((max (budget c 0 X) (budget c 1 X)-commonBudget c X : ℕ) : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hΔ
  have hs : Measurable (fun q : ℕ ×
      ((unitInterval × FCAppendix.Affine.WeightedSampling.Weights (Fin m)) × Option unitInterval) =>
      sampleSeedOption q.1 q.2.1 q.2.2) :=
    measurable_from_prod_countable_right (fun Δ => measurable_sampleSeedOption Δ)
  exact Measurable.ite
    (((measurableSet_le hc measurable_const).inter (measurableSet_lt hΔR hW)).preimage measurable_fst)
    (hs.comp ((hΔ.comp measurable_fst).prodMk
      (((hα.comp measurable_fst).prodMk (hw.comp measurable_fst)).prodMk measurable_snd)))
    measurable_const

theorem sourcePlanFromSeed_target_integral_le
    {ξ Λ a r U d₀ z t width ε : ℝ} (c : ℕ)
    (hm : 0 < m) (hε : 0 < ε) (X : StrictNative.ClassifiedContext m) (i : Fin m) :
    (∫ s : unitInterval, planTargetIndicator i
      (sourcePlanFromSeed ξ Λ r U c
        (sourceGuardAlpha ξ Λ a r U d₀ z t width ε c) X (some s))) ≤
      ((max (budget c 0 X) (budget c 1 X)-commonBudget c X : ℕ) : ℝ)/(ε*m) := by
  let Δ := max (budget c 0 X) (budget c 1 X)-commonBudget c X
  let w := sourceWeights ξ Λ r U X.1
  let α := sourceGuardAlpha ξ Λ a r U d₀ z t width ε c X
  have hden : 0 < ε*m := mul_pos hε (by exact_mod_cast hm)
  have hnon : 0 ≤ (Δ : ℝ)/(ε*m) := div_nonneg (Nat.cast_nonneg Δ) hden.le
  by_cases hg : (exceptionalSet U X.1).card ≤ 1 ∧
      (Δ : ℝ) < FCAppendix.Affine.WeightedSampling.totalWeight w
  · by_cases hp : 0 < (α : ℝ)
    · have hs := sourceGuardAlpha_outer c hm hε X hp 2
      have hslack : ε*m < FCAppendix.Affine.WeightedSampling.totalWeight w-Δ := by
        change ε*m < FCAppendix.Affine.WeightedSampling.totalWeight
          (sourceWeights ξ Λ r U X.1)-(max (budget c 0 X) (budget c 1 X)-commonBudget c X : ℕ) at hs
        exact hs
      have hh := planSampler_target_integral_le Δ α w hg.2 i
      have hb := hh.trans (div_le_div_of_nonneg_left (Nat.cast_nonneg Δ) hden hslack.le)
      simpa only [sourcePlanFromSeed,if_pos hg,sampleSeedOption,Δ,w,α] using hb
    · have hz : (α : ℝ) = 0 := le_antisymm (le_of_not_gt hp) α.2.1
      have hall (s : unitInterval) : planTargetIndicator i (planSampler Δ (α,w) s) = 0 := by
        cases he : planSampler Δ (α,w) s with
        | none => rfl
        | some E =>
            have hx := planSampler_some_alpha_pos Δ (α,w) s E he
            rw [hz] at hx
            exact (lt_irrefl 0 hx).elim
      simpa only [sourcePlanFromSeed,if_pos hg,sampleSeedOption,hall,integral_zero,Δ,w,α]
        using hnon
  · simpa only [sourcePlanFromSeed,if_neg hg,planTargetIndicator,integral_zero,Δ,w]
      using hnon

end Weighted
end FCAppendix.Affine.Uniform07Finishing
