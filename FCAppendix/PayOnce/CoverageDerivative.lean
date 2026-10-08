import FCAppendix.PayOnce.AnalyticalKernel
import FCAppendix.Probability.UnitInterval
import Mathlib.Analysis.Calculus.ParametricIntegral

namespace FCAppendix.PayOnce.AnalyticalKernel

open MeasureTheory Filter Topology Set CommonList OwnImpact
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

def RegularClearing (n c : ℕ) (rivals : ι → ℝ) (b : ℝ) : Prop :=
  (∀ j, 0 < rivals j) ∧ ∃ L, 0 < L ∧
    kernel n b L + ∑ j, kernel n (rivals j) L = c ∧
    b ≠ L ∧ b ≠ (n : ℝ) * L ∧
    (∀ j, rivals j ≠ L) ∧ (∀ j, rivals j ≠ (n : ℝ) * L)

theorem differentiableAt_allocation_of_regular {n c : ℕ} (hn : 2 ≤ n)
    (hc : c ≤ Fintype.card ι + 1) (rivals : ι → ℝ) {b : ℝ} (hb : 0 < b)
    (hreg : RegularClearing n c rivals b) :
    DifferentiableAt ℝ (allocation n c hn hc rivals) b := by
  obtain ⟨hr, L, hL, hcap, hzero, hone, hclip0, hclip1⟩ := hreg
  have hroot := fun (x : ℝ) (hx : 0 < x) => allocation_root hn hc rivals hr hx
  by_cases hbl : b < L
  · exact (hasStrictDerivAt_focal_kernel_zero hn rivals _ hb hL hbl hcap hroot).hasDerivAt.differentiableAt
  by_cases hnb : (n : ℝ) * L < b
  · exact (hasStrictDerivAt_focal_kernel_one hn rivals _ hb hL hnb hcap hroot).hasDerivAt.differentiableAt
  have hp := scalarThreshold_kernel n hn hb hL
  have hlb : L < b := lt_of_le_of_ne (le_of_not_gt hbl) hzero.symm
  have hbn : b < (n : ℝ) * L := lt_of_le_of_ne (le_of_not_gt hnb) hone
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hi : kernel n b L ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · apply lt_of_le_of_ne hp.1
      intro he
      exact hlb.not_ge ((kernel_eq_zero_iff n hn hb hL).mp he.symm)
    · apply lt_of_le_of_ne hp.2.1
      intro he
      have hh := (le_div_iff₀ hnR).mp ((kernel_eq_one_iff n hn hb hL).mp he)
      nlinarith
  exact (hasStrictDerivAt_focal_kernel hn rivals hr _ hb hL hcap hi hclip0 hclip1 hroot).hasDerivAt.differentiableAt

noncomputable def coverage (n c : ℕ) (hn : 2 ≤ n) (hc : c ≤ Fintype.card ι + 1)
    (μ : Measure (ι → ℝ)) (b : ℝ) : ℝ :=
  ∫ rivals, success n (allocation n c hn hc rivals b) ∂μ

theorem measurable_success_allocation {n c : ℕ} (hn : 2 ≤ n) (hc : c ≤ Fintype.card ι + 1)
    {b : ℝ} (hb : 0 < b) :
    Measurable (fun rivals : ι → ℝ => success n (allocation n c hn hc rivals b)) :=
  (continuous_success n).measurable.comp (measurable_allocation_rivals hn hc hb)

theorem success_allocation_bounds {n c : ℕ} (hn : 2 ≤ n) (hc : c ≤ Fintype.card ι + 1)
    (rivals : ι → ℝ) (b : ℝ) :
    success n (allocation n c hn hc rivals b) ∈ Icc (0 : ℝ) 1 := by
  have hp := allocation_bounds hn hc rivals b
  refine ⟨?_, success_le_one n _ hp.2⟩
  unfold success
  exact sub_nonneg.mpr (pow_le_one₀ (sub_nonneg.mpr hp.2) (by linarith [hp.1]))

theorem aestronglyMeasurable_success_deriv {n c : ℕ} (hn : 2 ≤ n)
    (hc : c ≤ Fintype.card ι + 1) (μ : Measure (ι → ℝ)) {b : ℝ} (hb : 0 < b)
    (hreg : ∀ᵐ rivals ∂μ, RegularClearing n c rivals b) :
    AEStronglyMeasurable (fun rivals => deriv (fun x => success n (allocation n c hn hc rivals x)) b) μ := by
  let F : ℝ → (ι → ℝ) → ℝ := fun x rivals => success n (allocation n c hn hc rivals x)
  let δ : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hδ (j : ℕ) : 0 < δ j := by dsimp only [δ]; positivity
  have hδlim : Tendsto δ atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Filter.Eventually.of_forall fun j => (hδ j).ne'⟩
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun j rivals => (F (b + δ j) rivals - F b rivals) / δ j)
  · intro j
    exact (((measurable_success_allocation hn hc (by linarith [hδ j])).sub
      (measurable_success_allocation hn hc hb)).div_const (δ j)).aestronglyMeasurable
  · filter_upwards [hreg] with rivals hr
    have hp := differentiableAt_allocation_of_regular hn hc rivals hb hr
    have hs : DifferentiableAt ℝ (fun x => F x rivals) b :=
      (differentiableAt_const (1 : ℝ)).sub (((differentiableAt_const (1 : ℝ)).sub hp).pow n)
    have hh := hs.hasDerivAt.tendsto_slope_zero.comp hδlim
    simpa only [Function.comp_def, F, smul_eq_mul, div_eq_mul_inv, mul_comm] using hh

theorem hasDerivAt_coverage_of_regular {n c : ℕ} (hn : 2 ≤ n)
    (hc : c ≤ Fintype.card ι + 1) (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    {b : ℝ} (hb : 0 < b) (hreg : ∀ᵐ rivals ∂μ, RegularClearing n c rivals b) :
    Integrable (fun rivals => deriv (fun x => success n (allocation n c hn hc rivals x)) b) μ ∧
      HasDerivAt (coverage n c hn hc μ)
        (∫ rivals, deriv (fun x => success n (allocation n c hn hc rivals x)) b ∂μ) b := by
  let F : ℝ → (ι → ℝ) → ℝ := fun x rivals => success n (allocation n c hn hc rivals x)
  have hhalf : 0 < b / 2 := by linarith
  apply hasDerivAt_integral_of_dominated_loc_of_lip
    (F := F) (s := Ioi (b / 2)) (bound := fun _ : ι → ℝ => (n : ℝ) ^ 2 / (b / 2))
    (Ioi_mem_nhds (by linarith : b / 2 < b))
  · filter_upwards [eventually_gt_nhds hb] with x hx
    exact (measurable_success_allocation hn hc hx).aestronglyMeasurable
  · exact UnitInterval.integrable μ _ (measurable_success_allocation hn hc hb)
      (fun rivals => (success_allocation_bounds hn hc rivals b).1)
      (fun rivals => (success_allocation_bounds hn hc rivals b).2)
  · exact aestronglyMeasurable_success_deriv hn hc μ hb hreg
  · filter_upwards [hreg] with rivals hr
    exact (focal_success_lipschitzOn hn rivals _ hhalf
      (fun x hx => allocation_root hn hc rivals hr.1 hx)).mono Ioi_subset_Ici_self
  · exact integrable_const _
  · filter_upwards [hreg] with rivals hr
    have hp := differentiableAt_allocation_of_regular hn hc rivals hb hr
    have hs : DifferentiableAt ℝ (fun x => F x rivals) b :=
      (differentiableAt_const (1 : ℝ)).sub (((differentiableAt_const (1 : ℝ)).sub hp).pow n)
    exact hs.hasDerivAt

end FCAppendix.PayOnce.AnalyticalKernel
