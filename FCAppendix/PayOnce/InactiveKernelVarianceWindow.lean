import FCAppendix.PayOnce.InactiveKernelCLT

namespace FCAppendix.Probability
open MeasureTheory ProbabilityTheory Set Filter

theorem variance_difference_le_of_unitInterval {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X Y : Ω → ℝ} {D : ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (hbX : ∀ᵐ ω ∂μ, X ω ∈ Icc 0 1) (hbY : ∀ᵐ ω ∂μ, Y ω ∈ Icc 0 1)
    (hXY : ∀ᵐ ω ∂μ, |X ω - Y ω| ≤ D) :
    |variance X μ - variance Y μ| ≤ 4 * D := by
  have hLpX : MemLp X 2 μ := MemLp.of_bound hX.aestronglyMeasurable 1
    (hbX.mono fun ω h => by simpa [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2)
  have hLpY : MemLp Y 2 μ := MemLp.of_bound hY.aestronglyMeasurable 1
    (hbY.mono fun ω h => by simpa [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2)
  have hiX := hLpX.integrable (by norm_num)
  have hiY := hLpY.integrable (by norm_num)
  have hmX := unitInterval_mean_mem_Icc μ hX hbX
  have hmY := unitInterval_mean_mem_Icc μ hY hbY
  have hmean : |(∫ ω, X ω ∂μ) - ∫ ω, Y ω ∂μ| ≤ D := by
    have hh := norm_integral_le_of_norm_le_const (μ := μ) (f := fun ω => X ω - Y ω)
      (C := D) (hXY.mono fun ω h => by simpa [Real.norm_eq_abs] using h)
    simpa [integral_sub hiX hiY] using hh
  have hsq (x y : ℝ) (hx : x ∈ Icc 0 1) (hy : y ∈ Icc 0 1) :
      |x ^ 2 - y ^ 2| ≤ 2 * |x - y| := by
    calc
      |x ^ 2 - y ^ 2| = |x - y| * |x + y| := by rw [← abs_mul]; congr 1; ring
      _ ≤ |x - y| * 2 := mul_le_mul_of_nonneg_left
        (by rw [abs_of_nonneg (add_nonneg hx.1 hy.1)]; linarith [hx.2, hy.2]) (abs_nonneg _)
      _ = 2 * |x - y| := by ring
  have hsecond : |(∫ ω, X ω ^ 2 ∂μ) - ∫ ω, Y ω ^ 2 ∂μ| ≤ 2 * D := by
    have hh := norm_integral_le_of_norm_le_const (μ := μ)
      (f := fun ω => X ω ^ 2 - Y ω ^ 2) (C := 2 * D) (by
        filter_upwards [hbX, hbY, hXY] with ω hx hy hxy
        rw [Real.norm_eq_abs]
        exact (hsq _ _ hx hy).trans (by linarith))
    simpa [integral_sub hLpX.integrable_sq hLpY.integrable_sq] using hh
  rw [variance_eq_sub hLpX, variance_eq_sub hLpY]
  simp only [Pi.pow_apply]
  have hsqmean := (hsq _ _ hmX hmY).trans (mul_le_mul_of_nonneg_left hmean (by norm_num))
  calc
    _ = |((∫ ω, X ω ^ 2 ∂μ) - ∫ ω, Y ω ^ 2 ∂μ) -
        ((∫ ω, X ω ∂μ) ^ 2 - (∫ ω, Y ω ∂μ) ^ 2)| := by congr 1; ring
    _ ≤ |(∫ ω, X ω ^ 2 ∂μ) - ∫ ω, Y ω ^ 2 ∂μ| +
        |(∫ ω, X ω ∂μ) ^ 2 - (∫ ω, Y ω ∂μ) ^ 2| := abs_sub _ _
    _ ≤ 4 * D := by linarith

end FCAppendix.Probability

namespace FCAppendix.PayOnce.KernelLawConvergence
open MeasureTheory ProbabilityTheory Set KernelTailEvent FCAppendix.CommonList

theorem kernel_variance_price_difference (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) {L T ℓ : ℝ}
    (hℓ : 0 < ℓ) (hL : ℓ ≤ L) (hT : ℓ ≤ T) :
    |variance (fun b => kernel n b L) μ - variance (fun b => kernel n b T) μ| ≤
      (4 * ((n : ℝ) / ℓ)) * |L - T| := by
  simpa [mul_assoc] using Probability.variance_difference_le_of_unitInterval μ
    (continuous_kernel_bid hn (hℓ.trans_le hL)).measurable
    (continuous_kernel_bid hn (hℓ.trans_le hT)).measurable
    (.of_forall fun b => kernel_bounds hn (hℓ.trans_le hL) b)
    (.of_forall fun b => kernel_bounds hn (hℓ.trans_le hT) b)
    (.of_forall fun b => kernel_price_difference hn hℓ hL hT b)

end FCAppendix.PayOnce.KernelLawConvergence

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.KernelLawConvergence PayOnce.KernelTailEvent
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_kernel_variance_window
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) :
    let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
    ∃ ℓ u V : ℝ, 0 < ℓ ∧ ℓ < u ∧ 0 < V ∧ L ∈ Ioo ℓ u ∧
      ∀ᶠ t in atTop, ∀ T ∈ Icc ℓ u,
        V ≤ variance (fun b => kernel (k+1) b T)
          (BidScaling.realBidLaw (Γ t) : Measure ℝ) := by
  dsimp only
  let μW := F.map (fun v => max (v-g) 0)
  let L := Limit.capRoot μW (k+1) ρ
  let v := variance (Limit.pStar (k+1) L) μW
  have hn : 2 ≤ k+1 := by have hk := h.proposers_two; omega
  have hnet : Measurable (fun v : ℝ => max (v-g) 0) :=
    (measurable_id.sub_const g).max measurable_const
  letI : IsProbabilityMeasure μW := Measure.isProbabilityMeasure_map hnet.aemeasurable
  have hL : 0 < L := (payOnce_inactive_limit_root_window Γ B F g ρ h
    (payOnce_inactive_bidLaw_tendsto Γ B F g ρ h)).1
  have hv : 0 < v := GaussianParameters.variance_pos μW hn hL hlocal
  have hvar := payOnce_inactive_real_kernel_variance_tendsto Γ B F g ρ h
    (T := fun _ => L) tendsto_const_nhds
  let A : ℝ := 4 * ((k+1 : ℕ) : ℝ) / (L/2)
  have hA : 0 < A := by dsimp [A]; positivity
  let r := min (L/4) (v/(4*A))
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrL : r ≤ L/4 := min_le_left _ _
  have hrv : r ≤ v/(4*A) := min_le_right _ _
  have hAr : A*r ≤ v/4 := by
    have hh := (le_div_iff₀ (show 0 < 4*A by positivity)).mp hrv
    nlinarith
  refine ⟨L-r,L+r,v/4,by linarith,by linarith,by positivity,⟨by linarith,by linarith⟩,?_⟩
  filter_upwards [hvar.eventually_const_le (show v/2 < v by linarith)] with t ht T hT
  have hTL : L/2 ≤ T := by rcases hT with ⟨hleft,hright⟩; linarith
  have hdist : |L-T| ≤ r := abs_le.mpr ⟨by linarith [hT.2],by linarith [hT.1]⟩
  have hd := kernel_variance_price_difference (BidScaling.realBidLaw (Γ t) : Measure ℝ)
    hn (show 0 < L/2 by linarith) (show L/2 ≤ L by linarith) hTL
  have hd' : |variance (fun b => kernel (k+1) b L) (BidScaling.realBidLaw (Γ t) : Measure ℝ) -
      variance (fun b => kernel (k+1) b T) (BidScaling.realBidLaw (Γ t) : Measure ℝ)| ≤ v/4 := by
    calc
      _ ≤ A * |L-T| := by convert hd using 1; dsimp [A]; ring
      _ ≤ A*r := mul_le_mul_of_nonneg_left hdist hA.le
      _ ≤ v/4 := hAr
  have hh := (abs_le.mp hd').2
  linarith

end FCAppendix.Bayes
