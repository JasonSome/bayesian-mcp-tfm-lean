import FCAppendix.PayOnce.ClippedPriceCLT
import FCAppendix.PayOnce.InactiveClippedPriceMoments
import FCAppendix.Probability.GaussianMeanConvergence
import FCAppendix.Probability.ClippedSubGaussianMoments

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel Probability

theorem inactiveGaussianScale_sq (M : ℕ → ℕ) (F : Measure ℝ) (n : ℕ) (g ρ : ℝ) (t : ℕ) :
    inactiveGaussianScale M F n g ρ t ^ 2 =
      GaussianParameters.sigma (F.map (fun v => max (v-g) 0)) n
        (Limit.capRoot (F.map (fun v => max (v-g) 0)) n ρ)^2/(M t:ℝ) := by
  unfold inactiveGaussianScale
  rw [div_pow,Real.sq_sqrt (Nat.cast_nonneg _)]

private theorem integral_normalized_sq_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : Ω → ℝ) {m : ℕ} {s δ K : ℝ}
    (hm : 0 < m) (hs : 0 < s) (hscale : δ^2 = s^2/(m:ℝ))
    (hbound : (∫ ω, (Y ω)^2 ∂μ) ≤ K/(m:ℝ)) :
    (∫ ω, (Y ω/δ)^2 ∂μ) ≤ K/s^2 := by
  have hmR : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hh := div_le_div_of_nonneg_right hbound (sq_nonneg δ)
  have he : (K/(m:ℝ))/δ^2 = K/s^2 := by
    rw [hscale]
    field_simp
  rw [he] at hh
  simpa only [div_pow,integral_div] using hh

private theorem normalized_clipped_secondMoment_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {Y : Ω → ℝ} (hY : Measurable Y)
    {ell u a s δ K : ℝ} {m : ℕ} (ha : a ∈ Icc ell u) (hm : 0 < m) (hs : 0 < s)
    (hscale : δ^2 = s^2/(m:ℝ))
    (hbound : (∫ ω, |clipToInterval ell u (Y ω)-a|^(2:ℝ) ∂μ) ≤ K*(m:ℝ)^(-(2:ℝ)/2)) :
    Measurable (fun ω => (clipToInterval ell u (Y ω)-a)/δ) ∧
      MemLp (fun ω => (clipToInterval ell u (Y ω)-a)/δ) 2 μ ∧
      (∫ ω, ((clipToInterval ell u (Y ω)-a)/δ)^2 ∂μ) ≤ K/s^2 := by
  refine ⟨(((measurable_clipToInterval ell u).comp hY).sub_const a).div_const δ,?_,?_⟩
  · have hh := (memLp_clipToInterval_sub μ hY ha 2).const_mul δ⁻¹
    simpa only [div_eq_mul_inv,mul_comm] using hh
  · apply integral_normalized_sq_le μ _ hm hs hscale
    norm_num only [Real.rpow_two,sq_abs,neg_div,neg_neg,div_self,OfNat.ofNat_ne_zero,
      Real.rpow_neg_one] at hbound
    simpa only [div_eq_mul_inv] using hbound

variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_clipped_focal_price_mean_uniform
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (ell u : ℝ) (hell : ell < Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)
    (hu : Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ < u) :
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    let P := fun t => Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    TendstoUniformlyOn (fun t b => (∫ z,
      clippedFocalPrice (k+1) (C t) hn ell u b z-bar t ∂P t)/
        inactiveGaussianScale M F (k+1) g ρ t) (fun _ => 0) atTop (Ioi (0:ℝ)) := by
  dsimp only
  have hk := h.proposers_two
  let μW := F.map (fun v => max (v-g) 0)
  let s := GaussianParameters.sigma μW (k+1) (Limit.capRoot μW (k+1) ρ)
  have hnet : Measurable (fun v : ℝ => max (v-g) 0) :=
    (measurable_id.sub_const g).max measurable_const
  letI : IsProbabilityMeasure μW := Measure.isProbabilityMeasure_map hnet.aemeasurable
  have hs : 0 < s := GaussianParameters.sigma_pos μW (by omega)
    (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1 hlocal
  obtain ⟨K,_,hK⟩ := payOnce_inactive_clipped_focal_price_moments Γ B F g ρ h
    ell u hell hu (r := 2) (by norm_num)
  have hi := (payOnce_inactive_population_price Γ B F g ρ h).2.eventually
    (Ioo_mem_nhds hell hu)
  have ht := gaussian_mean_tendstoUniformlyOn_of_secondMoment_bound
    (fun t => Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)))
    (Ioi (0:ℝ))
    (fun t b z => (clippedFocalPrice (k+1) (C t) (by omega) ell u b z-
      KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t)))/
        inactiveGaussianScale M F (k+1) g ρ t) (K/s^2) ?_
    (fun x => payOnce_inactive_clipped_focal_price_gaussian_uniform_population
      Γ B F g ρ h hlocal ell u hell hu x)
  · simpa only [integral_div] using ht
  · filter_upwards [hK,hi,h.population_grows.eventually_gt_atTop 0] with t hKt hit hmt
    intro b hb
    exact normalized_clipped_secondMoment_bound _ (measurable_focalPrice (by omega) b)
      ⟨hit.1.le,hit.2.le⟩ hmt hs (inactiveGaussianScale_sq M F (k+1) g ρ t) (hKt b hb).2

theorem payOnce_inactive_clipped_profile_price_mean_tendsto
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (ell u : ℝ) (hell : ell < Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)
    (hu : Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ < u) :
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    let P := fun t => Measure.pi (fun _ : Fin (M t) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    Tendsto (fun t => (∫ z,
      clippedProfilePrice (k+1) (C t) hn ell u z-bar t ∂P t)/
        inactiveGaussianScale M F (k+1) g ρ t) atTop (𝓝 0) := by
  dsimp only
  have hk := h.proposers_two
  let μW := F.map (fun v => max (v-g) 0)
  let s := GaussianParameters.sigma μW (k+1) (Limit.capRoot μW (k+1) ρ)
  have hnet : Measurable (fun v : ℝ => max (v-g) 0) :=
    (measurable_id.sub_const g).max measurable_const
  letI : IsProbabilityMeasure μW := Measure.isProbabilityMeasure_map hnet.aemeasurable
  have hs : 0 < s := GaussianParameters.sigma_pos μW (by omega)
    (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1 hlocal
  obtain ⟨K,_,hK⟩ := payOnce_inactive_clipped_profile_price_moments Γ B F g ρ h
    ell u hell hu (r := 2) (by norm_num)
  have hi := (payOnce_inactive_population_price Γ B F g ρ h).2.eventually
    (Ioo_mem_nhds hell hu)
  have ht := gaussian_mean_tendsto_of_eventually_secondMoment_bound
    (fun t => Measure.pi (fun _ : Fin (M t) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)))
    (fun t z => (clippedProfilePrice (k+1) (C t) (by omega) ell u z-
      KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t)))/
        inactiveGaussianScale M F (k+1) g ρ t) (K/s^2) ?_
    (fun x => payOnce_inactive_clipped_profile_price_gaussian_cdf
      Γ B F g ρ h hlocal ell u hell hu x)
  · simpa only [integral_div] using ht
  · filter_upwards [hK,hi,h.population_grows.eventually_gt_atTop 0] with t hKt hit hmt
    exact normalized_clipped_secondMoment_bound _ (measurable_sampleProfilePrice (by omega))
      ⟨hit.1.le,hit.2.le⟩ hmt hs (inactiveGaussianScale_sq M F (k+1) g ρ t) hKt.2

theorem payOnce_inactive_clipped_focal_price_mean_small
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (ell u : ℝ) (hell : ell < Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)
    (hu : Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ < u) :
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    let P := fun t => Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t in atTop, ∀ b : ℝ, 0 < b →
      |∫ z, clippedFocalPrice (k+1) (C t) hn ell u b z-bar t ∂P t| ≤
        ε*inactiveGaussianScale M F (k+1) g ρ t := by
  dsimp only
  intro ε hε
  have ht := (Metric.tendstoUniformlyOn_iff.mp
    (payOnce_inactive_clipped_focal_price_mean_uniform Γ B F g ρ h hlocal ell u hell hu)) ε hε
  filter_upwards [ht,h.population_grows.eventually_gt_atTop 0] with t hmt hpos
  intro b hb
  have hs := payOnce_inactive_gaussian_scale_pos Γ B F g ρ h hlocal hpos
  have hh := hmt b hb
  simp only [Real.dist_eq,zero_sub,abs_neg,abs_div,abs_of_pos hs] at hh
  exact ((div_lt_iff₀ hs).mp hh).le

theorem payOnce_inactive_clipped_profile_price_mean_small
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (ell u : ℝ) (hell : ell < Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)
    (hu : Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ < u) :
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    let P := fun t => Measure.pi (fun _ : Fin (M t) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t in atTop,
      |∫ z, clippedProfilePrice (k+1) (C t) hn ell u z-bar t ∂P t| ≤
        ε*inactiveGaussianScale M F (k+1) g ρ t := by
  dsimp only
  intro ε hε
  have ht := (Metric.tendsto_nhds.mp
    (payOnce_inactive_clipped_profile_price_mean_tendsto Γ B F g ρ h hlocal ell u hell hu)) ε hε
  filter_upwards [ht,h.population_grows.eventually_gt_atTop 0] with t hmt hpos
  have hs := payOnce_inactive_gaussian_scale_pos Γ B F g ρ h hlocal hpos
  have hh := hmt
  simp only [Real.dist_eq,sub_zero,abs_div,abs_of_pos hs] at hh
  exact ((div_lt_iff₀ hs).mp hh).le

end FCAppendix.Bayes
