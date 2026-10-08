import FCAppendix.Probability.RecenteringCDF
import FCAppendix.PayOnce.ClippedPriceCLT
import FCAppendix.PayOnce.InactiveValuePrice

namespace FCAppendix.Probability
open MeasureTheory Filter Topology Real

theorem tendsto_div_sqrtScale_of_isLittleO (M : ℕ → ℕ)
    (hM : Tendsto M atTop atTop) {s : ℝ} (hs : 0 < s) {e : ℕ → ℝ}
    (he : e =o[atTop] (fun t => (M t:ℝ)^(-(1:ℝ)/2))) :
    Tendsto (fun t => e t/(s/sqrt (M t:ℝ))) atTop (𝓝 0) := by
  have ht := he.tendsto_div_nhds_zero.div_const s
  simp only [zero_div] at ht
  apply ht.congr'
  filter_upwards [hM.eventually_gt_atTop 0] with t hmt
  have hm : (0:ℝ) < M t := Nat.cast_pos.mpr hmt
  have hroot : sqrt (M t:ℝ) ≠ 0 := (sqrt_pos.mpr hm).ne'
  rw [neg_div,rpow_neg hm.le,← sqrt_eq_rpow]
  field_simp

end FCAppendix.Probability

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList Real
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel Probability
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_gaussian_recenter_shift_of_isLittleO
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (center : ℕ → ℝ)
    (hsmall : (fun t => KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal)
      ((C t:ℝ)/(M t))-center t) =o[atTop] (fun t => (M t:ℝ)^(-(1:ℝ)/2))) :
    Tendsto (fun t => (KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal)
      ((C t:ℝ)/(M t))-center t)/inactiveGaussianScale M F (k+1) g ρ t) atTop (𝓝 0) := by
  let μW := F.map (fun v => max (v-g) 0)
  have hnet : Measurable (fun v : ℝ => max (v-g) 0) :=
    (measurable_id.sub_const g).max measurable_const
  letI : IsProbabilityMeasure μW := Measure.isProbabilityMeasure_map hnet.aemeasurable
  have hs := GaussianParameters.sigma_pos μW (n := k+1) (by have := h.proposers_two; omega)
    (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1 hlocal
  exact tendsto_div_sqrtScale_of_isLittleO M h.population_grows hs hsmall

theorem payOnce_inactive_focal_price_gaussian_uniform_population
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) (x : ℝ) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t in atTop, ∀ b : ℝ, 0 < b →
      |cdf ((Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))).map
        (fun r => (focalPrice (k+1) (C t) hn b r -
          KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t)))/
          inactiveGaussianScale M F (k+1) g ρ t)) x-cdf (gaussianReal 0 1) x| < ε := by
  dsimp only
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
  have hinside := (payOnce_inactive_gaussian_price_tendsto Γ B F g ρ h x).eventually
    (Ioo_mem_nhds (show L-1 < L by linarith) (show L < L+1 by linarith))
  intro ε hε
  filter_upwards [payOnce_inactive_clipped_focal_price_gaussian_uniform_population Γ B F g ρ h hlocal
    (L-1) (L+1) (by linarith) (by linarith) x ε hε,hinside,
    h.population_grows.eventually_gt_atTop 0] with t ht hit hmt b hb
  have he := cdf_standardized_clipToInterval_eq
    (Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)))
    (measurable_focalPrice (c := C t) hn b)
    (payOnce_inactive_gaussian_scale_pos Γ B F g ρ h hlocal hmt) hit
  have hh := ht b hb
  change |cdf ((_ : Measure (Fin (M t-1) → ℝ)).map (fun r =>
    (clipToInterval (L-1) (L+1) (focalPrice (k+1) (C t) hn b r)-_)/_)) x-_| < ε at hh
  rw [he] at hh
  exact hh

theorem payOnce_inactive_focal_price_gaussian_uniform_of_shift
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) (center : ℕ → ℝ)
    (hshift : Tendsto (fun t => (KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal)
      ((C t:ℝ)/(M t))-center t)/inactiveGaussianScale M F (k+1) g ρ t) atTop (𝓝 0)) (x : ℝ) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t in atTop, ∀ b : ℝ, 0 < b →
      |cdf ((Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))).map
        (fun r => (focalPrice (k+1) (C t) hn b r-center t)/
          inactiveGaussianScale M F (k+1) g ρ t)) x-cdf (gaussianReal 0 1) x| < ε := by
  dsimp only
  exact cdf_recenter_uniform
    (fun t => Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)))
    (fun t b => focalPrice (k+1) (C t) (by have := h.proposers_two; omega) b) (fun b => 0 < b)
    (fun _ b _ => measurable_focalPrice _ b) _ center _ (fun x => cdf (gaussianReal 0 1) x)
    continuous_Φ hshift (fun x => payOnce_inactive_focal_price_gaussian_uniform_population
      Γ B F g ρ h hlocal x) x

theorem payOnce_inactive_profile_price_gaussian_cdf_of_shift
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) (center : ℕ → ℝ)
    (hshift : Tendsto (fun t => (KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal)
      ((C t:ℝ)/(M t))-center t)/inactiveGaussianScale M F (k+1) g ρ t) atTop (𝓝 0)) (x : ℝ) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    Tendsto (fun t => cdf ((Measure.pi (fun _ : Fin (M t) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))).map
      (fun r => (sampleProfilePrice (k+1) (C t) hn r-center t)/
        inactiveGaussianScale M F (k+1) g ρ t)) x) atTop (𝓝 (cdf (gaussianReal 0 1) x)) := by
  dsimp only
  exact cdf_recenter_tendsto
    (fun t => Measure.pi (fun _ : Fin (M t) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)))
    (fun t => sampleProfilePrice (k+1) (C t) (by have := h.proposers_two; omega))
    (fun _ => measurable_sampleProfilePrice _) _ center _ (fun x => cdf (gaussianReal 0 1) x)
    continuous_Φ hshift (payOnce_inactive_profile_price_gaussian_cdf Γ B F g ρ h hlocal) x

end FCAppendix.Bayes
