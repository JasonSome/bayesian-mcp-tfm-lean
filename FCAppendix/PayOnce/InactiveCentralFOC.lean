import FCAppendix.PayOnce.InactiveCentralLimits
import FCAppendix.PayOnce.InactiveEntryHazard
import FCAppendix.PayOnce.GaussianResponseProfile

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList Real
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_central_foc_bid_bounded
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (x b : ℕ → ℝ) {x₀ : ℝ} (hx : Tendsto x atTop (𝓝 x₀))
    (hb : Tendsto b atTop (𝓝 (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)))
    (hupper : ∀ᶠ t in atTop, b t ≤ inactiveGaussianPrice Γ F g ρ (x t) t)
    (hfoc : ∀ᶠ t in atTop,
      let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
      let Q := coverage (k+1) (C t) hn
        (Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)))
      Q (b t)=(inactiveGaussianPrice Γ F g ρ (x t) t-b t)*deriv Q (b t)) :
    ∃ R : ℝ, 0 < R ∧ ∀ᶠ t in atTop,
      (b t-KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t)))/
        inactiveGaussianScale M F (k+1) g ρ t ∈ Icc (-R) R := by
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  let μW := F.map (fun v => max (v-g) 0)
  let L := Limit.capRoot μW (k+1) ρ
  let σ := GaussianParameters.sigma μW (k+1) L
  let bar := fun t => KernelDemand.populationPrice (k+1)
    (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
  let s := inactiveGaussianScale M F (k+1) g ρ
  let Q := fun t => coverage (k+1) (C t) hn
    (Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)))
  have hnet : Measurable (fun v : ℝ => max (v-g) 0) :=
    (measurable_id.sub_const g).max measurable_const
  letI : IsProbabilityMeasure μW := Measure.isProbabilityMeasure_map hnet.aemeasurable
  have hL : 0<L := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  have hσ : 0<σ := GaussianParameters.sigma_pos μW hn hL hlocal
  have hbar : Tendsto bar atTop (𝓝 L) := (payOnce_inactive_population_price Γ B F g ρ h).2
  change Tendsto b atTop (𝓝 L) at hb
  obtain ⟨η,A,hη,hA,hhazard⟩ := payOnce_inactive_entry_hazard Γ B F g ρ h hlocal
  have hgap : ∀ᶠ t in atTop, bar t-b t<η := by
    have hh := (hbar.sub hb).eventually_lt_const (by simpa only [sub_self] using hη)
    exact hh
  let R := |x₀|+1+A/σ
  have hR : 0<R := by dsimp only [R]; positivity
  refine ⟨R,hR,?_⟩
  filter_upwards [hhazard,hgap,hupper,hfoc,h.population_grows.eventually_gt_atTop 0,
    hx.abs.eventually_lt_const (by linarith : |x₀| < |x₀|+1)] with t hh hnear hu hf hmt hxt
  change Q t (b t)=(bar t+s t*x t-b t)*deriv (Q t) (b t) at hf
  have hst : 0<s t := payOnce_inactive_gaussian_scale_pos Γ B F g ρ h hlocal hmt
  have hsqrt : 0<sqrt (M t:ℝ) := sqrt_pos.mpr (Nat.cast_pos.mpr hmt)
  let y := (b t-bar t)/s t
  have hyupper : y ≤ x t := (div_le_iff₀ hst).mpr (by
    change b t ≤ bar t+s t*x t at hu
    nlinarith)
  have hxupper : x t ≤ |x₀|+1 := (le_abs_self (x t)).trans hxt.le
  have hxlower : -(|x₀|+1) ≤ x t := by linarith [neg_abs_le (x t)]
  have hyR : y ≤ R := by dsimp only [R]; linarith [div_pos hA hσ]
  refine ⟨?_,hyR⟩
  by_cases hbelow : b t ≤ bar t
  · have hz := hh (b t) ⟨by linarith,hbelow⟩
    have hsurplus : bar t+s t*x t-b t ≤ A/sqrt (M t:ℝ) := by
      have he : bar t+s t*x t-b t = Q t (b t)/deriv (Q t) (b t) := by
        rw [hf,mul_div_cancel_right₀ _ hz.2.2.1.ne']
      rw [he]
      exact hz.2.2.2.trans (div_le_div_of_nonneg_left hA.le hsqrt
        (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hbelow))))
    have hscale : (A/σ)*s t=A/sqrt (M t:ℝ) := by
      change (A/σ)*(σ/sqrt (M t:ℝ))=A/sqrt (M t:ℝ)
      field_simp
    have hrep : s t*y=b t-bar t := by dsimp only [y]; field_simp
    have hymin : x t-A/σ ≤ y := by
      apply le_of_mul_le_mul_left (a := s t) _ hst
      rw [hrep]
      rw [← hscale] at hsurplus
      nlinarith
    change -R ≤ y
    dsimp only [R]
    linarith
  · have hypos : 0 ≤ y := div_nonneg (sub_nonneg.mpr (le_of_not_ge hbelow)) hst.le
    exact (neg_nonpos.mpr hR.le).trans hypos

theorem payOnce_inactive_central_foc_bid_limit
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (x b : ℕ → ℝ) {x₀ : ℝ} (hx : Tendsto x atTop (𝓝 x₀))
    (hb : Tendsto b atTop (𝓝 (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)))
    (hupper : ∀ᶠ t in atTop, b t ≤ inactiveGaussianPrice Γ F g ρ (x t) t)
    (hfoc : ∀ᶠ t in atTop,
      let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
      let Q := coverage (k+1) (C t) hn
        (Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)))
      Q (b t)=(inactiveGaussianPrice Γ F g ρ (x t) t-b t)*deriv Q (b t)) :
    Tendsto (fun t => (b t-KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t)))/inactiveGaussianScale M F (k+1) g ρ t)
        atTop (𝓝 (GaussianResponse.response x₀)) := by
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
  let bar := fun t => KernelDemand.populationPrice (k+1)
    (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
  let s := inactiveGaussianScale M F (k+1) g ρ
  let Y := fun t => (b t-bar t)/s t
  let Q := fun t => coverage (k+1) (C t) hn
    (Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)))
  let a := ((k+1:ℕ):ℝ)*(2/((((k+1:ℕ):ℝ)-1)*L))
  have hL : 0<L := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  have hnR : (2:ℝ) ≤ (k+1:ℕ) := by exact_mod_cast hn
  have ha : 0<a := by dsimp only [a]; exact mul_pos (by positivity) (div_pos (by norm_num) (mul_pos (by linarith) hL))
  obtain ⟨R,_hR,hbound⟩ := payOnce_inactive_central_foc_bid_bounded Γ B F g ρ h hlocal x b hx hb hupper hfoc
  apply tendsto_of_subseq_tendsto
  intro φ hφ
  obtain ⟨z,_hz,χ,hχ,hconv⟩ := isCompact_Icc.isSeqCompact.subseq_of_frequently_in
    (hφ.eventually hbound).frequently
  let η := φ ∘ χ
  have hη : Tendsto η atTop atTop := hφ.comp hχ.tendsto_atTop
  have hy : Tendsto (Y ∘ η) atTop (𝓝 z) := hconv
  have hbs : Tendsto (b ∘ η) atTop (𝓝 L) := hb.comp hη
  have hq := payOnce_inactive_central_coverage_tendsto (fun t => Γ (η t)) (fun t => B (η t))
    F g ρ (h.along η hη) hlocal (Y ∘ η) hy
  have hprice : ∀ᶠ t in atTop,
      inactiveGaussianPrice (fun t => Γ (η t)) F g ρ (Y (η t)) t=b (η t) := by
    filter_upwards [hη.eventually (h.population_grows.eventually_gt_atTop 0)] with t ht
    have hs := payOnce_inactive_gaussian_scale_pos Γ B F g ρ h hlocal ht
    change bar (η t)+s (η t)*((b (η t)-bar (η t))/s (η t))=b (η t)
    rw [mul_div_cancel₀ _ (show s (η t) ≠ 0 from hs.ne'),add_sub_cancel]
  have hq' : Tendsto (fun t => Q (η t) (b (η t))/s (η t)) atTop (𝓝 (a*gaussianSuccessPrimitive z)) := by
    apply hq.congr'
    filter_upwards [hprice] with t ht
    change Q (η t) (inactiveGaussianPrice (fun t => Γ (η t)) F g ρ (Y (η t)) t)/s (η t) = _
    rw [ht]
  have hd := payOnce_inactive_central_coverage_derivative (fun t => Γ (η t)) (fun t => B (η t))
    F g ρ (h.along η hη) hlocal (b ∘ η) hbs hy
  have hd' : Tendsto (fun t => deriv (Q (η t)) (b (η t))) atTop (𝓝 (a*cdf (gaussianReal 0 1) z)) := by
    have he : 2*((k+1:ℕ):ℝ)/((((k+1:ℕ):ℝ)-1)*L)=a := by dsimp only [a]; ring
    change Tendsto (fun t => deriv (Q (η t)) (b (η t))) atTop
      (𝓝 ((2*((k+1:ℕ):ℝ)/((((k+1:ℕ):ℝ)-1)*L))*cdf (gaussianReal 0 1) z)) at hd
    rwa [he] at hd
  have hr := ((hx.comp hη).sub hy).mul hd'
  have hsame : (fun t => Q (η t) (b (η t))/s (η t)) =ᶠ[atTop]
      (fun t => (x (η t)-Y (η t))*deriv (Q (η t)) (b (η t))) := by
    filter_upwards [hη.eventually hfoc,hη.eventually (h.population_grows.eventually_gt_atTop 0)] with t ht hmt
    have hs := payOnce_inactive_gaussian_scale_pos Γ B F g ρ h hlocal hmt
    change Q (η t) (b (η t))=(bar (η t)+s (η t)*x (η t)-b (η t))*deriv (Q (η t)) (b (η t)) at ht
    rw [ht]
    dsimp only [Y]
    field_simp [show s (η t) ≠ 0 from hs.ne']
    ring
  have heq := tendsto_nhds_unique hq' (hr.congr' hsame.symm)
  have hresponse : z=GaussianResponse.response x₀ := by
    apply (GaussianResponse.response_equation_iff x₀ z).mp
    apply (mul_left_cancel₀ ha.ne')
    nlinarith only [heq]
  refine ⟨χ,?_⟩
  simpa only [hresponse,Function.comp_def] using hconv

end FCAppendix.Bayes
