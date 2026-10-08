import FCAppendix.PayOnce.InactivePriceConcentration
import FCAppendix.Probability.ClippedSubGaussianMoments

namespace FCAppendix.PayOnce.DummyKernel
open MeasureTheory Set CommonList

theorem integral_allocation_le_entry_probability {ι : Type*} [Fintype ι]
    {n c : ℕ} (hn : 2 ≤ n) (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ] (b : ℝ) :
    (∫ r, allocation n c hn r b ∂μ) ≤ μ.real {r | 0 < allocation n c hn r b} := by
  let p := fun r : ι → ℝ => allocation n c hn r b
  have hp : Measurable p := measurable_allocation_fixed_bid hn b
  have hpb : ∀ r, p r ∈ Icc (0:ℝ) 1 := fun r => allocation_bounds hn r b
  have hi := UnitInterval.integrable μ p hp (fun r => (hpb r).1) (fun r => (hpb r).2)
  have hE : MeasurableSet {r | 0 < p r} := measurableSet_lt measurable_const hp
  have hh := integral_mono hi ((integrable_const (1:ℝ)).indicator hE) (fun r => by
    by_cases hr : 0 < p r
    · simpa only [indicator_of_mem (show r ∈ {r | 0 < p r} from hr)] using (hpb r).2
    · simp only [indicator_of_notMem (show r ∉ {r | 0 < p r} from hr)]
      exact le_of_not_gt hr)
  rw [integral_indicator_const _ hE] at hh
  simpa only [smul_eq_mul,mul_one] using hh

end FCAppendix.PayOnce.DummyKernel

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel PayOnce.KernelTailEvent
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_below_entry_exponential
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) {ε : ℝ} (hε : 0 < ε) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ᶠ t in atTop, ∀ b : ℝ, b ≤ bar t-ε →
      (∫ r, allocation (k+1) (C t) hn r b
        ∂Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))) ≤
          A*Real.exp (-c*(M t:ℝ)) := by
  dsimp only
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  let bar := fun t => KernelDemand.populationPrice (k+1)
    (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
  obtain ⟨K,d,hK,hd,he⟩ := payOnce_inactive_focal_price_concentration Γ B F g ρ h
  let c := min d (ε^2/(2*K^2))/2
  have hc : 0 < c := by dsimp only [c]; positivity
  have hcd : 2*c ≤ d := by dsimp only [c]; linarith [min_le_left d (ε^2/(2*K^2))]
  have hcε : 2*c ≤ ε^2/(2*K^2) := by dsimp only [c]; linarith [min_le_right d (ε^2/(2*K^2))]
  refine ⟨3+2*Real.exp 8,c,by positivity,hc,?_⟩
  filter_upwards [he,h.population_grows.eventually_ge_atTop 2] with t ht htM
  intro b hb
  by_cases hbp : 0 < b
  swap
  · simp only [allocation_eq_zero_of_nonpos hn _ (le_of_not_gt hbp),integral_zero]
    positivity
  let μ := Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
  have hentry : μ.real {r | 0 < allocation (k+1) (C t) hn r b} ≤
      μ.real {r | ε ≤ |focalPrice (k+1) (C t) hn b r-bar t|} := by
    apply measureReal_mono ?_ (measure_ne_top _ _)
    intro r hr
    change 0 < allocation (k+1) (C t) hn r b at hr
    change ε ≤ |focalPrice (k+1) (C t) hn b r-bar t|
    have hs := focalPrice_spec (c := C t) hn b r hbp
    have hprice : focalPrice (k+1) (C t) hn b r < b := by
      by_contra hh
      have hz := (kernel_eq_zero_iff (k+1) hn hbp hs.1).mpr (le_of_not_gt hh)
      rw [hs.2.2,hz] at hr
      exact (lt_irrefl 0 hr).elim
    have hh := neg_le_abs (focalPrice (k+1) (C t) hn b r-bar t)
    linarith
  have hNM : (M t:ℝ)/2 ≤ ((M t-1:ℕ):ℝ) := by
    have he : ((M t-1:ℕ):ℝ)=(M t:ℝ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]
    rw [he]; have : (2:ℝ) ≤ M t := by exact_mod_cast htM
    linarith
  have hscale (a : ℝ) (ha : 2*c ≤ a) : c*(M t:ℝ) ≤ a*((M t-1:ℕ):ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hNM hc.le
    have h2 := mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg (M t-1) : (0:ℝ) ≤ ((M t-1:ℕ):ℝ))
    nlinarith
  have he₀ : Real.exp (-d*((M t-1:ℕ):ℝ)) ≤ Real.exp (-c*(M t:ℝ)) :=
    Real.exp_le_exp.mpr (by linarith [hscale d hcd])
  have he₁ : Real.exp (-((M t-1:ℕ):ℝ)*ε^2/(2*K^2)) ≤ Real.exp (-c*(M t:ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hh := hscale (ε^2/(2*K^2)) hcε
    calc
      _ = -(ε^2/(2*K^2)*((M t-1:ℕ):ℝ)) := by ring
      _ ≤ _ := by simpa only [neg_mul] using neg_le_neg hh
  have htail := ht b hbp ε hε.le
  have hmean := integral_allocation_le_entry_probability (c := C t) hn μ b
  change (∫ r, allocation (k+1) (C t) hn r b ∂μ) ≤ _
  have htotal := hmean.trans (hentry.trans htail)
  have h0 := mul_le_mul_of_nonneg_left he₀ (by norm_num : (0:ℝ) ≤ 3)
  have h1 := mul_le_mul_of_nonneg_left he₁ (by positivity : (0:ℝ) ≤ 2*Real.exp 8)
  nlinarith

theorem payOnce_inactive_below_entry_uniform_scaled_mean
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) {ε : ℝ} (hε : 0 < ε) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    ∀ η : ℝ, 0 < η → ∀ᶠ t in atTop, ∀ b : ℝ, b ≤ bar t-ε →
      Real.sqrt (M t:ℝ)*(∫ r, allocation (k+1) (C t) hn r b
        ∂Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))) < η := by
  dsimp only
  obtain ⟨A,c,hA,hc,he⟩ := payOnce_inactive_below_entry_exponential Γ B F g ρ h hε
  have hlim : Tendsto (fun t => Real.sqrt (M t:ℝ)*(A*Real.exp (-c*(M t:ℝ)))) atTop (𝓝 0) := by
    have hh := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((1:ℝ)/2) c hc).comp
      (tendsto_natCast_atTop_atTop.comp h.population_grows)).const_mul A
    convert hh using 1
    · funext t
      rw [Real.sqrt_eq_rpow]
      dsimp only [Function.comp_def]
      ring
    · simp
  intro η hη
  filter_upwards [he,hlim.eventually_lt_const hη] with t ht hlt b hb
  exact (mul_le_mul_of_nonneg_left (ht b hb) (Real.sqrt_nonneg _)).trans_lt hlt

theorem payOnce_inactive_below_entry_scaled_mean_tendsto
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) (b : ℕ → ℝ) {β : ℝ}
    (hb : Tendsto b atTop (𝓝 β))
    (hβ : β < Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ) :
    Tendsto (fun t => Real.sqrt (M t:ℝ)*
      (∫ r, allocation (k+1) (C t) (by have := h.proposers_two; omega) r (b t)
        ∂Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)))) atTop (𝓝 0) := by
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
  let ε := (L-β)/2
  have hε : 0 < ε := by dsimp only [ε,L]; linarith
  have hgap := ((payOnce_inactive_population_price Γ B F g ρ h).2.sub hb).eventually_const_lt
    (show ε < L-β by dsimp only [ε]; linarith)
  apply Metric.tendsto_nhds.mpr
  intro η hη
  filter_upwards [payOnce_inactive_below_entry_uniform_scaled_mean Γ B F g ρ h hε η hη,hgap]
    with t ht hbt
  have hh := ht (b t) (by linarith)
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _)
    (integral_nonneg fun r => (allocation_bounds hn r (b t)).1))]
  exact hh

end FCAppendix.Bayes
