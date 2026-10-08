import FCAppendix.PayOnce.InactiveDemandIncrement

namespace FCAppendix.PayOnce.GaussianThresholds
open MeasureTheory ProbabilityTheory Filter Topology Set

theorem raw_threshold_tendsto
    (N C : ℕ → ℕ) (p V : ℕ → ℝ) {ρ v x : ℝ}
    (hN : Tendsto N atTop atTop) (hv : 0 < v)
    (hcap : Tendsto (fun t => (C t:ℝ)/((N t+1:ℕ):ℝ)) atTop (𝓝 ρ))
    (hV : Tendsto V atTop (𝓝 v))
    (hp : Tendsto (fun t => Real.sqrt (N t)*
      (p t-(C t:ℝ)/((N t+1:ℕ):ℝ))) atTop (𝓝 (-Real.sqrt v*x))) (d : ℝ) :
    Tendsto (fun t => ((C t:ℝ)-d-(N t:ℝ)*p t)/Real.sqrt ((N t:ℝ)*V t)) atTop (𝓝 x) := by
  have hsN := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hN)
  have hz := (hcap.sub_const d).div_atTop hsN
  have hden := hV.sqrt
  have hroot : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have ht := (hz.sub hp).div hden hroot.ne'
  have hlim : (0-(-Real.sqrt v*x))/Real.sqrt v = x := by field_simp; ring
  rw [hlim] at ht
  apply ht.congr'
  filter_upwards [hN.eventually_gt_atTop 0,hV.eventually (eventually_gt_nhds hv)] with t hn hvt
  have hnR : (0:ℝ) < N t := Nat.cast_pos.mpr hn
  have hspos : 0 < Real.sqrt (N t) := Real.sqrt_pos.mpr hnR
  have hmpos : (0:ℝ) < (N t:ℝ)+1 := by positivity
  have hvpos : 0 < Real.sqrt (V t) := Real.sqrt_pos.mpr hvt
  have hsq := Real.sq_sqrt hnR.le
  simp only [Pi.div_apply,Function.comp_apply]
  rw [Real.sqrt_mul hnR.le]
  push_cast
  field_simp
  rw [hsq]
  ring

theorem population_threshold_tendsto
    (M C : ℕ → ℕ) (p V : ℕ → ℝ) {v x : ℝ}
    (hM : Tendsto M atTop atTop) (hv : 0 < v) (hV : Tendsto V atTop (𝓝 v))
    (hp : Tendsto (fun t => Real.sqrt (M t)*(p t-(C t:ℝ)/(M t))) atTop
      (𝓝 (-Real.sqrt v*x))) (d : ℝ) :
    Tendsto (fun t => ((C t:ℝ)-d-(M t:ℝ)*p t)/Real.sqrt ((M t:ℝ)*V t)) atTop (𝓝 x) := by
  have hsM := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hM)
  have hz : Tendsto (fun t => d/Real.sqrt (M t)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hsM
  have hroot : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have ht := (hp.neg.sub hz).div hV.sqrt hroot.ne'
  have hlim : (-(-Real.sqrt v*x)-0)/Real.sqrt v = x := by field_simp; ring
  rw [hlim] at ht
  apply ht.congr'
  filter_upwards [hM.eventually_gt_atTop 0,hV.eventually (eventually_gt_nhds hv)] with t hm hvt
  have hmR : (0:ℝ) < M t := Nat.cast_pos.mpr hm
  have hspos : 0 < Real.sqrt (M t) := Real.sqrt_pos.mpr hmR
  have hvpos : 0 < Real.sqrt (V t) := Real.sqrt_pos.mpr hvt
  have hsq := Real.sq_sqrt hmR.le
  simp only [Pi.div_apply]
  rw [Real.sqrt_mul hmR.le]
  field_simp
  rw [hsq]
  ring

theorem sqrt_rival_population_ratio (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) :
    Tendsto (fun t => Real.sqrt (N t)/Real.sqrt ((N t+1:ℕ):ℝ)) atTop (𝓝 1) := by
  have hh := ((tendsto_natCast_div_add_atTop (1:ℝ)).comp hN).sqrt
  simpa only [Function.comp_apply,Real.sqrt_one,Real.sqrt_div (Nat.cast_nonneg _),Nat.cast_add,Nat.cast_one] using hh

end FCAppendix.PayOnce.GaussianThresholds

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.OwnImpact
variable {M N C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def inactiveGaussianScale (M : ℕ → ℕ) (F : Measure ℝ) (n : ℕ) (g ρ : ℝ)
    (t : ℕ) : ℝ :=
  GaussianParameters.sigma (F.map (fun v => max (v-g) 0)) n
    (Limit.capRoot (F.map (fun v => max (v-g) 0)) n ρ)/Real.sqrt (M t)

noncomputable def inactiveGaussianPrice
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (F : Measure ℝ) (g ρ x : ℝ) (t : ℕ) : ℝ :=
  KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t)) +
    inactiveGaussianScale M F (k+1) g ρ t*x

theorem inactiveGaussianScale_tendsto_zero (M : ℕ → ℕ) (F : Measure ℝ) (n : ℕ) (g ρ : ℝ)
    (hM : Tendsto M atTop atTop) :
    Tendsto (inactiveGaussianScale M F n g ρ) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop
    (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hM))

theorem payOnce_inactive_gaussian_scale_pos
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) {t : ℕ} (ht : 0 < M t) :
    0 < inactiveGaussianScale M F (k+1) g ρ t := by
  let μW := F.map (fun v => max (v-g) 0)
  have hnet : Measurable (fun v : ℝ => max (v-g) 0) :=
    (measurable_id.sub_const g).max measurable_const
  letI : IsProbabilityMeasure μW := Measure.isProbabilityMeasure_map hnet.aemeasurable
  have hk := h.proposers_two
  have hL := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  exact div_pos (GaussianParameters.sigma_pos μW (by omega) hL hlocal)
    (Real.sqrt_pos.mpr (Nat.cast_pos.mpr ht))

theorem payOnce_inactive_gaussian_price_tendsto
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) (x : ℝ) :
    Tendsto (inactiveGaussianPrice Γ F g ρ x) atTop
      (𝓝 (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) := by
  have hh := (payOnce_inactive_population_price Γ B F g ρ h).2.add
    ((inactiveGaussianScale_tendsto_zero M F (k+1) g ρ h.population_grows).mul_const x)
  unfold inactiveGaussianPrice
  simpa only [zero_mul,add_zero] using hh

theorem InactiveSequenceAssumptions.rivals_grow
    {Γ : ∀ t, FiniteGame (N t+1) (k+1) (C t) Seed}
    {B : ∀ t, PosteriorSystem (Γ t)} {F : Measure ℝ} {g ρ : ℝ}
    (h : InactiveSequenceAssumptions (fun t => N t+1) C Γ B F g ρ) :
    Tendsto N atTop atTop := by
  have hh := (tendsto_sub_atTop_nat 1).comp h.population_grows
  change Tendsto (fun t => (N t+1)-1) atTop atTop at hh
  simpa only [Nat.add_sub_cancel] using hh

theorem payOnce_inactive_gaussian_mean_shift
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) (x : ℝ) :
    let μW := F.map (fun v => max (v-g) 0)
    let L := Limit.capRoot μW (k+1) ρ
    Tendsto (fun t => Real.sqrt (M t)*
      ((∫ b, kernel (k+1) b (inactiveGaussianPrice Γ F g ρ x t)
        ∂(BidScaling.realBidLaw (Γ t) : Measure ℝ))-(C t:ℝ)/(M t))) atTop
      (𝓝 (-Real.sqrt (variance (Limit.pStar (k+1) L) μW)*x)) := by
  dsimp only
  let μW := F.map (fun v => max (v-g) 0)
  let L := Limit.capRoot μW (k+1) ρ
  let A := EndpointVariance.priceSlope μW (k+1) L
  let σ := GaussianParameters.sigma μW (k+1) L
  let v := variance (Limit.pStar (k+1) L) μW
  have hnet : Measurable (fun v : ℝ => max (v-g) 0) :=
    (measurable_id.sub_const g).max measurable_const
  letI : IsProbabilityMeasure μW := Measure.isProbabilityMeasure_map hnet.aemeasurable
  have hk := h.proposers_two
  have hL : 0 < L := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  have hA : 0 < A := GaussianParameters.priceSlope_pos μW (by omega) hL hlocal.crossing.2
  have hσ : 0 < σ := GaussianParameters.sigma_pos μW (by omega) hL hlocal
  have hσA : σ*A = Real.sqrt v := div_mul_cancel₀ _ hA.ne'
  by_cases hx : x = 0
  · subst x
    simp only [mul_zero,inactiveGaussianPrice,add_zero]
    apply tendsto_const_nhds.congr'
    filter_upwards [payOnce_inactive_population_kernel_mean Γ B F g ρ h] with t ht
    rw [ht,sub_self,mul_zero]
  let S := fun t => KernelDemand.populationPrice (k+1)
    (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
  let δ := fun t => inactiveGaussianScale M F (k+1) g ρ t*x
  have hS : Tendsto S atTop (𝓝 L) := (payOnce_inactive_population_price Γ B F g ρ h).2
  have hδ : Tendsto δ atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (inactiveGaussianScale_tendsto_zero M F (k+1) g ρ h.population_grows).mul_const x
  have hδne : ∀ᶠ t in atTop, δ t ≠ 0 := by
    filter_upwards [h.population_grows.eventually_gt_atTop 0] with t ht
    exact mul_ne_zero (div_ne_zero hσ.ne' (Real.sqrt_pos.mpr (Nat.cast_pos.mpr ht)).ne') hx
  have hinc := payOnce_inactive_demand_increment_tendsto Γ B F g ρ h hS hδ hδne
  have hsize : Tendsto (fun t => Real.sqrt (M t)*δ t) atTop (𝓝 (σ*x)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [h.population_grows.eventually_gt_atTop 0] with t ht
    have hs : Real.sqrt (M t) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr ht)).ne'
    change σ*x = Real.sqrt (M t)*(σ/Real.sqrt (M t)*x)
    field_simp
  have hprod := hinc.mul hsize
  have htarget : (-A)*(σ*x) = -Real.sqrt v*x := by
    calc
      (-A)*(σ*x) = -(σ*A)*x := by ring
      _ = -Real.sqrt v*x := by rw [hσA]
  change Tendsto _ atTop (𝓝 ((-A)*(σ*x))) at hprod
  rw [htarget] at hprod
  apply hprod.congr'
  filter_upwards [(payOnce_inactive_population_price Γ B F g ρ h).1,
    (payOnce_inactive_gaussian_price_tendsto Γ B F g ρ h x).eventually
      (eventually_gt_nhds hL),hδne] with t ht hT hdt
  have hclear := (KernelDemand.populationPrice_spec ht.exists).2
  rw [realBidLaw_kernel_mean_eq_demand (Γ t) (by omega) hT,← hclear]
  change ((KernelDemand.demand (k+1) (bidLaw (Γ t) : Measure ENNReal) (S t+δ t)-
    KernelDemand.demand (k+1) (bidLaw (Γ t) : Measure ENNReal) (S t))/δ t)*
    (Real.sqrt (M t)*δ t) = Real.sqrt (M t)*
      (KernelDemand.demand (k+1) (bidLaw (Γ t) : Measure ENNReal) (S t+δ t)-
        KernelDemand.demand (k+1) (bidLaw (Γ t) : Measure ENNReal) (S t))
  field_simp

theorem payOnce_inactive_population_price_threshold_tendsto
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) (x d : ℝ) :
    Tendsto (fun t => ((C t:ℝ)-d-(M t:ℝ)*
      (∫ b, kernel (k+1) b (inactiveGaussianPrice Γ F g ρ x t)
        ∂(BidScaling.realBidLaw (Γ t) : Measure ℝ)))/
      Real.sqrt ((M t:ℝ)*variance (fun b => kernel (k+1) b (inactiveGaussianPrice Γ F g ρ x t))
        (BidScaling.realBidLaw (Γ t) : Measure ℝ))) atTop (𝓝 x) := by
  let μW := F.map (fun v => max (v-g) 0)
  have hnet : Measurable (fun v : ℝ => max (v-g) 0) :=
    (measurable_id.sub_const g).max measurable_const
  letI : IsProbabilityMeasure μW := Measure.isProbabilityMeasure_map hnet.aemeasurable
  have hk := h.proposers_two
  have hL := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  have hv := GaussianParameters.variance_pos μW (n := k+1) (by omega) hL hlocal
  exact GaussianThresholds.population_threshold_tendsto M C _ _ h.population_grows hv
    (payOnce_inactive_real_kernel_variance_tendsto Γ B F g ρ h
      (payOnce_inactive_gaussian_price_tendsto Γ B F g ρ h x))
    (payOnce_inactive_gaussian_mean_shift Γ B F g ρ h hlocal x) d

theorem payOnce_inactive_rival_price_threshold_tendsto
    (Γ : ∀ t, FiniteGame (N t+1) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions (fun t => N t+1) C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) (x d : ℝ) :
    Tendsto (fun t => ((C t:ℝ)-d-(N t:ℝ)*
      (∫ b, kernel (k+1) b (inactiveGaussianPrice Γ F g ρ x t)
        ∂(BidScaling.realBidLaw (Γ t) : Measure ℝ)))/
      Real.sqrt ((N t:ℝ)*variance (fun b => kernel (k+1) b (inactiveGaussianPrice Γ F g ρ x t))
        (BidScaling.realBidLaw (Γ t) : Measure ℝ))) atTop (𝓝 x) := by
  let μW := F.map (fun v => max (v-g) 0)
  let L := Limit.capRoot μW (k+1) ρ
  let v := variance (Limit.pStar (k+1) L) μW
  have hnet : Measurable (fun v : ℝ => max (v-g) 0) :=
    (measurable_id.sub_const g).max measurable_const
  letI : IsProbabilityMeasure μW := Measure.isProbabilityMeasure_map hnet.aemeasurable
  have hk := h.proposers_two
  have hL : 0 < L := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  have hv : 0 < v := GaussianParameters.variance_pos μW (by omega) hL hlocal
  have hN := h.rivals_grow
  have hratio := GaussianThresholds.sqrt_rival_population_ratio N hN
  have hfull := payOnce_inactive_gaussian_mean_shift Γ B F g ρ h hlocal x
  have hrival : Tendsto (fun t => Real.sqrt (N t)*
      ((∫ b, kernel (k+1) b (inactiveGaussianPrice Γ F g ρ x t)
        ∂(BidScaling.realBidLaw (Γ t) : Measure ℝ))-(C t:ℝ)/((N t+1:ℕ):ℝ))) atTop
      (𝓝 (-Real.sqrt v*x)) := by
    have hh := hratio.mul hfull
    simp only [one_mul] at hh
    apply hh.congr
    intro t
    have hs : Real.sqrt ((N t+1:ℕ):ℝ) ≠ 0 :=
      (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.succ_pos _))).ne'
    field_simp
  exact GaussianThresholds.raw_threshold_tendsto N C _ _ hN hv h.capacity_ratio
    (payOnce_inactive_real_kernel_variance_tendsto Γ B F g ρ h
      (payOnce_inactive_gaussian_price_tendsto Γ B F g ρ h x)) hrival d

end FCAppendix.Bayes
