import FCAppendix.PayOnce.KernelTaylor
import FCAppendix.PayOnce.InactiveClippedPriceMean
import FCAppendix.PayOnce.InactivePriceConcentration

namespace FCAppendix.Probability
open MeasureTheory Filter Topology Real

theorem tendsto_sqrt_mul_of_le_div {M : ℕ → ℕ} (hM : Tendsto M atTop atTop)
    {v : ℕ → ℝ} {K : ℝ} (hv : ∀ᶠ t in atTop, 0 ≤ v t ∧ v t ≤ K/(M t:ℝ)) :
    Tendsto (fun t => sqrt (M t:ℝ)*v t) atTop (𝓝 0) := by
  have hs := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hM)
  have hlim : Tendsto (fun t => K/sqrt (M t:ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hs
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [hv] with t ht
    exact mul_nonneg (sqrt_nonneg _) ht.1
  · filter_upwards [hv,hM.eventually_gt_atTop 0] with t ht hmt
    have hm : (0:ℝ) < M t := Nat.cast_pos.mpr hmt
    have hspos := sqrt_pos.mpr hm
    have he : sqrt (M t:ℝ)*(K/(M t:ℝ)) = K/sqrt (M t:ℝ) := by
      apply (eq_div_iff hspos.ne').mpr
      rw [mul_assoc,mul_comm (K/(M t:ℝ)),← mul_assoc,mul_self_sqrt hm.le]
      field_simp
    exact (mul_le_mul_of_nonneg_left ht.2 (sqrt_nonneg _)).trans_eq he

theorem tendsto_sqrt_mul_exp (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    {c : ℝ} (hc : 0 < c) (A : ℝ) :
    Tendsto (fun t => sqrt (M t:ℝ)*(A*exp (-c*(M t:ℝ)))) atTop (𝓝 0) := by
  have hh := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((1:ℝ)/2) c hc).comp
    (tendsto_natCast_atTop_atTop.comp hM)).const_mul A
  convert hh using 1
  · funext t
    rw [sqrt_eq_rpow]
    dsimp only [Function.comp_def]
    ring
  · simp

end FCAppendix.Probability

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList Real
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel PayOnce.KernelTailEvent
open PayOnce.KernelTaylor Probability
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_focal_price_outside_exponential
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) (ell u : ℝ)
    (hell : ell < Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)
    (hu : Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ < u) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ᶠ t in atTop, ∀ b : ℝ, 0 < b →
      (Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))).real
        {r | focalPrice (k+1) (C t) hn b r ∉ Icc ell u} ≤ A*exp (-c*(M t:ℝ)) := by
  dsimp only
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
  let ε := min (L-ell) (u-L)/2
  have hε : 0 < ε := by dsimp [ε,L]; positivity
  have hleft : ell < L-ε := by have := min_le_left (L-ell) (u-L); dsimp [ε]; dsimp [L] at *; linarith
  have hright : L+ε < u := by have := min_le_right (L-ell) (u-L); dsimp [ε]; dsimp [L] at *; linarith
  let bar := fun t => KernelDemand.populationPrice (k+1)
    (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
  have hbar := (payOnce_inactive_population_price Γ B F g ρ h).2
  have hbarI : ∀ᶠ t in atTop, bar t ∈ Ioo (ell+ε) (u-ε) :=
    hbar.eventually (Ioo_mem_nhds (by linarith) (by linarith))
  obtain ⟨K,d,hK,hd,he⟩ := payOnce_inactive_focal_price_concentration Γ B F g ρ h
  let c := min d (ε^2/(2*K^2))/2
  have hc : 0 < c := by dsimp [c]; positivity
  have hcd : 2*c ≤ d := by dsimp [c]; linarith [min_le_left d (ε^2/(2*K^2))]
  have hcε : 2*c ≤ ε^2/(2*K^2) := by dsimp [c]; linarith [min_le_right d (ε^2/(2*K^2))]
  refine ⟨3+2*exp 8,c,by positivity,hc,?_⟩
  filter_upwards [he,hbarI,h.population_grows.eventually_ge_atTop 2] with t ht htbar htM b hb
  let μ := Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
  have hsub : μ.real {r | focalPrice (k+1) (C t) hn b r ∉ Icc ell u} ≤
      μ.real {r | ε ≤ |focalPrice (k+1) (C t) hn b r-bar t|} := by
    apply measureReal_mono ?_ (measure_ne_top _ _)
    intro r hr
    change ε ≤ |focalPrice (k+1) (C t) hn b r-bar t|
    change ¬ (ell ≤ focalPrice (k+1) (C t) hn b r ∧ focalPrice (k+1) (C t) hn b r ≤ u) at hr
    have ha := le_abs_self (focalPrice (k+1) (C t) hn b r-bar t)
    have hb' := neg_le_abs (focalPrice (k+1) (C t) hn b r-bar t)
    rcases not_and_or.mp hr with hr | hr <;> push Not at hr <;> linarith [htbar.1,htbar.2]
  have hNM : (M t:ℝ)/2 ≤ ((M t-1:ℕ):ℝ) := by
    rw [Nat.cast_sub (by omega),Nat.cast_one]
    have : (2:ℝ) ≤ M t := by exact_mod_cast htM
    linarith
  have hscale (a : ℝ) (ha : 2*c ≤ a) : c*(M t:ℝ) ≤ a*((M t-1:ℕ):ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hNM hc.le
    have h2 := mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg (M t-1) : (0:ℝ) ≤ ((M t-1:ℕ):ℝ))
    nlinarith
  have he₀ : exp (-d*((M t-1:ℕ):ℝ)) ≤ exp (-c*(M t:ℝ)) :=
    exp_le_exp.mpr (by linarith [hscale d hcd])
  have he₁ : exp (-((M t-1:ℕ):ℝ)*ε^2/(2*K^2)) ≤ exp (-c*(M t:ℝ)) := by
    apply exp_le_exp.mpr
    have hh := hscale (ε^2/(2*K^2)) hcε
    calc
      _ = -(ε^2/(2*K^2)*((M t-1:ℕ):ℝ)) := by ring
      _ ≤ _ := by simpa only [neg_mul] using neg_le_neg hh
  have htotal := hsub.trans (ht b hb ε hε.le)
  have h0 := mul_le_mul_of_nonneg_left he₀ (by norm_num : (0:ℝ) ≤ 3)
  have h1 := mul_le_mul_of_nonneg_left he₁ (by positivity : (0:ℝ) ≤ 2*exp 8)
  change μ.real _ ≤ _
  nlinarith

theorem payOnce_inactive_clipped_focal_mean_sqrt
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (bs : ℕ → ℝ) {b₀ : ℝ} (hbs : Tendsto bs atTop (𝓝 b₀)) (hb₀ : 0 < b₀)
    (ell u : ℝ) (hell : ell < Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)
    (hu : Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ < u) :
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    let P := fun t => Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    Tendsto (fun t => sqrt (M t:ℝ)*(∫ z,
      clipToInterval ell u (focalPrice (k+1) (C t) hn (bs t) z)-bar t ∂P t)) atTop (𝓝 0) := by
  dsimp only
  let μW := F.map (fun v => max (v-g) 0)
  let s := GaussianParameters.sigma μW (k+1) (Limit.capRoot μW (k+1) ρ)
  have hnet : Measurable (fun v : ℝ => max (v-g) 0) :=
    (measurable_id.sub_const g).max measurable_const
  letI : IsProbabilityMeasure μW := Measure.isProbabilityMeasure_map hnet.aemeasurable
  have hs : 0 < s := GaussianParameters.sigma_pos μW
    (by have := h.proposers_two; omega)
    (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1 hlocal
  have hb : ∀ᶠ t in atTop, bs t ∈ Ioi (0:ℝ) := hbs.eventually (Ioi_mem_nhds hb₀)
  have ht := (payOnce_inactive_clipped_focal_price_mean_uniform Γ B F g ρ h hlocal
    ell u hell hu).tendsto_comp continuousWithinAt_const (tendsto_nhdsWithin_iff.mpr ⟨hbs,hb⟩)
  have hm := ht.const_mul s
  simp only [mul_zero] at hm
  apply hm.congr'
  filter_upwards [h.population_grows.eventually_gt_atTop 0] with t hmt
  have hroot : sqrt (M t:ℝ) ≠ 0 := (sqrt_pos.mpr (Nat.cast_pos.mpr hmt)).ne'
  change s*(_/(s/sqrt (M t:ℝ))) = sqrt (M t:ℝ)*_
  unfold clippedFocalPrice
  field_simp

theorem payOnce_inactive_focal_test_expectation_sqrt
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (bs : ℕ → ℝ) {b₀ : ℝ} (hbs : Tendsto bs atTop (𝓝 b₀))
    (hlo : Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ < b₀)
    (hhi : b₀ < ((k+1:ℕ):ℝ)*Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)
    (ψ : ℝ → ℝ) (hψ : ∀ p ∈ Icc (0:ℝ) 1, ContDiffAt ℝ 2 ψ p)
    (hψm : Measurable ψ) {D : ℝ} (hψD : ∀ p ∈ Icc (0:ℝ) 1, |ψ p| ≤ D) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    let P := fun t => Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
    Tendsto (fun t => sqrt (M t:ℝ)*((∫ r, ψ (allocation (k+1) (C t) hn r (bs t)) ∂P t)-
      ψ (kernel (k+1) (bs t) (bar t)))) atTop (𝓝 0) := by
  dsimp only
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
  have hL : 0 < L := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  have hnR : (0:ℝ) < (k+1:ℕ) := by positivity
  have hb₀ : 0 < b₀ := hL.trans hlo
  obtain ⟨ell,hell₀,hellL⟩ := exists_between (show max 0 (b₀/((k+1:ℕ):ℝ)) < L from
    max_lt hL ((div_lt_iff₀ hnR).mpr (by simpa only [mul_comm] using hhi)))
  have hell : 0 < ell := (le_max_left _ _).trans_lt hell₀
  have hbEll : b₀ < ((k+1:ℕ):ℝ)*ell := by
    have hh := (le_max_right (0:ℝ) (b₀/((k+1:ℕ):ℝ))).trans_lt hell₀
    have hbmul := (div_lt_iff₀ hnR).mp hh
    simpa only [mul_comm] using hbmul
  obtain ⟨u,hLu,hub⟩ := exists_between hlo
  obtain ⟨blo,hublo,hblo⟩ := exists_between hub
  obtain ⟨bhi,hbhi,hbhin⟩ := exists_between hbEll
  let bar := fun t => KernelDemand.populationPrice (k+1)
    (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
  let P := fun t => Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
  let X := fun t => focalPrice (N := M t-1) (k+1) (C t) hn (bs t)
  let m := fun t => ∫ z, clipToInterval ell u (X t z)-bar t ∂P t
  let v := fun t => ∫ z, (clipToInterval ell u (X t z)-bar t)^2 ∂P t
  let e := fun t => (∫ r, ψ (allocation (k+1) (C t) hn r (bs t)) ∂P t)-
    ψ (kernel (k+1) (bs t) (bar t))
  have hb : ∀ᶠ t in atTop, 0 < bs t := hbs.eventually_const_lt hb₀
  have hbI : ∀ᶠ t in atTop, bs t ∈ Icc blo bhi := by
    filter_upwards [hbs.eventually (Ioo_mem_nhds hblo hbhi)] with t ht
    exact ⟨ht.1.le,ht.2.le⟩
  have hbarI : ∀ᶠ t in atTop, bar t ∈ Icc ell u := by
    filter_upwards [(payOnce_inactive_population_price Γ B F g ρ h).2.eventually
      (Ioo_mem_nhds hellL hLu)] with t ht
    exact ⟨ht.1.le,ht.2.le⟩
  have hm : Tendsto (fun t => sqrt (M t:ℝ)*m t) atTop (𝓝 0) :=
    payOnce_inactive_clipped_focal_mean_sqrt Γ B F g ρ h hlocal bs hbs hb₀ ell u hellL hLu
  obtain ⟨J,_,hJ⟩ := payOnce_inactive_clipped_focal_price_moments Γ B F g ρ h ell u hellL hLu
    (r := 2) (by norm_num)
  have hv : Tendsto (fun t => sqrt (M t:ℝ)*v t) atTop (𝓝 0) := by
    apply tendsto_sqrt_mul_of_le_div h.population_grows (K := J)
    filter_upwards [hJ,hb] with t ht hbt
    refine ⟨integral_nonneg (fun _ => sq_nonneg _),?_⟩
    have hh := (ht (bs t) hbt).2
    norm_num only [rpow_two,sq_abs,neg_div,neg_neg,div_self,OfNat.ofNat_ne_zero,rpow_neg_one] at hh
    simpa only [v,X,P,bar,div_eq_mul_inv] using hh
  obtain ⟨A,c,hA,hc,hout⟩ := payOnce_inactive_focal_price_outside_exponential Γ B F g ρ h ell u hellL hLu
  obtain ⟨U,K,_,_,hTaylor⟩ := exists_clipped_kernel_test_integral_bound hn ψ hψ hψm hψD hell hublo hbhin
  have hD : 0 ≤ D := (abs_nonneg (ψ 0)).trans (hψD 0 (by norm_num))
  have hbound : ∀ᶠ t in atTop, |e t| ≤ 2*D*(A*exp (-c*(M t:ℝ)))+U*|m t|+K*v t := by
    filter_upwards [hout,hb,hbI,hbarI] with t ht hbt htI htbar
    have hpoint := hTaylor (P t) (X t) (measurable_focalPrice hn (bs t))
      (fun r => (focalPrice_spec hn (bs t) r hbt).1) (bs t) htI (bar t) htbar
    have heq : (∫ r, ψ (allocation (k+1) (C t) hn r (bs t)) ∂P t) =
        ∫ r, ψ (kernel (k+1) (bs t) (X t r)) ∂P t := by
      apply integral_congr_ae
      exact .of_forall fun r => congrArg ψ (focalPrice_spec hn (bs t) r hbt).2.2
    change |e t| ≤ _
    dsimp only [e]
    rw [heq]
    have hmul : 2*D*(P t).real {z | X t z ∉ Icc ell u} ≤
        2*D*(A*exp (-c*(M t:ℝ))) :=
      mul_le_mul_of_nonneg_left (ht (bs t) hbt) (by positivity)
    dsimp only [m,v]
    linarith
  have hr : Tendsto (fun t => 2*D*(sqrt (M t:ℝ)*(A*exp (-c*(M t:ℝ))))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_sqrt_mul_exp M h.population_grows hc A).const_mul (2*D)
  have hm' : Tendsto (fun t => U*|sqrt (M t:ℝ)*m t|) atTop (𝓝 0) := by
    simpa only [abs_zero,mul_zero] using hm.abs.const_mul U
  have hv' : Tendsto (fun t => K*(sqrt (M t:ℝ)*v t)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hv.const_mul K
  have hsum := (hr.add hm').add hv'
  simp only [zero_add] at hsum
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (.of_forall fun t => norm_nonneg _) ?_ hsum
  filter_upwards [hbound] with t ht
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sqrt_nonneg _)]
  have hh := mul_le_mul_of_nonneg_left ht (sqrt_nonneg (M t:ℝ))
  simpa only [abs_mul,abs_of_nonneg (sqrt_nonneg _),mul_add,mul_assoc,mul_left_comm] using hh

theorem payOnce_inactive_focal_allocation_mean_sqrt
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (bs : ℕ → ℝ) {b₀ : ℝ} (hbs : Tendsto bs atTop (𝓝 b₀))
    (hlo : Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ < b₀)
    (hhi : b₀ < ((k+1:ℕ):ℝ)*Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    let P := fun t => Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
    Tendsto (fun t => sqrt (M t:ℝ)*((∫ r, allocation (k+1) (C t) hn r (bs t) ∂P t)-
      kernel (k+1) (bs t) (bar t))) atTop (𝓝 0) := by
  exact payOnce_inactive_focal_test_expectation_sqrt Γ B F g ρ h hlocal bs hbs hlo hhi
    id (fun _ _ => contDiffAt_id) measurable_id
    (D := 1) (fun p hp => by simpa only [id_eq,abs_of_nonneg hp.1] using hp.2)

theorem payOnce_inactive_focal_coverage_mean_sqrt
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (bs : ℕ → ℝ) {b₀ : ℝ} (hbs : Tendsto bs atTop (𝓝 b₀))
    (hlo : Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ < b₀)
    (hhi : b₀ < ((k+1:ℕ):ℝ)*Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    let P := fun t => Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
    Tendsto (fun t => sqrt (M t:ℝ)*(coverage (k+1) (C t) hn (P t) (bs t)-
      success (k+1) (kernel (k+1) (bs t) (bar t)))) atTop (𝓝 0) := by
  exact payOnce_inactive_focal_test_expectation_sqrt Γ B F g ρ h hlocal bs hbs hlo hhi
    (success (k+1)) (fun p _ => contDiffAt_success_two _ p) (continuous_success _).measurable
    (D := 1) (fun p hp => by
      have hpos : 0 ≤ success (k+1) p := by
        unfold success
        exact sub_nonneg.mpr (pow_le_one₀ (sub_nonneg.mpr hp.2) (by linarith [hp.1]))
      rw [abs_of_nonneg hpos]
      exact success_le_one _ _ hp.2)

theorem payOnce_inactive_focal_phi_mean_sqrt
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (bs : ℕ → ℝ) {b₀ : ℝ} (hbs : Tendsto bs atTop (𝓝 b₀))
    (hlo : Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ < b₀)
    (hhi : b₀ < ((k+1:ℕ):ℝ)*Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    let P := fun t => Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
    Tendsto (fun t => sqrt (M t:ℝ)*((∫ r, RareSuccessSlope.phi (k+1)
      (allocation (k+1) (C t) hn r (bs t)) ∂P t)-
      RareSuccessSlope.phi (k+1) (kernel (k+1) (bs t) (bar t)))) atTop (𝓝 0) := by
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  exact payOnce_inactive_focal_test_expectation_sqrt Γ B F g ρ h hlocal bs hbs hlo hhi
    (RareSuccessSlope.phi (k+1)) (fun _ hp => contDiffAt_phi_two hn hp)
    (RareSuccessSlope.measurable_phi _) (D := ((k+1:ℕ):ℝ)^2)
    (fun _ hp => by
      rw [abs_of_nonneg (RareSuccessSlope.phi_nonneg hn hp)]
      exact RareSuccessSlope.phi_le_sq hn hp)

end FCAppendix.Bayes
