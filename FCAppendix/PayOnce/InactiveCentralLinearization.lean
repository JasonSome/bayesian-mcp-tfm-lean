import FCAppendix.PayOnce.KernelEntryL1
import FCAppendix.PayOnce.InactiveCentralMean

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList Real
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel PayOnce.KernelTailEvent
open PayOnce.KernelTaylor PayOnce.KernelEntryExpectation Probability
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_central_allocation_linearization
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (y : ℕ → ℝ) {z : ℝ} (hy : Tendsto y atTop (𝓝 z)) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    let s := inactiveGaussianScale M F (k+1) g ρ
    let b := fun t => bar t+s t*y t
    let X := fun t => clippedFocalPrice (N := M t-1) (k+1) (C t) hn (3*L/4) (5*L/4) (b t)
    Tendsto (fun t => ∫ r, |allocation (k+1) (C t) hn r (b t)/s t-
      (2/((((k+1:ℕ):ℝ)-1)*L))*max (y t-(X t r-bar t)/s t) 0|
        ∂Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))) atTop (𝓝 0) := by
  dsimp only
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  let μW := F.map (fun v => max (v-g) 0)
  let L := Limit.capRoot μW (k+1) ρ
  let σ := GaussianParameters.sigma μW (k+1) L
  let bar := fun t => KernelDemand.populationPrice (k+1)
    (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
  let s := inactiveGaussianScale M F (k+1) g ρ
  let b := fun t => bar t+s t*y t
  let μ := fun t => Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
  let X := fun t => clippedFocalPrice (N := M t-1) (k+1) (C t) hn (3*L/4) (5*L/4) (b t)
  let α := 2/((((k+1:ℕ):ℝ)-1)*L)
  have hnet : Measurable (fun v : ℝ => max (v-g) 0) :=
    (measurable_id.sub_const g).max measurable_const
  letI : IsProbabilityMeasure μW := Measure.isProbabilityMeasure_map hnet.aemeasurable
  have hL : 0 < L := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  have hσ : 0 < σ := GaussianParameters.sigma_pos μW hn hL hlocal
  have hell : 3*L/4 < L := by linarith
  have hu : L < 5*L/4 := by linarith
  have hbar : Tendsto bar atTop (𝓝 L) := (payOnce_inactive_population_price Γ B F g ρ h).2
  have hs : Tendsto s atTop (𝓝 0) := inactiveGaussianScale_tendsto_zero M F (k+1) g ρ h.population_grows
  have hb : Tendsto b atTop (𝓝 L) := payOnce_inactive_gaussian_bid_tendsto Γ B F g ρ h y hy
  have hbp : ∀ᶠ t in atTop, 0 < b t := hb.eventually_const_lt hL
  have hbI : ∀ᶠ t in atTop, b t ∈ Icc (3*L/4) (5*L/4) := by
    filter_upwards [hb.eventually (Ioo_mem_nhds hell hu)] with t ht
    exact ⟨ht.1.le,ht.2.le⟩
  have hsp : ∀ᶠ t in atTop, 0 < s t := by
    filter_upwards [h.population_grows.eventually_gt_atTop 0] with t ht
    exact payOnce_inactive_gaussian_scale_pos Γ B F g ρ h hlocal ht
  obtain ⟨J,_hJ,hJbound⟩ := payOnce_inactive_normalized_clipped_focal_secondMoment Γ B F g ρ h hlocal
    (3*L/4) (5*L/4) hell hu
  obtain ⟨U,hU,hentry⟩ := KernelEntryExpansion.exists_kernel_entry_expansion hn hL
  obtain ⟨A,c,_hA,hc,hout⟩ := payOnce_inactive_focal_price_outside_exponential Γ B F g ρ h
    (3*L/4) (5*L/4) hell hu
  have hrembound : Tendsto (fun t => U*(4*s t*((y t)^2+J)+|bar t-L| *(|y t|+1+J)))
      atTop (𝓝 0) := by
    have h0 := (hs.const_mul 4).mul ((hy.pow 2).add_const J)
    have h1 := ((hbar.sub_const L).abs).mul ((hy.abs.add_const 1).add_const J)
    simpa only [sub_self,abs_zero,mul_zero,zero_mul,zero_add] using (h0.add h1).const_mul U
  have hrare : Tendsto (fun t => 2*(A*exp (-c*(M t:ℝ)))/s t) atTop (𝓝 0) := by
    have hh := (tendsto_sqrt_mul_exp M h.population_grows hc A).const_mul (2/σ)
    convert hh using 1
    · funext t
      change 2*(A*exp (-c*(M t:ℝ)))/(σ/sqrt (M t:ℝ)) = _
      simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
      ring
    · simp
  apply squeeze_zero' (.of_forall fun t => integral_nonneg fun r => abs_nonneg _)
    (g := fun t => 2*(A*exp (-c*(M t:ℝ)))/s t+
      U*(4*s t*((y t)^2+J)+|bar t-L| *(|y t|+1+J))) ?_
    (by simpa only [zero_add] using hrare.add hrembound)
  filter_upwards [hJbound,hbI,hbp,hsp,hout] with t ht htI hbt hst hot
  let p := fun r : Fin (M t-1) → ℝ => allocation (k+1) (C t) hn r (b t)
  let q := fun r => kernel (k+1) (b t) (X t r)
  let v := fun r => α*max (y t-(X t r-bar t)/s t) 0
  have hXI r : X t r ∈ Icc (3*L/4) (5*L/4) := clipToInterval_mem (by linarith) _
  have hXp r : 0 < X t r := (by linarith : 0 < 3*L/4).trans_le (hXI r).1
  have hpm : Measurable p := measurable_allocation_fixed_bid hn (b t)
  have hXm : Measurable (X t) := measurable_clippedFocalPrice hn _ _ (b t)
  have hqm : Measurable q := measurable_kernel_of_positive_price hn hbt hXm hXp
  have hpb r : p r ∈ Icc (0:ℝ) 1 := allocation_bounds hn r (b t)
  have hqb r : q r ∈ Icc (0:ℝ) 1 := kernel_bounds hn (hXp r) (b t)
  have hpi : Integrable p (μ t) := UnitInterval.integrable _ _ hpm (fun r => (hpb r).1) (fun r => (hpb r).2)
  have hqi : Integrable q (μ t) := UnitInterval.integrable _ _ hqm (fun r => (hqb r).1) (fun r => (hqb r).2)
  have hXi : Integrable (X t) (μ t) :=
    (memLp_of_bounded (.of_forall hXI) hXm.aestronglyMeasurable 2).integrable (by norm_num)
  have hvi : Integrable v (μ t) :=
    (((integrable_const (y t)).sub ((hXi.sub (integrable_const (bar t))).div_const (s t))).sup
      (integrable_const 0)).const_mul α
  have hE : MeasurableSet {r : Fin (M t-1) → ℝ | focalPrice (k+1) (C t) hn (b t) r ∈ Icc (3*L/4) (5*L/4)} :=
    (measurable_focalPrice hn (b t)) measurableSet_Icc
  have hcmp := abs_integral_sub_le_of_eq_on (μ t) (g := fun _ => (0:ℝ)) (hpm.sub hqm).abs measurable_const
    (B := 1) (fun r => by simp only [Pi.sub_apply]; rw [abs_abs,abs_le]; constructor <;> linarith [(hpb r).1,(hpb r).2,(hqb r).1,(hqb r).2])
    (fun _ => by norm_num) hE (by
      intro r hr
      have he : X t r=focalPrice (k+1) (C t) hn (b t) r := by
        simp only [X,clippedFocalPrice,clipToInterval,min_eq_right hr.2,max_eq_right hr.1]
      change |p r-q r|=0
      dsimp only [p,q]
      rw [he,(focalPrice_spec hn (b t) r hbt).2.2,sub_self,abs_zero])
  have hbad : (∫ r, |p r/s t-q r/s t| ∂μ t) ≤ 2*(A*exp (-c*(M t:ℝ)))/s t := by
    have hh : (∫ r, |p r-q r| ∂μ t) ≤ 2*(A*exp (-c*(M t:ℝ))) := by
      have hc := hcmp.trans (mul_le_mul_of_nonneg_left (hot (b t) hbt) (by norm_num))
      simpa only [integral_const,mul_zero,smul_zero,sub_zero,
        abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _),mul_one,Pi.sub_apply] using hc
    simp_rw [← sub_div,abs_div,abs_of_pos hst,integral_div]
    exact div_le_div_of_nonneg_right hh hst.le
  have hrem : (∫ r, |q r/s t-v r| ∂μ t) ≤
      U*(4*s t*((y t)^2+J)+|bar t-L| *(|y t|+1+J)) := by
    exact normalized_integral_abs_entry_error_le (μ t) hn hL (X t) hXm hXI
      id measurable_id (B := 1) (fun p hp => by simpa only [id_eq,abs_of_nonneg hp.1] using hp.2)
      hU.le hst htI (hentry (b t) htI) (ht (b t) hbt).2.2
  have habi : Integrable (fun r => |p r/s t-q r/s t|) (μ t) :=
    ((hpi.div_const (s t)).sub (hqi.div_const (s t))).abs
  have hbci : Integrable (fun r => |q r/s t-v r|) (μ t) :=
    ((hqi.div_const (s t)).sub hvi).abs
  have haci : Integrable (fun r => |p r/s t-v r|) (μ t) :=
    ((hpi.div_const (s t)).sub hvi).abs
  have htri := integral_mono haci (habi.add hbci)
    (fun r => abs_sub_le (p r/s t) (q r/s t) (v r))
  simp only [Pi.add_apply] at htri
  rw [integral_add habi hbci] at htri
  exact htri.trans (add_le_add hbad hrem)

end FCAppendix.Bayes
