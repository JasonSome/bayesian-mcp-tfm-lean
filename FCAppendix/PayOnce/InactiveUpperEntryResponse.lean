import FCAppendix.PayOnce.InactiveUpperEntryBounds
import FCAppendix.PayOnce.InactiveDerivativeApproximation
import FCAppendix.PayOnce.GaussianResidualBounds
import FCAppendix.PayOnce.NearEntryFOCResponse

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList Real
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel PayOnce.KernelTailEvent
open PayOnce.RareSuccessSlope
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_upper_entry_response_error
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    let μ := fun t => Measure.pi (fun _ : Fin (M t-1) =>
      (BidScaling.realBidLaw (Γ t) : Measure ℝ))
    let Q := fun t => coverage (k+1) (C t) hn (μ t)
    ∃ ε D : ℝ, 0 < ε ∧ 0 < D ∧ ∀ᶠ t in atTop,
      ∀ w b : ℝ, b ∈ Icc (bar t) (bar t+ε) →
        Q t b=(w-b)*deriv (Q t) b →
        |(∫ r, allocation (k+1) (C t) hn r b ∂μ t)-Limit.pStar (k+1) (bar t) w| ≤
          D*(M t:ℝ)^(-(1:ℝ)/2) := by
  dsimp only
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
  let bar := fun t => KernelDemand.populationPrice (k+1)
    (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
  let μ := fun t => Measure.pi (fun _ : Fin (M t-1) =>
    (BidScaling.realBidLaw (Γ t) : Measure ℝ))
  let Q := fun t => coverage (k+1) (C t) hn (μ t)
  have hL : 0 < L := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  have hbar := (payOnce_inactive_population_price Γ B F g ρ h).2
  obtain ⟨ε,d,A,hε,hε₁,hd,hA,hbounds⟩ := payOnce_inactive_upper_entry_bounds Γ B F g ρ h hlocal
  obtain ⟨A₁,c,hA₁,hc,hderiv⟩ := payOnce_inactive_derivative_approximation Γ B F g ρ h
  obtain ⟨A₂,hA₂,hmoment⟩ := payOnce_inactive_focal_allocation_moments Γ B F g ρ h 1 (by norm_num)
  let K := A/d
  have hK : 0 < K := div_pos hA hd
  let R := (L+2)*((k+1:ℕ):ℝ)*A₂+K*A₁*(ε+2+1/sqrt c)
  have hR : 0 < R := by dsimp only [R]; positivity
  let D := A₂+(((k+1:ℕ):ℝ)*2^((k+1)-2))*R/(L/2)
  have hD : 0 < D := by dsimp only [D]; positivity
  have hδ : Tendsto (fun t => (M t:ℝ)^(-(1:ℝ)/2)) atTop (𝓝 0) := by
    simpa only [neg_div,Function.comp_def] using
      (tendsto_rpow_neg_atTop (y := (1:ℝ)/2) (by norm_num)).comp
        (tendsto_natCast_atTop_atTop.comp h.population_grows)
  refine ⟨ε,D,hε,hD,?_⟩
  filter_upwards [hbounds,hderiv,hmoment,hδ.eventually_le_const (by norm_num : (0:ℝ) < 1),
    h.population_grows.eventually_ge_atTop 1,
    hbar.eventually (Ioo_mem_nhds (show L/2 < L by linarith) (show L < L+1 by linarith))]
    with t hbo hde hmo hδ₁ htM hbt
  intro w b hb hFOC
  change Q t b=(w-b)*deriv (Q t) b at hFOC
  obtain ⟨hbp,hphalf,_,hdfloor,hQupper⟩ := hbo b hb
  have hderpos : 0 < deriv (Q t) b := hd.trans_le hdfloor
  have hbarpos : 0 < bar t := (by positivity : (0:ℝ) < L/2).trans hbt.1
  have hbhi : b ≤ L+2 := by linarith [hb.2]
  let p₀ := kernel (k+1) b (bar t)
  have hp₀ : p₀ ∈ Icc (0:ℝ) 1 := kernel_bounds hn hbarpos b
  let δ := (M t:ℝ)^(-(1:ℝ)/2)
  have hδnonneg : 0 ≤ δ := rpow_nonneg (Nat.cast_nonneg _) _
  have hQnonneg : 0 ≤ Q t b := integral_nonneg fun r =>
    Limit.success_nonneg (by omega) (allocation_bounds hn r b).1 (allocation_bounds hn r b).2
  have hsurEq : w-b=Q t b/deriv (Q t) b := by
    rw [hFOC,mul_div_cancel_right₀ _ hderpos.ne']
  have hsur0 : 0 ≤ w-b := by rw [hsurEq]; exact div_nonneg hQnonneg hderpos.le
  have hsur : w-b ≤ K*(b-bar t+δ) := by
    rw [hsurEq]
    have hh := div_le_div₀ (mul_nonneg hA.le (add_nonneg (sub_nonneg.mpr hb.1) hδnonneg))
      hQupper hd hdfloor
    exact hh.trans_eq (by dsimp only [K]; ring)
  have hmom : (∫ r, |allocation (k+1) (C t) hn r b-p₀| ∂μ t) ≤ A₂*δ := by
    simpa only [rpow_one] using (hmo b hbp).2
  have hQerr : |Q t b-success (k+1) p₀| ≤ ((k+1:ℕ):ℝ)*A₂*δ := by
    have hh := AnalyticalKernel.integral_success_error_le (μ t) (k+1)
      (fun r => allocation (k+1) (C t) hn r b) (measurable_allocation_fixed_bid hn b)
      (fun r => allocation_bounds hn r b) hp₀
    exact hh.trans (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hmom (Nat.cast_nonneg (k+1)))
  have hdErr : |b*deriv (Q t) b-phi (k+1) p₀| ≤
      A₁*δ+A₁*exp (-c*(M t:ℝ)*(b-bar t)^2) := (hde b hb.1).2
  have hsurErr := surplus_mul_derivative_error_le
    (Nat.cast_pos.mpr (by omega : 0 < M t)) hc
    (by linarith [hb.2] : b-bar t ≤ ε) hK.le hA₁.le hδ₁ hsur
  have hres : |b*success (k+1) p₀-(w-b)*phi (k+1) p₀| ≤ R*δ := by
    calc
      _ = |b*(success (k+1) p₀-Q t b)+(w-b)*(b*deriv (Q t) b-phi (k+1) p₀)| := by
        congr 1
        rw [hFOC]
        ring
      _ ≤ b*|Q t b-success (k+1) p₀|+(w-b)*|b*deriv (Q t) b-phi (k+1) p₀| := by
        simpa only [abs_mul,abs_of_pos hbp,abs_of_nonneg hsur0,abs_sub_comm (success (k+1) p₀)]
          using abs_add_le (b*(success (k+1) p₀-Q t b))
            ((w-b)*(b*deriv (Q t) b-phi (k+1) p₀))
      _ ≤ (L+2)*(((k+1:ℕ):ℝ)*A₂*δ)+
          K*A₁*(ε+2+1/sqrt c)*δ := by
        apply add_le_add
        · exact mul_le_mul hbhi hQerr (abs_nonneg _) (by positivity)
        · exact (mul_le_mul_of_nonneg_left hdErr hsur0).trans hsurErr
      _ = R*δ := by dsimp only [R]; ring
  have hinv := NearEntryFOCResponse.kernel_response_error_of_residual hn hbarpos hb.1
    (by linarith : b ≤ w) hphalf hres
  have hresp : |p₀-Limit.pStar (k+1) (bar t) w| ≤
      ((((k+1:ℕ):ℝ)*2^((k+1)-2))*R/(L/2))*δ := by
    apply hinv.trans
    have hh := div_le_div_of_nonneg_left (by positivity :
      0 ≤ (((k+1:ℕ):ℝ)*2^((k+1)-2))*(R*δ)) (by positivity : (0:ℝ) < L/2) hbt.1.le
    exact hh.trans_eq (by ring)
  have hmean := (allocation_mean_error_le hn (μ t) b p₀).trans hmom
  have hh := abs_sub_le (∫ r, allocation (k+1) (C t) hn r b ∂μ t) p₀
    (Limit.pStar (k+1) (bar t) w)
  change _ ≤ D*δ
  dsimp only [D]
  nlinarith

end FCAppendix.Bayes
