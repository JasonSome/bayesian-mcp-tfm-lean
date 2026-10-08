import FCAppendix.PayOnce.AllocationFirstMoment
import FCAppendix.PayOnce.InactiveEntryHazard

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList Real
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel PayOnce.EntryDerivativeLower PayOnce.KernelTailEvent
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_upper_entry_bounds
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
    ∃ ε d A : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < d ∧ 0 < A ∧ ∀ᶠ t in atTop,
      ∀ b ∈ Icc (bar t) (bar t+ε), 0 < b ∧ kernel (k+1) b (bar t) ≤ 1/2 ∧
        HasDerivAt (Q t) (deriv (Q t) b) b ∧ d ≤ deriv (Q t) b ∧
        Q t b ≤ A*(b-bar t+(M t:ℝ)^(-(1:ℝ)/2)) := by
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
  obtain ⟨A,hA,herror⟩ := payOnce_inactive_focal_allocation_moments Γ B F g ρ h 1 (by norm_num)
  obtain ⟨c₀,hc₀,hentry⟩ := payOnce_inactive_central_entry_lower Γ B F g ρ h hlocal 0
  obtain ⟨η,hη,_,hC,hcut⟩ := exists_entry_deriv_cutoff (n := k+1) hn
  let K := ((k+1:ℕ):ℝ)/(L/2)
  have hK : 0 < K := by dsimp only [K]; positivity
  let ε := min 1 (min (c₀*η/(4*K)) (1/(2*K)))
  have hε : 0 < ε := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hε₁ : ε ≤ 1 := min_le_left _ _
  have hε₂ : ε ≤ c₀*η/(4*K) := (min_le_right _ _).trans (min_le_left _ _)
  have hε₃ : ε ≤ 1/(2*K) := (min_le_right _ _).trans (min_le_right _ _)
  have hεtail : K*ε ≤ c₀*η/4 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4*K)).mp hε₂
    nlinarith
  have hεhalf : K*ε ≤ 1/2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*K)).mp hε₃
    nlinarith
  have hδ : Tendsto (fun t => (M t:ℝ)^(-(1:ℝ)/2)) atTop (𝓝 0) := by
    simpa only [neg_div,Function.comp_def] using
      (tendsto_rpow_neg_atTop (y := (1:ℝ)/2) (by norm_num)).comp
        (tendsto_natCast_atTop_atTop.comp h.population_grows)
  have hδA : Tendsto (fun t => A*(M t:ℝ)^(-(1:ℝ)/2)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hδ.const_mul A
  have hsmall : ∀ᶠ t in atTop, A*(M t:ℝ)^(-(1:ℝ)/2) ≤ c₀*η/4 :=
    hδA.eventually_le_const (by positivity)
  let d := (entrySlopeConstant (k+1)/(2*(L+2)))*c₀
  have hdcoef : 0 < entrySlopeConstant (k+1)/(2*(L+2)) := div_pos hC (by positivity)
  have hd : 0 < d := mul_pos hdcoef hc₀
  refine ⟨ε,d,((k+1:ℕ):ℝ)*max K A,hε,hε₁,hd,by positivity,?_⟩
  filter_upwards [herror,hentry,hsmall,h.eventually_scarce,
    hbar.eventually (Ioo_mem_nhds (show L/2 < L by linarith) (show L < L+1 by linarith))]
    with t he hce hsm hscarce hbt
  intro b hb
  have hbarpos : 0 < bar t := (by positivity : (0:ℝ) < L/2).trans hbt.1
  have hbp : 0 < b := hbarpos.trans_le hb.1
  have hp0 : kernel (k+1) b (bar t) ≤ K*(b-bar t) := by
    have hh := KernelLawConvergence.kernel_price_difference hn
      (by positivity : (0:ℝ) < L/2) hbt.1.le (hbt.1.le.trans hb.1) b
    rw [kernel_of_le (k+1) le_rfl,sub_zero,
      abs_of_nonneg (kernel_bounds hn hbarpos b).1,
      abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr hb.1)] at hh
    exact hh
  have hpε : kernel (k+1) b (bar t) ≤ K*ε :=
    hp0.trans (mul_le_mul_of_nonneg_left (by linarith [hb.2]) hK.le)
  have hmom : (∫ r, |allocation (k+1) (C t) hn r b-kernel (k+1) b (bar t)| ∂μ t) ≤
      A*(M t:ℝ)^(-(1:ℝ)/2) := by simpa only [rpow_one] using (he b hbp).2
  have hmean := mean_coverage_tail_le_of_error hn (μ t) hbarpos hmom
  have hentryb : c₀ ≤ (μ t).real {r | 0 < allocation (k+1) (C t) hn r b} := by
    simpa only [zero_div,sub_zero] using (hce b (by simpa only [zero_div,sub_zero] using hb.1)).2
  have htail : (μ t).real {r | η ≤ allocation (k+1) (C t) hn r b} ≤
      (μ t).real {r | 0 < allocation (k+1) (C t) hn r b}/2 := by
    apply (hmean.2.2 η hη).trans
    apply le_trans _ (div_le_div_of_nonneg_right hentryb (by norm_num))
    apply (div_le_iff₀ hη).mpr
    nlinarith [hpε.trans hεtail]
  have hatom (x : ℝ) (hx : 0 < x) : (BidScaling.realBidLaw (Γ t) : Measure ℝ) {x} = 0 :=
    realEffectiveBidLaw_positive_atomless (Γ t) hscarce.1 hscarce.2 (h.action_schedule t)
      (h.base_schedule t) (h.users t) (B t) (h.proposers t) (h.symmetry t)
      (h.positive_values_atomless t) (h.visible_atomless t) hx
  have hreg := ae_regularClearing_fixed_bid (ι := Fin (M t-1)) (c := C t)
    (BidScaling.realBidLaw (Γ t) : Measure ℝ) hatom hn hbp
  have hder := hcut (μ t) (C t) b hbp hreg η ⟨hη,le_rfl⟩
  have hD := absorb_bad_mass hC hbp (by linarith [hb.2] : b ≤ L+2)
    measureReal_nonneg htail hder.2
  refine ⟨hbp,hpε.trans hεhalf,hder.1,
    (mul_le_mul_of_nonneg_left hentryb hdcoef.le).trans hD,?_⟩
  have hδnonneg : 0 ≤ (M t:ℝ)^(-(1:ℝ)/2) := rpow_nonneg (Nat.cast_nonneg _) _
  have hlin : kernel (k+1) b (bar t)+A*(M t:ℝ)^(-(1:ℝ)/2) ≤
      max K A*(b-bar t+(M t:ℝ)^(-(1:ℝ)/2)) := by
    have hk := mul_le_mul_of_nonneg_right (le_max_left K A) (sub_nonneg.mpr hb.1)
    have ha := mul_le_mul_of_nonneg_right (le_max_right K A) hδnonneg
    nlinarith
  exact hmean.2.1.trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hlin (Nat.cast_nonneg (k+1)))

end FCAppendix.Bayes
