import FCAppendix.PayOnce.GaussianParameters
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace FCAppendix.PayOnce.Limit
open MeasureTheory ProbabilityTheory Set Filter Topology

theorem hasDerivAt_pStar_price_of_lt {n : ℕ} (hn : 2 ≤ n) {T w : ℝ}
    (hT : 0 < T) (hTw : T < w) :
    HasDerivAt (fun S => pStar n S w)
      (-((T/w)^(1/((n:ℝ)-1)-1)*(1/((n:ℝ)-1))/w)) T := by
  have hw := hT.trans hTw
  have hd := (((hasDerivAt_id T).div_const w).rpow_const
    (p := 1/((n:ℝ)-1)) (Or.inl (div_pos hT hw).ne')).const_sub 1
  have he : -(1/w*(1/((n:ℝ)-1))*(id T/w)^(1/((n:ℝ)-1)-1)) =
      -((T/w)^(1/((n:ℝ)-1)-1)*(1/((n:ℝ)-1))/w) := by dsimp only [id]; ring
  rw [he] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hT,eventually_lt_nhds hTw] with S hS hSw
  exact pStar_of_lt hn hS.le hSw

theorem pStar_price_difference_lower {n : ℕ} (hn : 2 ≤ n) {S U w z : ℝ}
    (hS : 0 < S) (hSU : S ≤ U) (hUw : U < w) (hwz : w ≤ z) :
    (1/((n:ℝ)-1))/z*(U-S) ≤ pStar n S w-pStar n U w := by
  obtain hSU | rfl := hSU.lt_or_eq
  · have he := exponent_pos hn
    have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
    have he1 : 1/((n:ℝ)-1) ≤ 1 := by
      apply (div_le_iff₀ (by linarith : (0:ℝ) < (n:ℝ)-1)).mpr
      linarith
    let f := fun T => pStar n T w
    let f' := fun T => -((T/w)^(1/((n:ℝ)-1)-1)*(1/((n:ℝ)-1))/w)
    have hd (T : ℝ) (hT : T ∈ Icc S U) : HasDerivAt f (f' T) T :=
      hasDerivAt_pStar_price_of_lt hn (hS.trans_le hT.1) (hT.2.trans_lt hUw)
    obtain ⟨T,hT,hder⟩ := exists_hasDerivAt_eq_slope f f' hSU
      (fun T hT => (hd T hT).continuousAt.continuousWithinAt)
      (fun T hT => hd T ⟨hT.1.le,hT.2.le⟩)
    have hw : 0 < w := (hS.trans hSU).trans hUw
    have hz : 0 < z := hw.trans_le hwz
    have hq0 : 0 < T/w := div_pos (hS.trans hT.1) hw
    have hq1 : T/w ≤ 1 := (div_le_one hw).mpr (hT.2.le.trans hUw.le)
    have hp : 1 ≤ (T/w)^(1/((n:ℝ)-1)-1) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hq0 hq1 (by linarith)
    have hlo : (1/((n:ℝ)-1))/z ≤
        (T/w)^(1/((n:ℝ)-1)-1)*(1/((n:ℝ)-1))/w := by
      calc
        (1/((n:ℝ)-1))/z ≤ (1/((n:ℝ)-1))/w := div_le_div_of_nonneg_left he.le hw hwz
        _ ≤ _ := (div_le_div_iff_of_pos_right hw).mpr (by nlinarith)
    have hden : 0 < U-S := sub_pos.mpr hSU
    have hmult := (div_eq_iff hden.ne').mp hder.symm
    dsimp only [f,f'] at hmult
    have hmul := mul_le_mul_of_nonneg_right hlo hden.le
    nlinarith
  · simp

theorem demand_price_difference_lower (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) {a z S U : ℝ} (hS : 0 < S) (hSU : S ≤ U)
    (hUa : U ≤ a) :
    ((1/((n:ℝ)-1))/z*μ.real (Ioo a z))*(U-S) ≤
      demand μ n S-demand μ n U := by
  have hi := integral_mono
    ((integrable_const ((1/((n:ℝ)-1))/z*(U-S))).indicator measurableSet_Ioo)
    ((integrable_pStar (n := n) μ hS.le).sub (integrable_pStar (n := n) μ (hS.le.trans hSU)))
    (show ∀ w : ℝ, (Ioo a z).indicator (fun _ => (1/((n:ℝ)-1))/z*(U-S)) w ≤
      pStar n S w-pStar n U w from ?_)
  · simp only [Pi.sub_apply] at hi
    rw [integral_indicator_const _ measurableSet_Ioo,smul_eq_mul,
      integral_sub (integrable_pStar (n := n) μ hS.le) (integrable_pStar (n := n) μ (hS.le.trans hSU))] at hi
    unfold demand
    nlinarith [hi]
  · intro w
    by_cases hw : w ∈ Ioo a z
    · rw [indicator_of_mem hw]
      exact pStar_price_difference_lower hn hS hSU (hUa.trans_lt hw.1) hw.2.le
    · rw [indicator_of_notMem hw]
      exact sub_nonneg.mpr (pStar_antitone_price hn hS.le hSU w)

theorem price_difference_le_demand_difference (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) {a z S U : ℝ} (hS : 0 < S) (hU : 0 < U)
    (hSa : S ≤ a) (hUa : U ≤ a) (hz : 0 < z) (hmass : 0 < μ.real (Ioo a z)) :
    |U-S| ≤ |demand μ n U-demand μ n S| /
      ((1/((n:ℝ)-1))/z*μ.real (Ioo a z)) := by
  have hc : 0 < (1/((n:ℝ)-1))/z*μ.real (Ioo a z) :=
    mul_pos (div_pos (exponent_pos hn) hz) hmass
  apply (le_div_iff₀ hc).mpr
  rcases le_total S U with hSU | hUS
  · rw [abs_of_nonneg (sub_nonneg.mpr hSU),
      abs_of_nonpos (sub_nonpos.mpr (demand_antitone μ hn hS.le hSU))]
    have hh := demand_price_difference_lower μ hn (z := z) hS hSU hUa
    nlinarith
  · rw [abs_of_nonpos (sub_nonpos.mpr hUS),
      abs_of_nonneg (sub_nonneg.mpr (demand_antitone μ hn hU.le hUS))]
    have hh := demand_price_difference_lower μ hn (z := z) hU hUS hSa
    nlinarith

theorem exists_served_value_window (μ : Measure ℝ) [IsFiniteMeasure μ] {L : ℝ}
    (hlocal : GaussianParameters.LocalFullSupport μ L) :
    ∃ a z : ℝ, L < a ∧ a < z ∧ 0 < μ.real (Ioo a z) := by
  obtain ⟨ε,hε,hfull⟩ := hlocal
  refine ⟨L+ε/4,L+ε/2,by linarith,by linarith,?_⟩
  exact ENNReal.toReal_pos (ne_of_gt (hfull (L+ε/4) (L+ε/2)
    (by linarith) (by linarith) (by linarith))) (measure_ne_top _ _)

theorem eventually_capRoot_difference_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : ρ < μ.real (Ioi 0))
    (hlocal : GaussianParameters.LocalFullSupport μ (capRoot μ n ρ)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ r in 𝓝 ρ,
      |capRoot μ n r-capRoot μ n ρ| ≤ K*|r-ρ| := by
  obtain ⟨hL,hroot⟩ := capRoot_spec μ hn hρ0 hρ
  obtain ⟨a,z,hLa,haz,hmass⟩ := exists_served_value_window μ hlocal
  have hz : 0 < z := (hL.trans hLa).trans haz
  let c := (1/((n:ℝ)-1))/z*μ.real (Ioo a z)
  have hc : 0 < c := mul_pos (div_pos (exponent_pos hn) hz) hmass
  refine ⟨c⁻¹,inv_pos.mpr hc,?_⟩
  have hcont := continuousAt_capRoot μ hn hρ0 hρ
  filter_upwards [Ioo_mem_nhds hρ0 hρ,hcont (eventually_lt_nhds hLa)] with r hr hra
  obtain ⟨hr0,hrr⟩ := capRoot_spec μ hn hr.1 hr.2
  have hh := price_difference_le_demand_difference μ hn hL hr0 hLa.le hra.le hz hmass
  rw [hrr,hroot] at hh
  simpa only [c,div_eq_mul_inv,mul_comm] using hh

theorem capRoot_difference_isLittleO (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : ρ < μ.real (Ioi 0))
    (hlocal : GaussianParameters.LocalFullSupport μ (capRoot μ n ρ))
    {r s : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 ρ))
    (hsmall : (fun t => r t-ρ) =o[atTop] s) :
    (fun t => capRoot μ n (r t)-capRoot μ n ρ) =o[atTop] s := by
  obtain ⟨K,hK,hbound⟩ := eventually_capRoot_difference_bound μ hn hρ0 hρ hlocal
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  filter_upwards [hr.eventually hbound,hsmall.bound (div_pos hε hK)] with t ht hsmallt
  simp only [Real.norm_eq_abs] at hsmallt ⊢
  have hh := mul_le_mul_of_nonneg_left hsmallt hK.le
  calc
    |capRoot μ n (r t)-capRoot μ n ρ| ≤ K*|r t-ρ| := ht
    _ ≤ K*(ε/K*|s t|) := hh
    _ = ε*|s t| := by field_simp

theorem root_error_isLittleO_of_demand_error (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : ρ < μ.real (Ioi 0))
    (hlocal : GaussianParameters.LocalFullSupport μ (capRoot μ n ρ))
    {r S s : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 ρ))
    (hS : Tendsto S atTop (𝓝 (capRoot μ n ρ)))
    (herr : (fun t => demand μ n (S t)-r t) =o[atTop] s) :
    (fun t => S t-capRoot μ n (r t)) =o[atTop] s := by
  obtain ⟨hL,hroot⟩ := capRoot_spec μ hn hρ0 hρ
  obtain ⟨a,z,hLa,haz,hmass⟩ := exists_served_value_window μ hlocal
  have hz : 0 < z := (hL.trans hLa).trans haz
  let c := (1/((n:ℝ)-1))/z*μ.real (Ioo a z)
  have hc : 0 < c := mul_pos (div_pos (exponent_pos hn) hz) hmass
  have ht := (continuousAt_capRoot μ hn hρ0 hρ).tendsto.comp hr
  have hbound : ∀ᶠ t in atTop,
      |S t-capRoot μ n (r t)| ≤ |demand μ n (S t)-r t|/c := by
    filter_upwards [hr.eventually (Ioo_mem_nhds hρ0 hρ),
      ht.eventually (eventually_lt_nhds hLa),hS.eventually (eventually_lt_nhds hLa),
      hS.eventually (eventually_gt_nhds hL)] with t hrt htt hSt hS0
    obtain ⟨hpos,he⟩ := capRoot_spec μ hn hrt.1 hrt.2
    have hh := price_difference_le_demand_difference μ hn hpos hS0 htt.le hSt.le hz hmass
    rw [he] at hh
    exact hh
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  filter_upwards [hbound,herr.bound (mul_pos hε hc)] with t ht herrt
  simp only [Real.norm_eq_abs] at herrt ⊢
  calc
    |S t-capRoot μ n (r t)| ≤ |demand μ n (S t)-r t|/c := ht
    _ ≤ (ε*c*|s t|)/c := (div_le_div_iff_of_pos_right hc).mpr herrt
    _ = ε*|s t| := by field_simp

end FCAppendix.PayOnce.Limit
