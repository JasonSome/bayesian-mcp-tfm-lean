import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover

def utilityOne (v b q : ℝ) : ℝ := (v-b)*q

def utilityTwo (eta v b q d : ℝ) : ℝ :=
  (v-b)*(2*q-d)-eta*b*d

theorem route_difference (eta v b q d : ℝ) :
    utilityTwo eta v b q d-utilityOne v b q =
      (v-b)*(q-d)-eta*b*d := by
  unfold utilityOne utilityTwo
  ring

theorem route_difference_low_form (eta v b q d : ℝ) :
    utilityTwo eta v b q d-utilityOne v b q =
      utilityOne v b q-((v-b)+eta*b)*d := by
  unfold utilityOne utilityTwo
  ring

theorem expand_stieltjes_density
    (eta b delta q q' d d' sErr sErr' dErr dErr' : ℝ)
    (hic : delta*(2*q'-d'+sErr') =
      (2*q-d+sErr)+eta*(d+dErr)+eta*b*(d'+dErr')) :
    delta*(2*q'-d') =
      2*q-(1-eta)*d+eta*b*d' +
        (sErr+eta*dErr+eta*b*dErr'-delta*sErr') := by
  nlinarith [hic]

def barrierNumerator (eta b q d d' : ℝ) : ℝ :=
  2*q-(1-eta)*d+eta*b*d'

def barrierDenominator (a q d' : ℝ) : ℝ := 2*a*q-d'

def barrier (eta b a q d d' : ℝ) : ℝ :=
  barrierNumerator eta b q d d' / barrierDenominator a q d'

theorem barrier_denominator_positive {a q d' : ℝ}
    (ha : 0< a) (hq : 0< q) (hd' : d'≤ a*q) :
    0< barrierDenominator a q d' := by
  unfold barrierDenominator
  nlinarith [mul_pos ha hq]

theorem barrier_denominator_of_uniform_bounds
    {a q d' a0 d0 m : ℝ}
    (hq : 0< q) (ha0 : 0< a0) (hm : 0< m)
    (ha : a0*m≤ a) (hd' : d'≤ d0*q) (hlarge : d0< a0*m) :
    0< barrierDenominator a q d' := by
  apply barrier_denominator_positive (lt_of_lt_of_le (mul_pos ha0 hm) ha) hq
  exact hd'.trans ((mul_le_mul_of_nonneg_right (hlarge.le.trans ha) hq.le))

theorem scaled_barrier_exact {eta b a q d d' m : ℝ}
    (hq : q≠0) (hm : m≠0)
    (hden : barrierDenominator a q d'≠0) :
    m*barrier eta b a q d d' =
      (2-(1-eta)*(d/q)+eta*b*(d'/q)) /
        (2*(a/m)-d'/(m*q)) := by
  unfold barrier barrierNumerator barrierDenominator at *
  have hd : 2*(a/m)-d'/(m*q)≠0 := by
    intro h
    have hh := congrArg (fun z : ℝ => z*(m*q)) h
    field_simp [hm,hq] at hh
    exact hden (by nlinarith [hh])
  field_simp [hm,hq,hden,hd]

theorem scaled_barrier_error {N K m lead eps : ℝ}
    (hK : 0< K) (hres : |m*N-lead*K|≤ eps*K) :
    |m*(N/K)-lead|≤ eps := by
  have he : m*(N/K)-lead=(m*N-lead*K)/K := by
    field_simp [hK.ne']
  rw [he,abs_div,abs_of_pos hK]
  exact (div_le_iff₀ hK).2 hres

theorem barrier_band_identity {delta q q' a d' N err : ℝ}
    (hden : barrierDenominator a q d'≠0)
    (hic : delta*(2*q'-d')=N+err) :
    2*delta*(q'-a*q) =
      (N/barrierDenominator a q d'-delta)*
        barrierDenominator a q d'+err := by
  have hid : (N/barrierDenominator a q d')*
      barrierDenominator a q d'=N := div_mul_cancel₀ _ hden
  unfold barrierDenominator at *
  nlinarith [hid,hic]

theorem negative_band_derivative_signs
    {delta p c p' rank' a d' N err gamma : ℝ}
    (hdelta : 0< delta) (hp : 0< p) (hc : 0< c)
    (hp' : 0< p') (hden : 0< barrierDenominator a (p+c) d')
    (hic : delta*(2*(p'*rank'+a*c)-d')=N+err)
    (hbudget : 0 <
      (N/barrierDenominator a (p+c) d'-delta)*
        barrierDenominator a (p+c) d'+err)
    (hrate : (1+gamma)*p'< a*p) :
    1+gamma< rank' ∧
      (a*c*(p+c)-c*(p'*rank'+a*c))/(p+c)^2<0 := by
  have hband := barrier_band_identity hden.ne' hic
  have hq' : a*(p+c)< p'*rank'+a*c := by
    have hpos : 0<2*delta*(p'*rank'+a*c-a*(p+c)) := by
      rw [hband]
      exact hbudget
    have hfactor : 0<2*delta := by positivity
    exact sub_pos.mp ((mul_pos_iff_of_pos_left hfactor).mp hpos)
  have hcross : a*p< p'*rank' := by nlinarith [hq']
  refine ⟨?_,?_⟩
  · by_contra h
    have hr : rank'≤ 1+gamma := le_of_not_gt h
    have hh := mul_le_mul_of_nonneg_left hr hp'.le
    nlinarith
  · have hn : a*c*(p+c)-c*(p'*rank'+a*c)<0 := by
      nlinarith [mul_pos hc (sub_pos.mpr hq')]
    exact div_neg_of_neg_of_pos hn (sq_pos_of_pos (add_pos hp hc))

theorem negative_band_error_budget {T delta K err eps m : ℝ}
    (hK : 0< K) (heps : 0< eps) (hm : 0< m)
    (hband : eps/(2*m)≤ T-delta)
    (herr : |err|≤ eps*K/(4*m)) :
    0<(T-delta)*K+err := by
  have he := (abs_le.mp herr).1
  have hmK := mul_le_mul_of_nonneg_right hband hK.le
  have hp : 0< eps*K/(4*m) := by positivity
  have hid : (eps/(2*m))*K = 2*(eps*K/(4*m)) := by ring
  nlinarith [hid]

theorem safe_side_log_slope {delta q q' a d' N err eps : ℝ}
    (hdelta : 0< delta) (hden : barrierDenominator a q d'≠0)
    (hic : delta*(2*q'-d')=N+err)
    (hbudget :
      (N/barrierDenominator a q d'-delta)*
        barrierDenominator a q d'+err ≤ 2*delta*eps*a*q) :
    q'≤(1+eps)*a*q := by
  have hid := barrier_band_identity hden hic
  have hm : 0<2*delta := by positivity
  have hh : q'-a*q≤ eps*a*q := by
    apply (mul_le_mul_iff_right₀ hm).mp
    nlinarith [hid,hbudget]
  nlinarith

theorem gap_reset_exact {delta N canonicalDen totalDen : ℝ}
    (hN : 0≤ N) (hc : 0< canonicalDen)
    (hden : canonicalDen≤ totalDen)
    (hleft : N≤ delta*canonicalDen) :
    N/totalDen≤ delta := by
  have ht : 0< totalDen := hc.trans_le hden
  have hq : N/totalDen≤ N/canonicalDen :=
    div_le_div_of_nonneg_left hN hc hden
  exact hq.trans ((div_le_iff₀ hc).2 hleft)

theorem gap_reset_with_error {delta N canonicalDen totalDen err : ℝ}
    (hc : 0< canonicalDen) (hden : canonicalDen≤ totalDen)
    (hN : 0≤ N-err) (hleft : N-err≤ delta*canonicalDen) :
    N/totalDen-err/totalDen≤ delta := by
  simpa only [sub_div] using gap_reset_exact hN hc hden hleft

theorem low_optimizer_strict_route_gap {eta v b q d L : ℝ}
    (hv : 0< v) (hb : 0≤ b) (_hbv : b≤ v)
    (_heta0 : 0≤ eta) (heta1 : eta≤ 1) (hd : 0≤ d)
    (hu : v*L/2≤ utilityOne v b q) (hsmall : d< L/2) :
    v*(L/2-d) ≤ utilityTwo eta v b q d-utilityOne v b q ∧
      utilityOne v b q < utilityTwo eta v b q d := by
  have hcoeff : (v-b)+eta*b≤ v := by
    nlinarith [mul_nonneg (sub_nonneg.mpr heta1) hb]
  have hdup := mul_le_mul_of_nonneg_right hcoeff hd
  have hbound : v*(L/2-d) ≤
      utilityTwo eta v b q d-utilityOne v b q := by
    rw [route_difference_low_form]
    nlinarith [hu,hdup]
  refine ⟨hbound,?_⟩
  apply sub_pos.mp
  exact (mul_pos hv (sub_pos.mpr hsmall)).trans_le hbound

theorem route_gap_from_relative_rent
    {eta v b q d a eps duplicateBudget : ℝ}
    (ha : 0< a) (hq : 0< q) (_hd : 0≤ d) (hdq : d≤ q)
    (_heps : eps≤ 1)
    (hrent : (1-eps)/a≤ v-b)
    (hdup : eta*b*d≤ duplicateBudget*q/a) :
    ((1-eps)*(1-d/q)-duplicateBudget)*q/a ≤
      utilityTwo eta v b q d-utilityOne v b q := by
  have hmul := mul_le_mul_of_nonneg_right hrent (sub_nonneg.mpr hdq)
  have hid : ((1-eps)*(1-d/q)-duplicateBudget)*q/a =
      ((1-eps)/a)*(q-d)-duplicateBudget*q/a := by
    field_simp [ha.ne',hq.ne']
  rw [hid,route_difference]
  linarith

theorem strict_route_gap_from_relative_rent
    {eta v b q d a eps duplicateBudget : ℝ}
    (ha : 0< a) (hq : 0< q) (hd : 0≤ d) (hdq : d≤ q)
    (heps : eps≤ 1) (hrent : (1-eps)/a≤ v-b)
    (hdup : eta*b*d≤ duplicateBudget*q/a)
    (hmargin : 0<(1-eps)*(1-d/q)-duplicateBudget) :
    utilityOne v b q < utilityTwo eta v b q d := by
  have hb := route_gap_from_relative_rent ha hq hd hdq heps hrent hdup
  apply sub_pos.mp
  exact (div_pos (mul_pos hmargin hq) ha).trans_le hb

theorem duplicate_budget_from_U19
    {eta xi b a c q d eps : ℝ}
    (heta : 0≤ eta) (hxi : 0< xi) (hb : 0< b) (ha : 0< a)
    (hcq : c≤ q) (heps : 0≤ 1+eps)
    (hd : d≤ 2*c*(1+eps)/(xi*b*a)) :
    eta*b*d ≤ (2*eta/xi)*(1+eps)*q/a := by
  have hmul := mul_le_mul_of_nonneg_left hd (mul_nonneg heta hb.le)
  have hcoef : 0≤(2*eta/xi)*(1+eps)/a := by positivity
  have hq := mul_le_mul_of_nonneg_left hcq hcoef
  have hid : eta*b*(2*c*(1+eps)/(xi*b*a)) =
      ((2*eta/xi)*(1+eps)/a)*c := by
    field_simp [hxi.ne',hb.ne',ha.ne']
  rw [hid] at hmul
  calc
    _ ≤ ((2*eta/xi)*(1+eps)/a)*c := hmul
    _ ≤ ((2*eta/xi)*(1+eps)/a)*q := hq
    _ = _ := by ring

end FCAppendix.Affine.Uniform07Finishing.Crossover
