import FCAppendix.Affine.Uniform07Finishing.Crossover.PhysicalRegularity

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover
open Set Filter Topology MeasureTheory

theorem signed_residual_bound_with_flow
    {eta b delta q flow m e s d s' d' : ℝ}
    (heta : eta∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1)
    (hdelta : delta∈Icc (0:ℝ) 1) (hq : 0≤ q) (hflow : 0≤ flow)
    (hm : 1≤ m) (he : 0≤ e)
    (hs : |s|≤ e*q/m) (hd : |d|≤ e*q/m)
    (hs' : |s'|≤ e*(flow/m+q)) (hd' : |d'|≤ e*(flow/m+q)) :
    |s+eta*d+eta*b*d'-delta*s'|≤ 4*e*(q+flow/m) := by
  have hm0 : 0< m := by linarith
  have heq : 0≤ e*q := mul_nonneg he hq
  have hdiv : e*q/m≤ e*q := (div_le_iff₀ hm0).2 (by nlinarith)
  have hflow' : 0≤ flow/m := div_nonneg hflow hm0.le
  have hmult : eta*b≤ 1 := by
    calc
      eta*b ≤ 1*b := mul_le_mul_of_nonneg_right heta.2 hb.1
      _ = b := one_mul b
      _ ≤ 1 := hb.2
  have hdeta : |eta*d|≤ e*q := by
    rw [abs_mul,abs_of_nonneg heta.1]
    have h := mul_le_mul_of_nonneg_left (hd.trans hdiv) heta.1
    nlinarith [mul_nonneg (sub_nonneg.mpr heta.2) heq]
  have hdt : |eta*b*d'|≤ e*(flow/m+q) := by
    rw [abs_mul,abs_of_nonneg (mul_nonneg heta.1 hb.1)]
    have h := mul_le_mul_of_nonneg_left hd' (mul_nonneg heta.1 hb.1)
    have hbnd : 0≤ e*(flow/m+q) := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hmult) hbnd]
  have hst : |delta*s'|≤ e*(flow/m+q) := by
    rw [abs_mul,abs_of_nonneg hdelta.1]
    have h := mul_le_mul_of_nonneg_left hs' hdelta.1
    have hbnd : 0≤ e*(flow/m+q) := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hdelta.2) hbnd]
  have h₁ := abs_add_le s (eta*d)
  have h₂ := abs_add_le (s+eta*d) (eta*b*d')
  have h₃ := abs_sub (s+eta*d+eta*b*d') (delta*s')
  nlinarith [hs.trans hdiv,hdeta,hdt,hst,h₁,h₂,h₃,mul_nonneg he hflow']

theorem physical_flow_bound_from_IC
    {delta flow canonicalDen N err q m e rentLower Nmax : ℝ}
    (hm : 0< m) (hc : 0< rentLower) (hq : 0≤ q) (hflow : 0≤ flow)
    (hcanon : 0≤ canonicalDen) (hdelta : rentLower/m≤ delta)
    (_he : 0≤ e) (he1 : e≤ 1) (hsmall : 4*e≤ rentLower)
    (hN : N≤ Nmax*q)
    (hIC : delta*(2*flow+canonicalDen)=N+err)
    (herror : |err|≤ 4*e*(q+flow/m)) :
    flow/m≤((Nmax+4)/rentLower)*q := by
  have hdelta0 : 0≤ delta := (div_pos hc hm).le.trans hdelta
  have hflowm : 0≤ flow/m := div_nonneg hflow hm.le
  have hdeltaFlow := mul_le_mul_of_nonneg_right hdelta (by positivity : 0≤ 2*flow)
  have hlow : 2*rentLower*(flow/m)≤ N+err := by
    have hid : (rentLower/m)*(2*flow)=2*rentLower*(flow/m) := by ring
    rw [hid] at hdeltaFlow
    nlinarith [hIC,mul_nonneg hdelta0 hcanon]
  have herr := (abs_le.mp herror).2
  have hcoef := mul_le_mul_of_nonneg_right hsmall hflowm
  have heq := mul_le_mul_of_nonneg_right he1 hq
  have hbound : rentLower*(flow/m)≤(Nmax+4)*q := by nlinarith
  have hid : ((Nmax+4)/rentLower)*q=((Nmax+4)*q)/rentLower := by ring
  rw [hid]
  exact (le_div_iff₀ hc).2 (by nlinarith [hbound])

theorem uniform_residual_after_flow_absorption
    {err q flow m e C : ℝ} (he : 0≤ e)
    (hflow : flow/m≤ C*q)
    (herror : |err|≤ 4*e*(q+flow/m)) :
    |err|≤(4*(1+C)*e)*q := by
  have h := mul_le_mul_of_nonneg_left (add_le_add_left hflow q) (by positivity : 0≤ 4*e)
  nlinarith

theorem physical_barrier_numerator_bounds
    {eta b q d d' Dmax : ℝ}
    (heta : eta∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1)
    (_hq : 0≤ q) (hd : d∈Icc (0:ℝ) q)
    (hd' : d'∈Icc (0:ℝ) (Dmax*q)) :
    q≤ barrierNumerator eta b q d d' ∧
      barrierNumerator eta b q d d'≤(2+Dmax)*q := by
  have hdcoef : (1-eta)*d≤ d := by
    nlinarith [mul_nonneg heta.1 hd.1]
  have hc : 0≤ eta*b*d' := mul_nonneg (mul_nonneg heta.1 hb.1) hd'.1
  have hcoef : eta*b≤ 1 := by
    calc
      eta*b ≤ 1*b := mul_le_mul_of_nonneg_right heta.2 hb.1
      _ = b := one_mul b
      _ ≤ 1 := hb.2
  have hdup : eta*b*d'≤ d' := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hcoef) hd'.1]
  unfold barrierNumerator
  constructor
  · linarith [hd.2]
  · nlinarith [hd'.2,mul_nonneg (sub_nonneg.mpr heta.2) hd.1]

theorem relative_residual_implies_band_budget
    {err q K m eps a0 errorCoefficient e : ℝ}
    (hm : 0< m) (heps : 0< eps) (hq : 0≤ q)
    (hden : a0*m*q≤ K)
    (herr : |err|≤ errorCoefficient*e*q)
    (hsmall : errorCoefficient*e≤ eps*a0/4) :
    |err|≤ eps*K/(4*m) := by
  have h₁ := mul_le_mul_of_nonneg_right hsmall hq
  have h₂ := mul_le_mul_of_nonneg_left hden heps.le
  apply (le_div_iff₀ (by positivity : 0<4*m)).2
  have h₃ := mul_le_mul_of_nonneg_right (herr.trans h₁) (by positivity : 0≤ 4*m)
  nlinarith

theorem actual_marginal_relative_error
    {qActual q s d e m : ℝ} (_hm : 0< m)
    (hid : qActual=q+(s+d)/2)
    (hs : |s|≤ e*q/m) (hd : |d|≤ e*q/m) :
    |qActual-q|≤ e*q/m := by
  rw [hid]
  have habs : |q+(s+d)/2-q|=|s+d|/2 := by
    rw [show q+(s+d)/2-q=(s+d)/2 by ring,abs_div]
    norm_num
  rw [habs]
  have hh := abs_add_le s d
  linarith

theorem actual_log_slope_from_comparison
    {qActual q qActual' q' a eps e tolerance : ℝ}
    (ha : 0≤ a) (hq : 0≤ q) (htol : 0≤ 1+tolerance)
    (hvalue : |qActual-q|≤ e*q)
    (hderiv : |qActual'-q'|≤ e*a*q)
    (hcomp : q'≤(1+eps)*a*q)
    (hbudget : 1+eps+e≤(1+tolerance)*(1-e)) :
    qActual'≤(1+tolerance)*a*qActual := by
  have hqlo : (1-e)*q≤ qActual := by linarith [(abs_le.mp hvalue).1]
  have hdhi := (abs_le.mp hderiv).2
  have hb := mul_le_mul_of_nonneg_right hbudget (mul_nonneg ha hq)
  have hv := mul_le_mul_of_nonneg_left hqlo (mul_nonneg htol ha)
  nlinarith

theorem actual_duplicate_payment_budget
    {eta xi b a C q qActual d dPure e ratioError aMax m : ℝ}
    (heta : 0≤ eta) (hxi : 0< xi) (hb : 0< b) (hb1 : b≤ 1)
    (ha : 0< a) (hm : 0< m) (hq : 0≤ q)
    (hCq : C≤ q) (he : 0≤ e) (hratio : 0≤ 1+ratioError)
    (hcanon : d≤ 2*C*(1+ratioError)/(xi*b*a))
    (hpure : dPure≤ e*q/m) (hscale : a/m≤ aMax)
    (hqActual : (1-e)*q≤ qActual)
    (he1 : e<1) :
    eta*b*(d+dPure)≤
      ((2*eta/xi*(1+ratioError)+eta*e*aMax)/(1-e))*qActual/a := by
  have hcanonical := duplicate_budget_from_U19 heta hxi hb ha hCq hratio hcanon
  have hp := mul_le_mul_of_nonneg_left hpure (mul_nonneg heta hb.le)
  have hscaled : eta*b*(e*q/m)≤ eta*e*aMax*q/a := by
    apply (le_div_iff₀ ha).2
    have hid : eta*b*(e*q/m)*a=b*(eta*e*q*(a/m)) := by ring
    rw [hid]
    have h₁ := mul_le_mul_of_nonneg_right hb1
      (show 0≤ eta*e*q*(a/m) by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hscale
      (mul_nonneg (mul_nonneg heta he) hq)
    nlinarith
  let K := 2*eta/xi*(1+ratioError)+eta*e*aMax
  have haMax : 0≤ aMax := (div_pos ha hm).le.trans hscale
  have hK : 0≤ K := by dsimp [K]; positivity
  have hden : 0<1-e := by linarith
  have htarget := mul_le_mul_of_nonneg_left hqActual
    (div_nonneg (div_nonneg hK hden.le) ha.le)
  have hid : (K/(1-e)/a)*((1-e)*q)=K*q/a := by
    field_simp [hden.ne',ha.ne']
  rw [hid] at htarget
  calc
    eta*b*(d+dPure) = eta*b*d+eta*b*dPure := by ring
    _ ≤ (2*eta/xi*(1+ratioError))*q/a+eta*b*(e*q/m) := add_le_add hcanonical hp
    _ ≤ (2*eta/xi*(1+ratioError))*q/a+eta*e*aMax*q/a := add_le_add le_rfl hscaled
    _ = K*q/a := by dsimp only [K]; ring
    _ ≤ K/(1-e)/a*qActual := htarget
    _ = _ := by dsimp only [K]; ring

end FCAppendix.Affine.Uniform07Finishing.Crossover
