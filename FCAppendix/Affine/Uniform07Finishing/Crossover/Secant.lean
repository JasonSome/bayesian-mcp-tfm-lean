import FCAppendix.Affine.Uniform07Finishing.Crossover.SupportGaps

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover
open Set MeasureTheory Filter Topology

theorem ac_growth_bound {q : ℝ→ℝ} {a b rate : ℝ}
    (hab : a≤ b) (hq : AbsolutelyContinuousOnInterval q a b)
    (hder : ∀ᵐ x ∂volume, x∈Icc a b → deriv q x≤ rate*q x) :
    q b≤ Real.exp (rate*(b-a))*q a := by
  let e : ℝ→ℝ := fun x => Real.exp (-rate*x)
  let f : ℝ→ℝ := fun x => e x*q x
  have heAC : AbsolutelyContinuousOnInterval e a b := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    dsimp [e]
    fun_prop
  have hfAC : AbsolutelyContinuousOnInterval f a b := heAC.fun_mul hq
  have heDer (x : ℝ) : HasDerivAt e (-rate*e x) x := by
    dsimp [e]
    convert! (((hasDerivAt_id x).const_mul (-rate)).exp) using 1; simp only [id_eq]; ring
  have hfder : ∀ᵐ x ∂volume.restrict (Icc a b), deriv f x≤ 0 := by
    apply (ae_restrict_iff' measurableSet_Icc).2
    filter_upwards [hq.ae_differentiableAt,hder] with x hqdiff hx hxab
    have hxu : x∈uIcc a b := by simpa only [uIcc_of_le hab] using hxab
    have hqD := (hqdiff hxu).hasDerivAt
    have hformula : deriv f x=e x*(deriv q x-rate*q x) := by
      convert! ((heDer x).mul hqD).deriv using 1; ring
    rw [hformula]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      (sub_nonpos.mpr (hx hxab))
  have hinc := ac_increment_upper hab hfAC hfder
  have hf : f b≤ f a := by linarith
  calc
    q b = Real.exp (rate*b)*f b := by
      dsimp [f,e]
      rw [←mul_assoc,←Real.exp_add]
      simp
    _ ≤ Real.exp (rate*b)*f a :=
      mul_le_mul_of_nonneg_left hf (Real.exp_pos _).le
    _ = Real.exp (rate*(b-a))*q a := by
      dsimp [f,e]
      rw [←mul_assoc,←Real.exp_add]
      congr 1
      ring

theorem singleton_rent_of_growth_ratio
    {v b h qL qR Gamma : ℝ}
    (hbv : b≤ v) (_hh : 0< h) (hqL : 0< qL) (hGamma : 1< Gamma)
    (hopt : (v-(b-h))*qL≤(v-b)*qR)
    (hgrowth : qR≤ Gamma*qL) :
    h/(Gamma-1)≤ v-b := by
  have hmul := mul_le_mul_of_nonneg_left hgrowth (sub_nonneg.mpr hbv)
  have hcancel : h*qL≤((v-b)*(Gamma-1))*qL := by
    nlinarith [hopt,hmul]
  have hh' := (mul_le_mul_iff_left₀ hqL).mp hcancel
  exact (div_le_iff₀ (sub_pos.mpr hGamma)).2 hh'

theorem exp_mul_one_sub_le_one (z : ℝ) :
    Real.exp z*(1-z)≤ 1 := by
  have hh := Real.add_one_le_exp (-z)
  have hm := mul_le_mul_of_nonneg_left hh (Real.exp_pos z).le
  rw [←Real.exp_add] at hm
  simp only [add_neg_cancel,Real.exp_zero] at hm
  nlinarith [hm]

theorem exponential_secant_bounds {z : ℝ} (hz : 0< z) (_hz1 : z<1) :
    1-z≤ z/(Real.exp z-1) ∧ z/(Real.exp z-1)≤ 1 := by
  have he : 0< Real.exp z-1 := by
    have hh : Real.exp 0< Real.exp z := Real.exp_lt_exp.mpr hz
    simpa using hh
  constructor
  · apply (le_div_iff₀ he).2
    nlinarith [exp_mul_one_sub_le_one z]
  · apply (div_le_iff₀ he).2
    have hh := Real.add_one_le_exp z
    linarith

theorem singleton_scaled_rent
    {v b qL qR a eps tau : ℝ}
    (ha : 0< a) (heps : 0≤ eps) (htau : 0< tau)
    (hsmall : (1+eps)*tau<1) (hbv : b≤ v) (hqL : 0< qL)
    (hopt : (v-(b-tau/a))*qL≤(v-b)*qR)
    (hgrowth : qR≤ Real.exp ((1+eps)*tau)*qL) :
    1-eps-(1+eps)*tau≤ a*(v-b) := by
  have hz : 0<(1+eps)*tau := by positivity
  have he : 1< Real.exp ((1+eps)*tau) := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hz
  have hsec := singleton_rent_of_growth_ratio hbv (div_pos htau ha) hqL he
    hopt hgrowth
  have hsecA : tau/(Real.exp ((1+eps)*tau)-1)≤ a*(v-b) := by
    have hh := mul_le_mul_of_nonneg_left hsec ha.le
    convert! hh using 1; field_simp [ha.ne']
  have hexp := (exponential_secant_bounds hz hsmall).1
  have heps1 : 0<1+eps := by positivity
  have hlow : (1-(1+eps)*tau)/(1+eps)≤
      tau/(Real.exp ((1+eps)*tau)-1) := by
    have hdiv := div_le_div_of_nonneg_right hexp heps1.le
    convert! hdiv using 1;
      field_simp [heps1.ne',(sub_pos.mpr he).ne']
  have hsimple : 1-eps-(1+eps)*tau≤(1-(1+eps)*tau)/(1+eps) := by
    apply (le_div_iff₀ heps1).2
    nlinarith [sq_nonneg eps,mul_nonneg heps (le_of_lt htau)]
  exact hsimple.trans (hlow.trans hsecA)

theorem singleton_relative_rent
    {v b qL qR a epsilon : ℝ}
    (ha : 0< a) (hepsilon : 0< epsilon) (hepsilon1 : epsilon<1)
    (hbv : b≤ v) (hqL : 0< qL)
    (hopt : (v-(b-(epsilon/4)/a))*qL≤(v-b)*qR)
    (hgrowth : qR≤ Real.exp ((1+epsilon/4)*(epsilon/4))*qL) :
    (1-epsilon)/a≤ v-b := by
  have hs : (1+epsilon/4)*(epsilon/4)<1 := by
    nlinarith [sq_nonneg (1-epsilon),mul_pos hepsilon (sub_pos.mpr hepsilon1)]
  have hr := singleton_scaled_rent ha (by positivity : 0≤ epsilon/4)
    (by positivity : 0< epsilon/4) hs hbv hqL hopt hgrowth
  have hclean : 1-epsilon≤ a*(v-b) := by
    have hsq : epsilon^2≤ epsilon := by
      nlinarith [mul_nonneg hepsilon.le (sub_nonneg.mpr hepsilon1.le)]
    nlinarith [hr,hsq]
  exact (div_le_iff₀ ha).2 (by simpa only [mul_comm] using hclean)

theorem singleton_relative_rent_of_integrated_slope
    {q : ℝ→ℝ} {v b a epsilon : ℝ}
    (ha : 0< a) (hepsilon : 0< epsilon) (hepsilon1 : epsilon<1)
    (hbv : b≤ v) (hqL : 0< q (b-(epsilon/4)/a))
    (hopt : utilityOne v (b-(epsilon/4)/a) (q (b-(epsilon/4)/a))≤
      utilityOne v b (q b))
    (hqAC : AbsolutelyContinuousOnInterval q (b-(epsilon/4)/a) b)
    (hslope : ∀ᵐ z ∂volume, z∈Icc (b-(epsilon/4)/a) b →
      deriv q z≤((1+epsilon/4)*a)*q z) :
    (1-epsilon)/a≤ v-b := by
  have hstep : 0<(epsilon/4)/a := by positivity
  have hgrowth := ac_growth_bound (show b-(epsilon/4)/a≤ b by linarith) hqAC hslope
  have he : ((1+epsilon/4)*a)*(b-(b-(epsilon/4)/a))=
      (1+epsilon/4)*(epsilon/4) := by
    field_simp [ha.ne']
    ring
  rw [he] at hgrowth
  exact singleton_relative_rent ha hepsilon hepsilon1 hbv hqL hopt hgrowth

theorem positive_singleton_utility_implies_underbid {v b q : ℝ}
    (hq : 0≤ q) (hu : 0< utilityOne v b q) : b< v := by
  unfold utilityOne at hu
  by_contra hh
  have hb : v≤ b := le_of_not_gt hh
  have hnonpos := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hb) hq
  exact (not_lt_of_ge hnonpos) hu

theorem eventually_strict_route_gap
    {eta : ℝ} {v b q d a rentErr dupBudget : ℕ→ℝ} {limitBudget : ℝ}
    (hlimit : limitBudget<1)
    (hrentErr : Tendsto rentErr atTop (𝓝 0))
    (hdupBudget : Tendsto dupBudget atTop (𝓝 limitBudget))
    (hdupRatio : Tendsto (fun m => d m/q m) atTop (𝓝 0))
    (hfinite : ∀ᶠ m in atTop,
      0< a m ∧ 0< q m ∧ 0≤ d m ∧ d m≤ q m ∧ rentErr m≤ 1 ∧
      (1-rentErr m)/a m≤ v m-b m ∧
      eta*b m*d m≤ dupBudget m*q m/a m) :
    ∀ᶠ m in atTop,
      utilityOne (v m) (b m) (q m) <
        utilityTwo eta (v m) (b m) (q m) (d m) := by
  have hmargin : Tendsto
      (fun m => (1-rentErr m)*(1-d m/q m)-dupBudget m)
      atTop (𝓝 (1-limitBudget)) := by
    convert ((tendsto_const_nhds.sub hrentErr).mul
      (tendsto_const_nhds.sub hdupRatio)).sub hdupBudget using 1; norm_num
  have hpos : ∀ᶠ m in atTop,
      0<(1-rentErr m)*(1-d m/q m)-dupBudget m :=
    hmargin.eventually (Ioi_mem_nhds (by linarith : 0<1-limitBudget))
  filter_upwards [hfinite,hpos] with m hm hp
  rcases hm with ⟨ha,hq,hd,hdq,he,hr,hdup⟩
  exact strict_route_gap_from_relative_rent ha hq hd hdq he hr hdup hp

end FCAppendix.Affine.Uniform07Finishing.Crossover
