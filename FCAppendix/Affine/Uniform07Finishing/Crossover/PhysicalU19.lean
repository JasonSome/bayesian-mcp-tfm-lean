import FCAppendix.Affine.Uniform07Finishing.Crossover.PhysicalErrors

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover
open Set Filter Topology

theorem canonical_share_bounds {p C : ℝ} (hp : 0≤ p) (hC : 0< C) :
    0< p+C ∧ C/(p+C)∈Icc (0:ℝ) 1 := by
  have hq : 0< p+C := add_pos_of_nonneg_of_pos hp hC
  exact ⟨hq,div_nonneg hC.le hq.le,(div_le_one hq).2 (by linarith)⟩

theorem canonical_ratio_to_share_error
    {p C D' xi b e : ℝ} (hp : 0≤ p) (hC : 0< C)
    (hxi : xi≠0) (hb : b≠0)
    (herror : |D'/C-2/(xi*b)|≤ e) :
    |D'/(p+C)-2*(C/(p+C))/(xi*b)|≤ e := by
  have hshare := canonical_share_bounds hp hC
  have he : 0≤ e := (abs_nonneg _).trans herror
  have hid : D'/(p+C)-2*(C/(p+C))/(xi*b)=
      (C/(p+C))*(D'/C-2/(xi*b)) := by
    field_simp [hshare.1.ne',hC.ne',hxi,hb]
  rw [hid,abs_mul,abs_of_nonneg hshare.2.1]
  have h₁ := mul_le_mul_of_nonneg_left herror hshare.2.1
  have h₂ := mul_le_mul_of_nonneg_right hshare.2.2 he
  nlinarith

theorem canonical_ratio_bound_to_total
    {p C D D' m Rmax Dmax : ℝ} (hp : 0≤ p) (hC : 0< C)
    (hm : 0< m) (hRmax : 0≤ Rmax) (hDmax : 0≤ Dmax)
    (hD : D∈Icc (0:ℝ) (Rmax*C/m))
    (hD' : D'∈Icc (0:ℝ) (Dmax*C)) :
    |D/(p+C)|≤ Rmax/m ∧ |D'/(p+C)|≤ Dmax := by
  have hq := (canonical_share_bounds hp hC).1
  constructor
  · rw [abs_of_nonneg (div_nonneg hD.1 hq.le)]
    apply (div_le_iff₀ hq).2
    have h := mul_le_mul_of_nonneg_left (show C≤ p+C by linarith)
      (div_nonneg hRmax hm.le)
    calc
      D ≤ Rmax*C/m := hD.2
      _ = Rmax/m*C := by ring
      _ ≤ Rmax/m*(p+C) := h
  · rw [abs_of_nonneg (div_nonneg hD'.1 hq.le)]
    apply (div_le_iff₀ hq).2
    exact hD'.2.trans (mul_le_mul_of_nonneg_left (by linarith : C≤ p+C) hDmax)

theorem normalized_U19_denominator
    {a A m s Amin e Dmax : ℝ}
    (hm : 0< m) (hA : Amin≤ A) (ha : |a/m-A|≤ e)
    (he : e≤ Amin/4) (hs : s≤ Dmax) (hsize : Dmax/m≤ Amin/2) :
    Amin≤ 2*(a/m)-s/m := by
  have helo := (abs_le.mp ha).1
  have hs' := div_le_div_of_nonneg_right hs hm.le
  linarith

theorem U19_denominator_order
    {a p C D' m Amin Dmax : ℝ}
    (hm : 0< m) (hAmin : 0< Amin) (hp : 0≤ p) (hC : 0< C)
    (ha : Amin*m≤ a) (hD' : D'≤ Dmax*C) (hsize : Dmax≤ Amin*m) :
    0<2*a*C-D' ∧
      2*a*C-D'≤ barrierDenominator a (p+C) D' ∧
      Amin*m*(p+C)≤ barrierDenominator a (p+C) D' := by
  have ha0 : 0< a := (mul_pos hAmin hm).trans_le ha
  have hD'a : D'≤ a*C := hD'.trans
    (mul_le_mul_of_nonneg_right (hsize.trans ha) hC.le)
  have hq : 0< p+C := add_pos_of_nonneg_of_pos hp hC
  have hD'q : D'≤ a*(p+C) := hD'a.trans
    (mul_le_mul_of_nonneg_left (by linarith : C≤ p+C) ha0.le)
  unfold barrierDenominator
  refine ⟨by nlinarith [mul_pos ha0 hC],?_,?_⟩
  · nlinarith [mul_nonneg ha0.le hp]
  · have h := mul_le_mul_of_nonneg_right ha hq.le
    nlinarith

theorem U23_leading_bounds
    {eta xi x A Amin Amax : ℝ}
    (heta : 0≤ eta) (hxi : 0< xi) (hx : x∈Icc (0:ℝ) 1)
    (hAmin : 0< Amin) (hA : A∈Icc Amin Amax) :
    1/Amax≤(1+(eta/xi)*x)/A ∧
      |(1+(eta/xi)*x)/A|≤(1+eta/xi)/Amin := by
  have hAp : 0< A := hAmin.trans_le hA.1
  have hAmax : 0< Amax := hAp.trans_le hA.2
  have hk : 0≤ eta/xi := div_nonneg heta hxi.le
  have hnumlo : 1≤ 1+(eta/xi)*x := by nlinarith [mul_nonneg hk hx.1]
  have hnumhi : 1+(eta/xi)*x≤ 1+eta/xi := by
    nlinarith [mul_nonneg hk (sub_nonneg.mpr hx.2)]
  have hnumpos : 0≤ 1+(eta/xi)*x := by positivity
  constructor
  · exact (one_div_le_one_div_of_le hAp hA.2).trans
      (div_le_div_of_nonneg_right hnumlo hAp.le)
  · rw [abs_of_nonneg (div_nonneg hnumpos hAp.le)]
    exact (div_le_div_of_nonneg_right hnumhi hAp.le).trans
      (div_le_div_of_nonneg_left (by positivity) hAmin hA.1)

theorem finite_U23_from_U19
    {eta xi b m p C a A D D' Amin Amax Rmax Dmax e : ℝ}
    (heta : eta∈Icc (0:ℝ) 1) (hxi : 0< xi)
    (hb : b∈Ioc (0:ℝ) 1) (hm : 0< m)
    (hp : 0≤ p) (hC : 0< C) (hAmin : 0< Amin)
    (hA : A∈Icc Amin Amax) (he : 0≤ e) (heSmall : e≤ Amin/4)
    (ha : |a/m-A|≤ e)
    (hRmax : 0≤ Rmax) (hDmax : 0≤ Dmax)
    (hD : D∈Icc (0:ℝ) (Rmax*C/m))
    (hD' : D'∈Icc (0:ℝ) (Dmax*C))
    (hDerror : |D'/C-2/(xi*b)|≤ e)
    (hsize : Dmax/m≤ Amin/2) :
    0< barrierDenominator a (p+C) D' ∧
      |m*barrier eta b a (p+C) D D'-
        (1+(eta/xi)*(C/(p+C)))/A|≤
      ((Rmax+((1+eta/xi)/Amin)*Dmax)/m+
        (eta+2*((1+eta/xi)/Amin))*e)/Amin := by
  let q := p+C
  let lead := (1+(eta/xi)*(C/q))/A
  let Lmax := (1+eta/xi)/Amin
  have hLmax : 0 ≤ Lmax := by
    dsimp only [Lmax]
    exact div_nonneg (by linarith [div_nonneg heta.1 hxi.le]) hAmin.le
  have hq : 0< q := (canonical_share_bounds hp hC).1
  have hx := (canonical_share_bounds hp hC).2
  have hratio := canonical_ratio_bound_to_total hp hC hm hRmax hDmax hD hD'
  have hratioD := canonical_ratio_to_share_error hp hC hxi.ne' hb.1.ne' hDerror
  have hlead := (U23_leading_bounds heta.1 hxi hx hAmin hA).2
  have hK : Amin≤ 2*(a/m)-(D'/q)/m :=
    normalized_U19_denominator hm hA.1 ha heSmall
      (le_trans (le_abs_self (D'/q)) hratio.2) hsize
  have hKpos : 0<2*(a/m)-(D'/q)/m := hAmin.trans_le hK
  have hdenid : barrierDenominator a q D'=
      (2*(a/m)-(D'/q)/m)*(m*q) := by
    unfold barrierDenominator
    field_simp [hm.ne',hq.ne']
  have hden : 0< barrierDenominator a q D' := by
    rw [hdenid]
    exact mul_pos hKpos (mul_pos hm hq)
  refine ⟨hden,?_⟩
  rw [scaled_barrier_exact hq.ne' hm.ne' hden.ne']
  have hrewrite : D'/(m*q)=(D'/q)/m := by ring
  rw [hrewrite]
  have hmatch : 2*A*lead=2+eta*b*(2*(C/q)/(xi*b)) :=
    source_leading_match hxi.ne' hb.1.ne' (hAmin.trans_le hA.1).ne'
  have hres := normalized_barrier_residual_bound hm he
    (div_nonneg hRmax hm.le) he hLmax hDmax
    hmatch ha hratio.1 hratioD hlead hratio.2
  have hbound : 0 ≤ |1-eta| * (Rmax/m)+|eta*b| * e+2*Lmax*e+Lmax*Dmax/m := by
    positivity
  have heq := normalized_quotient_error hAmin hK hbound hres
  have hcoeff : |1-eta|≤ 1 := by rw [abs_of_nonneg (sub_nonneg.mpr heta.2)]; linarith [heta.1]
  have hetab : |eta*b|≤ eta := by
    rw [abs_of_nonneg (mul_nonneg heta.1 hb.1.le)]
    nlinarith [mul_nonneg heta.1 (sub_nonneg.mpr hb.2)]
  have h₁ := mul_le_mul_of_nonneg_right hcoeff (div_nonneg hRmax hm.le)
  have h₂ := mul_le_mul_of_nonneg_right hetab he
  have hbound' : |1-eta| * (Rmax/m)+|eta*b| * e+2*Lmax*e+Lmax*Dmax/m≤
      (Rmax+Lmax*Dmax)/m+(eta+2*Lmax)*e := by
    calc
      _ ≤ Rmax/m+eta*e+2*Lmax*e+Lmax*Dmax/m := by nlinarith [h₁,h₂]
      _ = _ := by ring
  exact heq.trans (div_le_div_of_nonneg_right hbound' hAmin.le)

theorem U23_error_tendsto_zero {e : ℕ→ℝ} (he : Tendsto e atTop (𝓝 0))
    (eta xi Amin Rmax Dmax : ℝ) :
    Tendsto (fun m : ℕ =>
      ((Rmax+((1+eta/xi)/Amin)*Dmax)/(m:ℝ)+
        (eta+2*((1+eta/xi)/Amin))*e m)/Amin) atTop (𝓝 0) := by
  have hfrac : Tendsto (fun m : ℕ =>
      (Rmax+((1+eta/xi)/Amin)*Dmax)/(m:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  simpa only [mul_zero,add_zero,zero_div] using
    (hfrac.add (he.const_mul (eta+2*((1+eta/xi)/Amin)))).div_const Amin

theorem source_leading_upper_lt_399 (row : Uniform07.Row) :
    (1+Uniform07.eta row/Uniform07.xi row)/(Uniform07.slopeRatioLower row/500)<399 := by
  have hs : 0< Uniform07.slopeRatioLower row/500 := by
    cases row
    · linarith [Uniform07.physical_slope_numerics.1]
    · linarith [Uniform07.physical_slope_numerics.2]
  apply (div_lt_iff₀ hs).2
  cases row
  · norm_num [Uniform07.eta,Uniform07.etaQ,Uniform07.xi,Uniform07.xiQ] at *
    linarith [Uniform07.physical_slope_numerics.1]
  · norm_num [Uniform07.eta,Uniform07.etaQ,Uniform07.xi,Uniform07.xiQ] at *
    linarith [Uniform07.physical_slope_numerics.2]

end FCAppendix.Affine.Uniform07Finishing.Crossover
