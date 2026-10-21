import FCAppendix.Affine.Uniform07Finishing.Crossover.Algebra
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover
open Set MeasureTheory Filter Topology

theorem exists_first_used_to_right {S : Set ℝ} (hS : IsClosed S)
    {x b : ℝ} (hxb : x≤ b) (hx : x∉S) (hb : b∈S) :
    ∃ y, x< y ∧ y≤ b ∧ y∈S ∧ ∀ z∈Ioo x y, z∉S := by
  let K : Set ℝ := Icc x b ∩ S
  have hK : IsCompact K := isCompact_Icc.inter_right hS
  have hne : K.Nonempty := ⟨b,⟨⟨hxb,le_rfl⟩,hb⟩⟩
  obtain ⟨y,hy⟩ := hK.exists_isLeast hne
  have hxy : x< y := by
    have hle : x≤ y := hy.1.1.1
    refine lt_of_le_of_ne hle ?_
    intro he
    exact hx (he.symm ▸ hy.1.2)
  refine ⟨y,hxy,hy.1.1.2,hy.1.2,?_⟩
  intro z hz hzS
  have hzy : y≤ z := hy.2 ⟨⟨hz.1.le,hz.2.le.trans hy.1.1.2⟩,hzS⟩
  exact (not_le_of_gt hz.2) hzy

theorem negative_segment_has_no_gaps
    {S : Set ℝ} (hS : IsClosed S) {F : ℝ→ℝ} {a b upper : ℝ}
    (_hab : a≤ b) (hb : b∈S)
    (hnegative : ∀ y∈Ioc a b, F y< upper)
    (hreset : ∀ x y, a≤ x → x< y → y≤ b → y∈S →
      (∀ z∈Ioo x y, z∉S) → upper< F y) :
    Icc a b ⊆ S := by
  intro x hx
  by_contra hxS
  obtain ⟨y,hxy,hyb,hyS,hgap⟩ :=
    exists_first_used_to_right hS hx.2 hxS hb
  have hlow := hnegative y ⟨hx.1.trans_lt hxy,hyb⟩
  have hhigh := hreset x y hx.1 hxy hyb hyS hgap
  exact (not_lt_of_ge hlow.le) hhigh

theorem exists_closed_support_descending_band
    {S : Set ℝ} (hS : IsClosed S) {F : ℝ→ℝ}
    {L b lower upper : ℝ} (hLb : L≤ b)
    (hF : ContinuousOn F (Icc L b)) (hb : b∈S)
    (hstart : upper≤ F L) (hend : F b≤ lower) (hlevels : lower< upper)
    (hreset : ∀ x y, L≤ x → x< y → y≤ b → y∈S →
      (∀ z∈Ioo x y, z∉S) → upper< F y) :
    ∃ a c, L≤ a ∧ a< c ∧ c≤ b ∧ Icc a c ⊆ S ∧
      F a=upper ∧ F c=lower ∧ ∀ x∈Icc a c, F x∈Icc lower upper := by
  let U : Set ℝ := {x∈Icc L b | F x=upper}
  have hUclosed : IsClosed U :=
    isClosed_Icc.isClosed_eq hF continuousOn_const
  have hUcompact : IsCompact U :=
    isCompact_Icc.of_isClosed_subset hUclosed (fun _ hx => hx.1)
  have hUne : U.Nonempty := by
    obtain ⟨x,hx,hFx⟩ := (intermediate_value_Icc' hLb hF)
      ⟨hend.trans hlevels.le,hstart⟩
    exact ⟨x,hx,hFx⟩
  obtain ⟨a,ha⟩ := hUcompact.exists_isGreatest hUne
  have hLa : L≤ a := ha.1.1.1
  have hab : a≤ b := ha.1.1.2
  have hFa : F a=upper := ha.1.2
  have hablt : a< b := by
    refine lt_of_le_of_ne hab ?_
    intro he
    have hh : F b=upper := he ▸ hFa
    linarith
  have hnegative : ∀ x∈Ioc a b, F x< upper := by
    intro x hx
    by_contra hh
    have hxF : upper≤ F x := le_of_not_gt hh
    have hFx : ContinuousOn F (Icc x b) := hF.mono
      (fun y hy => ⟨hLa.trans (hx.1.le.trans hy.1),hy.2⟩)
    obtain ⟨y,hy,hFy⟩ := (intermediate_value_Icc' hx.2 hFx)
      ⟨hend.trans hlevels.le,hxF⟩
    have hya : y≤ a := ha.2 ⟨⟨hLa.trans (hx.1.le.trans hy.1),hy.2⟩,hFy⟩
    linarith [hy.1,hx.1]
  have habS : Icc a b ⊆ S := negative_segment_has_no_gaps hS hab hb hnegative
    (fun x y hax hxy hyb hyS hgap =>
      hreset x y (hLa.trans hax) hxy hyb hyS hgap)
  have hFab : ContinuousOn F (Icc a b) := hF.mono
    (fun x hx => ⟨hLa.trans hx.1,hx.2⟩)
  let D : Set ℝ := {x∈Icc a b | F x=lower}
  have hDclosed : IsClosed D :=
    isClosed_Icc.isClosed_eq hFab continuousOn_const
  have hDcompact : IsCompact D :=
    isCompact_Icc.of_isClosed_subset hDclosed (fun _ hx => hx.1)
  have hDne : D.Nonempty := by
    obtain ⟨x,hx,hFx⟩ := (intermediate_value_Icc' hab hFab)
      ⟨hend,by rw [hFa]; exact hlevels.le⟩
    exact ⟨x,hx,hFx⟩
  obtain ⟨c,hc⟩ := hDcompact.exists_isLeast hDne
  have hac : a< c := by
    refine lt_of_le_of_ne hc.1.1.1 ?_
    intro he
    have hh : F a=lower := he.symm ▸ hc.1.2
    linarith [hFa,hlevels]
  refine ⟨a,c,hLa,hac,hc.1.1.2,
    fun x hx => habS ⟨hx.1,hx.2.trans hc.1.1.2⟩,
    hFa,hc.1.2,?_⟩
  intro x hx
  constructor
  · by_contra hh
    have hxF : F x< lower := lt_of_not_ge hh
    have hxc : x< c := by
      refine lt_of_le_of_ne hx.2 ?_
      intro he
      have hh' : F x=lower := he.symm ▸ hc.1.2
      linarith
    have hFax : ContinuousOn F (Icc a x) := hFab.mono
      (fun y hy => ⟨hy.1,hy.2.trans (hx.2.trans hc.1.1.2)⟩)
    obtain ⟨y,hy,hFy⟩ := (intermediate_value_Icc' hx.1 hFax)
      ⟨hxF.le,by rw [hFa]; exact hlevels.le⟩
    have hcy : c≤ y := hc.2 ⟨⟨hy.1,hy.2.trans (hx.2.trans hc.1.1.2)⟩,hFy⟩
    linarith [hy.2]
  · by_cases hxa : x=a
    · simp [hxa,hFa]
    · exact (hnegative x
        ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa),hx.2.trans hc.1.1.2⟩).le

theorem ac_increment_lower {f : ℝ→ℝ} {a b k : ℝ}
    (hab : a≤ b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hder : ∀ᵐ x ∂volume.restrict (Icc a b), k≤ deriv f x) :
    k*(b-a)≤ f b-f a := by
  have hi := intervalIntegral.integral_mono_ae_restrict hab
    (show IntervalIntegrable (fun _ : ℝ => k) volume a b from intervalIntegrable_const)
    hf.intervalIntegrable_deriv hder
  rw [hf.integral_deriv_eq_sub] at hi
  simpa only [intervalIntegral.integral_const,smul_eq_mul,mul_comm] using hi

theorem ac_increment_upper {f : ℝ→ℝ} {a b k : ℝ}
    (hab : a≤ b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hder : ∀ᵐ x ∂volume.restrict (Icc a b), deriv f x≤ k) :
    f b-f a≤ k*(b-a) := by
  have hi := intervalIntegral.integral_mono_ae_restrict hab
    hf.intervalIntegrable_deriv
    (show IntervalIntegrable (fun _ : ℝ => k) volume a b from intervalIntegrable_const) hder
  rw [hf.integral_deriv_eq_sub] at hi
  simpa only [intervalIntegral.integral_const,smul_eq_mul,mul_comm] using hi

theorem finite_closed_support_barrier
    {S : Set ℝ} {delta T weight H : ℝ→ℝ}
    {L R m eps mu K k err omega : ℝ}
    (hS : IsClosed S) (hLR : L≤ R)
    (hm : 0< m) (heps : 0< eps) (hmu : 0< mu)
    (hk : 0≤ k) (homega : 0≤ omega)
    (hF : ContinuousOn (fun x => delta x-T x) (Icc L R))
    (hDeltaAC : AbsolutelyContinuousOnInterval delta L R)
    (hWeightAC : AbsolutelyContinuousOnInterval weight L R)
    (hstart : -eps/(2*m)≤ delta L-T L)
    (hreset : ∀ x y, L≤ x → x< y → y≤ R → y∈S →
      (∀ z∈Ioo x y, z∉S) → -eps/(2*m)< delta y-T y)
    (hbandBounds : ∀ x∈Icc L R, x∈S →
      delta x-T x∈Icc (-eps/m) (-eps/(2*m)) →
      0≤ delta x ∧ delta x≤ K/m)
    (hbandDeriv : ∀ᵐ x ∂volume, x∈Icc L R → x∈S →
      delta x-T x∈Icc (-eps/m) (-eps/(2*m)) →
      mu≤ deriv delta x ∧ deriv weight x≤ 0)
    (hweight : ∀ x∈Icc L R, weight x∈Icc (0:ℝ) 1)
    (hHpos : ∀ x∈Icc L R, 0≤ H x)
    (hlead : ∀ x∈Icc L R,
      |m*T x-(1+k*weight x)*H x|≤ err)
    (hmodulus : ∀ a∈Icc L R, ∀ b∈Icc L R,
      a≤ b → b-a≤ K/(mu*m) → |H b-H a|≤ omega)
    (hsmall : (1+k)*omega+2*err< eps/2) :
    ∀ b∈Icc L R, b∈S → T b-eps/m< delta b := by
  intro b hb hbS
  by_contra hbad
  have hend : delta b-T b≤-eps/m := by
    simp only [neg_div]
    linarith [le_of_not_gt hbad]
  have hlevels : -eps/m< -eps/(2*m) := by
    have hh : 0< eps/(2*m) := by positivity
    have he : eps/m=2*(eps/(2*m)) := by ring
    simp only [neg_div]
    linarith
  have hFb : ContinuousOn (fun x => delta x-T x) (Icc L b) :=
    hF.mono (fun x hx => ⟨hx.1,hx.2.trans hb.2⟩)
  obtain ⟨a,c,hLa,hac,hcb,hused,hFa,hFc,hband⟩ :=
    exists_closed_support_descending_band hS hb.1 hFb hbS hstart hend hlevels
      (fun x y hLx hxy hyb hyS hgap =>
        hreset x y hLx hxy (hyb.trans hb.2) hyS hgap)
  have haLR : a∈Icc L R := ⟨hLa,hac.le.trans (hcb.trans hb.2)⟩
  have hcLR : c∈Icc L R := ⟨hLa.trans hac.le,hcb.trans hb.2⟩
  have hsub : Icc a c ⊆ Icc L R := fun x hx =>
    ⟨hLa.trans hx.1,hx.2.trans hcLR.2⟩
  have huSub : uIcc a c ⊆ uIcc L R := by
    simpa only [uIcc_of_le hac.le,uIcc_of_le hLR] using hsub
  have hdAC := hDeltaAC.mono huSub
  have hwAC := hWeightAC.mono huSub
  have hdder : ∀ᵐ x ∂volume.restrict (Icc a c), mu≤ deriv delta x := by
    apply (ae_restrict_iff' measurableSet_Icc).2
    filter_upwards [hbandDeriv] with x hx hxc
    exact (hx (hsub hxc) (hused hxc) (hband x hxc)).1
  have hwder : ∀ᵐ x ∂volume.restrict (Icc a c), deriv weight x≤ 0 := by
    apply (ae_restrict_iff' measurableSet_Icc).2
    filter_upwards [hbandDeriv] with x hx hxc
    exact (hx (hsub hxc) (hused hxc) (hband x hxc)).2
  have hinc := ac_increment_lower hac.le hdAC hdder
  have hwinc := ac_increment_upper hac.le hwAC hwder
  have hwca : weight c≤ weight a := by simpa using hwinc
  have hDa := hbandBounds a haLR (hused ⟨le_rfl,hac.le⟩)
    (hband a ⟨le_rfl,hac.le⟩)
  have hDc := hbandBounds c hcLR (hused ⟨hac.le,le_rfl⟩)
    (hband c ⟨hac.le,le_rfl⟩)
  have hlength : c-a≤ K/(mu*m) := by
    apply (le_div_iff₀ (mul_pos hmu hm)).2
    have hh : mu*(c-a)≤ K/m := by linarith
    have hm' := (le_div_iff₀ hm).mp hh
    nlinarith
  have hHdiff := (abs_le.mp (hmodulus a haLR c hcLR hac.le hlength)).2
  have hwa := hweight a haLR
  have hHc := hHpos c hcLR
  have hcoeff0 : 0≤ 1+k*weight a := by nlinarith [mul_nonneg hk hwa.1]
  have hcoeff1 : 1+k*weight a≤ 1+k := by
    nlinarith [mul_nonneg hk (sub_nonneg.mpr hwa.2)]
  have hprod1 := mul_le_mul_of_nonneg_left hHdiff hcoeff0
  have hprod2 := mul_le_mul_of_nonneg_right hcoeff1 homega
  have hresetTerm : k*(weight c-weight a)*H c≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hk (sub_nonpos.mpr hwca)) hHc
  have hleadingInc : (1+k*weight c)*H c-(1+k*weight a)*H a≤(1+k)*omega := by
    nlinarith [hprod1,hprod2,hresetTerm]
  have hTa := (abs_le.mp (hlead a haLR)).1
  have hTc := (abs_le.mp (hlead c hcLR)).2
  have hTinc : m*(T c-T a)< eps/2 := by
    nlinarith [hleadingInc,hTa,hTc,hsmall]
  have hDinc0 : 0≤ delta c-delta a :=
    (mul_nonneg hmu.le (sub_nonneg.mpr hac.le)).trans hinc
  have hma : m*(delta a-T a) = -eps/2 := by
    rw [hFa]
    field_simp [hm.ne']
  have hmc : m*(delta c-T c) = -eps := by
    rw [hFc]
    field_simp [hm.ne']
  nlinarith [mul_nonneg hm.le hDinc0,hma,hmc,hTinc]

theorem eventually_shrinking_interval_modulus
    {H : ℝ→ℝ} {S : Set ℝ} {K mu : ℝ}
    (hH : UniformContinuousOn H S) (_hK : 0≤ K) (hmu : 0< mu) :
    ∀ omega>0, ∀ᶠ m : ℕ in atTop,
      ∀ a∈S, ∀ b∈S, a≤ b → b-a≤ K/(mu*(m:ℝ)) →
        |H b-H a|< omega := by
  intro omega homega
  obtain ⟨d,hd,hcontrol⟩ := Metric.uniformContinuousOn_iff.mp hH omega homega
  obtain ⟨N,hN⟩ := exists_nat_gt (K/(mu*d))
  filter_upwards [eventually_ge_atTop (N+1)] with m hmN
  have hm0 : 0<(m:ℝ) := by exact_mod_cast (show 0< m by omega)
  have hNm : (N:ℝ)< m := by exact_mod_cast (show N< m by omega)
  have hsize : K/(mu*d)< m := hN.trans hNm
  have hKsmall : K< mu*d*m := by
    simpa only [mul_comm] using (div_lt_iff₀ (mul_pos hmu hd)).mp hsize
  have hwidth : K/(mu*(m:ℝ))< d := by
    apply (div_lt_iff₀ (mul_pos hmu hm0)).2
    nlinarith [hKsmall]
  intro a ha b hb hab hdist
  have hdist' : dist b a< d := by
    rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hab)]
    exact hdist.trans_lt hwidth
  simpa only [Real.dist_eq] using hcontrol b hb a ha hdist'

theorem eventually_closed_support_barrier
    {S : ℕ→ Set ℝ} {delta T weight : ℕ→ℝ→ℝ} {H : ℝ→ℝ}
    {error : ℕ→ℝ} {L R mu K k : ℝ}
    (hLR : L≤ R) (hmu : 0< mu) (hK : 0≤ K) (hk : 0≤ k)
    (hH : UniformContinuousOn H (Icc L R))
    (hHpos : ∀ x∈Icc L R, 0≤ H x)
    (herror : Tendsto error atTop (𝓝 0))
    (hbasic : ∀ᶠ m : ℕ in atTop,
      IsClosed (S m) ∧
      ContinuousOn (fun x => delta m x-T m x) (Icc L R) ∧
      AbsolutelyContinuousOnInterval (delta m) L R ∧
      AbsolutelyContinuousOnInterval (weight m) L R ∧
      (∀ x∈Icc L R, weight m x∈Icc (0:ℝ) 1) ∧
      (∀ x∈Icc L R,
        |(m:ℝ)*T m x-(1+k*weight m x)*H x|≤ error m))
    (hstartReset : ∀ eps>0, ∀ᶠ m : ℕ in atTop,
      -eps/(2*(m:ℝ))≤ delta m L-T m L ∧
      (∀ x y, L≤ x → x< y → y≤ R → y∈S m →
        (∀ z∈Ioo x y, z∉S m) →
        -eps/(2*(m:ℝ))< delta m y-T m y))
    (hband : ∀ eps>0, ∀ᶠ m : ℕ in atTop,
      (∀ x∈Icc L R, x∈S m →
        delta m x-T m x∈Icc (-eps/(m:ℝ)) (-eps/(2*(m:ℝ))) →
        0≤ delta m x ∧ delta m x≤ K/(m:ℝ)) ∧
      (∀ᵐ x ∂volume, x∈Icc L R → x∈S m →
        delta m x-T m x∈Icc (-eps/(m:ℝ)) (-eps/(2*(m:ℝ))) →
        mu≤ deriv (delta m) x ∧ deriv (weight m) x≤ 0)) :
    ∀ eps>0, ∀ᶠ m : ℕ in atTop,
      ∀ b∈Icc L R, b∈S m → T m b-eps/(m:ℝ)< delta m b := by
  intro eps heps
  let omega : ℝ := eps/(8*(1+k))
  have hk1 : 0<1+k := by positivity
  have homega : 0< omega := by dsimp [omega]; positivity
  have hmod := eventually_shrinking_interval_modulus hH hK hmu omega homega
  have hevent : ∀ᶠ m : ℕ in atTop, error m< eps/16 :=
    herror.eventually (Iio_mem_nhds (by positivity : (0:ℝ)< eps/16))
  filter_upwards [hbasic,hstartReset eps heps,hband eps heps,
    hmod,hevent,eventually_ge_atTop 1] with m hm hs hb hw he hm1
  rcases hm with ⟨hS,hF,hD,hW,hrange,hlead⟩
  have hmpos : 0<(m:ℝ) := by exact_mod_cast (show 0< m by omega)
  apply finite_closed_support_barrier hS hLR hmpos heps hmu hk homega.le
    hF hD hW hs.1 hs.2 hb.1 hb.2 hrange hHpos hlead
  · intro a ha b hb hab hdist
    exact (hw a ha b hb hab hdist).le
  · have hcalc : (1+k)*omega=eps/8 := by
      dsimp [omega]
      field_simp [hk1.ne']
    linarith [hcalc]

end FCAppendix.Affine.Uniform07Finishing.Crossover
