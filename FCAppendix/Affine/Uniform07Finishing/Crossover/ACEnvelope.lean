import FCAppendix.Affine.Uniform07Finishing.Crossover.PhysicalGaps

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover
open MeasureTheory Set Filter Topology

theorem continuous_le_on_Icc_of_ae {f g : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hg : ContinuousOn g (Icc a b))
    (hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Icc a b → f x ≤ g x) :
    ∀ x ∈ Icc a b, f x ≤ g x := by
  intro x hx
  by_contra hbad
  have hgap : 0 < f x - g x := sub_pos.mpr (lt_of_not_ge hbad)
  obtain ⟨d, hd, hball⟩ := Metric.continuousWithinAt_iff.mp
    ((hf.sub hg) x hx) ((f x-g x)/2) (half_pos hgap)
  let l := max a (x-d/2)
  let r := min b (x+d/2)
  have hlr : l < r := by
    dsimp [l,r]
    rw [lt_min_iff, max_lt_iff, max_lt_iff]
    exact ⟨⟨hab,by linarith [hx.2]⟩,⟨by linarith [hx.1],by linarith⟩⟩
  have hpositive : ∀ z ∈ Ioo l r, g z < f z := by
    intro z hz
    have hza : a ≤ z := (le_max_left _ _).trans hz.1.le
    have hzb : z ≤ b := hz.2.le.trans (min_le_left _ _)
    have hzleft : x-d/2 < z := (le_max_right _ _).trans_lt hz.1
    have hzright : z < x+d/2 := hz.2.trans_le (min_le_right _ _)
    have hdist : dist z x < d := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    have hh := hball ⟨hza,hzb⟩ hdist
    rw [Real.dist_eq, abs_lt] at hh
    simp only [Pi.sub_apply] at hh
    linarith [hh.1]
  have hz : volume (Ioo l r) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hae] with z hz hzlr
    have hzI : z ∈ Icc a b :=
      ⟨(le_max_left _ _).trans hzlr.1.le,hzlr.2.le.trans (min_le_left _ _)⟩
    exact (not_lt_of_ge (hz hzI)) (hpositive z hzlr)
  have hp : 0 < volume (Ioo l r) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hlr)
  exact hp.ne' hz

theorem ac_right_comparison_derivative_envelope
    {f H : ℝ → ℝ} {x y K : ℝ}
    (hxy : x < y) (hf : AbsolutelyContinuousOnInterval f x y)
    (hH : ContinuousOn H (Icc x y))
    (hmax : ∀ z ∈ Ioo x y, f z ≤ f y + K*(y-z))
    (hder : ∀ᵐ z ∂(volume : Measure ℝ), z ∈ Ioo x y → deriv f z ≤ H z) :
    -K ≤ H y := by
  by_contra hbad
  have hneg : H y+K < 0 := by linarith [lt_of_not_ge hbad]
  let eps : ℝ := -(H y+K)/2
  have heps : 0 < eps := by dsimp [eps]; linarith
  obtain ⟨d, hd, hball⟩ := Metric.continuousWithinAt_iff.mp
    (hH y ⟨hxy.le,le_rfl⟩) eps heps
  let step := min ((y-x)/2) (d/2)
  let z := y-step
  have hs : 0 < step := by dsimp [step]; positivity
  have hsxy : step ≤ (y-x)/2 := min_le_left _ _
  have hsd : step ≤ d/2 := min_le_right _ _
  have hzxy : z ∈ Ioo x y := by dsimp [z]; constructor <;> linarith
  have hsub : uIcc z y ⊆ uIcc x y := by
    rw [uIcc_of_le hzxy.2.le,uIcc_of_le hxy.le]
    exact fun u hu => ⟨hzxy.1.le.trans hu.1,hu.2⟩
  have hhy : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ y :=
    measure_eq_zero_iff_ae_notMem.mp (measure_singleton y)
  have hupper : ∀ᵐ u ∂volume.restrict (Icc z y), deriv f u ≤ H y+eps := by
    apply (ae_restrict_iff' measurableSet_Icc).2
    filter_upwards [hder,hhy] with u hu hne huy
    have huI : u ∈ Ioo x y :=
      ⟨hzxy.1.trans_le huy.1,lt_of_le_of_ne huy.2 hne⟩
    have hdist : dist u y < d := by
      rw [Real.dist_eq,abs_lt]
      dsimp [z] at huy
      constructor <;> linarith [huy.1,huy.2]
    have hh := hball ⟨huI.1.le,huI.2.le⟩ hdist
    rw [Real.dist_eq,abs_lt] at hh
    exact (hu huI).trans (by linarith [hh.2])
  have hi := ac_increment_upper hzxy.2.le (hf.mono hsub) hupper
  have ho := hmax z hzxy
  have hc : H y+eps+K < 0 := by dsimp [eps]; linarith
  have hp := mul_neg_of_neg_of_pos hc (sub_pos.mpr hzxy.2)
  nlinarith

theorem canonical_gap_continuous_envelope
    {eta xi b delta q C D Cp Dp m A Rmax e19 : ℝ}
    (heta : eta ∈ Icc (0:ℝ) 1) (hxi : 0 < xi)
    (hb : b ∈ Ioc (0:ℝ) 1) (hdelta : 0 ≤ delta)
    (hm : 0 < m) (hA : 0 < A) (he19 : 0 ≤ e19)
    (hq : 0 < q) (hC : 0 < C) (hCq : C ≤ q)
    (hRmax : 0 ≤ Rmax) (hD0 : 0 ≤ D) (hD : D ≤ Rmax*C/m)
    (hCp : Cp ≤ m*(A+e19)*C) (hDp0 : 0 ≤ Dp)
    (hDp : |Dp/C-2/(xi*b)| ≤ e19) :
    delta*(2*Cp-Dp)-barrierNumerator eta b q D Dp ≤
      q*(2*m*(A+e19)*delta-2*(1+(eta/xi)*(C/q))+Rmax/m+e19) := by
  have hc1 := mul_le_mul_of_nonneg_left hCp (by positivity : 0 ≤ 2*delta)
  have hc2 := mul_le_mul_of_nonneg_left hCq (by positivity : 0 ≤ 2*m*(A+e19)*delta)
  have hc3 := mul_nonneg hdelta hDp0
  have hd1 : (1-eta)*D ≤ D := by nlinarith [mul_nonneg heta.1 hD0]
  have hd2 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hCq hRmax) hm.le
  have hdp := mul_le_mul_of_nonneg_right (abs_le.mp hDp).1 hC.le
  have hcancel : (Dp/C)*C=Dp := div_mul_cancel₀ _ hC.ne'
  rw [sub_mul,hcancel] at hdp
  have hdp' := mul_le_mul_of_nonneg_left hdp (mul_nonneg heta.1 hb.1.le)
  have hcancel' : eta*b*(2/(xi*b)*C)=2*(eta/xi)*C := by
    field_simp [hxi.ne',hb.1.ne']
  have he1 : eta*b ≤ 1 :=
    (mul_le_mul heta.2 hb.2 hb.1.le (by norm_num)).trans (by norm_num)
  have he2 := mul_le_mul_of_nonneg_right he1 (mul_nonneg he19 hC.le)
  have he3 := mul_le_mul_of_nonneg_left hCq he19
  have hshare : q*((eta/xi)*(C/q))=(eta/xi)*C := by
    field_simp [hq.ne']
  have hdq : Rmax*q/m=q*(Rmax/m) := by ring
  dsimp [barrierNumerator]
  nlinarith [hcancel',hshare,hdq]

theorem leading_gap_reset_algebra
    {m A Amin k theta e loss delta : ℝ}
    (hm : 0 < m) (hAmin : 0 < Amin) (hA : Amin ≤ A)
    (hk : 0 ≤ k) (htheta : theta ∈ Icc (0:ℝ) 1)
    (he : 0 ≤ e) (hloss : 0 ≤ loss) (_hdelta : 0 ≤ delta)
    (henvelope : 0 ≤ 2*m*(A+e)*delta-2*(1+k*theta)+loss) :
    (1+k*theta)/(m*A)-
        ((1+k)*e/Amin^2+loss/(2*Amin))/m ≤ delta := by
  have hApos : 0 < A := hAmin.trans_le hA
  have hAe : 0 < A+e := by positivity
  have htheta0 : 0 ≤ 1+k*theta := by
    linarith [mul_nonneg hk htheta.1]
  have htheta1 : 1+k*theta ≤ 1+k := by
    linarith [mul_le_mul_of_nonneg_left htheta.2 hk]
  have hδ : (1+k*theta)/(m*(A+e))-loss/(2*m*(A+e)) ≤ delta := by
    have hmain : (2*(1+k*theta)-loss)/(2*m*(A+e)) ≤ delta :=
      (div_le_iff₀ (by positivity : 0 < 2*m*(A+e))).2 (by nlinarith)
    have hid : (1+k*theta)/(m*(A+e))-loss/(2*m*(A+e)) =
        (2*(1+k*theta)-loss)/(2*m*(A+e)) := by
      field_simp [hm.ne',hAe.ne']
    rw [hid]
    exact hmain
  have hden : Amin^2 ≤ A*(A+e) := by
    simpa only [pow_two] using
      mul_le_mul hA (show Amin ≤ A+e by linarith) hAmin.le hApos.le
  have hdiff : (1+k*theta)/(m*A)-(1+k*theta)/(m*(A+e))=
      (1+k*theta)*e/(m*(A*(A+e))) := by
    field_simp [hm.ne',hApos.ne',hAe.ne']
    ring
  have hdiffbound : (1+k*theta)*e/(m*(A*(A+e))) ≤ ((1+k)*e/Amin^2)/m := by
    calc
      _ ≤ (1+k)*e/(m*(A*(A+e))) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right htheta1 he) (by positivity)
      _ ≤ (1+k)*e/(m*Amin^2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_left hden hm.le)
      _ = _ := by ring
  have hlossbound : loss/(2*m*(A+e)) ≤ (loss/(2*Amin))/m := by
    calc
      _ ≤ loss/(2*m*Amin) := div_le_div_of_nonneg_left hloss (by positivity)
        (mul_le_mul_of_nonneg_left (by linarith : Amin ≤ A+e) (by positivity))
      _ = _ := by ring
  calc
    _ = (1+k*theta)/(m*A)-
        (((1+k)*e/Amin^2)/m+(loss/(2*Amin))/m) := by ring
    _ ≤ (1+k*theta)/(m*(A+e))-loss/(2*m*(A+e)) := by
      linarith only [hdiff,hdiffbound,hlossbound]
    _ ≤ delta := hδ

end FCAppendix.Affine.Uniform07Finishing.Crossover
