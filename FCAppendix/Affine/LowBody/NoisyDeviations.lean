import FCAppendix.Affine.LowBody.NoisySupportedLimit

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set Classical
open Existence.Distributional

theorem bidRatio_width_pos {ε : ℝ} (hε : 0<ε) (hsmall : ε≤1/4) :
    0<1/(1+ε)-ε := by
  have hd : 0<1+ε:=by linarith
  apply sub_pos.mpr
  apply (lt_div_iff₀ hd).mpr
  nlinarith [mul_nonneg hε.le (show 0≤1/4-ε by linarith)]

def clippedRatio (ε r : ℝ) : ℝ:=max ε (min (1/(1+ε)) r)

theorem clippedRatio_bounds {ε : ℝ} (hε : 0<ε) (hsmall : ε≤1/4) (r : ℝ) :
    clippedRatio ε r∈Icc ε (1/(1+ε)) :=
  ⟨le_max_left _ _,max_le (le_of_lt (sub_pos.mp (bidRatio_width_pos hε hsmall))) (min_le_left _ _)⟩

def choiceAtRatio (ε : ℝ) (hε : 0<ε) (hsmall : ε≤1/4) (r : ℝ) : unitInterval :=
  ⟨(clippedRatio ε r-ε)/(1/(1+ε)-ε),
    div_nonneg (sub_nonneg.mpr (clippedRatio_bounds hε hsmall r).1) (bidRatio_width_pos hε hsmall).le,
    (div_le_one (bidRatio_width_pos hε hsmall)).mpr (by
      have hh:=(clippedRatio_bounds hε hsmall r).2
      linarith)⟩

theorem continuous_choiceAtRatio (ε : ℝ) (hε : 0<ε) (hsmall : ε≤1/4) :
    Continuous (choiceAtRatio ε hε hsmall) := by
  apply Continuous.subtype_mk
  unfold clippedRatio
  fun_prop

theorem bidRatio_choiceAtRatio (ε : ℝ) (hε : 0<ε) (hsmall : ε≤1/4) (r : ℝ) :
    bidRatio ε (choiceAtRatio ε hε hsmall r)=clippedRatio ε r := by
  unfold bidRatio choiceAtRatio
  dsimp only
  have hh:=div_mul_cancel₀ (clippedRatio ε r-ε) (bidRatio_width_pos hε hsmall).ne'
  nlinarith only [hh]

theorem clippedRatio_eq {ε r : ℝ} (hr : r∈Icc ε (1/(1+ε))) : clippedRatio ε r=r := by
  unfold clippedRatio
  rw [min_eq_right hr.2,max_eq_right hr.1]

theorem target_bid_exact {ε w x : ℝ} (hε : 0<ε) (hsmall : ε≤1/4) (hw : 0<w)
    (hlo : ε*w≤x) (hhi : x≤w/(1+ε)) :
    w*bidRatio ε (choiceAtRatio ε hε hsmall (x/w))=x := by
  have hr : x/w∈Icc ε (1/(1+ε)) := by
    constructor
    · exact (le_div_iff₀ hw).mpr (by nlinarith)
    · apply (div_le_iff₀ hw).mpr
      simpa only [div_eq_mul_inv,one_mul,mul_comm] using hhi
  rw [bidRatio_choiceAtRatio,clippedRatio_eq hr]
  field_simp

variable {N : ℕ}

theorem integrable_noisy_deviation (d : ℝ) {ξ ε : ℝ}
    (hξ : 0<ξ) (hξ1 : ξ<1) (hε : 0<ε) (hsmall : ε≤1/2)
    (c : ℕ) (categories : FiniteLaw (Fin 4))
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A:=unitInterval) mu)
    (dev : LowValue d×unitInterval→unitInterval) (hd : Measurable dev) :
    Integrable (fun x=>noisyExpectedUtility (N:=N) d ξ ε hε hsmall c categories mu (pi,(x.1,dev x)))
      (pi.1 : Measure (LowValue d×unitInterval)) := by
  let u : C(LowValue d×unitInterval,ℝ):=⟨fun x=>noisyExpectedUtility (N:=N) d ξ ε hε hsmall c categories mu (pi,x),
    (continuous_noisyExpectedUtility d hξ hξ1 hε hsmall c categories mu).comp
      (continuous_const.prodMk continuous_id)⟩
  apply Integrable.of_bound (u.continuous.measurable.comp (measurable_fst.prodMk hd)).aestronglyMeasurable ‖u‖
  exact ae_of_all _ (fun x=>u.norm_coe_le_norm (x.1,dev x))

theorem noisy_integrated_deviation_nonpos (d : ℝ) {ξ ε : ℝ}
    (hξ : 0<ξ) (hξ1 : ξ<1) (hε : 0<ε) (hsmall : ε≤1/2)
    (c : ℕ) (categories : FiniteLaw (Fin 4))
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A:=unitInterval) mu) (sigma : Kernel (LowValue d) unitInterval)
    [IsMarkovKernel sigma]
    (hdis : mu⊗ₘsigma=(pi.1 : Measure (LowValue d×unitInterval)))
    (hopt : ∀ᵐw ∂mu,∀ᵐq ∂sigma w,∀q' : unitInterval,
      noisyExpectedUtility (N:=N) d ξ ε hε hsmall c categories mu (pi,(w,q'))≤
        noisyExpectedUtility (N:=N) d ξ ε hε hsmall c categories mu (pi,(w,q)))
    (dev : LowValue d×unitInterval→unitInterval) (hd : Measurable dev)
    (E : Set (LowValue d×unitInterval)) :
    ∫x in E,(noisyExpectedUtility (N:=N) d ξ ε hε hsmall c categories mu (pi,(x.1,dev x))-
      noisyExpectedUtility (N:=N) d ξ ε hε hsmall c categories mu (pi,x))
        ∂(pi.1 : Measure (LowValue d×unitInterval))≤0 := by
  let u : LowValue d×unitInterval→ℝ:=fun x=>noisyExpectedUtility (N:=N) d ξ ε hε hsmall c categories mu (pi,x)
  have hu : Continuous u := (continuous_noisyExpectedUtility d hξ hξ1 hε hsmall c categories mu).comp
    (continuous_const.prodMk continuous_id)
  have hm : Measurable (fun x=>u (x.1,dev x)):=hu.measurable.comp (measurable_fst.prodMk hd)
  have hae : ∀ᵐx ∂(pi.1 : Measure (LowValue d×unitInterval)),u (x.1,dev x)≤u x := by
    rw [←hdis]
    apply Measure.ae_compProd_of_ae_ae (measurableSet_le hm hu.measurable)
    filter_upwards [hopt] with w hw
    filter_upwards [hw] with q hq
    exact hq (dev (w,q))
  exact integral_nonpos_of_ae ((ae_restrict_of_ae hae).mono (fun _ hh=>sub_nonpos.mpr hh))

end FCAppendix.Affine.LowBody
