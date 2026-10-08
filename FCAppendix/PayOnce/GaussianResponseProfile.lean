import FCAppendix.PayOnce.GaussianTruncatedMoments

noncomputable section
namespace FCAppendix.PayOnce.GaussianResponse
open MeasureTheory ProbabilityTheory Set Filter Topology
local notation "Φ" => cdf (gaussianReal 0 1)
local notation "φ" => gaussianPDFReal 0 1

def responseMap (y : ℝ) : ℝ := 2*y + φ y / Φ y

theorem hasDerivAt_responseMap (y : ℝ) :
    HasDerivAt responseMap (2-y*(φ y/Φ y)-(φ y/Φ y)^2) y := by
  have hp := CorrelatedLoads.gaussian_cdf_pos y
  have hh := ((hasDerivAt_id y).const_mul 2).add
    ((Bayes.hasDerivAt_standardGaussianPDF y).div (hasDerivAt_normalCDF y) hp.ne')
  change HasDerivAt (fun z => 2*z+φ z/Φ z) _ y
  apply hh.congr_deriv
  field_simp
  ring

theorem responseMap_deriv_lower (y : ℝ) :
    1 ≤ 2-y*(φ y/Φ y)-(φ y/Φ y)^2 := by
  linarith [truncated_variance_nonneg y]

theorem responseMap_strictMono : StrictMono responseMap :=
  strictMono_of_hasDerivAt_pos hasDerivAt_responseMap
    (fun y => lt_of_lt_of_le (by norm_num) (responseMap_deriv_lower y))

theorem responseMap_continuous : Continuous responseMap :=
  continuous_iff_continuousAt.mpr (fun y => (hasDerivAt_responseMap y).continuousAt)

theorem responseMap_sub_lower {a b : ℝ} (hab : a ≤ b) :
    b-a ≤ responseMap b-responseMap a := by
  have hh := mul_sub_le_image_sub_of_le_deriv
    (fun y => (hasDerivAt_responseMap y).differentiableAt)
    (fun y => by rw [(hasDerivAt_responseMap y).deriv]; exact responseMap_deriv_lower y) hab
  simpa using hh

theorem responseMap_tendsto_atTop : Tendsto responseMap atTop atTop := by
  apply tendsto_atTop_mono' atTop (f₁ := fun y => responseMap 0+y)
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with y hy
    linarith [responseMap_sub_lower hy]
  · exact tendsto_atTop_add_const_left atTop (responseMap 0) tendsto_id

theorem responseMap_tendsto_atBot : Tendsto responseMap atBot atBot := by
  apply tendsto_atBot_mono' atBot (f₁ := fun y => responseMap 0+y)
  · filter_upwards [eventually_le_atBot (0:ℝ)] with y hy
    linarith [responseMap_sub_lower hy]
  · exact tendsto_atBot_add_const_left atBot (responseMap 0) tendsto_id

theorem responseMap_surjective : Function.Surjective responseMap :=
  responseMap_continuous.surjective responseMap_tendsto_atTop responseMap_tendsto_atBot

theorem responseMap_existsUnique (x : ℝ) : ∃! y, responseMap y=x := by
  obtain ⟨y, hy⟩ := responseMap_surjective x
  exact ⟨y, hy, fun z hz => responseMap_strictMono.injective (hz.trans hy.symm)⟩

def response (x : ℝ) : ℝ := (responseMap_surjective x).choose

@[simp] theorem responseMap_response (x : ℝ) : responseMap (response x)=x :=
  (responseMap_surjective x).choose_spec

@[simp] theorem response_responseMap (y : ℝ) : response (responseMap y)=y :=
  responseMap_strictMono.injective (responseMap_response (responseMap y))

theorem response_strictMono : StrictMono response := by
  intro x z hxz
  apply responseMap_strictMono.lt_iff_lt.mp
  simpa only [responseMap_response] using hxz

theorem response_surjective : Function.Surjective response :=
  fun y => ⟨responseMap y, response_responseMap y⟩

theorem response_continuous : Continuous response :=
  response_strictMono.monotone.continuous_of_surjective response_surjective

theorem response_sub_le {x z : ℝ} (hxz : x ≤ z) :
    response z-response x ≤ z-x := by
  simpa only [responseMap_response] using responseMap_sub_lower (response_strictMono.monotone hxz)

theorem response_abs_sub_le (x z : ℝ) : |response z-response x| ≤ |z-x| := by
  rcases le_total x z with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr (response_strictMono.monotone h)),
      abs_of_nonneg (sub_nonneg.mpr h)]
    exact response_sub_le h
  · rw [abs_sub_comm (response z), abs_sub_comm z,
      abs_of_nonneg (sub_nonneg.mpr (response_strictMono.monotone h)),
      abs_of_nonneg (sub_nonneg.mpr h)]
    exact response_sub_le h

theorem successPrimitive_pos (y : ℝ) : 0 < Bayes.gaussianSuccessPrimitive y := by
  have hmono : StrictMono Bayes.gaussianSuccessPrimitive :=
    strictMono_of_hasDerivAt_pos Bayes.hasDerivAt_gaussianSuccessPrimitive
      CorrelatedLoads.gaussian_cdf_pos
  have hR : 0 < 1-min y 0 := by linarith [min_le_right y 0]
  have hn := (Bayes.gaussianSuccessPrimitive_neg_bounds hR).1
  have hlt : -(1-min y 0) < y := by linarith [min_le_left y 0]
  exact lt_of_le_of_lt hn (hmono hlt)

theorem responseMap_eq_iff (x y : ℝ) :
    responseMap y=x ↔ Bayes.gaussianSuccessPrimitive y=(x-y)*Φ y := by
  have hp := CorrelatedLoads.gaussian_cdf_pos y
  rw [responseMap, Bayes.gaussianSuccessPrimitive]
  constructor
  · intro h
    have hh := congrArg (fun z => z*Φ y) h
    field_simp at hh
    nlinarith only [hh]
  · intro h
    apply (mul_right_cancel₀ hp.ne')
    field_simp
    nlinarith only [h]

theorem response_equation (x : ℝ) :
    Bayes.gaussianSuccessPrimitive (response x)=(x-response x)*Φ (response x) :=
  (responseMap_eq_iff x (response x)).mp (responseMap_response x)

theorem response_lt (x : ℝ) : response x < x := by
  have hp := CorrelatedLoads.gaussian_cdf_pos (response x)
  have hh := successPrimitive_pos (response x)
  rw [response_equation] at hh
  exact sub_pos.mp ((mul_pos_iff_of_pos_right hp).mp hh)

theorem response_equation_existsUnique (x : ℝ) :
    ∃! y, Bayes.gaussianSuccessPrimitive y=(x-y)*Φ y := by
  refine ⟨response x, response_equation x, fun y hy => ?_⟩
  apply responseMap_strictMono.injective
  rw [responseMap_response]
  exact (responseMap_eq_iff x y).mpr hy

theorem response_equation_iff (x y : ℝ) :
    Bayes.gaussianSuccessPrimitive y=(x-y)*Φ y ↔ y=response x := by
  constructor
  · intro h
    exact (response_equation_existsUnique x).unique h (response_equation x)
  · rintro rfl
    exact response_equation x

end FCAppendix.PayOnce.GaussianResponse
