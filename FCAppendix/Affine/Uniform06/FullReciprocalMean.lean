import FCAppendix.Affine.Uniform06.CompactNullTests
import FCAppendix.Affine.Uniform06.FullBidGeometry
import FCAppendix.Affine.Uniform06.EntryRawTiltedFiber
import FCAppendix.Affine.Uniform06.RawTiltedSource
import FCAppendix.Affine.Uniform06.PhysicalExposureLimit

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.FullReciprocalMean

open MeasureTheory ProbabilityTheory Set Filter Topology LowBody
open Uniform07 FullJointLaw FullBidGeometry ReciprocalSecantBounds
open FCAppendix.ExponentialTilt FCAppendix.Affine.ClippedResidual
open RawMixedSource RawTiltedSource PhysicalExposureLimit MixedWeakLimits

def lowerTest (f : ℝ → ℝ) (r : RowRival) : ℝ := if r.1=0 then f r.2 else 0
def reciprocal (z : ℝ) : RowRival → ℝ := lowerTest (fun B => reciprocalTerm B z)
def window (lo hi : ℝ) : RowRival → ℝ :=
  lowerTest (fun B => if lo< B ∧ B≤ hi then 1 else 0)

theorem measurable_lowerTest {f : ℝ → ℝ} (hf : Measurable f) : Measurable (lowerTest f) :=
  Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const)
    (hf.comp measurable_snd) measurable_const

theorem measurable_reciprocal (z : ℝ) : Measurable (reciprocal z) :=
  measurable_lowerTest (EntryReciprocalLimit.measurable_reciprocalTerm measurable_id z)

theorem measurable_window (lo hi : ℝ) : Measurable (window lo hi) :=
  measurable_lowerTest (Measurable.ite
    ((measurableSet_lt measurable_const measurable_id).inter
      (measurableSet_le measurable_id measurable_const)) measurable_const measurable_const)

theorem reciprocal_bounds {lo z : ℝ} (hlo : 0 < lo) (hz : lo ≤ z) (r : RowRival) :
    0 ≤ reciprocal z r ∧ reciprocal z r ≤ lo⁻¹ := by
  unfold reciprocal lowerTest
  split_ifs
  · exact ⟨reciprocalTerm_nonneg (hlo.trans_le hz),
      (le_abs_self _).trans (EntryReciprocalLimit.reciprocal_abs_bound hlo hz)⟩
  · exact ⟨le_rfl,inv_nonneg.mpr hlo.le⟩

theorem window_bounds (lo hi : ℝ) (r : RowRival) : window lo hi r ∈ Icc (0:ℝ) 1 := by
  unfold window lowerTest
  by_cases hr : r.1=0
  · rw [if_pos hr]
    change (if lo<r.2 ∧ r.2≤hi then (1:ℝ) else 0)∈Icc (0:ℝ) 1
    split_ifs <;> norm_num
  · simp only [if_neg hr]
    norm_num

def factor (i : Row) (G : Measure (ℝ × ℝ)) (b θ : ℝ) : ℝ :=
  cutoff i*Real.exp (-cgf (demand (xi i) b) (source i G) (-θ))

theorem factor_pos (i : Row) (G : Measure (ℝ × ℝ)) (b θ : ℝ) :
    0 < factor i G b θ := mul_pos (cutoff_pos i) (Real.exp_pos _)

theorem integral_lowerTest (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {b : ℝ} (hb : 0 < b) (θ : ℝ) (f : ℝ → ℝ) (hf : Measurable f)
    {M : ℝ} (_hM : 0 ≤ M) (hbound : ∀ B,|f B| ≤ M) :
    (∫ r,lowerTest f r ∂tiltedSource i G b θ)=
      factor i G b θ*(∫ p,Real.exp (-θ*exposure (xi i) b p.2)*f p.2 ∂G) := by
  let L := G.map Prod.snd
  let X := demand (xi i) b
  let a := cgf X (source i G) (-θ)
  let H : RowRival → ℝ := fun r => Real.exp (-θ*X r-a)*lowerTest f r
  letI : IsProbabilityMeasure L := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hH : Measurable H :=
    ((((measurable_demand _ _).const_mul (-θ)).sub_const a).exp).mul (measurable_lowerTest hf)
  have hl : Integrable (fun B => H ((0:Fin 4),B)) L := by
    apply Integrable.of_bound (hH.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (Real.exp (|θ|+|a|)*M)
    apply ae_of_all
    intro B
    have hx := demand_bounds (xi_pos i) hb ((0:Fin 4),B)
    have he : Real.exp (-θ*X ((0:Fin 4),B)-a) ≤ Real.exp (|θ|+|a|) := by
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_right (neg_le_abs θ) hx.1
      have hh := mul_le_mul_of_nonneg_left hx.2 (abs_nonneg θ)
      dsimp [X] at *
      linarith [neg_le_abs a]
    change ‖Real.exp (-θ*X ((0:Fin 4),B)-a)*f B‖ ≤ _
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul he (hbound B) (abs_nonneg _) (Real.exp_pos _).le
  rw [tiltedSource,integral_tilted_mul_eq_cgf _
    (integrable_exp_mul_of_bounded (source i G) (measurable_demand _ _).aemeasurable
      (ae_of_all _ (demand_bounds (xi_pos i) hb)) (-θ))]
  simp only [smul_eq_mul]
  change (∫ r,H r ∂rivalLaw (cutoff i) 0 (1-cutoff i) L)=_
  rw [EntryRawTiltedFiber.integral_rivalLaw (cutoff i) (cutoff_pos i).le
    (cutoff_lt_one i).le L H hH hl]
  have h2 : H (2,0)=0 := by simp [H,lowerTest]
  have h3 : H (3,0)=0 := by simp [H,lowerTest]
  simp only [h2,h3,mul_zero,add_zero]
  have he : (∫ B,H ((0:Fin 4),B) ∂L)=
      Real.exp (-a)*(∫ p,Real.exp (-θ*exposure (xi i) b p.2)*f p.2 ∂G) := by
    let F : ℝ→ℝ:=fun B=>Real.exp (-θ*exposure (xi i) b B)*f B
    have hF : Measurable F :=
      ((((continuous_exposure (xi_pos i) hb).measurable.const_mul (-θ)).exp).mul hf)
    have hpull : (∫ p,F p.2 ∂G)=(∫ B,F B ∂L) :=
      (integral_map measurable_snd.aemeasurable hF.aestronglyMeasurable).symm
    calc
      _=(∫ B,Real.exp (-a)*F B ∂L) := by
        apply integral_congr_ae
        exact ae_of_all _ fun B=>by
          change Real.exp (-θ*exposure (xi i) b B-a)*f B=
            Real.exp (-a)*(Real.exp (-θ*exposure (xi i) b B)*f B)
          rw [sub_eq_add_neg,Real.exp_add]
          ring
      _=Real.exp (-a)*(∫ B,F B ∂L) := integral_const_mul _ _
      _=_ := congrArg (fun t=>Real.exp (-a)*t) hpull.symm
  rw [he]
  dsimp only [factor,a,X]
  ring

theorem factor_tendsto (i : Row)
    (G : ℕ → ProbabilityMeasure (ℝ × ℝ)) (G0 : ProbabilityMeasure (ℝ × ℝ))
    (hG : Tendsto G atTop (𝓝 G0)) (b θ : ℕ → ℝ) {b0 θ0 : ℝ}
    (hb : ∀ n,0 < b n) (hb0 : 0 < b0)
    (hblim : Tendsto b atTop (𝓝 b0)) (hθ : Tendsto θ atTop (𝓝 θ0)) :
    Tendsto (fun n => factor i (G n:Measure (ℝ × ℝ)) (b n) (θ n)) atTop
      (𝓝 (factor i (G0:Measure (ℝ × ℝ)) b0 θ0)) := by
  let ν := fun n => lowerProbability i (G n) (b n) (hb n)
  let ν0 := lowerProbability i G0 b0 hb0
  have hν := fun n => MixedLaw.physicalLowerLaw_bounds i (hb n) (G n:Measure (ℝ × ℝ))
  have hν0 := MixedLaw.physicalLowerLaw_bounds i hb0 (G0:Measure (ℝ × ℝ))
  have hw := lowerProbability_tendsto i G G0 hG b hb hb0 hblim
  have hZ := normalizer_tendsto i ν ν0 hν hν0 hw (fun n => -θ n) hθ.neg
  have hcg := hZ.log (normalizer_pos i (ν0:Measure ℝ) hν0 (-θ0)).ne'
  have he (M : ProbabilityMeasure (ℝ × ℝ)) {a : ℝ} (ha : 0 < a) (u : ℝ) :
      Real.log (normalizer i (MixedLaw.physicalLowerLaw i a (M:Measure (ℝ × ℝ))) u)=
        cgf (demand (xi i) a) (source i (M:Measure (ℝ × ℝ))) u := by
    letI : IsProbabilityMeasure (MixedLaw.physicalLowerLaw i a (M:Measure (ℝ × ℝ))) :=
      MixedLaw.physicalLowerLaw_probability i ha (M:Measure (ℝ × ℝ))
    rw [normalizer_eq_mgf i _ (MixedLaw.physicalLowerLaw_bounds i ha _)]
    exact (cgf_comp_of_preserving (point_preserving i _ ha) measurable_fst u).symm
  have hn (n : ℕ) : Real.log (normalizer i (ν n:Measure ℝ) (-θ n))=
      cgf (demand (xi i) (b n)) (source i (G n:Measure (ℝ × ℝ))) (-θ n) := by
    convert! he (G n) (hb n) (-θ n) using 1
  have hn0 : Real.log (normalizer i (ν0:Measure ℝ) (-θ0))=
      cgf (demand (xi i) b0) (source i (G0:Measure (ℝ × ℝ))) (-θ0) := by
    convert! he G0 hb0 (-θ0) using 1
  have hh := (Real.continuous_exp.continuousAt.tendsto.comp hcg.neg).const_mul (cutoff i)
  simpa only [hn,hn0,factor,Function.comp_def] using hh

def nu (i : Row) (b θ : ℝ) : ℝ :=
  ∫ r,reciprocal b r ∂tiltedSource i (law i:Measure (ℝ × ℝ)) b θ

theorem nu_pos (i : Row) {b : ℝ} (hb : 0 < b) (hbL : b < entry i) (θ : ℝ) :
    0 < nu i b θ := by
  let G := (law i:Measure (ℝ × ℝ))
  let f : (ℝ × ℝ) → ℝ := fun p =>
    Real.exp (-θ*exposure (xi i) b p.2)*reciprocalTerm p.2 b
  have hf0 : 0 ≤ f := fun p => mul_nonneg (Real.exp_pos _).le (reciprocalTerm_nonneg hb)
  have hf : Integrable f G := by
    apply Integrable.of_bound
      ((((continuous_exposure (xi_pos i) hb).measurable.comp measurable_snd).const_mul (-θ)).exp.mul
        ((EntryReciprocalLimit.measurable_reciprocalTerm measurable_id b).comp measurable_snd)).aestronglyMeasurable
      (Real.exp |θ| /b)
    apply ae_of_all
    intro p
    change ‖f p‖≤Real.exp |θ|/b
    have hx0 := exposure_nonneg (xi_pos i) hb (b:=p.2)
    have hx1 := exposure_le_one (xi i) b p.2
    have he : Real.exp (-θ*exposure (xi i) b p.2) ≤ Real.exp |θ| := by
      apply Real.exp_le_exp.mpr
      have h1 := mul_le_mul_of_nonneg_right (neg_le_abs θ) hx0
      have h2 := mul_le_mul_of_nonneg_left hx1 (abs_nonneg θ)
      linarith
    rw [Real.norm_of_nonneg (hf0 p)]
    exact (mul_le_mul he (reciprocalTerm_le hb) (reciprocalTerm_nonneg hb)
      (Real.exp_pos _).le).trans_eq (div_eq_mul_inv _ _).symm
  let A := {p : ℝ × ℝ | p.1 ∈ Ioc (entry i) (cutoff i)}
  have hA : 0 < G A := by
    have hm := EarlyMean.lower_active_mass i G (full_value_marginal i)
    have hx : 0 < 1-x i := by cases i <;> norm_num [x,xQ]
    have hreal : 0<G.real A := by
      change 0<G.real {p |p.1∈Ioc (entry i) (cutoff i)}
      rw [hm]
      exact hx
    exact (ENNReal.toReal_pos_iff.mp hreal).1
  have hsub : G A ≤ G (Function.support f) := by
    apply measure_mono_ae
    filter_upwards [full_active_graph i] with p hp hpa
    change f p≠0
    have hs : b< p.2 := hbL.trans (by rw [hp hpa]; exact EntryReciprocalLimit.entry_lt_activeBid i hpa.1)
    dsimp [f]
    rw [reciprocalTerm,if_pos hs]
    exact (mul_pos (Real.exp_pos _) (inv_pos.mpr (hb.trans hs))).ne'
  have hp := (integral_pos_iff_support_of_nonneg hf0 hf).mpr (hA.trans_le hsub)
  rw [nu,reciprocal,integral_lowerTest i G hb θ (fun B=>reciprocalTerm B b)
    (by convert! EntryReciprocalLimit.measurable_reciprocalTerm measurable_id b using 1)
    (inv_nonneg.mpr hb.le) (fun B => EntryReciprocalLimit.reciprocal_abs_bound hb le_rfl)]
  exact mul_pos (factor_pos i G b θ) hp

theorem original_tilted_reciprocal_and_window (i : Row)
    (G : ℕ → ProbabilityMeasure (ℝ × ℝ))
    (hG : Tendsto G atTop (𝓝 (law i)))
    {lo hi Θ U : ℝ} (hlo : 0 < lo) (hU : 0 ≤ U)
    (hbox : ∀ n,∀ᵐ p ∂(G n:Measure (ℝ × ℝ)),
      p ∈ EarlyJointCompactness.box (cutoff i) U)
    (b z θ : ℕ → ℝ) {b0 θ0 : ℝ}
    (hb : ∀ n,b n ∈ Icc lo hi) (hz : ∀ n,z n ∈ Icc lo hi)
    (hθ : ∀ n,θ n ∈ Icc (-Θ) Θ)
    (hblim : Tendsto b atTop (𝓝 b0)) (hzlim : Tendsto z atTop (𝓝 b0))
    (hθlim : Tendsto θ atTop (𝓝 θ0)) :
    Tendsto (fun n => ∫ r,reciprocal (z n) r
      ∂tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n)) atTop (𝓝 (nu i b0 θ0)) ∧
    Tendsto (fun n => ∫ r,window (z n) (b n) r
      ∂tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n)) atTop (𝓝 0) := by
  have hb0 := isClosed_Icc.mem_of_tendsto hblim (Eventually.of_forall hb)
  have hb0p := hlo.trans_le hb0.1
  have hbp := fun n => hlo.trans_le (hb n).1
  have hbox0 := EarlyJointCompactness.limit_supportedOn
    (EarlyJointCompactness.box_compact (cutoff i) U) G (law i) hG
      (Eventually.of_forall hbox)
  have ht := CompactNullTests.moving_reciprocal_and_window (xi_pos i) hlo hU G (law i) hG
    (fun n => (hbox n).mono fun _ h => h.2) (hbox0.mono fun _ h => h.2)
    b z θ hb hz hθ hblim hzlim hθlim (full_bid_singleton_null i b0)
  have hf := factor_tendsto i G (law i) hG b θ hbp hb0p hblim hθlim
  have hr := hf.mul ht.1
  have hw := hf.mul ht.2
  constructor
  · have hn (n : ℕ) := integral_lowerTest i (G n:Measure (ℝ × ℝ)) (hbp n) (θ n)
      (fun B=>reciprocalTerm B (z n))
      (by convert! EntryReciprocalLimit.measurable_reciprocalTerm measurable_id (z n) using 1)
      (inv_nonneg.mpr hlo.le) (fun B=>EntryReciprocalLimit.reciprocal_abs_bound hlo (hz n).1)
    have hn0 := integral_lowerTest i (law i:Measure (ℝ × ℝ)) hb0p θ0
      (fun B=>reciprocalTerm B b0)
      (by convert! EntryReciprocalLimit.measurable_reciprocalTerm measurable_id b0 using 1)
      (inv_nonneg.mpr hb0p.le) (fun B=>EntryReciprocalLimit.reciprocal_abs_bound hb0p le_rfl)
    simpa only [nu,reciprocal,hn,hn0] using hr
  · have he (n : ℕ) := integral_lowerTest i (G n:Measure (ℝ × ℝ)) (hbp n) (θ n)
      (fun B => if z n< B ∧ B≤ b n then 1 else 0)
      (Measurable.ite ((measurableSet_lt measurable_const measurable_id).inter
        (measurableSet_le measurable_id measurable_const)) measurable_const measurable_const)
      (by norm_num : (0:ℝ) ≤ 1) (by intro B; split_ifs <;> norm_num)
    simpa only [window,he,mul_zero] using hw

end FCAppendix.Affine.Uniform06.FullReciprocalMean
