import FCAppendix.Affine.Uniform06.FullRateLimit
import FCAppendix.Affine.Uniform06.FullReciprocalMean
import FCAppendix.Affine.Uniform06.ActualRootDerivative
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.FixedTiltPhysicalDerivative

open MeasureTheory ProbabilityTheory Set Filter Topology
open FCAppendix.Affine.ClippedResidual FCAppendix.ExponentialTilt
open Uniform07 RawMixedSource RawTiltedSource PhysicalExposureLimit MixedWeakLimits
open FullReciprocalMean

def lowerLaplace (ξ θ b : ℝ) (G : Measure (ℝ × ℝ)) : ℝ :=
  ∫ p,Real.exp (-θ*exposure ξ b p.2) ∂G

def Z (i : Row) (G : Measure (ℝ × ℝ)) (θ b : ℝ) : ℝ :=
  (1-cutoff i)*Real.exp (-θ/2)+cutoff i*lowerLaplace (xi i) θ b G

def objective (i : Row) (G : Measure (ℝ × ℝ)) (r θ b : ℝ) : ℝ :=
  -θ*r-Real.log (Z i G θ b)

theorem Z_eq_mgf (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {b : ℝ} (hb : 0 < b) (θ : ℝ) :
    Z i G θ b=mgf (demand (xi i) b) (source i G) (-θ) := by
  letI := MixedLaw.physicalLowerLaw_probability i hb G
  have hZ := normalizer_eq_mgf i (MixedLaw.physicalLowerLaw i b G)
    (MixedLaw.physicalLowerLaw_bounds i hb G) (-θ)
  have he : Z i G θ b=normalizer i (MixedLaw.physicalLowerLaw i b G) (-θ) := by
    unfold Z lowerLaplace normalizer MixedLaw.physicalLowerLaw
    rw [integral_map (show AEMeasurable (fun p : ℝ × ℝ => exposure (xi i) b p.2) G from
      ((continuous_exposure (xi_pos i) hb).measurable.comp measurable_snd).aemeasurable)
      (by fun_prop : AEStronglyMeasurable (fun x : ℝ => Real.exp (-θ*x)) _)]
  rw [he,hZ]
  have hp := point_preserving i G hb
  rw [mgf,← hp.map_eq]
  exact integral_map hp.measurable.aemeasurable
    ((measurable_fst.const_mul (-θ)).exp).aestronglyMeasurable

theorem Z_pos (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {b : ℝ} (hb : 0 < b) (θ : ℝ) : 0 < Z i G θ b := by
  rw [Z_eq_mgf i G hb θ]
  exact mgf_pos (integrable_exp_mul_of_bounded (source i G)
    (measurable_demand _ _).aemeasurable (ae_of_all _ (demand_bounds (xi_pos i) hb)) (-θ))

theorem objective_eq_cgf (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {b : ℝ} (hb : 0 < b) (r θ : ℝ) :
    objective i G r θ b=-θ*r-cgf (demand (xi i) b) (source i G) (-θ) := by
  rw [objective,Z_eq_mgf i G hb θ,cgf]

theorem likelihood_lipschitz {ξ θ lo : ℝ} (hξ : 0 < ξ) (hθ : 0 ≤ θ)
    (hlo : 0 < lo) (B : ℝ) :
    LipschitzOnWith (Real.nnabs (θ/(ξ*lo)))
      (fun b => Real.exp (-θ*exposure ξ b B)) (Ici lo) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro a ha b hb
  have he := exp_difference_upper
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hθ)
      (exposure_nonneg hξ (hlo.trans_le ha) (b:=B)))
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hθ)
      (exposure_nonneg hξ (hlo.trans_le hb) (b:=B)))
  have hx := exposure_price_lipschitz hξ hlo ha hb B
  have harg : |-θ*exposure ξ a B-(-θ*exposure ξ b B)|=
      θ*|exposure ξ a B-exposure ξ b B| := by
    rw [← mul_sub,abs_mul,abs_neg,abs_of_nonneg hθ]
  rw [Real.dist_eq,Real.dist_eq,Real.coe_nnabs,abs_of_nonneg (div_nonneg hθ (by positivity))]
  rw [Real.exp_zero,one_mul,harg] at he
  have hh := he.trans (mul_le_mul_of_nonneg_left hx hθ)
  convert! hh using 1
  ring

theorem lowerLaplace_hasDerivAt (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {U b θ : ℝ} (hb : 0 < b) (hθ : 0 ≤ θ)
    (hcap : ∀ᵐ p ∂G,p.2 ≤ U) (hguard : (1-xi i)*U < b)
    (hnull : (G.map Prod.snd) {b}=0) :
    HasDerivAt (fun a => lowerLaplace (xi i) θ a G)
      ((θ/(xi i))*(∫ p,Real.exp (-θ*exposure (xi i) b p.2)*
        ReciprocalSecantBounds.reciprocalTerm p.2 b ∂G)) b := by
  let f := fun a (p : ℝ × ℝ) => Real.exp (-θ*exposure (xi i) a p.2)
  let f' := fun p : ℝ × ℝ => (θ/xi i)*Real.exp (-θ*exposure (xi i) b p.2)*
    ReciprocalSecantBounds.reciprocalTerm p.2 b
  have hξ1 : xi i < 1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  have hne : ∀ᵐ p ∂G,p.2≠b := by
    have hh := measure_eq_zero_iff_ae_notMem.mp hnull
    exact (ae_map_iff measurable_snd.aemeasurable (by measurability)).mp hh
  have hd : ∀ᵐ p ∂G,HasDerivAt (fun a => f a p) (f' p) b := by
    filter_upwards [hcap,hne] with p hp hpne
    have hκ : (1-xi i)*p.2 < b :=
      (mul_le_mul_of_nonneg_left hp (sub_pos.mpr hξ1).le).trans_lt hguard
    have hh := (ActualRootDerivative.exposure_price_derivative (xi_pos i) hξ1 hb
      (Ne.symm hpne) hκ.ne').const_mul (-θ) |>.exp
    by_cases hbB : b< p.2
    · have hcase : (1-xi i)*p.2 < b ∧ b < p.2 := ⟨hκ,hbB⟩
      rw [if_pos hcase] at hh
      convert! hh using 1
      dsimp only [f']
      rw [ReciprocalSecantBounds.reciprocalTerm,if_pos hbB]
      ring
    · have hcase : ¬ ((1-xi i)*p.2 < b ∧ b < p.2) := fun h => hbB h.2
      rw [if_neg hcase,mul_zero,mul_zero] at hh
      simpa only [f,f',ReciprocalSecantBounds.reciprocalTerm,if_neg hbB,mul_zero] using hh
  have hm (a : ℝ) : Measurable (f a) := by unfold f exposure; fun_prop
  have hm' : Measurable f' := by
    exact ((hm b).const_mul (θ/xi i)).mul
      ((EntryReciprocalLimit.measurable_reciprocalTerm measurable_id b).comp measurable_snd)
  have hi : Integrable (f b) G := by
    apply Integrable.of_mem_Icc 0 1 (hm b).aemeasurable
    exact ae_of_all _ fun p => ⟨(Real.exp_pos _).le,by
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hθ) (exposure_nonneg (xi_pos i) hb)⟩
  have hs : Ici (b/2) ∈ 𝓝 b := Ici_mem_nhds (by linarith)
  have ht := hasDerivAt_integral_of_dominated_loc_of_lip hs
    (Eventually.of_forall fun a => (hm a).aestronglyMeasurable) hi hm'.aestronglyMeasurable
    (ae_of_all _ fun p => likelihood_lipschitz (xi_pos i) hθ (half_pos hb) p.2)
    (integrable_const (θ/(xi i*(b/2)))) hd
  have he : (∫ p,f' p ∂G)=(θ/xi i)*(∫ p,Real.exp (-θ*exposure (xi i) b p.2)*
      ReciprocalSecantBounds.reciprocalTerm p.2 b ∂G) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun p => by dsimp [f']; ring
  simpa only [lowerLaplace,f,he] using ht.2

theorem objective_hasDerivAt (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {U b θ : ℝ} (hb : 0 < b) (hθ : 0 ≤ θ) (r : ℝ)
    (hcap : ∀ᵐ p ∂G,p.2 ≤ U) (hguard : (1-xi i)*U < b)
    (hnull : (G.map Prod.snd) {b}=0) :
    HasDerivAt (objective i G r θ)
      (-θ/(xi i)*(∫ q,FullReciprocalMean.reciprocal b q ∂tiltedSource i G b θ)) b := by
  have hl := (lowerLaplace_hasDerivAt i G hb hθ hcap hguard hnull).const_mul (cutoff i)
  have hz := hl.const_add ((1-cutoff i)*Real.exp (-θ/2))
  have hlog := hz.log (Z_pos i G hb θ).ne'
  have hobj := hlog.neg.const_add (-θ*r)
  have he := integral_lowerTest i G hb θ (fun B => ReciprocalSecantBounds.reciprocalTerm B b)
    (EntryReciprocalLimit.measurable_reciprocalTerm measurable_id b)
    (inv_nonneg.mpr hb.le) (fun B => EntryReciprocalLimit.reciprocal_abs_bound hb le_rfl)
  have hfac : factor i G b θ=cutoff i/Z i G θ b := by
    rw [factor,cgf,← Z_eq_mgf i G hb θ,Real.exp_neg,Real.exp_log (Z_pos i G hb θ)]
    ring
  rw [hfac] at he
  convert! hobj using 1
  rw [FullReciprocalMean.reciprocal,he]
  dsimp only [Z]
  ring

theorem actual_triangular_gradient_limit (i : Row)
    (G : ℕ → ProbabilityMeasure (ℝ × ℝ))
    (hG : Tendsto G atTop (𝓝 (FullJointLaw.law i)))
    {lo hi Θ U : ℝ} (hlo : 0 < lo) (hU : 0 ≤ U)
    (hbox : ∀ n,∀ᵐ p ∂(G n:Measure (ℝ × ℝ)),
      p ∈ EarlyJointCompactness.box (cutoff i) U)
    (b θ : ℕ → ℝ) {b0 θ0 : ℝ}
    (hb : ∀ n,b n ∈ Icc lo hi) (hθ : ∀ n,θ n ∈ Icc (-Θ) Θ)
    (hblim : Tendsto b atTop (𝓝 b0)) (hθlim : Tendsto θ atTop (𝓝 θ0)) :
    Tendsto (fun n => θ n/(xi i)*(∫ q,FullReciprocalMean.reciprocal (b n) q
      ∂tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n))) atTop
      (𝓝 (θ0/(xi i)*nu i b0 θ0)) :=
  (hθlim.div_const (xi i)).mul
    (original_tilted_reciprocal_and_window i G hG hlo hU hbox
      b b θ hb hb hθ hblim hblim hθlim).1

end FCAppendix.Affine.Uniform06.FixedTiltPhysicalDerivative
