import FCAppendix.Affine.Uniform06.EntryTilts
import FCAppendix.Probability.StandardizedReverseTilt
import FCAppendix.PayOnce.GaussianTiltCDFComparison

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryLaplace
open MeasureTheory ProbabilityTheory Set Filter Topology
open FCAppendix.ExponentialTilt FCAppendix.PayOnce.GaussianTilt
universe u
local notation "φ0" => gaussianPDFReal 0 1 0

theorem prefactor_mul_tendsto (v : ℕ → ℝ) (hv : Tendsto v atTop atTop) :
    Tendsto (fun m => prefactor (v m)*v m) atTop (𝓝 φ0) := by
  have hi := tendsto_inv_atTop_zero.comp hv
  have hlow : Tendsto (fun m => φ0/(1+(v m)⁻¹^2)) atTop (𝓝 φ0) := by
    convert! tendsto_const_nhds.div (tendsto_const_nhds.add (hi.pow 2))
      (by norm_num : (1 : ℝ)+0^2 ≠ 0) using 1; norm_num
  apply hlow.squeeze' tendsto_const_nhds
  · filter_upwards [hv.eventually_gt_atTop 0] with m hm
    have h := mul_le_mul_of_nonneg_right (prefactor_mills_bounds hm).1 hm.le
    have he : (φ0*v m/(1+(v m)^2))*v m=φ0/(1+(v m)⁻¹^2) := by
      field_simp [hm.ne',show 1+(v m)^2 ≠ 0 by positivity,
        show 1+(v m)⁻¹^2 ≠ 0 by positivity]
      ring
    rwa [he] at h
  · filter_upwards [hv.eventually_gt_atTop 0] with m hm
    have h := mul_le_mul_of_nonneg_right (prefactor_mills_bounds hm).2 hm.le
    simpa only [div_mul_cancel₀ _ hm.ne'] using h

theorem strict_laplace_mul_tendsto_of_cdf
    (ν : ℕ → Measure ℝ) [∀ m, IsProbabilityMeasure (ν m)] (v δ : ℕ → ℝ)
    (hv : Tendsto v atTop atTop)
    (hCDF : ∀ᶠ m in atTop, ∀ z,
      |cdf (ν m) z-cdf (gaussianReal 0 1) z| ≤ δ m)
    (hscaled : Tendsto (fun m => δ m*v m) atTop (𝓝 0)) :
    Tendsto (fun m => (∫ z, strictNegativeHalfExp (v m) z ∂ν m)*v m)
      atTop (𝓝 φ0) := by
  have hp := prefactor_mul_tendsto v hv
  have he : Tendsto (fun m =>
      ((∫ z, strictNegativeHalfExp (v m) z ∂ν m)-prefactor (v m))*v m)
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (by simpa using hscaled.const_mul 2)
    filter_upwards [hCDF,hv.eventually_gt_atTop 0] with m hm hvm
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos hvm]
    exact (mul_le_mul_of_nonneg_right
      (integral_strictNegativeHalfExp_sub_prefactor_le (ν m) hm hvm.le) hvm.le).trans_eq
      (by ring)
  convert! he.add hp using 1
  · funext m; ring
  · simp

def weightedMonomial (θ : ℝ) (k : ℕ) (W : ℝ) : ℝ :=
  if 0 < W then Real.exp (-θ*W)*W^k else 0

def finiteDifference (θ h : ℝ) (k : ℕ) (W : ℝ) : ℝ :=
  if 0 < W then Real.exp (-θ*W)*(1-Real.exp (-h*W))^k/h^k else 0

def strictLaplace (θ W : ℝ) : ℝ := if 0 < W then Real.exp (-θ*W) else 0

lemma weightedMonomial_zero (θ W : ℝ) : weightedMonomial θ 0 W=strictLaplace θ W := by
  simp [weightedMonomial,strictLaplace]

theorem finiteDifference_sandwich {θ h : ℝ} (hh : 0 < h) (k : ℕ) (W : ℝ) :
    finiteDifference θ h k W ≤ weightedMonomial θ k W ∧
      weightedMonomial θ k W ≤ finiteDifference (θ-(k : ℝ)*h) h k W := by
  by_cases hW : 0 < W
  · simp only [finiteDifference,weightedMonomial,if_pos hW]
    have he0 : 0 ≤ 1-Real.exp (-h*W) := by
      have he := Real.exp_le_one_iff.mpr (by nlinarith : -h*W ≤ 0)
      linarith
    have hl : (1-Real.exp (-h*W))/h ≤ W := by
      apply (div_le_iff₀ hh).2
      have he := Real.add_one_le_exp (-h*W)
      nlinarith
    have hu : W ≤ Real.exp (h*W)*((1-Real.exp (-h*W))/h) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hh).2
      have he := Real.add_one_le_exp (h*W)
      have hex : Real.exp (h*W)*Real.exp (-h*W)=1 := by
        rw [← Real.exp_add]
        convert! Real.exp_zero using 1; ring
      nlinarith
    constructor
    · have hp := pow_le_pow_left₀ (div_nonneg he0 hh.le) hl k
      have hm := mul_le_mul_of_nonneg_left hp (Real.exp_pos (-θ*W)).le
      simpa only [div_pow,mul_div_assoc] using hm
    · have hp := pow_le_pow_left₀ hW.le hu k
      have hm := mul_le_mul_of_nonneg_left hp (Real.exp_pos (-θ*W)).le
      have hex : Real.exp (-θ*W)*(Real.exp (h*W))^k=
          Real.exp (-(θ-(k : ℝ)*h)*W) := by
        rw [← Real.exp_nat_mul,← Real.exp_add]
        congr 1
        ring
      simp only [mul_pow, div_pow] at hm
      rw [← mul_assoc, hex] at hm
      simpa only [mul_div_assoc] using hm
  · simp [finiteDifference,weightedMonomial,hW]

lemma strictLaplace_add_nat_mul (θ h W : ℝ) (k : ℕ) :
    strictLaplace (θ+(k : ℝ)*h) W = strictLaplace θ W*(Real.exp (-h*W))^k := by
  by_cases hW : 0 < W
  · simp only [strictLaplace,if_pos hW]
    rw [← Real.exp_nat_mul,← Real.exp_add]
    congr 1
    ring
  · simp [strictLaplace,hW]

lemma finiteDifference_one (θ h W : ℝ) :
    finiteDifference θ h 1 W=(strictLaplace θ W-strictLaplace (θ+h) W)/h := by
  have hh := strictLaplace_add_nat_mul θ h W 1
  norm_num only [Nat.cast_one,one_mul,pow_one] at hh
  rw [hh]
  by_cases hW : 0 < W <;> simp [finiteDifference,strictLaplace,hW]; ring

lemma finiteDifference_two (θ h W : ℝ) :
    finiteDifference θ h 2 W=(strictLaplace θ W-2*strictLaplace (θ+h) W+
      strictLaplace (θ+2*h) W)/h^2 := by
  have h1 := strictLaplace_add_nat_mul θ h W 1
  have h2 := strictLaplace_add_nat_mul θ h W 2
  norm_num only [Nat.cast_one,one_mul,pow_one,Nat.cast_ofNat] at h1 h2
  rw [h1,h2]
  by_cases hW : 0 < W <;> simp [finiteDifference,strictLaplace,hW]; ring

lemma finiteDifference_three (θ h W : ℝ) :
    finiteDifference θ h 3 W=(strictLaplace θ W-3*strictLaplace (θ+h) W+
      3*strictLaplace (θ+2*h) W-strictLaplace (θ+3*h) W)/h^3 := by
  have h1 := strictLaplace_add_nat_mul θ h W 1
  have h2 := strictLaplace_add_nat_mul θ h W 2
  have h3 := strictLaplace_add_nat_mul θ h W 3
  norm_num only [Nat.cast_one,one_mul,pow_one,Nat.cast_ofNat] at h1 h2 h3
  rw [h1,h2,h3]
  by_cases hW : 0 < W <;> simp [finiteDifference,strictLaplace,hW]; ring

theorem reciprocal_difference_constants {ε : ℝ} (hε : 0 < ε) :
    (1-1/(1+ε))/ε = 1/(1+ε) ∧
    (1-2/(1+ε)+1/(1+2*ε))/ε^2 = 2/((1+ε)*(1+2*ε)) ∧
    (1-3/(1+ε)+3/(1+2*ε)-1/(1+3*ε))/ε^3 =
      6/((1+ε)*(1+2*ε)*(1+3*ε)) := by
  constructor
  · field_simp [hε.ne',show 1+ε ≠ 0 by positivity]; ring
  constructor
  · field_simp [hε.ne',show 1+ε ≠ 0 by positivity,show 1+2*ε ≠ 0 by positivity]; ring
  · field_simp [hε.ne',show 1+ε ≠ 0 by positivity,show 1+2*ε ≠ 0 by positivity,
      show 1+3*ε ≠ 0 by positivity]; ring

theorem actual_centered_tilt_Laplace
    {Ω : ℕ → Type u} [∀ m, MeasurableSpace (Ω m)]
    (μ : (m : ℕ) → Measure (Ω m)) [∀ m, IsProbabilityMeasure (μ m)]
    (X : (m : ℕ) → Ω m → ℝ) (u lam : ℕ → ℝ) (N : ℕ → ℕ)
    (hX : ∀ m, Measurable (X m))
    (hb : ∀ m, ∀ᵐ ω ∂μ m, X m ω ∈ Icc (0 : ℝ) 1)
    (hN : Tendsto N atTop atTop) {v : ℝ} (hv : 0 < v)
    (hvar : Tendsto (fun m => variance (X m)
      ((μ m).tilted (fun ω => u m*X m ω))) atTop (𝓝 v))
    (hlam : Tendsto lam atTop (𝓝 0))
    (hwindow : Tendsto (fun m => lam m*Real.sqrt ((N m : ℝ)*variance (X m)
      ((μ m).tilted (fun ω => u m*X m ω)))) atTop atTop) :
    Tendsto (fun m =>
      (∫ r, strictLaplace (lam m)
        ((N m : ℝ)*(∫ ω, X m ω ∂(μ m).tilted (fun ω => u m*X m ω))-
          iidSum (X m) (N m) r)
        ∂(Measure.pi (fun _ : Fin (N m) => μ m)).tilted
          (fun r => u m*iidSum (X m) (N m) r))*
      (lam m*Real.sqrt ((N m : ℝ)*variance (X m)
        ((μ m).tilted (fun ω => u m*X m ω))))) atTop (𝓝 φ0) := by
  let s : ℕ → ℝ := fun m => Real.sqrt ((N m : ℝ)*variance (X m)
    ((μ m).tilted (fun ω => u m*X m ω)))
  let c : ℕ → ℝ := fun m => (N m : ℝ)*(∫ ω, X m ω ∂(μ m).tilted (fun ω => u m*X m ω))
  let P := fun m => Measure.pi (fun _ : Fin (N m) => μ m)
  let ν := fun m => standardizedTiltedLaw (P m) (iidSum (X m) (N m)) (u m) (c m) (s m)
  have hs : Tendsto s atTop atTop :=
    Real.tendsto_sqrt_atTop.comp
      ((tendsto_natCast_atTop_atTop.comp hN).atTop_mul_pos hv hvar)
  haveI : ∀ m, IsProbabilityMeasure (ν m) := fun m =>
    isProbabilityMeasure_standardizedTiltedLaw (P m) (measurable_iidSum (hX m) (N m))
      (integrable_exp_mul_iidSum (μ m) (hX m) (hb m) (u m) (N m))
  obtain ⟨C,hC,hBE⟩ := exists_tilted_iid_uniform_bound.{u}
  have hCDF : ∀ᶠ m in atTop, ∀ z,
      |cdf (ν m) z-cdf (gaussianReal 0 1) z| ≤ C/s m := by
    filter_upwards [hs.eventually_gt_atTop 0] with m hsm
    exact hBE (μ m) (X m) (u m) (N m) (hX m) (hb m) hsm
  have hscaled : Tendsto (fun m => (C/s m)*(lam m*s m)) atTop (𝓝 0) := by
    apply (show Tendsto (fun m => C*lam m) atTop (𝓝 0) from by simpa using hlam.const_mul C).congr'
    filter_upwards [hs.eventually_gt_atTop 0] with m hsm
    field_simp [hsm.ne']
  have ht := strict_laplace_mul_tendsto_of_cdf ν (fun m => lam m*s m) (fun m => C/s m)
    hwindow hCDF hscaled
  apply ht.congr'
  filter_upwards [hs.eventually_gt_atTop 0] with m hsm
  congr 1
  dsimp only [ν]
  rw [standardizedTiltedLaw,integral_map
    (((measurable_iidSum (hX m) (N m)).sub_const (c m)).div_const (s m)).aemeasurable
      (measurable_strictNegativeHalfExp _).aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with r
  have he : (iidSum (X m) (N m) r-c m)/s m < 0 ↔
      0 < c m-iidSum (X m) (N m) r := by
    rw [div_lt_iff₀ hsm]
    constructor <;> intro h <;> linarith
  change strictNegativeHalfExp (lam m*s m) ((iidSum (X m) (N m) r-c m)/s m) =
    strictLaplace (lam m) (c m-iidSum (X m) (N m) r)
  by_cases hp : 0 < c m-iidSum (X m) (N m) r
  · have hz := he.mpr hp
    simp only [strictNegativeHalfExp,Set.indicator_of_mem (show
      (iidSum (X m) (N m) r-c m)/s m ∈ Iio (0 : ℝ) from hz),strictLaplace,if_pos hp]
    congr 1
    field_simp [hsm.ne']
    ring
  · have hz : ¬(iidSum (X m) (N m) r-c m)/s m < 0 := fun h => hp (he.mp h)
    simp only [strictNegativeHalfExp, strictLaplace, if_neg hp]
    exact Set.indicator_of_notMem (show
      (iidSum (X m) (N m) r-c m)/s m ∉ Iio (0 : ℝ) from hz) _

end FCAppendix.Affine.Uniform06.EntryLaplace
