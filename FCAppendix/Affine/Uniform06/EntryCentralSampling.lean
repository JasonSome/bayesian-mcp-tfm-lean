import FCAppendix.Affine.Uniform06.EntrySamplingLaw
import FCAppendix.Affine.Uniform06.EntryEmpiricalRatio
import FCAppendix.Affine.Uniform06.EntryUI

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryCentralSampling
open MeasureTheory ProbabilityTheory Set Filter Topology
open FCAppendix.Affine.WeightedSampling
open FCAppendix.Affine.Uniform06.WeightedMoments
open FCAppendix.Affine.Uniform06.EntrySamplingLaw
open scoped BigOperators

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] [Nonempty ι]

def centeredGuardedSample (w : Ω → Weights ι) (h : Ω → ι → ℝ) (d : Ω → ℕ)
    (c : ℝ) (x : Ω × unitInterval) : ℝ :=
  if c ≤ totalWeight (w x.1) then
    sampled w h d x-(d x.1 : ℝ)*weightedMean (w x.1) (h x.1) else 0

def guardedMean (w : Ω → Weights ι) (h : Ω → ι → ℝ) (c h0 : ℝ) (ω : Ω) : ℝ :=
  if c ≤ totalWeight (w ω) then weightedMean (w ω) (h ω) else h0

def guardedSample (w : Ω → Weights ι) (h : Ω → ι → ℝ) (d : Ω → ℕ)
    (c h0 : ℝ) (x : Ω × unitInterval) : ℝ :=
  if c ≤ totalWeight (w x.1) then sampled w h d x else (d x.1 : ℝ)*h0

omit [MeasurableSpace Ω] in
lemma guarded_decomposition (w : Ω → Weights ι) (h : Ω → ι → ℝ) (d : Ω → ℕ)
    (c h0 : ℝ) (x : Ω × unitInterval) :
    guardedSample w h d c h0 x-(d x.1 : ℝ)*h0=
      centeredGuardedSample w h d c x+(d x.1 : ℝ)*(guardedMean w h c h0 x.1-h0) := by
  unfold guardedSample centeredGuardedSample guardedMean
  split_ifs <;> ring

omit [DecidableEq ι] [Nonempty ι] in
lemma measurable_guardedMean (w : Ω → Weights ι) (h : Ω → ι → ℝ)
    (hw : Measurable w) (hh : Measurable h) (c h0 : ℝ) :
    Measurable (guardedMean w h c h0) := by
  exact Measurable.ite
    (measurableSet_le measurable_const (continuous_totalWeight.measurable.comp hw))
    (measurable_weightedMean.comp (hw.prodMk hh)) measurable_const

lemma measurable_centeredGuardedSample (w : Ω → Weights ι) (h : Ω → ι → ℝ) (d : Ω → ℕ)
    (hw : Measurable w) (hh : Measurable h) (hd : Measurable d) (c : ℝ) :
    Measurable (centeredGuardedSample w h d c) := by
  exact Measurable.ite
    (measurableSet_le measurable_const (continuous_totalWeight.measurable.comp (hw.comp measurable_fst)))
    (measurable_error w h d hw hh hd) measurable_const

lemma measurable_guardedSample (w : Ω → Weights ι) (h : Ω → ι → ℝ) (d : Ω → ℕ)
    (hw : Measurable w) (hh : Measurable h) (hd : Measurable d) (c h0 : ℝ) :
    Measurable (guardedSample w h d c h0) := by
  exact Measurable.ite
    (measurableSet_le measurable_const (continuous_totalWeight.measurable.comp (hw.comp measurable_fst)))
    (measurable_sampled w h d hw hh hd) (((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp (hd.comp measurable_fst)).mul_const h0)

omit [MeasurableSpace Ω] in
lemma centeredGuardedSample_abs_le (w : Ω → Weights ι) (h : Ω → ι → ℝ) (d : Ω → ℕ)
    {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c) (hh : ∀ ω i, |h ω i| ≤ A)
    (x : Ω × unitInterval) : |centeredGuardedSample w h d c x| ≤ 2*A*d x.1 := by
  unfold centeredGuardedSample
  split_ifs with hg
  · exact abs_centeredSum_le (w x.1) (h x.1) hA (hh x.1) (hc.trans_le hg) _ _
  · simp
    positivity

omit [MeasurableSpace Ω] in
lemma guardedMean_abs_le (w : Ω → Weights ι) (h : Ω → ι → ℝ)
    {A c h0 : ℝ} (hc : 0 < c) (hh : ∀ ω i, |h ω i| ≤ A) (h0b : |h0| ≤ A) (ω : Ω) :
    |guardedMean w h c h0 ω| ≤ A := by
  unfold guardedMean
  split_ifs with hg
  · exact abs_weightedMean_le _ _ (hh ω) (hc.trans_le hg)
  · exact h0b

omit [MeasurableSpace Ω] in
lemma conditional_centered_second (w : Ω → Weights ι) (h : Ω → ι → ℝ) (d : Ω → ℕ)
    {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c) (hh : ∀ ω i, |h ω i| ≤ A) (ω : Ω) :
    (∫ u : unitInterval, (centeredGuardedSample w h d c (ω,u))^2) ≤
      8*A^2*d ω+32*A^2/c^2*(d ω : ℝ)^4 := by
  by_cases hg : c ≤ totalWeight (w ω)
  · simp only [centeredGuardedSample,if_pos hg]
    change (∫ u : unitInterval, (fun p : Path ι (d ω) =>
      (selectedSum (h ω) (d ω) p-(d ω : ℝ)*weightedMean (w ω) (h ω))^2)
      (sampler (d ω) (w ω) u)) ≤ _
    rw [integral_sampler_test (w ω) (d ω) (fun p : Path ι (d ω) =>
      (selectedSum (h ω) (d ω) p-(d ω:ℝ)*weightedMean (w ω) (h ω))^2)]
    apply (sampling_second_moment_all (w ω) (h ω) hA (hh ω) (d ω) (hc.trans_le hg)).trans
    have hden : c^2 ≤ (totalWeight (w ω))^2 := by nlinarith
    have ht := div_le_div_of_nonneg_left (show 0 ≤ 32*A^2*(d ω : ℝ)^4 by positivity)
      (sq_pos_of_pos hc) hden
    have ht' : 32*A^2*(d ω:ℝ)^4/(totalWeight (w ω))^2 ≤
        32*A^2/c^2*(d ω:ℝ)^4 := by
      convert! ht using 1
      ring
    exact add_le_add le_rfl ht'
  · simp only [centeredGuardedSample,if_neg hg,zero_pow (by decide : (2:ℕ)≠0),integral_zero]
    positivity

theorem actual_guarded_sampling_second (μ : Measure Ω) [IsProbabilityMeasure μ]
    (w : Ω → Weights ι) (h : Ω → ι → ℝ) (d : Ω → ℕ)
    (hw : Measurable w) (hmh : Measurable h) (hd : Measurable d)
    {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c) (hh : ∀ ω i, |h ω i| ≤ A)
    (D : ℕ) (hD : ∀ ω, d ω ≤ D) :
    (∫ x, (centeredGuardedSample w h d c x)^2 ∂μ.prod volume) ≤
      8*A^2*(∫ ω, (d ω : ℝ) ∂μ)+32*A^2/c^2*(∫ ω, (d ω : ℝ)^4 ∂μ) := by
  have hI : Integrable (fun x => (centeredGuardedSample w h d c x)^2) (μ.prod volume) := by
    apply Integrable.of_bound ((measurable_centeredGuardedSample w h d hw hmh hd c).pow_const 2).aestronglyMeasurable
      ((2*A*D)^2)
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),← sq_abs]
      apply pow_le_pow_left₀ (abs_nonneg _)
      exact (centeredGuardedSample_abs_le w h d hA hc hh x).trans
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hD x.1) (by positivity))
  have hdLp : MemLp (fun ω => (d ω : ℝ)) 4 μ :=
    MemLp.of_bound ((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp hd).aestronglyMeasurable D
      (Eventually.of_forall fun ω => by simpa using (show (d ω : ℝ) ≤ D by exact_mod_cast hD ω))
  have hd1 := hdLp.integrable (by norm_num)
  have hd4 : Integrable (fun ω => (d ω : ℝ)^4) μ := by
    have hh := hdLp.integrable_norm_pow (by norm_num : (4:ℕ)≠0)
    convert! hh using 1
    funext ω
    rw [Real.norm_eq_abs,abs_of_nonneg (show (0:ℝ) ≤ d ω from Nat.cast_nonneg _)]
  rw [integral_prod _ hI]
  have hR : Integrable (fun ω => 8*A^2*(d ω : ℝ)+32*A^2/c^2*(d ω : ℝ)^4) μ :=
    (hd1.const_mul _).add (hd4.const_mul _)
  have he := integral_mono hI.integral_prod_left hR
    (conditional_centered_second w h d hA hc hh)
  rw [integral_add (hd1.const_mul _) (hd4.const_mul _),integral_const_mul,integral_const_mul] at he
  exact he

lemma abs_le_one_add_fourth (x : ℝ) : |x| ≤ 1+x^4 := by
  by_cases hx : |x| ≤ 1
  · nlinarith [sq_nonneg (x^2)]
  · have h1 : 1 ≤ |x| := (lt_of_not_ge hx).le
    have h2 : |x| ≤ |x|^2 := by nlinarith [mul_nonneg (abs_nonneg x) (sub_nonneg.mpr h1)]
    have h4 : |x|^2 ≤ |x|^4 := by nlinarith [mul_nonneg (sq_nonneg |x|) (show 0 ≤ |x|^2-1 by nlinarith)]
    have he : |x|^4=x^4 := by rw [show (4:ℕ)=2*2 by norm_num,pow_mul,pow_mul,sq_abs]
    rw [he] at h4
    linarith

theorem physical_draw_moments (μ : Measure Ω) [IsProbabilityMeasure μ]
    {N : ℕ} (hN : 0 < N) (Y : Fin N → Ω → ℝ)
    (hmY : ∀ i, Measurable (Y i)) (hbY : ∀ i, ∀ᵐ ω ∂μ, |Y i ω| ≤ 1)
    (hzY : ∀ i, ∫ ω, Y i ω ∂μ=0) (hiY : iIndepFun Y μ)
    (d : Ω → ℕ) (_hd : Measurable d) (_hD : ∀ ω, d ω ≤ N)
    (hcount : ∀ ω, (d ω : ℝ)=|∑ i, Y i ω|) :
    (∫ ω, (d ω : ℝ) ∂μ) ≤ Real.sqrt (N : ℝ)*(1+2*FCAppendix.Probability.gaussianMomentConstant 4 2) ∧
    (∫ ω, (d ω : ℝ)^4 ∂μ) ≤ (N : ℝ)^2*(2*FCAppendix.Probability.gaussianMomentConstant 4 2) := by
  let Z := EntryUI.normalizedSum Y
  have hZ := EntryUI.normalizedSum_subgaussian μ hN Y hmY hbY hzY hiY
  have hZ4 := EntryUI.normalizedSum_fourth_moment μ hN Y hmY hbY hzY hiY
  have hr : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have he (ω : Ω) : (d ω : ℝ)=Real.sqrt (N : ℝ)*|Z ω| := by
    rw [hcount]
    change |∑ i, Y i ω| = Real.sqrt (N:ℝ)*|(∑ i,Y i ω)/Real.sqrt (N:ℝ)|
    rw [abs_div,abs_of_pos hr]
    field_simp [hr.ne']
  have h4 (ω : Ω) : (d ω : ℝ)^4=(N : ℝ)^2*(Z ω)^4 := by
    rw [he,mul_pow]
    have hs : (Real.sqrt (N:ℝ))^4=(N:ℝ)^2 := by
      rw [show (4:ℕ)=2*2 by norm_num,pow_mul,Real.sq_sqrt (Nat.cast_nonneg N)]
    rw [hs]
    simp only [show (4:ℕ)=2*2 by norm_num,pow_mul,sq_abs]
  have hZi : Integrable (fun ω => |Z ω|) μ := (hZ.memLp 4).abs.integrable (by norm_num)
  have hZ4i : Integrable (fun ω => (Z ω)^4) μ := by
    have hh := (hZ.memLp 4).integrable_norm_pow (by norm_num : (4:ℕ)≠0)
    convert! hh using 1
    funext ω
    change (Z ω)^4=|Z ω|^4
    simp only [show (4:ℕ)=2*2 by norm_num,pow_mul,sq_abs]
  have hfirst : (∫ ω, |Z ω| ∂μ) ≤ 1+2*FCAppendix.Probability.gaussianMomentConstant 4 2 := by
    have h := integral_mono hZi ((integrable_const (1:ℝ)).add hZ4i) (fun ω => abs_le_one_add_fourth (Z ω))
    simp only [Pi.add_apply] at h
    rw [integral_add (integrable_const _) hZ4i,integral_const,probReal_univ,one_smul] at h
    linarith
  constructor
  · simp_rw [he]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hfirst hr.le
  · simp_rw [h4]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hZ4 (sq_nonneg _)

lemma dependent_product_bound {Z e δ : ℝ} (hδ : 0 < δ) :
    Z^2*e^2 ≤ δ*Z^4+e^4/(4*δ) := by
  have hs := sq_nonneg (2*δ*Z^2-e^2)
  have hdiv : Z^2*e^2 ≤ (4*δ^2*Z^4+e^4)/(4*δ) := by
    apply (le_div_iff₀ (show 0 < 4*δ by positivity)).mpr
    nlinarith
  convert! hdiv using 1
  field_simp [hδ.ne']

end FCAppendix.Affine.Uniform06.EntryCentralSampling
