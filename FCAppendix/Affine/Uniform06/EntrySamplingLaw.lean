import FCAppendix.Affine.Uniform06.WeightedMoments
import FCAppendix.Proposer.LotterySupport
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntrySamplingLaw
open MeasureTheory Set Filter
open FCAppendix.Affine.WeightedSampling
open FCAppendix.Affine.Uniform06.WeightedMoments
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

private theorem integral_finiteLaw {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (P : FiniteLaw α) (f : α → ℝ) :
    (∫ a, f a ∂FiniteLaw.probabilityMeasure P)=P.expect f := by
  have he : FiniteLaw.ofMeasure (FiniteLaw.probabilityMeasure P) id measurable_id=P :=
    FiniteLaw.ofMeasure_eq_of_map_eq_probabilityMeasure (FiniteLaw.probabilityMeasure P) id measurable_id P Measure.map_id
  calc
    _ = (FiniteLaw.ofMeasure (FiniteLaw.probabilityMeasure P) id measurable_id).expect f :=
      (FiniteLaw.expect_ofMeasure (FiniteLaw.probabilityMeasure P) id measurable_id f).symm
    _ = _ := congrArg (fun Q : FiniteLaw α => Q.expect f) he

def sampler (n : ℕ) : Weights ι → unitInterval → Path ι n :=
  Classical.choose (exists_weighted_sampler (ι := ι) n ∅)

lemma measurable_sampler (n : ℕ) : Measurable (Function.uncurry (sampler (ι := ι) n)) :=
  (Classical.choose_spec (exists_weighted_sampler (ι := ι) n ∅)).1

lemma sampler_law (n : ℕ) (w : Weights ι) :
    volume.map (sampler n w)=FiniteLaw.probabilityMeasure (pathLaw w n ∅) :=
  (Classical.choose_spec (exists_weighted_sampler (ι := ι) n ∅)).2 w

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
lemma measurable_selectedSum_fixed_path (n : ℕ) (p : Path ι n) :
    Measurable (fun h : ι → ℝ => selectedSum h n p) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact (measurable_pi_apply p.1).add (ih p.2)

omit [DecidableEq ι] [Nonempty ι] in
lemma measurable_selectedSum (n : ℕ) :
    Measurable (fun x : (ι → ℝ) × Path ι n => selectedSum x.1 n x.2) :=
  measurable_from_prod_countable_left (measurable_selectedSum_fixed_path n)

omit [DecidableEq ι] [Nonempty ι] in
lemma measurable_weightedMean :
    Measurable (fun x : Weights ι × (ι → ℝ) => weightedMean x.1 x.2) := by
  unfold weightedMean
  apply Measurable.div
  · apply Finset.measurable_sum
    intro i _
    exact ((measurable_pi_apply i).comp measurable_fst.subtype_val).mul
      ((measurable_pi_apply i).comp measurable_snd)
  · exact continuous_totalWeight.measurable.comp measurable_fst

variable {Ω : Type*} [MeasurableSpace Ω]

def sampled (w : Ω → Weights ι) (h : Ω → ι → ℝ) (d : Ω → ℕ)
    (x : Ω × unitInterval) : ℝ :=
  selectedSum (h x.1) (d x.1) (sampler (d x.1) (w x.1) x.2)

def error (w : Ω → Weights ι) (h : Ω → ι → ℝ) (d : Ω → ℕ)
    (x : Ω × unitInterval) : ℝ :=
  sampled w h d x-(d x.1 : ℝ)*weightedMean (w x.1) (h x.1)

lemma measurable_sampled (w : Ω → Weights ι) (h : Ω → ι → ℝ) (d : Ω → ℕ)
    (hw : Measurable w) (hh : Measurable h) (hd : Measurable d) :
    Measurable (sampled w h d) := by
  have hm (n : ℕ) : Measurable (fun x : Ω × unitInterval =>
      selectedSum (h x.1) n (sampler n (w x.1) x.2)) :=
    (measurable_selectedSum n).comp
      ((hh.comp measurable_fst).prodMk
        ((measurable_sampler n).comp ((hw.comp measurable_fst).prodMk measurable_snd)))
  exact (measurable_from_prod_countable_right (f := fun x : ℕ × (Ω × unitInterval) =>
      selectedSum (h x.2.1) x.1 (sampler x.1 (w x.2.1) x.2.2)) hm).comp
    ((hd.comp measurable_fst).prodMk measurable_id)

lemma measurable_error (w : Ω → Weights ι) (h : Ω → ι → ℝ) (d : Ω → ℕ)
    (hw : Measurable w) (hh : Measurable h) (hd : Measurable d) :
    Measurable (error w h d) :=
  (measurable_sampled w h d hw hh hd).sub
    (((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (hd.comp measurable_fst)).mul
      (measurable_weightedMean.comp ((hw.comp measurable_fst).prodMk (hh.comp measurable_fst))))

theorem integral_sampler_test (w : Weights ι) (n : ℕ) (f : Path ι n → ℝ) :
    (∫ u : unitInterval, f (sampler n w u))=(pathLaw w n ∅).expect f := by
  have hm : Measurable (sampler n w) :=
    (measurable_sampler n).comp (measurable_const.prodMk measurable_id)
  rw [← integral_map hm.aemeasurable (measurable_of_countable f).aestronglyMeasurable,
    sampler_law,integral_finiteLaw]

omit [MeasurableSpace Ω] in
lemma abs_error_le (w : Ω → Weights ι) (h : Ω → ι → ℝ) (d : Ω → ℕ)
    {A : ℝ} (hA : 0 ≤ A) (hh : ∀ ω i, |h ω i| ≤ A)
    (hW : ∀ ω, 0 < totalWeight (w ω)) (x : Ω × unitInterval) :
    |error w h d x| ≤ 2*A*d x.1 :=
  abs_centeredSum_le (w x.1) (h x.1) hA (hh x.1) (hW x.1) _ _

omit [MeasurableSpace Ω] in

theorem conditional_moments (w : Ω → Weights ι) (h : Ω → ι → ℝ) (d : Ω → ℕ)
    {A : ℝ} (hA : 0 ≤ A) (hh : ∀ ω i, |h ω i| ≤ A)
    (hW : ∀ ω, 0 < totalWeight (w ω)) (ω : Ω) :
    |∫ u : unitInterval, error w h d (ω,u)| ≤
      4*A*(d ω : ℝ)^2/totalWeight (w ω) ∧
    (∫ u : unitInterval, (error w h d (ω,u))^2) ≤
      8*A^2*d ω+32*A^2*(d ω : ℝ)^4/(totalWeight (w ω))^2 := by
  constructor
  · change |∫ u : unitInterval, (fun p : Path ι (d ω) =>
      selectedSum (h ω) (d ω) p-(d ω : ℝ)*weightedMean (w ω) (h ω))
        (sampler (d ω) (w ω) u)| ≤ _
    have he := integral_sampler_test (w ω) (d ω) (fun p =>
      selectedSum (h ω) (d ω) p-(d ω : ℝ)*weightedMean (w ω) (h ω))
    convert! (sampling_mean_bound_all (w ω) (h ω) hA (hh ω) (d ω) (hW ω)) using 1
    rw [he, expect_sub, expect_const]
  · change (∫ u : unitInterval, (fun p : Path ι (d ω) =>
      (selectedSum (h ω) (d ω) p-(d ω : ℝ)*weightedMean (w ω) (h ω))^2)
        (sampler (d ω) (w ω) u)) ≤ _
    have he := integral_sampler_test (w ω) (d ω) (fun p =>
      (selectedSum (h ω) (d ω) p-(d ω : ℝ)*weightedMean (w ω) (h ω))^2)
    convert! (sampling_second_moment_all (w ω) (h ω) hA (hh ω) (d ω) (hW ω)) using 1

variable (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma integrable_error (w : Ω → Weights ι) (h : Ω → ι → ℝ) (d : Ω → ℕ)
    (hw : Measurable w) (hhm : Measurable h) (hd : Measurable d)
    {A : ℝ} (hA : 0 ≤ A) (hh : ∀ ω i, |h ω i| ≤ A)
    (hW : ∀ ω, 0 < totalWeight (w ω)) (D : ℕ) (hD : ∀ ω, d ω ≤ D) :
    Integrable (error w h d) (μ.prod volume) := by
  apply Integrable.of_bound (measurable_error w h d hw hhm hd).aestronglyMeasurable (2*A*D)
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]
    exact (abs_error_le w h d hA hh hW x).trans
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hD x.1) (by positivity))

lemma integrable_error_sq (w : Ω → Weights ι) (h : Ω → ι → ℝ) (d : Ω → ℕ)
    (hw : Measurable w) (hhm : Measurable h) (hd : Measurable d)
    {A : ℝ} (hA : 0 ≤ A) (hh : ∀ ω i, |h ω i| ≤ A)
    (hW : ∀ ω, 0 < totalWeight (w ω)) (D : ℕ) (hD : ∀ ω, d ω ≤ D) :
    Integrable (fun x => (error w h d x)^2) (μ.prod volume) := by
  apply Integrable.of_bound (C := (2*A*D)^2)
    ((measurable_error w h d hw hhm hd).pow_const 2).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _)
      ((abs_error_le w h d hA hh hW x).trans
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hD x.1) (by positivity))) 2

theorem integrated_second_moment (w : Ω → Weights ι) (h : Ω → ι → ℝ)
    (d : Ω → ℕ) (hw : Measurable w) (hhm : Measurable h) (hd : Measurable d)
    {A w0 : ℝ} (hA : 0 ≤ A) (hw0 : 0 < w0) (hh : ∀ ω i, |h ω i| ≤ A)
    (hW : ∀ ω, w0 ≤ totalWeight (w ω)) (D : ℕ) (hD : ∀ ω, d ω ≤ D) :
    (∫ x, (error w h d x)^2 ∂μ.prod volume) ≤
      8*A^2*(∫ ω, (d ω : ℝ) ∂μ)+32*A^2/w0^2*(∫ ω, (d ω : ℝ)^4 ∂μ) := by
  have hWp (ω : Ω) : 0 < totalWeight (w ω) := hw0.trans_le (hW ω)
  have hI := integrable_error_sq μ w h d hw hhm hd hA hh hWp D hD
  have hdI : Integrable (fun ω => (d ω : ℝ)) μ := by
    apply Integrable.of_bound ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hd).aestronglyMeasurable (D : ℝ)
    exact Eventually.of_forall fun ω => by simpa using (show (d ω : ℝ) ≤ D by exact_mod_cast hD ω)
  have hd4 : Integrable (fun ω => (d ω : ℝ)^4) μ := by
    apply Integrable.of_bound (C := (D : ℝ)^4)
      (((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hd).pow_const 4).aestronglyMeasurable
    exact Eventually.of_forall fun ω => by
      change |(d ω : ℝ)^4| ≤ (D : ℝ)^4
      rw [abs_of_nonneg (by positivity : 0 ≤ (d ω : ℝ)^4)]
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hD ω) 4
  rw [integral_prod _ hI]
  have hhI : Integrable (fun ω => ∫ u : unitInterval, (error w h d (ω,u))^2) μ :=
    hI.integral_prod_left
  have hR : Integrable (fun ω => 8*A^2*(d ω : ℝ)+32*A^2/w0^2*(d ω : ℝ)^4) μ :=
    (hdI.const_mul _).add (hd4.const_mul _)
  calc
    _ ≤ ∫ ω, 8*A^2*(d ω : ℝ)+32*A^2/w0^2*(d ω : ℝ)^4 ∂μ := by
      apply integral_mono_ae hhI hR
      exact Eventually.of_forall fun ω => by
        apply (conditional_moments w h d hA hh hWp ω).2.trans
        have hden : w0^2 ≤ totalWeight (w ω)^2 := by nlinarith [hW ω]
        have hhdiv := div_le_div_of_nonneg_left
          (show 0 ≤ 32*A^2*(d ω : ℝ)^4 by positivity) (sq_pos_of_pos hw0) hden
        have heq : 32*A^2*(d ω : ℝ)^4/w0^2 = 32*A^2/w0^2*(d ω : ℝ)^4 := by ring
        rw [heq] at hhdiv
        exact add_le_add_right hhdiv _
    _ = _ := by rw [integral_add (hdI.const_mul _) (hd4.const_mul _),
        integral_const_mul,integral_const_mul]

omit [IsProbabilityMeasure μ]

theorem transport_joint_law {Ξ : Type*} [MeasurableSpace Ξ]
    (ν : Measure Ξ) (L : Ξ → Ω) (U : Ξ → unitInterval)
    (hL : Measurable L) (hU : Measurable U)
    (hlaw : ν.map (fun x => (L x,U x))=μ.prod volume)
    (w : Ω → Weights ι) (h : Ω → ι → ℝ) (d : Ω → ℕ)
    (hw : Measurable w) (hh : Measurable h) (hd : Measurable d) :
    ν.map (fun x => sampled w h d (L x,U x))=(μ.prod volume).map (sampled w h d) := by
  rw [← hlaw,Measure.map_map (measurable_sampled w h d hw hh hd) (hL.prodMk hU)]
  rfl

theorem transport_joint_integral {Ξ : Type*} [MeasurableSpace Ξ]
    (ν : Measure Ξ) (L : Ξ → Ω) (U : Ξ → unitInterval)
    (hL : Measurable L) (hU : Measurable U)
    (hlaw : ν.map (fun x => (L x,U x))=μ.prod volume)
    (F : Ω × unitInterval → ℝ) (hF : Measurable F) :
    (∫ x, F (L x,U x) ∂ν)=∫ x, F x ∂μ.prod volume := by
  rw [← hlaw,integral_map (hL.prodMk hU).aemeasurable hF.aestronglyMeasurable]

end FCAppendix.Affine.Uniform06.EntrySamplingLaw
