import FCAppendix.Affine.Uniform06.EntryCentralRatio
import FCAppendix.Probability.ClippedSubGaussianMoments
import Mathlib.Probability.Moments.SubGaussian

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryUI
open MeasureTheory ProbabilityTheory Set Filter Topology
open FCAppendix.Probability
open FCAppendix.Affine.Uniform06
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem subgaussian_abs_tail {X : Ω → ℝ} {c : NNReal}
    (hX : HasSubgaussianMGF X c μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t < |X ω|} ≤ 2*Real.exp (-t^2/(2*(c : ℝ))) := by
  have hsub : {ω | t < |X ω|} ⊆ {ω | t ≤ X ω} ∪ {ω | t ≤ -X ω} := by
    intro ω hω
    change t < |X ω| at hω
    by_cases h : 0 ≤ X ω
    · left
      change t ≤ X ω
      simpa only [abs_of_nonneg h] using hω.le
    · right
      change t ≤ -X ω
      simpa only [abs_of_nonpos (le_of_not_ge h),neg_le_neg_iff] using hω.le
  have hp := (hX.measure_ge_le ht)
  have hn := (hX.neg.measure_ge_le ht)
  have hh := (measureReal_mono (μ := μ) hsub).trans (measureReal_union_le _ _)
  change μ.real {ω | t ≤ -X ω} ≤ _ at hn
  linarith

theorem subgaussian_fourth_moment {X : Ω → ℝ} (hm : Measurable X)
    (hX : HasSubgaussianMGF X 1 μ) :
    (∫ ω, (X ω)^4 ∂μ) ≤ 2*gaussianMomentConstant 4 2 := by
  have hi : Integrable (fun ω => |X ω|^4) μ := by
    simpa only [Real.norm_eq_abs] using
      (hX.memLp (4 : NNReal)).integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
  have ht := EntryCentralRatio.integrable_weighted_tail μ (fun ω => |X ω|)
    hm.abs (Eventually.of_forall fun _ => abs_nonneg _) 3 hi
  have hG : IntegrableOn (fun t : ℝ => t^3*Real.exp (-t^2/2)) (Ioi (0 : ℝ)) := by
    convert! integrable_gaussian_moment_weight (by norm_num : (1 : ℝ) ≤ 4)
      (by norm_num : (0 : ℝ)<2) using 1
    norm_num [Real.rpow_natCast]
  have hb : (∫ t in Ioi (0 : ℝ), μ.real {ω | t < |X ω|}*t^3) ≤
      2*(∫ t in Ioi (0 : ℝ), t^3*Real.exp (-t^2/2)) := by
    rw [← integral_const_mul]
    apply integral_mono_ae ht (hG.const_mul 2)
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t htp
    have hh := mul_le_mul_of_nonneg_right (subgaussian_abs_tail μ hX htp.le)
      (pow_nonneg htp.le 3)
    norm_num only [NNReal.coe_one,mul_one] at hh
    nlinarith
  have he := FCAppendix.PayOnce.EndpointMoments.integral_pow_eq_tail μ hm.abs.aemeasurable
    (Eventually.of_forall fun _ => abs_nonneg _) 3
  have ha (x : ℝ) : |x|^4=x^4 := by
    rw [show (4 : ℕ)=2*2 by norm_num,pow_mul,pow_mul,sq_abs]
  simp only [ha] at he
  norm_num only [Nat.cast_ofNat,show (3 : ℕ)+1=4 by norm_num] at he
  rw [he]
  have hGid : gaussianMomentConstant 4 2 =
      4*(∫ t : ℝ in Ioi 0, t^3*Real.exp (-t^2/2)) := by
    unfold gaussianMomentConstant
    norm_num only [show (4 : ℝ)-1=3 by norm_num,Real.rpow_natCast]
    simp only [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  rw [hGid]
  nlinarith

def normalizedSum {N : ℕ} (A : Fin N → Ω → ℝ) (ω : Ω) : ℝ :=
  (∑ i, A i ω)/Real.sqrt (N : ℝ)

lemma measurable_normalizedSum {N : ℕ} {A : Fin N → Ω → ℝ}
    (hm : ∀ i, Measurable (A i)) : Measurable (normalizedSum A) :=
  (Finset.measurable_sum _ (fun i _ => hm i)).div_const _

theorem normalizedSum_subgaussian {N : ℕ} (hN : 0 < N)
    (A : Fin N → Ω → ℝ) (hm : ∀ i, Measurable (A i))
    (hb : ∀ i, ∀ᵐ ω ∂μ, |A i ω| ≤ 1)
    (hz : ∀ i, ∫ ω, A i ω ∂μ=0) (hi : iIndepFun A μ) :
    HasSubgaussianMGF (normalizedSum A) 1 μ := by
  have hA (i : Fin N) : HasSubgaussianMGF (A i) 1 μ := by
    have hbb : ∀ᵐ ω ∂μ, A i ω ∈ Icc (-1 : ℝ) 1 := by
      filter_upwards [hb i] with ω hω
      exact abs_le.mp hω
    convert! hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (hm i).aemeasurable hbb (hz i)
      using 1
    norm_num
  have hsum : HasSubgaussianMGF (fun ω => ∑ i, A i ω) (N : NNReal) μ := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using
      HasSubgaussianMGF.sum_of_iIndepFun hi (s := Finset.univ) (fun i _ => hA i)
  have hr : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have hsc := hsum.const_mul (Real.sqrt (N : ℝ))⁻¹
  have hc : (NNReal.mk (((Real.sqrt (N : ℝ))⁻¹)^2) (sq_nonneg _))*(N : NNReal)=1 := by
    ext
    change ((Real.sqrt (N : ℝ))⁻¹)^2*(N : ℝ)=1
    have hs := Real.sq_sqrt (Nat.cast_nonneg N)
    field_simp [hr.ne']
    nlinarith
  change HasSubgaussianMGF (fun ω => (Real.sqrt (N:ℝ))⁻¹*(∑ i, A i ω))
    ((NNReal.mk (((Real.sqrt (N:ℝ))⁻¹)^2) (sq_nonneg _))*(N:NNReal)) μ at hsc
  rw [hc] at hsc
  convert! hsc using 1
  funext ω
  simp only [normalizedSum,div_eq_mul_inv]
  ring

theorem normalizedSum_fourth_moment {N : ℕ} (hN : 0 < N)
    (A : Fin N → Ω → ℝ) (hm : ∀ i, Measurable (A i))
    (hb : ∀ i, ∀ᵐ ω ∂μ, |A i ω| ≤ 1)
    (hz : ∀ i, ∫ ω, A i ω ∂μ=0) (hi : iIndepFun A μ) :
    (∫ ω, (normalizedSum A ω)^4 ∂μ) ≤ 2*gaussianMomentConstant 4 2 :=
  subgaussian_fourth_moment μ (measurable_normalizedSum hm)
    (normalizedSum_subgaussian μ hN A hm hb hz hi)

lemma positive_deficit_fourth_le {z X S : ℝ} (hS : 0 ≤ S) :
    (max (z-X-S) 0)^4 ≤ 8*z^4+8*X^4 := by
  have hmax : max (z-X-S) 0 ≤ |z|+|X| := by
    apply max_le
    · have hz := le_abs_self z
      have hx := neg_le_abs X
      linarith
    · positivity
  have hp := pow_le_pow_left₀ (le_max_right _ _) hmax 4
  have habsZ : |z|^4=z^4 := by
    rw [show (4 : ℕ)=2*2 by norm_num,pow_mul,pow_mul,sq_abs]
  have habsX : |X|^4=X^4 := by
    rw [show (4 : ℕ)=2*2 by norm_num,pow_mul,pow_mul,sq_abs]
  have hfour : (|z|+|X|)^4 ≤ 8*|z|^4+8*|X|^4 := by
    have h1 : (|z|+|X|)^2 ≤ 2*(|z|^2+|X|^2) := by nlinarith [sq_nonneg (|z|-|X|)]
    have h2 : (|z|^2+|X|^2)^2 ≤ 2*(|z|^4+|X|^4) := by
      nlinarith [sq_nonneg (|z|^2-|X|^2)]
    nlinarith [sq_nonneg ((|z|+|X|)^2-2*(|z|^2+|X|^2)),
      mul_nonneg (sub_nonneg.mpr h1) (show 0 ≤ 2*(|z|^2+|X|^2)+(|z|+|X|)^2 by positivity)]
  rw [habsZ,habsX] at hfour
  exact hp.trans hfour

theorem positive_deficit_fourth_bound {X S : Ω → ℝ}
    (hmX : Measurable X) (hmS : Measurable S) (hX : HasSubgaussianMGF X 1 μ)
    (hS : ∀ᵐ ω ∂μ, 0 ≤ S ω) (z : ℝ) :
    Integrable (fun ω => (max (z-X ω-S ω) 0)^4) μ ∧
    (∫ ω, (max (z-X ω-S ω) 0)^4 ∂μ) ≤
      8*z^4+16*gaussianMomentConstant 4 2 := by
  have hiX : Integrable (fun ω => (X ω)^4) μ := by
    have hh := (hX.memLp (4 : NNReal)).integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
    convert! hh using 1
    funext ω
    rw [Real.norm_eq_abs]
    simp only [show (4 : ℕ)=2*2 by norm_num,pow_mul,sq_abs]
  have hdom : Integrable (fun ω => 8*z^4+8*(X ω)^4) μ :=
    (integrable_const _).add (hiX.const_mul 8)
  have hF : Integrable (fun ω => (max (z-X ω-S ω) 0)^4) μ := by
    apply Integrable.mono' hdom
      ((((measurable_const.sub hmX).sub hmS).max measurable_const).pow_const 4).aestronglyMeasurable
    filter_upwards [hS] with ω hω
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (le_max_right _ _) 4)]
    exact positive_deficit_fourth_le hω
  refine ⟨hF,?_⟩
  have he := integral_mono_ae hF hdom (hS.mono fun _ h => positive_deficit_fourth_le h)
  rw [integral_add (integrable_const _) (hiX.const_mul 8),integral_const_mul,
    integral_const,probReal_univ,one_smul] at he
  rw [integral_const_mul] at he
  nlinarith [subgaussian_fourth_moment μ hmX hX]

theorem actual_normalized_deficit_fourth_bound {N : ℕ} (hN : 0 < N)
    (A : Fin N → Ω → ℝ) (hm : ∀ i, Measurable (A i))
    (hb : ∀ i, ∀ᵐ ω ∂μ, |A i ω| ≤ 1)
    (hz : ∀ i, ∫ ω, A i ω ∂μ=0) (hi : iIndepFun A μ)
    (S : Ω → ℝ) (hSm : Measurable S) (hS : ∀ᵐ ω ∂μ, 0 ≤ S ω) (z : ℝ) :
    Integrable (fun ω => (max (z-normalizedSum A ω-S ω) 0)^4) μ ∧
    (∫ ω, (max (z-normalizedSum A ω-S ω) 0)^4 ∂μ) ≤
      8*z^4+16*gaussianMomentConstant 4 2 :=
  positive_deficit_fourth_bound μ (measurable_normalizedSum hm) hSm
    (normalizedSum_subgaussian μ hN A hm hb hz hi) hS z

end FCAppendix.Affine.Uniform06.EntryUI
