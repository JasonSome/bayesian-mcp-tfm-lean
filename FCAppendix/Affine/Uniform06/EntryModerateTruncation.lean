import FCAppendix.Affine.Uniform06.EntryConditionalRelative
import FCAppendix.Affine.Uniform06.EntryWeightedLaplace

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryModerateTruncation
open MeasureTheory ProbabilityTheory Set Filter Topology
open FCAppendix.PiBinomial
open FCAppendix.Affine.WeightedSampling
open FCAppendix.Affine.Uniform06.EntryUntilting
open FCAppendix.Affine.Uniform06.EntryRenewal
open FCAppendix.Affine.Uniform06.EntryParity
open FCAppendix.Affine.Uniform06.EntryParityRenewal
open FCAppendix.Affine.Uniform06.EntryConditionalRelative
open FCAppendix.Affine.Uniform06.EntryLaplace
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma pathMoment_le_initial (w : Weights ι) (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i)
    (k d : ℕ) (S : Finset ι) (s : ℝ) : pathMoment w h k d S s ≤ deficitMoment k s := by
  apply expect_le_const
  intro p _
  apply deficitMoment_mono
  have hs := selectedSum_lower h hh d p
  simp only [zero_mul] at hs
  linarith

theorem stopped_coarse_bound (w : Weights ι) (h : ι → ℝ)
    {a : ℝ} (ha : 0 ≤ a) (hh : ∀ i, a ≤ h i)
    (n J k : ℕ) {e : ℕ} (he : e ≤ 1) {s : ℝ} (hs : s ≤ 2*a*J) :
    fairMoment w h (2*n+e) k s ≤
      2*pmf (2*n+e) (1/2) (n+e)*(J : ℝ)*deficitMoment k s := by
  let P := pmf (2*n+e) (1/2) (n+e)
  have hP : 0 ≤ P := half_pmf_nonneg _ _
  have hM := deficitMoment_nonneg k s
  have hterm (r : ℕ) : pmf (2*n+e) (1/2) (n+e+r)*pathMoment w h k (2*r+e) ∅ s ≤
      P*deficitMoment k s := by
    have hp : pmf (2*n+e) (1/2) (n+e+r) ≤ P := by
      rw [pmf_eq_ratio_mul_peak]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (upperRatio_le_one n he r) hP
    exact mul_le_mul hp (pathMoment_le_initial w h (fun i => ha.trans (hh i)) k _ ∅ s)
      (pathMoment_nonneg _ _ _ _ _ _) hP
  have hsum : (∑ r ∈ Finset.range (n+1),
      pmf (2*n+e) (1/2) (n+e+r)*pathMoment w h k (2*r+e) ∅ s) ≤
      (J : ℝ)*P*deficitMoment k s := by
    by_cases hJn : J ≤ n+1
    · rw [parity_sum_truncate w h ha hh n J k e hJn hs]
      have ht := Finset.sum_le_sum (fun r (_ : r ∈ Finset.range J) => hterm r)
      simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_assoc] using ht
    · have ht := Finset.sum_le_sum (fun r (_ : r ∈ Finset.range (n+1)) => hterm r)
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at ht
      have hJ : ((n+1 : ℕ) : ℝ) ≤ J := by exact_mod_cast (show n+1 ≤ J by omega)
      exact ht.trans (by nlinarith [mul_le_mul_of_nonneg_right hJ (mul_nonneg hP hM)])
  rw [fairMoment_parity_sum w h n k he s]
  have hcor : 0 ≤ if e=0 then pmf (2*n+e) (1/2) (n+e)*deficitMoment k s else 0 := by
    split_ifs <;> positivity
  dsimp [P] at *
  nlinarith

theorem actual_conditional_coarse_bound (w : Weights ι) (h : ι → ℝ)
    {a : ℝ} (ha : 0 < a) (hh : ∀ i, a ≤ h i) (H k : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    fairMoment w h H k s ≤
      2*Real.sqrt (2/((H : ℝ)+1))*(s/(2*a)+2)*deficitMoment k s := by
  have hbound (n e : ℕ) (he : e ≤ 1) :
      fairMoment w h (2*n+e) k s ≤
        2*Real.sqrt (2/(((2*n+e : ℕ) : ℝ)+1))*(s/(2*a)+2)*deficitMoment k s := by
    let J := stoppingPairs a s
    have hJ := stoppingPairs_bounds ha hs
    have hc := stopped_coarse_bound w h ha.le hh n J k he hJ.1
    have hP := pmf_half_le_sqrt (2*n+e) (n+e)
    have hM := deficitMoment_nonneg k s
    have hpeak := mul_le_mul_of_nonneg_right hP
      (show 0 ≤ 2*(J : ℝ)*deficitMoment k s by positivity)
    have hstop := mul_le_mul_of_nonneg_left hJ.2
      (show 0 ≤ 2*Real.sqrt (2/(((2*n+e : ℕ) : ℝ)+1))*deficitMoment k s by positivity)
    exact hc.trans (by nlinarith only [hpeak,hstop])
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' H
  · simpa only [Nat.add_zero] using hbound n 0 (by norm_num)
  · exact hbound n 1 (by norm_num)

lemma small_window_monomial {θ ε W : ℝ} (hθ : 0 < θ) (hε : 0 ≤ ε) (j : ℕ) :
    (if θ*W ≤ ε then weightedMonomial θ (j+1) W else 0) ≤
      (ε/θ)*weightedMonomial θ j W := by
  by_cases hW : 0 < W
  · by_cases hw : θ*W ≤ ε
    · simp only [if_pos hw,weightedMonomial,if_pos hW,pow_succ]
      have hdiv : W ≤ ε/θ := (le_div_iff₀ hθ).mpr (by nlinarith)
      have hh := mul_le_mul_of_nonneg_left hdiv (show 0 ≤ Real.exp (-θ*W)*W^j by positivity)
      nlinarith
    · simp [hw,weightedMonomial,hW]
      positivity
  · simp [weightedMonomial,hW]

lemma large_window_monomial {θ M W : ℝ} (_hθ : 0 < θ) (_hM : 0 ≤ M) (j : ℕ) :
    (if M ≤ θ*W then weightedMonomial θ j W else 0) ≤
      Real.exp (-M/2)*weightedMonomial (θ/2) j W := by
  by_cases hW : 0 < W
  · by_cases hw : M ≤ θ*W
    · simp only [if_pos hw,weightedMonomial,if_pos hW]
      have hexp : Real.exp (-θ*W) ≤ Real.exp (-M/2)*Real.exp (-(θ/2)*W) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by nlinarith)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hexp (pow_nonneg hW.le j)
    · simp [hw,weightedMonomial,hW]
      positivity
  · simp [weightedMonomial,hW]

section Integrals
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {W : Ω → ℝ} (hW : Measurable W)
include hW

theorem integral_small_window {θ ε : ℝ} (hθ : 0 < θ) (hε : 0 ≤ ε) (j : ℕ) :
    (∫ ω, if θ*W ω ≤ ε then weightedMonomial θ (j+1) (W ω) else 0 ∂μ) ≤
      (ε/θ)*(∫ ω, weightedMonomial θ j (W ω) ∂μ) := by
  have hi := EntryWeightedLaplace.integrable_weightedMonomial μ hW hθ (j+1)
  have his : Integrable (fun ω => if θ*W ω ≤ ε then weightedMonomial θ (j+1) (W ω) else 0) μ := by
    convert! hi.indicator (measurableSet_le (hW.const_mul θ) measurable_const) using 1
  rw [← integral_const_mul]
  exact integral_mono his ((EntryWeightedLaplace.integrable_weightedMonomial μ hW hθ j).const_mul _)
    (fun ω => small_window_monomial hθ hε j)

theorem integral_large_window {θ M : ℝ} (hθ : 0 < θ) (hM : 0 ≤ M) (j : ℕ) :
    (∫ ω, if M ≤ θ*W ω then weightedMonomial θ j (W ω) else 0 ∂μ) ≤
      Real.exp (-M/2)*(∫ ω, weightedMonomial (θ/2) j (W ω) ∂μ) := by
  have hi := EntryWeightedLaplace.integrable_weightedMonomial μ hW hθ j
  have his : Integrable (fun ω => if M ≤ θ*W ω then weightedMonomial θ j (W ω) else 0) μ := by
    convert! hi.indicator (measurableSet_le measurable_const (hW.const_mul θ)) using 1
  rw [← integral_const_mul]
  exact integral_mono his
    ((EntryWeightedLaplace.integrable_weightedMonomial μ hW (by positivity : 0 < θ/2) j).const_mul _)
    (fun ω => large_window_monomial hθ hM j)

end Integrals
end FCAppendix.Affine.Uniform06.EntryModerateTruncation
