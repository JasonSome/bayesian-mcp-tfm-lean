import FCAppendix.Affine.Uniform06.MixedCharacteristicGap
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.UniformSpace.Equicontinuity

noncomputable section

namespace FCAppendix.Affine.Uniform06.CharacteristicWeakConvergence

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open CharacteristicExpansion MixedCharacteristicGap
open FCAppendix.Affine.Uniform07

lemma hasDerivAt_phase (x : ℝ) : HasDerivAt phase (phase x * Complex.I) x := by
  convert! ((hasDerivAt_id x).ofReal_comp.mul_const Complex.I).cexp using 1
  simp [phase]

theorem phase_difference (u v : ℝ) : ‖phase u - phase v‖ ≤ |u - v| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := phase) (f' := fun x => phase x * Complex.I) (C := (1 : ℝ))
    (s := (Set.univ : Set ℝ))
    (fun x _ => (hasDerivAt_phase x).hasDerivWithinAt)
    (fun x _ => by simp only [norm_mul, norm_phase, Complex.norm_I, one_mul]; rfl)
    convex_univ (mem_univ v) (mem_univ u)
  simpa only [one_mul, Real.norm_eq_abs] using h

theorem jointPhase_difference {p : Pair}
    (hp : |p.1| ≤ 1 ∧ |p.2| ≤ 1) (q r : Pair) :
    ‖jointPhase q p - jointPhase r p‖ ≤ 2 * dist q r := by
  have h1 : |q.1 - r.1| ≤ dist q r := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact le_max_left _ _
  have h2 : |q.2 - r.2| ≤ dist q r := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact le_max_right _ _
  calc
    ‖jointPhase q p - jointPhase r p‖ ≤
        |(q.1 * p.1 + q.2 * p.2) - (r.1 * p.1 + r.2 * p.2)| :=
      phase_difference _ _
    _ = |(q.1 - r.1) * p.1 + (q.2 - r.2) * p.2| := by congr 1; ring
    _ ≤ |q.1 - r.1| * |p.1| + |q.2 - r.2| * |p.2| := by
      simpa only [abs_mul] using
        abs_add_le ((q.1 - r.1) * p.1) ((q.2 - r.2) * p.2)
    _ ≤ dist q r * 1 + dist q r * 1 :=
      add_le_add (mul_le_mul h1 hp.1 (abs_nonneg _) dist_nonneg)
        (mul_le_mul h2 hp.2 (abs_nonneg _) dist_nonneg)
    _ = 2 * dist q r := by ring

theorem jointCharacteristic_difference (μ : Measure Pair) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ p ∂μ, |p.1| ≤ 1 ∧ |p.2| ≤ 1) (q r : Pair) :
    ‖jointCharacteristic μ q - jointCharacteristic μ r‖ ≤ 2 * dist q r := by
  have hq : Integrable (jointPhase q) μ :=
    integrable_phase μ (by fun_prop)
  have hr : Integrable (jointPhase r) μ :=
    integrable_phase μ (by fun_prop)
  change ‖(∫ p, jointPhase q p ∂μ) - (∫ p, jointPhase r p ∂μ)‖ ≤ _
  rw [← integral_sub hq hr]
  calc
    ‖∫ p, jointPhase q p - jointPhase r p ∂μ‖ ≤
        ∫ p, ‖jointPhase q p - jointPhase r p‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ _ : Pair, 2 * dist q r ∂μ := by
      apply integral_mono_ae (hq.sub hr).norm (integrable_const _)
      exact hμ.mono fun p hp => jointPhase_difference hp q r
    _ = 2 * dist q r := by simp

theorem lipschitz_jointCharacteristic (μ : Measure Pair) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ p ∂μ, |p.1| ≤ 1 ∧ |p.2| ≤ 1) :
    LipschitzWith (2 : NNReal) (jointCharacteristic μ) := by
  apply LipschitzWith.of_dist_le_mul
  intro q r
  rw [dist_eq_norm]
  norm_num only [NNReal.coe_ofNat]
  exact jointCharacteristic_difference μ hμ q r

def jointPhaseBCF (q : Pair) : BoundedContinuousFunction Pair ℂ where
  toFun := jointPhase q
  continuous_toFun := continuous_jointPhase_right q
  map_bounded' := by
    refine ⟨2, ?_⟩
    intro p r
    calc
      dist (jointPhase q p) (jointPhase q r) =
          ‖jointPhase q p - jointPhase q r‖ := dist_eq_norm _ _
      _ ≤ ‖jointPhase q p‖ + ‖jointPhase q r‖ := norm_sub_le _ _
      _ = 2 := by norm_num

theorem tendsto_jointCharacteristic {P : ℕ → ProbabilityMeasure Pair}
    {P₀ : ProbabilityMeasure Pair} (hweak : Tendsto P atTop (𝓝 P₀)) (q : Pair) :
    Tendsto (fun n => jointCharacteristic (P n : Measure Pair) q)
      atTop (𝓝 (jointCharacteristic (P₀ : Measure Pair) q)) := by
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp
    hweak (jointPhaseBCF q)

theorem tendstoUniformlyOn_jointCharacteristic {P : ℕ → ProbabilityMeasure Pair}
    {P₀ : ProbabilityMeasure Pair}
    (hP : ∀ n, ∀ᵐ p ∂(P n : Measure Pair), |p.1| ≤ 1 ∧ |p.2| ≤ 1)
    (hweak : Tendsto P atTop (𝓝 P₀)) {K : Set Pair} (hK : IsCompact K) :
    TendstoUniformlyOn (fun n => jointCharacteristic (P n : Measure Pair))
      (jointCharacteristic (P₀ : Measure Pair)) atTop K := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hLipK : ∀ n, LipschitzWith (2 : NNReal)
      (fun q : K => jointCharacteristic (P n : Measure Pair) q) := by
    intro n
    exact LipschitzWith.of_dist_le_mul fun q r =>
      (lipschitz_jointCharacteristic (P n : Measure Pair) (hP n)).dist_le_mul q r
  have hEqui := (LipschitzWith.uniformEquicontinuous _ (2 : NNReal) hLipK).equicontinuous
  have h := (hEqui.tendsto_uniformFun_iff_pi atTop
      (fun q : K => jointCharacteristic (P₀ : Measure Pair) q)).mpr
    (tendsto_pi_nhds.mpr fun q => tendsto_jointCharacteristic hweak q)
  exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
    (UniformFun.tendsto_iff_tendstoUniformly.mp h)

theorem eventual_source_gap_of_weak_convergence (i : Row) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {P : ℕ → ProbabilityMeasure Pair}
    {P₀ : ProbabilityMeasure Pair}
    (hP : ∀ n, ∀ᵐ p ∂(P n : Measure Pair), |p.1| ≤ 1 ∧ |p.2| ≤ 1)
    (hweak : Tendsto P atTop (𝓝 P₀))
    (hback : MixedLaw.law i μ ≪ (P₀ : Measure Pair))
    {a b : ℝ} (hab : a < b) (hcomponent : volume.restrict (Ioo a b) ≪ μ)
    {K : Set Pair} (hK : IsCompact K)
    (hstrip : ∀ q ∈ K, q.2 ∈ Icc (-Real.pi) Real.pi)
    (hzero : (0 : Pair) ∉ K) :
    ∃ δ : ℝ, 0 ≤ δ ∧ δ < 1 ∧
      ∀ᶠ n in atTop, ∀ q ∈ K, ‖jointCharacteristic (P n : Measure Pair) q‖ ≤ δ := by
  apply eventual_gap_of_uniform_convergence hK
    (continuous_jointCharacteristic (P₀ : Measure Pair)).continuousOn
    (fun q hq => dominating_source_characteristic_norm_lt_one i μ _ hback hab
      hcomponent (hstrip q hq) (fun hq0 => hzero (hq0 ▸ hq)))
  exact tendstoUniformlyOn_jointCharacteristic hP hweak hK

end FCAppendix.Affine.Uniform06.CharacteristicWeakConvergence
