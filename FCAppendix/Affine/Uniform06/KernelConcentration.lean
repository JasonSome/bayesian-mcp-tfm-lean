import FCAppendix.Affine.Uniform06.IntervalRecovery
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

noncomputable section

namespace FCAppendix.Affine.Uniform06.KernelConcentration

open MeasureTheory Set
open scoped Topology
open IntervalRecovery

def kernelMean (ν : Measure ℝ) (K : ℝ → ℝ) (a : ℝ) : ℝ :=
  ∫ x, K (x - a) ∂ν

lemma integrable_kernel_joint (ν : Measure ℝ) [IsFiniteMeasure ν]
    {K : ℝ → ℝ} (hK : Continuous K) (hKi : Integrable K) :
    Integrable (fun z : ℝ × ℝ => K (z.1 - z.2)) (ν.prod volume) := by
  apply (integrable_prod_iff
    (hK.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ fun x => hKi.comp_sub_left x
  · have heq : (fun x : ℝ => ∫ a, ‖K (x - a)‖) =
        fun _ => ∫ a, ‖K a‖ := by
      funext x
      exact integral_sub_left_eq_self (fun a => ‖K a‖) volume x
    change Integrable (fun x : ℝ => ∫ a, ‖K (x-a)‖) ν
    rw [heq]
    exact integrable_const _

lemma integrable_kernelMean (ν : Measure ℝ) [IsFiniteMeasure ν]
    {K : ℝ → ℝ} (hK : Continuous K) (hKi : Integrable K) :
    Integrable (kernelMean ν K) :=
  (integrable_kernel_joint ν hK hKi).integral_prod_right

lemma integral_const_Icc_real {a b : ℝ} (hab : a ≤ b) (c : ℝ) :
    (∫ _x in Icc a b, c) = (b - a) * c := by
  rw [setIntegral_const]
  simp only [smul_eq_mul, Measure.real, Real.volume_Icc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]

lemma kernel_integral_near_point_lower {K : ℝ → ℝ} (hKi : Integrable K)
    (hK0 : ∀ t, 0 ≤ K t) {R κ : ℝ} (hR : 0 < R)
    (hκ : ∀ t, |t| ≤ R → κ ≤ K t)
    {a b x : ℝ} (hx : x ∈ Icc a b) :
    2 * R * κ ≤ ∫ z in Icc (a - R) (b + R), K (x - z) := by
  have hsmall :
      (∫ z in Icc (x - R) (x + R), κ) ≤
        ∫ z in Icc (x - R) (x + R), K (x - z) := by
    apply setIntegral_mono_on (integrable_const _) (hKi.comp_sub_left x).integrableOn
      measurableSet_Icc
    intro z hz
    apply hκ
    rw [abs_le]
    constructor <;> linarith [hz.1, hz.2]
  have hsub : Icc (x - R) (x + R) ⊆ Icc (a - R) (b + R) := by
    intro z hz
    constructor <;> linarith [hz.1, hz.2, hx.1, hx.2]
  have hmono :
      (∫ z in Icc (x - R) (x + R), K (x - z)) ≤
        ∫ z in Icc (a - R) (b + R), K (x - z) :=
    setIntegral_mono_set (hKi.comp_sub_left x).integrableOn
      (ae_of_all _ fun z => hK0 _) (ae_of_all _ hsub)
  rw [integral_const_Icc_real (by linarith : x - R ≤ x + R)] at hsmall
  calc
    2 * R * κ = (x + R - (x - R)) * κ := by ring
    _ ≤ ∫ z in Icc (x - R) (x + R), K (x - z) := hsmall
    _ ≤ _ := hmono

theorem interval_mass_mul_le (ν : Measure ℝ) [IsFiniteMeasure ν]
    {K : ℝ → ℝ} (hK : Continuous K) (hKi : Integrable K)
    (hK0 : ∀ t, 0 ≤ K t) {R κ L : ℝ} (hR : 0 < R)
    (hκ : ∀ t, |t| ≤ R → κ ≤ K t)
    (hmean : ∀ a, kernelMean ν K a ≤ L) {a b : ℝ} (hab : a ≤ b) :
    ν.real (Icc a b) * (2 * R * κ) ≤ (b - a + 2 * R) * L := by
  let J := Icc (a - R) (b + R)
  have hjoint : Integrable (fun z : ℝ × ℝ => K (z.1 - z.2))
      (ν.prod (volume.restrict J)) := by
    rw [show ν.prod (volume.restrict J) = (ν.prod volume).restrict (univ ×ˢ J) by
      simpa only [Measure.restrict_univ] using
        (Measure.prod_restrict (μ := ν) (ν := (volume : Measure ℝ)) univ J)]
    exact (integrable_kernel_joint ν hK hKi).restrict
  have hinnerI : Integrable (fun x => ∫ z in J, K (x - z)) ν :=
    hjoint.integral_prod_left
  have hind : Integrable ((Icc a b).indicator (fun _ : ℝ => 2 * R * κ)) ν :=
    (integrable_const _).indicator measurableSet_Icc
  have hpoint : ∀ x,
      (Icc a b).indicator (fun _ : ℝ => 2 * R * κ) x ≤
        ∫ z in J, K (x - z) := by
    intro x
    by_cases hx : x ∈ Icc a b
    · rw [indicator_of_mem hx]
      exact kernel_integral_near_point_lower hKi hK0 hR hκ hx
    · rw [indicator_of_notMem hx]
      exact integral_nonneg fun z => hK0 _
  calc
    ν.real (Icc a b) * (2 * R * κ) =
        ∫ x, (Icc a b).indicator (fun _ : ℝ => 2 * R * κ) x ∂ν := by
      rw [integral_indicator measurableSet_Icc, setIntegral_const]
      rfl
    _ ≤ ∫ x, (∫ z in J, K (x - z)) ∂ν :=
      integral_mono_ae hind hinnerI (ae_of_all _ hpoint)
    _ = ∫ z in J, kernelMean ν K z := integral_integral_swap hjoint
    _ ≤ ∫ _z in J, L :=
      integral_mono_ae (integrable_kernelMean ν hK hKi).integrableOn
        (integrable_const _) (ae_of_all _ hmean)
    _ = (b - a + 2 * R) * L := by
      rw [integral_const_Icc_real (by linarith : a - R ≤ b + R)]
      ring

theorem interval_mass_le_from_kernelMean (ν : Measure ℝ) [IsFiniteMeasure ν]
    {K : ℝ → ℝ} (hK : Continuous K) (hKi : Integrable K)
    (hK0 : ∀ t, 0 ≤ K t) {R κ L : ℝ} (hR : 0 < R) (hκ0 : 0 < κ)
    (hκ : ∀ t, |t| ≤ R → κ ≤ K t)
    (hmean : ∀ a, kernelMean ν K a ≤ L) {a b : ℝ} (hab : a ≤ b) :
    intervalMass ν a b ≤ (L / (2 * R * κ)) * (b - a + 2 * R) := by
  have h := interval_mass_mul_le ν hK hKi hK0 hR hκ hmean hab
  have hden : 0 < 2 * R * κ := by positivity
  rw [intervalMass_eq_measure,
    show L / (2 * R * κ) * (b - a + 2 * R) =
      ((b - a + 2 * R) * L) / (2 * R * κ) by ring]
  exact (le_div_iff₀ hden).mpr h

lemma shifted_indicator_integral (K : ℝ → ℝ) (a b x : ℝ) :
    (∫ u, K u * intervalIndicator (a + u) (b + u) x) =
      ∫ z in Icc a b, K (x - z) := by
  have heq : (fun z : ℝ => K (x - z) *
      intervalIndicator (a + (x - z)) (b + (x - z)) x) =
      (Icc a b).indicator (fun z => K (x - z)) := by
    funext z
    have hmem : x ∈ Icc (a + (x - z)) (b + (x - z)) ↔ z ∈ Icc a b := by
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    by_cases hz : z ∈ Icc a b
    · simp only [intervalIndicator, indicator_of_mem (hmem.mpr hz),
        indicator_of_mem hz, mul_one]
    · simp only [intervalIndicator,
        indicator_of_notMem (fun h => hz (hmem.mp h)), indicator_of_notMem hz, mul_zero]
  have h := integral_sub_left_eq_self
    (fun u => K u * intervalIndicator (a + u) (b + u) x) volume x
  rw [heq, integral_indicator measurableSet_Icc] at h
  exact h.symm

theorem blurredMass_eq_integral_kernelMean (ν : Measure ℝ) [IsFiniteMeasure ν]
    {K : ℝ → ℝ} (hK : Continuous K) (hKi : Integrable K) (a b : ℝ) :
    blurredMass ν K a b = ∫ z in Icc a b, kernelMean ν K z := by
  have hmeas : Measurable (fun z : ℝ × ℝ =>
      K z.1 * intervalIndicator (a + z.1) (b + z.1) z.2) := by
    have hm : MeasurableSet {z : ℝ × ℝ | z.2 ∈ Icc (a + z.1) (b + z.1)} :=
      (measurableSet_le (measurable_const.add measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd (measurable_const.add measurable_fst))
    have heq : (fun z : ℝ × ℝ => intervalIndicator (a + z.1) (b + z.1) z.2) =
        {z : ℝ × ℝ | z.2 ∈ Icc (a + z.1) (b + z.1)}.indicator (fun _ => (1 : ℝ)) := by
      funext z
      rfl
    rw [show (fun z : ℝ × ℝ => K z.1 * intervalIndicator (a + z.1) (b + z.1) z.2) =
      (fun z => K z.1) * (fun z => intervalIndicator (a + z.1) (b + z.1) z.2) by rfl,
      heq]
    exact (hK.measurable.comp measurable_fst).mul (measurable_const.indicator hm)
  have hji : Integrable (fun z : ℝ × ℝ =>
      K z.1 * intervalIndicator (a + z.1) (b + z.1) z.2) (volume.prod ν) := by
    apply (hKi.norm.comp_fst ν).mono' hmeas.aestronglyMeasurable
    exact ae_of_all _ fun z => by
      rw [norm_mul]
      apply mul_le_of_le_one_right (norm_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg (intervalIndicator_bounds _ _ _).1]
      exact (intervalIndicator_bounds _ _ _).2
  have hkj : Integrable (fun z : ℝ × ℝ => K (z.1 - z.2))
      (ν.prod (volume.restrict (Icc a b))) := by
    rw [show ν.prod (volume.restrict (Icc a b)) =
      (ν.prod volume).restrict (univ ×ˢ Icc a b) by
        simpa only [Measure.restrict_univ] using
          (Measure.prod_restrict (μ := ν) (ν := (volume : Measure ℝ)) univ (Icc a b))]
    exact (integrable_kernel_joint ν hK hKi).restrict
  calc
    blurredMass ν K a b = ∫ u, ∫ x,
        K u * intervalIndicator (a + u) (b + u) x ∂ν := by
      simp only [blurredMass, intervalMass, integral_const_mul]
    _ = ∫ x, (∫ u, K u * intervalIndicator (a + u) (b + u) x) ∂ν :=
      integral_integral_swap hji
    _ = ∫ x, (∫ z in Icc a b, K (x - z)) ∂ν := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => shifted_indicator_integral K a b x
    _ = ∫ z in Icc a b, kernelMean ν K z := integral_integral_swap hkj

end FCAppendix.Affine.Uniform06.KernelConcentration
