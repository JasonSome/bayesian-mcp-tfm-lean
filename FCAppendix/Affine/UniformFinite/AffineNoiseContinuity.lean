import FCAppendix.Affine.LowBody.NoisyPurePayoff
import FCAppendix.Affine.LowBody.PureTemplate

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open MeasureTheory Set Filter Topology
open scoped BigOperators

namespace Literal
open LowBody

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def affineFocal (i : ι) (a s : ℝ) (b : ι → ℝ) (z : ℝ) : ι → ℝ :=
  Function.update b i (a + s * z)

theorem potential_affineFocal (κ a s : ℝ) (b : ι → ℝ) (z : ℝ)
    (P : Finset ι × Finset ι) (i : ι) :
    CompleteInformation.potential κ (affineFocal i a s b z) P.1 P.2 =
      copyCoefficient κ P i * s * z +
        CompleteInformation.potential κ (Function.update b i a) P.1 P.2 := by
  rw [potential_eq_copyCoefficient, potential_eq_copyCoefficient]
  rw [← Finset.add_sum_erase Finset.univ
      (fun j => copyCoefficient κ P j * affineFocal i a s b z j) (Finset.mem_univ i),
    ← Finset.add_sum_erase Finset.univ
      (fun j => copyCoefficient κ P j * Function.update b i a j) (Finset.mem_univ i)]
  have he : (∑ j ∈ Finset.univ.erase i, copyCoefficient κ P j * affineFocal i a s b z j) =
      ∑ j ∈ Finset.univ.erase i, copyCoefficient κ P j * Function.update b i a j := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [affineFocal, Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [he]
  simp only [affineFocal, Function.update_self]
  ring

theorem ae_affine_potential_ties_same_focalCopy (μ : Measure ℝ)
    [NullSingletonClass μ] {κ s : ℝ} (hκ : 0 < κ) (hs : s ≠ 0)
    (a : ℝ) (b : ι → ℝ) (i : ι) :
    ∀ᵐ z ∂μ, ∀ P Q : Finset ι × Finset ι,
      CompleteInformation.potential κ (affineFocal i a s b z) P.1 P.2 =
        CompleteInformation.potential κ (affineFocal i a s b z) Q.1 Q.2 →
      focalCopy P i = focalCopy Q i := by
  classical
  apply ae_all_iff.mpr
  intro P
  apply ae_all_iff.mpr
  intro Q
  by_cases hc : focalCopy P i = focalCopy Q i
  · exact Eventually.of_forall (fun _ _ => hc)
  · have hd : copyCoefficient κ P i - copyCoefficient κ Q i ≠ 0 :=
      sub_ne_zero.mpr (copyCoefficient_ne_of_focalCopy_ne hκ P Q i hc)
    have hcoef : (copyCoefficient κ P i - copyCoefficient κ Q i) * s ≠ 0 :=
      mul_ne_zero hd hs
    filter_upwards [ae_affine_ne μ ((copyCoefficient κ P i - copyCoefficient κ Q i) * s)
      (CompleteInformation.potential κ (Function.update b i a) P.1 P.2 -
        CompleteInformation.potential κ (Function.update b i a) Q.1 Q.2) 0 hcoef]
      with z hz he
    apply False.elim (hz ?_)
    rw [potential_affineFocal, potential_affineFocal] at he
    nlinarith

abbrev AffineParameters (ι : Type*) := ℝ × ℝ × ℝ × (ι → ℝ)

def parameterAffineBids (i : ι) (t : AffineParameters ι) (z : ℝ) : ι → ℝ :=
  affineFocal i t.2.1 t.2.2.1 t.2.2.2 z

omit [Fintype ι] in
theorem continuous_parameterAffineBids (i : ι) :
    Continuous (fun p : AffineParameters ι × ℝ => parameterAffineBids i p.1 p.2) := by
  apply continuous_pi
  intro j
  by_cases hj : j = i
  · subst j
    simp only [parameterAffineBids, affineFocal, Function.update_self]
    fun_prop
  · simp only [parameterAffineBids, affineFocal, Function.update_of_ne hj]
    fun_prop

variable {A : Type*} [Fintype A] [Nonempty A]

def affinePurePayoff (pair : A → Finset ι × Finset ι) (κ : ℝ) (i : ι)
    (t : AffineParameters ι) (z : ℝ) : ℝ :=
  let b := parameterAffineBids i t z
  purePayoff κ t.1 b
    (pair (FiniteSelector.select (fun a => CompleteInformation.potential κ b (pair a).1 (pair a).2))) i

theorem ae_continuousAt_affinePurePayoff (pair : A → Finset ι × Finset ι)
    (μ : Measure ℝ) [NullSingletonClass μ] {κ : ℝ} (hκ : 0 < κ)
    (i : ι) (t₀ : AffineParameters ι) (hs : t₀.2.2.1 ≠ 0) :
    ∀ᵐ z ∂μ, ContinuousAt (fun t => affinePurePayoff pair κ i t z) t₀ := by
  have hgen := ae_affine_potential_ties_same_focalCopy μ hκ hs t₀.2.1 t₀.2.2.2 i
  filter_upwards [hgen] with z hz
  let b : AffineParameters ι → (ι → ℝ) := fun t => parameterAffineBids i t z
  have hb : Continuous b := (continuous_parameterAffineBids i).comp
    (continuous_id.prodMk continuous_const)
  apply continuousAt_selected_payoff
    (fun t a => CompleteInformation.potential κ (b t) (pair a).1 (pair a).2)
    (fun a => (continuous_potential κ (pair a)).comp hb)
    (fun a => focalCopy (pair a) i)
    (fun t a => purePayoff κ t.1 (b t) (pair a) i)
    (fun a => by unfold purePayoff; split_ifs <;> fun_prop)
    (fun t a a' h => purePayoff_eq_of_focalCopy_eq κ t.1 (b t) (pair a) (pair a') i h)
    t₀
  exact fun a a' he => hz (pair a) (pair a') he

theorem measurable_affinePurePayoff (pair : A → Finset ι × Finset ι)
    (κ : ℝ) (i : ι) (t : AffineParameters ι) :
    Measurable (affinePurePayoff pair κ i t) := by
  classical
  letI : MeasurableSpace A := ⊤
  let b : ℝ → (ι → ℝ) := parameterAffineBids i t
  have hb : Continuous b := (continuous_parameterAffineBids i).comp
    (continuous_const.prodMk continuous_id)
  have hsel : Measurable (fun z => FiniteSelector.select
      (fun a => CompleteInformation.potential κ (b z) (pair a).1 (pair a).2)) :=
    FiniteSelector.measurable_select _
      (fun a => ((continuous_potential κ (pair a)).comp hb).measurable)
  have hlab : Measurable (fun z => focalCopy (pair (FiniteSelector.select
      (fun a => CompleteInformation.potential κ (b z) (pair a).1 (pair a).2))) i) :=
    (measurable_of_countable (fun a : A => focalCopy (pair a) i)).comp hsel
  exact Measurable.ite (measurableSet_eq_fun hlab measurable_const)
    (by simp only [parameterAffineBids, affineFocal, Function.update_self]; fun_prop)
    (Measurable.ite (measurableSet_eq_fun hlab measurable_const)
      (by simp only [parameterAffineBids, affineFocal, Function.update_self]; fun_prop) measurable_const)

omit [Fintype ι] in
theorem abs_affineFocal_le (i : ι) (a s : ℝ) (b : ι → ℝ) (z : ℝ)
    (hz : z ∈ Icc (0 : ℝ) 1) : |affineFocal i a s b z i| ≤ |a| + |s| := by
  simp only [affineFocal, Function.update_self]
  calc
    |a + s * z| ≤ |a| + |s * z| := abs_add_le _ _
    _ = |a| + |s| * z := by rw [abs_mul, abs_of_nonneg hz.1]
    _ ≤ |a| + |s| := by nlinarith [abs_nonneg s, hz.2]

def affineSmoothedPayoff (pair : A → Finset ι × Finset ι) (μ : Measure ℝ)
    (κ : ℝ) (i : ι) (t : AffineParameters ι) : ℝ :=
  ∫ z, affinePurePayoff pair κ i t z ∂μ

omit [Fintype ι] in
theorem abs_affineSmoothedPayoff_le (pair : A → Finset ι × Finset ι)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ z ∂μ, z ∈ Icc (0 : ℝ) 1) (κ : ℝ) (i : ι) (t : AffineParameters ι) :
    |affineSmoothedPayoff pair μ κ i t| ≤
      |t.1| + (1 + 2 * |κ|) * (|t.2.1| + |t.2.2.1|) := by
  have hbound : ∀ᵐ z ∂μ,
      ‖affinePurePayoff pair κ i t z‖ ≤
        |t.1| + (1 + 2 * |κ|) * (|t.2.1| + |t.2.2.1|) := by
    filter_upwards [hμ] with z hz
    apply (abs_purePayoff_le κ t.1 _ _ i).trans
    have hf := mul_le_mul_of_nonneg_left
      (abs_affineFocal_le i t.2.1 t.2.2.1 t.2.2.2 z hz)
      (show 0 ≤ 1 + 2 * |κ| by positivity)
    change (1 + 2 * |κ|) * |parameterAffineBids i t z i| ≤ _ at hf
    linarith
  simpa only [affineSmoothedPayoff, Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const hbound

theorem continuousAt_affineSmoothedPayoff (pair : A → Finset ι × Finset ι)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (hμ : ∀ᵐ z ∂μ, z ∈ Icc (0 : ℝ) 1) {κ : ℝ} (hκ : 0 < κ)
    (i : ι) (t₀ : AffineParameters ι) (hs : t₀.2.2.1 ≠ 0) :
    ContinuousAt (affineSmoothedPayoff pair μ κ i) t₀ := by
  have hv : ∀ᶠ t : AffineParameters ι in 𝓝 t₀, |t.1| < |t₀.1| + 1 :=
    (show ContinuousAt (fun t : AffineParameters ι => |t.1|) t₀ from by fun_prop)
      (Iio_mem_nhds (by linarith))
  have ha : ∀ᶠ t : AffineParameters ι in 𝓝 t₀, |t.2.1| < |t₀.2.1| + 1 :=
    (show ContinuousAt (fun t : AffineParameters ι => |t.2.1|) t₀ from by fun_prop)
      (Iio_mem_nhds (by linarith))
  have hsl : ∀ᶠ t : AffineParameters ι in 𝓝 t₀, |t.2.2.1| < |t₀.2.2.1| + 1 :=
    (show ContinuousAt (fun t : AffineParameters ι => |t.2.2.1|) t₀ from by fun_prop)
      (Iio_mem_nhds (by linarith))
  let B : ℝ := (|t₀.1| + 1) + (1 + 2 * |κ|) * (|t₀.2.1| + |t₀.2.2.1| + 2)
  apply MeasureTheory.continuousAt_of_dominated
    (F := fun t z => affinePurePayoff pair κ i t z) (bound := fun _ => B)
    (Eventually.of_forall (fun t => (measurable_affinePurePayoff pair κ i t).aestronglyMeasurable))
    ?_ (integrable_const B) (ae_continuousAt_affinePurePayoff pair μ hκ i t₀ hs)
  filter_upwards [hv, ha, hsl] with t hvt hat hst
  filter_upwards [hμ] with z hz
  calc
    ‖affinePurePayoff pair κ i t z‖ ≤
        |t.1| + (1 + 2 * |κ|) * |parameterAffineBids i t z i| :=
      abs_purePayoff_le κ t.1 _ _ i
    _ ≤ |t.1| + (1 + 2 * |κ|) * (|t.2.1| + |t.2.2.1|) := by
      have hf := mul_le_mul_of_nonneg_left
        (abs_affineFocal_le i t.2.1 t.2.2.1 t.2.2.2 z hz)
        (show 0 ≤ 1 + 2 * |κ| by positivity)
      change (1 + 2 * |κ|) * |parameterAffineBids i t z i| ≤ _ at hf
      linarith
    _ ≤ B := by
      dsimp only [B]
      have hp := mul_le_mul_of_nonneg_left (add_le_add hat.le hst.le)
        (show 0 ≤ 1 + 2 * |κ| by positivity)
      nlinarith

omit [Fintype ι] in
theorem continuousAt_affineSmoothedPayoff_zero (pair : A → Finset ι × Finset ι)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ z ∂μ, z ∈ Icc (0 : ℝ) 1) (κ : ℝ) (i : ι)
    (t₀ : AffineParameters ι) (hv : t₀.1 = 0) (ha : t₀.2.1 = 0) (hs : t₀.2.2.1 = 0) :
    ContinuousAt (affineSmoothedPayoff pair μ κ i) t₀ := by
  have he : affineSmoothedPayoff pair μ κ i t₀ = 0 := by
    have hb := abs_affineSmoothedPayoff_le pair μ hμ κ i t₀
    simp only [hv, ha, hs, abs_zero, add_zero, mul_zero] at hb
    exact abs_eq_zero.mp (le_antisymm hb (abs_nonneg _))
  change Tendsto (affineSmoothedPayoff pair μ κ i) (𝓝 t₀)
    (𝓝 (affineSmoothedPayoff pair μ κ i t₀))
  rw [he]
  have hbound : Tendsto (fun t : AffineParameters ι =>
      |t.1| + (1 + 2 * |κ|) * (|t.2.1| + |t.2.2.1|)) (𝓝 t₀) (𝓝 0) := by
    have hc : Continuous (fun t : AffineParameters ι =>
        |t.1| + (1 + 2 * |κ|) * (|t.2.1| + |t.2.2.1|)) := by fun_prop
    have hh := hc.tendsto t₀
    simpa only [hv, ha, hs, abs_zero, zero_add, add_zero, mul_zero] using
      hh
  exact squeeze_zero_norm' (Eventually.of_forall
    (fun t => abs_affineSmoothedPayoff_le pair μ hμ κ i t)) hbound

end Literal
end FCAppendix.Affine.UniformFinite
