import FCAppendix.Affine.Uniform06.CharacteristicExpansion
import FCAppendix.Affine.Uniform06.MixedLaw
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

noncomputable section

namespace FCAppendix.Affine.Uniform06.MixedCharacteristicGap

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open CharacteristicExpansion
open FCAppendix.Affine.Uniform07

abbrev Pair := ℝ × ℝ

def jointPhase (q p : Pair) : ℂ := phase (q.1 * p.1 + q.2 * p.2)

def jointCharacteristic (μ : Measure Pair) (q : Pair) : ℂ :=
  ∫ p, jointPhase q p ∂μ

lemma continuous_jointPhase_left (p : Pair) : Continuous (fun q => jointPhase q p) :=
  continuous_phase.comp ((continuous_fst.mul continuous_const).add
    (continuous_snd.mul continuous_const))

lemma continuous_jointPhase_right (q : Pair) : Continuous (jointPhase q) :=
  continuous_phase.comp ((continuous_const.mul continuous_fst).add
    (continuous_const.mul continuous_snd))

@[simp] lemma norm_jointPhase (q p : Pair) : ‖jointPhase q p‖ = 1 :=
  norm_phase _

theorem continuous_jointCharacteristic (μ : Measure Pair) [IsFiniteMeasure μ] :
    Continuous (jointCharacteristic μ) := by
  apply continuous_of_dominated (bound := fun _ => (1 : ℝ))
  · intro q
    exact (continuous_jointPhase_right q).aestronglyMeasurable
  · intro q
    exact ae_of_all _ fun p => (norm_jointPhase q p).le
  · exact integrable_const 1
  · exact ae_of_all _ continuous_jointPhase_left

theorem frequency_zero_of_phase_constant_on_interval {a b s : ℝ} (hab : a < b)
    {c : ℂ} (hconstant : ∀ x ∈ Ioo a b, phase (s * x) = c) : s = 0 := by
  let x : ℝ := (a + b) / 2
  have hx : x ∈ Ioo a b := by dsimp [x]; constructor <;> linarith
  have hd : HasDerivAt (fun u : ℝ => phase (s * u))
      (phase (s * x) * ((s : ℂ) * Complex.I)) x := by
    convert! (((hasDerivAt_id x).const_mul s).ofReal_comp.mul_const Complex.I).cexp
      using 1
    simp [phase]
  have heq : (fun u : ℝ => phase (s * u)) =ᶠ[𝓝 x] (fun _ => c) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with u hu
    exact hconstant u hu
  have hd0 : HasDerivAt (fun u : ℝ => phase (s * u)) 0 x :=
    (hasDerivAt_const x c).congr_of_eventuallyEq heq
  have hz := hd.unique hd0
  have hp : phase (s * x) ≠ 0 := Complex.exp_ne_zero _
  have hsI : (s : ℂ) * Complex.I = 0 := (mul_eq_zero.mp hz).resolve_left hp
  have hs : (s : ℂ) = 0 := (mul_eq_zero.mp hsI).resolve_right Complex.I_ne_zero
  exact_mod_cast hs

theorem frequency_zero_of_phase_ae_constant {μ : Measure ℝ} {a b s : ℝ}
    (hab : a < b) (hcomponent : volume.restrict (Ioo a b) ≪ μ)
    {c : ℂ} (hconstant : ∀ᵐ x ∂μ, phase (s * x) = c) : s = 0 := by
  have hae : (fun x : ℝ => phase (s * x)) =ᵐ[volume.restrict (Ioo a b)]
      (fun _ => c) := hcomponent.ae_le hconstant
  have hpoint := Measure.eqOn_open_of_ae_eq hae isOpen_Ioo
    (continuous_phase.comp (continuous_const.mul continuous_id)).continuousOn
    continuousOn_const
  exact frequency_zero_of_phase_constant_on_interval hab hpoint

theorem frequency_zero_of_phase_eq_one {r : ℝ}
    (hr : r ∈ Icc (-Real.pi) Real.pi) (hphase : phase r = 1) : r = 0 := by
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hphase
  have hkr : r = (k : ℝ) * (2 * Real.pi) := by
    simpa using congrArg Complex.im hk
  have hperiod : 0 < 2 * Real.pi := by positivity
  have hklt : (k : ℝ) < 1 := by
    nlinarith [Real.pi_pos, hr.2]
  have hkgt : (-1 : ℝ) < (k : ℝ) := by
    nlinarith [Real.pi_pos, hr.1]
  have hklt' : k < (1 : ℤ) := by exact_mod_cast hklt
  have hkgt' : (-1 : ℤ) < k := by exact_mod_cast hkgt
  have hk0 : k = 0 := by omega
  simpa [hk0] using hkr

theorem source_phase_constant_forces_origin (i : Row) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {a b : ℝ} (hab : a < b)
    (hcomponent : volume.restrict (Ioo a b) ≪ μ)
    {q : Pair} (hq : q.2 ∈ Icc (-Real.pi) Real.pi) {c : ℂ}
    (hconstant : ∀ᵐ p ∂MixedLaw.law i μ, jointPhase q p = c) : q = 0 := by
  have ht : ENNReal.ofReal (cutoff i) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (cutoff_pos i))
  have hu : ENNReal.ofReal (1 - cutoff i) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr (cutoff_lt_one i)))
  rw [MixedLaw.law, ae_add_measure_iff] at hconstant
  have hlift : ∀ᵐ p ∂MixedLaw.lowerLift μ, jointPhase q p = c := by
    simpa [ae_iff, Measure.smul_apply, smul_eq_mul, ht] using hconstant.2
  have hlower : ∀ᵐ x ∂μ, phase (q.1 * x) = c := by
    rw [MixedLaw.lowerLift] at hlift
    have h := (ae_map_iff (by fun_prop)
      ((continuous_jointPhase_right q).measurable (measurableSet_singleton c))).mp hlift
    simpa [jointPhase] using h
  have hs : q.1 = 0 := frequency_zero_of_phase_ae_constant hab hcomponent hlower
  have hc : (1 : ℂ) = c := by simpa [hs, phase] using hlower
  have hupper : ∀ᵐ p ∂MixedLaw.upperSignLaw, jointPhase q p = c := by
    simpa [ae_iff, Measure.smul_apply, smul_eq_mul, hu] using hconstant.1
  rw [MixedLaw.upperSignLaw, ae_add_measure_iff] at hupper
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) ≠ 0 := by norm_num
  have hplus : ∀ᵐ p ∂Measure.dirac ((1 / 2 : ℝ), (1 : ℝ)),
      jointPhase q p = c := by
    simpa [ae_iff, Measure.smul_apply, smul_eq_mul, hhalf] using hupper.1
  have hp := (ae_dirac_iff ((continuous_jointPhase_right q).measurable (measurableSet_singleton c))).mp hplus
  have hphase : phase q.2 = 1 := by simpa [jointPhase, hs, ← hc] using hp
  have hr : q.2 = 0 := frequency_zero_of_phase_eq_one hq hphase
  exact Prod.ext hs hr

theorem source_characteristic_norm_lt_one (i : Row) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {a b : ℝ} (hab : a < b)
    (hcomponent : volume.restrict (Ioo a b) ≪ μ)
    {q : Pair} (hq : q.2 ∈ Icc (-Real.pi) Real.pi) (hq0 : q ≠ 0) :
    ‖jointCharacteristic (MixedLaw.law i μ) q‖ < 1 := by
  have halt := ae_eq_const_or_norm_integral_lt_of_norm_le_const
    (μ := MixedLaw.law i μ) (f := jointPhase q)
    (C := (1 : ℝ)) (ae_of_all _ fun p => (norm_jointPhase q p).le)
  rcases halt with hconst | hlt
  · exact (hq0 (source_phase_constant_forces_origin i μ hab hcomponent hq hconst)).elim
  · simpa [jointCharacteristic] using hlt

theorem dominating_source_characteristic_norm_lt_one (i : Row) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (ν : Measure Pair) [IsProbabilityMeasure ν]
    (hback : MixedLaw.law i μ ≪ ν) {a b : ℝ} (hab : a < b)
    (hcomponent : volume.restrict (Ioo a b) ≪ μ)
    {q : Pair} (hq : q.2 ∈ Icc (-Real.pi) Real.pi) (hq0 : q ≠ 0) :
    ‖jointCharacteristic ν q‖ < 1 := by
  have halt := ae_eq_const_or_norm_integral_lt_of_norm_le_const
    (μ := ν) (f := jointPhase q) (C := (1 : ℝ))
    (ae_of_all _ fun p => (norm_jointPhase q p).le)
  rcases halt with hconst | hlt
  · exact (hq0 (source_phase_constant_forces_origin i μ hab hcomponent hq
      (hback.ae_le hconst))).elim
  · simpa [jointCharacteristic] using hlt

theorem gap_on_compact {A : Type*} [TopologicalSpace A] {K : Set A}
    (hK : IsCompact K) {f : A → ℂ} (hf : ContinuousOn f K)
    (hlt : ∀ x ∈ K, ‖f x‖ < 1) :
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ x ∈ K, ‖f x‖ ≤ q := by
  by_cases hne : K.Nonempty
  · obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hne hf.norm
    rw [isMaxOn_iff] at hmax
    exact ⟨‖f x‖, norm_nonneg _, hlt x hx, fun y hy => hmax y hy⟩
  · exact ⟨0, le_rfl, zero_lt_one, fun x hx => (hne ⟨x, hx⟩).elim⟩

theorem source_gap_on_compact (i : Row) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (ν : Measure Pair) [IsProbabilityMeasure ν] (hback : MixedLaw.law i μ ≪ ν)
    {a b : ℝ} (hab : a < b) (hcomponent : volume.restrict (Ioo a b) ≪ μ)
    {K : Set Pair} (hK : IsCompact K)
    (hstrip : ∀ q ∈ K, q.2 ∈ Icc (-Real.pi) Real.pi)
    (hzero : (0 : Pair) ∉ K) :
    ∃ δ : ℝ, 0 ≤ δ ∧ δ < 1 ∧ ∀ q ∈ K, ‖jointCharacteristic ν q‖ ≤ δ := by
  apply gap_on_compact hK (continuous_jointCharacteristic ν).continuousOn
  intro q hq
  apply dominating_source_characteristic_norm_lt_one i μ ν hback hab hcomponent
    (hstrip q hq)
  intro hq0
  exact hzero (hq0 ▸ hq)

theorem eventual_gap_of_uniform_convergence {A : Type*} [TopologicalSpace A]
    {K : Set A} (hK : IsCompact K) {f : A → ℂ} {F : ℕ → A → ℂ}
    (hf : ContinuousOn f K) (hlt : ∀ x ∈ K, ‖f x‖ < 1)
    (hconv : TendstoUniformlyOn F f atTop K) :
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧
      ∀ᶠ n in atTop, ∀ x ∈ K, ‖F n x‖ ≤ q := by
  obtain ⟨q, hq0, hq1, hq⟩ := gap_on_compact hK hf hlt
  refine ⟨(1 + q) / 2, by linarith, by linarith, ?_⟩
  have he : 0 < (1 - q) / 2 := by linarith
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv ((1 - q) / 2) he]
    with n hn x hx
  have hd : ‖F n x - f x‖ < (1 - q) / 2 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hn x hx
  have htriangle := norm_add_le (F n x - f x) (f x)
  rw [sub_add_cancel] at htriangle
  linarith [hq x hx]

end FCAppendix.Affine.Uniform06.MixedCharacteristicGap
