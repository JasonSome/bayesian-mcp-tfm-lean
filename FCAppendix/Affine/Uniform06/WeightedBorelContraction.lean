import FCAppendix.Affine.Uniform06.ICAbsorption
import Mathlib.MeasureTheory.Measure.WithDensity

noncomputable section
namespace FCAppendix.Affine.Uniform06.WeightedBorelContraction

open MeasureTheory Set Filter Topology
open ScaledMeasure ICAbsorption SupportIntervalDomination

def weightMeasure (m lo hi : ℝ) : Measure ℝ :=
  (volume.restrict (Ioc lo hi)).withDensity (fun b => ENNReal.ofReal (rentWeight m b))

theorem rentWeight_nonnegative {m x : ℝ} (hm : 0 ≤ m) (hx : 0 ≤ x) :
    0 ≤ rentWeight m x := by
  unfold rentWeight
  positivity

theorem rentWeight_integrableOn {m lo hi : ℝ} (hm : 0 < m) (hlo : 0 < lo)
    {A : Set ℝ} (hA : A ⊆ Icc lo hi) : IntegrableOn (rentWeight m) A := by
  exact ((continuousOn_const : ContinuousOn (fun _ : ℝ => (1:ℝ)) (Icc lo hi)).integrableOn_Icc.mono_set hA).add
    (reciprocal_integrableOn hm hlo hA)

theorem weightMeasure_finite {m lo hi : ℝ} (hm : 0 < m) (hlo : 0 < lo) :
    IsFiniteMeasure (weightMeasure m lo hi) := by
  apply isFiniteMeasure_withDensity
  have hwi := rentWeight_integrableOn hm hlo (Ioc_subset_Icc_self : Ioc lo hi ⊆ Icc lo hi)
  have hn : ∀ᵐ b ∂volume.restrict (Ioc lo hi), 0 ≤ rentWeight m b := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with b hb
    exact rentWeight_nonnegative hm.le (hlo.le.trans hb.1.le)
  rw [← ofReal_integral_eq_lintegral_ofReal hwi hn]
  exact ENNReal.ofReal_ne_top

theorem weightMeasure_atomless (m lo hi x : ℝ) : weightMeasure m lo hi {x}=0 := by
  unfold weightMeasure
  exact measure_singleton x

theorem weightMeasure_real_apply {m lo hi : ℝ} (hm : 0 < m) (hlo : 0 < lo)
    {A : Set ℝ} (hAm : MeasurableSet A) (hA : A ⊆ Ioc lo hi) :
    (weightMeasure m lo hi).real A=∫ b in A, rentWeight m b := by
  have hAc : A ⊆ Icc lo hi := hA.trans Ioc_subset_Icc_self
  have hi := rentWeight_integrableOn hm hlo hAc
  have hn : ∀ᵐ b ∂volume.restrict A, 0 ≤ rentWeight m b := by
    filter_upwards [ae_restrict_mem hAm] with b hb
    exact rentWeight_nonnegative hm.le (hlo.le.trans (hAc hb).1)
  rw [Measure.real,weightMeasure,withDensity_apply _ hAm,
    Measure.restrict_restrict_of_subset hA,← ofReal_integral_eq_lintegral_ofReal hi hn,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hn)]

def comparison (μ : Measure ℝ) (κ C ε m lo hi : ℝ) : Measure ℝ :=
  ENNReal.ofReal C • weightMeasure m lo hi+
    ENNReal.ofReal ε • scaledRankMeasure κ μ

theorem comparison_finite (μ : Measure ℝ) [IsFiniteMeasure μ]
    (κ C ε : ℝ) {m lo hi : ℝ} (hm : 0 < m) (hlo : 0 < lo) :
    IsFiniteMeasure (comparison μ κ C ε m lo hi) := by
  letI := weightMeasure_finite (hi := hi) hm hlo
  letI : IsFiniteMeasure (scaledRankMeasure κ μ) := by
    unfold scaledRankMeasure
    infer_instance
  letI : IsFiniteMeasure (ENNReal.ofReal C • weightMeasure m lo hi) :=
    (weightMeasure m lo hi).smul_finite ENNReal.ofReal_ne_top
  letI : IsFiniteMeasure (ENNReal.ofReal ε • scaledRankMeasure κ μ) :=
    (scaledRankMeasure κ μ).smul_finite ENNReal.ofReal_ne_top
  unfold comparison
  infer_instance

theorem comparison_atomless (μ : Measure ℝ) (hatom : ∀ x : ℝ, μ {x}=0)
    {κ : ℝ} (hκ : κ ≠ 0) (C ε m lo hi x : ℝ) :
    comparison μ κ C ε m lo hi {x}=0 := by
  rw [comparison,Measure.add_apply,Measure.smul_apply,Measure.smul_apply,
    weightMeasure_atomless,scaledRankMeasure_atomless μ hatom hκ x]
  simp

theorem comparison_real_apply (μ : Measure ℝ) [IsFiniteMeasure μ]
    {κ C ε m lo hi : ℝ} (hκ : κ ≠ 0) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hm : 0 < m) (hlo : 0 < lo)
    {A : Set ℝ} (hAm : MeasurableSet A) (hA : A ⊆ Ioc lo hi) :
    (comparison μ κ C ε m lo hi).real A=
      C*(∫ b in A, rentWeight m b)+ε*μ.real (scaledSet κ A) := by
  letI := weightMeasure_finite (hi := hi) hm hlo
  letI : IsFiniteMeasure (scaledRankMeasure κ μ) := by
    unfold scaledRankMeasure
    infer_instance
  letI : IsFiniteMeasure (ENNReal.ofReal C • weightMeasure m lo hi) :=
    (weightMeasure m lo hi).smul_finite ENNReal.ofReal_ne_top
  letI : IsFiniteMeasure (ENNReal.ofReal ε • scaledRankMeasure κ μ) :=
    (scaledRankMeasure κ μ).smul_finite ENNReal.ofReal_ne_top
  rw [comparison,measureReal_add_apply (measure_ne_top _ _) (measure_ne_top _ _)]
  simp only [Measure.real,Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hC,ENNReal.toReal_ofReal hε]
  rw [← Measure.real,weightMeasure_real_apply hm hlo hAm hA,
    scaledRankMeasure_apply hκ μ hAm]

theorem left_weight_length_le_integral {m a b : ℝ}
    (hm : 0 < m) (ha : 0 < a) (hab : a ≤ b) (hb2 : b ≤ 2*a) :
    rentWeight m a*(b-a) ≤ 2*(∫ x in Ioc a b, rentWeight m x) := by
  have hi := rentWeight_integrableOn hm ha (Ioc_subset_Icc_self : Ioc a b ⊆ Icc a b)
  have hf : ∀ᵐ x ∂volume.restrict (Ioc a b), rentWeight m a ≤ 2*rentWeight m x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx0 := ha.trans hx.1
    have hx2 : x ≤ 2*a := hx.2.trans hb2
    have hi' : 1/(m*a) ≤ 2/(m*x) := by
      apply (div_le_div_iff₀ (mul_pos hm ha) (mul_pos hm hx0)).mpr
      nlinarith
    unfold rentWeight
    have he : 2/(m*x)=2*(1/(m*x)) := by ring
    rw [he] at hi'
    linarith only [hi']
  have hh := integral_mono_ae (integrable_const (rentWeight m a)) (hi.const_mul 2) hf
  rw [integral_const,integral_const_mul] at hh
  simp only [Measure.real,Measure.restrict_apply_univ,Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab),smul_eq_mul] at hh
  convert! hh using 1
  ring

theorem weighted_Borel_of_anchored_intervals
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hatom : ∀ x : ℝ, μ {x}=0) {κ C ε m lo hi δ : ℝ}
    (hκ : 0 < κ) (hC : 0 ≤ C) (hε : 0 ≤ ε) (hm : 0 < m)
    (hlo : 0 < lo) (hδ : 0 < δ) (hδlo : δ ≤ lo)
    (hanchor : ∀ a ∈ μ.support, ∀ b : ℝ,
      a ∈ Icc lo hi → b ∈ Icc lo hi → a ≤ b → b-a ≤ δ →
        μ.real (Ioc a b) ≤ C*rentWeight m a*(b-a)+ε*μ.real (Ioc (κ*a) (κ*b))) :
    ∀ A : Set ℝ, MeasurableSet A → A ⊆ Ioc lo hi →
      μ.real A ≤ (2*C)*(∫ b in A, rentWeight m b)+ε*μ.real (scaledSet κ A) := by
  let ν := comparison μ κ (2*C) ε m lo hi
  letI : IsFiniteMeasure ν := comparison_finite μ κ (2*C) ε hm hlo
  have hνatom : ∀ x : ℝ, ν {x}=0 := comparison_atomless μ hatom hκ.ne' (2*C) ε m lo hi
  have hdom : μ.restrict (Ioc lo hi) ≤ ν.restrict (Ioc lo hi) := by
    apply measure_restrict_le_of_local_support_bounds μ ν Measure.isClosed_support
      Measure.support_mem_ae hatom hνatom hδ
    intro a ha b haI hbI hab hstep
    have hsub : Ioc a b ⊆ Ioc lo hi :=
      fun _ hx => ⟨haI.1.trans_lt hx.1,hx.2.trans hbI.2⟩
    rw [comparison_real_apply μ hκ.ne' (by positivity) hε hm hlo measurableSet_Ioc hsub,
      scaledSet_Ioc hκ]
    have hw := left_weight_length_le_integral hm (hlo.trans_le haI.1) hab
      (show b ≤ 2*a by linarith [hstep.trans hδlo,haI.1])
    have hh := mul_le_mul_of_nonneg_left hw hC
    have hp := hanchor a ha b haI hbI hab hstep
    nlinarith
  intro A hAm hA
  have hh := Measure.le_iff'.mp hdom A
  rw [Measure.restrict_apply hAm,Measure.restrict_apply hAm,
    inter_eq_left.mpr hA] at hh
  have hr := ENNReal.toReal_mono (measure_ne_top ν A) hh
  change μ.real A ≤ ν.real A at hr
  change μ.real A ≤ (comparison μ κ (2*C) ε m lo hi).real A at hr
  rw [comparison_real_apply μ hκ.ne' (by positivity) hε hm hlo hAm hA] at hr
  exact hr

end FCAppendix.Affine.Uniform06.WeightedBorelContraction
