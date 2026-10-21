import FCAppendix.Affine.Uniform06.LowChernoffSource
import FCAppendix.Probability.StrictCramerComparison

set_option autoImplicit false

noncomputable section
namespace FCAppendix.Affine.Uniform06.LowChernoff

open MeasureTheory ProbabilityTheory Set
open FCAppendix.Affine.Uniform07 FCAppendix.Affine.ClippedResidual
open FCAppendix.ExponentialTilt FCAppendix.StrictCramerComparison

def lowerStatisticLaw (i : Row) (G : Measure (ℝ × ℝ)) : Measure ℝ :=
  G.map (fun p => physicalStatistic i p.2)

instance lowerStatisticLaw_probability (i : Row) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G] : IsProbabilityMeasure (lowerStatisticLaw i G) :=
  Measure.isProbabilityMeasure_map
    ((continuous_physicalStatistic i).measurable.comp measurable_snd).aemeasurable

def originalStatisticLaw (i : Row) (G : Measure (ℝ × ℝ)) : Measure ℝ :=
  ENNReal.ofReal (1-cutoff i) • Measure.dirac (1/2:ℝ) +
    ENNReal.ofReal (cutoff i) • lowerStatisticLaw i G

instance originalStatisticLaw_probability (i : Row) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G] : IsProbabilityMeasure (originalStatisticLaw i G) := by
  constructor
  simp only [originalStatisticLaw, Measure.add_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by linarith [cutoff_lt_one i]) (cutoff_pos i).le]
  norm_num

theorem lowerStatisticLaw_bounds (i : Row) (G : Measure (ℝ × ℝ)) :
    ∀ᵐ z ∂lowerStatisticLaw i G, z ∈ Icc (0:ℝ) 1 := by
  apply (ae_map_iff
    ((continuous_physicalStatistic i).measurable.comp measurable_snd).aemeasurable
    measurableSet_Icc).mpr
  exact Filter.Eventually.of_forall fun p =>
    ⟨physicalStatistic_nonneg i p.2, exposure_le_one _ _ _⟩

theorem originalStatisticLaw_bounds (i : Row) (G : Measure (ℝ × ℝ)) :
    ∀ᵐ z ∂originalStatisticLaw i G, z ∈ Icc (0:ℝ) 1 := by
  rw [originalStatisticLaw, ae_add_measure_iff]
  constructor
  · exact Measure.ae_smul_measure
      ((ae_dirac_iff (by measurability)).mpr (by norm_num)) _
  · exact Measure.ae_smul_measure (lowerStatisticLaw_bounds i G) _

theorem lowerStatisticLaw_integrable (i : Row) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G] {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable f (lowerStatisticLaw i G) := by
  have hi := hf.integrableOn_Icc (μ := lowerStatisticLaw i G)
    (a := (0:ℝ)) (b := 1)
  change Integrable f ((lowerStatisticLaw i G).restrict (Icc 0 1)) at hi
  rwa [Measure.restrict_eq_self_of_ae_mem (lowerStatisticLaw_bounds i G)] at hi

theorem originalStatisticLaw_integral (i : Row) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G] {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ z, f z ∂originalStatisticLaw i G) = (1-cutoff i)*f (1/2)+
      cutoff i*(∫ p, f (physicalStatistic i p.2) ∂G) := by
  have hl := lowerStatisticLaw_integrable i G hf
  have hd : Integrable f (Measure.dirac (1/2:ℝ)) :=
    integrable_dirac (by finiteness)
  rw [originalStatisticLaw, integral_add_measure
    (hd.smul_measure ENNReal.ofReal_ne_top) (hl.smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal (by linarith [cutoff_lt_one i]),
    ENNReal.toReal_ofReal (cutoff_pos i).le, lowerStatisticLaw,
    integral_map
      (show AEMeasurable (fun p : ℝ×ℝ => physicalStatistic i p.2) G from
        ((continuous_physicalStatistic i).measurable.comp measurable_snd).aemeasurable)
      hf.measurable.aestronglyMeasurable]
  rfl

theorem originalStatisticLaw_mgf (i : Row) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G] (θ : ℝ) :
    mgf id (originalStatisticLaw i G) (-θ) =
      (1-cutoff i)*Real.exp (-θ/2)+cutoff i*
        (∫ p, Real.exp (-θ*physicalStatistic i p.2) ∂G) := by
  rw [mgf, originalStatisticLaw_integral i G (by fun_prop)]
  simp only [id_eq]
  congr 2
  ring

theorem originalStatisticLaw_cgf_gap (i : Row) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst = conditionalValueLaw i)
    (hfloor : ∀ᵐ p ∂G, physicalFloor i p.1 ≤ p.2) :
    cgf id (originalStatisticLaw i G) (-(thetaQ i : ℝ)) <
      -(thetaQ i : ℝ)*rho-rankI0 i-sourceGap i := by
  have hg := original_lower_chernoff_gap i G hvalue hfloor
  rw [cgf, originalStatisticLaw_mgf]
  linarith

theorem original_iid_bound (i : Row)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst = conditionalValueLaw i)
    (hfloor : ∀ᵐ p ∂G, physicalFloor i p.1 ≤ p.2)
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {N : ℕ} (hNnat : 0 < N) (Y : Fin N → Ω → ℝ)
    (hY : ∀ j, Measurable (Y j)) (hind : iIndepFun Y P)
    (hlaw : ∀ j, IdentDistrib (Y j) id P (originalStatisticLaw i G)) (c : ℝ) :
    P.real {ω | rowSum Y ω ≤ c} ≤
      Real.exp ((thetaQ i : ℝ)*c-
        N*((thetaQ i : ℝ)*rho+rankI0 i+sourceGap i)) := by
  let ν : ProbabilityMeasure ℝ := ⟨originalStatisticLaw i G, inferInstance⟩
  have hbound : ∀ j, ∀ᵐ ω ∂P, Y j ω ∈ Icc (0:ℝ) 1 := fun j =>
    (hlaw j).symm.ae_mem_snd measurableSet_Icc (originalStatisticLaw_bounds i G)
  have hrow := row_chernoff_bound P hY hind hbound
    (ν := ν) hlaw hNnat
    (u := -(thetaQ i : ℝ)) (r := c)
    (by cases i <;> norm_num [thetaQ])
  have hN : (0:ℝ) < N := by exact_mod_cast hNnat
  have hcgf := (originalStatisticLaw_cgf_gap i G hvalue hfloor).le
  calc
    _ ≤ _ := hrow
    _ ≤ _ := Real.exp_le_exp.mpr (by
      change (N:ℝ)*
        (cgf id (originalStatisticLaw i G) (-(thetaQ i : ℝ))-
          -(thetaQ i : ℝ)*(c/N)) ≤ _
      have hh := mul_le_mul_of_nonneg_left hcgf hN.le
      field_simp [hN.ne'] at *
      nlinarith)

theorem original_iid_row_bound (i : Row)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst = conditionalValueLaw i)
    (hfloor : ∀ᵐ p ∂G, physicalFloor i p.1 ≤ p.2)
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {m : ℕ} (hm : 2 ≤ m) (Y : Fin (m-1) → Ω → ℝ)
    (hY : ∀ j, Measurable (Y j)) (hind : iIndepFun Y P)
    (hlaw : ∀ j, IdentDistrib (Y j) id P (originalStatisticLaw i G)) :
    P.real {ω | rowSum Y ω ≤ (capacity m : ℝ)} ≤
      Real.exp ((thetaQ i : ℝ)*(capacity m : ℝ)-
        (m-1:ℕ)*((thetaQ i : ℝ)*rho+rankI0 i+sourceGap i)) :=
  original_iid_bound i G hvalue hfloor P (by omega) Y hY hind hlaw _

theorem exposure_antitone_price {ξ z₁ z₂ b : ℝ}
    (hξ : 0 < ξ) (hz₁ : 0 < z₁) (h12 : z₁ ≤ z₂) :
    exposure ξ z₂ b ≤ exposure ξ z₁ b := by
  by_cases hb₂ : b ≤ z₂
  · rw [exposure_zero hb₂]
    exact exposure_nonneg hξ hz₁
  · have hz₂b := lt_of_not_ge hb₂
    have hz₁b := h12.trans_lt hz₂b
    have hb0 := hz₁.trans hz₁b
    unfold exposure
    rw [max_eq_left hz₂b.le, max_eq_left hz₁b.le,
      max_eq_right (sub_nonneg.mpr hz₂b.le),
      max_eq_right (sub_nonneg.mpr hz₁b.le)]
    exact min_le_min_left 1
      (div_le_div_of_nonneg_right (sub_le_sub_left h12 b) (mul_pos hξ hb0).le)

theorem exposure_pos_iff {ξ z b : ℝ} (hξ : 0 < ξ) (hz : 0 < z) :
    0 < exposure ξ z b ↔ z < b := by
  constructor
  · intro hp
    by_contra h
    rw [exposure_zero (le_of_not_gt h)] at hp
    exact lt_irrefl 0 hp
  · intro hzb
    unfold exposure
    rw [max_eq_left hzb.le, max_eq_right (sub_nonneg.mpr hzb.le)]
    exact lt_min (by norm_num) (div_pos (sub_pos.mpr hzb) (mul_pos hξ (hz.trans hzb)))

section FiniteEvent

variable {ι : Type*} [Fintype ι]

theorem equal_count_event_inclusion
    {ξ Λ z b₀ p H c : ℝ} (b floor : ι → ℝ)
    (hξ : 0 < ξ) (hΛ : 0 < Λ) (hb₀ : b₀ ≤ z)
    (hp : p = exposure ξ Λ b₀) (hppos : 0 < p)
    (hfloor : ∀ j, floor j ≤ b j)
    (hclear : (∑ j, exposure ξ Λ (b j))+p+H/2=c) :
    (∑ j, exposure ξ z (floor j))+H/2 < c := by
  have hΛb : Λ < b₀ := (exposure_pos_iff hξ hΛ).mp (hp ▸ hppos)
  have hΛz := hΛb.le.trans hb₀
  have hz : 0 < z := hΛ.trans_le hΛz
  have hsum : (∑ j, exposure ξ z (floor j)) ≤ ∑ j, exposure ξ Λ (b j) := by
    apply Finset.sum_le_sum
    intro j _
    exact (exposure_monotone_bid hξ hz (hfloor j)).trans
      (exposure_antitone_price hξ hΛ hΛz)
  linarith

theorem low_bid_guarded_exposure_zero (i : Row) {Λ b : ℝ}
    (hΛ : (52/100:ℝ)*cutoff i ≤ Λ)
    (hb : b ≤ (501/1000:ℝ)*cutoff i) :
    exposure (xi i) Λ b = 0 := by
  apply exposure_zero
  have ht := cutoff_pos i
  nlinarith

end FiniteEvent

end FCAppendix.Affine.Uniform06.LowChernoff
