import FCAppendix.Probability.ClippedSubGaussianMoments
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace FCAppendix.Probability
open MeasureTheory ProbabilityTheory Set Filter Topology
variable {Ω : Type*} [MeasurableSpace Ω]

theorem unitInterval_mean_le_exponential_tail
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Y : Ω → ℝ} (hY : Measurable Y)
    (hb : ∀ ω, Y ω ∈ Icc (0:ℝ) 1) {A B k : ℝ} (hA : 0 ≤ A) (hk : 0 < k)
    (htail : ∀ t ∈ Ioc (0:ℝ) 1, μ.real {ω | t ≤ Y ω} ≤ A*Real.exp (-k*t)+B) :
    (∫ ω, Y ω ∂μ) ≤ A/k+B := by
  have hmean := integral_rpow_eq_bounded_tail μ hY (by norm_num : (0:ℝ) ≤ 1)
    (r := 1) (by norm_num) hb
  simp only [Real.rpow_one,sub_self,Real.rpow_zero,mul_one,one_mul] at hmean
  have hi : IntegrableOn (fun t : ℝ => μ.real {ω | t ≤ Y ω}) (Ioc 0 1) := by
    simpa only [sub_self,Real.rpow_zero,mul_one] using
      integrable_bounded_tail_weight μ Y (D := 1) (r := 1) (by norm_num)
  have he := integrableOn_exp_mul_Ioi (show -k < 0 by linarith) 0
  have hei := he.mono_set (show Ioc (0:ℝ) 1 ⊆ Ioi 0 from Ioc_subset_Ioi_self)
  have hbi : IntegrableOn (fun _ : ℝ => B) (Ioc 0 1) := integrable_const _
  have hbound : (∫ t in Ioc (0:ℝ) 1, μ.real {ω | t ≤ Y ω}) ≤
      ∫ t in Ioc (0:ℝ) 1, A*Real.exp (-k*t)+B := by
    apply integral_mono_ae hi ((hei.const_mul A).add hbi)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact htail t ht
  have hmono : (∫ t : ℝ in Ioc 0 1, Real.exp (-k*t)) ≤
      ∫ t : ℝ in Ioi 0, Real.exp (-k*t) := by
    apply setIntegral_mono_set he
      (Eventually.of_forall fun _ => (Real.exp_pos _).le)
      (Eventually.of_forall fun _ ht => ht.1)
  have hfull : (∫ t : ℝ in Ioi 0, Real.exp (-k*t)) = 1/k := by
    rw [integral_exp_mul_Ioi (show -k < 0 by linarith) 0]
    simp
  rw [integral_add (hei.const_mul A) hbi,integral_const_mul,integral_const] at hbound
  norm_num [Measure.real,Real.volume_Ioc,smul_eq_mul] at hbound
  rw [hfull] at hmono
  rw [hmean]
  calc
    _ ≤ A*(∫ t : ℝ in Ioc 0 1, Real.exp (-k*t))+B := by simpa only [Measure.real,neg_mul] using hbound
    _ ≤ A*(1/k)+B := add_le_add (mul_le_mul_of_nonneg_left hmono hA) le_rfl
    _ = A/k+B := by ring

theorem unitInterval_mean_le_local_exponential_tail
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Y : Ω → ℝ} (hY : Measurable Y)
    (hb : ∀ ω, Y ω ∈ Icc (0:ℝ) 1) {A k ε : ℝ}
    (hA : 0 ≤ A) (hk : 0 < k) (hε : 0 < ε)
    (htail : ∀ t ∈ Ioc (0:ℝ) ε, μ.real {ω | t ≤ Y ω} ≤ A*Real.exp (-k*t)) :
    (∫ ω, Y ω ∂μ) ≤ A*(1+1/ε)/k := by
  have hh := unitInterval_mean_le_exponential_tail μ hY hb hA hk
    (B := A*Real.exp (-k*ε)) (by
      intro t ht
      by_cases htε : t ≤ ε
      · exact (htail t ⟨ht.1,htε⟩).trans (le_add_of_nonneg_right (by positivity))
      · have hm : μ.real {ω | t ≤ Y ω} ≤ μ.real {ω | ε ≤ Y ω} :=
          measureReal_mono (h₂ := measure_ne_top _ _)
            (fun _ h => (le_of_not_ge htε).trans h)
        exact (hm.trans (htail ε ⟨hε,le_rfl⟩)).trans
          (le_add_of_nonneg_left (by positivity)))
  have hexp : Real.exp (-k*ε) ≤ 1/(k*ε) := by
    apply (le_div_iff₀ (mul_pos hk hε)).mpr
    have he := (Real.mul_exp_neg_le_exp_neg_one (k*ε)).trans
      (Real.exp_le_one_iff.mpr (by norm_num : (-1:ℝ) ≤ 0))
    simpa only [neg_mul] using (show Real.exp (-(k*ε))*(k*ε) ≤ 1 by nlinarith [he])
  calc
    (∫ ω, Y ω ∂μ) ≤ A/k+A*Real.exp (-k*ε) := hh
    _ ≤ A/k+A*(1/(k*ε)) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hexp hA)
    _ = A*(1+1/ε)/k := by ring

theorem hazard_ratio_le_of_local_allocation_tail
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Y : Ω → ℝ} (hY : Measurable Y)
    (hb : ∀ ω, Y ω ∈ Icc (0:ℝ) 1) {A k ε c Q D : ℝ} {n : ℕ}
    (hA : 0 ≤ A) (hk : 0 < k) (hε : 0 < ε) (hc : 0 < c)
    (hF : 0 < μ.real {ω | 0 < Y ω})
    (htail : ∀ t ∈ Ioc (0:ℝ) ε,
      μ.real {ω | t ≤ Y ω} ≤ A*μ.real {ω | 0 < Y ω}*Real.exp (-k*t))
    (hQ : Q ≤ (n:ℝ)*(∫ ω, Y ω ∂μ))
    (hD : c*μ.real {ω | 0 < Y ω} ≤ D) :
    Q/D ≤ (n:ℝ)*A*(1+1/ε)/(c*k) := by
  have hDp : 0 < D := (mul_pos hc hF).trans_le hD
  have hm := unitInterval_mean_le_local_exponential_tail μ hY hb (mul_nonneg hA hF.le) hk hε htail
  have hq := hQ.trans (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg n))
  apply (div_le_iff₀ hDp).mpr
  calc
    Q ≤ (n:ℝ)*(A*μ.real {ω | 0 < Y ω}*(1+1/ε)/k) := hq
    _ = ((n:ℝ)*A*(1+1/ε)/(c*k))*(c*μ.real {ω | 0 < Y ω}) := by
      field_simp
    _ ≤ ((n:ℝ)*A*(1+1/ε)/(c*k))*D := mul_le_mul_of_nonneg_left hD (by positivity)

end FCAppendix.Probability
