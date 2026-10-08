import FCAppendix.PayOnce.BinomialContinuity
import FCAppendix.Probability.UnitInterval
import FCAppendix.Probability.NormalizedMoments

namespace FCAppendix.PayOnce.ManyProposers
open MeasureTheory ProbabilityTheory Set Filter Topology

theorem binomialMass_entry_remainder (n j : ℕ) {p : ℝ} (hp : p ∈ Icc (0:ℝ) 1) :
    |binomialMass n p j-(n.choose j:ℝ)*p^j| ≤
      (n.choose j:ℝ)*(n-j:ℕ)*p^(j+1) := by
  have hp' : 1-p ∈ Icc (0:ℝ) 1 := ⟨by linarith [hp.2],by linarith [hp.1]⟩
  have hmax : max |1-p| |(1:ℝ)| ≤ 1 := by
    rw [abs_of_nonneg hp'.1,abs_one]
    exact max_le hp'.2 le_rfl
  have hb := abs_pow_sub_pow_le (1-p) 1 (n-j)
  have hpw := pow_le_one₀ (le_max_of_le_left (abs_nonneg (1-p))) hmax (n := n-j-1)
  have hd : |(1-p)^(n-j)-1| ≤ (n-j:ℕ)*p := by
    have hh := mul_le_mul_of_nonneg_left hpw
      (mul_nonneg (abs_nonneg ((1-p)-1)) (Nat.cast_nonneg (n-j)))
    simp only [one_pow,sub_sub_cancel_left,abs_neg,abs_of_nonneg hp.1,mul_one] at hb hh
    nlinarith
  unfold binomialMass
  rw [show (n.choose j:ℝ)*p^j*(1-p)^(n-j)-(n.choose j:ℝ)*p^j =
    ((n.choose j:ℝ)*p^j)*((1-p)^(n-j)-1) by ring,
    abs_mul,abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp.1 _))]
  calc
    _ ≤ ((n.choose j:ℝ)*p^j)*((n-j:ℕ)*p) :=
      mul_le_mul_of_nonneg_left hd (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp.1 _))
    _ = _ := by rw [pow_succ]; ring

theorem binomialMass_integral_asymptotic
    {Ω : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)]
    (μ : (t : ℕ) → Measure (Ω t)) [∀ t, IsProbabilityMeasure (μ t)]
    (p : (t : ℕ) → Ω t → ℝ) (hp : ∀ t, Measurable (p t))
    (hpb : ∀ t ω, p t ω ∈ Icc (0:ℝ) 1)
    (s : ℕ → ℝ) (hsp : ∀ᶠ t in atTop, 0 < s t) (hs : Tendsto s atTop (𝓝 0))
    (n j : ℕ) {a b : ℝ}
    (ha : Tendsto (fun t => (∫ ω, (p t ω)^j ∂μ t)/(s t)^j) atTop (𝓝 a))
    (hb : Tendsto (fun t => (∫ ω, (p t ω)^(j+1) ∂μ t)/(s t)^(j+1)) atTop (𝓝 b)) :
    Tendsto (fun t => (∫ ω, binomialMass n (p t ω) j ∂μ t)/(s t)^j)
      atTop (𝓝 ((n.choose j:ℝ)*a)) := by
  have hi t (r : ℕ) : Integrable (fun ω => (p t ω)^r) (μ t) := by
    have hh := (Probability.memLp_unitInterval_div_pow (μ t) (p t) (hp t) (hpb t) 1 r).integrable (by norm_num)
    simpa only [div_one] using hh
  have hbin t : Integrable (fun ω => binomialMass n (p t ω) j) (μ t) :=
    UnitInterval.integrable _ _ ((continuous_binomialMass n j).measurable.comp (hp t))
      (fun ω => (binomialMass_bounds n j (hpb t ω)).1)
      (fun ω => (binomialMass_bounds n j (hpb t ω)).2)
  have hrem : Tendsto (fun t => (∫ ω, binomialMass n (p t ω) j ∂μ t)/(s t)^j-
      (n.choose j:ℝ)*((∫ ω, (p t ω)^j ∂μ t)/(s t)^j)) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    apply squeeze_zero' (.of_forall fun _ => abs_nonneg _)
      (g := fun t => ((n.choose j:ℝ)*(n-j:ℕ))*s t*
        ((∫ ω, (p t ω)^(j+1) ∂μ t)/(s t)^(j+1))) ?_
      (by simpa only [mul_zero,zero_mul] using (hs.const_mul ((n.choose j:ℝ)*(n-j:ℕ))).mul hb)
    filter_upwards [hsp] with t hst
    have hbound : |(∫ ω, binomialMass n (p t ω) j ∂μ t)-
        (n.choose j:ℝ)*(∫ ω, (p t ω)^j ∂μ t)| ≤
        ((n.choose j:ℝ)*(n-j:ℕ))*(∫ ω, (p t ω)^(j+1) ∂μ t) := by
      rw [← integral_const_mul,← integral_sub (hbin t) ((hi t j).const_mul _)]
      apply abs_integral_le_integral_abs.trans
      have hh := integral_mono ((hbin t).sub ((hi t j).const_mul _)).abs
        ((hi t (j+1)).const_mul ((n.choose j:ℝ)*(n-j:ℕ))) (fun ω => binomialMass_entry_remainder n j (hpb t ω))
      simpa only [Pi.sub_apply,integral_const_mul] using hh
    have he : ((n.choose j:ℝ)*(n-j:ℕ))*(∫ ω, (p t ω)^(j+1) ∂μ t)/(s t)^j =
        ((n.choose j:ℝ)*(n-j:ℕ))*s t*((∫ ω, (p t ω)^(j+1) ∂μ t)/(s t)^(j+1)) := by
      rw [pow_succ]
      field_simp
    have hh := div_le_div_of_nonneg_right hbound (pow_nonneg hst.le j)
    rw [he] at hh
    simpa only [← mul_div_assoc,← sub_div,abs_div,abs_of_pos (pow_pos hst j)] using hh
  have hh := hrem.add (ha.const_mul (n.choose j:ℝ))
  simpa only [sub_add_cancel,zero_add] using hh

end FCAppendix.PayOnce.ManyProposers
