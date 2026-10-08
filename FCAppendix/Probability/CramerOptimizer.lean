import FCAppendix.Probability.BoundedLawConvergence
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.Analysis.SpecificLimits.Basic

namespace FCAppendix.CramerOptimizer
open MeasureTheory ProbabilityTheory Filter Topology Set Real
open FCAppendix.ExponentialTilt

variable (μ : ProbabilityMeasure ℝ)
    (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) 1)

include hμ

theorem analyticAt_cgf_all (u : ℝ) : AnalyticAt ℝ (cgf id (μ : Measure ℝ)) u := by
  apply analyticAt_cgf
  rw [integrableExpSet_eq_univ_of_bounded (μ : Measure ℝ)
    measurable_id.aemeasurable hμ, interior_univ]
  trivial

theorem mem_interior_all (u : ℝ) : u ∈ interior (integrableExpSet id (μ : Measure ℝ)) := by
  rw [integrableExpSet_eq_univ_of_bounded (μ : Measure ℝ)
    measurable_id.aemeasurable hμ, interior_univ]
  trivial

theorem differentiable_cgf : Differentiable ℝ (cgf id (μ : Measure ℝ)) :=
  fun u => (analyticAt_cgf_all μ hμ u).differentiableAt

theorem differentiable_deriv_cgf : Differentiable ℝ (deriv (cgf id (μ : Measure ℝ))) :=
  fun u => (analyticAt_cgf_all μ hμ u).deriv.differentiableAt

theorem second_deriv_nonneg (u : ℝ) : 0 ≤ deriv (deriv (cgf id (μ : Measure ℝ))) u := by
  have hv := variance_tilted_mul (mem_interior_all μ hμ u)
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one] at hv
  rw [← hv]
  exact variance_nonneg _ _

theorem convex_cgf : ConvexOn ℝ univ (cgf id (μ : Measure ℝ)) :=
  convexOn_univ_of_deriv2_nonneg (differentiable_cgf μ hμ)
    (differentiable_deriv_cgf μ hμ) (second_deriv_nonneg μ hμ)

theorem second_deriv_pos
    (hnonconstant : ∀ c : ℝ, ¬ (∀ᵐ x ∂(μ : Measure ℝ), x = c)) (u : ℝ) :
    0 < deriv (deriv (cgf id (μ : Measure ℝ))) u := by
  have ht := integrable_exp_mul_of_bounded (μ : Measure ℝ) measurable_id.aemeasurable hμ u
  haveI : IsProbabilityMeasure ((μ : Measure ℝ).tilted (fun x => u * x)) :=
    isProbabilityMeasure_tilted ht
  apply lt_of_le_of_ne (second_deriv_nonneg μ hμ u)
  intro he
  have hv := variance_tilted_mul (mem_interior_all μ hμ u)
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, ← he] at hv
  have ha := ae_eq_integral_of_variance_eq_zero
    (memLp_tilted_mul (mem_interior_all μ hμ u) 2) hv
  exact hnonconstant _ ((absolutelyContinuous_tilted ht) ha)

theorem strictMono_deriv_cgf
    (hnonconstant : ∀ c : ℝ, ¬ (∀ᵐ x ∂(μ : Measure ℝ), x = c)) :
    StrictMono (deriv (cgf id (μ : Measure ℝ))) :=
  strictMono_of_deriv_pos (second_deriv_pos μ hμ hnonconstant)

theorem variational_le_at_mean {u ρ : ℝ}
    (hmean : deriv (cgf id (μ : Measure ℝ)) u = ρ) (v : ℝ) :
    v * ρ - cgf id (μ : Measure ℝ) v ≤ u * ρ - cgf id (μ : Measure ℝ) u := by
  rcases lt_trichotomy v u with hv | rfl | hv
  · have hh := (convex_cgf μ hμ).slope_le_deriv (mem_univ v) (mem_univ u) hv
      (differentiable_cgf μ hμ u)
    rw [hmean, slope_def_field] at hh
    have he := (div_le_iff₀ (sub_pos.mpr hv)).mp hh
    nlinarith
  · rfl
  · have hh := (convex_cgf μ hμ).deriv_le_slope (mem_univ u) (mem_univ v) hv
      (differentiable_cgf μ hμ u)
    rw [hmean, slope_def_field] at hh
    have he := (le_div_iff₀ (sub_pos.mpr hv)).mp hh
    nlinarith

theorem cgf_ge_lower_mass {a u : ℝ} (hp : 0 < (μ : Measure ℝ).real (Iic a))
    (hu : u ≤ 0) : u * a + log ((μ : Measure ℝ).real (Iic a)) ≤ cgf id (μ : Measure ℝ) u := by
  have ht := integrable_exp_mul_of_bounded (μ : Measure ℝ) measurable_id.aemeasurable hμ u
  have hi := setIntegral_mono_on (integrable_const (exp (u * a))) ht.integrableOn
    measurableSet_Iic (fun x hx => exp_le_exp.mpr (mul_le_mul_of_nonpos_left hx hu))
  rw [setIntegral_const, smul_eq_mul] at hi
  have ht' := setIntegral_le_integral (s := Iic a) ht
    (Filter.Eventually.of_forall fun x => (exp_pos (u * id x)).le)
  have hbound : exp (u * a) * (μ : Measure ℝ).real (Iic a) ≤ mgf id (μ : Measure ℝ) u := by
    simpa only [mgf, mul_comm] using hi.trans ht'
  have hl := log_le_log (mul_pos (exp_pos _) hp) hbound
  rwa [log_mul (exp_ne_zero _) hp.ne', log_exp] at hl

omit hμ in

theorem nonconstant_of_lower_mass {a ρ : ℝ} (ha : a < ρ)
    (hp : 0 < (μ : Measure ℝ).real (Iic a)) (hmean : ρ < ∫ x, x ∂(μ : Measure ℝ)) :
    ∀ c : ℝ, ¬ (∀ᵐ x ∂(μ : Measure ℝ), x = c) := by
  intro c hc
  have hm : (∫ x, x ∂(μ : Measure ℝ)) = c := by
    calc
      _ = ∫ _, c ∂(μ : Measure ℝ) := integral_congr_ae hc
      _ = c := by simp
  have hz : (μ : Measure ℝ) (Iic a) = 0 :=
    measure_eq_zero_iff_ae_notMem.mpr (hc.mono fun x hx => by
      change ¬ x ≤ a
      rw [hx]
      linarith)
  have hr : (μ : Measure ℝ).real (Iic a) = 0 := by simp [Measure.real, hz]
  linarith

theorem exists_negative_tilt {a ρ : ℝ} (ha : a < ρ)
    (hp : 0 < (μ : Measure ℝ).real (Iic a)) (hmean : ρ < ∫ x, x ∂(μ : Measure ℝ)) :
    ∃ u : ℝ, u < 0 ∧ deriv (cgf id (μ : Measure ℝ)) u = ρ := by
  let p := (μ : Measure ℝ).real (Iic a)
  let v := (|log p| + 1) / (a - ρ)
  have hv : v < 0 := div_neg_of_pos_of_neg (by positivity) (sub_neg.mpr ha)
  have hvprod : v * (a - ρ) = |log p| + 1 :=
    div_mul_cancel₀ _ (sub_ne_zero.mpr ha.ne)
  let f : ℝ → ℝ := fun x => cgf id (μ : Measure ℝ) x - ρ * x
  have hf : Differentiable ℝ f := (differentiable_cgf μ hμ).sub (differentiable_id.const_mul ρ)
  have hf0 : f 0 = 0 := by simp [f]
  have hfv : 0 < f v := by
    have hb := cgf_ge_lower_mass μ hμ hp hv.le
    have habs := neg_le_abs (log p)
    change v * a + log p ≤ cgf id (μ : Measure ℝ) v at hb
    dsimp [f]
    nlinarith
  obtain ⟨w, hw, hderiv⟩ := exists_deriv_eq_slope f hv hf.continuous.continuousOn hf.differentiableOn
  have hdw : deriv (cgf id (μ : Measure ℝ)) w < ρ := by
    have he : deriv f w = deriv (cgf id (μ : Measure ℝ)) w - ρ := by
      simpa [f, Pi.sub_apply] using
        (deriv_fun_sub (differentiable_cgf μ hμ w) (differentiable_id.const_mul ρ w))
    rw [hf0, he] at hderiv
    have hh : (0 - f v) / (0 - v) < 0 := div_neg_of_neg_of_pos (by linarith) (by linarith)
    linarith
  have hd0 : ρ < deriv (cgf id (μ : Measure ℝ)) 0 := by
    simpa only [deriv_cgf_zero (mem_interior_all μ hμ 0), probReal_univ, div_one, id_eq] using hmean
  obtain ⟨u, hu, hdu⟩ := intermediate_value_Icc hw.2.le
    (differentiable_deriv_cgf μ hμ).continuous.continuousOn ⟨hdw.le, hd0.le⟩
  refine ⟨u, lt_of_le_of_ne hu.2 ?_, hdu⟩
  intro heq
  rw [heq] at hdu
  linarith

theorem exists_lower_mass_of_essInf_lt {ρ : ℝ}
    (hρ : essInf id (μ : Measure ℝ) < ρ) :
    ∃ a : ℝ, a < ρ ∧ 0 < (μ : Measure ℝ).real (Iic a) := by
  obtain ⟨a, ha, haρ⟩ := exists_between hρ
  refine ⟨a, haρ, ?_⟩
  have hn : (μ : Measure ℝ) (Iic a) ≠ 0 := by
    intro hz
    have hl : ∀ᵐ x ∂(μ : Measure ℝ), a ≤ id x :=
      (measure_eq_zero_iff_ae_notMem.mp hz).mono fun x hx => (lt_of_not_ge hx).le
    have hb : IsCoboundedUnder (· ≥ ·) (ae (μ : Measure ℝ)) id :=
      isCoboundedUnder_ge_of_eventually_le _ (hμ.mono fun _ hx => hx.2)
    exact ha.not_ge (le_essInf_of_ae_le a hl hb)
  exact lt_of_le_of_ne measureReal_nonneg
    (Ne.symm ((measureReal_ne_zero_iff).mpr hn))

theorem exists_negative_tilt_of_essInf {ρ : ℝ}
    (hlower : essInf id (μ : Measure ℝ) < ρ)
    (hmean : ρ < ∫ x, x ∂(μ : Measure ℝ)) :
    ∃ u : ℝ, u < 0 ∧ deriv (cgf id (μ : Measure ℝ)) u = ρ := by
  obtain ⟨a, ha, hp⟩ := exists_lower_mass_of_essInf_lt μ hμ hlower
  exact exists_negative_tilt μ hμ ha hp hmean

noncomputable def lowerRate (ρ : ℝ) : ℝ :=
  sSup ((fun u : ℝ => u * ρ - cgf id (μ : Measure ℝ) u) '' Iic 0)

theorem lowerRate_eq {ρ u : ℝ} (hu : u ≤ 0)
    (hmean : deriv (cgf id (μ : Measure ℝ)) u = ρ) :
    lowerRate μ ρ = u * ρ - cgf id (μ : Measure ℝ) u := by
  have hb : BddAbove ((fun v : ℝ => v * ρ - cgf id (μ : Measure ℝ) v) '' Iic 0) := by
    refine ⟨u * ρ - cgf id (μ : Measure ℝ) u, ?_⟩
    rintro _ ⟨v, _, rfl⟩
    exact variational_le_at_mean μ hμ hmean v
  have hn : ((fun v : ℝ => v * ρ - cgf id (μ : Measure ℝ) v) '' Iic 0).Nonempty :=
    ⟨_, ⟨u, hu, rfl⟩⟩
  unfold lowerRate
  apply le_antisymm
  · apply csSup_le hn
    rintro _ ⟨v, _, rfl⟩
    exact variational_le_at_mean μ hμ hmean v
  · exact le_csSup hb ⟨u, hu, rfl⟩

theorem exists_tilt_lower_bound {ρ c : ℝ}
    (hlower : essInf id (μ : Measure ℝ) < ρ)
    (hmean : ρ < ∫ x, x ∂(μ : Measure ℝ)) (hc : c < -lowerRate μ ρ) :
    ∃ v : ℝ, v ≤ 0 ∧ deriv (cgf id (μ : Measure ℝ)) v < ρ ∧
      c < cgf id (μ : Measure ℝ) v - v * deriv (cgf id (μ : Measure ℝ)) v := by
  obtain ⟨a, ha, hp⟩ := exists_lower_mass_of_essInf_lt μ hμ hlower
  have hnc := nonconstant_of_lower_mass μ ha hp hmean
  obtain ⟨u, hu, hdu⟩ := exists_negative_tilt μ hμ ha hp hmean
  let v : ℕ → ℝ := fun n => u - 1 / (n + 1 : ℕ)
  have hvlim : Tendsto v atTop (𝓝 u) := by
    simpa only [v, Function.comp_def, sub_zero] using
      tendsto_const_nhds.sub (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ) |>.comp
        (tendsto_add_atTop_nat 1))
  have hfun := ((differentiable_cgf μ hμ).continuous.continuousAt.tendsto.comp hvlim).sub
    (hvlim.mul ((differentiable_deriv_cgf μ hμ).continuous.continuousAt.tendsto.comp hvlim))
  have hrate : cgf id (μ : Measure ℝ) u - u * deriv (cgf id (μ : Measure ℝ)) u =
      -lowerRate μ ρ := by rw [hdu, lowerRate_eq μ hμ hu.le hdu]; ring
  rw [hrate] at hfun
  obtain ⟨n, hn⟩ := (hfun.eventually_const_lt hc).exists
  have hvu : v n < u := sub_lt_self _ (by positivity)
  refine ⟨v n, hvu.le.trans hu.le, ?_, hn⟩
  rw [← hdu]
  exact strictMono_deriv_cgf μ hμ hnc hvu

end FCAppendix.CramerOptimizer
