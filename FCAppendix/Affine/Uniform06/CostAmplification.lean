import FCAppendix.Probability.BoundedCGFComparison
import FCAppendix.Affine.Uniform06.ExactUntilting
import FCAppendix.Affine.Uniform06.RawMixedSource
import FCAppendix.Affine.Uniform06.ReciprocalSecantBounds

noncomputable section
namespace FCAppendix.Affine.Uniform06.CostAmplification

open MeasureTheory ProbabilityTheory Set LowBody
open FCAppendix.ExponentialTilt FCAppendix.Affine.ClippedResidual
open Uniform07 RawMixedSource

variable {Ω : Type*} [MeasurableSpace Ω]

theorem finite_cost_gap (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hXb : ∀ᵐ ω ∂μ,X ω ∈ Icc (0 : ℝ) 1)
    (hYb : ∀ᵐ ω ∂μ,Y ω ∈ Icc (0 : ℝ) 1)
    (hXY : ∀ᵐ ω ∂μ,X ω ≤ Y ω)
    {N : ℕ} (hN : 0 < N) {cap θX θY Θ δ : ℝ}
    (hθX : 0 ≤ θX) (hθXΘ : θX ≤ Θ)
    (hmatchY : (∫ ω,Y ω ∂μ.tilted (fun ω => -θY*Y ω))=cap/(N : ℝ))
    (hgap : δ ≤ ∫ ω,Y ω-X ω ∂μ) :
    (N : ℝ)*Real.exp (-Θ)*θX*δ ≤
      ExactUntilting.cost μ Y θY cap N-ExactUntilting.cost μ X θX cap N := by
  have hh := tilted_rate_gap_lower_of_unitInterval_order μ hX hY hXb hYb hXY
    (a := Θ) (u := -θX) (v := -θY) (r := cap/(N : ℝ)) (q := cap/(N : ℝ))
    (neg_nonpos.mpr hθX) (neg_le_neg hθXΘ) hmatchY
  simp only [sub_self,mul_zero,add_zero,abs_neg,abs_of_nonneg hθX] at hh
  have hδ := mul_le_mul_of_nonneg_left hgap
    (mul_nonneg (Real.exp_pos (-Θ)).le hθX)
  have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hm := mul_le_mul_of_nonneg_left (hδ.trans hh) hNr.le
  unfold ExactUntilting.cost
  convert! hm using 1
  · ring
  · field_simp [hNr.ne']

def activeStrip (b U : ℝ) : Set RowRival := {r | r.1=0 ∧ b < r.2 ∧ r.2 ≤ U}

theorem measurable_activeStrip (b U : ℝ) : MeasurableSet (activeStrip b U) :=
  (measurableSet_eq_fun measurable_fst measurable_const).inter
    ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const))

theorem active_exposure_gap {ξ lo hi U B : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hlo : 0 < lo) (hlh : lo < hi)
    (hU : 0 < U) (hBU : B ≤ U) (hhiB : hi < B)
    (hguard : (1-ξ)*U ≤ lo) :
    (hi-lo)/(ξ*U) ≤ exposure ξ lo B-exposure ξ hi B := by
  have hb : 0 < B := (hlo.trans hlh).trans hhiB
  have hR : U⁻¹ ≤ ReciprocalSecantBounds.reciprocalTerm B hi := by
    rw [ReciprocalSecantBounds.reciprocalTerm,if_pos hhiB]
    simpa only [one_div] using one_div_le_one_div_of_le hb hBU
  have hbr := (ReciprocalSecantBounds.exposure_secant_bracket
    hξ hξ1 hlo hlh hBU hguard).1
  have hstep := (mul_le_mul_of_nonneg_left hR (sub_pos.mpr hlh).le).trans hbr
  apply (div_le_iff₀ (mul_pos hξ hU)).mpr
  have hm := mul_le_mul_of_nonneg_right hstep hU.le
  have he : (hi-lo)*U⁻¹*U=hi-lo := by field_simp [hU.ne']
  rw [he] at hm
  nlinarith

theorem raw_demand_antitone_price {ξ lo hi : ℝ}
    (hξ : 0 < ξ) (hlo : 0 < lo) (hlh : lo ≤ hi) (r : RowRival) :
    demand ξ hi r ≤ demand ξ lo r := by
  unfold demand
  split_ifs
  · exact LowChernoff.exposure_antitone_price hξ hlo hlh
  · rfl
  · rfl

theorem original_active_gap (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {lo hi U : ℝ} (hlo : 0 < lo) (hlh : lo < hi) (hU : 0 < U)
    (hguard : (1-xi i)*U ≤ lo) :
    ((hi-lo)/(xi i*U))*(source i G).real (activeStrip hi U) ≤
      ∫ r,demand (xi i) lo r-demand (xi i) hi r ∂source i G := by
  let μ := source i G
  let δ := (hi-lo)/(xi i*U)
  have hδ : 0 ≤ δ := div_nonneg (sub_pos.mpr hlh).le (mul_pos (xi_pos i) hU).le
  have hXi : Integrable (demand (xi i) hi) μ := Integrable.of_mem_Icc 0 1
    (measurable_demand _ _).aemeasurable
    (ae_of_all _ fun r => demand_bounds (xi_pos i) (hlo.trans hlh) r)
  have hYi : Integrable (demand (xi i) lo) μ := Integrable.of_mem_Icc 0 1
    (measurable_demand _ _).aemeasurable
    (ae_of_all _ fun r => demand_bounds (xi_pos i) hlo r)
  have hInd := (integrable_const δ (μ := μ)).indicator (measurable_activeStrip hi U)
  have hh := integral_mono_ae hInd (hYi.sub hXi) (ae_of_all _ fun r => by
    dsimp only [Pi.sub_apply]
    by_cases hr : r ∈ activeStrip hi U
    · rw [indicator_of_mem hr]
      have he := active_exposure_gap (xi_pos i) (by cases i <;> norm_num [xi,xiQ,etaQ]) hlo hlh hU hr.2.2 hr.2.1 hguard
      simpa only [demand,hr.1,if_true] using he
    · rw [indicator_of_notMem hr]
      exact sub_nonneg.mpr (raw_demand_antitone_price (xi_pos i) hlo hlh.le r))
  rw [integral_indicator (measurable_activeStrip hi U),setIntegral_const] at hh
  dsimp only [μ,δ] at hh
  simpa only [Pi.sub_apply,smul_eq_mul,mul_comm] using hh

theorem original_cost_amplification (i : Row)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {lo hi U θlo θhi Θ τ q cap : ℝ} {N : ℕ} (hN : 0 < N)
    (hlo : 0 < lo) (hlh : lo < hi) (hU : 0 < U)
    (hguard : (1-xi i)*U ≤ lo) (hτ : 0 < τ) (hθlower : τ ≤ θhi) (hθupper : θhi ≤ Θ)
    (hq : 0 ≤ q) (hmass : q ≤ (source i G).real (activeStrip hi U))
    (hmatch : (∫ r,demand (xi i) lo r
      ∂(source i G).tilted (fun r => -θlo*demand (xi i) lo r))=cap/(N : ℝ)) :
    (N : ℝ)*(Real.exp (-Θ)*τ*q/(xi i*U))*(hi-lo) ≤
      ExactUntilting.cost (source i G) (demand (xi i) lo) θlo cap N-
        ExactUntilting.cost (source i G) (demand (xi i) hi) θhi cap N := by
  have hgap : ((hi-lo)/(xi i*U))*q ≤
      ∫ r,demand (xi i) lo r-demand (xi i) hi r ∂source i G :=
    (mul_le_mul_of_nonneg_left hmass (div_nonneg (sub_pos.mpr hlh).le (mul_pos (xi_pos i) hU).le)).trans
      (original_active_gap i G hlo hlh hU hguard)
  have hh := finite_cost_gap (source i G) (measurable_demand _ _) (measurable_demand _ _)
    (ae_of_all _ fun r => demand_bounds (xi_pos i) (hlo.trans hlh) r)
    (ae_of_all _ fun r => demand_bounds (xi_pos i) hlo r)
    (ae_of_all _ fun r => raw_demand_antitone_price (xi_pos i) hlo hlh.le r)
    hN (hτ.le.trans hθlower) hθupper hmatch hgap
  have hstep : (N : ℝ)*Real.exp (-Θ)*τ*(((hi-lo)/(xi i*U))*q) ≤
      (N : ℝ)*Real.exp (-Θ)*θhi*(((hi-lo)/(xi i*U))*q) := by
    have hn : (0:ℝ) ≤ N := Nat.cast_nonneg N
    have hfac : 0 ≤ (N:ℝ)*Real.exp (-Θ)*(((hi-lo)/(xi i*U))*q) :=
      mul_nonneg (mul_nonneg hn (Real.exp_pos _).le)
        (mul_nonneg (div_nonneg (sub_pos.mpr hlh).le (mul_pos (xi_pos i) hU).le) hq)
    nlinarith [mul_le_mul_of_nonneg_left hθlower hfac]
  calc
    _ = (N : ℝ)*Real.exp (-Θ)*τ*(((hi-lo)/(xi i*U))*q) := by ring
    _ ≤ _ := hstep.trans hh

theorem finite_kernel_amplification {Clo Chi Ilo Ihi n c U κ Δ : ℝ}
    (hn : 0 < n) (hc : 0 < c) (hU : 0 < U)
    (hClo : 0 < Clo)
    (hlo : Clo ≤ U/n^2*Real.exp (-Ilo))
    (hhi : c/n^2*Real.exp (-Ihi) ≤ Chi)
    (hgap : n*κ*Δ ≤ Ilo-Ihi) :
    (c/U)*Real.exp (n*κ*Δ) ≤ Chi/Clo := by
  have hscale : 0 < U/n^2*Real.exp (-Ilo) := by positivity
  have hnum : 0 ≤ c/n^2*Real.exp (-Ihi) := by positivity
  calc
    (c/U)*Real.exp (n*κ*Δ) ≤ (c/U)*Real.exp (Ilo-Ihi) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hgap) (div_pos hc hU).le
    _ = (c/n^2*Real.exp (-Ihi))/(U/n^2*Real.exp (-Ilo)) := by
      rw [Real.exp_sub,Real.exp_neg,Real.exp_neg]
      field_simp [hn.ne',hU.ne',(Real.exp_pos Ilo).ne',(Real.exp_pos Ihi).ne']
    _ ≤ (c/n^2*Real.exp (-Ihi))/Clo :=
      div_le_div_of_nonneg_left hnum hClo hlo
    _ ≤ Chi/Clo := div_le_div_of_nonneg_right hhi hClo.le

end FCAppendix.Affine.Uniform06.CostAmplification
