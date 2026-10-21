import FCAppendix.Affine.Uniform06.EntryActiveLimit
import FCAppendix.Affine.Uniform06.TiltStability

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryActiveMoments
open MeasureTheory ProbabilityTheory Set Filter Topology
open FCAppendix.Affine.ClippedResidual
open FCAppendix.Affine.Uniform06
open FCAppendix.Affine.Uniform06.EntryActiveLimit
open FCAppendix.Affine.Uniform07
open FCAppendix.ExponentialTilt

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
lemma map_unit_bounds {X : Ω → ℝ} (hX : Measurable X)
    (hb : ∀ᵐ ω ∂μ, X ω ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ x ∂μ.map X, x ∈ Icc (0 : ℝ) 1 :=
  (ae_map_iff hX.aemeasurable measurableSet_Icc).mpr hb

theorem bounded_power_integral_tendsto
    (X : ℕ → Ω → ℝ) (X0 : Ω → ℝ) (hX : ∀ m, Measurable (X m))
    (hb : ∀ m, ∀ᵐ ω ∂μ, X m ω ∈ Icc (0 : ℝ) 1)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun m => X m ω) atTop (𝓝 (X0 ω))) (k : ℕ) :
    Tendsto (fun m => ∫ ω, (X m ω)^k ∂μ) atTop (𝓝 (∫ ω, (X0 ω)^k ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ : Ω => (1 : ℝ))
  · intro m
    exact ((hX m).pow_const k).aestronglyMeasurable
  · exact integrable_const _
  · intro m
    filter_upwards [hb m] with ω hω
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hω.1 k)]
    exact pow_le_one₀ hω.1 hω.2
  · exact hlim.mono fun _ h => h.pow k

theorem balanced_scalar_moment (i : Row) {X : Ω → ℝ}
    (hX : Measurable X) (hb : ∀ᵐ ω ∂μ, X ω ∈ Icc (0 : ℝ) 1) (k : ℕ) :
    (∫ p, p.1^k ∂MixedLaw.law i (μ.map X))=
      (1-cutoff i)*(1/2 : ℝ)^k+cutoff i*(∫ ω, (X ω)^k ∂μ) := by
  letI : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  rw [MixedLaw.integral_law i _ (map_unit_bounds μ hX hb) (by fun_prop),
    integral_map hX.aemeasurable (by fun_prop)]
  simp only [smul_eq_mul]
  ring

theorem balanced_scalar_variance (i : Row) {X : Ω → ℝ}
    (hX : Measurable X) (hb : ∀ᵐ ω ∂μ, X ω ∈ Icc (0 : ℝ) 1) :
    variance Prod.fst (MixedLaw.law i (μ.map X))=
      ((1-cutoff i)/4+cutoff i*(∫ ω, (X ω)^2 ∂μ))-
        ((1-cutoff i)/2+cutoff i*(∫ ω, X ω ∂μ))^2 := by
  letI : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have hLp := memLp_of_bounded (MixedLaw.demand_bounds i _ (map_unit_bounds μ hX hb))
    measurable_fst.aestronglyMeasurable 2
  rw [variance_eq_sub hLp]
  have h1 := balanced_scalar_moment μ i hX hb 1
  have h2 := balanced_scalar_moment μ i hX hb 2
  norm_num only [pow_one] at h1
  simp only [Pi.pow_apply]
  rw [h1,h2]
  ring

theorem balanced_scalar_variance_tendsto (i : Row)
    (X : ℕ → Ω → ℝ) (X0 : Ω → ℝ)
    (hX : ∀ m, Measurable (X m)) (hX0 : Measurable X0)
    (hb : ∀ m, ∀ᵐ ω ∂μ, X m ω ∈ Icc (0 : ℝ) 1)
    (hb0 : ∀ᵐ ω ∂μ, X0 ω ∈ Icc (0 : ℝ) 1)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun m => X m ω) atTop (𝓝 (X0 ω))) :
    Tendsto (fun m => variance Prod.fst (MixedLaw.law i (μ.map (X m))))
      atTop (𝓝 (variance Prod.fst (MixedLaw.law i (μ.map X0)))) := by
  simp_rw [balanced_scalar_variance μ i (hX _) (hb _),balanced_scalar_variance μ i hX0 hb0]
  have h1 := bounded_power_integral_tendsto μ X X0 hX hb hlim 1
  have h2 := bounded_power_integral_tendsto μ X X0 hX hb hlim 2
  simp only [pow_one] at h1
  exact (tendsto_const_nhds.add (h2.const_mul _)).sub
    ((tendsto_const_nhds.add (h1.const_mul _)).pow 2)

omit [IsProbabilityMeasure μ] in

theorem physicalLowerLaw_pure_joint (i : Row) {b : ℝ} (hb : 0 < b)
    (V B : Ω → ℝ) (hV : Measurable V) (hB : Measurable B) :
    MixedLaw.physicalLowerLaw i b (μ.map (fun ω => (V ω,B ω)))=
      μ.map (fun ω => exposure (xi i) b (B ω)) := by
  unfold MixedLaw.physicalLowerLaw
  rw [Measure.map_map (g := fun p : ℝ × ℝ => exposure (xi i) b p.2)
    ((continuous_exposure (xi_pos i) hb).measurable.comp measurable_snd) (hV.prodMk hB)]
  rfl

theorem actual_entry_variance_tendsto (i : Row)
    (V : Ω → ℝ) (B : ℕ → Ω → ℝ) (hV : Measurable V)
    (hB : ∀ m, Measurable (B m)) (b : ℕ → ℝ) (hbp : ∀ m, 0 < b m)
    (hb : Tendsto b atTop (𝓝 (entry i)))
    (hadmissible : ∀ m, ∀ᵐ ω ∂μ, B m ω ≤ V ω)
    (hthreshold : ∀ᵐ ω ∂μ, V ω ≠ entry i)
    (hactive : ∀ᵐ ω ∂μ, entry i < V ω → Tendsto (fun m => B m ω) atTop
      (𝓝 (ActiveGraphComponent.activeBid i (V ω)))) :
    Tendsto (fun m => variance Prod.fst
      (MixedLaw.law i (MixedLaw.physicalLowerLaw i (b m)
        (μ.map (fun ω => (V ω,B m ω)))))) atTop
      (𝓝 (variance Prod.fst (MixedLaw.law i (μ.map
        (fun ω => activeExposure (xi i) (entry i) (ActiveGraphComponent.activeBid i) (V ω)))))) := by
  simp_rw [physicalLowerLaw_pure_joint μ i (hbp _) V _ hV (hB _)]
  have hB0 : Measurable (ActiveGraphComponent.activeBid i) := by
    unfold ActiveGraphComponent.activeBid
    fun_prop
  apply balanced_scalar_variance_tendsto μ i _ _
    (fun m => (continuous_exposure (xi_pos i) (hbp m)).measurable.comp (hB m))
    ((measurable_activeExposure (xi_pos i) (EarlyMean.entry_pos i) hB0).comp hV)
    (fun m => Eventually.of_forall fun _ =>
      ⟨exposure_nonneg (xi_pos i) (hbp m),exposure_le_one _ _ _⟩)
    (Eventually.of_forall fun _ => activeExposure_bounds (xi_pos i) (EarlyMean.entry_pos i) _ _)
  exact entry_exposure_tendsto_ae μ V B _ (xi_pos i) (EarlyMean.entry_pos i)
    b hb hadmissible hthreshold hactive

theorem actual_tilted_variance_tendsto
    {Ξ : ℕ → Type*} [∀ m, MeasurableSpace (Ξ m)]
    (P : (m : ℕ) → Measure (Ξ m)) [∀ m, IsProbabilityMeasure (P m)]
    (X : (m : ℕ) → Ξ m → ℝ) (hX : ∀ m, Measurable (X m))
    (hb : ∀ m, ∀ᵐ ω ∂P m, X m ω ∈ Icc (0 : ℝ) 1)
    (u : ℕ → ℝ) (hu : Tendsto u atTop (𝓝 0)) {v : ℝ}
    (hv : Tendsto (fun m => variance (X m) (P m)) atTop (𝓝 v)) :
    Tendsto (fun m => variance (X m) ((P m).tilted (fun ω => u m*X m ω)))
      atTop (𝓝 v) := by
  have hlo : Tendsto (fun m => Real.exp (-2*|u m|)*variance (X m) (P m)) atTop (𝓝 v) := by
    have hneg : Tendsto (fun m => -2*|u m|) atTop (𝓝 0) := by
      simpa only [abs_zero,mul_zero] using hu.abs.const_mul (-2)
    convert! ((Real.continuous_exp.tendsto 0).comp hneg).mul hv using 1
    norm_num
  have hhi : Tendsto (fun m => Real.exp (2*|u m|)*variance (X m) (P m)) atTop (𝓝 v) := by
    have hpos : Tendsto (fun m => 2*|u m|) atTop (𝓝 0) := by
      simpa only [abs_zero,mul_zero] using hu.abs.const_mul 2
    convert! ((Real.continuous_exp.tendsto 0).comp hpos).mul hv using 1
    norm_num
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
  · intro m
    exact (tilted_variance_bounds (P m) (hX m) (hb m) (le_refl |u m|)).1
  · intro m
    exact (tilted_variance_bounds (P m) (hX m) (hb m) (le_refl |u m|)).2

theorem exposure_upper_of_linear_guard {ξ b B U c : ℝ}
    (hξ : 0 < ξ) (hb : 0 < b) (hc : 0 ≤ c) (hcoeff : 0 ≤ 1-ξ*c)
    (hBU : B ≤ U) (hguard : (1-ξ*c)*U ≤ b) : exposure ξ b B ≤ c := by
  by_cases hBb : B ≤ b
  · rw [exposure_zero hBb]
    exact hc
  · have hB : b < B := lt_of_not_ge hBb
    have hB0 : 0 < B := hb.trans hB
    have hlin : (1-ξ*c)*B ≤ b :=
      (mul_le_mul_of_nonneg_left hBU hcoeff).trans hguard
    rw [exposure,max_eq_left hB.le,max_eq_right (sub_nonneg.mpr hB.le)]
    apply (min_le_right _ _).trans
    apply (div_le_iff₀ (mul_pos hξ hB0)).mpr
    nlinarith

theorem actual_eligibility_moment_limits
    (V : Ω → ℝ) (B : ℕ → Ω → ℝ) (B0 : ℝ → ℝ)
    (hV : Measurable V) (hB : ∀ m, Measurable (B m)) (hB0 : Measurable B0)
    {ξ entryLimit r : ℝ} (hξ : 0 < ξ) (hentryLimit : 0 < entryLimit)
    (b l : ℕ → ℝ) (hbp : ∀ m, 0 < b m) (hlp : ∀ m, 0 < l m)
    (hb : Tendsto b atTop (𝓝 entryLimit)) (hl : Tendsto l atTop (𝓝 entryLimit))
    (hadmissible : ∀ m, ∀ᵐ ω ∂μ, B m ω ≤ V ω)
    (hthreshold : ∀ᵐ ω ∂μ, V ω ≠ entryLimit)
    (hactive : ∀ᵐ ω ∂μ, entryLimit < V ω →
      Tendsto (fun m => B m ω) atTop (𝓝 (B0 (V ω)))) :
    Tendsto (fun m => ∫ ω, eligibility r (exposure ξ (l m) (B m ω)) ∂μ) atTop
      (𝓝 (∫ ω, eligibility r (activeExposure ξ entryLimit B0 (V ω)) ∂μ)) ∧
    Tendsto (fun m => ∫ ω, eligibility r (exposure ξ (l m) (B m ω))*
      (1/2-exposure ξ (b m) (B m ω)) ∂μ) atTop
      (𝓝 (∫ ω, eligibility r (activeExposure ξ entryLimit B0 (V ω))*
        (1/2-activeExposure ξ entryLimit B0 (V ω)) ∂μ)) := by
  constructor
  · apply integral_entry_test_tendsto μ V B B0 hV hB hB0 hξ hentryLimit b l hbp hlp hb hl
      hadmissible hthreshold hactive (fun x => eligibility r x.2) (by
        exact (continuous_eligibility r).comp continuous_snd) 1
    intro x hx y hy
    rw [abs_of_nonneg (eligibility_bounds r y).1]
    exact (eligibility_bounds r y).2
  · apply integral_entry_test_tendsto μ V B B0 hV hB hB0 hξ hentryLimit b l hbp hlp hb hl
      hadmissible hthreshold hactive (fun x => eligibility r x.2*(1/2-x.1)) (by
        exact ((continuous_eligibility r).comp continuous_snd).mul
          (continuous_const.sub continuous_fst)) (1/2)
    intro x hx y hy
    have hh : |1/2-x| ≤ (1/2 : ℝ) := by rw [abs_le]; constructor <;> linarith [hx.1,hx.2]
    rw [abs_mul,abs_of_nonneg (eligibility_bounds r y).1]
    exact (mul_le_mul_of_nonneg_left hh (eligibility_bounds r y).1).trans (by
      have hb := (eligibility_bounds r y).2
      nlinarith)

end FCAppendix.Affine.Uniform06.EntryActiveMoments
