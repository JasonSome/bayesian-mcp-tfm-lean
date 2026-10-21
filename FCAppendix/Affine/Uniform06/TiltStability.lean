import FCAppendix.Affine.Uniform06.SubentryTilt
import FCAppendix.Probability.BoundedLawConvergence

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.TiltStability

open MeasureTheory ProbabilityTheory Set Filter
open FCAppendix.ExponentialTilt SubentryTilt

section Bounded

variable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X)
    (hb : ∀ᵐ ω ∂μ, X ω ∈ Icc (0:ℝ) 1)

include hX hb

theorem mean_bounds : (∫ ω, X ω ∂μ) ∈ Icc (0:ℝ) 1 := by
  have hi : Integrable X μ := Integrable.of_mem_Icc 0 1 hX.aemeasurable hb
  constructor
  · exact integral_nonneg_of_ae (hb.mono fun _ hx => hx.1)
  · simpa using integral_mono_ae hi (integrable_const (1:ℝ)) (hb.mono fun _ hx => hx.2)

theorem variance_bounds_from_zero_mass {z r : ℝ}
    (_hz : 0 ≤ z) (hr : 0 ≤ r)
    (hzero : z ≤ μ.real {ω | X ω=0}) (hmean : r ≤ ∫ ω, X ω ∂μ) :
    z*r^2 ≤ variance X μ ∧ variance X μ ≤ 1 := by
  let a : ℝ := ∫ ω, X ω ∂μ
  have ha := mean_bounds μ hX hb
  have hLp := memLp_of_bounded hb hX.aestronglyMeasurable 2
  have hi : Integrable (fun ω => (X ω-a)^2) μ :=
    (hLp.sub (memLp_const a)).integrable_sq
  have hE : MeasurableSet {ω | X ω=0} := hX (measurableSet_singleton 0)
  have hlow := integral_mono_ae ((integrable_const (a^2)).indicator hE) hi
    (Filter.Eventually.of_forall fun ω => by
      by_cases hω : X ω=0
      · simp [Set.indicator,hω]
      · rw [Set.indicator_of_notMem (show ω ∉ {ω | X ω=0} from hω)]
        exact sq_nonneg (X ω-a))
  rw [integral_indicator_const _ hE,smul_eq_mul,
    ← variance_eq_integral hX.aemeasurable] at hlow
  have hra : r^2 ≤ a^2 := by dsimp [a] at *; nlinarith
  constructor
  · exact ((mul_le_mul_of_nonneg_right hzero (sq_nonneg r)).trans
      (mul_le_mul_of_nonneg_left hra measureReal_nonneg)).trans hlow
  · rw [variance_eq_integral hX.aemeasurable]
    have hh : ∀ᵐ ω ∂μ, (X ω-a)^2 ≤ 1 := by
      filter_upwards [hb] with ω hω
      dsimp [a] at *
      nlinarith [hω.1,hω.2,ha.1,ha.2]
    simpa using integral_mono_ae hi (integrable_const (1:ℝ)) hh

theorem strictAnti_mean (hv : 0 < variance X μ) : StrictAnti (mean μ X) := by
  have hder (θ : ℝ) : HasDerivAt (mean μ X)
      (-variance X (μ.tilted (fun ω => -θ*X ω))) θ := by
    convert! (hasDerivAt_tilted_mean μ hX hb (-θ)).comp θ
      (hasDerivAt_neg θ) using 1
    simp
  have hpos (θ : ℝ) : 0 < variance X (μ.tilted (fun ω => -θ*X ω)) :=
    (mul_pos (Real.exp_pos _) hv).trans_le
      (tilted_variance_bounds μ hX hb (show |(-θ)| ≤ |θ| by simp)).1
  exact strictAnti_of_hasDerivAt_neg hder (fun θ => by have h := hpos θ; linarith)

theorem antitone_mean : Antitone (mean μ X) := by
  intro θ₁ θ₂ hθ
  exact monotone_tilted_mean μ hX hb (neg_le_neg hθ)

theorem exists_uniform_matching_tilt {z r₀ g r : ℝ}
    (hz : 0 < z) (hr₀ : 0 < r₀) (hg : 0 < g)
    (hr : r₀ ≤ r) (hzero : z ≤ μ.real {ω | X ω=0})
    (hgap : r+g ≤ ∫ ω, X ω ∂μ) :
    ∃ θ : ℝ,
      g/Real.exp (4/(r₀*z)) ≤ θ ∧ θ < 2/(r₀*z) ∧
      mean μ X θ=r ∧
      Real.exp (-4/(r₀*z))*z*r₀^2 ≤
        variance X (μ.tilted (fun ω => -θ*X ω)) ∧
      variance X (μ.tilted (fun ω => -θ*X ω)) ≤ Real.exp (4/(r₀*z)) := by
  have hr0 := hr₀.trans_le hr
  have hmean : r < ∫ ω, X ω ∂μ := by linarith
  obtain ⟨θ,hθ,hmatch⟩ := exists_matching_tilt μ hX hb hr0 hz hzero hmean
  let T : ℝ := 2/(r₀*z)
  have hT : 0 < T := by dsimp [T]; positivity
  have hθT : θ < T := hθ.2.trans_le
    (div_le_div_of_nonneg_left (by norm_num) (mul_pos hr₀ hz)
      (mul_le_mul_of_nonneg_right hr hz.le))
  have hbase := variance_bounds_from_zero_mass μ hX hb hz.le hr₀.le hzero
    (hr.trans hmean.le)
  have hvar := tilted_variance_bounds μ hX hb
    (show |(-θ)| ≤ T by rw [abs_neg,abs_of_pos hθ.1]; exact hθT.le)
  have hmeanLoss := (mean_sub_tilted_mean_bounds μ hX hb
    (u := -θ) (a := T) ⟨by linarith,by linarith [hθ.1]⟩).2
  rw [abs_neg,abs_of_pos hθ.1] at hmeanLoss
  change (∫ ω, X ω ∂μ)-mean μ X θ ≤ Real.exp (2*T)*variance X μ*θ at hmeanLoss
  rw [hmatch] at hmeanLoss
  have hprod : Real.exp (2*T)*variance X μ*θ ≤ Real.exp (2*T)*θ :=
    mul_le_mul_of_nonneg_right
      (by simpa using mul_le_mul_of_nonneg_left hbase.2 (Real.exp_pos (2*T)).le) hθ.1.le
  have hlo : g/Real.exp (2*T) ≤ θ :=
    (div_le_iff₀ (Real.exp_pos (2*T))).mpr (by nlinarith)
  have hvl := (mul_le_mul_of_nonneg_left hbase.1 (Real.exp_pos (-2*T)).le).trans hvar.1
  have hvu := hvar.2.trans (mul_le_mul_of_nonneg_left hbase.2 (Real.exp_pos (2*T)).le)
  have htwo : 2*T=4/(r₀*z) := by dsimp [T]; ring
  have hneg : -2*T=-(4/(r₀*z)) := by nlinarith [htwo]
  refine ⟨θ,?_,hθT,hmatch,?_,?_⟩
  · simpa [htwo] using hlo
  · simpa only [hneg,mul_assoc, neg_div] using hvl
  · simpa only [htwo,mul_one] using hvu

end Bounded

theorem matching_tilts_tendsto
    (ν : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (hν : ∀ n, ∀ᵐ x ∂(ν n:Measure ℝ), x ∈ Icc (0:ℝ) 1)
    (hμ : ∀ᵐ x ∂(μ:Measure ℝ), x ∈ Icc (0:ℝ) 1)
    (hweak : Tendsto ν atTop (nhds μ))
    (θ r : ℕ → ℝ) {θ₀ r₀ : ℝ}
    (hr : Tendsto r atTop (nhds r₀))
    (hmatch : ∀ᶠ n in atTop, mean (ν n:Measure ℝ) id (θ n)=r n)
    (hmatch₀ : mean (μ:Measure ℝ) id θ₀=r₀)
    (hv : 0 < variance id (μ:Measure ℝ)) :
    Tendsto θ atTop (nhds θ₀) := by
  have hstrict := strictAnti_mean (μ:Measure ℝ) measurable_id hμ hv
  have hanti (n : ℕ) := antitone_mean (ν n:Measure ℝ) measurable_id (hν n)
  have hfixed (u : ℝ) :
      Tendsto (fun n => mean (ν n:Measure ℝ) id u) atTop
        (nhds (mean (μ:Measure ℝ) id u)) :=
    FCAppendix.BoundedLawConvergence.tendsto_tilted_mean hν hμ hweak (-u)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hlo : r₀ < mean (μ:Measure ℝ) id (θ₀-ε) := by
    rw [← hmatch₀]
    exact hstrict (by linarith)
  have hhi : mean (μ:Measure ℝ) id (θ₀+ε) < r₀ := by
    rw [← hmatch₀]
    exact hstrict (by linarith)
  have hleft := Filter.Tendsto.eventually_lt hr (hfixed (θ₀-ε)) hlo
  have hright := Filter.Tendsto.eventually_lt (hfixed (θ₀+ε)) hr hhi
  filter_upwards [hmatch,hleft,hright] with n hn hl hh
  have hθlo : θ₀-ε < θ n := by
    by_contra h
    have hle := hanti n (le_of_not_gt h)
    rw [hn] at hle
    linarith
  have hθhi : θ n < θ₀+ε := by
    by_contra h
    have hle := hanti n (le_of_not_gt h)
    rw [hn] at hle
    linarith
  rw [Real.dist_eq]
  exact abs_lt.mpr ⟨by linarith,by linarith⟩

end FCAppendix.Affine.Uniform06.TiltStability
