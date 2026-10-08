import Mathlib.Probability.Moments.Tilted
import Mathlib.Probability.Moments.Variance

namespace FCAppendix.ExponentialTilt

open MeasureTheory ProbabilityTheory Filter Topology Set Real

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {u : ℝ}

theorem integrable_reverse_weight (ht : Integrable (fun ω => exp (u * X ω)) μ) :
    Integrable (fun ω => exp (cgf X μ u - u * X ω)) (μ.tilted (fun ω => u * X ω)) := by
  rw [integrable_tilted_iff ht]
  have he : (fun ω => exp (u * X ω) • exp (cgf X μ u - u * X ω)) =
      (fun _ => exp (cgf X μ u)) := by
    funext ω
    rw [smul_eq_mul, ← exp_add]
    congr 1
    ring
  rw [he]
  exact integrable_const _

omit [IsProbabilityMeasure μ] in

theorem measureReal_eq_reverse_tilt (ht : Integrable (fun ω => exp (u * X ω)) μ)
    {s : Set Ω} (hs : MeasurableSet s) :
    μ.real s = ∫ ω in s, exp (cgf X μ u - u * X ω) ∂(μ.tilted (fun ω => u * X ω)) := by
  rw [setIntegral_tilted_mul_eq_cgf' _ hs ht]
  have he : (fun ω => exp (u * X ω - cgf X μ u) • exp (cgf X μ u - u * X ω)) =
      (fun _ => (1 : ℝ)) := by
    funext ω
    rw [smul_eq_mul, ← exp_add]
    convert exp_zero using 2
    ring
  rw [he, setIntegral_const, smul_eq_mul, mul_one]

theorem lower_tail_ge_tilted_band (hX : Measurable X)
    (ht : Integrable (fun ω => exp (u * X ω)) μ) (hu : u ≤ 0)
    {z δ r : ℝ} (hr : z + δ ≤ r) :
    exp (cgf X μ u - u * (z - δ)) *
        (μ.tilted (fun ω => u * X ω)).real {ω | |X ω - z| < δ} ≤ μ.real {ω | X ω ≤ r} := by
  let ν := μ.tilted (fun ω => u * X ω)
  haveI : IsProbabilityMeasure ν := isProbabilityMeasure_tilted ht
  let s := {ω | |X ω - z| < δ}
  have hs : MeasurableSet s := measurableSet_lt (hX.sub_const z).abs measurable_const
  have hweight := (integrable_reverse_weight μ ht).integrableOn (s := s)
  have hbound : ∀ᵐ ω ∂ν.restrict s,
      exp (cgf X μ u - u * (z - δ)) ≤ exp (cgf X μ u - u * X ω) := by
    filter_upwards [self_mem_ae_restrict hs] with ω hω
    apply exp_le_exp.mpr
    have hx := (abs_lt.mp (show |X ω - z| < δ from hω)).1
    have hm := mul_le_mul_of_nonpos_left (show z - δ ≤ X ω by linarith) hu
    linarith
  have hi := integral_mono_ae (integrable_const _) hweight hbound
  rw [setIntegral_const, smul_eq_mul, ← measureReal_eq_reverse_tilt μ ht hs] at hi
  have hmono : μ.real s ≤ μ.real {ω | X ω ≤ r} := by
    apply measureReal_mono (h₂ := measure_ne_top _ _)
    intro ω hω
    have hx := (abs_lt.mp (show |X ω - z| < δ from hω)).2
    change X ω ≤ r
    linarith
  exact (by simpa only [mul_comm] using hi :
    exp (cgf X μ u - u * (z - δ)) * ν.real s ≤ μ.real s).trans hmono

theorem lower_tail_ge_tilted_chebyshev (hX : Measurable X)
    (ht : Integrable (fun ω => exp (u * X ω)) μ) (hu : u ≤ 0)
    (hLp : MemLp X 2 (μ.tilted (fun ω => u * X ω))) {δ r : ℝ} (hδ : 0 < δ)
    (hr : (∫ ω, X ω ∂(μ.tilted (fun ω => u * X ω))) + δ ≤ r) :
    exp (cgf X μ u - u * ((∫ ω, X ω ∂(μ.tilted (fun ω => u * X ω))) - δ)) *
      (1 - variance X (μ.tilted (fun ω => u * X ω)) / δ ^ 2) ≤ μ.real {ω | X ω ≤ r} := by
  let ν := μ.tilted (fun ω => u * X ω)
  haveI : IsProbabilityMeasure ν := isProbabilityMeasure_tilted ht
  let z := ∫ ω, X ω ∂ν
  let s := {ω | |X ω - z| < δ}
  have hs : MeasurableSet s := measurableSet_lt (hX.sub_const z).abs measurable_const
  have hc := meas_ge_le_variance_div_sq hLp hδ
  have hnonneg : 0 ≤ variance X ν / δ ^ 2 := div_nonneg (variance_nonneg X ν) (sq_nonneg _)
  have hreal := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hc
  rw [ENNReal.toReal_ofReal hnonneg] at hreal
  have hset : {ω | δ ≤ |X ω - z|} = sᶜ := by ext ω; simp [s]
  change ν.real {ω | δ ≤ |X ω - z|} ≤ variance X ν / δ ^ 2 at hreal
  rw [hset, probReal_compl_eq_one_sub hs] at hreal
  have hband : 1 - variance X ν / δ ^ 2 ≤ ν.real s := by linarith
  have hmul := mul_le_mul_of_nonneg_left hband (exp_pos (cgf X μ u - u * (z - δ))).le
  exact hmul.trans (lower_tail_ge_tilted_band μ hX ht hu hr)

theorem integrable_exp_mul_of_bounded (hX : AEMeasurable X μ) {B : ℝ}
    (hB : ∀ᵐ ω ∂μ, X ω ∈ Icc 0 B) (u : ℝ) :
    Integrable (fun ω => exp (u * X ω)) μ := by
  apply Integrable.mono' (integrable_const (exp (|u| * B)))
    (hX.const_mul u).exp.aestronglyMeasurable
  filter_upwards [hB] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  exact exp_le_exp.mpr ((mul_le_mul_of_nonneg_right (le_abs_self u) hω.1).trans
    (mul_le_mul_of_nonneg_left hω.2 (abs_nonneg u)))

theorem integrableExpSet_eq_univ_of_bounded (hX : AEMeasurable X μ) {B : ℝ}
    (hB : ∀ᵐ ω ∂μ, X ω ∈ Icc 0 B) : integrableExpSet X μ = univ := by
  ext u
  simp only [mem_univ, iff_true]
  exact integrable_exp_mul_of_bounded μ hX hB u

def rowSum {m : ℕ} (Y : Fin m → Ω → ℝ) (ω : Ω) : ℝ := ∑ i, Y i ω

omit [MeasurableSpace Ω] in
theorem rowSum_eq_sum {m : ℕ} (Y : Fin m → Ω → ℝ) : rowSum Y = ∑ i, Y i := by
  funext ω
  simp [rowSum]

theorem measurable_rowSum {m : ℕ} {Y : Fin m → Ω → ℝ} (hY : ∀ i, Measurable (Y i)) :
    Measurable (rowSum Y) := by
  unfold rowSum
  fun_prop

omit [IsProbabilityMeasure μ] in
theorem rowSum_bounded {m : ℕ} {Y : Fin m → Ω → ℝ}
    (hY : ∀ i, ∀ᵐ ω ∂μ, Y i ω ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ ω ∂μ, rowSum Y ω ∈ Icc (0 : ℝ) m := by
  filter_upwards [ae_all_iff.mpr hY] with ω hω
  constructor
  · exact Finset.sum_nonneg (fun i _ => (hω i).1)
  · calc
      rowSum Y ω ≤ ∑ _i : Fin m, (1 : ℝ) := Finset.sum_le_sum (fun i _ => (hω i).2)
      _ = (m : ℝ) := by simp

theorem cgf_rowSum {m : ℕ} {Y : Fin m → Ω → ℝ} (hY : ∀ i, Measurable (Y i))
    (hbound : ∀ i, ∀ᵐ ω ∂μ, Y i ω ∈ Icc (0 : ℝ) 1) (hind : iIndepFun Y μ)
    (i : Fin m) (hident : ∀ j, IdentDistrib (Y j) (Y i) μ μ) (u : ℝ) :
    cgf (rowSum Y) μ u = (m : ℝ) * cgf (Y i) μ u := by
  rw [rowSum_eq_sum]
  have hh := hind.cgf_sum hY (s := Finset.univ)
    (fun j _ => integrable_exp_mul_of_bounded μ (hY j).aemeasurable (hbound j) u)
  rw [hh]
  have he : ∀ j, cgf (Y j) μ u = cgf (Y i) μ u := by
    intro j
    rw [cgf, cgf, mgf_congr_of_identDistrib (Y j) (Y i) (hident j) u]
  simp_rw [he]
  simp

theorem tilted_row_mean {m : ℕ} {Y : Fin m → Ω → ℝ} (hY : ∀ i, Measurable (Y i))
    (hbound : ∀ i, ∀ᵐ ω ∂μ, Y i ω ∈ Icc (0 : ℝ) 1) (hind : iIndepFun Y μ)
    (i : Fin m) (hident : ∀ j, IdentDistrib (Y j) (Y i) μ μ) (u : ℝ) :
    (∫ ω, rowSum Y ω ∂(μ.tilted (fun ω => u * rowSum Y ω))) =
      (m : ℝ) * ∫ ω, Y i ω ∂(μ.tilted (fun ω => u * Y i ω)) := by
  have hS : u ∈ interior (integrableExpSet (rowSum Y) μ) := by
    rw [integrableExpSet_eq_univ_of_bounded μ (measurable_rowSum hY).aemeasurable (rowSum_bounded μ hbound)]
    simp
  have hYi : u ∈ interior (integrableExpSet (Y i) μ) := by
    rw [integrableExpSet_eq_univ_of_bounded μ (hY i).aemeasurable (hbound i)]
    simp
  rw [integral_tilted_mul_self hS, integral_tilted_mul_self hYi]
  have he : cgf (rowSum Y) μ = fun u => (m : ℝ) * cgf (Y i) μ u :=
    funext (cgf_rowSum μ hY hbound hind i hident)
  rw [he, deriv_const_mul_field]

theorem tilted_row_variance {m : ℕ} {Y : Fin m → Ω → ℝ} (hY : ∀ i, Measurable (Y i))
    (hbound : ∀ i, ∀ᵐ ω ∂μ, Y i ω ∈ Icc (0 : ℝ) 1) (hind : iIndepFun Y μ)
    (i : Fin m) (hident : ∀ j, IdentDistrib (Y j) (Y i) μ μ) (u : ℝ) :
    variance (rowSum Y) (μ.tilted (fun ω => u * rowSum Y ω)) =
      (m : ℝ) * variance (Y i) (μ.tilted (fun ω => u * Y i ω)) := by
  have hS : u ∈ interior (integrableExpSet (rowSum Y) μ) := by
    rw [integrableExpSet_eq_univ_of_bounded μ (measurable_rowSum hY).aemeasurable (rowSum_bounded μ hbound)]
    simp
  have hYi : u ∈ interior (integrableExpSet (Y i) μ) := by
    rw [integrableExpSet_eq_univ_of_bounded μ (hY i).aemeasurable (hbound i)]
    simp
  rw [variance_tilted_mul hS, variance_tilted_mul hYi]
  have he : cgf (rowSum Y) μ = fun u => (m : ℝ) * cgf (Y i) μ u :=
    funext (cgf_rowSum μ hY hbound hind i hident)
  rw [he, iteratedDeriv_const_mul_field]

theorem tilted_row_variance_le {m : ℕ} {Y : Fin m → Ω → ℝ} (hY : ∀ i, Measurable (Y i))
    (hbound : ∀ i, ∀ᵐ ω ∂μ, Y i ω ∈ Icc (0 : ℝ) 1) (hind : iIndepFun Y μ)
    (i : Fin m) (hident : ∀ j, IdentDistrib (Y j) (Y i) μ μ) (u : ℝ) :
    variance (rowSum Y) (μ.tilted (fun ω => u * rowSum Y ω)) ≤ (m : ℝ) / 4 := by
  rw [tilted_row_variance μ hY hbound hind i hident u]
  let ν := μ.tilted (fun ω => u * Y i ω)
  haveI : IsProbabilityMeasure ν := isProbabilityMeasure_tilted
    (integrable_exp_mul_of_bounded μ (hY i).aemeasurable (hbound i) u)
  have hac := tilted_absolutelyContinuous μ (fun ω => u * Y i ω)
  have hvar := variance_le_sq_of_bounded (hac (hbound i)) ((hY i).aemeasurable.mono_ac hac)
  norm_num at hvar
  have hh := mul_le_mul_of_nonneg_left hvar (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  simpa only [mul_one_div] using hh

theorem iid_row_lower_tail {m : ℕ} {Y : Fin m → Ω → ℝ} (hY : ∀ i, Measurable (Y i))
    (hbound : ∀ i, ∀ᵐ ω ∂μ, Y i ω ∈ Icc (0 : ℝ) 1) (hind : iIndepFun Y μ)
    (i : Fin m) (hident : ∀ j, IdentDistrib (Y j) (Y i) μ μ) {u ε r : ℝ}
    (hu : u ≤ 0) (hε : 0 < ε)
    (hr : (m : ℝ) * ((∫ ω, Y i ω ∂(μ.tilted (fun ω => u * Y i ω))) + ε) ≤ r) :
    exp ((m : ℝ) * (cgf (Y i) μ u -
        u * ((∫ ω, Y i ω ∂(μ.tilted (fun ω => u * Y i ω))) - ε))) *
      (1 - 1 / (4 * (m : ℝ) * ε ^ 2)) ≤ μ.real {ω | rowSum Y ω ≤ r} := by
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hSm := measurable_rowSum hY
  have hSb := rowSum_bounded μ hbound
  have ht := integrable_exp_mul_of_bounded μ hSm.aemeasurable hSb u
  have hS : u ∈ interior (integrableExpSet (rowSum Y) μ) := by
    rw [integrableExpSet_eq_univ_of_bounded μ hSm.aemeasurable hSb]
    simp
  have hLp : MemLp (rowSum Y) 2 (μ.tilted (fun ω => u * rowSum Y ω)) := memLp_tilted_mul hS 2
  have hmean := tilted_row_mean μ hY hbound hind i hident u
  have hr' : (∫ ω, rowSum Y ω ∂(μ.tilted (fun ω => u * rowSum Y ω))) + (m : ℝ) * ε ≤ r := by
    rw [hmean]
    nlinarith
  have hh := lower_tail_ge_tilted_chebyshev μ hSm ht hu hLp (mul_pos hmR hε) hr'
  have hvar := tilted_row_variance_le μ hY hbound hind i hident u
  have hvar' := div_le_div_of_nonneg_right hvar (sq_nonneg ((m : ℝ) * ε))
  have he : ((m : ℝ) / 4) / ((m : ℝ) * ε) ^ 2 = 1 / (4 * (m : ℝ) * ε ^ 2) := by field_simp
  rw [he] at hvar'
  have hfactor : 1 - 1 / (4 * (m : ℝ) * ε ^ 2) ≤
      1 - variance (rowSum Y) (μ.tilted (fun ω => u * rowSum Y ω)) / ((m : ℝ) * ε) ^ 2 := by linarith
  rw [cgf_rowSum μ hY hbound hind i hident u, hmean] at hh
  have hexp : (m : ℝ) * cgf (Y i) μ u -
      u * ((m : ℝ) * (∫ ω, Y i ω ∂(μ.tilted (fun ω => u * Y i ω))) - (m : ℝ) * ε) =
      (m : ℝ) * (cgf (Y i) μ u - u * ((∫ ω, Y i ω ∂(μ.tilted (fun ω => u * Y i ω))) - ε)) := by ring
  rw [hexp] at hh
  exact (mul_le_mul_of_nonneg_left hfactor (exp_pos _).le).trans hh

theorem iid_row_log_lower_bound {m : ℕ} {Y : Fin m → Ω → ℝ} (hY : ∀ i, Measurable (Y i))
    (hbound : ∀ i, ∀ᵐ ω ∂μ, Y i ω ∈ Icc (0 : ℝ) 1) (hind : iIndepFun Y μ)
    (i : Fin m) (hident : ∀ j, IdentDistrib (Y j) (Y i) μ μ) {u ε r : ℝ}
    (hu : u ≤ 0) (hε : 0 < ε) (hsize : 2 ≤ 4 * (m : ℝ) * ε ^ 2)
    (hr : (m : ℝ) * ((∫ ω, Y i ω ∂(μ.tilted (fun ω => u * Y i ω))) + ε) ≤ r) :
    0 < μ.real {ω | rowSum Y ω ≤ r} ∧
      cgf (Y i) μ u - u * ((∫ ω, Y i ω ∂(μ.tilted (fun ω => u * Y i ω))) - ε) -
        log 2 / (m : ℝ) ≤ log (μ.real {ω | rowSum Y ω ≤ r}) / (m : ℝ) := by
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hden : 0 < 4 * (m : ℝ) * ε ^ 2 := by positivity
  have hfactor : (1 / 2 : ℝ) ≤ 1 - 1 / (4 * (m : ℝ) * ε ^ 2) := by
    have hh : 1 / (4 * (m : ℝ) * ε ^ 2) ≤ (1 / 2 : ℝ) :=
      (div_le_iff₀ hden).mpr (by linarith)
    linarith
  let a : ℝ := cgf (Y i) μ u - u * ((∫ ω, Y i ω ∂(μ.tilted (fun ω => u * Y i ω))) - ε)
  have hprob := (mul_le_mul_of_nonneg_left hfactor (exp_pos ((m : ℝ) * a)).le).trans
    (iid_row_lower_tail μ hY hbound hind i hident hu hε hr)
  have hhalf : exp ((m : ℝ) * a) / 2 ≤ μ.real {ω | rowSum Y ω ≤ r} := by
    simpa only [mul_one_div] using hprob
  have hhalfpos : 0 < exp ((m : ℝ) * a) / 2 := by positivity
  have hlog := log_le_log hhalfpos hhalf
  rw [log_div (exp_ne_zero _) (by norm_num), log_exp] at hlog
  refine ⟨hhalfpos.trans_le hhalf, ?_⟩
  change a - log 2 / (m : ℝ) ≤ _
  rw [le_div_iff₀ hmR]
  have he : (a - log 2 / (m : ℝ)) * m = (m : ℝ) * a - log 2 := by field_simp
  rw [he]
  exact hlog

theorem iid_row_log_upper_bound {m : ℕ} {Y : Fin m → Ω → ℝ} (hY : ∀ i, Measurable (Y i))
    (hbound : ∀ i, ∀ᵐ ω ∂μ, Y i ω ∈ Icc (0 : ℝ) 1) (hind : iIndepFun Y μ)
    (i : Fin m) (hident : ∀ j, IdentDistrib (Y j) (Y i) μ μ) {u r : ℝ}
    (hu : u ≤ 0) (hpos : 0 < μ.real {ω | rowSum Y ω ≤ r}) :
    log (μ.real {ω | rowSum Y ω ≤ r}) / (m : ℝ) ≤ cgf (Y i) μ u - u * (r / m) := by
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have ht := integrable_exp_mul_of_bounded μ (measurable_rowSum hY).aemeasurable (rowSum_bounded μ hbound) u
  have hh := measure_le_le_exp_cgf (μ := μ) (X := rowSum Y) r hu ht
  have hlog := log_le_log hpos hh
  rw [log_exp, cgf_rowSum μ hY hbound hind i hident u] at hlog
  rw [div_le_iff₀ hmR]
  have he : (cgf (Y i) μ u - u * (r / (m : ℝ))) * m = -(u * r) + (m : ℝ) * cgf (Y i) μ u := by
    field_simp
    ring
  rw [he]
  simpa only [neg_mul] using hlog

end FCAppendix.ExponentialTilt
