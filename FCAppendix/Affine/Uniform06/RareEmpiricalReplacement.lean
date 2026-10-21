import FCAppendix.Probability.EmpiricalConcentration
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

noncomputable section

namespace FCAppendix.Affine.Uniform06.RareEmpiricalReplacement

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open FCAppendix.Probability

variable {Ω : Type*} [MeasurableSpace Ω]

def empirical (f : Ω → ℝ) (N : ℕ) (ω : Fin N → Ω) : ℝ :=
  (∑ j, f (ω j)) / (N : ℝ)

lemma measurable_empirical {f : Ω → ℝ} (hf : Measurable f) (N : ℕ) :
    Measurable (empirical f N) :=
  (Finset.measurable_sum _ fun j _ => hf.comp (measurable_pi_apply j)).div_const _

lemma integral_unit_bounds (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : Measurable f)
    (hb : ∀ᵐ ω ∂μ, f ω ∈ Icc (0 : ℝ) 1) :
    (∫ ω, f ω ∂μ) ∈ Icc (0 : ℝ) 1 := by
  have hi := Integrable.of_mem_Icc 0 1 hf.aemeasurable hb
  refine ⟨integral_nonneg_of_ae (hb.mono fun _ h => h.1), ?_⟩
  have h := integral_mono_ae hi (integrable_const 1) (hb.mono fun _ h => h.2)
  simpa only [integral_const, probReal_univ, one_smul] using h

lemma empirical_unit_bounds (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hb : ∀ᵐ ω ∂μ, f ω ∈ Icc (0 : ℝ) 1)
    {N : ℕ} (hN : 0 < N) :
    ∀ᵐ ω ∂Measure.pi (fun _ : Fin N => μ), empirical f N ω ∈ Icc (0 : ℝ) 1 := by
  have hall (j : Fin N) :=
    (measurePreserving_eval (fun _ : Fin N => μ) j).quasiMeasurePreserving.ae hb
  filter_upwards [ae_all_iff.mpr hall] with ω hω
  have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun j _ => (hω j).1) hNr.le
  · apply (div_le_iff₀ hNr).mpr
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, one_mul] using
      (Finset.sum_le_sum (s := Finset.univ) (fun j _ => (hω j).2))

theorem weighted_empirical_deviation (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : Measurable f)
    (hb : ∀ᵐ ω ∂μ, f ω ∈ Icc (0 : ℝ) 1)
    {N : ℕ} (hN : 0 < N) (T : (Fin N → Ω) → ℝ) (hT : Measurable T)
    {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (hTb : ∀ᵐ ω ∂Measure.pi (fun _ : Fin N => μ), 0 ≤ T ω ∧ T ω ≤ M) :
    (∫ ω, T ω * |empirical f N ω - ∫ x, f x ∂μ|
      ∂Measure.pi (fun _ : Fin N => μ)) ≤
        ε * (∫ ω, T ω ∂Measure.pi (fun _ : Fin N => μ)) +
          2 * M * Real.exp (-2 * (N : ℝ) * ε ^ 2) := by
  let P := Measure.pi (fun _ : Fin N => μ)
  let m := ∫ x, f x ∂μ
  let E := {ω : Fin N → Ω | ε ≤ |empirical f N ω - m|}
  have hE : MeasurableSet E := measurableSet_le measurable_const
    (((measurable_empirical hf N).sub_const m).abs)
  have hmean := integral_unit_bounds μ hf hb
  have hemb := empirical_unit_bounds μ hb hN
  have herror : ∀ᵐ ω ∂P, |empirical f N ω - m| ≤ 1 := by
    filter_upwards [hemb] with ω hω
    rw [abs_le]
    constructor <;> dsimp [m] at * <;> linarith [hω.1, hω.2, hmean.1, hmean.2]
  have hTi : Integrable T P :=
    Integrable.of_mem_Icc 0 M hT.aemeasurable hTb
  have hFi : Integrable (fun ω => T ω * |empirical f N ω - m|) P := by
    apply Integrable.of_bound
      (hT.mul (((measurable_empirical hf N).sub_const m).abs)).aestronglyMeasurable M
    filter_upwards [hTb, herror] with ω hω herr
    simp only [Pi.mul_apply]
    rw [Real.norm_of_nonneg (mul_nonneg hω.1 (abs_nonneg _))]
    exact (mul_le_mul_of_nonneg_left herr hω.1).trans (by simpa using hω.2)
  have hpoint : ∀ᵐ ω ∂P,
      T ω * |empirical f N ω - m| ≤ ε * T ω + E.indicator (fun _ => M) ω := by
    filter_upwards [hTb, herror] with ω hω herr
    by_cases hbad : ω ∈ E
    · rw [indicator_of_mem hbad]
      have hle : T ω * |empirical f N ω - m| ≤ M :=
        (mul_le_mul_of_nonneg_left herr hω.1).trans (by simpa using hω.2)
      linarith [mul_nonneg hε hω.1]
    · rw [indicator_of_notMem hbad]
      have hsmall : |empirical f N ω - m| < ε := lt_of_not_ge hbad
      simpa only [add_zero, mul_comm ε] using
        mul_le_mul_of_nonneg_left hsmall.le hω.1
  have hI := integral_mono_ae hFi
    ((hTi.const_mul ε).add ((integrable_const M).indicator hE)) hpoint
  simp only [Pi.add_apply] at hI
  rw [integral_add (hTi.const_mul ε) ((integrable_const M).indicator hE),
    integral_const_mul, integral_indicator hE, setIntegral_const] at hI
  have hprob := iid_empiricalMean_two_sided_le μ hf.aemeasurable hb N hN hε
  calc
    _ ≤ ε * (∫ ω, T ω ∂P) + P.real E * M := hI
    _ ≤ ε * (∫ ω, T ω ∂P) + (2 * Real.exp (-2 * (N : ℝ) * ε ^ 2)) * M :=
      add_le_add_right (mul_le_mul_of_nonneg_right hprob hM) _
    _ = _ := by ring

theorem polynomial_exp_tendsto (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (k : ℕ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n => (N n : ℝ) ^ k * Real.exp (-a * (N n : ℝ))) atTop (𝓝 0) := by
  convert!
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) a ha).comp
      (tendsto_natCast_atTop_atTop.comp hN) using 1
  simp only [Real.rpow_natCast, Function.comp_def]

theorem rare_current_mean_replacement
    (μ : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (μ n)]
    (f : ℕ → Ω → ℝ) (hf : ∀ n, Measurable (f n))
    (hb : ∀ n, ∀ᵐ x ∂μ n, f n x ∈ Icc (0 : ℝ) 1)
    (N : ℕ → ℕ) (hNpos : ∀ n, 0 < N n) (hN : Tendsto N atTop atTop)
    (T : (n : ℕ) → (Fin (N n) → Ω) → ℝ) (hT : ∀ n, Measurable (T n))
    (k : ℕ) {B Q : ℝ} (hB : 0 ≤ B) (hQ : 0 < Q)
    (hTb : ∀ n, ∀ᵐ ω ∂Measure.pi (fun _ : Fin (N n) => μ n),
      0 ≤ T n ω ∧ T n ω ≤ B * (N n : ℝ)^k)
    (hrare : ∀ᶠ n in atTop, (N n : ℝ) *
      (∫ ω, T n ω ∂Measure.pi (fun _ : Fin (N n) => μ n)) ≤ Q) :
    Tendsto (fun n => (N n : ℝ) * ∫ ω,
      T n ω * |empirical (f n) (N n) ω - ∫ x, f n x ∂μ n|
        ∂Measure.pi (fun _ : Fin (N n) => μ n)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η : ℝ := ε/(2*Q)
  have hη : 0 < η := by dsimp [η]; positivity
  have htail : Tendsto (fun n => 2*B*((N n : ℝ)^(k+1)*
      Real.exp (-(2*η^2)*(N n : ℝ)))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (polynomial_exp_tendsto N hN (k+1) (by positivity : 0 < 2*η^2)).const_mul (2*B)
  have hsmall := htail.eventually (Iio_mem_nhds (show (0 : ℝ) < ε/2 by positivity))
  filter_upwards [hrare,hsmall] with n hRn htailn
  have hNr : 0 ≤ (N n : ℝ) := Nat.cast_nonneg _
  have hbnd := mul_le_mul_of_nonneg_left
    (weighted_empirical_deviation (μ n) (hf n) (hb n) (hNpos n)
      (T n) (hT n) (show 0 ≤ B*(N n : ℝ)^k by positivity) hη.le (hTb n)) hNr
  have hnonneg : 0 ≤ (N n : ℝ) * ∫ ω,
      T n ω * |empirical (f n) (N n) ω - ∫ x, f n x ∂μ n|
        ∂Measure.pi (fun _ : Fin (N n) => μ n) := by
    exact mul_nonneg hNr (integral_nonneg_of_ae
      ((hTb n).mono fun ω hω => mul_nonneg hω.1 (abs_nonneg _)))
  have he : (N n : ℝ) * (η * (∫ ω, T n ω
      ∂Measure.pi (fun _ : Fin (N n) => μ n)) +
      2*(B*(N n : ℝ)^k)*Real.exp (-2*(N n : ℝ)*η^2)) =
      η*((N n : ℝ)*(∫ ω, T n ω ∂Measure.pi (fun _ : Fin (N n) => μ n))) +
      2*B*((N n : ℝ)^(k+1)*Real.exp (-(2*η^2)*(N n : ℝ))) := by
    rw [show -2*(N n : ℝ)*η^2=-(2*η^2)*(N n : ℝ) by ring]
    ring
  rw [he] at hbnd
  have hηQ : η*Q=ε/2 := by dsimp [η]; field_simp [hQ.ne']
  have hmain := mul_le_mul_of_nonneg_left hRn hη.le
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hnonneg]
  linarith

theorem rare_bad_event_replacement
    (μ : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (μ n)]
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (T : (n : ℕ) → (Fin (N n) → Ω) → ℝ) (hT : ∀ n, Measurable (T n))
    (E : (n : ℕ) → Set (Fin (N n) → Ω)) (hE : ∀ n, MeasurableSet (E n))
    (k : ℕ) {B C a : ℝ} (hB : 0 ≤ B) (_hC : 0 ≤ C) (ha : 0 < a)
    (hTb : ∀ n, ∀ᵐ ω ∂Measure.pi (fun _ : Fin (N n) => μ n),
      0 ≤ T n ω ∧ T n ω ≤ B*(N n : ℝ)^k)
    (hbad : ∀ᶠ n in atTop,
      (Measure.pi (fun _ : Fin (N n) => μ n)).real (E n) ≤
        C*Real.exp (-a*(N n : ℝ))) :
    Tendsto (fun n => (N n : ℝ)*∫ ω, (E n).indicator (T n) ω
      ∂Measure.pi (fun _ : Fin (N n) => μ n)) atTop (𝓝 0) := by
  have hbound : ∀ᶠ n in atTop, (N n : ℝ)*∫ ω, (E n).indicator (T n) ω
      ∂Measure.pi (fun _ : Fin (N n) => μ n) ≤
        B*C*((N n : ℝ)^(k+1)*Real.exp (-a*(N n : ℝ))) := by
    filter_upwards [hbad] with n hn
    let P := Measure.pi (fun _ : Fin (N n) => μ n)
    have hTi : Integrable (T n) P :=
      Integrable.of_mem_Icc 0 _ (hT n).aemeasurable (hTb n)
    have hle : (∫ ω, (E n).indicator (T n) ω ∂P) ≤
        P.real (E n)*(B*(N n : ℝ)^k) := by
      rw [show P.real (E n)*(B*(N n : ℝ)^k) =
        ∫ ω, (E n).indicator (fun _ => B*(N n : ℝ)^k) ω ∂P by
          rw [integral_indicator_const _ (hE n), smul_eq_mul]]
      apply integral_mono_ae (hTi.indicator (hE n))
        ((integrable_const _).indicator (hE n))
      filter_upwards [hTb n] with ω hω
      by_cases he : ω ∈ E n
      · simpa only [indicator_of_mem he] using hω.2
      · simp only [indicator_of_notMem he]; exact le_refl _
    have hh := mul_le_mul_of_nonneg_left (hle.trans
      (mul_le_mul_of_nonneg_right hn (by positivity : 0 ≤ B*(N n : ℝ)^k)))
      (Nat.cast_nonneg (N n) : 0 ≤ (N n : ℝ))
    convert! hh using 1
    ring
  have ht : Tendsto (fun n => B*C*((N n : ℝ)^(k+1)*
      Real.exp (-a*(N n : ℝ)))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (polynomial_exp_tendsto N hN (k+1) ha).const_mul (B*C)
  apply squeeze_zero' _ hbound ht
  exact Eventually.of_forall fun n => mul_nonneg (Nat.cast_nonneg _)
    (integral_nonneg_of_ae ((hTb n).mono fun ω hω => by
      by_cases he : ω ∈ E n
      · convert! hω.1 using 1
        simp only [indicator_of_mem he]
      · simp only [indicator_of_notMem he]; exact le_refl _))

theorem rare_empirical_replacement
    (μ : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (μ n)]
    (f : ℕ → Ω → ℝ) (hf : ∀ n, Measurable (f n))
    (hb : ∀ n, ∀ᵐ ω ∂μ n, f n ω ∈ Icc (0 : ℝ) 1)
    (N : ℕ → ℕ) (hNpos : ∀ n, 0 < N n) (hN : Tendsto N atTop atTop)
    (T : (n : ℕ) → (Fin (N n) → Ω) → ℝ) (hT : ∀ n, Measurable (T n))
    (k : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hTb : ∀ n, ∀ᵐ ω ∂Measure.pi (fun _ : Fin (N n) => μ n),
      0 ≤ T n ω ∧ T n ω ≤ B * (N n : ℝ) ^ k)
    {L ν : ℝ}
    (hrare : Tendsto (fun n => (N n : ℝ) *
      ∫ ω, T n ω ∂Measure.pi (fun _ : Fin (N n) => μ n)) atTop (𝓝 L))
    (hmean : Tendsto (fun n => ∫ ω, f n ω ∂μ n) atTop (𝓝 ν)) :
    Tendsto (fun n => (N n : ℝ) * ∫ ω,
      T n ω * |empirical (f n) (N n) ω - ν|
        ∂Measure.pi (fun _ : Fin (N n) => μ n)) atTop (𝓝 0) := by
  let P := fun n => Measure.pi (fun _ : Fin (N n) => μ n)
  let e := fun n => ∫ ω, f n ω ∂μ n
  have hν : ν ∈ Icc (0 : ℝ) 1 := by
    exact isClosed_Icc.mem_of_tendsto hmean
      (Eventually.of_forall fun n => integral_unit_bounds (μ n) (hf n) (hb n))
  have hTi (n : ℕ) : Integrable (T n) (P n) :=
    Integrable.of_mem_Icc 0 _ (hT n).aemeasurable (hTb n)
  have hFi (n : ℕ) (a : ℝ) : Integrable
      (fun ω => T n ω * |empirical (f n) (N n) ω - a|) (P n) := by
    apply Integrable.of_bound
      ((hT n).mul (((measurable_empirical (hf n) (N n)).sub_const a).abs)).aestronglyMeasurable
      (B * (N n : ℝ) ^ k * (1 + |a|))
    filter_upwards [hTb n, empirical_unit_bounds (μ n) (hb n) (hNpos n)] with ω hω hem
    simp only [Pi.mul_apply]
    rw [Real.norm_of_nonneg (mul_nonneg hω.1 (abs_nonneg _))]
    have ha : |empirical (f n) (N n) ω - a| ≤ 1 + |a| := by
      calc
        _ ≤ |empirical (f n) (N n) ω|+|a| := abs_sub _ _
        _ ≤ 1+|a| := by rw [abs_of_nonneg hem.1]; linarith [hem.2]
    exact mul_le_mul hω.2 ha (abs_nonneg _) (by positivity)
  have hsplit (n : ℕ) :
      (∫ ω, T n ω * |empirical (f n) (N n) ω - ν| ∂P n) ≤
        (∫ ω, T n ω * |empirical (f n) (N n) ω - e n| ∂P n) +
          |e n - ν| * ∫ ω, T n ω ∂P n := by
    rw [← integral_const_mul, ← integral_add (hFi n (e n)) ((hTi n).const_mul _)]
    apply integral_mono_ae (hFi n ν) ((hFi n (e n)).add ((hTi n).const_mul _))
    filter_upwards [hTb n] with ω hω
    have h := mul_le_mul_of_nonneg_left
      (abs_sub_le (empirical (f n) (N n) ω) (e n) ν) hω.1
    convert! h using 1
    simp only [Pi.add_apply]
    ring
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let Q : ℝ := |L| + 1
  have hQ : 0 < Q := by dsimp [Q]; positivity
  let τ : ℝ := ε / (4 * Q)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hsmallRare := hrare.eventually (Iio_mem_nhds
    (show L < Q by dsimp [Q]; linarith [le_abs_self L]))
  have hsmallMean := ((hmean.sub_const ν).abs).eventually
    (Iio_mem_nhds (show |ν - ν| < τ by simpa using hτ))
  have hbad : Tendsto (fun n =>
      2 * B * ((N n : ℝ) ^ (k + 1) * Real.exp (-(2 * τ ^ 2) * (N n : ℝ))))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (polynomial_exp_tendsto N hN (k + 1) (by positivity : 0 < 2 * τ ^ 2)).const_mul (2 * B)
  have hsmallBad := hbad.eventually (Iio_mem_nhds (show (0 : ℝ) < ε / 2 by positivity))
  filter_upwards [hsmallRare, hsmallMean, hsmallBad] with n hRn hmn hbn
  have hNr : 0 < (N n : ℝ) := Nat.cast_pos.mpr (hNpos n)
  have hR0 : 0 ≤ (N n : ℝ) * ∫ ω, T n ω ∂P n :=
    mul_nonneg hNr.le (integral_nonneg_of_ae ((hTb n).mono fun _ h => h.1))
  have hfinite := weighted_empirical_deviation (μ n) (hf n) (hb n) (hNpos n)
    (T n) (hT n) (show 0 ≤ B * (N n : ℝ) ^ k by positivity) hτ.le (hTb n)
  have hbound := mul_le_mul_of_nonneg_left ((hsplit n).trans
    (add_le_add_left hfinite _)) hNr.le
  have hmain : (N n : ℝ) * ∫ ω,
      T n ω * |empirical (f n) (N n) ω - ν| ∂P n ≤
      τ * ((N n : ℝ) * ∫ ω, T n ω ∂P n) +
        2 * B * ((N n : ℝ) ^ (k + 1) * Real.exp (-(2 * τ ^ 2) * (N n : ℝ))) +
          |e n - ν| * ((N n : ℝ) * ∫ ω, T n ω ∂P n) := by
    convert! hbound using 1
    dsimp [e, P] at *
    rw [show -2 * (N n : ℝ) * τ ^ 2 = -(2 * τ ^ 2) * (N n : ℝ) by ring]
    ring
  have hterm1 : τ * ((N n : ℝ) * ∫ ω, T n ω ∂P n) ≤ τ * Q :=
    mul_le_mul_of_nonneg_left hRn.le hτ.le
  have hterm2 : |e n - ν| * ((N n : ℝ) * ∫ ω, T n ω ∂P n) ≤ τ * Q :=
    (mul_le_mul_of_nonneg_right hmn.le hR0).trans hterm1
  have hnonneg : 0 ≤ (N n : ℝ) * ∫ ω,
      T n ω * |empirical (f n) (N n) ω - ν| ∂P n := by
    apply mul_nonneg hNr.le
    exact integral_nonneg_of_ae ((hTb n).mono fun ω hω => mul_nonneg hω.1 (abs_nonneg _))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  have hτQ : 2 * (τ * Q) = ε / 2 := by dsimp [τ]; field_simp [hQ.ne']; norm_num
  change _ < ε
  linarith

lemma guarded_inverse_error {c ν x : ℝ} (hc : 0 < c) (hcν : c ≤ ν) :
    |(max c x)⁻¹ - ν⁻¹| ≤ |x - ν| / (c * ν) := by
  have hν : 0 < ν := hc.trans_le hcν
  have hmax : 0 < max c x := hc.trans_le (le_max_left _ _)
  have hclamp : |max c x - ν| ≤ |x - ν| := by
    simpa only [max_comm c x, max_eq_left hcν] using abs_max_sub_max_le_abs x ν c
  have hid : (max c x)⁻¹ - ν⁻¹ = (ν - max c x) / (max c x * ν) := by
    field_simp [hmax.ne', hν.ne']
  rw [hid, abs_div, abs_sub_comm, abs_of_pos (mul_pos hmax hν)]
  exact (div_le_div_of_nonneg_right hclamp (mul_pos hmax hν).le).trans
    (div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos hc hν)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hν.le))

end FCAppendix.Affine.Uniform06.RareEmpiricalReplacement
