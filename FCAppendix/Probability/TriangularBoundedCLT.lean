import FCAppendix.Probability.BernoulliApproximation
import FCAppendix.Probability.EmpiricalMean

noncomputable section
namespace FCAppendix.Probability
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators ProbabilityTheory

universe u

def iidStandardizedSum {α : Type u} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (N : ℕ) (r : Fin N → α) : ℝ :=
  (∑ i, (f (r i)-∫ a, f a ∂μ)) / Real.sqrt ((N:ℝ)*variance f μ)

theorem iidStandardizedSum_eq {α : Type u} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (N : ℕ) (r : Fin N → α) :
    iidStandardizedSum μ f N r =
      ((∑ i, f (r i))-(N:ℝ)*(∫ a, f a ∂μ)) / Real.sqrt ((N:ℝ)*variance f μ) := by
  simp only [iidStandardizedSum, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem measurable_iidStandardizedSum {α : Type u} [MeasurableSpace α]
    (μ : Measure α) {f : α → ℝ} (hf : Measurable f) (N : ℕ) :
    Measurable (iidStandardizedSum μ f N) := by
  apply Measurable.div_const
  exact Finset.measurable_sum _ (fun i _ => (hf.comp (measurable_pi_apply i)).sub_const _)

theorem cdf_iidStandardizedSum_eq {α : Type u} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ}
    (hf : Measurable f) (N : ℕ) (x : ℝ) :
    cdf ((Measure.pi (fun _ : Fin N => μ)).map (iidStandardizedSum μ f N)) x =
      (Measure.pi (fun _ : Fin N => μ)).real {r | iidStandardizedSum μ f N r ≤ x} := by
  have hm := measurable_iidStandardizedSum μ hf N
  haveI := Measure.isProbabilityMeasure_map
    (μ := Measure.pi (fun _ : Fin N => μ)) hm.aemeasurable
  rw [cdf_eq_real, map_measureReal_apply hm measurableSet_Iic]
  rfl

theorem unitInterval_mean_mem_Icc {α : Type u} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ}
    (hf : Measurable f) (hb : ∀ᵐ a ∂μ, f a ∈ Icc 0 1) :
    (∫ a, f a ∂μ) ∈ Icc 0 1 := by
  have hi := Integrable.of_mem_Icc 0 1 hf.aemeasurable hb
  refine ⟨integral_nonneg_of_ae (hb.mono fun _ h => h.1), ?_⟩
  have hh := integral_mono_ae hi (integrable_const (1:ℝ)) (hb.mono fun _ h => h.2)
  simpa using hh

theorem exists_iid_unitInterval_nonuniform_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
        (f : α → ℝ) (N : ℕ),
        Measurable f → (∀ᵐ a ∂μ, f a ∈ Icc 0 1) →
        0 < Real.sqrt ((N:ℝ)*variance f μ) → ∀ x : ℝ,
          |cdf ((Measure.pi (fun _ : Fin N => μ)).map (iidStandardizedSum μ f N)) x -
            cdf (gaussianReal 0 1) x| ≤
            C / Real.sqrt ((N:ℝ)*variance f μ) / (1+|x|^3) := by
  obtain ⟨C, hC, hBE⟩ := BernoulliApproximation.exists_nonuniform_bound.{0,u}
  refine ⟨C, hC, ?_⟩
  intro α _ μ _ f N hf hb hσ x
  let P := Measure.pi (fun _ : Fin N => μ)
  let Y : Fin N → (Fin N → α) → ℝ := fun i r => f (r i)-∫ a, f a ∂μ
  have hi : Integrable f μ := Integrable.of_mem_Icc 0 1 hf.aemeasurable hb
  have hm := unitInterval_mean_mem_Icc μ hf hb
  have hYm (i : Fin N) : Measurable (Y i) := (hf.comp (measurable_pi_apply i)).sub_const _
  have hYi : iIndepFun Y P :=
    iIndepFun_pi (fun _ : Fin N => (hf.sub_const (∫ a, f a ∂μ)).aemeasurable)
  have hY0 (i : Fin N) : ∫ r, Y i r ∂P = 0 := by
    rw [show Y i = fun r => f (r i)-∫ a, f a ∂μ from rfl]
    rw [integral_sub (integrable_comp_eval hi) (integrable_const _),
      integral_comp_eval hf.aestronglyMeasurable]
    simp
  have hY1 (i : Fin N) : ∀ᵐ r ∂P, |Y i r| ≤ 1 := by
    filter_upwards [(measurePreserving_eval (fun _ : Fin N => μ) i).quasiMeasurePreserving.ae hb]
      with r hr
    exact abs_le.mpr ⟨by dsimp [Y]; linarith [hr.1, hm.2],
      by dsimp [Y]; linarith [hr.2, hm.1]⟩
  have hYv : (∑ i, variance (Y i) P) = (Real.sqrt ((N:ℝ)*variance f μ))^2 := by
    have hv (i : Fin N) : variance (Y i) P = variance f μ := by
      have hraw : Measurable (fun r : Fin N → α => f (r i)) :=
        hf.comp (measurable_pi_apply i)
      rw [show Y i = fun r => f (r i)-∫ a, f a ∂μ from rfl,
        variance_sub_const (μ := P) hraw.aestronglyMeasurable]
      exact (measurePreserving_eval (fun _ : Fin N => μ) i).variance_fun_comp hf.aemeasurable
    simp only [hv, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact (Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg _) (variance_nonneg f μ))).symm
  have hh := hBE P Y 1 (Real.sqrt ((N:ℝ)*variance f μ)) hYm hYi hY0 hY1 hσ hYv x
  have hs : (fun r : Fin N → α => (∑ i, Y i r) / Real.sqrt ((N:ℝ)*variance f μ)) =
      iidStandardizedSum μ f N := rfl
  rw [hs] at hh
  simpa only [P, mul_one_div] using hh

section TriangularRows

variable {α : ℕ → Type u} [∀ m, MeasurableSpace (α m)]
  (μ : (m : ℕ) → Measure (α m)) [∀ m, IsProbabilityMeasure (μ m)]
  (f : (m : ℕ) → α m → ℝ) (N : ℕ → ℕ)

omit [∀ m, IsProbabilityMeasure (μ m)] in

theorem iid_totalStandardDeviation_tendsto_atTop
    (hN : Tendsto N atTop atTop) {v : ℝ} (hv : 0 < v)
    (hvar : Tendsto (fun m => variance (f m) (μ m)) atTop (𝓝 v)) :
    Tendsto (fun m => Real.sqrt ((N m:ℝ)*variance (f m) (μ m))) atTop atTop := by
  have hNR : Tendsto (fun m => (N m:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hN
  exact Real.tendsto_sqrt_atTop.comp (hNR.atTop_mul_pos hv hvar)

theorem iid_unitInterval_cdf_error_tendsto_zero
    (hf : ∀ m, Measurable (f m)) (hb : ∀ m, ∀ᵐ a ∂μ m, f m a ∈ Icc 0 1)
    (hN : Tendsto N atTop atTop) {v : ℝ} (hv : 0 < v)
    (hvar : Tendsto (fun m => variance (f m) (μ m)) atTop (𝓝 v)) (x : ℕ → ℝ) :
    Tendsto (fun m =>
      |cdf ((Measure.pi (fun _ : Fin (N m) => μ m)).map (iidStandardizedSum (μ m) (f m) (N m))) (x m) -
        cdf (gaussianReal 0 1) (x m)|) atTop (𝓝 0) := by
  obtain ⟨C, hC, hBE⟩ := exists_iid_unitInterval_nonuniform_bound.{u}
  have hσ := iid_totalStandardDeviation_tendsto_atTop μ f N hN hv hvar
  have hlim : Tendsto (fun m => C / Real.sqrt ((N m:ℝ)*variance (f m) (μ m))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hσ
  apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) ?_ hlim
  filter_upwards [hσ.eventually_gt_atTop 0] with m hm
  exact (hBE (μ m) (f m) (N m) (hf m) (hb m) hm (x m)).trans
    (div_le_self (div_nonneg hC.le hm.le)
      (by have := pow_nonneg (abs_nonneg (x m)) 3; linarith))

theorem iid_unitInterval_cdf_tendsto_gaussian
    (hf : ∀ m, Measurable (f m)) (hb : ∀ m, ∀ᵐ a ∂μ m, f m a ∈ Icc 0 1)
    (hN : Tendsto N atTop atTop) {v : ℝ} (hv : 0 < v)
    (hvar : Tendsto (fun m => variance (f m) (μ m)) atTop (𝓝 v)) (x : ℝ) :
    Tendsto (fun m =>
      cdf ((Measure.pi (fun _ : Fin (N m) => μ m)).map (iidStandardizedSum (μ m) (f m) (N m))) x)
      atTop (𝓝 (cdf (gaussianReal 0 1) x)) := by
  have hh := iid_unitInterval_cdf_error_tendsto_zero μ f N hf hb hN hv hvar (fun _ => x)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using hh)

theorem iid_unitInterval_cdf_tendsto_gaussian_moving
    (hf : ∀ m, Measurable (f m)) (hb : ∀ m, ∀ᵐ a ∂μ m, f m a ∈ Icc 0 1)
    (hN : Tendsto N atTop atTop) {v : ℝ} (hv : 0 < v)
    (hvar : Tendsto (fun m => variance (f m) (μ m)) atTop (𝓝 v))
    {x : ℕ → ℝ} {z : ℝ} (hx : Tendsto x atTop (𝓝 z)) :
    Tendsto (fun m =>
      cdf ((Measure.pi (fun _ : Fin (N m) => μ m)).map (iidStandardizedSum (μ m) (f m) (N m))) (x m))
      atTop (𝓝 (cdf (gaussianReal 0 1) z)) := by
  have he := iid_unitInterval_cdf_error_tendsto_zero μ f N hf hb hN hv hvar x
  have he' : Tendsto (fun m =>
      cdf ((Measure.pi (fun _ : Fin (N m) => μ m)).map (iidStandardizedSum (μ m) (f m) (N m))) (x m) -
        cdf (gaussianReal 0 1) (x m)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs] using he
  have hc : Continuous (fun a : ℝ => cdf (gaussianReal 0 1) a) := continuous_Φ
  simpa only [Function.comp_def, sub_add_cancel, zero_add] using he'.add (hc.tendsto z |>.comp hx)

theorem iid_unitInterval_probability_le_tendsto_gaussian
    (hf : ∀ m, Measurable (f m)) (hb : ∀ m, ∀ᵐ a ∂μ m, f m a ∈ Icc 0 1)
    (hN : Tendsto N atTop atTop) {v : ℝ} (hv : 0 < v)
    (hvar : Tendsto (fun m => variance (f m) (μ m)) atTop (𝓝 v))
    {x : ℕ → ℝ} {z : ℝ} (hx : Tendsto x atTop (𝓝 z)) :
    Tendsto (fun m => (Measure.pi (fun _ : Fin (N m) => μ m)).real
      {r | iidStandardizedSum (μ m) (f m) (N m) r ≤ x m})
      atTop (𝓝 (cdf (gaussianReal 0 1) z)) := by
  simpa only [cdf_iidStandardizedSum_eq _ (hf _)] using
    iid_unitInterval_cdf_tendsto_gaussian_moving μ f N hf hb hN hv hvar hx

end TriangularRows
end FCAppendix.Probability
