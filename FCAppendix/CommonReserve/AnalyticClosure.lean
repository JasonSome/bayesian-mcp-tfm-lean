import FCAppendix.CommonReserve.PriceIdentification
import FCAppendix.Finite.NearPPIUtility

noncomputable section
namespace FCAppendix.CommonReserve.ReserveAnalysis

open MeasureTheory Filter Set Topology

variable {n : ℕ}

theorem coverage_limit (F : Measure ℝ) [IsProbabilityMeasure F]
    (μ : ℕ → ℝ → CountLaw n) (U e δ : ℕ → ℝ → ℝ) (c p : ℝ)
    (hp : 0 ≤ p) (hc : F {c} = 0)
    (hS : ∀ k, AEStronglyMeasurable (fun v => (μ k v).success) F)
    (hU : ∀ k, ∀ᵐ v ∂F, 0 ≤ U k v)
    (he : ∀ k, 0 ≤ᵐ[F] e k) (hd : ∀ k, 0 ≤ᵐ[F] δ k)
    (hu : ∀ k, ∀ᵐ v ∂F,
      U k v ≤ (v - c) * (μ k v).success - p * (μ k v).duplicates + e k v)
    (hl : ∀ k, ∀ᵐ v ∂F, max (v - c) 0 - δ k v ≤ U k v)
    (hIe : ∀ k, Integrable (e k) F)
    (he0 : Tendsto (fun k => ∫ v, e k v ∂F) atTop (𝓝 0))
    (hd0 : ∀ᵐ v ∂F, Tendsto (fun k => δ k v) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ v, (μ k v).success ∂F) atTop (𝓝 (F.real (Ioi c))) := by
  have heM := NearPPI.mean_error_tendstoInMeasure F e he hIe he0
  have hcAE : ∀ᵐ v ∂F, v - c ≠ 0 := by
    have h : ∀ᵐ v ∂F, v ∉ ({c} : Set ℝ) := by
      rw [ae_iff]
      simpa using hc
    simpa only [mem_singleton_iff, sub_ne_zero] using h
  have hb : ∀ᵐ v ∂F, ∀ k,
      0 ≤ U k v ∧ 0 ≤ e k v ∧ 0 ≤ δ k v ∧
      U k v ≤ (v - c) * (μ k v).success - p * (μ k v).duplicates + e k v ∧
      max (v - c) 0 - δ k v ≤ U k v := by
    apply ae_all_iff.mpr
    intro k
    filter_upwards [hU k, he k, hd k, hu k, hl k] with v h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, hms, heAE⟩ := (heM.comp hns).exists_seq_tendsto_ae
  have hs : ∀ᵐ v ∂F, Tendsto (fun k => (μ (ns (ms k)) v).success)
      atTop (𝓝 (NearPPI.cutoffSuccess (v - c))) := by
    filter_upwards [hcAE, hb, hd0, heAE] with v hv hb' hd' he'
    exact NearPPI.tendsto_success hv hp (fun k => (hb' _).1)
      (fun k => (μ (ns (ms k)) v).success_nonneg)
      (fun k => (μ (ns (ms k)) v).success_le_one)
      (fun k => (μ (ns (ms k)) v).duplicates_nonneg)
      (fun k => (hb' _).2.1) (fun k => (hb' _).2.2.1)
      (fun k => (hb' _).2.2.2.1) (fun k => (hb' _).2.2.2.2)
      he' (hd'.comp (hns.comp hms.tendsto_atTop))
  have h := tendsto_integral_of_dominated_convergence (μ := F) (fun _ => (1 : ℝ))
    (fun k => hS (ns (ms k))) (integrable_const (1 : ℝ))
    (fun k => ae_of_all _ fun v => by
      rw [Real.norm_eq_abs, abs_of_nonneg (μ (ns (ms k)) v).success_nonneg]
      exact (μ (ns (ms k)) v).success_le_one) hs
  exact ⟨ms, by simpa only [NearPPI.integral_cutoffSuccess, Measure.real] using h⟩

theorem utility_limit (F : Measure ℝ) [IsProbabilityMeasure F]
    (μ : ℕ → ℝ → CountLaw n) (U e δ : ℕ → ℝ → ℝ) (c p : ℝ)
    (hp : 0 ≤ p) (hU : ∀ k v, 0 ≤ U k v)
    (hmono : ∀ k, Monotone (U k))
    (hLip : ∀ k v w, |U k v - U k w| ≤ |v - w|)
    (he : ∀ k, 0 ≤ᵐ[F] e k) (hIe : ∀ k, Integrable (e k) F)
    (hu : ∀ k, ∀ᵐ v ∂F,
      U k v ≤ (v - c) * (μ k v).success - p * (μ k v).duplicates + e k v)
    (hl : ∀ k v, max (v - c) 0 - δ k v ≤ U k v)
    (he0 : Tendsto (fun k => ∫ v, e k v ∂F) atTop (𝓝 0))
    (hd0 : ∀ v, Tendsto (fun k => δ k v) atTop (𝓝 0))
    (hleft : ∀ w < c, 0 < F.real (Ioo w c)) :
    ∀ v, Tendsto (fun k => U k v) atTop (𝓝 (max (v - c) 0)) := by
  have hbelow (w : ℝ) (hw : w < c) : Tendsto (fun k => U k w) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => hU k w)
      (g := fun k => (∫ v, e k v ∂F) / F.real (Ioo w c))
    · intro k
      apply (le_div_iff₀ (hleft w hw)).mpr
      have hh := Bayes.monotone_utility_le_mean_error F (U k) (e k) c w
        (hmono k) (hIe k) (he k) (by
          filter_upwards [hu k] with v hv hvc
          have hnet := mul_nonpos_of_nonpos_of_nonneg
            (sub_nonpos.mpr hvc.le) (μ k v).success_nonneg
          have hdup := mul_nonneg hp (μ k v).duplicates_nonneg
          linarith)
      simpa only [mul_comm] using hh
    · simpa only [zero_div] using he0.div_const (F.real (Ioo w c))
  apply NearPPI.utility_limit_across_support_gaps hmono hLip hl hd0
  intro ε hε
  exact ⟨c - ε / 2, by linarith, by linarith, hbelow _ (by linarith)⟩

structure Estimates (F : Measure ℝ) (g r ρ : ℝ)
    (t κ : ℕ → ℝ) (μ : ℕ → ℝ → CountLaw n)
    (U e δ : ℕ → ℝ → ℝ) (η : ℕ → ℝ) : Prop where
  reserve_nonneg : 0 ≤ r
  reserve_le : ∀ k, r ≤ t k
  price_bounded : ∃ B : ℝ, ∀ k, t k ≤ B
  capacity_limit : Tendsto κ atTop (𝓝 ρ)
  success_measurable : ∀ k, AEStronglyMeasurable (fun v => (μ k v).success) F
  duplicates_measurable : ∀ k, AEStronglyMeasurable (fun v => (μ k v).duplicates) F
  utility_nonneg : ∀ k v, 0 ≤ U k v
  utility_monotone : ∀ k, Monotone (U k)
  utility_lipschitz : ∀ k v w, |U k v - U k w| ≤ |v - w|
  reserve_ceiling : ∀ k v, U k v ≤ max (v - g - r) 0
  error_nonneg : ∀ k, 0 ≤ᵐ[F] e k
  error_integrable : ∀ k, Integrable (e k) F
  error_mean : Tendsto (fun k => ∫ v, e k v ∂F) atTop (𝓝 0)
  deviation_nonneg : ∀ k v, 0 ≤ δ k v
  deviation_limit : ∀ v, Tendsto (fun k => δ k v) atTop (𝓝 0)
  payment_upper : ∀ k, ∀ᵐ v ∂F,
    U k v ≤ (v - g - t k) * (μ k v).success - t k * (μ k v).duplicates + e k v
  singleton_lower : ∀ k v, max (v - g - t k) 0 - δ k v ≤ U k v
  load_upper : ∀ k, (∫ v, (μ k v).load ∂F) ≤ (n : ℝ) * κ k
  load_lower : ∀ k, r < t k → (n : ℝ) * κ k - η k ≤ ∫ v, (μ k v).load ∂F
  shortfall_limit : Tendsto η atTop (𝓝 0)

namespace Estimates

variable {F : Measure ℝ} [IsProbabilityMeasure F]
  {g r ρ : ℝ} {t κ : ℕ → ℝ} {μ : ℕ → ℝ → CountLaw n}
  {U e δ : ℕ → ℝ → ℝ} {η : ℕ → ℝ}

omit [IsProbabilityMeasure F] in
theorem comp (h : Estimates F g r ρ t κ μ U e δ η)
    (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) :
    Estimates F g r ρ (t ∘ φ) (κ ∘ φ) (μ ∘ φ) (U ∘ φ) (e ∘ φ) (δ ∘ φ) (η ∘ φ) where
  reserve_nonneg := h.reserve_nonneg
  reserve_le := fun k => h.reserve_le (φ k)
  price_bounded := h.price_bounded.imp fun _ hB k => hB (φ k)
  capacity_limit := h.capacity_limit.comp hφ
  success_measurable := fun k => h.success_measurable (φ k)
  duplicates_measurable := fun k => h.duplicates_measurable (φ k)
  utility_nonneg := fun k => h.utility_nonneg (φ k)
  utility_monotone := fun k => h.utility_monotone (φ k)
  utility_lipschitz := fun k => h.utility_lipschitz (φ k)
  reserve_ceiling := fun k => h.reserve_ceiling (φ k)
  error_nonneg := fun k => h.error_nonneg (φ k)
  error_integrable := fun k => h.error_integrable (φ k)
  error_mean := h.error_mean.comp hφ
  deviation_nonneg := fun k => h.deviation_nonneg (φ k)
  deviation_limit := fun v => (h.deviation_limit v).comp hφ
  payment_upper := fun k => h.payment_upper (φ k)
  singleton_lower := fun k => h.singleton_lower (φ k)
  load_upper := fun k => h.load_upper (φ k)
  load_lower := fun k => h.load_lower (φ k)
  shortfall_limit := h.shortfall_limit.comp hφ

def shiftedError (p : ℝ) (k : ℕ) (v : ℝ) : ℝ := e k v + (n : ℝ) * |t k - p|
def shiftedDeviation (p : ℝ) (k : ℕ) (v : ℝ) : ℝ := δ k v + |t k - p|

omit [IsProbabilityMeasure F] in
theorem shifted_error_nonneg (h : Estimates F g r ρ t κ μ U e δ η) (p : ℝ) (k : ℕ) :
    0 ≤ᵐ[F] shiftedError (n := n) (e := e) (t := t) p k := by
  filter_upwards [h.error_nonneg k] with v hv
  exact add_nonneg hv (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))

theorem shifted_error_integrable (h : Estimates F g r ρ t κ μ U e δ η) (p : ℝ) (k : ℕ) :
    Integrable (shiftedError (n := n) (e := e) (t := t) p k) F :=
  (h.error_integrable k).add (integrable_const _)

theorem shifted_error_mean (h : Estimates F g r ρ t κ μ U e δ η)
    (p : ℝ) (ht : Tendsto t atTop (𝓝 p)) :
    Tendsto (fun k => ∫ v, shiftedError (n := n) (e := e) (t := t) p k v ∂F)
      atTop (𝓝 0) := by
  have h0 := h.error_mean.add (((ht.sub_const p).abs).const_mul (n : ℝ))
  simpa only [shiftedError, integral_add (h.error_integrable _) (integrable_const _),
    integral_const, probReal_univ, one_smul, sub_self, abs_zero, mul_zero, add_zero] using h0

omit [IsProbabilityMeasure F] in
theorem shifted_deviation_nonneg (h : Estimates F g r ρ t κ μ U e δ η)
    (p : ℝ) (k : ℕ) (v : ℝ) :
    0 ≤ shiftedDeviation (δ := δ) (t := t) p k v :=
  add_nonneg (h.deviation_nonneg k v) (abs_nonneg _)

omit [IsProbabilityMeasure F] in
theorem shifted_deviation_limit (h : Estimates F g r ρ t κ μ U e δ η)
    (p : ℝ) (ht : Tendsto t atTop (𝓝 p)) (v : ℝ) :
    Tendsto (fun k => shiftedDeviation (δ := δ) (t := t) p k v) atTop (𝓝 0) := by
  simpa [shiftedDeviation] using (h.deviation_limit v).add ((ht.sub_const p).abs)

omit [IsProbabilityMeasure F] in
theorem shifted_upper (h : Estimates F g r ρ t κ μ U e δ η) (p : ℝ) (k : ℕ) :
    ∀ᵐ v ∂F, U k v ≤ (v - (g + p)) * (μ k v).success - p * (μ k v).duplicates +
      shiftedError (n := n) (e := e) (t := t) p k v := by
  filter_upwards [h.payment_upper k] with v hv
  simpa only [sub_add_eq_sub_sub, shiftedError] using NearPPI.change_price (μ k v) hv

omit [IsProbabilityMeasure F] in
theorem shifted_lower (h : Estimates F g r ρ t κ μ U e δ η) (p : ℝ) (k : ℕ) (v : ℝ) :
    max (v - (g + p)) 0 - shiftedDeviation (δ := δ) (t := t) p k v ≤ U k v := by
  have hmax : max (v - (g + p)) 0 ≤ max (v - g - t k) 0 + |t k - p| := by
    apply max_le
    · linarith [le_max_left (v - g - t k) 0, le_abs_self (t k - p)]
    · exact add_nonneg (le_max_right _ _) (abs_nonneg _)
  have hl := h.singleton_lower k v
  unfold shiftedDeviation
  linarith

theorem integrable_success (h : Estimates F g r ρ t κ μ U e δ η) (k : ℕ) :
    Integrable (fun v => (μ k v).success) F := by
  apply Integrable.mono' (integrable_const (1 : ℝ)) (h.success_measurable k)
  exact ae_of_all _ fun v => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (μ k v).success_nonneg] using
      (μ k v).success_le_one

theorem integrable_load (h : Estimates F g r ρ t κ μ U e δ η) (k : ℕ) :
    Integrable (fun v => (μ k v).load) F := by
  have hm : AEStronglyMeasurable (fun v => (μ k v).load) F := by
    convert (h.duplicates_measurable k).add (h.success_measurable k) using 1
    ext v
    simp [CountLaw.duplicates]
  apply Integrable.mono' (integrable_const (n : ℝ)) hm
  exact ae_of_all _ fun v => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (μ k v).load_nonneg] using (μ k v).load_le_n

theorem coverage_le_capacity (h : Estimates F g r ρ t κ μ U e δ η) (k : ℕ) :
    (∫ v, (μ k v).success ∂F) ≤ (n : ℝ) * κ k := by
  apply le_trans (integral_mono_ae (h.integrable_success k) (h.integrable_load k) ?_)
    (h.load_upper k)
  exact ae_of_all _ fun v => (μ k v).success_le_load

theorem tail_le_capacity [NullSingletonClass F]
    (h : Estimates F g r ρ t κ μ U e δ η) (p : ℝ)
    (ht : Tendsto t atTop (𝓝 p)) :
    F.real (Ioi (g + p)) ≤ (n : ℝ) * ρ := by
  have hrp : r ≤ p := ge_of_tendsto ht (Eventually.of_forall h.reserve_le)
  have hQ := coverage_limit F μ U
    (shiftedError (n := n) (e := e) (t := t) p)
    (shiftedDeviation (δ := δ) (t := t) p) (g + p) p
    (h.reserve_nonneg.trans hrp) (measure_singleton _) h.success_measurable
    (fun k => ae_of_all _ (h.utility_nonneg k)) (h.shifted_error_nonneg p)
    (fun k => ae_of_all _ (h.shifted_deviation_nonneg p k))
    (h.shifted_upper p) (fun k => ae_of_all _ (h.shifted_lower p k))
    (h.shifted_error_integrable p) (h.shifted_error_mean p ht)
    (ae_of_all _ (h.shifted_deviation_limit p ht))
  exact le_of_tendsto_of_tendsto' hQ (h.capacity_limit.const_mul (n : ℝ)) h.coverage_le_capacity

theorem aggregates_at_price [NullSingletonClass F]
    (h : Estimates F g r ρ t κ μ U e δ η) (p : ℝ) (hp : 0 < p)
    (ht : Tendsto t atTop (𝓝 p)) :
    Tendsto (fun k => (∫ v, (μ k v).success ∂F,
      (∫ v, (μ k v).duplicates ∂F, ∫ v, (μ k v).load ∂F))) atTop
      (𝓝 (F.real (Ioi (g + p)), (0, F.real (Ioi (g + p))))) := by
  simpa only [NearPPI.integral_cutoffSuccess, Measure.real] using NearPPI.aggregate_limits F μ U
    (shiftedError (n := n) (e := e) (t := t) p)
    (shiftedDeviation (δ := δ) (t := t) p) (g + p) p hp (measure_singleton _)
    h.success_measurable h.duplicates_measurable
    (fun k => ae_of_all _ (h.utility_nonneg k)) (h.shifted_error_nonneg p)
    (fun k => ae_of_all _ (h.shifted_deviation_nonneg p k))
    (h.shifted_upper p) (fun k => ae_of_all _ (h.shifted_lower p k))
    (h.shifted_error_integrable p) (h.shifted_error_mean p ht)
    (ae_of_all _ (h.shifted_deviation_limit p ht))

theorem identify_subsequence [NullSingletonClass F]
    (h : Estimates F g r ρ t κ μ U e δ η)
    (vstar p : ℝ) (hscarce : (n : ℝ) * ρ < F.real (Ioi g))
    (hcut : F.real (Ioi vstar) = (n : ℝ) * ρ)
    (hleft : ∀ v < vstar, 0 < F.real (Ioo v vstar))
    (hright : ∀ v > vstar, 0 < F.real (Ioo vstar v))
    (ht : Tendsto t atTop (𝓝 p)) : p = max r (vstar - g) := by
  have hrp : r ≤ p := ge_of_tendsto ht (Eventually.of_forall h.reserve_le)
  have hcap := h.tail_le_capacity p ht
  have hp := price_pos_of_scarcity F g p ((n : ℝ) * ρ)
    (h.reserve_nonneg.trans hrp) hscarce hcap
  apply price_eq_max_of_tail_conditions F g r p vstar ((n : ℝ) * ρ) hrp hcut hleft hright
  · intro hpr
    have hagg := h.aggregates_at_price p hp ht
    have hL : Tendsto (fun k => ∫ v, (μ k v).load ∂F)
        atTop (𝓝 (F.real (Ioi (g + p)))) := hagg.snd_nhds.snd_nhds
    have hlow : ∀ᶠ k in atTop, (n : ℝ) * κ k - η k ≤ ∫ v, (μ k v).load ∂F := by
      filter_upwards [ht.eventually (lt_mem_nhds hpr)] with k hk
      exact h.load_lower k hk
    have hlim : Tendsto (fun k => (n : ℝ) * κ k - η k) atTop (𝓝 ((n : ℝ) * ρ)) := by
      simpa using (h.capacity_limit.const_mul (n : ℝ)).sub h.shortfall_limit
    exact le_antisymm hcap (le_of_tendsto_of_tendsto hlim hL hlow)
  · intro hpr
    simpa only [hpr] using hcap

theorem price_limit [NullSingletonClass F]
    (h : Estimates F g r ρ t κ μ U e δ η)
    (vstar : ℝ) (hscarce : (n : ℝ) * ρ < F.real (Ioi g))
    (hcut : F.real (Ioi vstar) = (n : ℝ) * ρ)
    (hleft : ∀ v < vstar, 0 < F.real (Ioo v vstar))
    (hright : ∀ v > vstar, 0 < F.real (Ioo vstar v)) :
    Tendsto t atTop (𝓝 (max r (vstar - g))) := by
  obtain ⟨B, hB⟩ := h.price_bounded
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨p, _, φ, hφ, ht⟩ :=
    (isCompact_Icc : IsCompact (Icc r B)).tendsto_subseq
      (fun k => show t (ns k) ∈ Icc r B from ⟨h.reserve_le _, hB _⟩)
  have hcomp := h.comp (ns ∘ φ) (hns.comp hφ.tendsto_atTop)
  have heq := hcomp.identify_subsequence vstar p hscarce hcut hleft hright ht
  exact ⟨φ, by simpa only [heq, Function.comp_def] using ht⟩

theorem utility_at_price (h : Estimates F g r ρ t κ μ U e δ η)
    (vstar p : ℝ) (ht : Tendsto t atTop (𝓝 p)) (hp : p = max r (vstar - g))
    (hleft : ∀ v < vstar, 0 < F.real (Ioo v vstar)) :
    ∀ v, Tendsto (fun k => U k v) atTop (𝓝 (max (v - g - p) 0)) := by
  have hrp : r ≤ p := by rw [hp]; exact le_max_left _ _
  rcases eq_or_lt_of_le hrp with hpr | hpr
  · rw [← hpr] at ht ⊢
    exact binding_utility_limit g r (fun k v => by
        simpa only [sub_add_eq_sub_sub] using h.shifted_lower r k v)
      h.reserve_ceiling (h.shifted_deviation_limit r ht)
  · have he : p = vstar - g := by
      have hrv : r < vstar - g := by simpa only [hp, lt_max_iff,
        lt_self_iff_false, false_or] using hpr
      exact hp.trans (max_eq_right hrv.le)
    have hc : g + p = vstar := by linarith
    have hlim := utility_limit F μ U
      (shiftedError (n := n) (e := e) (t := t) p)
      (shiftedDeviation (δ := δ) (t := t) p) (g + p) p
      (h.reserve_nonneg.trans hrp) h.utility_nonneg h.utility_monotone h.utility_lipschitz
      (h.shifted_error_nonneg p) (h.shifted_error_integrable p) (h.shifted_upper p)
      (h.shifted_lower p) (h.shifted_error_mean p ht) (h.shifted_deviation_limit p ht)
      (by simpa only [hc] using hleft)
    simpa only [sub_add_eq_sub_sub] using hlim

theorem full_limits [NullSingletonClass F]
    (h : Estimates F g r ρ t κ μ U e δ η)
    (vstar : ℝ) (hscarce : (n : ℝ) * ρ < F.real (Ioi g))
    (hcut : F.real (Ioi vstar) = (n : ℝ) * ρ)
    (hleft : ∀ v < vstar, 0 < F.real (Ioo v vstar))
    (hright : ∀ v > vstar, 0 < F.real (Ioo vstar v)) :
    (∀ v, Tendsto (fun k => U k v) atTop (𝓝 (max (v - g - max r (vstar - g)) 0))) ∧
    Tendsto (fun k => (∫ v, (μ k v).success ∂F,
      (∫ v, (μ k v).duplicates ∂F, ∫ v, (μ k v).load ∂F))) atTop
      (𝓝 (F.real (Ioi (g + max r (vstar - g))),
        (0, F.real (Ioi (g + max r (vstar - g)))))) := by
  have ht := h.price_limit vstar hscarce hcut hleft hright
  have hp := price_pos_of_scarcity F g (max r (vstar - g)) ((n : ℝ) * ρ)
    (h.reserve_nonneg.trans (le_max_left _ _)) hscarce (h.tail_le_capacity _ ht)
  exact ⟨h.utility_at_price vstar _ ht rfl hleft, h.aggregates_at_price _ hp ht⟩

end Estimates
end FCAppendix.CommonReserve.ReserveAnalysis
