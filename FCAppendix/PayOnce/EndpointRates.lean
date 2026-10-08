import FCAppendix.PayOnce.EndpointMoments

namespace FCAppendix.PayOnce.EndpointRates

open MeasureTheory Filter Topology Set ManyProposers BoundedEndpoint SharpEndpoint EndpointMoments

theorem endpoint_of_tail (μ : Measure ℝ) [IsFiniteMeasure μ]
    {M γ c : ℝ} (hc : 0 < c)
    (htail : Tendsto (fun u : ℝ => μ.real (Ioi (M - u)) / u ^ γ) (𝓝[>] 0) (𝓝 c)) :
    ∀ u > 0, 0 < μ (Ioi (M - u)) := by
  intro u hu
  have hu' : ∀ᶠ v in 𝓝[>] (0 : ℝ), v ∈ Ioo 0 u := Ioo_mem_nhdsGT hu
  obtain ⟨v, hv, hpos⟩ := (hu'.and (htail.eventually (lt_mem_nhds hc))).exists
  have hvγ : 0 < v ^ γ := Real.rpow_pos_of_pos hv.1 γ
  have hreal : 0 < μ.real (Ioi (M - v)) := (div_pos_iff_of_pos_right hvγ).mp hpos
  have hmeas : 0 < μ (Ioi (M - v)) :=
    pos_iff_ne_zero.mpr ((measureReal_ne_zero_iff).mp hreal.ne')
  exact lt_of_lt_of_le hmeas (measure_mono (Ioi_subset_Ioi (by linarith [hv.2])))

theorem tendsto_first_moment (μ : Measure ℝ) [IsFiniteMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) {M γ c : ℝ} (hM : 0 < M) (hγ : 0 < γ) (hc : 0 < c)
    (hle : ∀ᵐ w ∂μ, w ≤ M)
    (htail : Tendsto (fun u : ℝ => μ.real (Ioi (M - u)) / u ^ γ) (𝓝[>] 0) (𝓝 c)) :
    Tendsto (fun d : ℝ => (∫ w, pStar n (M - d) w ∂μ) / d ^ (γ + 1))
      (𝓝[>] 0) (𝓝 (c / ((γ + 1) * (M * ((n : ℝ) - 1))))) := by
  have h := tendsto_pStar_moment μ hn hM hγ hc hle htail 0
  norm_num [Real.Gamma_nat_eq_factorial] at h
  have hq : γ + 1 ≠ 0 := (by linarith : 0 < γ + 1).ne'
  have hG : Real.Gamma (γ + 1) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  rw [Real.Gamma_add_one hq] at h
  have he : c * Real.Gamma (γ + 1) / ((γ + 1) * Real.Gamma (γ + 1)) /
      (M * ((n : ℝ) - 1)) = c / ((γ + 1) * (M * ((n : ℝ) - 1))) := by
    field_simp
  rwa [he] at h

theorem tendsto_second_moment (μ : Measure ℝ) [IsFiniteMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) {M γ c : ℝ} (hM : 0 < M) (hγ : 0 < γ) (hc : 0 < c)
    (hle : ∀ᵐ w ∂μ, w ≤ M)
    (htail : Tendsto (fun u : ℝ => μ.real (Ioi (M - u)) / u ^ γ) (𝓝[>] 0) (𝓝 c)) :
    Tendsto (fun d : ℝ => (∫ w, pStar n (M - d) w ^ 2 ∂μ) / d ^ (γ + 2))
      (𝓝[>] 0) (𝓝 (2 * c / ((γ + 1) * (γ + 2) * (M * ((n : ℝ) - 1)) ^ 2))) := by
  have h := tendsto_pStar_moment μ hn hM hγ hc hle htail 1
  norm_num [Real.Gamma_nat_eq_factorial] at h
  have hq : γ + 1 ≠ 0 := (by linarith : 0 < γ + 1).ne'
  have hr : γ + 2 ≠ 0 := (by linarith : 0 < γ + 2).ne'
  have hG : Real.Gamma (γ + 1) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hre : γ + 2 = (γ + 1) + 1 := by ring
  rw [Real.Gamma_add_one hr, hre, Real.Gamma_add_one hq] at h
  have he : c * Real.Gamma (γ + 1) * 2 /
      ((γ + 1 + 1) * ((γ + 1) * Real.Gamma (γ + 1))) / (M * ((n : ℝ) - 1)) ^ 2 =
      2 * c / ((γ + 1) * (γ + 2) * (M * ((n : ℝ) - 1)) ^ 2) := by
    field_simp
    ring
  rwa [he, ← hre] at h

theorem tendsto_moment_ratio_div_gap (μ : Measure ℝ) [IsFiniteMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) {M γ c : ℝ} (hM : 0 < M) (hγ : 0 < γ) (hc : 0 < c)
    (hle : ∀ᵐ w ∂μ, w ≤ M)
    (htail : Tendsto (fun u : ℝ => μ.real (Ioi (M - u)) / u ^ γ) (𝓝[>] 0) (𝓝 c)) :
    Tendsto (fun d : ℝ => ((∫ w, pStar n (M - d) w ^ 2 ∂μ) /
      (∫ w, pStar n (M - d) w ∂μ)) / d) (𝓝[>] 0)
      (𝓝 (2 / ((γ + 2) * (M * ((n : ℝ) - 1))))) := by
  have h₁ := tendsto_first_moment μ hn hM hγ hc hle htail
  have h₂ := tendsto_second_moment μ hn hM hγ hc hle htail
  have ha := nat_sub_one_pos hn
  have hC : 0 < c / ((γ + 1) * (M * ((n : ℝ) - 1))) :=
    div_pos hc (mul_pos (by linarith) (mul_pos hM ha))
  have hh := h₂.div h₁ hC.ne'
  have he : (2 * c / ((γ + 1) * (γ + 2) * (M * ((n : ℝ) - 1)) ^ 2)) /
      (c / ((γ + 1) * (M * ((n : ℝ) - 1)))) =
      2 / ((γ + 2) * (M * ((n : ℝ) - 1))) := by
    have hq : γ + 1 ≠ 0 := (by linarith : 0 < γ + 1).ne'
    field_simp
  rw [he] at hh
  apply hh.congr'
  filter_upwards [Ioo_mem_nhdsGT hM] with d hd
  have hp : d ^ (γ + 1) ≠ 0 := (Real.rpow_pos_of_pos hd.1 _).ne'
  have he' : d ^ (γ + 2) = d ^ (γ + 1) * d := by
    rw [show γ + 2 = (γ + 1) + 1 by ring, Real.rpow_add_one hd.1.ne']
  dsimp only [Pi.div_apply]
  rw [he']
  field_simp

theorem tendsto_capacity_gap (μ : Measure ℝ) [IsFiniteMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) {M γ c : ℝ} (hM : 0 < M) (hc : 0 < c)
    (hle : ∀ᵐ w ∂μ, w ≤ M)
    (htail : Tendsto (fun u : ℝ => μ.real (Ioi (M - u)) / u ^ γ) (𝓝[>] 0) (𝓝 c))
    {β₀ : ℝ} (hβ₀ : 0 < β₀) {t : ℝ → ℝ}
    (hcap : ∀ β ∈ Ioo 0 β₀, 0 < t β ∧ ∫ w, pStar n (t β) w ∂μ = β / n) :
    Tendsto (fun β => M - t β) (𝓝[>] 0) (𝓝[>] 0) := by
  have hend := endpoint_of_tail μ hc htail
  have ht := tendsto_nhdsWithin_iff.1 (tendsto_root_endpoint μ hn hM hle hend hβ₀ hcap)
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · simpa using ht.1.const_sub M
  · filter_upwards [ht.2] with β hβ
    exact sub_pos.mpr (show t β < M from hβ)

theorem tendsto_capacity_div_gap_power (μ : Measure ℝ) [IsFiniteMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) {M γ c : ℝ} (hM : 0 < M) (hγ : 0 < γ) (hc : 0 < c)
    (hle : ∀ᵐ w ∂μ, w ≤ M)
    (htail : Tendsto (fun u : ℝ => μ.real (Ioi (M - u)) / u ^ γ) (𝓝[>] 0) (𝓝 c))
    {β₀ : ℝ} (hβ₀ : 0 < β₀) {t : ℝ → ℝ}
    (hcap : ∀ β ∈ Ioo 0 β₀, 0 < t β ∧ ∫ w, pStar n (t β) w ∂μ = β / n) :
    Tendsto (fun β : ℝ => β / (M - t β) ^ (γ + 1)) (𝓝[>] 0)
      (𝓝 ((n : ℝ) * c / ((γ + 1) * (M * ((n : ℝ) - 1))))) := by
  have hd := tendsto_capacity_gap μ hn hM hc hle htail hβ₀ hcap
  have hh := ((tendsto_first_moment μ hn hM hγ hc hle htail).comp hd).const_mul (n : ℝ)
  simp only [Function.comp_apply, sub_sub_cancel, ← mul_div_assoc] at hh
  apply hh.congr'
  filter_upwards [Ioo_mem_nhdsGT hβ₀] with β hβ
  rw [(hcap β hβ).2, mul_div_cancel₀ _ (nat_cast_pos hn).ne']

theorem tendsto_multiplicity_excess_div_gap (μ : Measure ℝ) [IsFiniteMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) {M γ c : ℝ} (hM : 0 < M) (hγ : 0 < γ) (hc : 0 < c)
    (hle : ∀ᵐ w ∂μ, w ≤ M)
    (htail : Tendsto (fun u : ℝ => μ.real (Ioi (M - u)) / u ^ γ) (𝓝[>] 0) (𝓝 c))
    {β₀ : ℝ} (hβ₀ : 0 < β₀) {t : ℝ → ℝ}
    (hcap : ∀ β ∈ Ioo 0 β₀, 0 < t β ∧ ∫ w, pStar n (t β) w ∂μ = β / n) :
    Tendsto (fun β : ℝ =>
      (β / (∫ w, success n (pStar n (t β) w) ∂μ) - 1) / (M - t β))
      (𝓝[>] 0) (𝓝 (1 / ((γ + 2) * M))) := by
  have hend := endpoint_of_tail μ hc htail
  have hd := tendsto_capacity_gap μ hn hM hc hle htail hβ₀ hcap
  have hμ := tendsto_multiplicity_excess_div_moment_ratio μ hn hM hle hend hβ₀ hcap
  have hratio := (tendsto_moment_ratio_div_gap μ hn hM hγ hc hle htail).comp hd
  simp only [Function.comp_def, sub_sub_cancel] at hratio
  have hh := hμ.mul hratio
  have ha := nat_sub_one_pos hn
  have he : ((n : ℝ) - 1) / 2 * (2 / ((γ + 2) * (M * ((n : ℝ) - 1)))) =
      1 / ((γ + 2) * M) := by field_simp
  rw [he] at hh
  apply hh.congr'
  filter_upwards [Ioo_mem_nhdsGT hβ₀] with β hβ
  have htβ := (hcap β hβ).1
  have htM := root_lt_endpoint μ hn hle hβ.1 htβ (hcap β hβ).2
  have hI1 := integral_pStar_pow_pos μ hn hend htβ htM 1
  have hI2 := integral_pStar_pow_pos μ hn hend htβ htM 2
  simp only [pow_one] at hI1
  field_simp

theorem tendsto_gap_div_capacity_rpow (μ : Measure ℝ) [IsFiniteMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) {M γ c : ℝ} (hM : 0 < M) (hγ : 0 < γ) (hc : 0 < c)
    (hle : ∀ᵐ w ∂μ, w ≤ M)
    (htail : Tendsto (fun u : ℝ => μ.real (Ioi (M - u)) / u ^ γ) (𝓝[>] 0) (𝓝 c))
    {β₀ : ℝ} (hβ₀ : 0 < β₀) {t : ℝ → ℝ}
    (hcap : ∀ β ∈ Ioo 0 β₀, 0 < t β ∧ ∫ w, pStar n (t β) w ∂μ = β / n) :
    Tendsto (fun β : ℝ => (M - t β) / β ^ (1 / (γ + 1))) (𝓝[>] 0)
      (𝓝 ((((γ + 1) * (M * ((n : ℝ) - 1))) / ((n : ℝ) * c)) ^ (1 / (γ + 1)))) := by
  have ha := nat_sub_one_pos hn
  have hn0 := nat_cast_pos hn
  have hq : 0 < γ + 1 := by linarith
  have hC : 0 < (n : ℝ) * c / ((γ + 1) * (M * ((n : ℝ) - 1))) :=
    div_pos (mul_pos hn0 hc) (mul_pos hq (mul_pos hM ha))
  have hinv := (tendsto_capacity_div_gap_power μ hn hM hγ hc hle htail hβ₀ hcap).inv₀ hC.ne'
  simp only [inv_div] at hinv
  have hA : 0 < (γ + 1) * (M * ((n : ℝ) - 1)) / ((n : ℝ) * c) :=
    div_pos (mul_pos hq (mul_pos hM ha)) (mul_pos hn0 hc)
  have hh := hinv.rpow_const (p := 1 / (γ + 1)) (Or.inl hA.ne')
  have hend := endpoint_of_tail μ hc htail
  apply hh.congr'
  filter_upwards [Ioo_mem_nhdsGT hβ₀] with β hβ
  have hd : 0 < M - t β := sub_pos.mpr
    (root_lt_endpoint μ hn hle hβ.1 (hcap β hβ).1 (hcap β hβ).2)
  rw [Real.div_rpow (Real.rpow_nonneg hd.le _) hβ.1.le,
    ← Real.rpow_mul hd.le, mul_one_div_cancel hq.ne', Real.rpow_one]

noncomputable def comparisonGap (n : ℕ) (M γ c β : ℝ) : ℝ :=
  (((γ + 1) * (M * ((n : ℝ) - 1))) * β / ((n : ℝ) * c)) ^ (1 / (γ + 1))

theorem tendsto_gap_div_comparisonGap (μ : Measure ℝ) [IsFiniteMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) {M γ c : ℝ} (hM : 0 < M) (hγ : 0 < γ) (hc : 0 < c)
    (hle : ∀ᵐ w ∂μ, w ≤ M)
    (htail : Tendsto (fun u : ℝ => μ.real (Ioi (M - u)) / u ^ γ) (𝓝[>] 0) (𝓝 c))
    {β₀ : ℝ} (hβ₀ : 0 < β₀) {t : ℝ → ℝ}
    (hcap : ∀ β ∈ Ioo 0 β₀, 0 < t β ∧ ∫ w, pStar n (t β) w ∂μ = β / n) :
    Tendsto (fun β : ℝ => (M - t β) / comparisonGap n M γ c β) (𝓝[>] 0) (𝓝 1) := by
  let A : ℝ := (γ + 1) * (M * ((n : ℝ) - 1)) / ((n : ℝ) * c)
  have hA : 0 < A := div_pos (mul_pos (by linarith) (mul_pos hM (nat_sub_one_pos hn)))
    (mul_pos (nat_cast_pos hn) hc)
  have hh := (tendsto_gap_div_capacity_rpow μ hn hM hγ hc hle htail hβ₀ hcap).div_const
    (A ^ (1 / (γ + 1)))
  change Tendsto _ _ (𝓝 (A ^ (1 / (γ + 1)) / A ^ (1 / (γ + 1)))) at hh
  rw [div_self (Real.rpow_pos_of_pos hA _).ne'] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with β hβ
  have hform : comparisonGap n M γ c β = A ^ (1 / (γ + 1)) * β ^ (1 / (γ + 1)) := by
    unfold comparisonGap
    have he : (γ + 1) * (M * ((n : ℝ) - 1)) * β / ((n : ℝ) * c) = A * β := by dsimp [A]; ring
    rw [he, Real.mul_rpow hA.le (show 0 ≤ β from le_of_lt hβ)]
  rw [hform]
  ring

theorem tendsto_multiplicity_excess_div_comparisonGap (μ : Measure ℝ) [IsFiniteMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) {M γ c : ℝ} (hM : 0 < M) (hγ : 0 < γ) (hc : 0 < c)
    (hle : ∀ᵐ w ∂μ, w ≤ M)
    (htail : Tendsto (fun u : ℝ => μ.real (Ioi (M - u)) / u ^ γ) (𝓝[>] 0) (𝓝 c))
    {β₀ : ℝ} (hβ₀ : 0 < β₀) {t : ℝ → ℝ}
    (hcap : ∀ β ∈ Ioo 0 β₀, 0 < t β ∧ ∫ w, pStar n (t β) w ∂μ = β / n) :
    Tendsto (fun β : ℝ =>
      (β / (∫ w, success n (pStar n (t β) w) ∂μ) - 1) / comparisonGap n M γ c β)
      (𝓝[>] 0) (𝓝 (1 / ((γ + 2) * M))) := by
  have hh := (tendsto_multiplicity_excess_div_gap μ hn hM hγ hc hle htail hβ₀ hcap).mul
    (tendsto_gap_div_comparisonGap μ hn hM hγ hc hle htail hβ₀ hcap)
  rw [mul_one] at hh
  have hend := endpoint_of_tail μ hc htail
  apply hh.congr'
  filter_upwards [Ioo_mem_nhdsGT hβ₀] with β hβ
  have hd : 0 < M - t β := sub_pos.mpr
    (root_lt_endpoint μ hn hle hβ.1 (hcap β hβ).1 (hcap β hβ).2)
  field_simp

theorem tendsto_tail_div_gap_of_density (μ : Measure ℝ) [IsFiniteMeasure μ]
    {M u₀ : ℝ} {f : ℝ → ℝ} (hu₀ : 0 < u₀)
    (hf : ContinuousOn f (Icc (M - u₀) M))
    (hdens : ∀ u ∈ Ioc 0 u₀, μ.real (Ioi (M - u)) = ∫ x in (M - u)..M, f x) :
    Tendsto (fun u : ℝ => μ.real (Ioi (M - u)) / u) (𝓝[>] 0) (𝓝 (f M)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.mp
    (hf M ⟨by linarith, le_rfl⟩) (ε / 2) (half_pos hε)
  filter_upwards [Ioo_mem_nhdsGT (lt_min hu₀ (half_pos hδ))] with u hu
  have huu₀ : u ≤ u₀ := hu.2.le.trans (min_le_left _ _)
  have huδ : u < δ / 2 := hu.2.trans_le (min_le_right _ _)
  have hsub : Icc (M - u) M ⊆ Icc (M - u₀) M := Icc_subset_Icc (by linarith) le_rfl
  have hfu : ∀ x ∈ Icc (M - u) M, f M - ε / 2 ≤ f x ∧ f x ≤ f M + ε / 2 := by
    intro x hx
    have hd : dist x M < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hx.1, hx.2]
    have hh := hball (hsub hx) hd
    rw [Real.dist_eq, abs_lt] at hh
    constructor <;> linarith [hh.1, hh.2]
  have hle : M - u ≤ M := by linarith [hu.1]
  have hi : IntervalIntegrable f volume (M - u) M := (hf.mono hsub).intervalIntegrable_of_Icc hle
  have hlo := intervalIntegral.integral_mono_on hle intervalIntegrable_const hi
    (fun x hx => (hfu x hx).1)
  have hup := intervalIntegral.integral_mono_on hle hi intervalIntegrable_const
    (fun x hx => (hfu x hx).2)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hlo hup
  rw [hdens u ⟨hu.1, huu₀⟩, Real.dist_eq, abs_lt]
  have hlo' : f M - ε / 2 ≤ (∫ x in (M - u)..M, f x) / u := by
    rw [le_div_iff₀ hu.1]
    nlinarith
  have hup' : (∫ x in (M - u)..M, f x) / u ≤ f M + ε / 2 := by
    rw [div_le_iff₀ hu.1]
    nlinarith
  constructor <;> linarith

theorem tendsto_multiplicity_excess_div_sqrt_of_density (μ : Measure ℝ) [IsFiniteMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) {M u₀ : ℝ} {f : ℝ → ℝ} (hM : 0 < M) (hu₀ : 0 < u₀)
    (hle : ∀ᵐ w ∂μ, w ≤ M) (hf : ContinuousOn f (Icc (M - u₀) M)) (hfM : 0 < f M)
    (hdens : ∀ u ∈ Ioc 0 u₀, μ.real (Ioi (M - u)) = ∫ x in (M - u)..M, f x)
    {β₀ : ℝ} (hβ₀ : 0 < β₀) {t : ℝ → ℝ}
    (hcap : ∀ β ∈ Ioo 0 β₀, 0 < t β ∧ ∫ w, pStar n (t β) w ∂μ = β / n) :
    Tendsto (fun β : ℝ =>
      (β / (∫ w, success n (pStar n (t β) w) ∂μ) - 1) / Real.sqrt β)
      (𝓝[>] 0) (𝓝 ((1 / 3 : ℝ) * Real.sqrt (2 * ((n : ℝ) - 1) / ((n : ℝ) * M * f M)))) := by
  have htail : Tendsto (fun u : ℝ => μ.real (Ioi (M - u)) / u ^ (1 : ℝ))
      (𝓝[>] 0) (𝓝 (f M)) := by
    simpa only [Real.rpow_one] using tendsto_tail_div_gap_of_density μ hu₀ hf hdens
  have hh := (tendsto_multiplicity_excess_div_gap μ hn hM zero_lt_one hfM hle htail hβ₀ hcap).mul
    (tendsto_gap_div_capacity_rpow μ hn hM zero_lt_one hfM hle htail hβ₀ hcap)
  norm_num only at hh
  simp only [← Real.sqrt_eq_rpow] at hh
  have ha := nat_sub_one_pos hn
  have hn0 := nat_cast_pos hn
  have he : 1 / (3 * M) * Real.sqrt (2 * (M * ((n : ℝ) - 1)) / ((n : ℝ) * f M)) =
      (1 / 3 : ℝ) * Real.sqrt (2 * ((n : ℝ) - 1) / ((n : ℝ) * M * f M)) := by
    have he' : 2 * ((n : ℝ) - 1) / ((n : ℝ) * M * f M) =
        (2 * (M * ((n : ℝ) - 1)) / ((n : ℝ) * f M)) / M ^ 2 := by
      field_simp
    rw [he', Real.sqrt_div (x := 2 * (M * ((n : ℝ) - 1)) / ((n : ℝ) * f M))
      (y := M ^ 2) (by positivity), Real.sqrt_sq hM.le]
    ring
  rw [he] at hh
  apply hh.congr'
  filter_upwards [Ioo_mem_nhdsGT hβ₀] with β hβ
  have hd : 0 < M - t β := sub_pos.mpr
    (root_lt_endpoint μ hn hle hβ.1 (hcap β hβ).1 (hcap β hβ).2)
  field_simp

theorem comparisonGap_pos {n : ℕ} (hn : 2 ≤ n) {M γ c β : ℝ}
    (hM : 0 < M) (hγ : 0 < γ) (hc : 0 < c) (hβ : 0 < β) :
    0 < comparisonGap n M γ c β := by
  unfold comparisonGap
  apply Real.rpow_pos_of_pos
  exact div_pos (mul_pos (mul_pos (by linarith) (mul_pos hM (nat_sub_one_pos hn))) hβ)
    (mul_pos (nat_cast_pos hn) hc)

theorem tendsto_cutoff_remainder (μ : Measure ℝ) [IsFiniteMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) {M γ c : ℝ} (hM : 0 < M) (hγ : 0 < γ) (hc : 0 < c)
    (hle : ∀ᵐ w ∂μ, w ≤ M)
    (htail : Tendsto (fun u : ℝ => μ.real (Ioi (M - u)) / u ^ γ) (𝓝[>] 0) (𝓝 c))
    {β₀ : ℝ} (hβ₀ : 0 < β₀) {t : ℝ → ℝ}
    (hcap : ∀ β ∈ Ioo 0 β₀, 0 < t β ∧ ∫ w, pStar n (t β) w ∂μ = β / n) :
    Tendsto (fun β : ℝ => (t β - (M - comparisonGap n M γ c β)) /
      comparisonGap n M γ c β) (𝓝[>] 0) (𝓝 0) := by
  have hh := (tendsto_gap_div_comparisonGap μ hn hM hγ hc hle htail hβ₀ hcap).const_sub 1
  rw [sub_self] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with β hβ
  have hcomp := comparisonGap_pos hn hM hγ hc hβ
  field_simp
  ring

theorem tendsto_pStar_moment_capacity_root (μ : Measure ℝ) [IsFiniteMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) {M γ c : ℝ} (hM : 0 < M) (hγ : 0 < γ) (hc : 0 < c)
    (hle : ∀ᵐ w ∂μ, w ≤ M)
    (htail : Tendsto (fun u : ℝ => μ.real (Ioi (M - u)) / u ^ γ) (𝓝[>] 0) (𝓝 c))
    {β₀ : ℝ} (hβ₀ : 0 < β₀) {t : ℝ → ℝ}
    (hcap : ∀ β ∈ Ioo 0 β₀, 0 < t β ∧ ∫ w, pStar n (t β) w ∂μ = β / n) (j : ℕ) :
    Tendsto (fun β : ℝ => (∫ w, pStar n (t β) w ^ (j + 1) ∂μ) /
      (M - t β) ^ (γ + (j + 1 : ℕ))) (𝓝[>] 0)
      (𝓝 ((c * Real.Gamma (γ + 1) * Real.Gamma ((j + 1 : ℕ) + 1) /
        Real.Gamma (γ + (j + 1 : ℕ) + 1)) / (M * ((n : ℝ) - 1)) ^ (j + 1))) := by
  have hh := (tendsto_pStar_moment μ hn hM hγ hc hle htail j).comp
    (tendsto_capacity_gap μ hn hM hc hle htail hβ₀ hcap)
  simpa only [Function.comp_def, sub_sub_cancel] using hh

end FCAppendix.PayOnce.EndpointRates
