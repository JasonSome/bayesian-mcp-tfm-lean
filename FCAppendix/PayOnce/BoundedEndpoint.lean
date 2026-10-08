import FCAppendix.PayOnce.ManyProposers

namespace FCAppendix
namespace PayOnce
namespace BoundedEndpoint

open MeasureTheory Filter Topology Set ManyProposers

theorem success_le_nat_mul (n : ℕ) {p : ℝ} (hp1 : p ≤ 1) :
    success n p ≤ n * p := by
  unfold success
  have h := one_add_mul_le_pow (a := -p) (by linarith) n
  rw [← sub_eq_add_neg] at h
  linarith

theorem nat_mul_le_success (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (n : ℝ) * p * (1 - ((n : ℝ) - 1) * p) ≤ success n p := by
  induction n with
  | zero => simp [success]
  | succ n ih =>
    have hs : success (n + 1) p = p + (1 - p) * success n p := by
      unfold success
      ring
    rw [hs]
    push_cast
    have h1 := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hp1)
    have h2 : 0 ≤ (n : ℝ) * p ^ 2 := by positivity
    have h3 : 0 ≤ (n : ℝ) * (n : ℝ) * p ^ 3 := by positivity
    have h4 : 0 ≤ (n : ℝ) * p ^ 3 := by positivity
    nlinarith

theorem ae_le_iff_measure_Ioi (μW : Measure ℝ) (B : ℝ) :
    (∀ᵐ w ∂μW, w ≤ B) ↔ μW (Ioi B) = 0 := by
  rw [ae_iff]
  have : {w : ℝ | ¬w ≤ B} = Ioi B := by
    ext w
    simp
  rw [this]

theorem exists_upper_endpoint (μW : Measure ℝ) (hbdd : ∃ B, ∀ᵐ w ∂μW, w ≤ B)
    (hpos : 0 < μW (Ioi 0)) :
    ∃ M, 0 < M ∧ (∀ᵐ w ∂μW, w ≤ M) ∧ ∀ u > 0, 0 < μW (Ioi (M - u)) := by
  set S : Set ℝ := {B | μW (Ioi B) = 0} with hS
  obtain ⟨B, hB⟩ := hbdd
  have hBS : B ∈ S := (ae_le_iff_measure_Ioi μW B).mp hB
  have hSpos : ∀ x ∈ S, 0 < x := by
    intro x hx
    by_contra h
    push Not at h
    have : μW (Ioi 0) ≤ μW (Ioi x) := measure_mono (Ioi_subset_Ioi h)
    rw [show μW (Ioi x) = 0 from hx] at this
    exact absurd (lt_of_lt_of_le hpos this) (lt_irrefl _)
  have hbelow : BddBelow S := ⟨0, fun x hx => (hSpos x hx).le⟩
  have hne : S.Nonempty := ⟨B, hBS⟩
  set M := sInf S with hMdef
  have hMS : M ∈ S := by
    have hU : Ioi M = ⋃ k : ℕ, Ioi (M + 1 / ((k : ℝ) + 1)) := by
      ext x
      simp only [mem_Ioi, mem_iUnion]
      constructor
      · intro hx
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
        exact ⟨k, by linarith⟩
      · rintro ⟨k, hk⟩
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
    change μW (Ioi M) = 0
    rw [hU]
    refine measure_iUnion_null (fun k => ?_)
    have hlt : sInf S < M + 1 / ((k : ℝ) + 1) := by
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
    obtain ⟨x, hxS, hx⟩ := exists_lt_of_csInf_lt hne hlt
    exact measure_mono_null (Ioi_subset_Ioi hx.le) hxS
  refine ⟨M, hSpos M hMS, (ae_le_iff_measure_Ioi μW M).mpr hMS, fun u hu => ?_⟩
  by_contra h
  have h0 : μW (Ioi (M - u)) = 0 := le_antisymm (not_lt.mp h) zero_le
  have := csInf_le hbelow (show M - u ∈ S from h0)
  linarith

section Endpoint

variable (μW : Measure ℝ) [IsFiniteMeasure μW] {n : ℕ} {M : ℝ}

theorem nat_cast_pos {n : ℕ} (hn : 2 ≤ n) : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)

theorem integral_pStar_pos (hn : 2 ≤ n) (hend : ∀ u > 0, 0 < μW (Ioi (M - u))) {s : ℝ}
    (hs : 0 < s) (hsM : s < M) : 0 < ∫ w, pStar n s w ∂μW := by
  rw [integral_pos_iff_support_of_nonneg (fun w => pStar_nonneg n s w)
    (integrable_pStar μW hn hs)]
  have h := hend (M - s) (by linarith)
  rw [sub_sub_cancel] at h
  refine lt_of_lt_of_le h (measure_mono ?_)
  intro w hw
  exact Function.mem_support.mpr (pStar_pos hn hs hw).ne'

omit [IsFiniteMeasure μW] in

theorem root_lt_endpoint (hn : 2 ≤ n) (hle : ∀ᵐ w ∂μW, w ≤ M) {β s : ℝ} (hβ : 0 < β)
    (hs : 0 < s) (hcap : ∫ w, pStar n s w ∂μW = β / n) : s < M := by
  by_contra h
  push Not at h
  have h0 : ∫ w, pStar n s w ∂μW = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hle] with w hw
    exact pStar_eq_zero hn hs (hw.trans h)
  rw [h0] at hcap
  have : 0 < β / n := div_pos hβ (nat_cast_pos hn)
  linarith

variable {β₀ : ℝ} {t : ℝ → ℝ}

theorem root_strictAntiOn (hn : 2 ≤ n)
    (hcap : ∀ β ∈ Ioo 0 β₀, 0 < t β ∧ ∫ w, pStar n (t β) w ∂μW = β / n) :
    StrictAntiOn t (Ioo 0 β₀) := by
  intro β₁ h₁ β₂ h₂ h12
  by_contra h
  push Not at h
  have hmono := integral_pStar_anti μW hn (hcap β₁ h₁).1 h
  rw [(hcap β₁ h₁).2, (hcap β₂ h₂).2] at hmono
  have := (div_le_div_iff_of_pos_right (nat_cast_pos hn)).mp hmono
  linarith

theorem tendsto_root_endpoint (hn : 2 ≤ n) (hM : 0 < M) (hle : ∀ᵐ w ∂μW, w ≤ M)
    (hend : ∀ u > 0, 0 < μW (Ioi (M - u))) (hβ₀ : 0 < β₀)
    (hcap : ∀ β ∈ Ioo 0 β₀, 0 < t β ∧ ∫ w, pStar n (t β) w ∂μW = β / n) :
    Tendsto t (𝓝[>] 0) (𝓝[<] M) := by
  have hdom : ∀ᶠ β in 𝓝[>] (0 : ℝ), β ∈ Ioo 0 β₀ := Ioo_mem_nhdsGT hβ₀
  have hlt : ∀ᶠ β in 𝓝[>] (0 : ℝ), t β < M :=
    hdom.mono (fun β hβ => root_lt_endpoint μW hn hle hβ.1 (hcap β hβ).1 (hcap β hβ).2)
  refine tendsto_nhdsWithin_iff.2 ⟨?_, hlt⟩
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => hlt.mono (fun β h => h.trans hb)⟩
  have hs0 : 0 < max a (M / 2) := lt_of_lt_of_le (half_pos hM) (le_max_right _ _)
  have hsM : max a (M / 2) < M := max_lt ha (half_lt_self hM)
  have hnc : 0 < (n : ℝ) * ∫ w, pStar n (max a (M / 2)) w ∂μW :=
    mul_pos (nat_cast_pos hn) (integral_pStar_pos μW hn hend hs0 hsM)
  filter_upwards [hdom, Ioo_mem_nhdsGT hnc] with β hβ hβc
  by_contra hle'
  push Not at hle'
  have hmono := integral_pStar_anti μW hn (hcap β hβ).1 (hle'.trans (le_max_left a (M / 2)))
  rw [(hcap β hβ).2] at hmono
  have := (le_div_iff₀ (nat_cast_pos hn)).mp hmono
  linarith [hβc.2]

omit [IsFiniteMeasure μW] in
theorem tendsto_pStar_at_endpoint (hn : 2 ≤ n) (hM : 0 < M) {s : ℝ → ℝ} {l : Filter ℝ}
    (hs : Tendsto s l (𝓝 M)) : Tendsto (fun β => pStar n (s β) M) l (𝓝 0) := by
  have hL : Tendsto (fun β => logPlus (M / s β)) l (𝓝 (logPlus (M / M))) :=
    (continuous_logPlus.tendsto _).comp (tendsto_const_nhds.div hs hM.ne')
  rw [div_self hM.ne', logPlus_of_le_one le_rfl] at hL
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
    ((Real.continuous_exp.tendsto _).comp ((hL.div_const ((n : ℝ) - 1)).neg))
  simp only [zero_div, neg_zero, Real.exp_zero, sub_self] at h
  refine h.congr' ?_
  filter_upwards [hs.eventually (lt_mem_nhds hM)] with β hβ
  rw [pStar_eq_exp hn hβ]
  rfl

theorem sup_pStar_tendsto_zero (hn : 2 ≤ n) (hM : 0 < M) (hle : ∀ᵐ w ∂μW, w ≤ M)
    (hend : ∀ u > 0, 0 < μW (Ioi (M - u))) (hβ₀ : 0 < β₀)
    (hcap : ∀ β ∈ Ioo 0 β₀, 0 < t β ∧ ∫ w, pStar n (t β) w ∂μW = β / n) :
    ∀ ε > 0, ∀ᶠ β in 𝓝[>] (0 : ℝ), ∀ w ≤ M, pStar n (t β) w < ε := by
  intro ε hε
  have ht := tendsto_nhdsWithin_iff.1 (tendsto_root_endpoint μW hn hM hle hend hβ₀ hcap)
  have h0 := tendsto_pStar_at_endpoint hn hM ht.1
  filter_upwards [(tendsto_order.1 h0).2 ε hε, Ioo_mem_nhdsGT hβ₀] with β hβ hβd w hw
  exact lt_of_le_of_lt (pStar_mono_value hn (hcap β hβd).1 hw) hβ

theorem tendsto_coverage_div_capacity (hn : 2 ≤ n) (hM : 0 < M) (hle : ∀ᵐ w ∂μW, w ≤ M)
    (hend : ∀ u > 0, 0 < μW (Ioi (M - u))) (hβ₀ : 0 < β₀)
    (hcap : ∀ β ∈ Ioo 0 β₀, 0 < t β ∧ ∫ w, pStar n (t β) w ∂μW = β / n) :
    Tendsto (fun β => (∫ w, success n (pStar n (t β) w) ∂μW) / β) (𝓝[>] 0) (𝓝 1) := by
  have ht := tendsto_nhdsWithin_iff.1 (tendsto_root_endpoint μW hn hM hle hend hβ₀ hcap)
  have hδ := tendsto_pStar_at_endpoint hn hM ht.1
  have hlow : Tendsto (fun β => 1 - ((n : ℝ) - 1) * pStar n (t β) M) (𝓝[>] 0) (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (hδ.const_mul ((n : ℝ) - 1))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  all_goals filter_upwards [Ioo_mem_nhdsGT hβ₀] with β hβ
  all_goals
    obtain ⟨htβ, hcapβ⟩ := hcap β hβ
    have hn0 := nat_cast_pos hn
    have hn1 := nat_sub_one_pos hn
    have hIp := integrable_pStar μW hn htβ
    have hIS : Integrable (fun w => success n (pStar n (t β) w)) μW :=
      Integrable.mono' (integrable_const (1 : ℝ))
        ((continuous_success n).comp (continuous_pStar hn htβ)).aestronglyMeasurable
        (Eventually.of_forall (fun w => by
          rw [Real.norm_eq_abs]
          exact abs_success_pStar_le n htβ.le w))
    have hnp : ∫ w, (n : ℝ) * pStar n (t β) w ∂μW = β := by
      rw [integral_const_mul, hcapβ]
      field_simp
  · set δ := pStar n (t β) M
    have hbound : ∀ᵐ w ∂μW, (n : ℝ) * (1 - ((n : ℝ) - 1) * δ) * pStar n (t β) w ≤
        success n (pStar n (t β) w) := by
      filter_upwards [hle] with w hw
      have hp0 := pStar_nonneg n (t β) w
      have hp1 := pStar_le_one n htβ.le w
      have hpδ : pStar n (t β) w ≤ δ := pStar_mono_value hn htβ hw
      have h := nat_mul_le_success n hp0 hp1
      have : (n : ℝ) * pStar n (t β) w * (1 - ((n : ℝ) - 1) * δ) ≤
          (n : ℝ) * pStar n (t β) w * (1 - ((n : ℝ) - 1) * pStar n (t β) w) :=
        mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
      linarith
    have hint := integral_mono_ae (hIp.const_mul ((n : ℝ) * (1 - ((n : ℝ) - 1) * δ))) hIS hbound
    rw [integral_const_mul] at hint
    have hβpos := hβ.1
    rw [le_div_iff₀ hβpos]
    have : (n : ℝ) * (1 - ((n : ℝ) - 1) * δ) * ∫ w, pStar n (t β) w ∂μW =
        (1 - ((n : ℝ) - 1) * δ) * β := by
      rw [hcapβ]
      field_simp
    linarith
  · have hint := integral_mono hIS (hIp.const_mul (n : ℝ))
      (fun w => success_le_nat_mul n (pStar_le_one n htβ.le w))
    rw [hnp] at hint
    rw [div_le_one hβ.1]
    exact hint

theorem tendsto_multiplicity_one (hn : 2 ≤ n) (hM : 0 < M) (hle : ∀ᵐ w ∂μW, w ≤ M)
    (hend : ∀ u > 0, 0 < μW (Ioi (M - u))) (hβ₀ : 0 < β₀)
    (hcap : ∀ β ∈ Ioo 0 β₀, 0 < t β ∧ ∫ w, pStar n (t β) w ∂μW = β / n) :
    Tendsto (fun β => β / ∫ w, success n (pStar n (t β) w) ∂μW) (𝓝[>] 0) (𝓝 1) := by
  have h := (tendsto_coverage_div_capacity μW hn hM hle hend hβ₀ hcap).inv₀ one_ne_zero
  rw [inv_one] at h
  exact h.congr (fun β => inv_div _ _)

end Endpoint

theorem cor_tails_iii_bounded (μW : Measure ℝ) [IsFiniteMeasure μW] {n : ℕ} (hn : 2 ≤ n)
    (hbdd : ∃ B, ∀ᵐ w ∂μW, w ≤ B) (hpos : 0 < μW (Ioi 0)) {β₀ : ℝ} (hβ₀ : 0 < β₀)
    {t : ℝ → ℝ} (hcap : ∀ β ∈ Ioo 0 β₀, 0 < t β ∧ ∫ w, pStar n (t β) w ∂μW = β / n) :
    ∃ M, 0 < M ∧ (∀ᵐ w ∂μW, w ≤ M) ∧ (∀ u > 0, 0 < μW (Ioi (M - u))) ∧
      StrictAntiOn t (Ioo 0 β₀) ∧ Tendsto t (𝓝[>] 0) (𝓝[<] M) ∧
      (∀ ε > 0, ∀ᶠ β in 𝓝[>] (0 : ℝ), ∀ w ≤ M, pStar n (t β) w < ε) ∧
      Tendsto (fun β => (∫ w, success n (pStar n (t β) w) ∂μW) / β) (𝓝[>] 0) (𝓝 1) ∧
      Tendsto (fun β => β / ∫ w, success n (pStar n (t β) w) ∂μW) (𝓝[>] 0) (𝓝 1) := by
  obtain ⟨M, hM, hle, hend⟩ := exists_upper_endpoint μW hbdd hpos
  exact ⟨M, hM, hle, hend, root_strictAntiOn μW hn hcap,
    tendsto_root_endpoint μW hn hM hle hend hβ₀ hcap,
    sup_pStar_tendsto_zero μW hn hM hle hend hβ₀ hcap,
    tendsto_coverage_div_capacity μW hn hM hle hend hβ₀ hcap,
    tendsto_multiplicity_one μW hn hM hle hend hβ₀ hcap⟩

section Rate

theorem success_le_sub (n : ℕ) (hn : 1 ≤ n) {p : ℝ} (hp1 : p ≤ 1) :
    success n p ≤ n * p - ((n : ℝ) - 1) * p ^ 2 := by
  induction n, hn using Nat.le_induction with
  | base => simp [success]
  | succ n hn ih =>
    have hs : success (n + 1) p = p + (1 - p) * success n p := by
      unfold success
      ring
    rw [hs]
    push_cast
    have h1 := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hp1)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h2 : 0 ≤ ((n : ℝ) - 1) * p ^ 2 * (1 - p) :=
      mul_nonneg (mul_nonneg (sub_nonneg.mpr hn1) (sq_nonneg p)) (sub_nonneg.mpr hp1)
    nlinarith

theorem pStar_le_log_div {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 0 < t) (w : ℝ) :
    pStar n t w ≤ logPlus (w / t) / ((n : ℝ) - 1) := by
  rw [pStar_eq_exp hn ht]
  exact one_sub_exp_neg_le

theorem logPlus_div_le_gap {t w : ℝ} (ht : 0 < t) (htw : t < w) :
    logPlus (w / t) ≤ (w - t) / t := by
  rw [logPlus_of_one_le ((one_le_div ht).mpr htw.le)]
  have := Real.log_le_sub_one_of_pos (div_pos (ht.trans htw) ht)
  have h : w / t - 1 = (w - t) / t := by
    field_simp
  linarith

theorem gap_div_le_logPlus {t w : ℝ} (ht : 0 < t) (htw : t < w) :
    (w - t) / w ≤ logPlus (w / t) := by
  rw [logPlus_of_one_le ((one_le_div ht).mpr htw.le)]
  have := Real.one_sub_inv_le_log_of_pos (div_pos (ht.trans htw) ht)
  have hw0 : w ≠ 0 := (ht.trans htw).ne'
  have h : 1 - (w / t)⁻¹ = (w - t) / w := by
    field_simp
  linarith

theorem indicator_const_sq (s : Set ℝ) (c w : ℝ) :
    (s.indicator (fun _ => c) w) ^ 2 = s.indicator (fun _ => c ^ 2) w := by
  by_cases h : w ∈ s
  · simp [indicator_of_mem h]
  · simp [indicator_of_notMem h]

theorem pStar_le_near {n : ℕ} (hn : 2 ≤ n) {t M w : ℝ} (ht : 0 < t) (htM : t ≤ M)
    (hMt : M ≤ 2 * t) (hw : w ≤ M) :
    pStar n t w ≤ (Ioi t).indicator (fun _ => 2 * (M - t) / (M * ((n : ℝ) - 1))) w := by
  have hm := nat_sub_one_pos hn
  have hM : 0 < M := ht.trans_le htM
  by_cases htw : t < w
  · rw [indicator_of_mem (mem_Ioi.mpr htw)]
    calc pStar n t w ≤ logPlus (w / t) / ((n : ℝ) - 1) := pStar_le_log_div hn ht w
      _ ≤ ((w - t) / t) / ((n : ℝ) - 1) :=
          div_le_div_of_nonneg_right (logPlus_div_le_gap ht htw) hm.le
      _ ≤ 2 * (M - t) / (M * ((n : ℝ) - 1)) := by
          rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
          have h1 : (w - t) * M ≤ (M - t) * M := mul_le_mul_of_nonneg_right (by linarith) hM.le
          have h2 : (M - t) * M ≤ (M - t) * (2 * t) :=
            mul_le_mul_of_nonneg_left hMt (by linarith)
          have := mul_le_mul_of_nonneg_right (h1.trans h2) hm.le
          nlinarith
  · rw [indicator_of_notMem (by simpa using htw), pStar_eq_zero hn ht (not_lt.mp htw)]

theorem pStar_ge_near {n : ℕ} (hn : 2 ≤ n) {t M w : ℝ} (ht : 0 < t) (htM : t ≤ M)
    (hMt : M ≤ 2 * t) (hw : w ≤ M) :
    (Ioi (M - (M - t) / 2)).indicator (fun _ => (M - t) / (4 * M * ((n : ℝ) - 1))) w ≤
      pStar n t w := by
  have hm := nat_sub_one_pos hn
  have hm1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hM : 0 < M := ht.trans_le htM
  by_cases hmid : w ∈ Ioi (M - (M - t) / 2)
  · rw [indicator_of_mem hmid]
    have hmid' : M - (M - t) / 2 < w := hmid
    have htw : t < w := by linarith
    have hw0 : 0 < w := ht.trans htw
    set x := logPlus (w / t) / ((n : ℝ) - 1) with hxdef
    have hx0 : 0 ≤ x := div_nonneg (logPlus_nonneg _) hm.le
    have hx1 : x ≤ 1 := by
      have h1 : x ≤ ((w - t) / t) / ((n : ℝ) - 1) :=
        div_le_div_of_nonneg_right (logPlus_div_le_gap ht htw) hm.le
      have h2 : (w - t) / t ≤ 1 := by
        rw [div_le_one ht]
        linarith
      have h3 : ((w - t) / t) / ((n : ℝ) - 1) ≤ 1 := by
        rw [div_le_one hm]
        linarith
      linarith
    have hxlow : (M - t) / (2 * M * ((n : ℝ) - 1)) ≤ x := by
      have h1 : ((w - t) / w) / ((n : ℝ) - 1) ≤ x :=
        div_le_div_of_nonneg_right (gap_div_le_logPlus ht htw) hm.le
      have h2 : (M - t) / (2 * M * ((n : ℝ) - 1)) ≤ ((w - t) / w) / ((n : ℝ) - 1) := by
        rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        have h3 : (M - t) * w ≤ 2 * (w - t) * M := by nlinarith
        have := mul_le_mul_of_nonneg_right h3 hm.le
        nlinarith
      linarith
    have hp : x / 2 ≤ pStar n t w := by
      rw [pStar_eq_exp hn ht]
      have h1 := div_one_add_le_one_sub_exp_neg hx0
      have h2 : x / 2 ≤ x / (1 + x) := div_le_div_of_nonneg_left hx0 (by linarith) (by linarith)
      linarith
    have : (M - t) / (4 * M * ((n : ℝ) - 1)) = (M - t) / (2 * M * ((n : ℝ) - 1)) / 2 := by
      field_simp
      ring
    linarith
  · rw [indicator_of_notMem hmid]
    exact pStar_nonneg _ _ _

variable (μW : Measure ℝ) [IsFiniteMeasure μW]

theorem moment_bounds_near {n : ℕ} (hn : 2 ≤ n) {M : ℝ} (hle : ∀ᵐ w ∂μW, w ≤ M)
    {c₁ c₂ u₀ : ℝ}
    (htail : ∀ u ∈ Ioc 0 u₀, c₁ * u ≤ μW.real (Ioi (M - u)) ∧ μW.real (Ioi (M - u)) ≤ c₂ * u)
    {t : ℝ} (ht : 0 < t) (htM : t < M) (hMt : M ≤ 2 * t) (hdu : M - t ≤ u₀) :
    (∫ w, pStar n t w ∂μW) * (M * ((n : ℝ) - 1)) ≤ 2 * c₂ * (M - t) ^ 2 ∧
    c₁ * (M - t) ^ 2 ≤ 8 * (M * ((n : ℝ) - 1)) * ∫ w, pStar n t w ∂μW ∧
    (∫ w, pStar n t w ^ 2 ∂μW) * (M * ((n : ℝ) - 1)) ^ 2 ≤ 4 * c₂ * (M - t) ^ 3 ∧
    c₁ * (M - t) ^ 3 ≤ 32 * (M * ((n : ℝ) - 1)) ^ 2 * ∫ w, pStar n t w ^ 2 ∂μW := by
  have hm := nat_sub_one_pos hn
  have hM : 0 < M := ht.trans htM
  set d := M - t with hd
  have hd0 : 0 < d := by rw [hd]; linarith
  set K := M * ((n : ℝ) - 1) with hK
  have hK0 : 0 < K := by positivity
  have hIp := integrable_pStar μW hn ht
  have hIp2 : Integrable (fun w => pStar n t w ^ 2) μW :=
    Integrable.mono' (integrable_const (1 : ℝ))
      ((continuous_pStar hn ht).pow 2).aestronglyMeasurable
      (Eventually.of_forall (fun w => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_one₀ (pStar_nonneg n t w) (pStar_le_one n ht.le w)))
  have hTop := (htail d ⟨hd0, hdu⟩).2
  have hBot := (htail (d / 2) ⟨half_pos hd0, by linarith⟩).1
  have htd : t = M - d := by rw [hd]; ring
  have hIt : μW.real (Ioi t) ≤ c₂ * d := by rw [htd]; exact hTop
  have hmeas0 : 0 ≤ μW.real (Ioi (M - d / 2)) := measureReal_nonneg
  have hmeas1 : 0 ≤ μW.real (Ioi t) := measureReal_nonneg

  have hup := integral_mono_ae hIp ((integrable_const _).indicator measurableSet_Ioi)
    (hle.mono (fun w hw => pStar_le_near hn ht htM.le hMt hw))
  rw [integral_indicator_const _ measurableSet_Ioi, smul_eq_mul] at hup

  have hlow := integral_mono_ae ((integrable_const _).indicator measurableSet_Ioi) hIp
    (hle.mono (fun w hw => pStar_ge_near hn ht htM.le hMt hw))
  rw [integral_indicator_const _ measurableSet_Ioi, smul_eq_mul] at hlow

  have hup2 := integral_mono_ae hIp2 ((integrable_const _).indicator measurableSet_Ioi)
    (hle.mono (fun w hw => by
      have h := pow_le_pow_left₀ (pStar_nonneg n t w) (pStar_le_near hn ht htM.le hMt hw) 2
      rwa [indicator_const_sq] at h))
  rw [integral_indicator_const _ measurableSet_Ioi, smul_eq_mul] at hup2

  have hlow2 := integral_mono_ae ((integrable_const _).indicator measurableSet_Ioi) hIp2
    (hle.mono (fun w hw => by
      have h := pow_le_pow_left₀ (indicator_nonneg (fun _ _ => by positivity) w)
        (pStar_ge_near hn ht htM.le hMt hw) 2
      rwa [indicator_const_sq] at h))
  rw [integral_indicator_const _ measurableSet_Ioi, smul_eq_mul] at hlow2
  have hdK : 2 * (M - t) / K * K = 2 * d := by rw [← hd]; field_simp
  have hdK' : (M - t) / (4 * M * ((n : ℝ) - 1)) * K = d / 4 := by
    rw [← hd, hK]; field_simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_right hup hK0.le
    have h2 : μW.real (Ioi t) * (2 * (M - t) / K) * K = 2 * d * μW.real (Ioi t) := by
      rw [mul_assoc, hdK]; ring
    rw [h2] at this
    nlinarith
  · have := mul_le_mul_of_nonneg_right hlow hK0.le
    have h2 : μW.real (Ioi (M - (M - t) / 2)) * ((M - t) / (4 * M * ((n : ℝ) - 1))) * K =
        d / 4 * μW.real (Ioi (M - d / 2)) := by
      rw [mul_assoc, hdK', ← hd]; ring
    rw [h2] at this
    nlinarith
  · have := mul_le_mul_of_nonneg_right hup2 (sq_nonneg K)
    have h2 : μW.real (Ioi t) * (2 * (M - t) / K) ^ 2 * K ^ 2 = (2 * d) ^ 2 * μW.real (Ioi t) := by
      rw [mul_assoc, ← mul_pow, hdK]; ring
    rw [h2] at this
    nlinarith
  · have := mul_le_mul_of_nonneg_right hlow2 (sq_nonneg K)
    have h2 : μW.real (Ioi (M - (M - t) / 2)) * ((M - t) / (4 * M * ((n : ℝ) - 1))) ^ 2 * K ^ 2 =
        (d / 4) ^ 2 * μW.real (Ioi (M - d / 2)) := by
      rw [mul_assoc, ← mul_pow, hdK', ← hd]; ring
    rw [h2] at this
    nlinarith

theorem multiplicity_sub_one_theta_sqrt {n : ℕ} (hn : 2 ≤ n) {M : ℝ} (hM : 0 < M)
    (hle : ∀ᵐ w ∂μW, w ≤ M) {c₁ c₂ u₀ : ℝ} (hc₁ : 0 < c₁) (hu₀ : 0 < u₀)
    (htail : ∀ u ∈ Ioc 0 u₀, c₁ * u ≤ μW.real (Ioi (M - u)) ∧ μW.real (Ioi (M - u)) ≤ c₂ * u)
    {β₀ : ℝ} (hβ₀ : 0 < β₀) {t : ℝ → ℝ}
    (hcap : ∀ β ∈ Ioo 0 β₀, 0 < t β ∧ ∫ w, pStar n (t β) w ∂μW = β / n) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ᶠ β in 𝓝[>] (0 : ℝ),
      C₁ * Real.sqrt β ≤ β / (∫ w, success n (pStar n (t β) w) ∂μW) - 1 ∧
      β / (∫ w, success n (pStar n (t β) w) ∂μW) - 1 ≤ C₂ * Real.sqrt β := by
  have hm := nat_sub_one_pos hn
  have hn0 := nat_cast_pos hn
  have hc₂ : 0 < c₂ := by
    have h := htail u₀ ⟨hu₀, le_rfl⟩
    have h1 : c₁ * u₀ ≤ c₂ * u₀ := h.1.trans h.2
    by_contra hc
    push Not at hc
    nlinarith [mul_pos hc₁ hu₀]
  have hend : ∀ u > 0, 0 < μW (Ioi (M - u)) := by
    intro u hu
    have hv : min u u₀ ∈ Ioc 0 u₀ := ⟨lt_min hu hu₀, min_le_right _ _⟩
    have hreal : 0 < μW.real (Ioi (M - min u u₀)) :=
      lt_of_lt_of_le (mul_pos hc₁ hv.1) (htail _ hv).1
    have hsub : Ioi (M - min u u₀) ⊆ Ioi (M - u) :=
      Ioi_subset_Ioi (by linarith [min_le_left u u₀])
    rw [measureReal_def] at hreal
    exact lt_of_lt_of_le (ENNReal.toReal_pos_iff.mp hreal).1 (measure_mono hsub)
  set K := M * ((n : ℝ) - 1) with hKdef
  have hK : 0 < K := by positivity
  set L₁ := c₁ / (64 * M * n * c₂) with hL₁
  set U₁ := 64 * c₂ / (M * c₁) with hU₁
  have hL₁0 : 0 < L₁ := by positivity
  have hU₁0 : 0 < U₁ := by positivity
  set a₁ := K / (2 * n * c₂) with ha₁
  set b₁ := 8 * K / (n * c₁) with hb₁
  have ha₁0 : 0 < a₁ := by positivity
  have hb₁0 : 0 < b₁ := by positivity
  refine ⟨L₁ * Real.sqrt a₁, U₁ * Real.sqrt b₁, by positivity, by positivity, ?_⟩
  have ht := tendsto_nhdsWithin_iff.1 (tendsto_root_endpoint μW hn hM hle hend hβ₀ hcap)
  have hQ := tendsto_coverage_div_capacity μW hn hM hle hend hβ₀ hcap
  have hδ : 0 < min u₀ (M / 2) := lt_min hu₀ (half_pos hM)
  filter_upwards [Ioo_mem_nhdsGT hβ₀, (tendsto_order.1 ht.1).1 _ (sub_lt_self M hδ),
    (tendsto_order.1 hQ).1 (1 / 2) (by norm_num), ht.2] with β hβ hnear hhalf htlt
  obtain ⟨htβ, hcapβ⟩ := hcap β hβ
  have hβ0 : 0 < β := hβ.1
  have htlt' : t β < M := htlt
  set d := M - t β with hd
  have hd0 : 0 < d := by rw [hd]; linarith
  have hdδ : d ≤ min u₀ (M / 2) := by rw [hd]; linarith
  have hdu : M - t β ≤ u₀ := le_trans hdδ (min_le_left _ _)
  have hMt : M ≤ 2 * t β := by
    have := le_trans hdδ (min_le_right _ _)
    rw [hd] at this
    linarith
  obtain ⟨A1, A2, A3, A4⟩ := moment_bounds_near μW hn hle htail htβ htlt' hMt hdu
  rw [← hd, ← hKdef] at A1 A2 A3 A4
  set P1 := ∫ w, pStar n (t β) w ∂μW with hP1
  set P2 := ∫ w, pStar n (t β) w ^ 2 ∂μW with hP2
  set Q := ∫ w, success n (pStar n (t β) w) ∂μW with hQdef
  have hIp := integrable_pStar μW hn htβ
  have hIp2 : Integrable (fun w => pStar n (t β) w ^ 2) μW :=
    Integrable.mono' (integrable_const (1 : ℝ))
      ((continuous_pStar hn htβ).pow 2).aestronglyMeasurable
      (Eventually.of_forall (fun w => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_one₀ (pStar_nonneg n _ w) (pStar_le_one n htβ.le w)))
  have hIS : Integrable (fun w => success n (pStar n (t β) w)) μW :=
    Integrable.mono' (integrable_const (1 : ℝ))
      ((continuous_success n).comp (continuous_pStar hn htβ)).aestronglyMeasurable
      (Eventually.of_forall (fun w => by
        rw [Real.norm_eq_abs]
        exact abs_success_pStar_le n htβ.le w))
  have hcap' : (n : ℝ) * P1 = β := by
    rw [hcapβ]
    field_simp

  have B1 : β - Q ≤ (n : ℝ) * ((n : ℝ) - 1) * P2 := by
    have hI1 : Integrable (fun w => (n : ℝ) * pStar n (t β) w -
        (n : ℝ) * ((n : ℝ) - 1) * pStar n (t β) w ^ 2) μW :=
      (hIp.const_mul _).sub (hIp2.const_mul _)
    have h := integral_mono hI1 hIS (fun w => by
        have := nat_mul_le_success n (pStar_nonneg n _ w) (pStar_le_one n htβ.le w)
        change (n : ℝ) * pStar n (t β) w - (n : ℝ) * ((n : ℝ) - 1) * pStar n (t β) w ^ 2 ≤ _
        nlinarith)
    rw [integral_sub (hIp.const_mul _) (hIp2.const_mul _), integral_const_mul,
      integral_const_mul] at h
    rw [← hP1, ← hP2, hcap'] at h
    linarith

  have B2 : ((n : ℝ) - 1) * P2 ≤ β - Q := by
    have hI2 : Integrable (fun w => (n : ℝ) * pStar n (t β) w -
        ((n : ℝ) - 1) * pStar n (t β) w ^ 2) μW :=
      (hIp.const_mul _).sub (hIp2.const_mul _)
    have h := integral_mono hIS hI2
      (fun w => success_le_sub n (by omega) (pStar_le_one n htβ.le w))
    rw [integral_sub (hIp.const_mul _) (hIp2.const_mul _), integral_const_mul,
      integral_const_mul] at h
    rw [← hP1, ← hP2, hcap'] at h
    linarith
  have hP2nn : 0 ≤ P2 := integral_nonneg (fun w => sq_nonneg _)
  clear_value P1 P2 Q d K L₁ U₁ a₁ b₁
  have hmP2 : 0 ≤ ((n : ℝ) - 1) * P2 := mul_nonneg hm.le hP2nn
  have hQle : Q ≤ β := by linarith
  have hQhalf : β / 2 < Q := by
    have := (lt_div_iff₀ hβ0).mp hhalf
    linarith
  have hQ0 : 0 < Q := by linarith

  have hβK : β * K ≤ 2 * n * c₂ * d ^ 2 := by
    have h := mul_le_mul_of_nonneg_left A1 hn0.le
    calc β * K = (n : ℝ) * (P1 * K) := by rw [← hcap']; ring
      _ ≤ (n : ℝ) * (2 * c₂ * d ^ 2) := h
      _ = 2 * n * c₂ * d ^ 2 := by ring
  have hβK' : (n : ℝ) * c₁ * d ^ 2 ≤ 8 * K * β := by
    have h := mul_le_mul_of_nonneg_left A2 hn0.le
    calc (n : ℝ) * c₁ * d ^ 2 = (n : ℝ) * (c₁ * d ^ 2) := by ring
      _ ≤ (n : ℝ) * (8 * K * P1) := h
      _ = 8 * K * β := by rw [← hcap']; ring
  have hd2low : a₁ * β ≤ d ^ 2 := by
    rw [ha₁, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    linarith
  have hd2up : d ^ 2 ≤ b₁ * β := by
    rw [hb₁, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    linarith
  have hmu : β / Q - 1 = (β - Q) / Q := by
    field_simp

  have hlow : L₁ * d ≤ β / Q - 1 := by
    rw [hmu]
    have h1 : (β - Q) / β ≤ (β - Q) / Q :=
      div_le_div_of_nonneg_left (by linarith) hQ0 hQle
    refine le_trans ?_ h1
    rw [le_div_iff₀ hβ0]
    have h2 := mul_le_mul_of_nonneg_left hβK (by positivity : (0 : ℝ) ≤ c₁ * d)
    have h3 := mul_le_mul_of_nonneg_left A4 (by positivity : (0 : ℝ) ≤ 2 * n * c₂)
    have key : c₁ * d * β * K ≤ 64 * n * c₂ * K * P2 * K := by
      have e1 : c₁ * d * (β * K) = c₁ * d * β * K := by ring
      have e2 : c₁ * d * (2 * n * c₂ * d ^ 2) = 2 * n * c₂ * (c₁ * d ^ 3) := by ring
      have e3 : 2 * n * c₂ * (32 * K ^ 2 * P2) = 64 * n * c₂ * K * P2 * K := by ring
      linarith
    have key' : c₁ * d * β ≤ 64 * n * c₂ * K * P2 := le_of_mul_le_mul_right key hK
    have h4 := mul_le_mul_of_nonneg_left B2 (by positivity : (0 : ℝ) ≤ 64 * M * n * c₂)
    have e4 : 64 * n * c₂ * K * P2 = 64 * M * n * c₂ * (((n : ℝ) - 1) * P2) := by
      rw [hKdef]
      ring
    have e5 : L₁ * d * β = (c₁ * d * β) / (64 * M * n * c₂) := by
      rw [hL₁]
      ring
    rw [e5, div_le_iff₀ (by positivity)]
    linarith

  have hup : β / Q - 1 ≤ U₁ * d := by
    rw [hmu]
    have h1 : (β - Q) / Q ≤ (β - Q) / (β / 2) :=
      div_le_div_of_nonneg_left (by linarith) (by positivity) hQhalf.le
    refine le_trans h1 ?_
    rw [div_le_iff₀ (by positivity)]
    have h2 := mul_le_mul_of_nonneg_left A3 (by positivity : (0 : ℝ) ≤ 2 * n * c₁)
    have h3 := mul_le_mul_of_nonneg_left hβK' (by positivity : (0 : ℝ) ≤ 4 * c₂ * d)
    have h5 := mul_le_mul_of_nonneg_left B1 (by positivity : (0 : ℝ) ≤ M * c₁)

    have key : M * c₁ * (β - Q) * K ≤ 32 * c₂ * d * β * K := by
      have e1 : M * c₁ * ((n : ℝ) * ((n : ℝ) - 1) * P2) * K =
          2 * n * c₁ * (P2 * K ^ 2) / 2 := by
        rw [hKdef]
        ring
      have e2 : 2 * n * c₁ * (4 * c₂ * d ^ 3) = 2 * (4 * c₂ * d * ((n : ℝ) * c₁ * d ^ 2)) := by
        ring
      have e3 : 4 * c₂ * d * (8 * K * β) = 32 * c₂ * d * β * K := by ring
      have h6 := mul_le_mul_of_nonneg_right h5 hK.le
      linarith
    have key' := le_of_mul_le_mul_right key hK
    have e6 : U₁ * d * (β / 2) = (32 * c₂ * d * β) / (M * c₁) := by
      rw [hU₁]
      ring
    rw [e6, le_div_iff₀ (by positivity)]
    linarith
  constructor
  · calc L₁ * Real.sqrt a₁ * Real.sqrt β = L₁ * Real.sqrt (a₁ * β) := by
          rw [Real.sqrt_mul ha₁0.le]
          ring
      _ ≤ L₁ * d := by
          apply mul_le_mul_of_nonneg_left _ hL₁0.le
          calc Real.sqrt (a₁ * β) ≤ Real.sqrt (d ^ 2) := Real.sqrt_le_sqrt hd2low
            _ = d := Real.sqrt_sq hd0.le
      _ ≤ β / Q - 1 := hlow
  · calc β / Q - 1 ≤ U₁ * d := hup
      _ ≤ U₁ * Real.sqrt (b₁ * β) := by
          apply mul_le_mul_of_nonneg_left _ hU₁0.le
          calc d = Real.sqrt (d ^ 2) := (Real.sqrt_sq hd0.le).symm
            _ ≤ Real.sqrt (b₁ * β) := Real.sqrt_le_sqrt hd2up
      _ = U₁ * Real.sqrt b₁ * Real.sqrt β := by
          rw [Real.sqrt_mul hb₁0.le]
          ring

omit [IsFiniteMeasure μW] in

theorem linear_tail_of_density {M u₀ : ℝ} {f : ℝ → ℝ} (hu₀ : 0 < u₀)
    (hf : ContinuousOn f (Icc (M - u₀) M)) (hfM : 0 < f M)
    (hdens : ∀ u ∈ Ioc 0 u₀, μW.real (Ioi (M - u)) = ∫ x in (M - u)..M, f x) :
    ∃ u₁ > 0, ∀ u ∈ Ioc 0 u₁, f M / 2 * u ≤ μW.real (Ioi (M - u)) ∧
      μW.real (Ioi (M - u)) ≤ 2 * f M * u := by
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.mp
    (hf M ⟨by linarith, le_rfl⟩) (f M / 2) (half_pos hfM)
  refine ⟨min u₀ (δ / 2), lt_min hu₀ (half_pos hδ), fun u hu => ?_⟩
  have hu0 : 0 < u := hu.1
  have huu₀ : u ≤ u₀ := hu.2.trans (min_le_left _ _)
  have huδ : u ≤ δ / 2 := hu.2.trans (min_le_right _ _)
  have hsub : Icc (M - u) M ⊆ Icc (M - u₀) M := Icc_subset_Icc (by linarith) le_rfl
  have hfu : ∀ x ∈ Icc (M - u) M, f M / 2 ≤ f x ∧ f x ≤ 2 * f M := by
    intro x hx
    have hd : dist x M < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hx.1, hx.2]
    have h := hball (hsub hx) hd
    rw [Real.dist_eq, abs_lt] at h
    constructor <;> linarith [h.1, h.2]
  have hle : M - u ≤ M := by linarith
  have hint : IntervalIntegrable f volume (M - u) M :=
    (hf.mono hsub).intervalIntegrable_of_Icc hle
  rw [hdens u ⟨hu0, huu₀⟩]
  constructor
  · have h := intervalIntegral.integral_mono_on hle intervalIntegrable_const hint
      (fun x hx => (hfu x hx).1)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    linarith
  · have h := intervalIntegral.integral_mono_on hle hint intervalIntegrable_const
      (fun x hx => (hfu x hx).2)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    linarith

theorem multiplicity_sub_one_theta_sqrt_of_density {n : ℕ} (hn : 2 ≤ n) {M : ℝ}
    (hM : 0 < M) (hle : ∀ᵐ w ∂μW, w ≤ M) {u₀ : ℝ} {f : ℝ → ℝ} (hu₀ : 0 < u₀)
    (hf : ContinuousOn f (Icc (M - u₀) M)) (hfM : 0 < f M)
    (hdens : ∀ u ∈ Ioc 0 u₀, μW.real (Ioi (M - u)) = ∫ x in (M - u)..M, f x)
    {β₀ : ℝ} (hβ₀ : 0 < β₀) {t : ℝ → ℝ}
    (hcap : ∀ β ∈ Ioo 0 β₀, 0 < t β ∧ ∫ w, pStar n (t β) w ∂μW = β / n) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ᶠ β in 𝓝[>] (0 : ℝ),
      C₁ * Real.sqrt β ≤ β / (∫ w, success n (pStar n (t β) w) ∂μW) - 1 ∧
      β / (∫ w, success n (pStar n (t β) w) ∂μW) - 1 ≤ C₂ * Real.sqrt β := by
  obtain ⟨u₁, hu₁, htail⟩ := linear_tail_of_density μW hu₀ hf hfM hdens
  exact multiplicity_sub_one_theta_sqrt μW hn hM hle (half_pos hfM) hu₁ htail hβ₀ hcap

end Rate

end BoundedEndpoint
end PayOnce
end FCAppendix
