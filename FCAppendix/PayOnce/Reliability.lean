import FCAppendix.PayOnce.LimitFormulas
import FCAppendix.Probability.BinomialTails

namespace FCAppendix
namespace PayOnce
namespace Limit

open MeasureTheory Set IndependentCounts

section Binomial

theorem binomial_none (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (binomial n p hp0 hp1).prob (fun r => r.val = 0) = (1 - p) ^ n := by
  classical
  induction n with
  | zero => simp [binomial, independentCount, FiniteLaw.prob]
  | succ n ih =>
    rw [FiniteLaw.prob_eq_expect, expect_binomial_succ]
    have hf : ∀ r : Fin (n + 1),
        (if (addCount n false r).val = 0 then (1 : ℝ) else 0) =
          if r.val = 0 then 1 else 0 := by
      intro r
      simp only [val_add_false]
    have ht : ∀ r : Fin (n + 1),
        (if (addCount n true r).val = 0 then (1 : ℝ) else 0) = 0 := by
      intro r
      simp only [val_add_true]
      rw [if_neg (by omega)]
    simp_rw [hf, ht]
    rw [FiniteLaw.expect_zero, ← FiniteLaw.prob_eq_expect, ih, pow_succ]
    ring

theorem binomial_single (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (binomial n p hp0 hp1).prob (fun r => r.val = 1) = n * p * (1 - p) ^ (n - 1) := by
  classical
  induction n with
  | zero => simp [binomial, independentCount, FiniteLaw.prob]
  | succ n ih =>
    rw [FiniteLaw.prob_eq_expect, expect_binomial_succ]
    have hf : ∀ r : Fin (n + 1),
        (if (addCount n false r).val = 1 then (1 : ℝ) else 0) =
          if r.val = 1 then 1 else 0 := by
      intro r
      simp only [val_add_false]
    have ht : ∀ r : Fin (n + 1),
        (if (addCount n true r).val = 1 then (1 : ℝ) else 0) =
          if r.val = 0 then 1 else 0 := by
      intro r
      simp only [val_add_true]
      by_cases h : r.val = 0
      · rw [if_pos (by omega), if_pos h]
      · rw [if_neg (by omega), if_neg h]
    simp_rw [hf, ht]
    rw [← FiniteLaw.prob_eq_expect, ← FiniteLaw.prob_eq_expect, ih, binomial_none]
    cases n with
    | zero => simp
    | succ m =>
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
      ring

theorem binomial_atLeastOne (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (binomial n p hp0 hp1).prob (fun r => 1 ≤ r.val) = success n p := by
  have he : (fun r : Fin (n + 1) => 1 ≤ r.val) = (fun r => ¬ r.val = 0) := by
    funext r
    exact propext Nat.one_le_iff_ne_zero
  rw [he, FiniteLaw.prob_compl, binomial_none]
  rfl

theorem binomial_atLeastTwo (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (binomial n p hp0 hp1).prob (fun r => 2 ≤ r.val) =
      success n p - n * p * (1 - p) ^ (n - 1) := by
  classical
  rw [← binomial_atLeastOne n p hp0 hp1, ← binomial_single n p hp0 hp1,
    FiniteLaw.prob_eq_expect, FiniteLaw.prob_eq_expect, FiniteLaw.prob_eq_expect,
    ← FiniteLaw.expect_sub]
  apply FiniteLaw.expect_congr
  intro r
  split_ifs <;> norm_num <;> omega

theorem binomial_duplicate_given_included (n : ℕ) (hn : 0 < n) (p : ℝ) (hp0 : 0 < p)
    (hp1 : p ≤ 1) :
    (binomial n p hp0.le hp1).prob (fun r => 2 ≤ r.val) /
        (binomial n p hp0.le hp1).prob (fun r => 1 ≤ r.val) =
      1 - n * p * (1 - p) ^ (n - 1) / success n p := by
  have hS := success_pos n hn p hp0 hp1
  rw [binomial_atLeastTwo, binomial_atLeastOne]
  field_simp

end Binomial

section Reliability

variable {n : ℕ} {ε : ℝ}

noncomputable def reliabilityMarginal (n : ℕ) (ε : ℝ) : ℝ := 1 - ε ^ (1 / (n : ℝ))

theorem root_nonneg (hε0 : 0 ≤ ε) : 0 ≤ ε ^ (1 / (n : ℝ)) := Real.rpow_nonneg hε0 _

theorem root_le_one (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) : ε ^ (1 / (n : ℝ)) ≤ 1 :=
  Real.rpow_le_one hε0 hε1 (by positivity)

theorem reliabilityMarginal_nonneg (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    0 ≤ reliabilityMarginal n ε := sub_nonneg.mpr (root_le_one hε0 hε1)

theorem reliabilityMarginal_le_one (hε0 : 0 ≤ ε) : reliabilityMarginal n ε ≤ 1 := by
  unfold reliabilityMarginal
  linarith [root_nonneg (n := n) hε0]

theorem reliabilityMarginal_pos (hn : 0 < n) (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    0 < reliabilityMarginal n ε := by
  unfold reliabilityMarginal
  have := Real.rpow_lt_one hε0 hε1 (show 0 < 1 / (n : ℝ) by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity)
  linarith

theorem failure_reliabilityMarginal (hn : 0 < n) (hε0 : 0 ≤ ε) :
    (1 - reliabilityMarginal n ε) ^ n = ε := by
  unfold reliabilityMarginal
  rw [sub_sub_cancel, one_div]
  exact Real.rpow_inv_natCast_pow hε0 (Nat.pos_iff_ne_zero.mp hn)

theorem eq_reliabilityMarginal (hn : 0 < n) {p : ℝ} (hp1 : p ≤ 1) :
    p = reliabilityMarginal n ((1 - p) ^ n) := by
  unfold reliabilityMarginal
  rw [one_div, Real.pow_rpow_inv_natCast (sub_nonneg.mpr hp1) (Nat.pos_iff_ne_zero.mp hn)]
  ring

theorem pStar_eq_reliabilityMarginal (hn : 2 ≤ n) {t w : ℝ} (ht : 0 ≤ t) (htw : t < w) :
    pStar n t w = reliabilityMarginal n ((t / w) ^ ((n : ℝ) / ((n : ℝ) - 1))) := by
  rw [← failure_eq hn ht htw]
  exact eq_reliabilityMarginal (by omega) (pStar_le_one ht)

theorem success_reliabilityMarginal (hn : 0 < n) (hε0 : 0 ≤ ε) :
    success n (reliabilityMarginal n ε) = 1 - ε := by
  unfold success
  rw [failure_reliabilityMarginal hn hε0]

theorem failure_pred_reliabilityMarginal (hn : 0 < n) (hε0 : 0 ≤ ε) :
    (1 - reliabilityMarginal n ε) ^ (n - 1) = ε ^ (((n : ℝ) - 1) / n) := by
  unfold reliabilityMarginal
  rw [sub_sub_cancel, ← Real.rpow_mul_natCast hε0, Nat.cast_sub (by omega), Nat.cast_one]
  congr 1
  ring

theorem reliability_load (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (binomial n (reliabilityMarginal n ε) (reliabilityMarginal_nonneg hε0 hε1)
      (reliabilityMarginal_le_one hε0)).load = n * (1 - ε ^ (1 / (n : ℝ))) := by
  rw [binomial_load]
  rfl

theorem reliability_success (hn : 0 < n) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (binomial n (reliabilityMarginal n ε) (reliabilityMarginal_nonneg hε0 hε1)
      (reliabilityMarginal_le_one hε0)).success = 1 - ε := by
  rw [binomial_success]
  exact success_reliabilityMarginal hn hε0

theorem reliability_multiplicity (hn : 0 < n) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    conditionalMultiplicity
      (binomial n (reliabilityMarginal n ε) (reliabilityMarginal_nonneg hε0 hε1)
        (reliabilityMarginal_le_one hε0)).success
      (binomial n (reliabilityMarginal n ε) (reliabilityMarginal_nonneg hε0 hε1)
        (reliabilityMarginal_le_one hε0)).load =
      n * (1 - ε ^ (1 / (n : ℝ))) / (1 - ε) := by
  unfold conditionalMultiplicity
  rw [reliability_load hε0 hε1, reliability_success hn hε0 hε1]

theorem reliability_duplicate_given_included (hn : 0 < n) (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    (binomial n (reliabilityMarginal n ε) (reliabilityMarginal_nonneg hε0 hε1.le)
        (reliabilityMarginal_le_one hε0)).prob (fun r => 2 ≤ r.val) /
      (binomial n (reliabilityMarginal n ε) (reliabilityMarginal_nonneg hε0 hε1.le)
        (reliabilityMarginal_le_one hε0)).prob (fun r => 1 ≤ r.val) =
      1 - n * (1 - ε ^ (1 / (n : ℝ))) * ε ^ (((n : ℝ) - 1) / n) / (1 - ε) := by
  have h := binomial_duplicate_given_included n hn (reliabilityMarginal n ε)
    (reliabilityMarginal_pos hn hε0 hε1) (reliabilityMarginal_le_one hε0)
  rw [h, failure_pred_reliabilityMarginal hn hε0, success_reliabilityMarginal hn hε0]
  rfl

end Reliability

section Monotone

variable {n : ℕ} {t : ℝ}

theorem copies_mono_value (hn : 2 ≤ n) (ht : 0 ≤ t) :
    Monotone (fun w => (n : ℝ) * pStar n t w) :=
  fun _ _ h => mul_le_mul_of_nonneg_left (pStar_mono_value hn ht h) (Nat.cast_nonneg n)

theorem copies_strictMonoOn_value (hn : 2 ≤ n) (ht : 0 < t) :
    StrictMonoOn (fun w => (n : ℝ) * pStar n t w) (Ioi t) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact fun _ ha _ hb h => mul_lt_mul_of_pos_left (pStar_strictMonoOn_value hn ht ha hb h) hnR

theorem multiplicity_strictMonoOn_value (hn : 2 ≤ n) (ht : 0 < t) :
    StrictMonoOn (fun w => (n : ℝ) * pStar n t w / success n (pStar n t w)) (Ioi t) := by
  intro w₁ hw₁ w₂ hw₂ h
  exact multiplicity_strict n hn _ _ ((pStar_pos_iff hn ht.le).mpr hw₁)
    (pStar_strictMonoOn_value hn ht hw₁ hw₂ h) (pStar_le_one ht.le)

theorem failure_ge_of_le_bound (hn : 2 ≤ n) (ht : 0 < t) {w M : ℝ} (htw : t < w)
    (hwM : w ≤ M) :
    0 < (t / M) ^ ((n : ℝ) / ((n : ℝ) - 1)) ∧
      (t / M) ^ ((n : ℝ) / ((n : ℝ) - 1)) ≤ (1 - pStar n t w) ^ n := by
  have hw : 0 < w := lt_trans ht htw
  have hM : 0 < M := lt_of_lt_of_le hw hwM
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨Real.rpow_pos_of_pos (div_pos ht hM) _, ?_⟩
  rw [failure_eq hn ht.le htw]
  exact Real.rpow_le_rpow (div_nonneg ht.le hM.le) (div_le_div_of_nonneg_left ht.le hw hwM)
    (div_nonneg (by linarith) (by linarith))

theorem ae_failure_ge_of_bounded (μW : Measure ℝ) (hn : 2 ≤ n) (ht : 0 < t) {M : ℝ}
    (hM : μW (Ioi M) = 0) :
    ∀ᵐ w ∂μW, t < w → 0 < (t / M) ^ ((n : ℝ) / ((n : ℝ) - 1)) ∧
      (t / M) ^ ((n : ℝ) / ((n : ℝ) - 1)) ≤ (1 - pStar n t w) ^ n := by
  have hle : ∀ᵐ w ∂μW, w ≤ M := by
    rw [ae_iff]
    simpa only [not_le, Set.Ioi] using hM
  filter_upwards [hle] with w hw htw
  exact failure_ge_of_le_bound hn ht htw hw

end Monotone

end Limit
end PayOnce
end FCAppendix
