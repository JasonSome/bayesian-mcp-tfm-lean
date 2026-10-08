import FCAppendix.Ample.Deficit
import FCAppendix.Game.Bayesian

noncomputable section
namespace FCAppendix.Ample
open Filter Set Topology

def populationLogRate (M : ℕ) (p : ℝ) : ℝ := -Real.log p / (M : ℝ)

theorem populationLogRate_mul (M : ℕ) {a p : ℝ} (ha : 0 < a) (hp : 0 < p) :
    populationLogRate M (a * p) =
      populationLogRate M p - Real.log a / (M : ℝ) := by
  unfold populationLogRate
  rw [Real.log_mul ha.ne' hp.ne']
  ring

theorem populationLogRate_anti {M : ℕ} (hM : 0 < M) {p q : ℝ}
    (hp : 0 < p) (hpq : p ≤ q) :
    populationLogRate M q ≤ populationLogRate M p := by
  exact div_le_div_of_nonneg_right (neg_le_neg (Real.log_le_log hp hpq))
    (Nat.cast_pos.mpr hM).le

theorem populationLogRate_tendsto_of_comparable
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (f r : ℕ → ℝ) {A B J : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hcmp : ∀ᶠ m in atTop, 0 < r m ∧ A * r m ≤ f m ∧ f m ≤ B * r m)
    (hr : Tendsto (fun m => populationLogRate (M m) (r m)) atTop (𝓝 J)) :
    Tendsto (fun m => populationLogRate (M m) (f m)) atTop (𝓝 J) := by
  have hi : Tendsto (fun m => (M m : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hM)
  have hc (x : ℝ) : Tendsto (fun m => x / (M m : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hi.const_mul x
  have hlo : Tendsto (fun m => populationLogRate (M m) (r m) -
      Real.log B / (M m : ℝ)) atTop (𝓝 J) := by
    simpa only [sub_zero] using hr.sub (hc (Real.log B))
  have hup : Tendsto (fun m => populationLogRate (M m) (r m) -
      Real.log A / (M m : ℝ)) atTop (𝓝 J) := by
    simpa only [sub_zero] using hr.sub (hc (Real.log A))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup
  · filter_upwards [hcmp, hM.eventually_gt_atTop 0] with m hm hm0
    have hf := (mul_pos hA hm.1).trans_le hm.2.1
    simpa only [populationLogRate_mul (M m) hB hm.1] using
      populationLogRate_anti hm0 hf hm.2.2
  · filter_upwards [hcmp, hM.eventually_gt_atTop 0] with m hm hm0
    simpa only [populationLogRate_mul (M m) hA hm.1] using
      populationLogRate_anti hm0 (mul_pos hA hm.1) hm.2.1

theorem deficit_logRate_tendsto {n : ℕ}
    (P : ℕ → Interim.Problem n) (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    {z w J : ℝ} (hz : 0 < z) (hw : 0 < w)
    (hzpos : ∀ᶠ m in atTop, 0 < deficit (P m) z)
    (hzrate : Tendsto (fun m => populationLogRate (M m) (deficit (P m) z))
      atTop (𝓝 J)) :
    Tendsto (fun m => populationLogRate (M m) (deficit (P m) w))
      atTop (𝓝 J) := by
  apply populationLogRate_tendsto_of_comparable M hM
    (fun m => deficit (P m) w) (fun m => deficit (P m) z)
    (A := min 1 (w / z)) (B := max 1 (w / z))
    (lt_min (by norm_num) (div_pos hw hz))
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _))
    _ hzrate
  filter_upwards [hzpos] with m hm
  exact ⟨hm, deficit_ratio_bounds (P m) w z hw hz⟩

theorem deficit_touching {n : ℕ} (P : Interim.Problem n)
    (t x : ℝ) (act : Game.JointAction n)
    (ha : P.BestResponse (t + P.g) act) :
    deficit P x ≤ deficit P t + (x - t) * (1 - (P.outcome act).success) := by
  have hh := P.supporting_line (t + P.g) act ha (x + P.g)
  unfold deficit
  nlinarith

theorem deficit_oscillation_le {n : ℕ} (P : Interim.Problem n)
    {t lo hi w z : ℝ} (ht : t ≤ lo) (hw : w ∈ Icc lo hi) (hz : z ∈ Icc lo hi)
    (act : Game.JointAction n) (ha : P.BestResponse (t + P.g) act) :
    |deficit P w - deficit P z| ≤ (hi - t) * (1 - (P.outcome act).success) := by
  have hd : 0 ≤ 1 - (P.outcome act).success :=
    sub_nonneg.mpr (P.outcome act).success_le_one
  have htw : t ≤ w := ht.trans hw.1
  have htz : t ≤ z := ht.trans hz.1
  have hlw := deficit_monotone P htw
  have hlz := deficit_monotone P htz
  have huw := deficit_touching P t w act ha
  have huz := deficit_touching P t z act ha
  have hmw := mul_le_mul_of_nonneg_right
    (show w - t ≤ hi - t by linarith [hw.2]) hd
  have hmz := mul_le_mul_of_nonneg_right
    (show z - t ≤ hi - t by linarith [hz.2]) hd
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem deficit_flat_uniform_of_witness {n : ℕ}
    (P : ℕ → Interim.Problem n) (C t : ℕ → ℝ)
    (act : ℕ → Game.JointAction n) {lo hi z : ℝ}
    (hz : z ∈ Icc lo hi)
    (hC : ∀ᶠ m in atTop, 0 < C m)
    (hscale : ∀ m, C m = deficit (P m) z)
    (ht : ∀ᶠ m in atTop, 0 ≤ t m ∧ t m ≤ lo)
    (hbr : ∀ᶠ m in atTop, (P m).BestResponse (t m + (P m).g) (act m))
    (hsmall : Tendsto (fun m => (1 - ((P m).outcome (act m)).success) / C m)
      atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ m in atTop, ∀ w ∈ Icc lo hi,
      |deficit (P m) w / C m - 1| < ε := by
  intro ε hε
  have hlim : Tendsto (fun m => max hi 0 *
      ((1 - ((P m).outcome (act m)).success) / C m)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hsmall.const_mul (max hi 0)
  filter_upwards [hC, ht, hbr, (tendsto_order.mp hlim).2 ε hε]
    with m hmC hmt hmbr hme
  intro w hw
  have hosc := deficit_oscillation_le (P m) hmt.2 hw hz (act m) hmbr
  have hden : 0 ≤ (1 - ((P m).outcome (act m)).success) / C m :=
    div_nonneg (sub_nonneg.mpr (CountLaw.success_le_one _)) hmC.le
  have hbound :
      |deficit (P m) w / C m - 1| ≤
        max hi 0 * ((1 - ((P m).outcome (act m)).success) / C m) := by
    rw [show deficit (P m) w / C m - 1 =
        (deficit (P m) w - deficit (P m) z) / C m by
          rw [← hscale m]; field_simp [hmC.ne'], abs_div, abs_of_pos hmC]
    calc
      _ ≤ ((hi - t m) * (1 - ((P m).outcome (act m)).success)) / C m :=
        div_le_div_of_nonneg_right hosc hmC.le
      _ = (hi - t m) * ((1 - ((P m).outcome (act m)).success) / C m) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by have hh := le_max_left hi 0; linarith [hmt.1]) hden
  exact hbound.trans_lt hme

end FCAppendix.Ample
