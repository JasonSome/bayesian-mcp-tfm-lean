import FCAppendix.Exclusive.NarrowKernel
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace FCAppendix.Exclusive.Narrow
open MeasureTheory Set Filter Topology

noncomputable def meanExposure (n : ℕ) (D : ℝ) (beta : ℝ → ℝ) (v : ℝ) : ℝ :=
  1 - D * inverseBid n (beta v)

theorem inverseBid_natPower (d : ℕ) (hd : 1 ≤ d) {b : ℝ} (hb : 0 < b) :
    inverseBid (d + 1) b ^ d = b⁻¹ := by
  have he : (-rate (d + 1)) * (d : ℝ) = -1 := by
    have hr := rate_mul (d + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hr
    nlinarith
  rw [inverseBid, ← Real.rpow_natCast, ← Real.rpow_mul hb.le, he, Real.rpow_neg_one]

theorem inverse_mean_bounds {μ : Measure ℝ} [IsFiniteMeasure μ]
    (n : ℕ) (hn : 2 ≤ n) {h a B : ℝ} (hh : 0 < h)
    (hmass : μ.real Set.univ = h) (ha : 0 < a) (haB : a ≤ B)
    (beta : ℝ → ℝ) (hbeta : Measurable beta)
    (hband : ∀ᵐ v ∂μ, beta v ∈ Icc a B) :
    Integrable (fun v => inverseBid n (beta v)) μ ∧
      (∫ v, inverseBid n (beta v) ∂μ) ∈ Icc (h * inverseBid n B) (h * inverseBid n a) ∧
      0 < ∫ v, inverseBid n (beta v) ∂μ := by
  have hm : Measurable (fun v => inverseBid n (beta v)) := hbeta.pow_const (-rate n)
  have hb : ∀ᵐ v ∂μ, inverseBid n (beta v) ∈ Icc (inverseBid n B) (inverseBid n a) := by
    filter_upwards [hband] with v hv
    exact ⟨inverseBid_antitone n hn (ha.trans_le hv.1) hv.2,
      inverseBid_antitone n hn ha hv.1⟩
  have hnonneg : ∀ᵐ v ∂μ, 0 ≤ inverseBid n (beta v) := by
    filter_upwards [hband] with v hv
    exact (inverseBid_pos n (ha.trans_le hv.1)).le
  have hi : Integrable (fun v => inverseBid n (beta v)) μ :=
    Integrable.of_bound hm.aestronglyMeasurable (inverseBid n a) (by
      filter_upwards [hb, hnonneg] with v hv hv0
      rw [Real.norm_eq_abs, abs_of_nonneg hv0]
      exact hv.2)
  have hlo := integral_mono_ae (integrable_const (inverseBid n B)) hi (hb.mono fun _ hv => hv.1)
  have hhi := integral_mono_ae hi (integrable_const (inverseBid n a)) (hb.mono fun _ hv => hv.2)
  simp only [integral_const, smul_eq_mul, hmass] at hlo hhi
  exact ⟨hi, ⟨hlo, hhi⟩, (mul_pos hh (inverseBid_pos n (ha.trans_le haB))).trans_le hlo⟩

theorem meanExposure_capacity {μ : Measure ℝ} [IsFiniteMeasure μ]
    {n : ℕ} {h rho : ℝ} (hmass : μ.real Set.univ = h) (beta : ℝ → ℝ)
    (hi : Integrable (fun v => inverseBid n (beta v)) μ)
    (hw : (∫ v, inverseBid n (beta v) ∂μ) ≠ 0) :
    ∫ v, meanExposure n ((h - rho) / (∫ w, inverseBid n (beta w) ∂μ)) beta v ∂μ = rho := by
  unfold meanExposure
  rw [integral_sub (integrable_const _) (hi.const_mul _), integral_const_mul]
  simp only [integral_const, smul_eq_mul, mul_one, hmass]
  rw [div_mul_cancel₀ _ hw]
  ring

theorem meanExposure_bid_formula (d : ℕ) (hd : 1 ≤ d) {D b : ℝ}
    (hD : 0 < D) (hb : 0 < b) :
    b = D ^ d / (1 - (1 - D * inverseBid (d + 1) b)) ^ d := by
  have hq : 0 < D * inverseBid (d + 1) b := mul_pos hD (inverseBid_pos _ hb)
  rw [sub_sub_cancel]
  apply (eq_div_iff (pow_ne_zero _ hq.ne')).mpr
  rw [mul_pow, inverseBid_natPower d hd hb]
  field_simp [hb.ne']

theorem meanExposure_monotone (n : ℕ) (hn : 2 ≤ n) {D a : ℝ}
    (hD : 0 ≤ D) (ha : 0 < a) (beta : ℝ → ℝ)
    (hbeta : Monotone beta) (hfloor : ∀ v, a ≤ beta v) :
    Monotone (meanExposure n D beta) := by
  intro v w hvw
  have h := mul_le_mul_of_nonneg_left
    (inverseBid_antitone n hn (ha.trans_le (hfloor v)) (hbeta hvw)) hD
  dsimp [meanExposure]
  linarith

theorem meanExposure_corridor {n : ℕ} {h rho W a B b : ℝ}
    (hn : 2 ≤ n) (hh : 0 < h) (hrho : rho < h) (ha : 0 < a)
    (hab : b ∈ Icc a B)
    (hW : W ∈ Icc (h * inverseBid n B) (h * inverseBid n a)) :
    ((h - rho) / (h * inverseBid n a)) * inverseBid n B ≤
      ((h - rho) / W) * inverseBid n b ∧
    ((h - rho) / W) * inverseBid n b ≤
      ((h - rho) / (h * inverseBid n B)) * inverseBid n a := by
  have hB : 0 < B := ha.trans_le (hab.1.trans hab.2)
  have hWa : 0 < h * inverseBid n a := mul_pos hh (inverseBid_pos n ha)
  have hWB : 0 < h * inverseBid n B := mul_pos hh (inverseBid_pos n hB)
  have hwpos : 0 < W := hWB.trans_le hW.1
  have hd : 0 < h - rho := sub_pos.mpr hrho
  have hlo : (h - rho) / (h * inverseBid n a) ≤ (h - rho) / W :=
    div_le_div_of_nonneg_left hd.le hwpos hW.2
  have hhi : (h - rho) / W ≤ (h - rho) / (h * inverseBid n B) :=
    div_le_div_of_nonneg_left hd.le hWB hW.1
  have hwb := inverseBid_antitone n hn (ha.trans_le hab.1) hab.2
  have haw := inverseBid_antitone n hn ha hab.1
  exact ⟨mul_le_mul hlo hwb (inverseBid_pos n hB).le (div_nonneg hd.le hwpos.le),
    mul_le_mul hhi haw (inverseBid_pos n (ha.trans_le hab.1)).le (div_nonneg hd.le hWB.le)⟩

end FCAppendix.Exclusive.Narrow
