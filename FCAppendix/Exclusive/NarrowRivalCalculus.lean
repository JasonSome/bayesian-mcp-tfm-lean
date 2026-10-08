import FCAppendix.Exclusive.NarrowTestBounds
import Mathlib.Analysis.Calculus.ParametricIntegral

namespace FCAppendix.Exclusive.Narrow.Finite
open MeasureTheory Filter Topology Set
open scoped BigOperators

structure Corridor (n m c : ℕ) where
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  width : lower < upper
  proposers : 2 ≤ n
  population : 0 < m
  capacity : 0 < c
  spread : ((m : ℝ) - c) * inverseBid n lower <
    (m : ℝ) * inverseBid n upper

variable {n m c : ℕ}

namespace Corridor
variable (P : Corridor n m c)

def interior : Set ℝ := Ioo P.lower P.upper
noncomputable def radius : ℝ := rate n / P.lower
noncomputable def ownBound : ℝ :=
  inverseBid n P.lower / (((c : ℝ) + 1) * inverseBid n P.upper)

lemma upper_pos : 0 < P.upper := P.lower_pos.trans P.width
lemma radius_nonneg : 0 ≤ P.radius :=
  (div_pos (rate_pos n P.proposers) P.lower_pos).le
lemma ownBound_nonneg : 0 ≤ P.ownBound := by
  exact (div_pos (inverseBid_pos n P.lower_pos)
    (mul_pos (by positivity) (inverseBid_pos n P.upper_pos))).le

def ListBounds (N : ℕ) (W : ℝ) : Prop :=
  1 ≤ N ∧ N ≤ m ∧
    ((N - 1 : ℕ) : ℝ) * inverseBid n P.upper ≤ W ∧
    W ≤ ((N - 1 : ℕ) : ℝ) * inverseBid n P.lower

noncomputable def allocation (_P : Corridor n m c) (N : ℕ) (W b : ℝ) : ℝ :=
  focalMarginal (rate n) ((N - c : ℕ) : ℝ) W b
noncomputable def share (_P : Corridor n m c) (W b : ℝ) : ℝ := focalShare (rate n) W b
noncomputable def velocity0 (N : ℕ) (W b : ℝ) : ℝ :=
  rate n * (1 - P.allocation N W b) / b
noncomputable def velocity (N : ℕ) (W b : ℝ) : ℝ :=
  P.velocity0 N W b * (1 - P.share W b)
noncomputable def pricePower (_P : Corridor n m c) (N : ℕ) (W b : ℝ) : ℝ :=
  ((N - c : ℕ) : ℝ) / (W + inverseBid n b)

lemma demand_spread : (m : ℝ) * demand n P.upper P.lower < c := by
  have hp : 0 < demand n P.upper P.lower :=
    (demand_pos_iff n P.proposers P.upper_pos P.lower_pos.le).mpr P.width
  have he := one_sub_demand_eq_inverseBid n P.proposers P.upper_pos P.lower_pos hp
  have hinv : P.lower ^ rate n * inverseBid n P.lower = 1 := by
    unfold inverseBid
    rw [← Real.rpow_add P.lower_pos]
    simp
  have hw := inverseBid_pos n P.lower_pos
  have hid : demand n P.upper P.lower * inverseBid n P.lower =
      inverseBid n P.lower - inverseBid n P.upper := by
    calc
      _ = inverseBid n P.lower -
          (1 - demand n P.upper P.lower) * inverseBid n P.lower := by ring
      _ = inverseBid n P.lower - inverseBid n P.upper := by
        rw [he]
        have hz : (P.lower ^ rate n * inverseBid n P.upper) * inverseBid n P.lower =
            inverseBid n P.upper := by
          calc
            _ = (P.lower ^ rate n * inverseBid n P.lower) * inverseBid n P.upper := by ring
            _ = inverseBid n P.upper := by rw [hinv, one_mul]
        rw [hz]
  apply (mul_lt_mul_iff_left₀ hw).mp
  calc
    ((m : ℝ) * demand n P.upper P.lower) * inverseBid n P.lower =
        (m : ℝ) * (inverseBid n P.lower - inverseBid n P.upper) := by rw [mul_assoc, hid]
    _ < (c : ℝ) * inverseBid n P.lower := by nlinarith [P.spread]

lemma weight_bounds {b : ℝ} (hb : b ∈ Icc P.lower P.upper) :
    inverseBid n P.upper ≤ inverseBid n b ∧
      inverseBid n b ≤ inverseBid n P.lower :=
  ⟨inverseBid_antitone n P.proposers (P.lower_pos.trans_le hb.1) hb.2,
    inverseBid_antitone n P.proposers P.lower_pos hb.1⟩

lemma weightSum_lower {N : ℕ} {W b : ℝ}
    (h : P.ListBounds N W) (hb : b ∈ Icc P.lower P.upper) :
    (N : ℝ) * inverseBid n P.upper ≤ W + inverseBid n b := by
  have hw := (P.weight_bounds hb).1
  have hW := h.2.2.1
  rw [Nat.cast_sub h.1, Nat.cast_one] at hW
  nlinarith

lemma rival_nonneg {N : ℕ} {W : ℝ} (h : P.ListBounds N W) : 0 ≤ W :=
  (mul_nonneg (Nat.cast_nonneg _) (inverseBid_pos n P.upper_pos).le).trans h.2.2.1

lemma allocation_bounds {N : ℕ} {W b : ℝ}
    (h : P.ListBounds N W) (hb : b ∈ Icc P.lower P.upper) :
    0 < P.allocation N W b ∧ P.allocation N W b ≤ 1 := by
  have hbpos := P.lower_pos.trans_le hb.1
  have hw := inverseBid_pos n hbpos
  have hW := P.rival_nonneg h
  have hden : 0 < W + inverseBid n b := add_pos_of_nonneg_of_pos hW hw
  have hgap : 0 ≤ ((N - c : ℕ) : ℝ) := Nat.cast_nonneg _
  have hq0 := div_nonneg (mul_nonneg hgap hw.le) hden.le
  have hq1 : ((N - c : ℕ) : ℝ) * inverseBid n b / (W + inverseBid n b) < 1 := by
    by_cases hNc : N ≤ c
    · simp [Nat.sub_eq_zero_of_le hNc]
    · have hcN : c ≤ N := by omega
      have hweights : 0 ≤ inverseBid n P.lower - inverseBid n P.upper :=
        sub_nonneg.mpr (inverseBid_antitone n P.proposers P.lower_pos P.width.le)
      have hNm : (N : ℝ) ≤ m := by exact_mod_cast h.2.1
      have hgrowth := mul_le_mul_of_nonneg_right hNm hweights
      have hnum : ((N : ℝ) - c) * inverseBid n P.lower <
          (N : ℝ) * inverseBid n P.upper := by
        nlinarith [P.spread]
      have hsum := P.weightSum_lower h hb
      have hsmall := mul_le_mul_of_nonneg_left (P.weight_bounds hb).2 hgap
      apply (div_lt_one hden).mpr
      rw [Nat.cast_sub hcN] at hsmall ⊢
      exact lt_of_le_of_lt hsmall (hnum.trans_le hsum)
  change 0 < 1 - _ ∧ 1 - _ ≤ 1
  exact ⟨sub_pos.mpr hq1, sub_le_self _ hq0⟩

lemma share_bounds {N : ℕ} {W b : ℝ}
    (h : P.ListBounds N W) (hb : b ∈ Icc P.lower P.upper) :
    0 ≤ P.share W b ∧ P.share W b ≤ 1 := by
  have hw := inverseBid_pos n (P.lower_pos.trans_le hb.1)
  have hW := P.rival_nonneg h
  have hden : 0 < W + inverseBid n b := add_pos_of_nonneg_of_pos hW hw
  change 0 ≤ inverseBid n b / (W + inverseBid n b) ∧
    inverseBid n b / (W + inverseBid n b) ≤ 1
  exact ⟨div_nonneg hw.le hden.le, (div_le_one hden).mpr (by linarith)⟩

lemma share_le_ownBound {N : ℕ} {W b : ℝ}
    (h : P.ListBounds N W) (hb : b ∈ Icc P.lower P.upper) (hover : c < N) :
    P.share W b ≤ P.ownBound := by
  have hcount : (c : ℝ) + 1 ≤ N := by
    exact_mod_cast (Nat.succ_le_of_lt hover)
  have hwb := inverseBid_pos n P.upper_pos
  have hden0 : 0 < ((c : ℝ) + 1) * inverseBid n P.upper := mul_pos (by positivity) hwb
  have hden := (mul_le_mul_of_nonneg_right hcount hwb.le).trans (P.weightSum_lower h hb)
  exact (div_le_div_of_nonneg_right (P.weight_bounds hb).2
    (hden0.trans_le hden).le).trans
      (div_le_div_of_nonneg_left (inverseBid_pos n P.lower_pos).le hden0 hden)

@[simp] lemma allocation_underloaded {N : ℕ} (W b : ℝ) (hN : N ≤ c) :
    P.allocation N W b = 1 := by
  simp [allocation, Nat.sub_eq_zero_of_le hN]

@[simp] lemma velocity0_underloaded {N : ℕ} (W b : ℝ) (hN : N ≤ c) :
    P.velocity0 N W b = 0 := by simp [velocity0, P.allocation_underloaded W b hN]

@[simp] lemma velocity_underloaded {N : ℕ} (W b : ℝ) (hN : N ≤ c) :
    P.velocity N W b = 0 := by simp [velocity, P.velocity0_underloaded W b hN]

lemma velocity0_bounds {N : ℕ} {W b : ℝ}
    (h : P.ListBounds N W) (hb : b ∈ Icc P.lower P.upper) :
    0 ≤ P.velocity0 N W b ∧ P.velocity0 N W b ≤ P.radius := by
  have hp := P.allocation_bounds h hb
  have hr := (rate_pos n P.proposers).le
  have hbpos := P.lower_pos.trans_le hb.1
  refine ⟨div_nonneg (mul_nonneg hr (sub_nonneg.mpr hp.2)) hbpos.le, ?_⟩
  calc
    P.velocity0 N W b ≤ rate n / b := by
      apply div_le_div_of_nonneg_right _ hbpos.le
      nlinarith
    _ ≤ P.radius := div_le_div_of_nonneg_left hr P.lower_pos hb.1

lemma velocity_bounds {N : ℕ} {W b : ℝ}
    (h : P.ListBounds N W) (hb : b ∈ Icc P.lower P.upper) :
    0 ≤ P.velocity N W b ∧ P.velocity N W b ≤ P.radius := by
  have hv := P.velocity0_bounds h hb
  have hs := P.share_bounds h hb
  exact ⟨mul_nonneg hv.1 (sub_nonneg.mpr hs.2),
    (mul_le_of_le_one_right hv.1 (by linarith : 1 - P.share W b ≤ 1)).trans hv.2⟩

lemma velocity_error {N : ℕ} {W b : ℝ}
    (h : P.ListBounds N W) (hb : b ∈ Icc P.lower P.upper) :
    |P.velocity N W b - P.velocity0 N W b| ≤ P.radius * P.ownBound := by
  by_cases hover : c < N
  · have hv := P.velocity0_bounds h hb
    have hs := P.share_bounds h hb
    have he : P.velocity N W b - P.velocity0 N W b =
        -(P.velocity0 N W b * P.share W b) := by unfold velocity; ring
    rw [he, abs_neg, abs_of_nonneg (mul_nonneg hv.1 hs.1)]
    exact mul_le_mul hv.2 (P.share_le_ownBound h hb hover) hs.1 P.radius_nonneg
  · simp only [P.velocity_underloaded W b (by omega : N ≤ c),
      P.velocity0_underloaded W b (by omega : N ≤ c), sub_self, abs_zero]
    exact mul_nonneg P.radius_nonneg P.ownBound_nonneg

lemma hasDerivAt_allocation {N : ℕ} {W b : ℝ}
    (h : P.ListBounds N W) (hb : b ∈ Icc P.lower P.upper) :
    HasDerivAt (P.allocation N W) (P.velocity N W b) b :=
  hasDerivAt_focalMarginal (P.lower_pos.trans_le hb.1) (P.rival_nonneg h)

lemma allocation_lt_one {N : ℕ} {W b : ℝ}
    (h : P.ListBounds N W) (hb : b ∈ Icc P.lower P.upper) (hover : c < N) :
    P.allocation N W b < 1 := by
  have hd : (0 : ℝ) < (N - c : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hover
  have hw := inverseBid_pos n (P.lower_pos.trans_le hb.1)
  have hden : 0 < W + inverseBid n b := add_pos_of_nonneg_of_pos (P.rival_nonneg h) hw
  have hpos := div_pos (mul_pos hd hw) hden
  change 1 - ((N-c : ℕ) : ℝ) * inverseBid n b / (W + inverseBid n b) < 1
  linarith

lemma velocity_pos {N : ℕ} {W b : ℝ}
    (h : P.ListBounds N W) (hb : b ∈ Icc P.lower P.upper) (hover : c < N) :
    0 < P.velocity N W b := by
  have hN : 0 < N - 1 := by have := P.capacity; omega
  have hW : 0 < W := (mul_pos (by exact_mod_cast hN)
    (inverseBid_pos n P.upper_pos)).trans_le h.2.2.1
  exact focalMarginal_derivative_pos (rate_pos n P.proposers)
    (by exact_mod_cast Nat.sub_pos_of_lt hover) hW (P.lower_pos.trans_le hb.1)

lemma pricePower_bounds {N : ℕ} {W b : ℝ}
    (h : P.ListBounds N W) (hb : b ∈ Icc P.lower P.upper) :
    0 ≤ P.pricePower N W b ∧ P.pricePower N W b ≤ 1 / inverseBid n P.upper := by
  have hN : (0 : ℝ) < N := by
    exact_mod_cast (show 0 < N by have := h.1; omega)
  have hw := inverseBid_pos n P.upper_pos
  have hd : 0 < W + inverseBid n b :=
    (mul_pos hN hw).trans_le (P.weightSum_lower h hb)
  refine ⟨div_nonneg (Nat.cast_nonneg _) hd.le, ?_⟩
  apply (div_le_div_iff₀ hd hw).mpr
  have hgap : ((N-c:ℕ):ℝ) ≤ N := by exact_mod_cast Nat.sub_le N c
  simpa only [one_mul] using
    (mul_le_mul_of_nonneg_right hgap hw.le).trans (P.weightSum_lower h hb)

lemma rival_price_equation {N : ℕ} {W b : ℝ}
    (h : P.ListBounds N W) (hb : b ∈ Icc P.lower P.upper) (hover : c < N) :
    P.pricePower N W b =
      (((N - 1 - c : ℕ) : ℝ) + P.allocation N W b) / W := by
  have hc : c ≤ N - 1 := by omega
  have hN : 0 < N - 1 := by have := P.capacity; omega
  have hW : 0 < W := (mul_pos (by exact_mod_cast hN)
    (inverseBid_pos n P.upper_pos)).trans_le h.2.2.1
  have hw := inverseBid_pos n (P.lower_pos.trans_le hb.1)
  have hd : W + inverseBid n b ≠ 0 := (add_pos hW hw).ne'
  unfold inverseBid at hd
  unfold pricePower allocation focalMarginal inverseBid
  rw [Nat.cast_sub hc, Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one,
    Nat.cast_sub hover.le]
  field_simp [hW.ne', hd]
  ring

lemma hasDerivAt_pricePower {N : ℕ} {W b : ℝ}
    (h : P.ListBounds N W) (hb : b ∈ Icc P.lower P.upper) :
    HasDerivAt (P.pricePower N W)
      (rate n / b * P.pricePower N W b * P.share W b) b := by
  have hbpos := P.lower_pos.trans_le hb.1
  have hw := inverseBid_pos n hbpos
  have hd : W + inverseBid n b ≠ 0 :=
    (add_pos_of_nonneg_of_pos (P.rival_nonneg h) hw).ne'
  have hpow : b ^ (-rate n - 1) = b ^ (-rate n) / b := by
    rw [Real.rpow_sub hbpos, Real.rpow_one]
  have hder := (hasDerivAt_const b ((N-c:ℕ):ℝ)).div
    ((hasDerivAt_const b W).add
      (Real.hasDerivAt_rpow_const (x := b) (p := -rate n) (Or.inl hbpos.ne'))) hd
  apply hder.congr_deriv
  dsimp only [pricePower, share, focalShare, inverseBid, Pi.add_apply]
  rw [hpow]
  unfold inverseBid at hd
  field_simp [hbpos.ne', hd]
  ring

lemma pricePower_derivative_bound {N : ℕ} {W b : ℝ}
    (h : P.ListBounds N W) (hb : b ∈ Icc P.lower P.upper) :
    |rate n / b * P.pricePower N W b * P.share W b| ≤
      (P.radius / inverseBid n P.upper) * P.ownBound := by
  by_cases hover : c < N
  · have hr : 0 ≤ rate n / b := div_nonneg (rate_pos n P.proposers).le
      (P.lower_pos.trans_le hb.1).le
    have hp := P.pricePower_bounds h hb
    have hs := P.share_bounds h hb
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg hr hp.1) hs.1)]
    calc
      _ ≤ (P.radius * (1 / inverseBid n P.upper)) * P.ownBound :=
        mul_le_mul (mul_le_mul
          (div_le_div_of_nonneg_left (rate_pos n P.proposers).le P.lower_pos hb.1)
          hp.2 hp.1 P.radius_nonneg)
          (P.share_le_ownBound h hb hover) hs.1
          (mul_nonneg P.radius_nonneg (one_div_nonneg.mpr (inverseBid_pos n P.upper_pos).le))
      _ = _ := by ring
  · simp only [pricePower, Nat.sub_eq_zero_of_le (by omega : N ≤ c), Nat.cast_zero,
      zero_div, mul_zero, zero_mul, abs_zero]
    exact mul_nonneg (div_nonneg P.radius_nonneg
      (inverseBid_pos n P.upper_pos).le) P.ownBound_nonneg

end Corridor

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

structure Row (P : Corridor n m c) (μ : Measure Ω) where
  count : Ω → ℕ
  weight : Ω → ℝ
  count_measurable : Measurable count
  weight_measurable : Measurable weight
  bounds : ∀ᵐ ω ∂μ, P.ListBounds (count ω) (weight ω)

namespace Row
variable {P : Corridor n m c} (R : Row P μ)

noncomputable def p (b : ℝ) (ω : Ω) := P.allocation (R.count ω) (R.weight ω) b
noncomputable def dp (b : ℝ) (ω : Ω) := P.velocity (R.count ω) (R.weight ω) b
noncomputable def dp0 (b : ℝ) (ω : Ω) := P.velocity0 (R.count ω) (R.weight ω) b
noncomputable def moment (f : ℕ → ℝ) (b : ℝ) := ∫ ω, binomialPolynomial n f (R.p b ω) ∂μ
noncomputable def momentDerivative (f : ℕ → ℝ) (b : ℝ) :=
  ∫ ω, binomialPolynomialDerivative n f (R.p b ω) * R.dp b ω ∂μ
noncomputable def referenceDerivative (f : ℕ → ℝ) (b : ℝ) :=
  ∫ ω, binomialPolynomialDerivative n f (R.p b ω) * R.dp0 b ω ∂μ

lemma measurable_p (b : ℝ) : Measurable (R.p b) := by
  exact measurable_const.sub ((((measurable_of_countable (fun N : ℕ => ((N - c : ℕ) : ℝ))).comp
    R.count_measurable).mul measurable_const).div (R.weight_measurable.add measurable_const))

lemma measurable_dp0 (b : ℝ) : Measurable (R.dp0 b) := by
  exact ((measurable_const.mul (measurable_const.sub (R.measurable_p b))).div_const b)

lemma measurable_dp (b : ℝ) : Measurable (R.dp b) := by
  exact (R.measurable_dp0 b).mul (measurable_const.sub
    (measurable_const.div (R.weight_measurable.add measurable_const)))

lemma measurable_test (f : ℕ → ℝ) (b : ℝ) :
    Measurable (fun ω => binomialPolynomial n f (R.p b ω)) :=
  (continuous_binomialPolynomial n f).measurable.comp (R.measurable_p b)

lemma measurable_testDerivative (f : ℕ → ℝ) (b : ℝ) :
    Measurable (fun ω => binomialPolynomialDerivative n f (R.p b ω) * R.dp b ω) :=
  ((continuous_binomialPolynomialDerivative n f).measurable.comp (R.measurable_p b)).mul
    (R.measurable_dp b)

variable [IsProbabilityMeasure μ]

lemma integrable_test (f : ℕ → ℝ) {K b : ℝ}
    (hf : CountTestBound n f K) (hb : b ∈ Icc P.lower P.upper) :
    Integrable (fun ω => binomialPolynomial n f (R.p b ω)) μ := by
  apply Integrable.of_bound (R.measurable_test f b).aestronglyMeasurable K
  filter_upwards [R.bounds] with ω hω
  simpa only [Real.norm_eq_abs, p] using
    abs_binomialPolynomial_le n f hf ⟨(P.allocation_bounds hω hb).1.le,
      (P.allocation_bounds hω hb).2⟩

omit [IsProbabilityMeasure μ] in
lemma testDerivative_bound (f : ℕ → ℝ) {K b : ℝ}
    (hf : CountTestBound n f K) (hb : b ∈ Icc P.lower P.upper) :
    ∀ᵐ ω ∂μ, |binomialPolynomialDerivative n f (R.p b ω) * R.dp b ω| ≤
      2 * n * K * P.radius := by
  filter_upwards [R.bounds] with ω hω
  have hp := P.allocation_bounds hω hb
  have hv := P.velocity_bounds hω hb
  dsimp only [p, dp]
  rw [abs_mul, abs_of_nonneg hv.1]
  exact mul_le_mul (abs_binomialPolynomialDerivative_le n f hf ⟨hp.1.le, hp.2⟩)
    hv.2 hv.1 (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) hf.1)

lemma integrable_testDerivative (f : ℕ → ℝ) {K b : ℝ}
    (hf : CountTestBound n f K) (hb : b ∈ Icc P.lower P.upper) :
    Integrable (fun ω => binomialPolynomialDerivative n f (R.p b ω) * R.dp b ω) μ := by
  apply Integrable.of_bound (R.measurable_testDerivative f b).aestronglyMeasurable
    (2 * n * K * P.radius)
  simpa only [Real.norm_eq_abs] using R.testDerivative_bound f hf hb

theorem hasDerivAt_moment (f : ℕ → ℝ) {b : ℝ} (hb : b ∈ P.interior) :
    HasDerivAt (R.moment f) (R.momentDerivative f b) b := by
  obtain ⟨K,hK⟩ := countTestBound_exists n f
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := fun x ω => binomialPolynomial n f (R.p x ω))
    (F' := fun x ω => binomialPolynomialDerivative n f (R.p x ω) * R.dp x ω)
    (s := P.interior) (bound := fun _ : Ω => 2 * n * K * P.radius)
    (Ioo_mem_nhds hb.1 hb.2)
    (Eventually.of_forall fun x => (R.measurable_test f x).aestronglyMeasurable)
    (R.integrable_test f hK ⟨hb.1.le,hb.2.le⟩)
    (R.measurable_testDerivative f b).aestronglyMeasurable
    (by
      filter_upwards [R.bounds] with ω hω x hx
      have hp := P.allocation_bounds hω ⟨hx.1.le,hx.2.le⟩
      have hv := P.velocity_bounds hω ⟨hx.1.le,hx.2.le⟩
      dsimp only [p, dp]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hv.1]
      exact mul_le_mul (abs_binomialPolynomialDerivative_le n f hK ⟨hp.1.le,hp.2⟩)
        hv.2 hv.1 (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) hK.1))
    (integrable_const _)
    (by
      filter_upwards [R.bounds] with ω hω x hx
      exact (hasDerivAt_binomialPolynomial n f (R.p x ω)).comp x
        (P.hasDerivAt_allocation hω ⟨hx.1.le,hx.2.le⟩))
  exact h.2

lemma integrable_referenceDerivative (f : ℕ → ℝ) {K b : ℝ}
    (hf : CountTestBound n f K) (hb : b ∈ Icc P.lower P.upper) :
    Integrable (fun ω => binomialPolynomialDerivative n f (R.p b ω) * R.dp0 b ω) μ := by
  apply Integrable.of_bound
    (((continuous_binomialPolynomialDerivative n f).measurable.comp (R.measurable_p b)).mul
      (R.measurable_dp0 b)).aestronglyMeasurable (2 * n * K * P.radius)
  filter_upwards [R.bounds] with ω hω
  have hp := P.allocation_bounds hω hb
  have hv := P.velocity0_bounds hω hb
  dsimp only [Function.comp_apply, Pi.mul_apply, p, dp0]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hv.1]
  exact mul_le_mul (abs_binomialPolynomialDerivative_le n f hf ⟨hp.1.le,hp.2⟩)
    hv.2 hv.1 (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) hf.1)

theorem derivative_error (f : ℕ → ℝ) {K b : ℝ}
    (hf : CountTestBound n f K) (hb : b ∈ Icc P.lower P.upper) :
    |R.momentDerivative f b - R.referenceDerivative f b| ≤
      2 * n * K * P.radius * P.ownBound := by
  rw [momentDerivative, referenceDerivative, ← integral_sub
    (R.integrable_testDerivative f hf hb) (R.integrable_referenceDerivative f hf hb)]
  apply abs_integral_le_integral_abs.trans
  calc
    _ ≤ ∫ _ω : Ω, 2 * n * K * P.radius * P.ownBound ∂μ := by
      apply integral_mono_ae
        ((R.integrable_testDerivative f hf hb).sub (R.integrable_referenceDerivative f hf hb)).abs
        (integrable_const _)
      filter_upwards [R.bounds] with ω hω
      have hp := P.allocation_bounds hω hb
      dsimp only [Pi.sub_apply, p, dp, dp0]
      rw [← mul_sub, abs_mul]
      calc
        _ ≤ (2 * n * K) * (P.radius * P.ownBound) :=
          mul_le_mul (abs_binomialPolynomialDerivative_le n f hf ⟨hp.1.le,hp.2⟩)
            (P.velocity_error hω hb) (abs_nonneg _)
            (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) hf.1)
        _ = _ := by ring
    _ = _ := by simp

theorem exceptional_derivative_bound (f : ℕ → ℝ) {K b : ℝ}
    (hf : CountTestBound n f K) (hb : b ∈ Icc P.lower P.upper) (E : Set Ω) :
    (∫ ω in E, |binomialPolynomialDerivative n f (R.p b ω) * R.dp b ω| ∂μ) ≤
      μ.real E * (2 * n * K * P.radius) := by
  calc
    _ ≤ ∫ _ω in E, 2 * n * K * P.radius ∂μ := by
      apply integral_mono_ae (R.integrable_testDerivative f hf hb).abs.restrict
        (integrable_const _)
      exact ae_restrict_of_ae (R.testDerivative_bound f hf hb)
    _ = _ := by simp [Measure.real, smul_eq_mul]

omit [IsProbabilityMeasure μ] in

theorem momentDerivative_eq_zero_of_full_capacity (hcap : m ≤ c) (f : ℕ → ℝ) (b : ℝ) :
    R.momentDerivative f b = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [R.bounds] with ω hω
  have hN := hω.2.1.trans hcap
  simp only [dp, P.velocity_underloaded (R.weight ω) b hN, mul_zero, Pi.zero_apply]

omit [IsProbabilityMeasure μ] in
theorem referenceDerivative_eq_zero_of_full_capacity (hcap : m ≤ c) (f : ℕ → ℝ) (b : ℝ) :
    R.referenceDerivative f b = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [R.bounds] with ω hω
  have hN := hω.2.1.trans hcap
  simp only [dp0, P.velocity0_underloaded (R.weight ω) b hN, mul_zero, Pi.zero_apply]

end Row
end FCAppendix.Exclusive.Narrow.Finite
