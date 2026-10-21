import FCAppendix.Affine.Multiple07.MenuAdapter
import FCAppendix.Affine.Multiple07.OutcomeCertificate
import FCAppendix.Affine.Hybrid.NormalizedGuardRegion

noncomputable section
namespace FCAppendix.Affine.Multiple07
open MeasureTheory Set Uniform07

def kappa : ℝ := 1 - xi
def meanReceipt (r : Partition) : ℝ := 1 - xi * activeFraction r
def sourceInwardScale (r : Partition) : ℝ := (1 - activeFraction r) / meanReceipt r
def bidLower (r : Partition) : ℝ := sourceInwardScale r * activeLower r - 1 / 1000
def bidUpper (r : Partition) : ℝ := sourceInwardScale r * activeUpper r + 1 / 1000

theorem sourceExposure_zero (r : Partition) :
    Hybrid.sourceExposure (activeMass r) (upperMass r) rho 0 = activeFraction r := by
  simp [Hybrid.sourceExposure, activeFraction]

theorem sourceInwardScale_zero (r : Partition) :
    Hybrid.inwardScale xi 0 (activeFraction r) = sourceInwardScale r := by
  cases r <;> norm_num [Hybrid.inwardScale, sourceInwardScale, meanReceipt,
    activeFraction, activeMass, upperMass, rho, xi]

theorem meanReceipt_pos (r : Partition) : 0 < meanReceipt r := by
  cases r <;> norm_num [meanReceipt, xi, activeFraction, activeMass, upperMass, rho]

def multiplierLower : Partition → ℝ
  | .row335 => 467910 / 1000000
  | .row665 => 494813 / 1000000

def multiplierUpper : Partition → ℝ
  | .row335 => 467911 / 1000000
  | .row665 => 494815 / 1000000

theorem source_multiplier_enclosures (r : Partition) :
    multiplierLower r < multiplier r ∧ multiplier r < multiplierUpper r := by
  constructor
  · apply Box.lower_real (multiplierBox_ok r)
    cases r <;> norm_num [multiplierLower, multiplierBox, unfilledFractionQ,
      reciprocalBox, firstReciprocalBox, secondReciprocalBox, firstBandLog,
      secondBandLog, LogCertificate.box, Box.add, Box.sub, Box.neg, Box.mul,
      Box.scale, Box.div, Box.inv, Box.point]
  · apply Box.upper_real (multiplierBox_ok r)
    cases r <;> norm_num [multiplierUpper, multiplierBox, unfilledFractionQ,
      reciprocalBox, firstReciprocalBox, secondReciprocalBox, firstBandLog,
      secondBandLog, LogCertificate.box, Box.add, Box.sub, Box.neg, Box.mul,
      Box.scale, Box.div, Box.inv, Box.point]

theorem literal_receipt_inward_guards (r : Partition) :
    0 < bidLower r ∧ bidLower r < bidUpper r ∧
    kappa * bidUpper r < meanReceipt r * bidLower r ∧
    meanReceipt r * bidLower r < meanReceipt r * bidUpper r ∧
    meanReceipt r * bidUpper r < bidLower r ∧
    lowCeiling < kappa * bidLower r ∧
    bidLower r < sourceInwardScale r * activeLower r ∧
    sourceInwardScale r * activeLower r < sourceInwardScale r * activeUpper r ∧
    sourceInwardScale r * activeUpper r < bidUpper r ∧
    bidUpper r < activeLower r ∧ bidUpper r < upperFloor r ∧
    0 < upperFloor r ∧ upperFloor r < upperLower r := by
  cases r <;> norm_num [bidLower, bidUpper, sourceInwardScale, meanReceipt,
    activeFraction, activeMass, upperMass, rho, xi, kappa, activeLower,
    activeUpper, upperFloor, upperLower, lowCeiling]

theorem source_exposure_lt_53 (r : Partition) {v : ℝ}
    (hv : v ∈ Icc (activeLower r) (activeUpper r)) :
    0 < exposure r v ∧ exposure r v < 53 / 100 := by
  have hv0 := (activeLower_pos r).trans_le hv.1
  have hnum : (47 / 100 : ℝ) * activeUpper r < multiplierLower r := by
    cases r <;> norm_num [activeUpper, multiplierLower]
  have hmul : (47 / 100 : ℝ) * v < multiplier r :=
    (mul_le_mul_of_nonneg_left hv.2 (by norm_num)).trans_lt
      (hnum.trans (source_multiplier_enclosures r).1)
  have hdiv : (47 / 100 : ℝ) < multiplier r / v := (lt_div_iff₀ hv0).2 hmul
  exact ⟨(exposure_bounds_of_lower r hv.1).1, by dsimp [exposure]; linarith⟩

private theorem quadratic_pos {a b c : ℝ} (ha : 0 < a)
    (hd : 0 < 4 * a * c - b ^ 2) (q : ℝ) :
    0 < a * q ^ 2 + b * q + c := by
  have he : 4 * a * (a * q ^ 2 + b * q + c) =
      (2 * a * q + b) ^ 2 + (4 * a * c - b ^ 2) := by ring
  have hp : 0 < 4 * a * (a * q ^ 2 + b * q + c) := by
    rw [he]
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) hd
  exact (mul_pos_iff_of_pos_left (by positivity : (0 : ℝ) < 4 * a)).mp hp

theorem source_one_denominator_pos {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    0 < 1 - xi * q := by
  norm_num [xi] at *
  linarith [hq.2]

theorem source_outsideTwo_identity (v lam : ℝ) (hv : v ≠ 0) :
    (v - Hybrid.outsideTwo v lam) * v = 2 * lam * v - lam ^ 2 := by
  unfold Hybrid.outsideTwo
  field_simp [hv]; ring

theorem source_outsideTwo_exposure (r : Partition) {v : ℝ}
    (hv : activeLower r ≤ v) :
    Hybrid.outsideTwo v (multiplier r) = v * (exposure r v) ^ 2 := by
  have hv0 : v ≠ 0 := ((activeLower_pos r).trans_le hv).ne'
  unfold Hybrid.outsideTwo exposure
  field_simp [hv0]

theorem active_two_gt_every_one (r : Partition) {v q : ℝ}
    (hv : v ∈ Icc (activeLower r) (activeUpper r)) (hq : q ∈ Icc (0 : ℝ) 1) :
    Hybrid.one xi 0 v (multiplier r) q < Hybrid.outsideTwo v (multiplier r) := by
  let p := exposure r v
  have hp : 0 < p ∧ p < 53 / 100 := source_exposure_lt_53 r hv
  have hξ : 0 < xi := by norm_num [xi]
  have hA : 0 ≤ 1 + xi * p := add_nonneg zero_le_one (mul_nonneg hξ.le hp.1.le)
  have hB : 0 ≤ 1 + xi * (53 / 100 : ℝ) := by norm_num [xi]
  have hAB : 1 + xi * p ≤ 1 + xi * (53 / 100 : ℝ) :=
    add_le_add_right (mul_le_mul_of_nonneg_left hp.2.le hξ.le) 1
  have hsq := mul_le_mul hAB hAB hA hB
  have hdisc : 0 < 4 * xi * p ^ 2 - (-(p + xi * p ^ 2)) ^ 2 := by
    have he : 4 * xi * p ^ 2 - (-(p + xi * p ^ 2)) ^ 2 =
        p ^ 2 * (4 * xi - (1 + xi * p) ^ 2) := by ring
    rw [he]
    apply mul_pos (sq_pos_of_pos hp.1)
    norm_num [xi] at hsq ⊢
    nlinarith
  have hpoly := quadratic_pos hξ hdisc q
  have hv0 := (activeLower_pos r).trans_le hv.1
  have hd := source_one_denominator_pos hq
  have hlam : multiplier r = v * (1 - p) := by
    dsimp [p, exposure]
    field_simp [hv0.ne']; ring
  have he : (Hybrid.outsideTwo v (multiplier r) -
      Hybrid.one xi 0 v (multiplier r) q) * (1 - xi * q) =
      v * (xi * q ^ 2 + (-(p + xi * p ^ 2)) * q + p ^ 2) := by
    rw [source_outsideTwo_exposure r hv.1]
    change (v * p ^ 2 - Hybrid.one xi 0 v (multiplier r) q) * _ = _
    unfold Hybrid.one
    simp only [zero_div, sub_zero, one_mul, zero_add]
    rw [hlam]
    have hdn : 1-q*xi ≠ 0 := by simpa only [mul_comm] using hd.ne'
    field_simp [hd.ne',hdn]; ring
  have hpos : 0 < (Hybrid.outsideTwo v (multiplier r) -
      Hybrid.one xi 0 v (multiplier r) q) * (1 - xi * q) := by
    rw [he]
    exact mul_pos hv0 hpoly
  exact sub_pos.mp ((mul_pos_iff_of_pos_right hd).mp hpos)

theorem active_two_gt_upper_price (r : Partition) {v : ℝ}
    (hv : v ∈ Icc (activeLower r) (activeUpper r)) :
    v - upperFloor r < Hybrid.outsideTwo v (multiplier r) := by
  have hv0 := (activeLower_pos r).trans_le hv.1
  have hlam := source_multiplier_enclosures r
  have hlo : 0 ≤ multiplierLower r := by cases r <;> norm_num [multiplierLower]
  have hhi : 0 ≤ 2 * multiplierUpper r - upperFloor r := by
    cases r <;> norm_num [multiplierUpper, upperFloor]
  have hn : 0 < (multiplierLower r) ^ 2 -
      (2 * multiplierUpper r - upperFloor r) * activeUpper r := by
    cases r <;> norm_num [multiplierLower, multiplierUpper, upperFloor, activeUpper]
  have hs := mul_le_mul hlam.1.le hlam.1.le hlo (multiplier_bounds r).1.le
  have h1 := mul_le_mul_of_nonneg_right
    (show 2 * multiplier r - upperFloor r ≤ 2 * multiplierUpper r - upperFloor r by linarith)
    hv0.le
  have h2 := mul_le_mul_of_nonneg_left hv.2 hhi
  have he := source_outsideTwo_identity v (multiplier r) hv0.ne'
  have hp : 0 < (Hybrid.outsideTwo v (multiplier r) - (v - upperFloor r)) * v := by
    nlinarith
  exact sub_pos.mp ((mul_pos_iff_of_pos_right hv0).mp hp)

theorem upper_price_gt_outsideTwo (r : Partition) {v : ℝ} (hv : upperLower r ≤ v) :
    Hybrid.outsideTwo v (multiplier r) < v - upperFloor r := by
  have hvH : 0 < upperLower r := by cases r <;> norm_num [upperLower]
  have hv0 := hvH.trans_le hv
  have hlam := source_multiplier_enclosures r
  have hhi : 0 ≤ multiplierUpper r := by cases r <;> norm_num [multiplierUpper]
  have hlo : 0 ≤ 2 * multiplierLower r - upperFloor r := by
    cases r <;> norm_num [multiplierLower, upperFloor]
  have hn : 0 < (2 * multiplierLower r - upperFloor r) * upperLower r -
      (multiplierUpper r) ^ 2 := by
    cases r <;> norm_num [multiplierLower, multiplierUpper, upperFloor, upperLower]
  have hs := mul_le_mul hlam.2.le hlam.2.le (multiplier_bounds r).1.le hhi
  have h1 := mul_le_mul_of_nonneg_right
    (show 2 * multiplierLower r - upperFloor r ≤ 2 * multiplier r - upperFloor r by linarith)
    hv0.le
  have h2 := mul_le_mul_of_nonneg_left hv hlo
  have he := source_outsideTwo_identity v (multiplier r) hv0.ne'
  have hp : 0 < ((v - upperFloor r) - Hybrid.outsideTwo v (multiplier r)) * v := by
    nlinarith
  exact sub_pos.mp ((mul_pos_iff_of_pos_right hv0).mp hp)

theorem upper_price_gt_every_one (r : Partition) {v q : ℝ}
    (hv : upperLower r ≤ v) (hq : q ∈ Icc (0 : ℝ) 1) :
    Hybrid.one xi 0 v (multiplier r) q < v - upperFloor r := by
  have ha : 0 < xi * upperLower r := by cases r <;> norm_num [xi, upperLower]
  have hdisc : 0 <
      4 * (xi * upperLower r) * (upperLower r - upperFloor r) -
        (-upperLower r * (1 + xi) + upperFloor r * xi + multiplierLower r) ^ 2 := by
    cases r <;> norm_num [xi, upperLower, upperFloor, multiplierLower]
  have hquad := quadratic_pos ha hdisc q
  have hd := source_one_denominator_pos hq
  have hvprod : 0 ≤ (v - upperLower r) * (1 - q) * (1 - xi * q) :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hv) (sub_nonneg.mpr hq.2)) hd.le
  have hlamprod : 0 ≤ (multiplier r - multiplierLower r) * q :=
    mul_nonneg (sub_nonneg.mpr (source_multiplier_enclosures r).1.le) hq.1
  have hp : 0 < xi * v * q ^ 2 +
      (-v * (1 + xi) + upperFloor r * xi + multiplier r) * q + (v - upperFloor r) := by
    nlinarith
  have he : ((v - upperFloor r) - Hybrid.one xi 0 v (multiplier r) q) *
      (1 - xi * q) = xi * v * q ^ 2 +
        (-v * (1 + xi) + upperFloor r * xi + multiplier r) * q + (v - upperFloor r) := by
    unfold Hybrid.one
    simp only [zero_div, sub_zero, one_mul, zero_add]
    have hdn : 1-q*xi ≠ 0 := by simpa only [mul_comm] using hd.ne'
    field_simp [hd.ne',hdn]; ring
  exact sub_pos.mp ((mul_pos_iff_of_pos_right hd).mp (he.symm ▸ hp))

theorem literal_active_menu_guards (r : Partition) {v : ℝ}
    (hv : v ∈ Icc (activeLower r) (activeUpper r)) :
    (∀ q ∈ Icc (0 : ℝ) 1,
      Hybrid.one xi 0 v (multiplier r) q <
        Hybrid.two xi 0 v (multiplier r) (exposure r v)) ∧
    v - upperFloor r < Hybrid.two xi 0 v (multiplier r) (exposure r v) ∧
    Hybrid.two xi 0 v (multiplier r) (exposure r v) =
      Hybrid.outsideTwo v (multiplier r) := by
  rw [(source_two_zero_optimizer r hv.1).2.1]
  exact ⟨fun _ hq => active_two_gt_every_one r hv hq,
    active_two_gt_upper_price r hv, rfl⟩

theorem literal_upper_menu_guards (r : Partition) {v : ℝ} (hv : upperLower r ≤ v) :
    Hybrid.outsideTwo v (multiplier r) < v - upperFloor r ∧
    (∀ q ∈ Icc (0 : ℝ) 1, Hybrid.one xi 0 v (multiplier r) q < v - upperFloor r) ∧
    (∀ q ∈ Icc (0 : ℝ) 1, Hybrid.two xi 0 v (multiplier r) q < v - upperFloor r) := by
  have hvA : activeLower r ≤ v := by
    have h : activeLower r ≤ upperLower r := by cases r <;> norm_num [activeLower, upperLower]
    exact h.trans hv
  have hprice := upper_price_gt_outsideTwo r hv
  exact ⟨hprice, fun _ hq => upper_price_gt_every_one r hv hq,
    fun q _ => ((source_two_zero_optimizer r hvA).2.2 q).trans_lt hprice⟩

theorem source_one_maximum_attained (r : Partition) (v : ℝ) :
    ∃ q ∈ Icc (0 : ℝ) 1, ∀ q' ∈ Icc (0 : ℝ) 1,
      Hybrid.one xi 0 v (multiplier r) q' ≤ Hybrid.one xi 0 v (multiplier r) q := by
  have hc : ContinuousOn (fun q => Hybrid.one xi 0 v (multiplier r) q) (Icc (0 : ℝ) 1) := by
    have he : (fun q => Hybrid.one xi 0 v (multiplier r) q) =
        (fun q => q * (v - multiplier r / (1 - xi * q))) := by
      funext q
      simp [Hybrid.one]
    rw [he]
    exact continuousOn_id.mul (continuousOn_const.sub
      (continuousOn_const.div
        (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
        (fun _ hq => (source_one_denominator_pos hq).ne')))
  obtain ⟨q, hq, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) 1).Nonempty from ⟨0, by norm_num⟩) hc
  exact ⟨q, hq, hmax⟩

end FCAppendix.Affine.Multiple07
