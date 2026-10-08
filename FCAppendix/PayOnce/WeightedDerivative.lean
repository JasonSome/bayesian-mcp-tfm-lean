import FCAppendix.PayOnce.CoverageDerivative
import FCAppendix.PayOnce.RareSuccessSlope

namespace FCAppendix.PayOnce.OwnImpact
open Set CommonList
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem rivalSensitivity_nonneg {n : ℕ} (hn : 2 ≤ n) (rivals : ι → ℝ)
    (hr : ∀ j, 0 < rivals j) (L : ℝ) : 0 ≤ rivalSensitivity n rivals L := by
  classical
  apply Finset.sum_nonneg
  intro j _
  split_ifs with hj
  · exact (sensitivity_pos hn (hr j) ⟨hj.1.le, hj.2.le⟩).le
  · exact le_rfl

theorem focalWeight_bounds {n : ℕ} (hn : 2 ≤ n) {b p D : ℝ}
    (hb : 0 < b) (hp : p ∈ Icc (0 : ℝ) 1) (hD : 0 ≤ D) :
    focalWeight n b p D ∈ Icc (0 : ℝ) 1 := by
  have hd := sensitivity_pos hn hb hp
  have hden : 0 < sensitivity n b p + D := by positivity
  exact ⟨div_nonneg hd.le hden.le, (div_le_one hden).mpr (by linarith)⟩

theorem focalWeight_gap {n c : ℕ} (hn : 2 ≤ n) (rivals : ι → ℝ)
    (hr : ∀ j, 0 < rivals j) {b L : ℝ} (hb : 0 < b) (hL : 0 < L)
    (hcap : kernel n b L + ∑ j, kernel n (rivals j) L = c)
    (hi : kernel n b L ∈ Ioo (0 : ℝ) 1) :
    1 / ((n : ℝ) ^ 3 + 1) ≤
      1 - focalWeight n b (kernel n b L) (rivalSensitivity n rivals L) := by
  classical
  let bids : Option ι → ℝ := fun j => j.elim b rivals
  let p : Option ι → ℝ := fun j => kernel n (bids j) L
  have hpos (j : Option ι) : 0 < bids j := by cases j <;> simp [bids, hb, hr]
  have hp (j : Option ι) : p j ∈ Icc (0 : ℝ) 1 :=
    ⟨kernel_nonneg n hn (hpos j) hL, kernel_le_one n hn (hpos j) hL⟩
  have hsum : ∑ j, p j = c := by simpa [p, bids, Fintype.sum_option] using hcap
  obtain ⟨j, hj, hjp⟩ := exists_other_interior p c hp hsum none hi
  obtain ⟨j, rfl⟩ : ∃ k, j = some k := by cases j with
    | none => exact (hj rfl).elim
    | some k => exact ⟨k, rfl⟩
  change kernel n (rivals j) L ∈ Ioo (0 : ℝ) 1 at hjp
  have hscore := (scalarThreshold_kernel n hn hb hL).2.2.2.2 hi.1 hi.2
  have hjscore := (scalarThreshold_kernel n hn (hr j) hL).2.2.2.2 hjp.1 hjp.2
  have hratio := sensitivity_ratio_bound hn hb (hr j) ⟨hi.1.le, hi.2.le⟩
    ⟨hjp.1.le, hjp.2.le⟩ (hscore.trans hjscore.symm)
  have hjD : sensitivity n (rivals j) (kernel n (rivals j) L) ≤
      rivalSensitivity n rivals L := by
    have hh := Finset.single_le_sum (s := Finset.univ)
      (f := fun k => if 0 < kernel n (rivals k) L ∧ kernel n (rivals k) L < 1 then
        sensitivity n (rivals k) (kernel n (rivals k) L) else 0)
      (fun k _ => by
        split_ifs with hk
        · exact (sensitivity_pos hn (hr k) ⟨hk.1.le, hk.2.le⟩).le
        · exact le_rfl) (Finset.mem_univ j)
    simpa only [rivalSensitivity, if_pos (show 0 < kernel n (rivals j) L ∧ kernel n (rivals j) L < 1 from hjp)] using hh
  have hD := rivalSensitivity_nonneg hn rivals hr L
  have hd := sensitivity_pos hn hb ⟨hi.1.le, hi.2.le⟩
  have hden : 0 < sensitivity n b (kernel n b L) + rivalSensitivity n rivals L := by positivity
  have hratio' := hratio.trans (mul_le_mul_of_nonneg_left hjD (by positivity : 0 ≤ (n : ℝ)^3))
  unfold focalWeight
  apply (div_le_iff₀ (by positivity : 0 < (n : ℝ)^3+1)).mpr
  apply (mul_le_mul_iff_right₀ hden).mp
  field_simp
  nlinarith

end FCAppendix.PayOnce.OwnImpact

namespace FCAppendix.PayOnce.AnalyticalKernel
open MeasureTheory Set CommonList OwnImpact RareSuccessSlope
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

theorem phi_pos_interior {n : ℕ} (hn : 2 ≤ n) {p : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) : 0 < phi n p := by
  unfold phi
  exact div_pos (mul_pos (mul_pos (Nat.cast_pos.mpr (by omega))
    (pow_pos (sub_pos.mpr hp.2) _)) (H_pos n (by omega) p hp.1.le hp.2.le))
    (Hslope_pos hn ⟨hp.1.le, hp.2.le⟩)

theorem exists_weight_success_derivative_of_regular {n c : ℕ} (hn : 2 ≤ n)
    (hc : c ≤ Fintype.card ι + 1) (rivals : ι → ℝ) {b : ℝ} (hb : 0 < b)
    (hreg : RegularClearing n c rivals b) :
    ∃ w : ℝ, w ∈ Icc (0 : ℝ) 1 ∧
      (0 < allocation n c hn hc rivals b ∧ allocation n c hn hc rivals b < 1 →
        1 / ((n : ℝ)^3+1) ≤ 1-w) ∧
      b * deriv (fun x => success n (allocation n c hn hc rivals x)) b =
        weightedSlope n (allocation n c hn hc rivals b) w := by
  classical
  obtain ⟨hr, L, hL, hcap, hzero, hone, hclip0, hclip1⟩ := hreg
  have hroot := fun (x : ℝ) (hx : 0 < x) => allocation_root hn hc rivals hr hx
  have he := allocation_eq_kernel hn hc rivals hr hb hL hcap
  have hp : kernel n b L ∈ Icc (0 : ℝ) 1 :=
    ⟨kernel_nonneg n hn hb hL, kernel_le_one n hn hb hL⟩
  refine ⟨focalWeight n b (kernel n b L) (rivalSensitivity n rivals L),
    focalWeight_bounds hn hb hp (rivalSensitivity_nonneg hn rivals hr L), ?_, ?_⟩
  · rw [he]
    exact fun hi => focalWeight_gap hn rivals hr hb hL hcap hi
  rw [he]
  by_cases hi : 0 < kernel n b L ∧ kernel n b L < 1
  · rw [weightedSlope, if_pos hi]
    exact focal_success_derivative_ownImpact hn rivals hr _ hb hL hcap hi hclip0 hclip1 hroot
  · rw [weightedSlope, if_neg hi]
    have hf : HasDerivAt (allocation n c hn hc rivals) 0 b := by
      by_cases hbl : b < L
      · exact (hasStrictDerivAt_focal_kernel_zero hn rivals _ hb hL hbl hcap hroot).hasDerivAt
      have hnb : (n : ℝ) * L < b := by
        have hlb : L < b := lt_of_le_of_ne (le_of_not_gt hbl) hzero.symm
        have hkp : 0 < kernel n b L := by
          apply lt_of_le_of_ne hp.1
          intro hz
          exact hlb.not_ge ((kernel_eq_zero_iff n hn hb hL).mp hz.symm)
        have hko : kernel n b L = 1 := le_antisymm hp.2 (le_of_not_gt fun hk => hi ⟨hkp, hk⟩)
        have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        have hle := (le_div_iff₀ hnR).mp ((kernel_eq_one_iff n hn hb hL).mp hko)
        exact lt_of_le_of_ne (by nlinarith) hone.symm
      exact (hasStrictDerivAt_focal_kernel_one hn rivals _ hb hL hnb hcap hroot).hasDerivAt
    have hs := (((hf.const_sub 1).pow n).const_sub 1)
    have hz : deriv (fun x => success n (allocation n c hn hc rivals x)) b = 0 := by
      convert hs.deriv using 1 <;> simp [success]
    rw [hz, mul_zero]

end FCAppendix.PayOnce.AnalyticalKernel

namespace FCAppendix.PayOnce.AnalyticalKernel
open MeasureTheory Set CommonList OwnImpact RareSuccessSlope
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

theorem exists_measurable_weight_coverage_derivative {n c : ℕ} (hn : 2 ≤ n)
    (hc : c ≤ Fintype.card ι + 1) (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    {b : ℝ} (hb : 0 < b) (hreg : ∀ᵐ rivals ∂μ, RegularClearing n c rivals b) :
    ∃ weight : (ι → ℝ) → ℝ, Measurable weight ∧
      (∀ rivals, weight rivals ∈ Icc (0 : ℝ) 1) ∧
      (∀ rivals, 1 / ((n : ℝ)^3+1) ≤ 1-weight rivals) ∧
      (∀ᵐ rivals ∂μ,
        b * deriv (fun x => success n (allocation n c hn hc rivals x)) b =
          weightedSlope n (allocation n c hn hc rivals b) (weight rivals)) ∧
      HasDerivAt (coverage n c hn hc μ)
        ((∫ rivals, weightedSlope n (allocation n c hn hc rivals b) (weight rivals) ∂μ) / b) b := by
  let p := fun rivals : ι → ℝ => allocation n c hn hc rivals b
  let d := fun rivals : ι → ℝ => deriv (fun x => success n (allocation n c hn hc rivals x)) b
  have hd := aestronglyMeasurable_success_deriv hn hc μ hb hreg
  let dm := hd.mk d
  let κ : ℝ := 1 / ((n : ℝ)^3+1)
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  have hκ1 : κ ≤ 1 := by
    dsimp only [κ]
    apply (div_le_one (by positivity : 0 < (n : ℝ)^3+1)).mpr
    linarith [pow_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) 3]
  let weight := fun rivals : ι → ℝ => max 0 (min (1-κ) (1-b*dm rivals/phi n (p rivals)))
  have hw : Measurable weight := by
    exact measurable_const.max (measurable_const.min
      (measurable_const.sub ((hd.measurable_mk.const_mul b).div
        ((measurable_phi n).comp (measurable_allocation_rivals hn hc hb)))))
  have hw0 (rivals : ι → ℝ) : 0 ≤ weight rivals := le_max_left _ _
  have hwcap (rivals : ι → ℝ) : weight rivals ≤ 1-κ :=
    max_le (sub_nonneg.mpr hκ1) (min_le_left _ _)
  have hw1 (rivals : ι → ℝ) : weight rivals ≤ 1 := (hwcap rivals).trans (by linarith)
  have he : ∀ᵐ rivals ∂μ, b*d rivals = weightedSlope n (p rivals) (weight rivals) := by
    filter_upwards [hreg, hd.ae_eq_mk] with rivals hrr hdme
    obtain ⟨w, hwbound, hwgap, hderiv⟩ := exists_weight_success_derivative_of_regular hn hc rivals hb hrr
    change b*d rivals = weightedSlope n (p rivals) w at hderiv
    by_cases hi : 0 < p rivals ∧ p rivals < 1
    · have hφ := phi_pos_interior hn hi
      have hsolve : 1-b*dm rivals/phi n (p rivals) = w := by
        change d rivals = dm rivals at hdme
        rw [← hdme, hderiv, weightedSlope, if_pos hi]
        field_simp
        ring
      have hweight : weight rivals = w := by
        change max 0 (min (1-κ) (1-b*dm rivals/phi n (p rivals))) = w
        rw [hsolve, min_eq_right (by linarith [hwgap hi]), max_eq_right hwbound.1]
      rw [hweight]
      exact hderiv
    · simpa only [weightedSlope, if_neg hi] using hderiv
  refine ⟨weight, hw, fun rivals => ⟨hw0 rivals, hw1 rivals⟩,
    fun rivals => by linarith [hwcap rivals], he, ?_⟩
  have hderiv := hasDerivAt_coverage_of_regular hn hc μ hb hreg
  have hint : (∫ rivals, weightedSlope n (p rivals) (weight rivals) ∂μ) =
      b * ∫ rivals, d rivals ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [he] with rivals hr
    exact hr.symm
  change HasDerivAt _ ((∫ rivals, weightedSlope n (p rivals) (weight rivals) ∂μ) / b) b
  rw [hint, mul_div_cancel_left₀ _ hb.ne']
  exact hderiv.2

end FCAppendix.PayOnce.AnalyticalKernel
