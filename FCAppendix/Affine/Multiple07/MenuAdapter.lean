import FCAppendix.Affine.Multiple07.ProfileIntegrals
import FCAppendix.Affine.Hybrid.Menu

noncomputable section
namespace FCAppendix.Affine.Multiple07

open MeasureTheory Set

theorem mean_exposure_at_multiplier (r : Partition) (lam : ℝ) :
    (∫ v : ℝ, (1 - lam / v) ∂activeValueLaw r) =
      1 - lam * reciprocalMean r := by
  simp only [div_eq_mul_inv]
  rw [integral_sub (integrable_const _)
    ((integrable_active_reciprocal r).const_mul lam), integral_const_mul]
  simp only [integral_const, probReal_univ, one_smul, reciprocalMean]

theorem clearing_multiplier_unique (r : Partition) {lam : ℝ}
    (h : (∫ v : ℝ, (1 - lam / v) ∂activeValueLaw r) = activeFraction r) :
    lam = multiplier r := by
  rw [mean_exposure_at_multiplier] at h
  unfold multiplier
  apply (eq_div_iff (reciprocalMean_pos r).ne').2
  linarith

theorem source_capacity_clearing (r : Partition) :
    activeMass r * (∫ v, exposure r v ∂activeValueLaw r) + upperMass r / 2 = rho := by
  rw [active_exposure_integral]
  cases r <;> norm_num [activeFraction, activeMass, upperMass, rho]

theorem source_two_zero_optimizer (r : Partition) {v : ℝ}
    (hv : activeLower r ≤ v) :
    exposure r v ∈ Ioo (0 : ℝ) 1 ∧
      Hybrid.two xi 0 v (multiplier r) (exposure r v) =
        Hybrid.outsideTwo v (multiplier r) ∧
      ∀ q : ℝ, Hybrid.two xi 0 v (multiplier r) q ≤
        Hybrid.outsideTwo v (multiplier r) := by
  simpa only [exposure] using Hybrid.two_zero_max (xi := xi)
    ((activeLower_pos r).trans_le hv) (multiplier_bounds r).1
    ((multiplier_bounds r).2.trans_le hv)

theorem source_two_zero_strict_away (r : Partition) {v q : ℝ}
    (hv : activeLower r ≤ v) (hq : q ≠ exposure r v) :
    Hybrid.two xi 0 v (multiplier r) q <
      Hybrid.two xi 0 v (multiplier r) (exposure r v) := by
  rw [(source_two_zero_optimizer r hv).2.1]
  exact Hybrid.two_zero_strict_away ((activeLower_pos r).trans_le hv) hq

theorem source_two_zero_argmax_iff (r : Partition) {v q : ℝ}
    (hv : activeLower r ≤ v) :
    (∀ q' ∈ Icc (0 : ℝ) 1,
      Hybrid.two xi 0 v (multiplier r) q' ≤ Hybrid.two xi 0 v (multiplier r) q) ↔
      q = exposure r v := by
  constructor
  · intro h
    by_contra hq
    have hopt := source_two_zero_optimizer r hv
    exact (not_le_of_gt (source_two_zero_strict_away r hv hq))
      (h (exposure r v) ⟨hopt.1.1.le, hopt.1.2.le⟩)
  · rintro rfl q' _
    have hopt := source_two_zero_optimizer r hv
    rw [hopt.2.1]
    exact hopt.2.2 q'

def activeBid (r : Partition) (v : ℝ) : ℝ :=
  multiplier r / (1 - xi * exposure r v)

theorem activeBid_denominator_pos (r : Partition) {v : ℝ}
    (hv : activeLower r ≤ v) : 0 < 1 - xi * exposure r v := by
  have hq := (exposure_bounds_of_lower r hv).2
  norm_num [xi] at *
  linarith

theorem activeBid_pos (r : Partition) {v : ℝ} (hv : activeLower r ≤ v) :
    0 < activeBid r v :=
  div_pos (multiplier_bounds r).1 (activeBid_denominator_pos r hv)

theorem activeBid_receipt (r : Partition) {v : ℝ} (hv : activeLower r ≤ v) :
    activeBid r v * (1 - xi * exposure r v) = multiplier r := by
  exact div_mul_cancel₀ _ (activeBid_denominator_pos r hv).ne'

theorem activeBid_exposure (r : Partition) {v : ℝ} (hv : activeLower r ≤ v) :
    Hybrid.exposure xi (multiplier r) (activeBid r v) = exposure r v := by
  have hlam : multiplier r ≠ 0 := (multiplier_bounds r).1.ne'
  have hd : 1 - xi * exposure r v ≠ 0 := (activeBid_denominator_pos r hv).ne'
  have hξ : xi ≠ 0 := by norm_num [xi]
  unfold Hybrid.exposure activeBid
  field_simp [hlam, hd, hξ]; ring

theorem source_independent_menu_value (r : Partition) {v : ℝ}
    (hv : activeLower r ≤ v) :
    Hybrid.independentTwo eta v (activeBid r v) (exposure r v) =
      Hybrid.outsideTwo v (multiplier r) := by
  have hmenu := Hybrid.independentTwo_eq_menu
    (show eta = 1 - 2 * xi by norm_num [eta, xi])
    (show xi ≠ 0 by norm_num [xi]) (activeBid_pos r hv).ne'
    (lam := multiplier r) (v := v)
  rw [activeBid_exposure r hv] at hmenu
  exact hmenu.trans (source_two_zero_optimizer r hv).2.1

end FCAppendix.Affine.Multiple07
