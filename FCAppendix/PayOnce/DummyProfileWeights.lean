import FCAppendix.PayOnce.DummyProfileKernel
import FCAppendix.PayOnce.ProfileWeights

namespace FCAppendix.PayOnce.DummyKernel
open MeasureTheory Set CommonList OwnImpact
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

theorem rivalSensitivity_active (n : ℕ) (r : ι → ℝ) {L : ℝ} (hL : 0 < L) :
    rivalSensitivity n (fun j : Active r => r j.val) L = rivalSensitivity n r L := by
  classical
  have h := Fintype.sum_subtype_add_sum_subtype (p := fun j => 0 < r j)
    (fun j => if 0 < kernel n (r j) L ∧ kernel n (r j) L < 1 then
      sensitivity n (r j) (kernel n (r j) L) else 0)
  have hz : (∑ j : {j // ¬0 < r j}, if 0 < kernel n (r j.val) L ∧ kernel n (r j.val) L < 1 then
      sensitivity n (r j.val) (kernel n (r j.val) L) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [kernel_of_le n ((le_of_not_gt j.property).trans hL.le)]
    simp only [lt_self_iff_false,false_and,if_false]
  rw [hz,add_zero] at h
  exact h

theorem weight_eq_impactWeight_of_derivative {m n c : ℕ} (hn : 2 ≤ n)
    (b : Fin m → ℝ) {L : ℝ} (hL : 0 < L)
    (hcap : ∑ j, kernel n (b j) L = min c (Fintype.card (Active b))) (i : Fin m)
    (hi : kernel n (b i) L ∈ Ioo (0:ℝ) 1)
    (hclip0 : ∀ j, b j ≠ L) (hclip1 : ∀ j, b j ≠ (n:ℝ)*L) (weight : ℝ)
    (hweight : b i*deriv (fun x => success n
      (allocation n c hn (fun j : Bayes.Rival i => b j.val) x)) (b i) =
        RareSuccessSlope.weightedSlope n (kernel n (b i) L) weight) :
    weight = impactWeight n b (fun j => kernel n (b j) L) i := by
  have hbi : 0 < b i := by
    by_contra hh
    have hz := kernel_of_le n ((le_of_not_gt hh).trans hL.le)
    linarith [hi.1]
  let r : Bayes.Rival i → ℝ := fun j => b j.val
  have hcap' : kernel n (b i) L + ∑ j : Active r, kernel n (r j.val) L =
      min c (Fintype.card (Active r)+1) := by
    rw [sum_active r hL,← active_card_focal b i hbi]
    exact (Bayes.sum_focal_rivals i (fun j => kernel n (b j) L)).trans hcap
  have hd := focal_success_derivative_ownImpact hn (fun j : Active r => r j.val)
    (fun j => j.property) (allocation n c hn r) hbi hL hcap' hi
    (fun j => hclip0 j.val.val) (fun j => hclip1 j.val.val)
    (fun x hx => AnalyticalKernel.allocation_root hn (min_le_right c (Fintype.card (Active r)+1))
      (fun j : Active r => r j.val) (fun j => j.property) hx)
  rw [RareSuccessSlope.weightedSlope,if_pos (show 0 < kernel n (b i) L ∧ kernel n (b i) L < 1 from hi)] at hweight
  change b i*_ = RareSuccessSlope.phi n (kernel n (b i) L)*_ at hd
  rw [rivalSensitivity_active n r hL] at hd
  have hφ := AnalyticalKernel.phi_pos_interior hn hi
  rw [impactWeight_eq_focalWeight b L i hi]
  change _ = focalWeight n (b i) (kernel n (b i) L) (rivalSensitivity n r L)
  nlinarith [hweight,hd]

end FCAppendix.PayOnce.DummyKernel
