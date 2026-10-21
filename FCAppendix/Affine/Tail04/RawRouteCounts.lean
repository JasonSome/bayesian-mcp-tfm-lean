import FCAppendix.Affine.Tail04.CountLaws
import FCAppendix.Affine.LowBody.HiddenRoute

noncomputable section
namespace FCAppendix.Affine.Tail04.RawRoutes
open MeasureTheory ProbabilityTheory Game Bayes Set

def action (b : ℝ) (hb : 0 ≤ b) (k : Fin 3) : JointAction 2 :=
  ⟨b, hb, k.val, by omega⟩

variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
  (Γ : FiniteGame m 2 c Seed) (i : Fin m) (b : ℝ) (hb : 0 ≤ b)

def broadcastDuplicates : ℝ :=
  ((problem Γ i).outcome (action b hb 2)).duplicates

include hb in
theorem present_acceptance_bounds : meanAcceptProb Γ i b ∈ Icc (0:ℝ) 1 := by
  have hlow : 0 ≤ meanAcceptProb Γ i b := by
    unfold meanAcceptProb acceptProb
    positivity
  have hhigh := (meanAcceptProb_le_success Γ (by norm_num : 0<2) i
    (action b hb 1) (by norm_num [action])).trans
      ((problem Γ i).outcome (action b hb 1)).success_le_one
  exact ⟨hlow, hhigh⟩

theorem zero_route_statistics :
    ((problem Γ i).outcome (action b hb 0)).success=0 ∧
      ((problem Γ i).outcome (action b hb 0)).duplicates=0 := by
  have hL := load_eq_mean Γ (by norm_num : 0<2) i (action b hb 0)
  simp only [show (action b hb 0).routeCount=0 by rfl,
    show (action b hb 0).bid=b by rfl,Nat.cast_zero,zero_mul] at hL
  have hS : ((problem Γ i).outcome (action b hb 0)).success=0 := by
    have hlo := ((problem Γ i).outcome (action b hb 0)).success_nonneg
    have hhi := ((problem Γ i).outcome (action b hb 0)).success_le_load
    linarith
  exact ⟨hS, by rw [CountLaw.duplicates, hL, hS, sub_self]⟩

theorem singleton_statistics :
    ((problem Γ i).outcome (action b hb 1)).success=meanAcceptProb Γ i b ∧
      ((problem Γ i).outcome (action b hb 1)).duplicates=0 := by
  have hL := load_eq_mean Γ (by norm_num : 0<2) i (action b hb 1)
  simp only [show (action b hb 1).routeCount=1 by rfl,
    show (action b hb 1).bid=b by rfl,Nat.cast_one,one_mul] at hL
  have hLS := load_le_routeCount_mul_success Γ i (action b hb 1)
  simp only [show (action b hb 1).routeCount=1 by rfl,
    Nat.cast_one,one_mul] at hLS
  have hS : ((problem Γ i).outcome (action b hb 1)).success=meanAcceptProb Γ i b := by
    have hSL := ((problem Γ i).outcome (action b hb 1)).success_le_load
    linarith
  exact ⟨hS, by rw [CountLaw.duplicates, hL, hS, sub_self]⟩

theorem singleton_count_law :
    (problem Γ i).outcome (action b hb 1) =
      Counts.singletonLaw (meanAcceptProb Γ i b) (present_acceptance_bounds Γ i b hb) := by
  have h := singleton_statistics Γ i b hb
  have hJ := Counts.singletonLaw_statistics (meanAcceptProb Γ i b)
    (present_acceptance_bounds Γ i b hb)
  exact Counts.eq_of_success_duplicates _ _ (h.1.trans hJ.1.symm) (h.2.trans hJ.2.1.symm)

theorem zero_count_law : (problem Γ i).outcome (action b hb 0) = FiniteLaw.dirac 0 := by
  have h := zero_route_statistics Γ i b hb
  apply Counts.eq_of_success_duplicates
  · simpa [CountLaw.success, FiniteLaw.expect_dirac, successIndicator] using h.1
  · simpa [CountLaw.duplicates, CountLaw.success, CountLaw.load,
      FiniteLaw.expect_dirac, successIndicator] using h.2

theorem broadcast_count_masses :
    ((problem Γ i).outcome (action b hb 2)).mass 0 =
      1-2*meanAcceptProb Γ i b+broadcastDuplicates Γ i b hb ∧
    ((problem Γ i).outcome (action b hb 2)).mass 1 =
      2*meanAcceptProb Γ i b-2*broadcastDuplicates Γ i b hb ∧
    ((problem Γ i).outcome (action b hb 2)).mass 2 =
      broadcastDuplicates Γ i b hb := by
  have hL := load_eq_mean Γ (by norm_num : 0<2) i (action b hb 2)
  change ((problem Γ i).outcome (action b hb 2)).load=2*meanAcceptProb Γ i b at hL
  have hD : broadcastDuplicates Γ i b hb =
      ((problem Γ i).outcome (action b hb 2)).load-
        ((problem Γ i).outcome (action b hb 2)).success := rfl
  have h := Counts.count_masses ((problem Γ i).outcome (action b hb 2))
  have hDup : ((problem Γ i).outcome (action b hb 2)).duplicates=broadcastDuplicates Γ i b hb := rfl
  rw [hDup] at h
  change ((problem Γ i).outcome (action b hb 2)).mass 0 = _ ∧
    ((problem Γ i).outcome (action b hb 2)).mass 1 = _ ∧
    ((problem Γ i).outcome (action b hb 2)).mass 2 = _
  exact ⟨by linarith only [h.1,hD,hL],by linarith only [h.2.1,hD,hL],h.2.2⟩

theorem all_route_payoffs (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hA : Γ.A=Schedule.affine 2 η hη0 hη1) (hg : Γ.g=0) (v : ℝ) :
    (problem Γ i).payoff v (action b hb 0)=0 ∧
    (problem Γ i).payoff v (action b hb 1)=(v-b)*meanAcceptProb Γ i b ∧
    (problem Γ i).payoff v (action b hb 2)=
      2*(v-b)*meanAcceptProb Γ i b-
        (v-(1-η)*b)*broadcastDuplicates Γ i b hb := by
  have h0 := zero_route_statistics Γ i b hb
  have h1 := singleton_statistics Γ i b hb
  have hL := load_eq_mean Γ (by norm_num : 0<2) i (action b hb 2)
  change ((problem Γ i).outcome (action b hb 2)).load=2*meanAcceptProb Γ i b at hL
  have hD : broadcastDuplicates Γ i b hb =
      ((problem Γ i).outcome (action b hb 2)).load-
        ((problem Γ i).outcome (action b hb 2)).success := rfl
  constructor
  · rw [LowBody.native_affine_zero_fee_payoff Γ hη0 hη1 hA hg,
      h0.1, h0.2]
    ring
  constructor
  · rw [LowBody.native_affine_zero_fee_payoff Γ hη0 hη1 hA hg,
      h1.1, h1.2]
    simp only [action, mul_zero, sub_zero]
  · rw [LowBody.native_affine_zero_fee_payoff Γ hη0 hη1 hA hg]
    change (v-b)*_ - η*b*broadcastDuplicates Γ i b hb = _
    rw [hL] at hD
    rw [show ((problem Γ i).outcome (action b hb 2)).success =
      2*meanAcceptProb Γ i b-broadcastDuplicates Γ i b hb by linarith only [hD]]
    ring

omit [MeasurableSpace Seed] in
theorem local_list_for_every_route (k : Fin 3) (ω : Sample m 2 Seed) (j : Fin 2)
    (hj : j ∈ firstK ω.2 k.val) :
    observe (deviated i (action b hb k) ω) j = presentList ω.1 i b j :=
  observe_deviated_of_mem i (action b hb k) ω j hj

end FCAppendix.Affine.Tail04.RawRoutes
