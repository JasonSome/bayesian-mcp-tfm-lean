import FCAppendix.Ample.SlackAccounting
import FCAppendix.Ample.FreeBaseIncentives

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

structure FreeBaseAmpleSequence
    (M C : ℕ → ℕ) (Γ : ∀ t, FiniteGame (M t) n (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) (g ρ : ℝ) : Prop where
  common_values : ∀ t, (Γ t).F = F
  common_fee : ∀ t, (Γ t).g = g
  atomless_values : ∀ v : ℝ, F {v} = 0
  population_grows : Tendsto M atTop atTop
  capacity_ratio : Tendsto (fun t => (C t : ℝ) / M t) atTop (𝓝 ρ)
  ample : F.real (Ioi g) < (n : ℝ) * ρ
  interior : ρ < F.real (Ioi g)
  users : ∀ t, UsersOptimal (Γ t)
  bayes_receipts : ∀ t, BayesReceiptOptimalOnPath (Γ t) (B t)
  feasible_continuations : ∀ t j, ProposerRationalAtFeasibleLists (Γ t) j
  visible_atomless : ∀ t, PositiveVisibleAtomless (Γ t)
  ppi : ∀ t, (Γ t).A = Schedule.ppi n
  free : ∀ t, FreeDuplicateBase (Γ t)
  abstention : ∀ t, NonpositiveAbstention (Γ t)
  reject_zero : ∀ t, RejectsZeroBids (Γ t)

namespace FreeBaseAmpleSequence
variable {M C : ℕ → ℕ} {Γ : ∀ t, FiniteGame (M t) n (C t) Seed}
  {B : ∀ t, PosteriorSystem (Γ t)} {F : Measure ℝ} {g ρ : ℝ}
  (h : FreeBaseAmpleSequence M C Γ B F g ρ)

include h

lemma probability : IsProbabilityMeasure F := by
  rw [← h.common_values 0]
  infer_instance

lemma proposers_pos : 0 < n := by
  by_contra hn
  have hz : n = 0 := by omega
  have hh := h.ample
  rw [hz, Nat.cast_zero, zero_mul] at hh
  exact (measureReal_nonneg : 0 ≤ F.real (Ioi g)).not_gt hh

lemma ratio_pos : 0 < ρ := by
  by_contra hρ
  have hh := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) (le_of_not_gt hρ)
  exact (measureReal_nonneg : 0 ≤ F.real (Ioi g)).not_gt (h.ample.trans_le hh)

lemma active_pos : 0 < F.real (Ioi g) := h.ratio_pos.trans h.interior

lemma active_le_one : F.real (Ioi g) ≤ 1 := by
  letI := h.probability
  exact measureReal_le_one

lemma ratio_lt_one : ρ < 1 := h.interior.trans_le h.active_le_one

lemma two_proposers : 2 ≤ n := by
  by_contra hn
  have hn1 : n = 1 := by have := h.proposers_pos; omega
  have hh := h.ample
  rw [hn1, Nat.cast_one, one_mul] at hh
  exact lt_asymm hh h.interior

theorem receipt : ReceiptSequenceAssumptions M C Γ B F g 1 ρ where
  proposers_pos := h.proposers_pos
  common_values := h.common_values
  common_fee := h.common_fee
  factor_pos := by norm_num
  ratio_pos := h.ratio_pos
  ratio_lt_one := h.ratio_lt_one
  population_grows := h.population_grows
  capacity_ratio := h.capacity_ratio
  users := h.users
  bayes_receipts := h.bayes_receipts
  feasible_continuations := h.feasible_continuations
  visible_atomless := h.visible_atomless
  receipt_lower := by
    intro t r _ _
    simp [h.ppi t, Schedule.ppi]

lemma coverage_tendsto :
    Tendsto (fun t => finiteCoverage (Γ t)) atTop (𝓝 (F.real (Ioi g))) := by
  letI := h.probability
  exact h.receipt.ample_coverage_tendsto (h.atomless_values g) (by simpa using h.ample)

lemma positiveParticipation_tendsto :
    Tendsto (fun t => positiveRouteMass (Γ t) (fun _ => True)) atTop
      (𝓝 (F.real (Ioi g))) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' h.coverage_tendsto tendsto_const_nhds
  · filter_upwards [h.population_grows.eventually_ge_atTop 1] with t ht
    exact finiteCoverage_le_positiveParticipation (Γ t) ht h.proposers_pos (h.reject_zero t)
  · filter_upwards [] with t
    simpa only [h.common_values t, h.common_fee t] using
      positiveRouteMass_le_active (Γ t) (h.abstention t) (fun _ => True)

lemma zeroBidDiscrepancy_tendsto :
    Tendsto (fun t => submittedMarginal (Γ t) -
      Ample.contactMarginal n (visibleClassMass (Γ t) 0)) atTop (𝓝 0) := by
  have hd : Tendsto (fun t => F.real (Ioi g) - finiteCoverage (Γ t)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := F.real (Ioi g))).sub h.coverage_tendsto
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hd
  · filter_upwards [] with t
    exact sub_nonneg.mpr (arrivalMean_le_submitted (Γ t) 0)
  · filter_upwards [h.population_grows.eventually_ge_atTop 1] with t ht
    simpa only [h.common_values t, h.common_fee t] using
      submitted_minus_positive_le_coverage_deficit (Γ t) ht h.proposers_pos
        (h.abstention t) (h.reject_zero t)

lemma eventually_finite_guards :
    ∀ᶠ t in atTop, 1 < M t ∧ 0 < C t ∧ C t ≤ M t - 1 := by
  filter_upwards [h.population_grows.eventually_ge_atTop 2,
    h.receipt.eventually_capacity_pos,
    (tendsto_order.mp h.capacity_ratio).2 1 h.ratio_lt_one] with t hM hC hr
  have hMr : (0 : ℝ) < M t := by exact_mod_cast (show 0 < M t by omega)
  have hCM : (C t : ℝ) < M t := (div_lt_one hMr).mp hr
  have hCMn : C t < M t := by exact_mod_cast hCM
  exact ⟨by omega, hC, by omega⟩

lemma along (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) :
    FreeBaseAmpleSequence (M ∘ φ) (C ∘ φ) (fun t => Γ (φ t))
      (fun t => B (φ t)) F g ρ where
  common_values := fun t => h.common_values (φ t)
  common_fee := fun t => h.common_fee (φ t)
  atomless_values := h.atomless_values
  population_grows := h.population_grows.comp hφ
  capacity_ratio := h.capacity_ratio.comp hφ
  ample := h.ample
  interior := h.interior
  users := fun t => h.users (φ t)
  bayes_receipts := fun t => h.bayes_receipts (φ t)
  feasible_continuations := fun t => h.feasible_continuations (φ t)
  visible_atomless := fun t => h.visible_atomless (φ t)
  ppi := fun t => h.ppi (φ t)
  free := fun t => h.free (φ t)
  abstention := fun t => h.abstention (φ t)
  reject_zero := fun t => h.reject_zero (φ t)

end FreeBaseAmpleSequence
end FCAppendix.Bayes
