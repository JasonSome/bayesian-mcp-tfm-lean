import FCAppendix.Finite.ConditionalCountLaw
import FCAppendix.Finite.BalancedOrder
import FCAppendix.Probability.Bounds

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Filter Set Topology
open scoped BigOperators
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem chosen_realized_mismatch_le_load_gap
    (Γ : FiniteGame m n c Seed) (i : Fin m) (act : JointAction n) :
    ((problem Γ i).outcome act).prob (fun r => r.val ≠ act.routeCount) ≤
      (act.routeCount : ℝ) - ((problem Γ i).outcome act).load := by
  classical
  let K := focalCount Γ i act
  have hK : Measurable K := measurable_focalCount Γ i act
  have hpoint (ω : Sample m n Seed) :
      (if (K ω).val ≠ act.routeCount then (1 : ℝ) else 0) ≤
        (act.routeCount : ℝ) - (K ω).val := by
    have hk : (K ω).val ≤ act.routeCount := focalCount_le Γ i act ω
    by_cases he : (K ω).val = act.routeCount
    · simp only [he, ne_eq, not_true_eq_false, if_false, sub_self, le_refl]
    · rw [if_pos he]
      have hh : (K ω).val + 1 ≤ act.routeCount := by omega
      have hhR : ((K ω).val : ℝ) + 1 ≤ act.routeCount := by exact_mod_cast hh
      linarith
  have hleft := CountLaw.integrable_comp (sampleLaw Γ) K hK
    (fun r => if r.val ≠ act.routeCount then (1 : ℝ) else 0)
  have hright := (integrable_const (act.routeCount : ℝ)).sub
    (CountLaw.integrable_comp (sampleLaw Γ) K hK (fun r => (r.val : ℝ)))
  have hh := integral_mono hleft hright hpoint
  simp only [Pi.sub_apply] at hh
  rw [integral_sub (integrable_const _) (CountLaw.integrable_comp (sampleLaw Γ) K hK
    (fun r => (r.val : ℝ))), integral_const, probReal_univ, one_smul] at hh
  have hprob : ((problem Γ i).outcome act).prob (fun r => r.val ≠ act.routeCount) =
      ∫ ω, (if (K ω).val ≠ act.routeCount then (1 : ℝ) else 0) ∂sampleLaw Γ := by
    simp only [FiniteLaw.prob, problem_outcome, CountLaw.expect_ofMeasure]
    apply integral_congr_ae
    exact Eventually.of_forall fun ω => by
      by_cases he : (K ω).val = act.routeCount <;> simp [K] at he ⊢
  rw [hprob]
  simpa only [problem_outcome, CountLaw.load, CountLaw.expect_ofMeasure, K] using hh

theorem chosen_realized_mismatch_le_marginal
    (Γ : FiniteGame m n c Seed) (hn : 0 < n) (i : Fin m) (act : JointAction n) :
    ((problem Γ i).outcome act).prob (fun r => r.val ≠ act.routeCount) ≤
      (act.routeCount : ℝ) * (1 - meanAcceptProb Γ i act.bid) := by
  have hh := chosen_realized_mismatch_le_load_gap Γ i act
  rw [load_eq_mean Γ hn i act] at hh
  nlinarith

theorem chosen_realized_mismatch_le_error
    (Γ : FiniteGame m n c Seed) (hn : 0 < n) (i : Fin m) (act : JointAction n)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hq : 0 < act.routeCount → 1 - meanAcceptProb Γ i act.bid ≤ ε) :
    ((problem Γ i).outcome act).prob (fun r => r.val ≠ act.routeCount) ≤ (n : ℝ) * ε := by
  have hh := chosen_realized_mismatch_le_marginal Γ hn i act
  by_cases hk : act.routeCount = 0
  · rw [hk, Nat.cast_zero, zero_mul] at hh
    simpa only [hk] using hh.trans (mul_nonneg (Nat.cast_nonneg n) hε)
  · have hq' := hq (Nat.pos_of_ne_zero hk)
    have hkr : (act.routeCount : ℝ) ≤ n := by exact_mod_cast act.routeCount_le
    exact hh.trans ((mul_le_mul_of_nonneg_left hq' (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hkr hε))

theorem chosen_realized_class_error
    (Γ : FiniteGame m n c Seed) (hn : 0 < n) (i : Fin m) (act : JointAction n)
    (j : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hq : 0 < act.routeCount → 1 - meanAcceptProb Γ i act.bid ≤ ε) :
    |((problem Γ i).outcome act).prob (fun r => r.val = j) -
      (if act.routeCount = j then 1 else 0)| ≤ (n : ℝ) * ε := by
  classical
  have hh := FiniteLaw.coupling_event_bound ((problem Γ i).outcome act)
    (fun r => r.val) (fun _ => act.routeCount) j
  have hc : ((problem Γ i).outcome act).prob (fun _ => act.routeCount = j) =
      (if act.routeCount = j then 1 else 0) := by
    by_cases he : act.routeCount = j <;> simp [he]
  rw [hc] at hh
  exact hh.trans (chosen_realized_mismatch_le_error Γ hn i act hε hq)

theorem mixed_chosen_realized_class_error
    (Γ : FiniteGame m n c Seed) (hn : 0 < n) (i : Fin m)
    (ν : Measure (JointAction n)) [IsProbabilityMeasure ν]
    (j : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hq : ∀ᵐ act ∂ν, 0 < act.routeCount → 1 - meanAcceptProb Γ i act.bid ≤ ε) :
    |(∫ act, ((problem Γ i).outcome act).prob (fun r => r.val = j) ∂ν) -
      (∫ act, (if act.routeCount = j then (1 : ℝ) else 0) ∂ν)| ≤ (n : ℝ) * ε := by
  classical
  let f : JointAction n → ℝ := fun act =>
    ((problem Γ i).outcome act).prob (fun r => r.val = j)
  let q : JointAction n → ℝ := fun act => if act.routeCount = j then 1 else 0
  have hf : Integrable f ν := by
    simpa only [f, FiniteLaw.prob_eq_expect] using
      FiniteLaw.integrable_expect ν (problem Γ i).outcome
        (measurable_outcome_mass Γ i) (fun r => if r.val = j then 1 else 0)
  have hqm : Measurable q := by
    exact Measurable.ite ((measurable_routeCount n) (measurableSet_singleton j))
      measurable_const measurable_const
  have hqi : Integrable q ν := Integrable.of_bound hqm.aestronglyMeasurable 1
    (Eventually.of_forall fun act => by dsimp [q]; split_ifs <;> norm_num)
  have hb : ∀ᵐ act ∂ν, |f act - q act| ≤ (n : ℝ) * ε := by
    filter_upwards [hq] with act ha
    exact chosen_realized_class_error Γ hn i act j hε ha
  have hh := integral_mono_ae (hf.sub hqi).abs (integrable_const ((n : ℝ) * ε)) hb
  rw [integral_const, probReal_univ, one_smul] at hh
  calc
    _ = |∫ act, f act - q act ∂ν| := by rw [integral_sub hf hqi]
    _ ≤ ∫ act, |f act - q act| ∂ν := abs_integral_le_integral_abs
    _ ≤ _ := hh

end FCAppendix.Bayes
