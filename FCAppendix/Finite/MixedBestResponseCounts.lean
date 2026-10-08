import FCAppendix.Finite.ConditionalCountLaw
import FCAppendix.Finite.PPIBidConvergence
import FCAppendix.Finite.BelowCutoffCounts

noncomputable section

namespace FCAppendix.FiniteLaw

open Filter Topology
open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

lemma expect_error_le_prob_ne (μ : FiniteLaw Ω) (j : Ω) (f : Ω → ℝ) :
    |μ.expect f - f j| ≤ (∑ x, |f x - f j|) * μ.prob (fun x => x ≠ j) := by
  classical
  let B := ∑ x, |f x - f j|
  calc
    _ = |μ.expect (fun x => f x - f j)| := by rw [μ.expect_sub, μ.expect_const]
    _ ≤ μ.expect (fun x => |f x - f j|) := μ.abs_expect_le _
    _ ≤ μ.expect (fun x => B * (if x ≠ j then 1 else 0)) := by
      apply μ.expect_mono
      intro x
      by_cases hx : x = j
      · simp [hx]
      · simp only [hx, ne_eq, not_false_eq_true, if_true, mul_one]
        exact Finset.single_le_sum (fun y _ => abs_nonneg (f y - f j)) (Finset.mem_univ x)
    _ = _ := by rw [μ.expect_const_mul, μ.prob_eq_expect]

theorem tendsto_expect_of_prob_ne (μ : ℕ → FiniteLaw Ω) (j : Ω)
    (hμ : Tendsto (fun k => (μ k).prob (fun x => x ≠ j)) atTop (𝓝 0)) (f : Ω → ℝ) :
    Tendsto (fun k => (μ k).expect f) atTop (𝓝 (f j)) := by
  apply (tendsto_iff_dist_tendsto_zero).mpr
  simp only [Real.dist_eq]
  apply squeeze_zero (fun k => abs_nonneg _) (fun k => (μ k).expect_error_le_prob_ne j f)
  simpa only [mul_zero] using hμ.const_mul (∑ x, |f x - f j|)

end FCAppendix.FiniteLaw

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Filter Topology

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def mixedCountLaw (Γ : FiniteGame m n c Seed) (i : Fin m)
    (ν : Measure (JointAction n)) [IsProbabilityMeasure ν] : CountLaw n :=
  FiniteLaw.average ν (problem Γ i).outcome (measurable_outcome_mass Γ i)

lemma mixedCountLaw_expect (Γ : FiniteGame m n c Seed) (i : Fin m)
    (ν : Measure (JointAction n)) [IsProbabilityMeasure ν] (f : Fin (n + 1) → ℝ) :
    (mixedCountLaw Γ i ν).expect f = ∫ act, ((problem Γ i).outcome act).expect f ∂ν :=
  FiniteLaw.expect_average _ _ _ _

lemma mixedCountLaw_prob (Γ : FiniteGame m n c Seed) (i : Fin m)
    (ν : Measure (JointAction n)) [IsProbabilityMeasure ν] (E : Fin (n + 1) → Prop) :
    (mixedCountLaw Γ i ν).prob E = ∫ act, ((problem Γ i).outcome act).prob E ∂ν :=
  mixedCountLaw_expect Γ i ν _

lemma mixedCountLaw_prob_le_of_ae (Γ : FiniteGame m n c Seed) (i : Fin m)
    (ν : Measure (JointAction n)) [IsProbabilityMeasure ν] (E : Fin (n + 1) → Prop)
    (ε : ℝ) (hbound : ∀ᵐ act ∂ν, ((problem Γ i).outcome act).prob E ≤ ε) :
    (mixedCountLaw Γ i ν).prob E ≤ ε := by
  classical
  rw [mixedCountLaw_prob]
  have hi := FiniteLaw.integrable_expect ν (problem Γ i).outcome
    (measurable_outcome_mass Γ i) (fun r => if E r then 1 else 0)
  have hi' : Integrable (fun act => ((problem Γ i).outcome act).prob E) ν := by
    simpa only [FiniteLaw.prob_eq_expect] using hi
  have hh := integral_mono_ae hi' (integrable_const ε) hbound
  simpa only [integral_const, probReal_univ, one_smul] using hh

theorem mixedCountLaw_prob_tendsto_zero_of_all_bestResponses
    (M C : ℕ → ℕ) (Γ : (k : ℕ) → FiniteGame (M k) n (C k) Seed)
    (i : (k : ℕ) → Fin (M k)) (ν : ℕ → Measure (JointAction n))
    [∀ k, IsProbabilityMeasure (ν k)] (v : ℝ) (j : ℕ)
    (hbr : ∀ k, ∀ᵐ act ∂ν k, (problem (Γ k) (i k)).BestResponse v act)
    (hlim : ∀ ε > 0, ∀ᶠ k in atTop, ∀ act : JointAction n,
      (problem (Γ k) (i k)).BestResponse v act →
      ((problem (Γ k) (i k)).outcome act).prob (fun r => r.val ≠ j) < ε) :
    Tendsto (fun k => (mixedCountLaw (Γ k) (i k) (ν k)).prob (fun r => r.val ≠ j)) atTop (𝓝 0) := by
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro ε hε
    exact Eventually.of_forall fun k => hε.trans_le (FiniteLaw.prob_nonneg _ _)
  · intro ε hε
    filter_upwards [hlim (ε / 2) (half_pos hε)] with k hk
    have hh := mixedCountLaw_prob_le_of_ae (Γ k) (i k) (ν k) (fun r => r.val ≠ j) (ε / 2) (by
      filter_upwards [hbr k] with act hact
      exact (hk act hact).le)
    exact hh.trans_lt (half_lt_self hε)

theorem mixedCountLaw_test_tendsto_of_all_bestResponses
    (M C : ℕ → ℕ) (Γ : (k : ℕ) → FiniteGame (M k) n (C k) Seed)
    (i : (k : ℕ) → Fin (M k)) (ν : ℕ → Measure (JointAction n))
    [∀ k, IsProbabilityMeasure (ν k)] (v : ℝ) (j : Fin (n + 1))
    (hbr : ∀ k, ∀ᵐ act ∂ν k, (problem (Γ k) (i k)).BestResponse v act)
    (hlim : ∀ ε > 0, ∀ᶠ k in atTop, ∀ act : JointAction n,
      (problem (Γ k) (i k)).BestResponse v act →
      ((problem (Γ k) (i k)).outcome act).prob (fun r => r.val ≠ j.val) < ε)
    (f : Fin (n + 1) → ℝ) :
    Tendsto (fun k => (mixedCountLaw (Γ k) (i k) (ν k)).expect f) atTop (𝓝 (f j)) := by
  apply FiniteLaw.tendsto_expect_of_prob_ne _ j _ f
  have hh := mixedCountLaw_prob_tendsto_zero_of_all_bestResponses M C Γ i ν v j.val hbr hlim
  have hpred : (fun r : Fin (n + 1) => r.val ≠ j.val) = (fun r => r ≠ j) := by
    funext r
    apply propext
    constructor
    · intro hne he
      exact hne (congrArg Fin.val he)
    · intro hne he
      exact hne (Fin.ext he)
  rw [hpred] at hh
  exact hh

theorem mixed_bid_tail_eventually_zero_of_all_bestResponses
    (M C : ℕ → ℕ) (Γ : (k : ℕ) → FiniteGame (M k) n (C k) Seed)
    (i : (k : ℕ) → Fin (M k)) (ν : ℕ → Measure (JointAction n))
    (v p : ℝ)
    (hbr : ∀ k, ∀ᵐ act ∂ν k, (problem (Γ k) (i k)).BestResponse v act)
    (hlim : ∀ ε > 0, ∀ᶠ k in atTop, ∀ act : JointAction n,
      (problem (Γ k) (i k)).BestResponse v act → |act.bid - p| < ε) :
    ∀ ε > 0, ∀ᶠ k in atTop, (ν k).real {act | ε ≤ |act.bid - p|} = 0 := by
  intro ε hε
  filter_upwards [hlim ε hε] with k hk
  have hh : ν k {act | ε ≤ |act.bid - p|} = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hbr k] with act hact
    exact not_le_of_gt (hk act hact)
  simp only [Measure.real, hh, ENNReal.toReal_zero]

theorem ae_all_rows_bestResponse
    (M C : ℕ → ℕ) (Γ : (k : ℕ) → FiniteGame (M k) n (C k) Seed)
    (F : Measure ℝ) (hF : ∀ k, (Γ k).F = F) (hΓ : ∀ k, UsersOptimal (Γ k)) :
    ∀ᵐ v ∂F, ∀ k (i : Fin (M k)), ∀ᵐ act ∂(Γ k).σ v, (problem (Γ k) i).BestResponse v act := by
  apply ae_all_iff.mpr
  intro k
  apply ae_all_iff.mpr
  intro i
  rw [← hF k]
  exact hΓ k i

@[simp] lemma mixedCountLaw_strategy_eq_typeOutcome (Γ : FiniteGame m n c Seed)
    (i : Fin m) (v : ℝ) : mixedCountLaw Γ i (Γ.σ v) = typeOutcome Γ i v := rfl

end FCAppendix.Bayes
