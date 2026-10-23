import FCAppendix.CommonReserve.Bayesian
import FCAppendix.CommonReserve.Interim
import FCAppendix.Game.PosteriorFeasible
import FCAppendix.Probability.FiniteAveraging

noncomputable section
namespace FCAppendix.CommonReserve
open Game MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ProbabilityTheory

variable {m n c : ℕ} {r : ℝ} {Seed : Type*} [MeasurableSpace Seed]

namespace FiniteGame

def focalIndicator (Γ : FiniteGame m n c r Seed) (i : Fin m) (j : Fin n)
    (a : Action n r) (ω : Sample m n r Seed) : ℝ :=
  if i ∈ allocation (deviated i a ω) Γ.policy ω.2 j then 1 else 0

theorem measurable_focalIndicator_joint (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (j : Fin n) :
    Measurable (fun p : Action n r × Sample m n r Seed => Γ.focalIndicator i j p.1 p.2) := by
  classical
  have hseed : Measurable (fun p : Action n r × Sample m n r Seed => p.2.2 j) :=
    (measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)
  have ha : Measurable (fun p : Action n r × Sample m n r Seed =>
      allocation (deviated i p.1 p.2) Γ.policy p.2.2 j) :=
    (Γ.policy_measurable j).comp ((measurable_observe_deviated_joint i j).prodMk hseed)
  exact Measurable.ite
    (ha (MeasurableSet.of_discrete : MeasurableSet {S : Finset (Fin m) | i ∈ S}))
    measurable_const measurable_const

theorem focalIndicator_nonneg (Γ : FiniteGame m n c r Seed) (i : Fin m) (j : Fin n)
    (a : Action n r) (ω : Sample m n r Seed) : 0 ≤ Γ.focalIndicator i j a ω := by
  unfold focalIndicator
  split <;> norm_num

theorem focalIndicator_le_one (Γ : FiniteGame m n c r Seed) (i : Fin m) (j : Fin n)
    (a : Action n r) (ω : Sample m n r Seed) : Γ.focalIndicator i j a ω ≤ 1 := by
  unfold focalIndicator
  split <;> norm_num

theorem integrable_focalIndicator (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (j : Fin n) (a : Action n r) :
    Integrable (Γ.focalIndicator i j a) Γ.sampleLaw := by
  have hm : Measurable (Γ.focalIndicator i j a) :=
    Measurable.of_uncurry_left (f := Γ.focalIndicator i j) (x := a)
      (Γ.measurable_focalIndicator_joint i j)
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  exact Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Γ.focalIndicator_nonneg i j a ω)]
    exact Γ.focalIndicator_le_one i j a ω

theorem measurable_focalCount (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (a : Action n r) : Measurable (Γ.focalCount i a) :=
  Measurable.of_uncurry_left (f := Γ.focalCount i) (x := a)
    (Γ.measurable_focalCount_joint i)

theorem integrable_count_test (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (a : Action n r) (f : Fin (n + 1) → ℝ) :
    Integrable (fun ω => f (Γ.focalCount i a ω)) Γ.sampleLaw :=
  CountLaw.integrable_comp Γ.sampleLaw _ (Γ.measurable_focalCount i a) f

@[simp] theorem outcome_expect (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (a : Action n r) (f : Fin (n + 1) → ℝ) :
    (Γ.outcome i a).expect f = ∫ ω, f (Γ.focalCount i a ω) ∂Γ.sampleLaw :=
  CountLaw.expect_ofMeasure Γ.sampleLaw (Γ.focalCount i a) (Γ.measurable_focalCount i a) f

theorem measurable_outcome_expect (Γ : FiniteGame m n c r Seed) (i : Fin m)
    (f : Fin (n + 1) → ℝ) : Measurable (fun a => (Γ.outcome i a).expect f) := by
  simp_rw [outcome_expect]
  exact ((measurable_of_countable f).comp
    (Γ.measurable_focalCount_joint i)).stronglyMeasurable.integral_prod_right'.measurable

theorem measurable_success (Γ : FiniteGame m n c r Seed) (i : Fin m) :
    Measurable (fun a => (Γ.outcome i a).success) := Γ.measurable_outcome_expect i _

theorem measurable_load (Γ : FiniteGame m n c r Seed) (i : Fin m) :
    Measurable (fun a => (Γ.outcome i a).load) := Γ.measurable_outcome_expect i _

theorem measurable_outcome_mass (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (k : Fin (n + 1)) : Measurable (fun a => (Γ.outcome i a).mass k) := by
  simpa only [FiniteLaw.expect_singleton] using
    Γ.measurable_outcome_expect i (fun l => if l = k then 1 else 0)

theorem integrable_outcome_expect (Γ : FiniteGame m n c r Seed) (i : Fin m)
    (ν : Measure (Action n r)) [IsFiniteMeasure ν] (f : Fin (n + 1) → ℝ) :
    Integrable (fun a => (Γ.outcome i a).expect f) ν :=
  FiniteLaw.integrable_expect ν _ (Γ.measurable_outcome_mass i) f

theorem payment_deviated_eq (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (a : Action n r) (ω : Sample m n r Seed) :
    payment (deviated i a ω) Γ.policy ω.2 i =
      ∑ j, Bayes.entryBid (a.val j) * Γ.focalIndicator i j a ω := by
  classical
  simp [payment, accepted, Finset.sum_filter, focalIndicator, deviated, mul_ite]

theorem measurable_payment_joint (Γ : FiniteGame m n c r Seed) (i : Fin m) :
    Measurable (fun p : Action n r × Sample m n r Seed =>
      payment (deviated i p.1 p.2) Γ.policy p.2.2 i) := by
  simp_rw [Γ.payment_deviated_eq]
  apply Finset.measurable_sum
  intro j _
  exact (Bayes.measurable_entryBid.comp
    (((measurable_pi_apply j).comp measurable_subtype_coe).comp measurable_fst)).mul
      (Γ.measurable_focalIndicator_joint i j)

theorem integrable_payment (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (a : Action n r) :
    Integrable (fun ω => payment (deviated i a ω) Γ.policy ω.2 i) Γ.sampleLaw := by
  simp_rw [Γ.payment_deviated_eq]
  exact integrable_finsetSum _ (fun j _ => (Γ.integrable_focalIndicator i j a).const_mul _)

theorem entryBid_nonneg (Γ : FiniteGame m n c r Seed) (a : Action n r) (j : Fin n) :
    0 ≤ Bayes.entryBid (a.val j) := by
  cases he : a.val j with
  | none => simp [Bayes.entryBid]
  | some b => exact Γ.reserve_nonneg.trans (a.property j b he)

theorem payment_nonneg (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (a : Action n r) (ω : Sample m n r Seed) :
    0 ≤ payment (deviated i a ω) Γ.policy ω.2 i := by
  rw [Γ.payment_deviated_eq]
  exact Finset.sum_nonneg fun j _ =>
    mul_nonneg (Γ.entryBid_nonneg a j) (Γ.focalIndicator_nonneg i j a ω)

theorem payment_le_sum_bid (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (a : Action n r) (ω : Sample m n r Seed) :
    payment (deviated i a ω) Γ.policy ω.2 i ≤ ∑ j, Bayes.entryBid (a.val j) := by
  rw [Γ.payment_deviated_eq]
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_of_le_one_right (Γ.entryBid_nonneg a j) (Γ.focalIndicator_le_one i j a ω)

theorem integrable_totalPayment_integrand (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (a : Action n r) :
    Integrable (fun ω => payment (deviated i a ω) Γ.policy ω.2 i +
      Γ.g * Γ.G.charge (count (deviated i a ω) Γ.policy ω.2 i)) Γ.sampleLaw :=
  (Γ.integrable_payment i a).add ((Γ.integrable_count_test i a
    (fun k => Γ.G.charge k.val)).const_mul Γ.g)

theorem measurable_totalPayment (Γ : FiniteGame m n c r Seed) (i : Fin m) :
    Measurable (Γ.totalPayment i) := by
  have hm := (Γ.measurable_payment_joint i).add
    (((measurable_of_countable (fun k : Fin (n + 1) => Γ.G.charge k.val)).comp
      (Γ.measurable_focalCount_joint i)).const_mul Γ.g)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem totalPayment_nonneg (Γ : FiniteGame m n c r Seed) (i : Fin m) (a : Action n r) :
    0 ≤ Γ.totalPayment i a :=
  integral_nonneg fun ω => add_nonneg (Γ.payment_nonneg i a ω)
    (mul_nonneg Γ.g_nonneg (Γ.G.nonneg _ (count_le _ _ _ _)))

theorem totalPayment_le_sum_bid (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (a : Action n r) :
    Γ.totalPayment i a ≤ (∑ j, Bayes.entryBid (a.val j)) + Γ.g * n := by
  have hh := integral_mono (Γ.integrable_totalPayment_integrand i a)
    (integrable_const ((∑ j, Bayes.entryBid (a.val j)) + Γ.g * n)) (fun ω => by
      have hG := Γ.G.upper _ (count_le (deviated i a ω) Γ.policy ω.2 i)
      have hK : (count (deviated i a ω) Γ.policy ω.2 i : ℝ) ≤ n := by
        exact_mod_cast count_le (deviated i a ω) Γ.policy ω.2 i
      exact add_le_add (Γ.payment_le_sum_bid i a ω)
        (mul_le_mul_of_nonneg_left (hG.trans hK) Γ.g_nonneg))
  simpa only [totalPayment, integral_const, probReal_univ, one_smul] using hh

theorem integrable_purePayoff (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (v : ℝ) (a : Action n r) :
    Integrable (fun ω => payoff v Γ.g Γ.G (deviated i a ω) Γ.policy ω.2 i) Γ.sampleLaw := by
  exact (((Γ.integrable_count_test i a (fun k => successIndicator k.val)).const_mul v).sub
    (Γ.integrable_payment i a)).sub
      ((Γ.integrable_count_test i a (fun k => Γ.G.charge k.val)).const_mul Γ.g)

theorem purePayoff_eq (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (v : ℝ) (a : Action n r) :
    Γ.purePayoff i v a = v * (Γ.outcome i a).success - Γ.totalPayment i a := by
  have he : (fun ω : Sample m n r Seed =>
      payoff v Γ.g Γ.G (deviated i a ω) Γ.policy ω.2 i) =
      fun ω => v * successIndicator (Γ.focalCount i a ω).val -
        (payment (deviated i a ω) Γ.policy ω.2 i +
          Γ.g * Γ.G.charge (count (deviated i a ω) Γ.policy ω.2 i)) := by
    funext ω
    dsimp only [payoff, focalCount]
    ring
  unfold purePayoff
  rw [he, integral_sub
    ((Γ.integrable_count_test i a (fun k => successIndicator k.val)).const_mul v)
    (Γ.integrable_totalPayment_integrand i a)]
  simp only [integral_const_mul, CountLaw.success, outcome_expect, totalPayment]

theorem measurable_purePayoff (Γ : FiniteGame m n c r Seed) (i : Fin m) :
    Measurable (fun p : ℝ × Action n r => Γ.purePayoff i p.1 p.2) := by
  simp_rw [Γ.purePayoff_eq]
  exact (measurable_fst.mul ((Γ.measurable_success i).comp measurable_snd)).sub
    ((Γ.measurable_totalPayment i).comp measurable_snd)

theorem totalPayment_floor (Γ : FiniteGame m n c r Seed) (i : Fin m) (a : Action n r) :
    (Γ.g + r) * (Γ.outcome i a).success ≤ Γ.totalPayment i a := by
  have hh := integral_mono
    ((Γ.integrable_count_test i a (fun k => successIndicator k.val)).const_mul (Γ.g + r))
    (Γ.integrable_totalPayment_integrand i a) (fun ω => by
      have hbid := reserve_payment (deviated i a ω) Γ.policy ω.2 i
      have hS := mul_le_mul_of_nonneg_left
        (successIndicator_le_count (count (deviated i a ω) Γ.policy ω.2 i)) Γ.reserve_nonneg
      have hG := mul_le_mul_of_nonneg_left
        (base_charge_ge_success Γ.G _
          (count_le (deviated i a ω) Γ.policy ω.2 i)) Γ.g_nonneg
      dsimp only [focalCount]
      nlinarith)
  simpa only [integral_const_mul, CountLaw.success, outcome_expect, totalPayment] using hh

@[simp] theorem accepted_abstain (Γ : FiniteGame m n c r Seed) (i : Fin m)
    (ω : Sample m n r Seed) : accepted (deviated i abstain ω) Γ.policy ω.2 i = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  have hp := accepted_present (deviated i abstain ω) Γ.policy ω.2 i j hj
  exact hp (by simp [deviated, abstain])

@[simp] theorem count_abstain (Γ : FiniteGame m n c r Seed) (i : Fin m)
    (ω : Sample m n r Seed) : count (deviated i abstain ω) Γ.policy ω.2 i = 0 := by
  simp [count]

@[simp] theorem success_abstain (Γ : FiniteGame m n c r Seed) (i : Fin m) :
    (Γ.outcome i abstain).success = 0 := by
  simp [CountLaw.success, outcome_expect, focalCount, successIndicator]

@[simp] theorem totalPayment_abstain (Γ : FiniteGame m n c r Seed) (i : Fin m) :
    Γ.totalPayment i abstain = 0 := by
  simp [totalPayment, payment, Γ.G.zero]

def interim (Γ : FiniteGame m n c r Seed) (i : Fin m) : InterimProblem (Action n r) where
  g := Γ.g
  r := r
  success := fun a => (Γ.outcome i a).success
  cost := Γ.totalPayment i
  success_nonneg a := (Γ.outcome i a).success_nonneg
  success_le_one a := (Γ.outcome i a).success_le_one
  cost_floor := Γ.totalPayment_floor i
  zero := abstain
  success_zero := Γ.success_abstain i
  cost_zero := Γ.totalPayment_abstain i

@[simp] theorem interim_success (Γ : FiniteGame m n c r Seed) (i : Fin m) (a : Action n r) :
    (Γ.interim i).success a = (Γ.outcome i a).success := rfl

@[simp] theorem interim_cost (Γ : FiniteGame m n c r Seed) (i : Fin m) (a : Action n r) :
    (Γ.interim i).cost a = Γ.totalPayment i a := rfl

@[simp] theorem interim_payoff (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (v : ℝ) (a : Action n r) :
    (Γ.interim i).payoff v a = Γ.purePayoff i v a := (Γ.purePayoff_eq i v a).symm

@[simp] theorem interim_envelope (Γ : FiniteGame m n c r Seed) (i : Fin m) (v : ℝ) :
    (Γ.interim i).envelope v = Γ.envelope i v := by
  unfold InterimProblem.envelope envelope
  rw [show (Γ.interim i).payoff v = Γ.purePayoff i v from funext (Γ.interim_payoff i v)]

@[simp] theorem interim_bestResponse (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (v : ℝ) (a : Action n r) :
    (Γ.interim i).BestResponse v a ↔ ∀ b, Γ.purePayoff i v b ≤ Γ.purePayoff i v a := by
  simp only [InterimProblem.BestResponse, interim_payoff]

theorem interim_identification (Γ : FiniteGame m n c r Seed) (i : Fin m) :
    (∀ a, (Γ.interim i).success a = (Γ.outcome i a).success) ∧
    (∀ a, (Γ.interim i).cost a = Γ.totalPayment i a) ∧
    (∀ v a, (Γ.interim i).payoff v a = Γ.purePayoff i v a) ∧
    (∀ v, (Γ.interim i).envelope v = Γ.envelope i v) :=
  ⟨fun _ => rfl, fun _ => rfl, Γ.interim_payoff i, Γ.interim_envelope i⟩

theorem measurable_envelope (Γ : FiniteGame m n c r Seed) (i : Fin m) :
    Measurable (Γ.envelope i) := by
  have hl : LipschitzWith 1 (Γ.interim i).envelope := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
      (Γ.interim i).envelope_lipschitz_inequality v w
  have he : (Γ.interim i).envelope = Γ.envelope i := funext (Γ.interim_envelope i)
  rw [← he]
  exact hl.continuous.measurable

theorem measurableSet_bestResponse (Γ : FiniteGame m n c r Seed) (i : Fin m) :
    MeasurableSet {p : ℝ × Action n r | (Γ.interim i).BestResponse p.1 p.2} := by
  have he : {p : ℝ × Action n r | (Γ.interim i).BestResponse p.1 p.2} =
      {p | Γ.purePayoff i p.1 p.2 = Γ.envelope i p.1} := by
    ext p
    simpa only [Set.mem_setOf_eq, interim_payoff, interim_envelope] using
      (Γ.interim i).bestResponse_iff_attains p.1 p.2
  rw [he]
  exact measurableSet_eq_fun (Γ.measurable_purePayoff i)
    ((Γ.measurable_envelope i).comp measurable_fst)

theorem ae_bestResponse_userLaw (Γ : FiniteGame m n c r Seed) (hΓ : Γ.UsersOptimal)
    (i : Fin m) : ∀ᵐ p ∂Γ.userLaw, (Γ.interim i).BestResponse p.1 p.2 := by
  apply Measure.ae_compProd_of_ae_ae (Γ.measurableSet_bestResponse i)
  filter_upwards [hΓ i] with v hv
  filter_upwards [hv] with a ha
  exact (Γ.interim_bestResponse i v a).mpr ha

theorem bestResponse_payment_bound (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (v : ℝ) (a : Action n r) (ha : (Γ.interim i).BestResponse v a) :
    0 ≤ Γ.totalPayment i a ∧ Γ.totalPayment i a ≤ max v 0 := by
  have hU := (Γ.interim i).envelope_nonneg v
  have hatt := (Γ.interim i).bestResponse_iff_attains v a |>.mp ha
  have hS0 := (Γ.outcome i a).success_nonneg
  have hS1 := (Γ.outcome i a).success_le_one
  have hvs : v * (Γ.outcome i a).success ≤ max v 0 := by
    by_cases hv : 0 ≤ v
    · rw [max_eq_left hv]
      nlinarith
    · rw [max_eq_right (le_of_not_ge hv)]
      exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hv) hS0
  rw [interim_payoff, Γ.purePayoff_eq] at hatt
  exact ⟨Γ.totalPayment_nonneg i a, by linarith⟩

theorem integrable_totalPayment_of_bestResponse (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (v : ℝ) (ν : Measure (Action n r)) [IsFiniteMeasure ν]
    (hν : ∀ᵐ a ∂ν, (Γ.interim i).BestResponse v a) :
    Integrable (Γ.totalPayment i) ν := by
  apply Integrable.of_bound (Γ.measurable_totalPayment i).aestronglyMeasurable (max v 0)
  filter_upwards [hν] with a ha
  rw [Real.norm_eq_abs, abs_of_nonneg (Γ.totalPayment_nonneg i a)]
  exact (Γ.bestResponse_payment_bound i v a ha).2

theorem mixedOutcome_expect (Γ : FiniteGame m n c r Seed) (i : Fin m)
    (ν : Measure (Action n r)) [IsProbabilityMeasure ν] (f : Fin (n + 1) → ℝ) :
    (Γ.mixedOutcome i ν).expect f = ∫ a, (Γ.outcome i a).expect f ∂ν := by
  rw [mixedOutcome, CountLaw.expect_ofMeasure]
  rw [integral_prod _ (CountLaw.integrable_comp (ν.prod Γ.sampleLaw)
    (fun p => Γ.focalCount i p.1 p.2) (Γ.measurable_focalCount_joint i) f)]
  simp only [outcome_expect]

theorem mixedOutcome_success (Γ : FiniteGame m n c r Seed) (i : Fin m)
    (ν : Measure (Action n r)) [IsProbabilityMeasure ν] :
    (Γ.mixedOutcome i ν).success = ∫ a, (Γ.outcome i a).success ∂ν :=
  Γ.mixedOutcome_expect i ν _

theorem mixed_payment_identity (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (v : ℝ) (ν : Measure (Action n r)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ a ∂ν, (Γ.interim i).BestResponse v a) :
    (∫ a, Γ.totalPayment i a ∂ν) =
      v * (Γ.mixedOutcome i ν).success - Γ.envelope i v := by
  have he : Γ.totalPayment i =ᵐ[ν]
      fun a => v * (Γ.outcome i a).success - Γ.envelope i v := by
    filter_upwards [hν] with a ha
    have hh := (Γ.interim i).bestResponse_iff_attains v a |>.mp ha
    rw [interim_payoff, interim_envelope, Γ.purePayoff_eq] at hh
    linarith
  have hS : Integrable (fun a => (Γ.outcome i a).success) ν :=
    Γ.integrable_outcome_expect i ν (fun k => successIndicator k.val)
  rw [integral_congr_ae he,
    integral_sub (hS.const_mul v) (integrable_const _),
    integral_const_mul, integral_const, probReal_univ, one_smul,
    ← Γ.mixedOutcome_success i ν]

theorem integrable_mixed_payment_integrand (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (v : ℝ) (ν : Measure (Action n r)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ a ∂ν, (Γ.interim i).BestResponse v a) :
    Integrable (fun p : Action n r × Sample m n r Seed =>
      payment (deviated i p.1 p.2) Γ.policy p.2.2 i +
        Γ.g * Γ.G.charge (count (deviated i p.1 p.2) Γ.policy p.2.2 i))
      (ν.prod Γ.sampleLaw) := by
  have hmeas : Measurable (fun p : Action n r × Sample m n r Seed =>
      payment (deviated i p.1 p.2) Γ.policy p.2.2 i +
        Γ.g * Γ.G.charge (count (deviated i p.1 p.2) Γ.policy p.2.2 i)) :=
    (Γ.measurable_payment_joint i).add
      (((measurable_of_countable (fun k : Fin (n + 1) => Γ.G.charge k.val)).comp
        (Γ.measurable_focalCount_joint i)).const_mul Γ.g)
  apply (integrable_prod_iff hmeas.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall (Γ.integrable_totalPayment_integrand i), ?_⟩
  have he : (fun a => ∫ ω, ‖payment (deviated i a ω) Γ.policy ω.2 i +
      Γ.g * Γ.G.charge (count (deviated i a ω) Γ.policy ω.2 i)‖ ∂Γ.sampleLaw) =
      Γ.totalPayment i := by
    funext a
    apply integral_congr_ae
    exact Eventually.of_forall fun ω => by
      dsimp only
      rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (Γ.payment_nonneg i a ω)
        (mul_nonneg Γ.g_nonneg (Γ.G.nonneg _ (count_le _ _ _ _))))]
  rw [he]
  exact Γ.integrable_totalPayment_of_bestResponse i v ν hν

theorem mixed_actual_payment_identity (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (v : ℝ) (ν : Measure (Action n r)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ a ∂ν, (Γ.interim i).BestResponse v a) :
    (∫ p : Action n r × Sample m n r Seed,
      payment (deviated i p.1 p.2) Γ.policy p.2.2 i +
        Γ.g * Γ.G.charge (count (deviated i p.1 p.2) Γ.policy p.2.2 i)
      ∂ν.prod Γ.sampleLaw) =
      v * (Γ.mixedOutcome i ν).success - Γ.envelope i v := by
  rw [integral_prod _ (Γ.integrable_mixed_payment_integrand i v ν hν)]
  exact Γ.mixed_payment_identity i v ν hν

theorem ae_integrable_strategy_totalPayment (Γ : FiniteGame m n c r Seed)
    (hΓ : Γ.UsersOptimal) (i : Fin m) :
    ∀ᵐ v ∂Γ.F, Integrable (Γ.totalPayment i) (Γ.σ v) := by
  filter_upwards [hΓ i] with v hv
  exact Γ.integrable_totalPayment_of_bestResponse i v (Γ.σ v) (by
    filter_upwards [hv] with a ha
    exact (Γ.interim_bestResponse i v a).mpr ha)

theorem ae_integrable_actual_type_payment (Γ : FiniteGame m n c r Seed)
    (hΓ : Γ.UsersOptimal) (i : Fin m) :
    ∀ᵐ v ∂Γ.F, Integrable (fun p : Action n r × Sample m n r Seed =>
      payment (deviated i p.1 p.2) Γ.policy p.2.2 i +
        Γ.g * Γ.G.charge (count (deviated i p.1 p.2) Γ.policy p.2.2 i))
      ((Γ.σ v).prod Γ.sampleLaw) := by
  filter_upwards [hΓ i] with v hv
  exact Γ.integrable_mixed_payment_integrand i v (Γ.σ v) (by
    filter_upwards [hv] with a ha
    exact (Γ.interim_bestResponse i v a).mpr ha)

theorem ae_type_payment_identity (Γ : FiniteGame m n c r Seed)
    (hΓ : Γ.UsersOptimal) (i : Fin m) :
    ∀ᵐ v ∂Γ.F, (∫ a, Γ.totalPayment i a ∂Γ.σ v) =
      v * (Γ.typeOutcome i v).success - Γ.envelope i v := by
  filter_upwards [hΓ i] with v hv
  exact Γ.mixed_payment_identity i v (Γ.σ v) (by
    filter_upwards [hv] with a ha
    exact (Γ.interim_bestResponse i v a).mpr ha)

end FiniteGame
end FCAppendix.CommonReserve
