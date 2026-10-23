import FCAppendix.CommonReserve.AnonymousDeviationBridge
import FCAppendix.CommonReserve.MixedInterim

noncomputable section
namespace FCAppendix.CommonReserve
open Game MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ProbabilityTheory

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def anonymousPaymentError (Γ : Bayes.FiniteGame m n c Seed)
    (i : Fin m) (p : ℝ) (a : JointAction n) : ℝ :=
  max (p - a.bid) 0 * ((Bayes.problem Γ i).outcome a).load

theorem measurable_anonymousPaymentError (Γ : Bayes.FiniteGame m n c Seed)
    (i : Fin m) (p : ℝ) : Measurable (anonymousPaymentError Γ i p) :=
  ((measurable_const.sub (measurable_bid n)).max measurable_const).mul
    (Bayes.measurable_outcome_expect Γ i _)

theorem anonymousPaymentError_nonneg (Γ : Bayes.FiniteGame m n c Seed)
    (i : Fin m) (p : ℝ) (a : JointAction n) : 0 ≤ anonymousPaymentError Γ i p a :=
  mul_nonneg (le_max_right _ _) (CountLaw.load_nonneg _)

theorem anonymousPaymentError_le (Γ : Bayes.FiniteGame m n c Seed)
    (i : Fin m) (p : ℝ) (a : JointAction n) :
    anonymousPaymentError Γ i p a ≤ (n : ℝ) * max p 0 := by
  have hg : max (p - a.bid) 0 ≤ max p 0 :=
    max_le_max (sub_le_self _ a.bid_nonneg) le_rfl
  exact (mul_le_mul hg (CountLaw.load_le_n _) (CountLaw.load_nonneg _)
    (le_max_right _ _)).trans_eq (mul_comm _ _)

theorem integrable_anonymousPaymentError (Γ : Bayes.FiniteGame m n c Seed)
    (i : Fin m) (p : ℝ) (ν : Measure (JointAction n)) [IsFiniteMeasure ν] :
    Integrable (anonymousPaymentError Γ i p) ν := by
  apply Integrable.of_bound (measurable_anonymousPaymentError Γ i p).aestronglyMeasurable
    ((n : ℝ) * max p 0)
  exact Eventually.of_forall fun a => by
    rw [Real.norm_eq_abs, abs_of_nonneg (anonymousPaymentError_nonneg Γ i p a)]
    exact anonymousPaymentError_le Γ i p a

theorem anonymous_payoff_le_price_error (Γ : Bayes.FiniteGame m n c Seed)
    (hA : Γ.A = Schedule.ppi n) (i : Fin m) (p v : ℝ) (a : JointAction n) :
    (Bayes.problem Γ i).payoff v a ≤
      (v - Γ.g - p) * ((Bayes.problem Γ i).outcome a).success -
        p * ((Bayes.problem Γ i).outcome a).duplicates + anonymousPaymentError Γ i p a := by
  have hG := mul_le_mul_of_nonneg_left
    (((Bayes.problem Γ i).outcome a).success_le_charge Γ.G) Γ.g_nonneg
  have hgap := mul_le_mul_of_nonneg_right (le_max_left (p - a.bid) 0)
    (((Bayes.problem Γ i).outcome a).load_nonneg)
  change ((Bayes.problem Γ i).outcome a).utility v a.bid Γ.g Γ.A Γ.G ≤ _
  rw [CountLaw.utility_eq, hA, CountLaw.charge_ppi]
  unfold CountLaw.duplicates anonymousPaymentError
  nlinarith

theorem anonymous_envelope_le_mixed_price_error (Γ : Bayes.FiniteGame m n c Seed)
    (r : ℝ) (hr : 0 ≤ r) (hT : ∀ j, UniformReserveRule Γ.seedLaw (Γ.policy j) r)
    (hA : Γ.A = Schedule.ppi n) (i : Fin m) (p v : ℝ)
    (ν : Measure (JointAction n)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ a ∂ν, (Bayes.problem Γ i).BestResponse v a) :
    (Bayes.problem Γ i).envelope v ≤
      (v - Γ.g - p) * (Bayes.mixedCountLaw Γ i ν).success -
        p * (Bayes.mixedCountLaw Γ i ν).duplicates + ∫ a, anonymousPaymentError Γ i p a ∂ν := by
  let P := anonymousInterim Γ r hr hT i
  have he : (Bayes.problem Γ i).payoff v =ᵐ[ν] fun _ => (Bayes.problem Γ i).envelope v := by
    filter_upwards [hν] with a ha
    simpa only [P, anonymousInterim_payoff, anonymousInterim_envelope] using
      (P.bestResponse_iff_attains v a).mp ((anonymousInterim_bestResponse Γ r hr hT i v a).mpr ha)
  have hi : Integrable ((Bayes.problem Γ i).payoff v) ν := (integrable_const _).congr he.symm
  have hS : Integrable (fun a => ((Bayes.problem Γ i).outcome a).success) ν :=
    FiniteLaw.integrable_expect ν (Bayes.problem Γ i).outcome
      (Bayes.measurable_outcome_mass Γ i) (fun k => successIndicator k.val)
  have hD : Integrable (fun a => ((Bayes.problem Γ i).outcome a).duplicates) ν := by
    simpa only [CountLaw.duplicates_eq_expect] using
      FiniteLaw.integrable_expect ν (Bayes.problem Γ i).outcome
        (Bayes.measurable_outcome_mass Γ i) (fun k => (k.val : ℝ) - successIndicator k.val)
  have hR₀ : Integrable (fun a =>
      (v - Γ.g - p) * ((Bayes.problem Γ i).outcome a).success -
        p * ((Bayes.problem Γ i).outcome a).duplicates) ν :=
    (hS.const_mul _).sub (hD.const_mul _)
  have hR : Integrable (fun a =>
      (v - Γ.g - p) * ((Bayes.problem Γ i).outcome a).success -
        p * ((Bayes.problem Γ i).outcome a).duplicates + anonymousPaymentError Γ i p a) ν :=
    hR₀.add (integrable_anonymousPaymentError Γ i p ν)
  have hh := integral_mono hi hR (anonymous_payoff_le_price_error Γ hA i p v)
  rw [integral_congr_ae he, integral_const, probReal_univ, one_smul,
    integral_add hR₀
      (integrable_anonymousPaymentError Γ i p ν),
    integral_sub (hS.const_mul _) (hD.const_mul _), integral_const_mul, integral_const_mul] at hh
  simpa only [CountLaw.success, CountLaw.duplicates_eq_expect,
    Bayes.mixedCountLaw_expect] using hh

def anonymousTypePaymentError (Γ : Bayes.FiniteGame m n c Seed)
    (i : Fin m) (p v : ℝ) : ℝ := ∫ a, anonymousPaymentError Γ i p a ∂Γ.σ v

theorem measurable_anonymousTypePaymentError (Γ : Bayes.FiniteGame m n c Seed)
    (i : Fin m) (p : ℝ) : Measurable (anonymousTypePaymentError Γ i p) :=
  ((measurable_anonymousPaymentError Γ i p).comp
    (show Measurable (fun x : ℝ × JointAction n => x.2) from measurable_snd)).stronglyMeasurable.integral_kernel_prod_right'.measurable

theorem anonymousTypePaymentError_nonneg (Γ : Bayes.FiniteGame m n c Seed)
    (i : Fin m) (p v : ℝ) : 0 ≤ anonymousTypePaymentError Γ i p v :=
  integral_nonneg (anonymousPaymentError_nonneg Γ i p)

theorem anonymousTypePaymentError_le (Γ : Bayes.FiniteGame m n c Seed)
    (i : Fin m) (p v : ℝ) : anonymousTypePaymentError Γ i p v ≤ (n : ℝ) * max p 0 := by
  have h := integral_mono (integrable_anonymousPaymentError Γ i p (Γ.σ v))
    (integrable_const ((n : ℝ) * max p 0)) (anonymousPaymentError_le Γ i p)
  simpa only [anonymousTypePaymentError, integral_const, probReal_univ, one_smul] using h

theorem integrable_anonymousTypePaymentError (Γ : Bayes.FiniteGame m n c Seed)
    (i : Fin m) (p : ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (anonymousTypePaymentError Γ i p) μ := by
  apply Integrable.of_bound (measurable_anonymousTypePaymentError Γ i p).aestronglyMeasurable
    ((n : ℝ) * max p 0)
  exact Eventually.of_forall fun v => by
    rw [Real.norm_eq_abs, abs_of_nonneg (anonymousTypePaymentError_nonneg Γ i p v)]
    exact anonymousTypePaymentError_le Γ i p v

theorem anonymous_ae_envelope_le_type_price_error (Γ : Bayes.FiniteGame m n c Seed)
    (r : ℝ) (hr : 0 ≤ r) (hT : ∀ j, UniformReserveRule Γ.seedLaw (Γ.policy j) r)
    (hA : Γ.A = Schedule.ppi n) (i : Fin m) (p : ℝ) (hu : Bayes.UsersOptimal Γ) :
    ∀ᵐ v ∂Γ.F, (Bayes.problem Γ i).envelope v ≤
      (v - Γ.g - p) * (Bayes.typeOutcome Γ i v).success -
        p * (Bayes.typeOutcome Γ i v).duplicates + anonymousTypePaymentError Γ i p v := by
  filter_upwards [hu i] with v hv
  exact anonymous_envelope_le_mixed_price_error Γ r hr hT hA i p v (Γ.σ v) hv

theorem routed_shortfall_eq_common (Γ : Bayes.FiniteGame m n c Seed)
    (r p : ℝ) (hr : 0 ≤ r) (ω : Bayes.Background m n Seed) (i : Fin m) :
    shortfall p (FiniteGame.actualProfile (routedSample r ω)) Γ.policy ω.2 i =
      max (p - (ω.1 i).1.2.bid) 0 *
        ((routedSource Γ r hr).playedCount i (routedSample r ω)).val := by
  classical
  let x := FiniteGame.actualProfile (routedSample r ω)
  have hentry (j : Fin n) (hj : j ∈ accepted x Γ.policy ω.2 i) :
      Bayes.entryBid ((x i).val j) = (ω.1 i).1.2.bid := by
    have hn := accepted_present x Γ.policy ω.2 i j hj
    change Bayes.entryBid ((routedAction r (ω.1 i)).val j) = _
    change (routedAction r (ω.1 i)).val j ≠ none at hn
    by_cases h : r ≤ (ω.1 i).1.2.bid ∧
        j ∈ firstK (ω.1 i).2 (ω.1 i).1.2.routeCount
    · simp [routedAction, h, Bayes.entryBid]
    · exact (hn (by simp [routedAction, h])).elim
  unfold shortfall
  change (∑ j ∈ accepted x Γ.policy ω.2 i, max (p - Bayes.entryBid ((x i).val j)) 0) = _
  rw [Finset.sum_congr rfl (fun j hj => by rw [hentry j hj])]
  simp only [Finset.sum_const, nsmul_eq_mul, FiniteGame.playedCount, count, routedSource]
  change ((accepted x Γ.policy ω.2 i).card : ℝ) * max (p - (ω.1 i).1.2.bid) 0 =
    max (p - (ω.1 i).1.2.bid) 0 * ((accepted x Γ.policy ω.2 i).card : ℝ)
  ring

theorem anonymous_integral_typePaymentError_eq_routed (Γ : Bayes.FiniteGame m n c Seed)
    (r : ℝ) (hr : 0 ≤ r) (hT : ∀ j, UniformReserveRule Γ.seedLaw (Γ.policy j) r)
    (i : Fin m) (p : ℝ) :
    (∫ v, anonymousTypePaymentError Γ i p v ∂Γ.F) =
      ∫ v, (routedSource Γ r hr).typePaymentError i p v ∂(routedSource Γ r hr).F := by
  let Γ' := routedSource Γ r hr
  let f : (ℝ × JointAction n) × Fin (n + 1) → ℝ :=
    fun z => max (p - z.1.2.bid) 0 * (z.2.val : ℝ)
  have hf : Measurable f :=
    ((measurable_const.sub ((measurable_bid n).comp
      (measurable_snd.comp measurable_fst))).max measurable_const).mul
      ((measurable_of_countable (fun k : Fin (n + 1) => (k.val : ℝ))).comp measurable_snd)
  have hB (z : (ℝ × JointAction n) × Fin (n + 1)) : ‖f z‖ ≤ (n : ℝ) * max p 0 := by
    have h0 : 0 ≤ f z := mul_nonneg (le_max_right _ _) (Nat.cast_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    have hg : max (p - z.1.2.bid) 0 ≤ max p 0 :=
      max_le_max (sub_le_self _ z.1.2.bid_nonneg) le_rfl
    have hk : (z.2.val : ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt_succ z.2.isLt
    exact (mul_le_mul hg hk (Nat.cast_nonneg _) (le_max_right _ _)).trans_eq (mul_comm _ _)
  have hactual : (∫ v, anonymousTypePaymentError Γ i p v ∂Γ.F) =
      ∫ ω, max (p - (ω.1 i).1.2.bid) 0 * (Bayes.playedCount Γ i ω).val
        ∂Bayes.backgroundLaw Γ := by
    have hi := Bayes.integrable_interim_expect Γ i f hf ((n : ℝ) * max p 0) hB
    have he := Bayes.integral_realized_eq_interim Γ i f hf ((n : ℝ) * max p 0) hB
    simp only [f, FiniteLaw.expect_const_mul] at hi he
    rw [he, Measure.integral_compProd hi]
    rfl
  rw [hactual, Γ'.integral_typePaymentError_eq_actual]
  have hp := routedSample_measurePreserving Γ r hr
  have hMeas := Γ'.measurable_actual_shortfall i p
  rw [← hp.map_eq, integral_map_of_stronglyMeasurable hp.measurable hMeas.stronglyMeasurable]
  change (∫ ω, max (p - (ω.1 i).1.2.bid) 0 * (Bayes.playedCount Γ i ω).val
      ∂Bayes.backgroundLaw Γ) =
    ∫ ω, shortfall p (FiniteGame.actualProfile (routedSample r ω)) Γ.policy ω.2 i
      ∂Bayes.backgroundLaw Γ
  have hiRaw : Integrable (fun ω =>
      max (p - (ω.1 i).1.2.bid) 0 * (Bayes.playedCount Γ i ω).val)
      (Bayes.backgroundLaw Γ) :=
    Bayes.integrable_realized_statistic Γ i f hf ((n : ℝ) * max p 0) hB
  have hiRoute : Integrable (fun ω : Bayes.Background m n Seed =>
      shortfall p (FiniteGame.actualProfile (routedSample r ω)) Γ.policy ω.2 i)
      (Bayes.backgroundLaw Γ) := by
    apply Integrable.of_bound (hMeas.comp hp.measurable).aestronglyMeasurable ((n : ℝ) * max p 0)
    exact Eventually.of_forall fun ω => by
      change ‖shortfall p (FiniteGame.actualProfile (routedSample r ω)) Γ.policy ω.2 i‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (shortfall_nonneg p _ _ _ _)]
      exact Γ'.actual_shortfall_le i p (routedSample r ω)
  rw [show Bayes.backgroundLaw Γ = (Measure.pi fun _ : Fin m => Bayes.userLaw Γ).prod
      (Measure.pi fun _ : Fin n => Γ.seedLaw) from rfl,
    integral_prod _ hiRaw, integral_prod _ hiRoute]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro d
  simp_rw [routed_shortfall_eq_common Γ r p hr, integral_const_mul]
  exact congrArg (fun z : ℝ => max (p - (d i).1.2.bid) 0 * z)
    (integral_routed_playedCount_seed Γ r hr hT d i (fun k => (k.val : ℝ))).symm

end FCAppendix.CommonReserve
