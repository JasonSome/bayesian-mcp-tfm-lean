import FCAppendix.CommonReserve.Source
import FCAppendix.CommonReserve.AnalyticClosure
import FCAppendix.CommonReserve.RateChoice
import FCAppendix.CommonReserve.BidTightness
import FCAppendix.CommonReserve.SingletonEstimate
import FCAppendix.CommonReserve.ActualIdentityBounds

noncomputable section
namespace FCAppendix.CommonReserve
open Game MeasureTheory ProbabilityTheory Filter Set Topology

variable {n : ℕ} {r : ℝ} {Seed : Type*} [MeasurableSpace Seed]
  {M C : ℕ → ℕ} {Γ : ∀ k, FiniteGame (M k) n (C k) r Seed}
  {F : Measure ℝ} [IsProbabilityMeasure F] {g ρ vstar : ℝ}

namespace SourceAssumptions

theorem price_bounded (h : SourceAssumptions M C Γ F g ρ vstar) :
    ∃ B : ℝ, ∀ k, price (Γ k) (marketSlack (M k) (C k)) ≤ B := by
  apply bounded_reserve_prices M C Γ F g ρ (by have := h.proposers; omega)
    h.users_pos h.capacity_pos
    h.rho_pos h.capacity_tendsto
  intro k j b hb
  have hb' : (n : ℝ) * (Γ k).g ≤ b := by simpa only [h.base k] using hb
  simpa only [h.base k, h.law k] using bid_tail_from_values (Γ k) (h.users_pos k)
    (h.capacity_pos k) h.proposers (h.optimal k) (h.uniform_ties k) j b hb'

theorem estimates (h : SourceAssumptions M C Γ F g ρ vstar)
    (i : ∀ k, Fin (M k)) :
    ReserveAnalysis.Estimates F g r ρ
      (fun k => price (Γ k) (marketSlack (M k) (C k)))
      (fun k => (C k : ℝ) / M k)
      (fun k v => (Γ k).typeOutcome (i k) v)
      (fun k v => (Γ k).envelope (i k) v)
      (fun k v => (Γ k).typePaymentError (i k)
        (price (Γ k) (marketSlack (M k) (C k))) v)
      (fun k v => marketSlack (M k) (C k) +
        singletonFailure (M k) (C k) * max (v - g) 0)
      (fun k => (n : ℝ) * slotError (M k) (C k)) := by
  have hn : 0 < n := by have := h.proposers; omega
  have hd k := marketSlack_pos (M k) (C k) (h.users_pos k) (h.capacity_pos k)
  have hdκ k := marketSlack_lt_capacity (M k) (C k) (h.users_pos k) (h.capacity_pos k)
  have hP k := price_nonneg (Γ k) (marketSlack (M k) (C k)) hn (hdκ k)
  have hη k := slotError_nonneg (M k) (C k) (h.users_pos k) (h.capacity_pos k)
  have hd0 := marketSlack_tendsto M C ρ h.rho_pos h.users_tendsto h.capacity_tendsto
  have hf0 := singletonFailure_tendsto M C ρ h.rho_pos h.users_tendsto h.capacity_tendsto
  have hη0 := slotError_tendsto M C ρ h.rho_pos h.users_tendsto h.capacity_tendsto
  refine {
    reserve_nonneg := (Γ 0).reserve_nonneg
    reserve_le := fun k => reserve_le_price (Γ k) _ hn (hdκ k)
    price_bounded := h.price_bounded
    capacity_limit := h.capacity_tendsto
    success_measurable := ?_
    duplicates_measurable := ?_
    utility_nonneg := ?_
    utility_monotone := ?_
    utility_lipschitz := ?_
    reserve_ceiling := ?_
    error_nonneg := ?_
    error_integrable := ?_
    error_mean := ?_
    deviation_nonneg := ?_
    deviation_limit := ?_
    payment_upper := ?_
    singleton_lower := ?_
    load_upper := ?_
    load_lower := ?_
    shortfall_limit := by simpa only [mul_zero] using hη0.const_mul (n : ℝ) }
  · intro k
    exact ((Γ k).measurable_typeOutcome_expect (i k) _).aestronglyMeasurable
  · intro k
    exact (((Γ k).measurable_typeOutcome_expect (i k) (fun z => (z.val : ℝ))).sub
      ((Γ k).measurable_typeOutcome_expect (i k) (fun z => successIndicator z.val))).aestronglyMeasurable
  · intro k v
    simpa only [FiniteGame.interim_envelope] using ((Γ k).interim (i k)).envelope_nonneg v
  · intro k v w hvw
    simpa only [FiniteGame.interim_envelope] using
      ((Γ k).interim (i k)).envelope_monotone hvw
  · intro k v w
    simpa only [FiniteGame.interim_envelope] using
      ((Γ k).interim (i k)).envelope_lipschitz_inequality v w
  · intro k v
    have hh := ((Γ k).interim (i k)).envelope_upper v
    rw [FiniteGame.interim_envelope] at hh
    change (Γ k).envelope (i k) v ≤ max (v - ((Γ k).g + r)) 0 at hh
    simpa only [h.base k, sub_add_eq_sub_sub] using hh
  · intro k
    exact ae_of_all _ ((Γ k).typePaymentError_nonneg (i k) _)
  · intro k
    exact (Γ k).integrable_typePaymentError (i k) _ F
  · obtain ⟨B, hB⟩ := h.price_bounded
    have hB0 : 0 ≤ B := (hP 0).trans (hB 0)
    apply squeeze_zero
      (fun k => integral_nonneg ((Γ k).typePaymentError_nonneg (i k) _))
      (g := fun k => (2 * (n : ℝ) * B) * slotError (M k) (C k))
    · intro k
      have hb := integral_typePaymentError_le (Γ k) (h.users_pos k) hn
        (marketSlack (M k) (C k)) (hd k).le (hdκ k) (h.uniform_ties k) (i k)
      rw [h.law k] at hb
      exact hb.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hB k) (by positivity)) (hη k))
    · simpa only [mul_zero] using hη0.const_mul (2 * (n : ℝ) * B)
  · intro k v
    exact add_nonneg (hd k).le
      (mul_nonneg (singletonFailure_nonneg _ _) (le_max_right _ _))
  · intro v
    simpa only [zero_mul, zero_add] using hd0.add (hf0.mul_const (max (v - g) 0))
  · intro k
    simpa only [h.law k, h.base k] using
      (Γ k).ae_envelope_le_type_price_error (i k) _ (h.optimal k)
  · intro k v
    obtain ⟨j, hb, hS⟩ := singleton_at_min_quantile (Γ k) (h.users_pos k)
      (h.capacity_lt_users k).le hn (i k) (marketSlack (M k) (C k))
      (marketSlack (M k) (C k)) (hd k) (hdκ k) (hd k) (h.uniform_ties k)
    have hS' : 1 - singletonFailure (M k) (C k) ≤
        ((Γ k).outcome (i k) (singleton j
          (price (Γ k) (marketSlack (M k) (C k)) + marketSlack (M k) (C k)) hb)).success := by
      have hf := binomialFailure_le (M k) (C k) (h.users_pos k) (h.capacity_pos k)
      linarith
    simpa only [h.base k] using (Γ k).singleton_envelope_lower (i k) j
      (price (Γ k) (marketSlack (M k) (C k))) (marketSlack (M k) (C k))
      (singletonFailure (M k) (C k)) v (hP k) (hd k).le
      (singletonFailure_nonneg _ _) hb hS'
  · intro k
    simpa only [h.law k] using
      integral_typeLoad_le_capacity (Γ k) (h.uniform_ties k) (i k)
  · intro k hPr
    simpa only [h.law k, slotError] using
      integral_typeLoad_lower_of_price_gt_reserve (Γ k) (h.users_pos k)
        (marketSlack (M k) (C k)) (hd k).le hPr (h.uniform_ties k) (i k)

theorem utility_and_counts [NullSingletonClass F]
    (h : SourceAssumptions M C Γ F g ρ vstar) (i : ∀ k, Fin (M k)) :
    (∀ v, Tendsto (fun k => (Γ k).envelope (i k) v) atTop
      (𝓝 (max (v - g - max r (vstar - g)) 0))) ∧
    Tendsto (fun k => (∫ v, ((Γ k).typeOutcome (i k) v).success ∂F,
      (∫ v, ((Γ k).typeOutcome (i k) v).duplicates ∂F,
        ∫ v, ((Γ k).typeOutcome (i k) v).load ∂F))) atTop
      (𝓝 (F.real (Ioi (g + max r (vstar - g))),
        (0, F.real (Ioi (g + max r (vstar - g)))))) :=
  (h.estimates i).full_limits vstar h.scarcity h.cutoff
    h.density.interval_mass.1 h.density.interval_mass.2

end SourceAssumptions
end FCAppendix.CommonReserve
