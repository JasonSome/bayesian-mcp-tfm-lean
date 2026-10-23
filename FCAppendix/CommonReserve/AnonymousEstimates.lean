import FCAppendix.CommonReserve.AnonymousSource
import FCAppendix.CommonReserve.AnonymousPaymentError
import FCAppendix.CommonReserve.ActualIdentityBounds
import FCAppendix.CommonReserve.SingletonEstimate
import FCAppendix.CommonReserve.AnalyticClosure
import FCAppendix.CommonReserve.RateChoice
import FCAppendix.Finite.PPIRankTypes

noncomputable section
namespace FCAppendix.CommonReserve
open Game MeasureTheory ProbabilityTheory Filter Set Topology

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem anonymous_singleton_at_price (Γ : Bayes.FiniteGame m n c Seed)
    (r : ℝ) (hr : 0 ≤ r) (hT : ∀ j, UniformReserveRule Γ.seedLaw (Γ.policy j) r)
    (hm : 0 < m) (hc : c ≤ m) (hn : 0 < n) (i : Fin m)
    (δ d : ℝ) (hδ : 0 < δ) (hδκ : δ < (c : ℝ) / m) (hd : 0 < d) :
    ∃ hb : r ≤ price (routedSource Γ r hr) δ + d,
      1 - ((m - 1 : ℕ) : ℝ) / (4 * ((m : ℝ) * δ) ^ 2) ≤
        ((Bayes.problem Γ i).outcome
          (⟨price (routedSource Γ r hr) δ + d, hr.trans hb, 1, hn⟩ : JointAction n)).success := by
  let Γ' := routedSource Γ r hr
  have hPr : r ≤ price Γ' δ := reserve_le_price Γ' δ hn hδκ
  have hb : r ≤ price Γ' δ + d := by linarith
  refine ⟨hb, anonymous_singleton_success_lower Γ r hr hT hn i
    (price Γ' δ + d) (((m - 1 : ℕ) : ℝ) / (4 * ((m : ℝ) * δ) ^ 2)) hb ?_⟩
  intro j
  obtain ⟨hb', hS⟩ := singleton_at_quantile Γ' hm hc i j δ d hδ hδκ hd (hT j)
  have he : quantile Γ' j δ = price Γ' δ :=
    (routed_price_eq_quantile Γ r hr j δ).symm
  simpa only [he] using hS

theorem anonymous_singleton_envelope_lower (Γ : Bayes.FiniteGame m n c Seed)
    (hn : 0 < n) (i : Fin m) (p d ε v : ℝ) (hp : 0 ≤ p) (hd : 0 ≤ d)
    (hε : 0 ≤ ε)
    (hS : 1 - ε ≤ ((Bayes.problem Γ i).outcome
      (⟨p + d, add_nonneg hp hd, 1, hn⟩ : JointAction n)).success) :
    max (v - Γ.g - p) 0 - (d + ε * max (v - Γ.g) 0) ≤
      (Bayes.problem Γ i).envelope v := by
  let a : JointAction n := ⟨p + d, add_nonneg hp hd, 1, hn⟩
  have hs : 1 - ε ≤ Bayes.meanAcceptProb Γ i a.bid := by
    rw [← Bayes.singleton_success Γ hn i a rfl]
    exact hS
  have hu := Bayes.envelope_lower_singleton Γ hn i a rfl ε hε hs v
  have hg : max (v - Γ.g - p) 0 ≤ max (v - Γ.g - (p + d)) 0 + d := by
    apply max_le
    · have h := le_max_left (v - Γ.g - (p + d)) 0
      linarith
    · exact add_nonneg (le_max_right _ _) hd
  dsimp only [a] at hu
  linarith

variable {M C : ℕ → ℕ} {Γ : ∀ k, Bayes.FiniteGame (M k) n (C k) Seed}
  {F : Measure ℝ} [IsProbabilityMeasure F] {g r ρ vstar : ℝ}

namespace AnonymousSourceAssumptions

theorem price_bounded (h : AnonymousSourceAssumptions M C Γ F g r ρ vstar) :
    ∃ B : ℝ, ∀ k, price (routedSource (Γ k) r h.reserve_nonneg)
      (marketSlack (M k) (C k)) ≤ B := by
  have hg : 0 ≤ g := by rw [← h.base 0]; exact (Γ 0).g_nonneg
  apply bounded_reserve_prices M C (fun k => routedSource (Γ k) r h.reserve_nonneg)
    F g ρ (by have := h.proposers; omega) h.users_pos h.capacity_pos h.rho_pos h.capacity_tendsto
  intro k j b hb
  rw [routed_bidTail_eq]
  have hb0 : 0 ≤ b := (mul_nonneg (Nat.cast_nonneg _) hg).trans hb
  have ht := anonymous_eligible_tail_le_value_tail (Γ k) r (h.users_pos k)
    (h.capacity_pos k) (h.optimal k) (h.uniform_ties k) j b hb0
  rw [h.law k, h.base k] at ht
  apply ht.trans
  exact measureReal_mono (Ioi_subset_Ioi (by nlinarith [mul_nonneg (Nat.cast_nonneg n) hg]))

theorem estimates (h : AnonymousSourceAssumptions M C Γ F g r ρ vstar)
    (i : ∀ k, Fin (M k)) :
    ReserveAnalysis.Estimates F g r ρ
      (fun k => price (routedSource (Γ k) r h.reserve_nonneg) (marketSlack (M k) (C k)))
      (fun k => (C k : ℝ) / M k)
      (fun k v => Bayes.typeOutcome (Γ k) (i k) v)
      (fun k v => (Bayes.problem (Γ k) (i k)).envelope v)
      (fun k v => anonymousTypePaymentError (Γ k) (i k)
        (price (routedSource (Γ k) r h.reserve_nonneg) (marketSlack (M k) (C k))) v)
      (fun k v => marketSlack (M k) (C k) + singletonFailure (M k) (C k) * max (v - g) 0)
      (fun k => (n : ℝ) * slotError (M k) (C k)) := by
  let Ψ := fun k => routedSource (Γ k) r h.reserve_nonneg
  let P := fun k => anonymousInterim (Γ k) r h.reserve_nonneg (h.uniform_ties k) (i k)
  have hn : 0 < n := by have := h.proposers; omega
  have hd k := marketSlack_pos (M k) (C k) (h.users_pos k) (h.capacity_pos k)
  have hdκ k := marketSlack_lt_capacity (M k) (C k) (h.users_pos k) (h.capacity_pos k)
  have hP k := price_nonneg (Ψ k) (marketSlack (M k) (C k)) hn (hdκ k)
  have hη k := slotError_nonneg (M k) (C k) (h.users_pos k) (h.capacity_pos k)
  have hd0 := marketSlack_tendsto M C ρ h.rho_pos h.users_tendsto h.capacity_tendsto
  have hf0 := singletonFailure_tendsto M C ρ h.rho_pos h.users_tendsto h.capacity_tendsto
  have hη0 := slotError_tendsto M C ρ h.rho_pos h.users_tendsto h.capacity_tendsto
  refine {
    reserve_nonneg := h.reserve_nonneg
    reserve_le := fun k => reserve_le_price (Ψ k) _ hn (hdκ k)
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
    exact (Bayes.measurable_typeOutcome_expect (Γ k) (i k) _).aestronglyMeasurable
  · intro k
    exact ((Bayes.measurable_typeOutcome_expect (Γ k) (i k) (fun z => (z.val : ℝ))).sub
      (Bayes.measurable_typeOutcome_expect (Γ k) (i k) (fun z => successIndicator z.val))).aestronglyMeasurable
  · intro k v
    simpa only [P, anonymousInterim_envelope] using (P k).envelope_nonneg v
  · intro k v w hvw
    simpa only [P, anonymousInterim_envelope] using (P k).envelope_monotone hvw
  · intro k v w
    simpa only [P, anonymousInterim_envelope] using (P k).envelope_lipschitz_inequality v w
  · intro k v
    have hh := (P k).envelope_upper v
    dsimp only [P] at hh
    rw [anonymousInterim_envelope] at hh
    change (Bayes.problem (Γ k) (i k)).envelope v ≤ max (v - ((Γ k).g + r)) 0 at hh
    simpa only [h.base k, sub_add_eq_sub_sub] using hh
  · intro k
    exact ae_of_all _ (anonymousTypePaymentError_nonneg (Γ k) (i k) _)
  · intro k
    exact integrable_anonymousTypePaymentError (Γ k) (i k) _ F
  · obtain ⟨B, hB⟩ := h.price_bounded
    apply squeeze_zero (fun k => integral_nonneg (anonymousTypePaymentError_nonneg (Γ k) (i k) _))
      (g := fun k => (2 * (n : ℝ) * B) * slotError (M k) (C k))
    · intro k
      have hb := integral_typePaymentError_le (Ψ k) (h.users_pos k) hn
        (marketSlack (M k) (C k)) (hd k).le (hdκ k) (h.uniform_ties k) (i k)
      rw [← anonymous_integral_typePaymentError_eq_routed (Γ k) r h.reserve_nonneg
        (h.uniform_ties k) (i k), h.law k] at hb
      exact hb.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hB k) (by positivity)) (hη k))
    · simpa only [mul_zero] using hη0.const_mul (2 * (n : ℝ) * B)
  · intro k v
    exact add_nonneg (hd k).le
      (mul_nonneg (singletonFailure_nonneg _ _) (le_max_right _ _))
  · intro v
    simpa only [zero_mul, zero_add] using hd0.add (hf0.mul_const (max (v - g) 0))
  · intro k
    simpa only [h.law k, h.base k] using anonymous_ae_envelope_le_type_price_error
      (Γ k) r h.reserve_nonneg (h.uniform_ties k) (h.bid_charge k) (i k) _ (h.optimal k)
  · intro k v
    obtain ⟨hb, hS⟩ := anonymous_singleton_at_price (Γ k) r h.reserve_nonneg
      (h.uniform_ties k) (h.users_pos k) (h.capacity_lt_users k).le hn (i k)
      (marketSlack (M k) (C k)) (marketSlack (M k) (C k)) (hd k) (hdκ k) (hd k)
    have hS' : 1 - singletonFailure (M k) (C k) ≤
        ((Bayes.problem (Γ k) (i k)).outcome
          (⟨price (Ψ k) (marketSlack (M k) (C k)) + marketSlack (M k) (C k),
            add_nonneg (hP k) (hd k).le, 1, hn⟩ : JointAction n)).success := by
      have hf := binomialFailure_le (M k) (C k) (h.users_pos k) (h.capacity_pos k)
      linarith
    simpa only [h.base k] using anonymous_singleton_envelope_lower (Γ k) hn (i k)
      (price (Ψ k) (marketSlack (M k) (C k))) (marketSlack (M k) (C k))
      (singletonFailure (M k) (C k)) v (hP k) (hd k).le
      (singletonFailure_nonneg _ _) hS'
  · intro k
    have he := anonymous_integral_typeCount_eq_routed (Γ k) r h.reserve_nonneg
      (h.uniform_ties k) (i k) (fun z => (z.val : ℝ))
    rw [h.law k] at he
    rw [show (∫ v, (Bayes.typeOutcome (Γ k) (i k) v).load ∂F) =
      ∫ v, ((Ψ k).typeOutcome (i k) v).load ∂(Ψ k).F from he]
    exact integral_typeLoad_le_capacity (Ψ k) (h.uniform_ties k) (i k)
  · intro k hPr
    have he := anonymous_integral_typeCount_eq_routed (Γ k) r h.reserve_nonneg
      (h.uniform_ties k) (i k) (fun z => (z.val : ℝ))
    rw [h.law k] at he
    rw [show (∫ v, (Bayes.typeOutcome (Γ k) (i k) v).load ∂F) =
      ∫ v, ((Ψ k).typeOutcome (i k) v).load ∂(Ψ k).F from he]
    exact integral_typeLoad_lower_of_price_gt_reserve (Ψ k) (h.users_pos k)
      (marketSlack (M k) (C k)) (hd k).le hPr (h.uniform_ties k) (i k)

theorem utility_and_counts [NullSingletonClass F]
    (h : AnonymousSourceAssumptions M C Γ F g r ρ vstar) (i : ∀ k, Fin (M k)) :
    (∀ v, Tendsto (fun k => (Bayes.problem (Γ k) (i k)).envelope v) atTop
      (𝓝 (max (v - g - max r (vstar - g)) 0))) ∧
    Tendsto (fun k => (∫ v, (Bayes.typeOutcome (Γ k) (i k) v).success ∂F,
      (∫ v, (Bayes.typeOutcome (Γ k) (i k) v).duplicates ∂F,
        ∫ v, (Bayes.typeOutcome (Γ k) (i k) v).load ∂F))) atTop
      (𝓝 (F.real (Ioi (g + max r (vstar - g))),
        (0, F.real (Ioi (g + max r (vstar - g)))))) :=
  (h.estimates i).full_limits vstar h.scarcity h.cutoff
    h.density.interval_mass.1 h.density.interval_mass.2

end AnonymousSourceAssumptions
end FCAppendix.CommonReserve
