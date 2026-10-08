import FCAppendix.Finite.TruncatedActualPayments

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Filter
open scoped BigOperators ProbabilityTheory

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def BayesReceiptOptimalOnPath
    (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ) : Prop :=
  ∀ j, ∀ᵐ ℓ ∂observedListLaw Γ j, ∀ᵐ s ∂Γ.seedLaw,
    Finite.Optimal c (beliefReceipts Γ.A (posteriorCountBelief Γ B j ℓ) ℓ)
      (Γ.policy j ℓ s).val

theorem bayesReceiptOptimalOnPath_iff {k : ℕ}
    (Γ : FiniteGame m (k + 1) c Seed) (B : PosteriorSystem Γ) :
    BayesReceiptOptimalOnPath Γ B ↔ PosteriorProposerOptimalOnPath Γ B := Iff.rfl

theorem posterior_onPath_of_feasible (Γ : FiniteGame m n c Seed)
    (B : PosteriorSystem Γ) (hB : PosteriorProposerOptimalAE Γ B) :
    BayesReceiptOptimalOnPath Γ B := by
  intro j
  filter_upwards [B.ae_observation Γ j] with ℓ hℓ
  obtain ⟨d, hd⟩ := hℓ.exists
  exact hB j ℓ ⟨d, hd⟩

theorem posterior_isAEEquilibrium_onPath (Γ : FiniteGame m n c Seed)
    (B : PosteriorSystem Γ) (hu : UsersOptimal Γ)
    (hB : BayesReceiptOptimalOnPath Γ B) : IsAEEquilibrium Γ :=
  ⟨hu, fun j => ⟨posteriorCountBelief Γ B j, hB j⟩⟩

noncomputable def localSelectedCount (Γ : FiniteGame m n c Seed)
    (j : Fin n) (ω : Background m n Seed) : ℝ :=
  (allocation (drawsRealization ω.1) Γ.policy ω.2 j).card

theorem measurable_localSelectedCount (Γ : FiniteGame m n c Seed) (j : Fin n) :
    Measurable (localSelectedCount Γ j) :=
  (measurable_of_countable (fun S : Finset (Fin m) => (S.card : ℝ))).comp
    (measurable_allocation_draws Γ j)

theorem integrable_localSelectedCount (Γ : FiniteGame m n c Seed) (j : Fin n) :
    Integrable (localSelectedCount Γ j) (backgroundLaw Γ) := by
  apply Integrable.of_bound (measurable_localSelectedCount Γ j).aestronglyMeasurable c
  apply Eventually.of_forall
  intro ω
  rw [localSelectedCount, Real.norm_natCast]
  exact_mod_cast (Γ.policy j (observe (drawsRealization ω.1) j) (ω.2 j)).property.1

noncomputable def highBidCount (Γ : FiniteGame m n c Seed)
    (j : Fin n) (R : ℝ) (ω : Background m n Seed) : ℕ := by
  classical
  exact ((allocation (drawsRealization ω.1) Γ.policy ω.2 j) ∩
    Finset.univ.filter (fun i => R < (ω.1 i).1.2.bid)).card

theorem highBidCount_eq_sum (Γ : FiniteGame m n c Seed)
    (j : Fin n) (R : ℝ) (ω : Background m n Seed) :
    highBidCount Γ j R ω = ∑ i,
      if i ∈ allocation (drawsRealization ω.1) Γ.policy ω.2 j ∧
        R < (ω.1 i).1.2.bid then 1 else 0 := by
  classical
  rw [highBidCount, ← sum_membership]
  simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]

theorem measurable_highBidCount (Γ : FiniteGame m n c Seed) (j : Fin n) (R : ℝ) :
    Measurable (highBidCount Γ j R) := by
  classical
  simp_rw [show highBidCount Γ j R = fun ω => ∑ i,
    if i ∈ allocation (drawsRealization ω.1) Γ.policy ω.2 j ∧
      R < (ω.1 i).1.2.bid then 1 else 0 from funext (highBidCount_eq_sum Γ j R)]
  apply Finset.measurable_sum
  intro i _
  apply Measurable.ite _ measurable_const measurable_const
  apply MeasurableSet.inter
  · exact (measurable_allocation_draws Γ j)
      (MeasurableSet.of_discrete : MeasurableSet {S : Finset (Fin m) | i ∈ S})
  · exact measurableSet_lt measurable_const ((measurable_bid n).comp
      (measurable_snd.comp (measurable_fst.comp ((measurable_pi_apply i).comp measurable_fst))))

theorem highBidCount_le_capacity (Γ : FiniteGame m n c Seed)
    (j : Fin n) (R : ℝ) (ω : Background m n Seed) : highBidCount Γ j R ω ≤ c :=
  (Finset.card_le_card Finset.inter_subset_left).trans
    (Γ.policy j (observe (drawsRealization ω.1) j) (ω.2 j)).property.1

theorem integrable_highBidCount (Γ : FiniteGame m n c Seed) (j : Fin n) (R : ℝ) :
    Integrable (fun ω => (highBidCount Γ j R ω : ℝ)) (backgroundLaw Γ) := by
  apply Integrable.of_bound
    ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
      (measurable_highBidCount Γ j R)).aestronglyMeasurable c
  exact Eventually.of_forall fun ω => by
    rw [Function.comp_apply, Real.norm_natCast]
    exact_mod_cast highBidCount_le_capacity Γ j R ω

noncomputable def receiptArrivalShortfall (_Γ : FiniteGame m n c Seed)
    (j : Fin n) (t : ℝ) (ω : Background m n Seed) : ℝ :=
  max ((c : ℝ) - PiBinomial.count (aboveAt j t) Finset.univ ω.1) 0

theorem measurable_receiptArrivalShortfall (Γ : FiniteGame m n c Seed)
    (j : Fin n) (t : ℝ) : Measurable (receiptArrivalShortfall Γ j t) :=
  (measurable_const.sub ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
    ((PiBinomial.measurable_count (aboveAt j t) (measurableSet_aboveAt j t)
      (Finset.univ : Finset (Fin m))).comp measurable_fst))).max measurable_const

theorem integrable_receiptArrivalShortfall (Γ : FiniteGame m n c Seed)
    (j : Fin n) (t : ℝ) : Integrable (receiptArrivalShortfall Γ j t) (backgroundLaw Γ) := by
  apply Integrable.of_bound (measurable_receiptArrivalShortfall Γ j t).aestronglyMeasurable c
  exact Eventually.of_forall fun ω => by
    rw [receiptArrivalShortfall, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (sub_le_self _ (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

theorem integral_receiptArrivalShortfall_eq (Γ : FiniteGame m n c Seed)
    (j : Fin n) (t : ℝ) :
    (∫ ω, receiptArrivalShortfall Γ j t ω ∂backgroundLaw Γ) =
      ∫ d, max ((c : ℝ) - PiBinomial.count (aboveAt j t) Finset.univ d) 0
        ∂userProfileLaw Γ := by
  simp only [receiptArrivalShortfall, backgroundLaw,
    integral_fun_fst (fun d : UserProfile m n =>
      max ((c : ℝ) - PiBinomial.count (aboveAt j t) Finset.univ d) 0),
    probReal_univ, one_smul, userProfileLaw]

theorem local_posterior_truncated_lower (Γ : FiniteGame m n c Seed)
    (B : PosteriorSystem Γ) (j : Fin n) (a t R : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t)
    (hA : ∀ r : ℕ, 0 < r → r ≤ n → a * (r : ℝ) ≤ Γ.A.charge r)
    (ω : Background m n Seed)
    (hopt : Finite.Optimal c
      (beliefReceipts Γ.A (posteriorCountBelief Γ B j (observe (drawsRealization ω.1) j))
        (observe (drawsRealization ω.1) j))
      (allocation (drawsRealization ω.1) Γ.policy ω.2 j)) :
    (a * t) * (localSelectedCount Γ j ω - (highBidCount Γ j R ω : ℝ) -
      receiptArrivalShortfall Γ j t ω) ≤ ∑ i, truncatedPosteriorReceipt Γ B j i R ω := by
  classical
  let S := allocation (drawsRealization ω.1) Γ.policy ω.2 j
  let ℓ := observe (drawsRealization ω.1) j
  let r := beliefReceipts Γ.A (posteriorCountBelief Γ B j ℓ) ℓ
  let H := Finset.univ.filter (fun i => ω.1 i ∈ aboveAt j t)
  have hr (i : Fin m) (hi : i ∈ S) :
      r i = (ω.1 i).1.2.bid * posteriorReceiptFactor Γ B j ℓ i := by
    dsimp only [r, beliefReceipts, ℓ]
    simp only [observe_some_of_selected Γ j i ω hi, conditionalReceipt_eq_mul_ratio_expect]
    rfl
  have hpos (i : Fin m) (hi : i ∈ S) : 0 ≤ r i := by
    rw [hr i hi]
    exact mul_nonneg (ω.1 i).1.2.bid_nonneg (posteriorReceiptFactor_bounds Γ B j ℓ i).1
  have hH (i : Fin m) (hi : i ∈ H) : a * t ≤ r i := by
    have hh : j ∈ firstK (ω.1 i).2 (ω.1 i).1.2.routeCount ∧ t < (ω.1 i).1.2.bid :=
      (Finset.mem_filter.mp hi).2
    have hsome : ℓ i = some (ω.1 i).1.2.bid := by
      simp [ℓ, observe, drawsRealization, hh.1]
    exact (mul_le_mul_of_nonneg_left hh.2.le ha).trans
      (beliefReceipts_bounds Γ.A (posteriorCountBelief Γ B j ℓ) ℓ a hA i _
        (ω.1 i).1.2.bid_nonneg hsome).1
  have hbad : S.filter (fun i => ¬ (ω.1 i).1.2.bid ≤ R) =
      S ∩ Finset.univ.filter (fun i => R < (ω.1 i).1.2.bid) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_univ, true_and, not_le]
  have he (i : Fin m) : truncatedPosteriorReceipt Γ B j i R ω =
      if i ∈ S then (if (ω.1 i).1.2.bid ≤ R then r i else 0) else 0 := by
    by_cases hi : i ∈ S
    · rw [if_pos hi, hr i hi]
      by_cases hb : (ω.1 i).1.2.bid ≤ R <;>
        simp only [truncatedPosteriorReceipt, selectedTruncatedBid, truncatedBid,
          show i ∈ allocation (drawsRealization ω.1) Γ.policy ω.2 j from hi,
          hb, ↓reduceIte, max_eq_left (ω.1 i).1.2.bid_nonneg, zero_mul, ℓ]
    · simp only [truncatedPosteriorReceipt, selectedTruncatedBid,
        show i ∉ allocation (drawsRealization ω.1) Γ.policy ω.2 j from hi,
        if_neg hi, ↓reduceIte, zero_mul]
  have hsum : (∑ i, truncatedPosteriorReceipt Γ B j i R ω) =
      ∑ i ∈ S, if (ω.1 i).1.2.bid ≤ R then r i else 0 := by
    simp_rw [he]
    rw [← Finset.sum_filter]
    simp
  have h := Finite.optimal_truncated_receipt_lower c r S H hopt hpos (a * t)
    (mul_nonneg ha ht) hH (fun i => (ω.1 i).1.2.bid ≤ R)
  rw [hbad] at h
  rw [hsum]
  exact h

theorem ae_posterior_truncated_lower (Γ : FiniteGame m n c Seed)
    (B : PosteriorSystem Γ) (hB : BayesReceiptOptimalOnPath Γ B)
    (j : Fin n) (a t R : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t)
    (hA : ∀ r : ℕ, 0 < r → r ≤ n → a * (r : ℝ) ≤ Γ.A.charge r) :
    ∀ᵐ ω ∂backgroundLaw Γ,
      (a * t) * (localSelectedCount Γ j ω - (highBidCount Γ j R ω : ℝ) -
        receiptArrivalShortfall Γ j t ω) ≤ ∑ i, truncatedPosteriorReceipt Γ B j i R ω := by
  have hl : Measurable (fun ω : Background m n Seed =>
      (a * t) * (localSelectedCount Γ j ω - (highBidCount Γ j R ω : ℝ) -
        receiptArrivalShortfall Γ j t ω)) :=
    measurable_const.mul (((measurable_localSelectedCount Γ j).sub
      ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
        (measurable_highBidCount Γ j R))).sub (measurable_receiptArrivalShortfall Γ j t))
  have hr : Measurable (fun ω => ∑ i, truncatedPosteriorReceipt Γ B j i R ω) :=
    Finset.measurable_sum _ (fun i _ => measurable_truncatedPosteriorReceipt Γ B j i R)
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hl hr)).mpr
  have hd := ae_of_ae_map (measurable_observe_draws j).aemeasurable (hB j)
  filter_upwards [hd] with d hd
  have hs := (measurePreserving_eval (fun _ : Fin n => Γ.seedLaw) j).quasiMeasurePreserving.ae hd
  filter_upwards [hs] with s hs
  exact local_posterior_truncated_lower Γ B j a t R ha ht hA (d, s) hs

theorem integral_truncated_proposer_lower (Γ : FiniteGame m n c Seed)
    (B : PosteriorSystem Γ) (hB : BayesReceiptOptimalOnPath Γ B)
    (j : Fin n) (a t R : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) (hR : 0 ≤ R)
    (hA : ∀ r : ℕ, 0 < r → r ≤ n → a * (r : ℝ) ≤ Γ.A.charge r) :
    (a * t) * ((∫ ω, localSelectedCount Γ j ω ∂backgroundLaw Γ) -
      (∫ ω, (highBidCount Γ j R ω : ℝ) ∂backgroundLaw Γ) -
      (∫ ω, receiptArrivalShortfall Γ j t ω ∂backgroundLaw Γ)) ≤
      ∑ i, ∫ ω, truncatedActualReceipt Γ j i R ω ∂backgroundLaw Γ := by
  have hc := integrable_localSelectedCount Γ j
  have hh := integrable_highBidCount Γ j R
  have hs := integrable_receiptArrivalShortfall Γ j t
  have hp := integrable_finsetSum Finset.univ
    (fun i _ => integrable_truncatedPosteriorReceipt Γ B j i R hR)
  have h := integral_mono_ae (((hc.sub hh).sub hs).const_mul (a * t)) hp
    (ae_posterior_truncated_lower Γ B hB j a t R ha ht hA)
  have hs₁ := integral_sub (hc.sub hh) hs
  have hs₂ := integral_sub hc hh
  simp only [Pi.sub_apply] at h hs₁ hs₂
  rw [integral_const_mul, hs₁, hs₂,
    integral_finsetSum _ (fun i _ => integrable_truncatedPosteriorReceipt Γ B j i R hR)] at h
  simpa only [integral_truncatedActualReceipt_eq_posterior Γ B _ _ R hR] using h

theorem sum_integral_localSelectedCount (Γ : FiniteGame m n c Seed) :
    (∑ j, ∫ ω, localSelectedCount Γ j ω ∂backgroundLaw Γ) / m = finiteLoad Γ := by
  rw [finiteLoad_eq_actual,
    ← integral_finsetSum _ (fun j _ => integrable_localSelectedCount Γ j),
    ← integral_finsetSum _ (fun i _ => CountLaw.integrable_comp (backgroundLaw Γ) _
      (measurable_playedCount Γ i) (fun r => (r.val : ℝ)))]
  congr 1
  apply integral_congr_ae
  apply Eventually.of_forall
  intro ω
  simp only [localSelectedCount, playedCount]
  exact_mod_cast (double_count (drawsRealization ω.1) Γ.policy ω.2).symm

theorem finiteTruncatedPayment_lower_counts (Γ : FiniteGame m n c Seed)
    (B : PosteriorSystem Γ) (hB : BayesReceiptOptimalOnPath Γ B)
    (a t R : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) (hR : 0 ≤ R)
    (hA : ∀ r : ℕ, 0 < r → r ≤ n → a * (r : ℝ) ≤ Γ.A.charge r) :
    (a * t) * (finiteLoad Γ -
      (∑ j, ∫ ω, (highBidCount Γ j R ω : ℝ) ∂backgroundLaw Γ) / m -
      (∑ j, ∫ d, max ((c : ℝ) - PiBinomial.count (aboveAt j t) Finset.univ d) 0
        ∂userProfileLaw Γ) / m) ≤ finiteTruncatedPayment Γ R := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
    (fun j _ => integral_truncated_proposer_lower Γ B hB j a t R ha ht hR hA)
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib] at h
  have hd := div_le_div_of_nonneg_right h (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  rw [← sum_integral_localSelectedCount Γ]
  simp_rw [integral_receiptArrivalShortfall_eq] at hd
  change _ ≤ (∑ j, ∑ i, ∫ ω, truncatedActualReceipt Γ j i R ω ∂backgroundLaw Γ) / m
  simpa only [mul_sub, sub_div, mul_div_assoc] using hd

end FCAppendix.Bayes
