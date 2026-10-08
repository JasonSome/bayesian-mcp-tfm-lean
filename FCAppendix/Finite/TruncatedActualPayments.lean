import FCAppendix.Game.PosteriorReceipts
import FCAppendix.Finite.TruncatedReceiptBounds
import FCAppendix.Finite.CapacityFill
import FCAppendix.Finite.PaymentShortfall

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Filter
open scoped BigOperators ProbabilityTheory

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def truncatedBid (R b : ℝ) : ℝ :=
  if b ≤ R then max b 0 else 0

theorem truncatedBid_bounds (R b : ℝ) (hR : 0 ≤ R) :
    0 ≤ truncatedBid R b ∧ truncatedBid R b ≤ R := by
  by_cases h : b ≤ R
  · simp only [truncatedBid, if_pos h]
    exact ⟨le_max_right _ _, max_le h hR⟩
  · simp only [truncatedBid, if_neg h]
    exact ⟨le_rfl, hR⟩

theorem measurable_truncatedBid (R : ℝ) : Measurable (truncatedBid R) :=
  Measurable.ite (measurableSet_le measurable_id measurable_const)
    (measurable_id.max measurable_const) measurable_const

def visibleBidValue : Option ℝ → ℝ
  | none => 0
  | some b => b

theorem measurable_visibleBidValue : Measurable visibleBidValue := by
  intro s hs
  change MeasurableSet ((fun b : ℝ => b) ⁻¹' s)
  exact hs

theorem observe_some_of_selected (Γ : FiniteGame m n c Seed)
    (j : Fin n) (i : Fin m) (ω : Background m n Seed)
    (hi : i ∈ allocation (drawsRealization ω.1) Γ.policy ω.2 j) :
    observe (drawsRealization ω.1) j i = some (ω.1 i).1.2.bid := by
  classical
  have hp := (Γ.policy j (observe (drawsRealization ω.1) j) (ω.2 j)).property.2 i hi
  by_cases hj : j ∈ firstK (ω.1 i).2 (ω.1 i).1.2.routeCount
  · simp [observe, drawsRealization, hj]
  · exact (hp (by simp [observe, drawsRealization, hj])).elim

noncomputable def selectedTruncatedBid (Γ : FiniteGame m n c Seed)
    (j : Fin n) (i : Fin m) (R : ℝ) (ω : Background m n Seed) : ℝ :=
  if i ∈ allocation (drawsRealization ω.1) Γ.policy ω.2 j then
    truncatedBid R (ω.1 i).1.2.bid else 0

theorem measurable_selectedTruncatedBid (Γ : FiniteGame m n c Seed)
    (j : Fin n) (i : Fin m) (R : ℝ) : Measurable (selectedTruncatedBid Γ j i R) := by
  classical
  apply Measurable.ite _ _ measurable_const
  · exact (measurable_allocation_draws Γ j)
      (MeasurableSet.of_discrete : MeasurableSet {S : Finset (Fin m) | i ∈ S})
  · exact (measurable_truncatedBid R).comp ((measurable_bid n).comp
      (measurable_snd.comp (measurable_fst.comp ((measurable_pi_apply i).comp measurable_fst))))

theorem selectedTruncatedBid_bounds (Γ : FiniteGame m n c Seed)
    (j : Fin n) (i : Fin m) (R : ℝ) (hR : 0 ≤ R) (ω : Background m n Seed) :
    0 ≤ selectedTruncatedBid Γ j i R ω ∧ selectedTruncatedBid Γ j i R ω ≤ R := by
  classical
  unfold selectedTruncatedBid
  split
  · exact truncatedBid_bounds R _ hR
  · exact ⟨le_rfl, hR⟩

noncomputable def truncatedActualReceipt (Γ : FiniteGame m n c Seed)
    (j : Fin n) (i : Fin m) (R : ℝ) (ω : Background m n Seed) : ℝ :=
  selectedTruncatedBid Γ j i R ω *
    Γ.A.receiptRatio ((otherInclusionCount Γ j i ω).val + 1)

noncomputable def truncatedPosteriorReceipt (Γ : FiniteGame m n c Seed)
    (B : PosteriorSystem Γ) (j : Fin n) (i : Fin m) (R : ℝ)
    (ω : Background m n Seed) : ℝ :=
  selectedTruncatedBid Γ j i R ω *
    posteriorReceiptFactor Γ B j (observe (drawsRealization ω.1) j) i

theorem measurable_truncatedActualReceipt (Γ : FiniteGame m n c Seed)
    (j : Fin n) (i : Fin m) (R : ℝ) : Measurable (truncatedActualReceipt Γ j i R) :=
  (measurable_selectedTruncatedBid Γ j i R).mul
    ((measurable_of_countable (fun r : Fin n => Γ.A.receiptRatio (r.val + 1))).comp
      (measurable_otherInclusionCount Γ j i))

theorem measurable_truncatedPosteriorReceipt (Γ : FiniteGame m n c Seed)
    (B : PosteriorSystem Γ) (j : Fin n) (i : Fin m) (R : ℝ) :
    Measurable (truncatedPosteriorReceipt Γ B j i R) :=
  (measurable_selectedTruncatedBid Γ j i R).mul
    ((measurable_posteriorReceiptFactor Γ B j i).comp
      ((measurable_observe_draws j).comp measurable_fst))

theorem truncatedActualReceipt_bounds (Γ : FiniteGame m n c Seed)
    (j : Fin n) (i : Fin m) (R : ℝ) (hR : 0 ≤ R) (ω : Background m n Seed) :
    0 ≤ truncatedActualReceipt Γ j i R ω ∧ truncatedActualReceipt Γ j i R ω ≤ R := by
  have hb := selectedTruncatedBid_bounds Γ j i R hR ω
  have hr := receiptRatio_unit Γ.A (otherInclusionCount Γ j i ω)
  exact ⟨mul_nonneg hb.1 hr.1,
    (mul_le_mul_of_nonneg_left hr.2 hb.1).trans (by simpa using hb.2)⟩

theorem truncatedPosteriorReceipt_bounds (Γ : FiniteGame m n c Seed)
    (B : PosteriorSystem Γ) (j : Fin n) (i : Fin m) (R : ℝ) (hR : 0 ≤ R)
    (ω : Background m n Seed) :
    0 ≤ truncatedPosteriorReceipt Γ B j i R ω ∧
      truncatedPosteriorReceipt Γ B j i R ω ≤ R := by
  have hb := selectedTruncatedBid_bounds Γ j i R hR ω
  have hr := posteriorReceiptFactor_bounds Γ B j (observe (drawsRealization ω.1) j) i
  exact ⟨mul_nonneg hb.1 hr.1,
    (mul_le_mul_of_nonneg_left hr.2 hb.1).trans (by simpa using hb.2)⟩

theorem integrable_truncatedActualReceipt (Γ : FiniteGame m n c Seed)
    (j : Fin n) (i : Fin m) (R : ℝ) (hR : 0 ≤ R) :
    Integrable (truncatedActualReceipt Γ j i R) (backgroundLaw Γ) := by
  apply Integrable.of_bound (measurable_truncatedActualReceipt Γ j i R).aestronglyMeasurable R
  exact Eventually.of_forall fun ω => by
    have h := truncatedActualReceipt_bounds Γ j i R hR ω
    simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2

theorem integrable_truncatedPosteriorReceipt (Γ : FiniteGame m n c Seed)
    (B : PosteriorSystem Γ) (j : Fin n) (i : Fin m) (R : ℝ) (hR : 0 ≤ R) :
    Integrable (truncatedPosteriorReceipt Γ B j i R) (backgroundLaw Γ) := by
  apply Integrable.of_bound
    (measurable_truncatedPosteriorReceipt Γ B j i R).aestronglyMeasurable R
  exact Eventually.of_forall fun ω => by
    have h := truncatedPosteriorReceipt_bounds Γ B j i R hR ω
    simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2

theorem integral_truncatedActualReceipt_eq_posterior
    (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ)
    (j : Fin n) (i : Fin m) (R : ℝ) (hR : 0 ≤ R) :
    (∫ ω, truncatedActualReceipt Γ j i R ω ∂backgroundLaw Γ) =
      ∫ ω, truncatedPosteriorReceipt Γ B j i R ω ∂backgroundLaw Γ := by
  classical
  let w : LocalList m → ℝ := fun ℓ => truncatedBid R (visibleBidValue (ℓ i))
  have hw : Measurable w := (measurable_truncatedBid R).comp
    (measurable_visibleBidValue.comp (measurable_pi_apply i))
  have hwb : ∀ ℓ, ‖w ℓ‖ ≤ R := by
    intro ℓ
    have h := truncatedBid_bounds R (visibleBidValue (ℓ i)) hR
    simpa only [w, Real.norm_eq_abs, abs_of_nonneg h.1] using h.2
  have he (ω : Background m n Seed) :
      (if i ∈ allocation (drawsRealization ω.1) Γ.policy ω.2 j then
        w (observe (drawsRealization ω.1) j) else 0) =
      selectedTruncatedBid Γ j i R ω := by
    by_cases hi : i ∈ allocation (drawsRealization ω.1) Γ.policy ω.2 j
    · simp only [if_pos hi, selectedTruncatedBid, w,
        observe_some_of_selected Γ j i ω hi, visibleBidValue]
    · simp only [if_neg hi, selectedTruncatedBid]
  have h := integral_weighted_receipt_eq_actual_posterior Γ B j i w hw R hwb
  simpa only [he, truncatedActualReceipt, truncatedPosteriorReceipt] using h

noncomputable def finiteTruncatedPayment (Γ : FiniteGame m n c Seed) (R : ℝ) : ℝ :=
  (∑ j, ∑ i, ∫ ω, truncatedActualReceipt Γ j i R ω ∂backgroundLaw Γ) / m

theorem finiteTruncatedPayment_nonneg (Γ : FiniteGame m n c Seed) (R : ℝ) (hR : 0 ≤ R) :
    0 ≤ finiteTruncatedPayment Γ R :=
  div_nonneg (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ =>
    integral_nonneg fun ω => (truncatedActualReceipt_bounds Γ j i R hR ω).1)
      (Nat.cast_nonneg _)

theorem finiteTruncatedPayment_le (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (R : ℝ) (hR : 0 ≤ R) :
    finiteTruncatedPayment Γ R ≤ n * R := by
  have hi (j : Fin n) (i : Fin m) :
      (∫ ω, truncatedActualReceipt Γ j i R ω ∂backgroundLaw Γ) ≤ R := by
    have h := integral_mono_ae (integrable_truncatedActualReceipt Γ j i R hR)
      (integrable_const R)
      (Eventually.of_forall fun ω => (truncatedActualReceipt_bounds Γ j i R hR ω).2)
    simpa only [integral_const, probReal_univ, one_smul] using h
  have hsum := Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
    Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => hi j i
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  unfold finiteTruncatedPayment
  apply (div_le_iff₀ hmR).mpr
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using hsum

theorem otherInclusionCount_add_one_of_selected (Γ : FiniteGame m n c Seed)
    (j : Fin n) (i : Fin m) (ω : Background m n Seed)
    (hi : i ∈ allocation (drawsRealization ω.1) Γ.policy ω.2 j) :
    (otherInclusionCount Γ j i ω).val + 1 = (playedCount Γ i ω).val := by
  classical
  rw [otherInclusionCount_eq_sum]
  change _ = inclusionCount (drawsRealization ω.1) Γ.policy ω.2 i
  rw [inclusionCount_eq_sum]
  simpa only [if_pos hi] using Finset.sum_erase_add Finset.univ
    (fun l => if i ∈ allocation (drawsRealization ω.1) Γ.policy ω.2 l then (1 : ℕ) else 0)
    (Finset.mem_univ j)

theorem sum_truncatedActualReceipt_eq_user_payment (Γ : FiniteGame m n c Seed)
    (i : Fin m) (R : ℝ) (ω : Background m n Seed) :
    (∑ j, truncatedActualReceipt Γ j i R ω) =
      truncatedBid R (ω.1 i).1.2.bid * Γ.A.charge (playedCount Γ i ω).val := by
  classical
  have he (j : Fin n) : truncatedActualReceipt Γ j i R ω =
      (if i ∈ allocation (drawsRealization ω.1) Γ.policy ω.2 j then (1 : ℝ) else 0) *
        (truncatedBid R (ω.1 i).1.2.bid * Γ.A.receiptRatio (playedCount Γ i ω).val) := by
    by_cases hi : i ∈ allocation (drawsRealization ω.1) Γ.policy ω.2 j
    · simp only [truncatedActualReceipt, selectedTruncatedBid, if_pos hi, one_mul,
        otherInclusionCount_add_one_of_selected Γ j i ω hi]
    · simp only [truncatedActualReceipt, selectedTruncatedBid, if_neg hi, zero_mul]
  have hc : (∑ j, if i ∈ allocation (drawsRealization ω.1) Γ.policy ω.2 j
      then (1 : ℝ) else 0) = ((playedCount Γ i ω).val : ℝ) := by
    change _ = (inclusionCount (drawsRealization ω.1) Γ.policy ω.2 i : ℝ)
    simp only [inclusionCount_eq_sum, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  simp_rw [he]
  rw [← Finset.sum_mul, hc, Schedule.receiptRatio]
  by_cases hk : (playedCount Γ i ω).val = 0
  · simp [hk, Γ.A.zero]
  · have hkR : ((playedCount Γ i ω).val : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
    field_simp [hkR]

theorem finiteTruncatedPayment_eq_user_integrals (Γ : FiniteGame m n c Seed)
    (R : ℝ) (hR : 0 ≤ R) :
    finiteTruncatedPayment Γ R =
      (∑ i, ∫ ω, truncatedBid R (ω.1 i).1.2.bid *
        Γ.A.charge (playedCount Γ i ω).val ∂backgroundLaw Γ) / m := by
  unfold finiteTruncatedPayment
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← integral_finsetSum _ (fun j _ => integrable_truncatedActualReceipt Γ j i R hR)]
  apply integral_congr_ae
  exact Eventually.of_forall (sum_truncatedActualReceipt_eq_user_payment Γ i R)

end FCAppendix.Bayes
