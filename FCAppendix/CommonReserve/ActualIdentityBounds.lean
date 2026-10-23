import FCAppendix.CommonReserve.LocalIdentityStatistics
import FCAppendix.CommonReserve.ActualConditioning
import FCAppendix.CommonReserve.LayerCake
import FCAppendix.CommonReserve.CapacityEstimate

noncomputable section
namespace FCAppendix.CommonReserve
open Game MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ProbabilityTheory

variable {m n c : ℕ} {r : ℝ} {Seed : Type*} [MeasurableSpace Seed]

def gapWeight (j : Fin n) (p : ℝ) (x : UserDraw n r) : ℝ :=
  max (p - Bayes.entryBid (x.2.val j)) 0

theorem measurable_gapWeight (j : Fin n) (p : ℝ) : Measurable (gapWeight (r := r) j p) :=
  (measurable_const.sub (measurable_coordinateBid j)).max measurable_const

theorem gapWeight_nonneg (j : Fin n) (p : ℝ) (x : UserDraw n r) :
    0 ≤ gapWeight j p x := le_max_right _ _

theorem gapWeight_le (Γ : FiniteGame m n c r Seed) (j : Fin n) (p : ℝ)
    (hp : 0 ≤ p) (x : UserDraw n r) : gapWeight j p x ≤ p := by
  have hb : 0 ≤ Bayes.entryBid (x.2.val j) := by
    cases he : x.2.val j with
    | none => simp [Bayes.entryBid]
    | some b => exact Γ.reserve_nonneg.trans (x.2.property j b he)
  exact max_le (sub_le_self _ hb) hp

theorem integral_typeLoad_eq_sum_localStatistic (Γ : FiniteGame m n c r Seed) (i : Fin m) :
    (∫ v, (Γ.typeOutcome i v).load ∂Γ.F) =
      ∑ j, ∫ d, localStatistic Γ j (fun _ => 1) d i
        ∂(Measure.pi fun _ : Fin m => Γ.userLaw) := by
  classical
  simp only [CountLaw.load, Γ.integral_typeOutcome_expect_eq_actual]
  have he (ω : Sample m n r Seed) : ((Γ.playedCount i ω).val : ℝ) =
      ∑ j, if i ∈ playedAllocation Γ j ω then (1 : ℝ) else 0 := by
    simp only [FiniteGame.playedCount, count, accepted, playedAllocation,
      ← Game.sum_membership_real]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [show FiniteGame.actualProfile ω = playedProfile ω from rfl]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : i ∈ allocation (playedProfile ω) Γ.policy ω.2 j <;> simp [hj]
  simp_rw [he]
  rw [integral_finsetSum _ (fun j _ =>
    integrable_weighted_membership Γ.sampleLaw _ (measurable_playedAllocation Γ j)
      (fun _ => 1) measurable_const 1 (by norm_num) (fun _ => by norm_num) i)]
  apply Finset.sum_congr rfl
  intro j _
  exact (integral_statistic_eq_actual Γ j _ measurable_const 1
    (by norm_num) (fun _ => by norm_num) i).symm

theorem integral_typePaymentError_eq_sum_localStatistic (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (p : ℝ) (hp : 0 ≤ p) :
    (∫ v, Γ.typePaymentError i p v ∂Γ.F) =
      ∑ j, ∫ d, localStatistic Γ j (gapWeight j p) d i
        ∂(Measure.pi fun _ : Fin m => Γ.userLaw) := by
  classical
  rw [Γ.integral_typePaymentError_eq_actual]
  have he (ω : Sample m n r Seed) : shortfall p (FiniteGame.actualProfile ω) Γ.policy ω.2 i =
      ∑ j, if i ∈ playedAllocation Γ j ω then gapWeight j p (ω.1 i) else 0 := by
    rw [show FiniteGame.actualProfile ω = playedProfile ω from rfl]
    simp only [shortfall, accepted, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    rfl
  simp_rw [he]
  have hbound (j : Fin n) (x : UserDraw n r) : ‖gapWeight j p x‖ ≤ p := by
    rw [Real.norm_eq_abs, abs_of_nonneg (gapWeight_nonneg j p x)]
    exact gapWeight_le Γ j p hp x
  have hi (j : Fin n) : Integrable (fun ω : Sample m n r Seed =>
      if i ∈ playedAllocation Γ j ω then gapWeight j p (ω.1 i) else 0) Γ.sampleLaw :=
    integrable_weighted_membership Γ.sampleLaw _
      (measurable_playedAllocation Γ j) _
      ((measurable_gapWeight j p).comp ((measurable_pi_apply i).comp measurable_fst))
      p hp (fun ω => hbound j _) i
  rw [integral_finsetSum _ (fun j _ => hi j)]
  apply Finset.sum_congr rfl
  intro j _
  exact (integral_statistic_eq_actual Γ j _ (measurable_gapWeight j p)
    p hp (hbound j) i).symm

theorem integral_positive_gap_le_localError (Γ : FiniteGame m n c r Seed)
    (j : Fin n) (hT : UniformReserveRule Γ.seedLaw (Γ.policy j) r)
    (i : Fin m) (p : ℝ) (hp : 0 ≤ p) :
    (∫ d, localPositive Γ j (gapWeight j p) d i
      ∂(Measure.pi fun _ : Fin m => Γ.userLaw)) ≤
      (∫ ω, localError Γ j p ω ∂Γ.sampleLaw) / m := by
  classical
  have hw (x : UserDraw n r) : ‖gapWeight j p x‖ ≤ p := by
    rw [Real.norm_eq_abs, abs_of_nonneg (gapWeight_nonneg j p x)]
    exact gapWeight_le Γ j p hp x
  rw [integral_localPositive_identity_average Γ j hT _ (measurable_gapWeight j p) i]
  simp_rw [integral_positive_eq_actual Γ j _ (measurable_gapWeight j p) p hp hw]
  have hi (l : Fin m) : Integrable
      (fun ω : Sample m n r Seed => if l ∈ positivePlayedAllocation Γ j ω
        then gapWeight j p (ω.1 l) else 0) Γ.sampleLaw :=
    integrable_weighted_membership Γ.sampleLaw _ (measurable_positivePlayedAllocation Γ j)
      _ ((measurable_gapWeight j p).comp ((measurable_pi_apply l).comp measurable_fst))
      p hp (fun ω => hw _) l
  rw [← integral_finsetSum _ (fun l _ => hi l)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply integral_mono (integrable_finsetSum _ (fun l _ => hi l)) (integrable_localError Γ j p)
  intro ω
  rw [localError_eq_sum]
  apply Finset.sum_le_sum
  intro l _
  by_cases hl : l ∈ playedAllocation Γ j ω
  · simp only [positivePlayedAllocation, positiveSelection, Finset.mem_filter, hl,
      true_and, if_true, gapWeight]
    split <;> simp_all
  · simp [positivePlayedAllocation, positiveSelection, hl]

theorem integral_localZeroShare_le_slotError (Γ : FiniteGame m n c r Seed)
    (hm : 0 < m) (j : Fin n) (i : Fin m) (δ : ℝ) (hδ : 0 ≤ δ)
    (hP : 0 < price Γ δ) :
    (∫ d, localZeroShare Γ j d i ∂(Measure.pi fun _ : Fin m => Γ.userLaw)) ≤
      δ + 1 / (2 * Real.sqrt m) := by
  by_cases hr : 0 < r
  · simp_rw [localZeroShare_eq_zero_of_reserve_pos Γ hr j, integral_zero]
    positivity
  · have hr0 : r = 0 := le_antisymm (le_of_not_gt hr) Γ.reserve_nonneg
    have htail := (price_tail_below Γ δ 0 (by rw [hr0]) hP j).le
    apply (integral_localZeroShare_le_shortfall Γ j i).trans
    have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
    have hh := PiBinomial.integral_normalized_shortfall_le Γ.userLaw (aboveAt j 0)
      (measurableSet_aboveAt j 0) (Finset.univ : Finset (Fin m)) (by simpa using hm)
      ((c : ℝ) / m) ((c : ℝ) / m) δ hδ htail
    simpa only [Finset.card_univ, Fintype.card_fin, sub_self, abs_zero, add_zero,
      mul_div_cancel₀ _ hmR.ne', slotShortfall] using hh

theorem integral_gap_localStatistic_le (Γ : FiniteGame m n c r Seed)
    (hm : 0 < m) (hn : 0 < n) (j : Fin n)
    (hT : UniformReserveRule Γ.seedLaw (Γ.policy j) r)
    (i : Fin m) (δ : ℝ) (hδ : 0 ≤ δ) (hδκ : δ < (c : ℝ) / m) :
    (∫ d, localStatistic Γ j (gapWeight j (price Γ δ)) d i
      ∂(Measure.pi fun _ : Fin m => Γ.userLaw)) ≤
      2 * price Γ δ * (δ + 1 / (2 * Real.sqrt m)) := by
  let p := price Γ δ
  let η := δ + 1 / (2 * Real.sqrt m)
  have hp : 0 ≤ p := price_nonneg Γ δ hn hδκ
  have hw (x : UserDraw n r) : ‖gapWeight j p x‖ ≤ p := by
    rw [Real.norm_eq_abs, abs_of_nonneg (gapWeight_nonneg j p x)]
    exact gapWeight_le Γ j p hp x
  have hpI := integrable_localPositive Γ j _ (measurable_gapWeight j p) p hp hw i
  have hzI := integrable_localZeroShare Γ j i
  have hsI := integrable_localStatistic Γ j _ (measurable_gapWeight j p) p hp hw i
  have hAdd : Integrable (fun d => localPositive Γ j (gapWeight j p) d i +
      p * localZeroShare Γ j d i) (Measure.pi fun _ : Fin m => Γ.userLaw) :=
    hpI.add (hzI.const_mul p)
  have hb := integral_mono hsI hAdd
    (localStatistic_le_positive_add_zero Γ j hT (gapWeight j p) p hp
      (gapWeight_nonneg j p) (gapWeight_le Γ j p hp) · i)
  rw [integral_add hpI (hzI.const_mul p), integral_const_mul] at hb
  have hpos : (∫ d, localPositive Γ j (gapWeight j p) d i
      ∂(Measure.pi fun _ : Fin m => Γ.userLaw)) ≤ p * η :=
    (integral_positive_gap_le_localError Γ j hT i p hp).trans
      (integral_localError_normalized_le Γ hm hn j hT δ hδ hδκ)
  by_cases hp0 : p = 0
  · rw [hp0, zero_mul, add_zero] at hb
    have hz : (∫ d, localPositive Γ j (gapWeight j 0) d i
        ∂(Measure.pi fun _ : Fin m => Γ.userLaw)) ≤ 0 := by simpa only [hp0, zero_mul] using hpos
    simpa only [← show p = price Γ δ from rfl, hp0, mul_zero, zero_mul] using hb.trans hz
  · have hpp : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
    have hzero := integral_localZeroShare_le_slotError Γ hm j i δ hδ hpp
    have hz := mul_le_mul_of_nonneg_left hzero hp
    nlinarith

theorem integral_typePaymentError_le (Γ : FiniteGame m n c r Seed)
    (hm : 0 < m) (hn : 0 < n) (δ : ℝ) (hδ : 0 ≤ δ) (hδκ : δ < (c : ℝ) / m)
    (hT : ∀ j, UniformReserveRule Γ.seedLaw (Γ.policy j) r) (i : Fin m) :
    (∫ v, Γ.typePaymentError i (price Γ δ) v ∂Γ.F) ≤
      2 * (n : ℝ) * price Γ δ * (δ + 1 / (2 * Real.sqrt m)) := by
  rw [integral_typePaymentError_eq_sum_localStatistic Γ i _ (price_nonneg Γ δ hn hδκ)]
  have h := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) =>
    integral_gap_localStatistic_le Γ hm hn j (hT j) i δ hδ hδκ
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  nlinarith [h]

theorem integral_typeLoad_le_capacity (Γ : FiniteGame m n c r Seed)
    (hT : ∀ j, UniformReserveRule Γ.seedLaw (Γ.policy j) r) (i : Fin m) :
    (∫ v, (Γ.typeOutcome i v).load ∂Γ.F) ≤ (n : ℝ) * ((c : ℝ) / m) := by
  rw [integral_typeLoad_eq_sum_localStatistic Γ i]
  have h := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) =>
    integral_localStatistic_one_le_capacity Γ j (hT j) i
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h

theorem positiveLoad_le_integral_typeLoad (Γ : FiniteGame m n c r Seed)
    (hT : ∀ j, UniformReserveRule Γ.seedLaw (Γ.policy j) r) (i : Fin m) :
    positiveLoad Γ ≤ ∫ v, (Γ.typeOutcome i v).load ∂Γ.F := by
  rw [integral_typeLoad_eq_sum_localStatistic Γ i, positiveLoad, Finset.sum_div]
  apply Finset.sum_le_sum
  intro j _
  rw [← sum_integral_positive_eq_card Γ j,
    ← integral_localPositive_identity_average Γ j (hT j) _ measurable_const i]
  apply integral_mono
    (integrable_localPositive Γ j (fun _ => 1) measurable_const 1
      (by norm_num) (fun _ => by norm_num) i)
    (integrable_localStatistic Γ j (fun _ => 1) measurable_const 1
      (by norm_num) (fun _ => by norm_num) i)
  exact fun d => localPositive_le_statistic Γ j (fun _ => 1) (fun _ => by norm_num) d i

theorem integral_typeLoad_lower_of_price_gt_reserve (Γ : FiniteGame m n c r Seed)
    (hm : 0 < m) (δ : ℝ) (hδ : 0 ≤ δ) (hPr : r < price Γ δ)
    (hT : ∀ j, UniformReserveRule Γ.seedLaw (Γ.policy j) r) (i : Fin m) :
    (n : ℝ) * ((c : ℝ) / m) - (n : ℝ) * (δ + 1 / (2 * Real.sqrt m)) ≤
      ∫ v, (Γ.typeOutcome i v).load ∂Γ.F :=
  (positiveLoad_lower_of_price_gt_reserve Γ hm δ hδ hPr hT).trans
    (positiveLoad_le_integral_typeLoad Γ hT i)

end FCAppendix.CommonReserve
