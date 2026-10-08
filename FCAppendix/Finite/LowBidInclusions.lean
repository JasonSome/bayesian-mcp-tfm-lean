import FCAppendix.Finite.ReceiptShortfall
import FCAppendix.Finite.ReceiptBoundsAE
import FCAppendix.Probability.PiBinomialMoments

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game
open scoped BigOperators ProbabilityTheory

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def lowBidCount (Γ : FiniteGame m n c Seed) (j : Fin n) (b : ℝ)
    (ω : Background m n Seed) : ℕ := by
  classical
  exact ((allocation (drawsRealization ω.1) Γ.policy ω.2 j) ∩
    Finset.univ.filter (fun i => (ω.1 i).1.2.bid ≤ b)).card

theorem lowBidCount_eq_sum (Γ : FiniteGame m n c Seed) (j : Fin n) (b : ℝ)
    (ω : Background m n Seed) :
    lowBidCount Γ j b ω = ∑ i, if i ∈ allocation (drawsRealization ω.1) Γ.policy ω.2 j ∧
      (ω.1 i).1.2.bid ≤ b then 1 else 0 := by
  classical
  rw [lowBidCount, ← sum_membership]
  simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]

theorem measurable_lowBidCount (Γ : FiniteGame m n c Seed) (j : Fin n) (b : ℝ) :
    Measurable (lowBidCount Γ j b) := by
  classical
  simp_rw [show lowBidCount Γ j b = fun ω => ∑ i, if
    i ∈ allocation (drawsRealization ω.1) Γ.policy ω.2 j ∧ (ω.1 i).1.2.bid ≤ b
    then 1 else 0 from funext (lowBidCount_eq_sum Γ j b)]
  apply Finset.measurable_sum
  intro i _
  apply Measurable.ite _ measurable_const measurable_const
  apply MeasurableSet.inter
  · exact (measurable_allocation_draws Γ j) (Set.to_countable {S : Finset (Fin m) | i ∈ S}).measurableSet
  · exact measurableSet_le ((measurable_bid n).comp
      (measurable_snd.comp (measurable_fst.comp ((measurable_pi_apply i).comp measurable_fst))))
      measurable_const

theorem lowBidCount_le_capacity (Γ : FiniteGame m n c Seed) (j : Fin n) (b : ℝ)
    (ω : Background m n Seed) : lowBidCount Γ j b ω ≤ c :=
  (Finset.card_le_card Finset.inter_subset_left).trans
    (Γ.policy j (observe (drawsRealization ω.1) j) (ω.2 j)).property.1

theorem integrable_lowBidCount (Γ : FiniteGame m n c Seed) (j : Fin n) (b : ℝ) :
    Integrable (fun ω => (lowBidCount Γ j b ω : ℝ)) (backgroundLaw Γ) := by
  apply Integrable.of_bound ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp (measurable_lowBidCount Γ j b)).aestronglyMeasurable c
  apply Filter.Eventually.of_forall
  intro ω
  change ‖(lowBidCount Γ j b ω : ℝ)‖ ≤ (c : ℝ)
  rw [Real.norm_natCast]
  exact_mod_cast lowBidCount_le_capacity Γ j b ω

theorem lowBidCount_le_shortfall (Γ : FiniteGame m n c Seed) (j : Fin n)
    (a : ℝ) (ha : 0 < a)
    (hA : ∀ r : ℕ, 0 < r → r ≤ n → a * (r : ℝ) ≤ Γ.A.charge r)
    (b t : ℝ) (hbt : b < a * t) (ω : Background m n Seed)
    (belief : Fin m → FiniteLaw (Fin n))
    (hopt : Finite.Optimal c
      (beliefReceipts Γ.A belief (observe (drawsRealization ω.1) j))
      (allocation (drawsRealization ω.1) Γ.policy ω.2 j)) :
    (lowBidCount Γ j b ω : ℝ) ≤
      max ((c : ℝ) - PiBinomial.count (aboveAt j t) Finset.univ ω.1) 0 := by
  classical
  apply Finite.optimal_low_card_real_le_shortfall c _ _
    (Finset.univ.filter fun i => ω.1 i ∈ aboveAt j t) _ hopt
  intro h hh l hl
  have hh' : j ∈ firstK (ω.1 h).2 (ω.1 h).1.2.routeCount ∧ t < (ω.1 h).1.2.bid :=
    (Finset.mem_filter.mp hh).2
  have hl' : (ω.1 l).1.2.bid ≤ b := (Finset.mem_filter.mp hl).2
  have hsome : observe (drawsRealization ω.1) j h = some (ω.1 h).1.2.bid := by
    simp [observe, drawsRealization, hh'.1]
  have hrh := (beliefReceipts_bounds Γ.A belief _ a hA h _
    (ω.1 h).1.2.bid_nonneg hsome).1
  have hrl : beliefReceipts Γ.A belief (observe (drawsRealization ω.1) j) l ≤
      (ω.1 l).1.2.bid := by
    by_cases hreach : j ∈ firstK (ω.1 l).2 (ω.1 l).1.2.routeCount
    · exact (beliefReceipts_bounds Γ.A belief _ a hA l _ (ω.1 l).1.2.bid_nonneg
        (by simp [observe, drawsRealization, hreach])).2
    · simp only [observe, drawsRealization, hreach, ↓reduceIte, beliefReceipts]
      exact (ω.1 l).1.2.bid_nonneg
  have hstrict := mul_lt_mul_of_pos_left hh'.2 ha
  linarith

theorem ae_lowBidCount_le_shortfall (Γ : FiniteGame m n c Seed) (j : Fin n)
    (hj : ProposerRationalOnPath Γ j) (a : ℝ) (ha : 0 < a)
    (hA : ∀ r : ℕ, 0 < r → r ≤ n → a * (r : ℝ) ≤ Γ.A.charge r)
    (b t : ℝ) (hbt : b < a * t) : ∀ᵐ ω ∂backgroundLaw Γ,
    (lowBidCount Γ j b ω : ℝ) ≤
      max ((c : ℝ) - PiBinomial.count (aboveAt j t) Finset.univ ω.1) 0 := by
  have hm := (PiBinomial.measurable_count (aboveAt j t) (measurableSet_aboveAt j t)
    (Finset.univ : Finset (Fin m))).comp
      (show Measurable (fun ω : Background m n Seed => ω.1) from measurable_fst)
  have hset : MeasurableSet {ω : Background m n Seed | (lowBidCount Γ j b ω : ℝ) ≤
      max ((c : ℝ) - PiBinomial.count (aboveAt j t) Finset.univ ω.1) 0} :=
    measurableSet_le ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp (measurable_lowBidCount Γ j b))
      ((measurable_const.sub ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp hm)).max measurable_const)
  apply (Measure.ae_prod_iff_ae_ae hset).mpr
  obtain ⟨belief, hopt⟩ := hj
  have hd := ae_of_ae_map (measurable_observe_draws j).aemeasurable hopt
  filter_upwards [hd] with d hd
  have hs := (measurePreserving_eval (fun _ : Fin n => Γ.seedLaw) j).quasiMeasurePreserving.ae hd
  filter_upwards [hs] with s hs
  exact lowBidCount_le_shortfall Γ j a ha hA b t hbt (d, s) _ hs

theorem integral_lowBidCount_le_shortfall (Γ : FiniteGame m n c Seed) (j : Fin n)
    (hj : ProposerRationalOnPath Γ j) (a : ℝ) (ha : 0 < a)
    (hA : ∀ r : ℕ, 0 < r → r ≤ n → a * (r : ℝ) ≤ Γ.A.charge r)
    (b t : ℝ) (hbt : b < a * t) :
    (∫ ω, (lowBidCount Γ j b ω : ℝ) ∂backgroundLaw Γ) ≤
      ∫ d, max ((c : ℝ) - PiBinomial.count (aboveAt j t) Finset.univ d) 0
        ∂(userProfileLaw Γ) := by
  have hm := (PiBinomial.measurable_count (aboveAt j t) (measurableSet_aboveAt j t)
    (Finset.univ : Finset (Fin m))).comp
      (show Measurable (fun ω : Background m n Seed => ω.1) from measurable_fst)
  have hi : Integrable (fun ω : Background m n Seed =>
      max ((c : ℝ) - PiBinomial.count (aboveAt j t) Finset.univ ω.1) 0) (backgroundLaw Γ) := by
    apply Integrable.of_bound ((measurable_const.sub ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp hm)).max measurable_const).aestronglyMeasurable c
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    apply max_le
    · exact sub_le_self _ (Nat.cast_nonneg _)
    · exact Nat.cast_nonneg _
  have hle := integral_mono_ae (integrable_lowBidCount Γ j b) hi
    (ae_lowBidCount_le_shortfall Γ j hj a ha hA b t hbt)
  simpa only [backgroundLaw, integral_fun_fst (fun d : UserProfile m n =>
    max ((c : ℝ) - PiBinomial.count (aboveAt j t) Finset.univ d) 0),
    probReal_univ, one_smul, userProfileLaw] using hle

theorem integral_lowBidCount_le (Γ : FiniteGame m n c Seed) (j : Fin n)
    (hj : ProposerRationalOnPath Γ j) (a : ℝ) (ha : 0 < a)
    (hA : ∀ r : ℕ, 0 < r → r ≤ n → a * (r : ℝ) ≤ Γ.A.charge r)
    (b t : ℝ) (hbt : b < a * t) :
    (∫ ω, (lowBidCount Γ j b ω : ℝ) ∂backgroundLaw Γ) ≤
      max ((c : ℝ) - m * alphaGt Γ j t) 0 + Real.sqrt m / 2 := by
  apply (integral_lowBidCount_le_shortfall Γ j hj a ha hA b t hbt).trans
  simpa only [Finset.card_univ, Fintype.card_fin, alphaGt, userProfileLaw] using
    PiBinomial.integral_shortfall_le (userLaw Γ) (aboveAt j t) (measurableSet_aboveAt j t)
      (Finset.univ : Finset (Fin m)) c

theorem integral_lowBidCount_normalized_le (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (j : Fin n) (hj : ProposerRationalOnPath Γ j) (a : ℝ) (ha : 0 < a)
    (hA : ∀ r : ℕ, 0 < r → r ≤ n → a * (r : ℝ) ≤ Γ.A.charge r)
    (b t ρ ε : ℝ) (hbt : b < a * t) (hε : 0 ≤ ε)
    (ht : ρ - ε ≤ alphaGt Γ j t) :
    (∫ ω, (lowBidCount Γ j b ω : ℝ) ∂backgroundLaw Γ) / m ≤
      ε + |(c : ℝ) / m - ρ| + 1 / (2 * Real.sqrt m) := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  apply (div_le_div_of_nonneg_right
    (integral_lowBidCount_le_shortfall Γ j hj a ha hA b t hbt) hmR.le).trans
  have hh := PiBinomial.integral_normalized_shortfall_le (userLaw Γ) (aboveAt j t)
    (measurableSet_aboveAt j t) (Finset.univ : Finset (Fin m)) (by simpa using hm)
    ((c : ℝ) / m) ρ ε hε ht
  simpa only [Finset.card_univ, Fintype.card_fin, mul_div_cancel₀ _ hmR.ne',
    userProfileLaw] using hh

noncomputable def lowBidTotal (Γ : FiniteGame m n c Seed) (b : ℝ)
    (ω : Background m n Seed) : ℝ := ∑ j, (lowBidCount Γ j b ω : ℝ)

theorem lowBidTotal_eq_user_sum (Γ : FiniteGame m n c Seed) (b : ℝ)
    (ω : Background m n Seed) :
    lowBidTotal Γ b ω = ∑ i, if (ω.1 i).1.2.bid ≤ b then
      ((playedCount Γ i ω).val : ℝ) else 0 := by
  classical
  simp only [lowBidTotal, lowBidCount_eq_sum, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  change (∑ j, if i ∈ allocation (drawsRealization ω.1) Γ.policy ω.2 j ∧
      (ω.1 i).1.2.bid ≤ b then (1 : ℝ) else 0) =
    if (ω.1 i).1.2.bid ≤ b then
      (inclusionCount (drawsRealization ω.1) Γ.policy ω.2 i : ℝ) else 0
  by_cases hb : (ω.1 i).1.2.bid ≤ b
  · simp only [hb, and_true, ↓reduceIte, inclusionCount_eq_sum, Nat.cast_sum,
      Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  · simp [hb]

theorem integrable_lowBidTotal (Γ : FiniteGame m n c Seed) (b : ℝ) :
    Integrable (lowBidTotal Γ b) (backgroundLaw Γ) :=
  integrable_finsetSum _ (fun j _ => integrable_lowBidCount Γ j b)

theorem integral_lowBidTotal_normalized_le (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (hΓ : ∀ j, ProposerRationalOnPath Γ j) (j₀ : Fin n) (a : ℝ) (ha : 0 < a)
    (hA : ∀ r : ℕ, 0 < r → r ≤ n → a * (r : ℝ) ≤ Γ.A.charge r)
    (b t ρ ε : ℝ) (hbt : b < a * t) (hε : 0 ≤ ε)
    (ht : ρ - ε ≤ alphaGt Γ j₀ t) :
    (∫ ω, lowBidTotal Γ b ω ∂backgroundLaw Γ) / m ≤
      n * (ε + |(c : ℝ) / m - ρ| + 1 / (2 * Real.sqrt m)) := by
  unfold lowBidTotal
  rw [integral_finsetSum _ (fun j _ => integrable_lowBidCount Γ j b), Finset.sum_div]
  calc
    _ ≤ ∑ _j : Fin n, (ε + |(c : ℝ) / m - ρ| + 1 / (2 * Real.sqrt m)) := by
      apply Finset.sum_le_sum
      intro j _
      apply integral_lowBidCount_normalized_le Γ hm j (hΓ j) a ha hA b t ρ ε hbt hε
      rwa [alphaGt_eq Γ j j₀]
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end FCAppendix.Bayes
