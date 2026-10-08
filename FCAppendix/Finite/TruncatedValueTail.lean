import FCAppendix.Finite.TruncatedReceiptLower

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Filter
open scoped BigOperators ProbabilityTheory

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem highBidCount_le_arrivals (Γ : FiniteGame m n c Seed)
    (j : Fin n) (R : ℝ) (ω : Background m n Seed) :
    highBidCount Γ j R ω ≤ PiBinomial.count (aboveAt j R) Finset.univ ω.1 := by
  classical
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hiS, hiR⟩ := Finset.mem_inter.mp hi
  have hb := (Finset.mem_filter.mp hiR).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, hb⟩
  have ho := observe_some_of_selected Γ j i ω hiS
  by_cases hj : j ∈ firstK (ω.1 i).2 (ω.1 i).1.2.routeCount
  · exact hj
  · simp [observe, drawsRealization, hj] at ho

theorem integral_highBidCount_le_arrival_mean (Γ : FiniteGame m n c Seed)
    (j : Fin n) (R : ℝ) :
    (∫ ω, (highBidCount Γ j R ω : ℝ) ∂backgroundLaw Γ) ≤ m * alphaGt Γ j R := by
  have hi : Integrable (fun ω : Background m n Seed =>
      (PiBinomial.count (aboveAt j R) Finset.univ ω.1 : ℝ)) (backgroundLaw Γ) :=
    CountLaw.integrable_comp (backgroundLaw Γ)
      (fun ω => PiBinomial.boundedCount (aboveAt j R) Finset.univ ω.1)
      ((PiBinomial.measurable_boundedCount (aboveAt j R) (measurableSet_aboveAt j R)
        (Finset.univ : Finset (Fin m))).comp measurable_fst) (fun r => (r.val : ℝ))
  have he : (∫ ω : Background m n Seed,
      (PiBinomial.count (aboveAt j R) Finset.univ ω.1 : ℝ) ∂backgroundLaw Γ) =
      m * alphaGt Γ j R := by
    simp only [backgroundLaw, integral_fun_fst (fun d : UserProfile m n =>
      (PiBinomial.count (aboveAt j R) Finset.univ d : ℝ)), probReal_univ, one_smul]
    rw [PiBinomial.integral_count_eq (userLaw Γ) (aboveAt j R)
      (measurableSet_aboveAt j R) Finset.univ (fun k => (k : ℝ))]
    change (IndependentCounts.binomial _ _ _ _).load = _
    rw [IndependentCounts.binomial_load]
    simp only [Finset.card_univ, Fintype.card_fin, alphaGt]
  rw [← he]
  apply integral_mono_ae (integrable_highBidCount Γ j R) hi
  exact Eventually.of_forall fun ω => by
    change (highBidCount Γ j R ω : ℝ) ≤
      (PiBinomial.count (aboveAt j R) Finset.univ ω.1 : ℝ)
    exact_mod_cast highBidCount_le_arrivals Γ j R ω

theorem normalized_highBidCount_le_value_tail (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hc : 0 < c) (hΓ : IsAEEquilibrium Γ) (R : ℝ) (hR : 0 ≤ R) :
    (∑ j, ∫ ω, (highBidCount Γ j R ω : ℝ) ∂backgroundLaw Γ) / m ≤
      n * Γ.F.real (Set.Ioi (Γ.g + R)) := by
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) (fun j _ =>
    (integral_highBidCount_le_arrival_mean Γ j R).trans
      (mul_le_mul_of_nonneg_left (alphaGt_le_value_tail_onPath Γ hm hc hΓ j R hR)
        (Nat.cast_nonneg m)))
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  apply (div_le_iff₀ hmR).mpr
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_assoc, mul_comm, mul_left_comm] using hsum

theorem finiteTruncatedPayment_lower_value_tail (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hc : 0 < c) (B : PosteriorSystem Γ)
    (hu : UsersOptimal Γ) (hB : BayesReceiptOptimalOnPath Γ B)
    (a t R : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) (hR : 0 ≤ R)
    (hA : ∀ r : ℕ, 0 < r → r ≤ n → a * (r : ℝ) ≤ Γ.A.charge r) :
    (a * t) * (finiteLoad Γ - n * Γ.F.real (Set.Ioi (Γ.g + R)) -
      (∑ j, ∫ d, max ((c : ℝ) - PiBinomial.count (aboveAt j t) Finset.univ d) 0
        ∂userProfileLaw Γ) / m) ≤ finiteTruncatedPayment Γ R := by
  have htail := normalized_highBidCount_le_value_tail Γ hm hc
    (posterior_isAEEquilibrium_onPath Γ B hu hB) R hR
  apply le_trans _ (finiteTruncatedPayment_lower_counts Γ B hB a t R ha ht hR hA)
  exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg ha ht)

theorem normalized_receiptArrivalShortfall_le (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (j₀ : Fin n) (t ρ ε : ℝ) (hε : 0 ≤ ε)
    (ht : ρ - ε ≤ alphaGt Γ j₀ t) :
    (∑ j, ∫ d, max ((c : ℝ) - PiBinomial.count (aboveAt j t) Finset.univ d) 0
      ∂userProfileLaw Γ) / m ≤
        n * (ε + |(c : ℝ) / m - ρ| + 1 / (2 * Real.sqrt m)) := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hh (j : Fin n) :
      (∫ d, max ((c : ℝ) - PiBinomial.count (aboveAt j t) Finset.univ d) 0
        ∂userProfileLaw Γ) / m ≤
          ε + |(c : ℝ) / m - ρ| + 1 / (2 * Real.sqrt m) := by
    have hprob : ρ - ε ≤ alphaGt Γ j t := by rwa [alphaGt_eq Γ j j₀ t]
    have h := PiBinomial.integral_normalized_shortfall_le (userLaw Γ) (aboveAt j t)
      (measurableSet_aboveAt j t) (Finset.univ : Finset (Fin m)) (by simpa using hm)
      ((c : ℝ) / m) ρ ε hε hprob
    simpa only [Finset.card_univ, Fintype.card_fin, mul_div_cancel₀ _ hmR.ne',
      userProfileLaw] using h
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) (fun j _ => hh j)
  simpa only [← Finset.sum_div, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] using h

theorem finiteTruncatedPayment_lower_quantitative (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hc : 0 < c) (B : PosteriorSystem Γ)
    (hu : UsersOptimal Γ) (hB : BayesReceiptOptimalOnPath Γ B) (j₀ : Fin n)
    (a t R ρ ε : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) (hR : 0 ≤ R) (hε : 0 ≤ ε)
    (hA : ∀ r : ℕ, 0 < r → r ≤ n → a * (r : ℝ) ≤ Γ.A.charge r)
    (hquant : ρ - ε ≤ alphaGt Γ j₀ t) :
    (a * t) * (finiteLoad Γ - n * Γ.F.real (Set.Ioi (Γ.g + R)) -
      n * (ε + |(c : ℝ) / m - ρ| + 1 / (2 * Real.sqrt m))) ≤
        finiteTruncatedPayment Γ R := by
  have hs := normalized_receiptArrivalShortfall_le Γ hm j₀ t ρ ε hε hquant
  apply le_trans _
    (finiteTruncatedPayment_lower_value_tail Γ hm hc B hu hB a t R ha ht hR hA)
  exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg ha ht)

end FCAppendix.Bayes
