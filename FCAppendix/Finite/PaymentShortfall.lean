import FCAppendix.Finite.LowBidInclusions

namespace FCAppendix.Game

open scoped BigOperators

theorem weighted_double_count {m n c : ℕ} {Seed : Type*}
    (x : Realization m n) (policy : Fin n → LocalPolicy m c Seed)
    (seed : Fin n → Seed) (w : Fin m → ℝ) :
    (∑ j, ∑ i ∈ allocation x policy seed j, w i) =
      ∑ i, w i * (inclusionCount x policy seed i : ℝ) := by
  classical
  simp_rw [inclusionCount_eq_sum, Nat.cast_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  simp

end FCAppendix.Game

namespace FCAppendix.Finite

open scoped BigOperators

theorem sum_payment_shortfall_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (c : ℕ) (hc : S.card ≤ c) (B : ι → ℝ) (hB : ∀ i, 0 ≤ B i)
    (a p b : ℝ) (ha : 0 ≤ a) (hp : 0 ≤ p) :
    (∑ i ∈ S, max (p - a * B i) 0) ≤
      p * ((S ∩ Finset.univ.filter (fun i => B i ≤ b)).card : ℝ) +
      max (p - a * b) 0 * c := by
  classical
  have hpoint (i : ι) : max (p - a * B i) 0 ≤
      (if B i ≤ b then p else 0) + max (p - a * b) 0 := by
    by_cases hi : B i ≤ b
    · rw [if_pos hi]
      have hm : max (p - a * B i) 0 ≤ p := max_le (sub_le_self _ (mul_nonneg ha (hB i))) hp
      exact hm.trans (le_add_of_nonneg_right (le_max_right _ _))
    · rw [if_neg hi, zero_add]
      exact max_le_max (sub_le_sub_left (mul_le_mul_of_nonneg_left (le_of_not_ge hi) ha) p) le_rfl
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ S) => hpoint i)
  have heq : (∑ i ∈ S, if B i ≤ b then p else 0) =
      p * ((S ∩ Finset.univ.filter (fun i => B i ≤ b)).card : ℝ) := by
    rw [← Finset.sum_filter]
    have hs : S.filter (fun i => B i ≤ b) = S ∩ Finset.univ.filter (fun i => B i ≤ b) := by
      ext i
      simp
    simp only [hs, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [Finset.sum_add_distrib, heq, Finset.sum_const, nsmul_eq_mul] at hsum
  apply hsum.trans
  have hcard : (S.card : ℝ) ≤ c := Nat.cast_le.mpr hc
  nlinarith [mul_le_mul_of_nonneg_left hcard (le_max_right (p - a * b) 0)]

end FCAppendix.Finite

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game
open scoped BigOperators ProbabilityTheory

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def proposerPaymentShortfall (Γ : FiniteGame m n c Seed) (j : Fin n)
    (a p : ℝ) (ω : Background m n Seed) : ℝ :=
  ∑ i ∈ allocation (drawsRealization ω.1) Γ.policy ω.2 j, max (p - a * (ω.1 i).1.2.bid) 0

noncomputable def paymentShortfall (Γ : FiniteGame m n c Seed) (a p : ℝ)
    (ω : Background m n Seed) : ℝ := ∑ j, proposerPaymentShortfall Γ j a p ω

theorem paymentShortfall_eq_user_sum (Γ : FiniteGame m n c Seed) (a p : ℝ)
    (ω : Background m n Seed) :
    paymentShortfall Γ a p ω = ∑ i,
      max (p - a * (ω.1 i).1.2.bid) 0 * ((playedCount Γ i ω).val : ℝ) :=
  weighted_double_count _ _ _ _

theorem proposerPaymentShortfall_le (Γ : FiniteGame m n c Seed) (j : Fin n)
    (a p b : ℝ) (ha : 0 ≤ a) (hp : 0 ≤ p) (ω : Background m n Seed) :
    proposerPaymentShortfall Γ j a p ω ≤ p * (lowBidCount Γ j b ω : ℝ) +
      max (p - a * b) 0 * c :=
  Finite.sum_payment_shortfall_le _ c
    (Γ.policy j (observe (drawsRealization ω.1) j) (ω.2 j)).property.1
    (fun i => (ω.1 i).1.2.bid) (fun i => (ω.1 i).1.2.bid_nonneg) a p b ha hp

theorem paymentShortfall_le (Γ : FiniteGame m n c Seed) (a p b : ℝ)
    (ha : 0 ≤ a) (hp : 0 ≤ p) (ω : Background m n Seed) :
    paymentShortfall Γ a p ω ≤ p * lowBidTotal Γ b ω + n * (max (p - a * b) 0 * c) := by
  have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
    proposerPaymentShortfall_le Γ j a p b ha hp ω)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  dsimp only [paymentShortfall, lowBidTotal]
  nlinarith [hh]

theorem measurable_proposerPaymentShortfall (Γ : FiniteGame m n c Seed) (j : Fin n)
    (a p : ℝ) : Measurable (proposerPaymentShortfall Γ j a p) := by
  classical
  have heq : proposerPaymentShortfall Γ j a p = fun ω => ∑ i, if
      i ∈ allocation (drawsRealization ω.1) Γ.policy ω.2 j then
      max (p - a * (ω.1 i).1.2.bid) 0 else 0 := by
    funext ω
    simp only [proposerPaymentShortfall, ← Finset.sum_filter]
    simp
  rw [heq]
  apply Finset.measurable_sum
  intro i _
  apply Measurable.ite _ _ measurable_const
  · exact (measurable_allocation_draws Γ j) (Set.to_countable {S : Finset (Fin m) | i ∈ S}).measurableSet
  · have hb := (measurable_bid n).comp
      (measurable_snd.comp (measurable_fst.comp ((measurable_pi_apply i).comp
        (show Measurable (fun ω : Background m n Seed => ω.1) from measurable_fst))))
    exact (measurable_const.sub (measurable_const.mul hb)).max measurable_const

theorem integrable_proposerPaymentShortfall (Γ : FiniteGame m n c Seed) (j : Fin n)
    (a p : ℝ) (ha : 0 ≤ a) (hp : 0 ≤ p) :
    Integrable (proposerPaymentShortfall Γ j a p) (backgroundLaw Γ) := by
  apply Integrable.of_bound (measurable_proposerPaymentShortfall Γ j a p).aestronglyMeasurable (p * c)
  apply Filter.Eventually.of_forall
  intro ω
  have hnon : 0 ≤ proposerPaymentShortfall Γ j a p ω :=
    Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnon]
  calc
    _ ≤ ∑ _i ∈ allocation (drawsRealization ω.1) Γ.policy ω.2 j, p := by
      apply Finset.sum_le_sum
      intro i _
      exact max_le (sub_le_self _ (mul_nonneg ha (ω.1 i).1.2.bid_nonneg)) hp
    _ ≤ p * c := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hh : ((allocation (drawsRealization ω.1) Γ.policy ω.2 j).card : ℝ) ≤ c := by
        exact_mod_cast (Γ.policy j (observe (drawsRealization ω.1) j) (ω.2 j)).property.1
      nlinarith [mul_le_mul_of_nonneg_left hh hp]

theorem integrable_paymentShortfall (Γ : FiniteGame m n c Seed)
    (a p : ℝ) (ha : 0 ≤ a) (hp : 0 ≤ p) :
    Integrable (paymentShortfall Γ a p) (backgroundLaw Γ) :=
  integrable_finsetSum _ (fun j _ => integrable_proposerPaymentShortfall Γ j a p ha hp)

theorem integral_paymentShortfall_normalized_le (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (hΓ : ∀ j, ProposerRationalOnPath Γ j) (j₀ : Fin n) (a p b t ρ ε : ℝ)
    (ha : 0 < a) (hp : 0 ≤ p)
    (hA : ∀ r : ℕ, 0 < r → r ≤ n → a * (r : ℝ) ≤ Γ.A.charge r)
    (hbt : b < a * t) (hε : 0 ≤ ε) (ht : ρ - ε ≤ alphaGt Γ j₀ t) :
    (∫ ω, paymentShortfall Γ a p ω ∂backgroundLaw Γ) / m ≤
      p * (n * (ε + |(c : ℝ) / m - ρ| + 1 / (2 * Real.sqrt m))) +
      n * max (p - a * b) 0 * ((c : ℝ) / m) := by
  have hi := (integrable_lowBidTotal Γ b).const_mul p
  have hh := integral_mono_ae (integrable_paymentShortfall Γ a p ha.le hp)
    (hi.add (integrable_const (n * (max (p - a * b) 0 * c))))
    (Filter.Eventually.of_forall (paymentShortfall_le Γ a p b ha.le hp))
  simp only [Pi.add_apply] at hh
  rw [integral_add hi (integrable_const _), integral_const_mul, integral_const,
    probReal_univ, one_smul] at hh
  have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hdiv := div_le_div_of_nonneg_right hh hmR
  have hlo := mul_le_mul_of_nonneg_left
    (integral_lowBidTotal_normalized_le Γ hm hΓ j₀ a ha hA b t ρ ε hbt hε ht) hp
  calc
    _ ≤ (p * (∫ ω, lowBidTotal Γ b ω ∂backgroundLaw Γ) +
      n * (max (p - a * b) 0 * c)) / m := hdiv
    _ = p * ((∫ ω, lowBidTotal Γ b ω ∂backgroundLaw Γ) / m) +
      n * max (p - a * b) 0 * ((c : ℝ) / m) := by ring
    _ ≤ _ := add_le_add hlo le_rfl

end FCAppendix.Bayes
