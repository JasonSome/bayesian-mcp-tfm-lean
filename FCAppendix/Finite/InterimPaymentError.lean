import FCAppendix.Game.RealizedIntegrals
import FCAppendix.Finite.PaymentErrorLimit

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game
open scoped BigOperators ProbabilityTheory

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def paymentErrorTest (a p : ℝ)
    (x : (ℝ × JointAction n) × Fin (n + 1)) : ℝ :=
  max (p - a * x.1.2.bid) 0 * x.2.val

theorem measurable_paymentErrorTest (a p : ℝ) :
    Measurable (paymentErrorTest (n := n) a p) := by
  have hb := (measurable_bid n).comp (measurable_snd.comp
    (show Measurable (fun x : (ℝ × JointAction n) × Fin (n + 1) => x.1) from measurable_fst))
  exact ((measurable_const.sub (measurable_const.mul hb)).max measurable_const).mul
    ((measurable_of_countable (fun r : Fin (n + 1) => (r.val : ℝ))).comp measurable_snd)

theorem paymentErrorTest_bound (a p : ℝ) (ha : 0 ≤ a) (hp : 0 ≤ p)
    (x : (ℝ × JointAction n) × Fin (n + 1)) : ‖paymentErrorTest a p x‖ ≤ p * n := by
  have hgap : max (p - a * x.1.2.bid) 0 ≤ p :=
    max_le (sub_le_self _ (mul_nonneg ha x.1.2.bid_nonneg)) hp
  have hr : (x.2.val : ℝ) ≤ n := Nat.cast_le.mpr (Nat.le_of_lt_succ x.2.isLt)
  rw [paymentErrorTest, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_max_right _ _) (Nat.cast_nonneg _))]
  exact mul_le_mul hgap hr (Nat.cast_nonneg _) hp

noncomputable def interimPaymentError (Γ : FiniteGame m n c Seed) (i : Fin m)
    (a p : ℝ) (x : ℝ × JointAction n) : ℝ :=
  max (p - a * x.2.bid) 0 * ((problem Γ i).outcome x.2).load

theorem paymentErrorTest_expect (Γ : FiniteGame m n c Seed) (i : Fin m)
    (a p : ℝ) (x : ℝ × JointAction n) :
    ((problem Γ i).outcome x.2).expect (fun r => paymentErrorTest a p (x, r)) =
      interimPaymentError Γ i a p x := by
  simpa only [paymentErrorTest, interimPaymentError, CountLaw.load] using
    ((problem Γ i).outcome x.2).expect_const_mul (max (p - a * x.2.bid) 0)
      (fun r : Fin (n + 1) => (r.val : ℝ))

theorem measurable_interimPaymentError (Γ : FiniteGame m n c Seed) (i : Fin m) (a p : ℝ) :
    Measurable (interimPaymentError Γ i a p) := by
  have hh := measurable_interim_expect Γ i (paymentErrorTest a p) (measurable_paymentErrorTest a p)
  simpa only [paymentErrorTest_expect] using hh

theorem integrable_interimPaymentError (Γ : FiniteGame m n c Seed) (i : Fin m)
    (a p : ℝ) (ha : 0 ≤ a) (hp : 0 ≤ p) :
    Integrable (interimPaymentError Γ i a p) (Γ.F ⊗ₘ Γ.σ) := by
  have hh := integrable_interim_expect Γ i (paymentErrorTest a p)
    (measurable_paymentErrorTest a p) (p * n) (paymentErrorTest_bound a p ha hp)
  simpa only [paymentErrorTest_expect] using hh

theorem integral_paymentShortfall_eq_interim (Γ : FiniteGame m n c Seed)
    (a p : ℝ) (ha : 0 ≤ a) (hp : 0 ≤ p) :
    (∫ ω, paymentShortfall Γ a p ω ∂backgroundLaw Γ) =
      ∑ i, ∫ x, interimPaymentError Γ i a p x ∂(Γ.F ⊗ₘ Γ.σ) := by
  simp_rw [paymentShortfall_eq_user_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    have hh := integral_realized_eq_interim Γ i (paymentErrorTest a p)
      (measurable_paymentErrorTest a p) (p * n) (paymentErrorTest_bound a p ha hp)
    simpa only [paymentErrorTest, FiniteLaw.expect_const_mul, CountLaw.load, interimPaymentError] using hh
  · intro i _
    exact integrable_realized_statistic Γ i (paymentErrorTest a p)
      (measurable_paymentErrorTest a p) (p * n) (paymentErrorTest_bound a p ha hp)

noncomputable def typePaymentError (Γ : FiniteGame m n c Seed) (a p : ℝ) (v : ℝ) : ℝ :=
  (∑ i, ∫ act, interimPaymentError Γ i a p (v, act) ∂Γ.σ v) / m

theorem measurable_typePaymentError (Γ : FiniteGame m n c Seed) (a p : ℝ) :
    Measurable (typePaymentError Γ a p) := by
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro i _
  exact (measurable_interimPaymentError Γ i a p).stronglyMeasurable.integral_kernel_prod_right'.measurable

theorem typePaymentError_nonneg (Γ : FiniteGame m n c Seed) (a p v : ℝ) :
    0 ≤ typePaymentError Γ a p v := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro i _
  apply integral_nonneg
  intro act
  exact mul_nonneg (le_max_right _ _) (CountLaw.load_nonneg _)

theorem integrable_typePaymentError (Γ : FiniteGame m n c Seed)
    (a p : ℝ) (ha : 0 ≤ a) (hp : 0 ≤ p) :
    Integrable (typePaymentError Γ a p) Γ.F := by
  apply Integrable.div_const
  apply integrable_finsetSum
  intro i _
  have hi := integrable_interimPaymentError Γ i a p ha hp
  have hnon : ∀ x, 0 ≤ interimPaymentError Γ i a p x :=
    fun x => mul_nonneg (le_max_right _ _) (CountLaw.load_nonneg _)
  have hh := (Measure.integrable_compProd_iff hi.aestronglyMeasurable).mp hi |>.2
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hnon _)] using hh

theorem integral_typePaymentError_eq (Γ : FiniteGame m n c Seed)
    (a p : ℝ) (ha : 0 ≤ a) (hp : 0 ≤ p) :
    (∫ v, typePaymentError Γ a p v ∂Γ.F) =
      (∫ ω, paymentShortfall Γ a p ω ∂backgroundLaw Γ) / m := by
  rw [integral_paymentShortfall_eq_interim Γ a p ha hp]
  unfold typePaymentError
  rw [integral_div, integral_finsetSum]
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact (Measure.integral_compProd (integrable_interimPaymentError Γ i a p ha hp)).symm
  · intro i _
    have hi := integrable_interimPaymentError Γ i a p ha hp
    have hnon : ∀ x, 0 ≤ interimPaymentError Γ i a p x :=
      fun x => mul_nonneg (le_max_right _ _) (CountLaw.load_nonneg _)
    have hh := (Measure.integrable_compProd_iff hi.aestronglyMeasurable).mp hi |>.2
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hnon _)] using hh

theorem tendsto_mean_typePaymentError_of_visible_tail
    (M C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (M k) n (C k) Seed) (j₀ : Fin n)
    (a : ℕ → ℝ) (p ρ : ℝ) (hp : 0 ≤ p) (hρ : 0 ≤ ρ)
    (hM : Filter.Tendsto M Filter.atTop Filter.atTop)
    (ha : Filter.Tendsto a Filter.atTop (nhds 1))
    (hcap : Filter.Tendsto (fun k => (C k : ℝ) / M k) Filter.atTop (nhds ρ))
    (hΓ : ∀ k j, ProposerRationalOnPath (Γ k) j)
    (hA : ∀ k r, 0 < r → r ≤ n → a k * (r : ℝ) ≤ (Γ k).A.charge r)
    (htail : ∀ t < p, ∀ ε > 0, ∀ᶠ k in Filter.atTop, ρ - ε ≤ alphaGt (Γ k) j₀ t) :
    Filter.Tendsto (fun k => ∫ v, typePaymentError (Γ k) (a k) p v ∂(Γ k).F)
      Filter.atTop (nhds 0) := by
  have hh := tendsto_paymentShortfall_of_visible_tail M C Γ j₀ a p ρ hp hρ hM ha hcap hΓ hA htail
  apply hh.congr'
  filter_upwards [(tendsto_order.mp ha).1 0 zero_lt_one] with k hk
  exact (integral_typePaymentError_eq (Γ k) (a k) p hk.le hp).symm

end FCAppendix.Bayes
