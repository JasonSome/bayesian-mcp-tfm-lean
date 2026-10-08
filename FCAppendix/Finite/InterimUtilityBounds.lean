import FCAppendix.Finite.InterimPaymentError
import FCAppendix.Finite.NearPPILimit
import FCAppendix.Probability.UnitInterval

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game
open scoped BigOperators ProbabilityTheory

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payoff_le_price_with_error (Γ : FiniteGame m n c Seed) (i : Fin m)
    (a p v : ℝ) (act : JointAction n)
    (hA : ∀ r, 0 < r → r ≤ n → a * (r : ℝ) ≤ Γ.A.charge r) :
    (problem Γ i).payoff v act ≤
      (v - Γ.g - p) * ((problem Γ i).outcome act).success -
      p * ((problem Γ i).outcome act).duplicates + interimPaymentError Γ i a p (v, act) := by
  let μ := (problem Γ i).outcome act
  have hrec : a * μ.load ≤ μ.charge Γ.A := by
    apply μ.receipt_lower
    intro r hr
    by_cases hz : r = 0
    · simp [hz, Γ.A.zero]
    · exact hA r (Nat.pos_of_ne_zero hz) hr
  have hcharge := mul_le_mul_of_nonneg_left hrec act.bid_nonneg
  have hbase := mul_le_mul_of_nonneg_left (μ.success_le_charge Γ.G) Γ.g_nonneg
  have hgap := mul_le_mul_of_nonneg_right (le_max_left (p - a * act.bid) 0) μ.load_nonneg
  change μ.utility v act.bid Γ.g Γ.A Γ.G ≤ _
  rw [CountLaw.utility_eq]
  change _ ≤ (v - Γ.g - p) * μ.success - p * (μ.load - μ.success) +
    max (p - a * act.bid) 0 * μ.load
  nlinarith

theorem integrable_success_strategy (Γ : FiniteGame m n c Seed) (i : Fin m) (v : ℝ) :
    Integrable (fun act => ((problem Γ i).outcome act).success) (Γ.σ v) :=
  UnitInterval.integrable _ _ (measurable_outcome_expect Γ i _)
    (fun _ => CountLaw.success_nonneg _) (fun _ => CountLaw.success_le_one _)

theorem integrable_duplicates_strategy (Γ : FiniteGame m n c Seed) (i : Fin m) (v : ℝ) :
    Integrable (fun act => ((problem Γ i).outcome act).duplicates) (Γ.σ v) := by
  have hm : Measurable (fun act => ((problem Γ i).outcome act).duplicates) :=
    (measurable_outcome_expect Γ i (fun r => (r.val : ℝ))).sub
      (measurable_outcome_expect Γ i (fun r => successIndicator r.val))
  apply Integrable.of_bound hm.aestronglyMeasurable (n : ℝ)
  apply Filter.Eventually.of_forall
  intro act
  rw [Real.norm_eq_abs, abs_of_nonneg (CountLaw.duplicates_nonneg _)]
  have hL := CountLaw.load_le_n ((problem Γ i).outcome act)
  have hS := CountLaw.success_nonneg ((problem Γ i).outcome act)
  dsimp only [CountLaw.duplicates]
  linarith

theorem integrable_paymentError_strategy (Γ : FiniteGame m n c Seed) (i : Fin m)
    (a p : ℝ) (ha : 0 ≤ a) (hp : 0 ≤ p) (v : ℝ) :
    Integrable (fun act => interimPaymentError Γ i a p (v, act)) (Γ.σ v) := by
  have hm : Measurable (fun act => interimPaymentError Γ i a p (v, act)) :=
    (measurable_interimPaymentError Γ i a p).comp
    (measurable_const.prodMk (show Measurable (fun act : JointAction n => act) from measurable_id))
  apply Integrable.of_bound hm.aestronglyMeasurable (p * n)
  apply Filter.Eventually.of_forall
  intro act
  have hgap : max (p - a * act.bid) 0 ≤ p :=
    max_le (sub_le_self _ (mul_nonneg ha act.bid_nonneg)) hp
  change ‖max (p - a * act.bid) 0 * ((problem Γ i).outcome act).load‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_max_right _ _) (CountLaw.load_nonneg _))]
  exact mul_le_mul hgap (CountLaw.load_le_n _) (CountLaw.load_nonneg _) hp

theorem envelope_le_strategy_price_error (Γ : FiniteGame m n c Seed) (i : Fin m)
    (a p v : ℝ) (ha : 0 ≤ a) (hp : 0 ≤ p)
    (hA : ∀ r, 0 < r → r ≤ n → a * (r : ℝ) ≤ Γ.A.charge r)
    (hbr : ∀ᵐ act ∂Γ.σ v, (problem Γ i).BestResponse v act) :
    (problem Γ i).envelope v ≤
      (v - Γ.g - p) * (∫ act, ((problem Γ i).outcome act).success ∂Γ.σ v) -
      p * (∫ act, ((problem Γ i).outcome act).duplicates ∂Γ.σ v) +
      ∫ act, interimPaymentError Γ i a p (v, act) ∂Γ.σ v := by
  have hiS := (integrable_success_strategy Γ i v).const_mul (v - Γ.g - p)
  have hiD := (integrable_duplicates_strategy Γ i v).const_mul p
  have hiE := integrable_paymentError_strategy Γ i a p ha hp v
  have hh := integral_mono_ae (integrable_const ((problem Γ i).envelope v))
    ((hiS.sub hiD).add hiE) (show (fun _ => (problem Γ i).envelope v) ≤ᵐ[Γ.σ v]
      (fun act => (v - Γ.g - p) * ((problem Γ i).outcome act).success -
        p * ((problem Γ i).outcome act).duplicates + interimPaymentError Γ i a p (v, act)) from by
      filter_upwards [hbr] with act hact
      rw [← (problem Γ i).bestResponse_iff_attains v act |>.mp hact]
      exact payoff_le_price_with_error Γ i a p v act hA)
  have hadd := integral_add (hiS.sub hiD) hiE
  have hsub := integral_sub hiS hiD
  dsimp only [Pi.add_apply, Pi.sub_apply] at hh hadd hsub
  rw [hadd, hsub] at hh
  simpa only [integral_const_mul, integral_const, probReal_univ, one_smul] using hh

noncomputable def typeUtility (Γ : FiniteGame m n c Seed) (v : ℝ) : ℝ :=
  (∑ i, (problem Γ i).envelope v) / m

theorem typeUtility_nonneg (Γ : FiniteGame m n c Seed) (v : ℝ) : 0 ≤ typeUtility Γ v :=
  div_nonneg (Finset.sum_nonneg fun i _ => (problem Γ i).envelope_nonneg v) (Nat.cast_nonneg _)

theorem typeUtility_measurable (Γ : FiniteGame m n c Seed) : Measurable (typeUtility Γ) := by
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro i _
  exact (problem Γ i).envelope_lipschitzWith.continuous.measurable

theorem typeUtility_lower (Γ : FiniteGame m n c Seed) (hm : 0 < m) (v z : ℝ)
    (hz : ∀ i, z ≤ (problem Γ i).envelope v) : z ≤ typeUtility Γ v := by
  apply (le_div_iff₀ (Nat.cast_pos.mpr hm : (0 : ℝ) < m)).mpr
  simpa [mul_comm] using Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m))) (fun i _ => hz i)

end FCAppendix.Bayes
