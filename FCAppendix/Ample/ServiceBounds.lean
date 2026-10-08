import FCAppendix.Ample.Deficit
import FCAppendix.Finite.ConditionalCountLaw

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Filter Set Topology
open scoped BigOperators ProbabilityTheory

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem bestResponse_success_zero_below_fee (P : Interim.Problem n) (v : ℝ)
    (act : JointAction n) (hbr : P.BestResponse v act) (hv : v < P.g) :
    (P.outcome act).success = 0 := by
  have hpay : 0 ≤ P.payoff v act := by
    simpa only [P.payoff_abstain] using hbr (Interim.abstain n)
  have hA := mul_nonneg act.bid_nonneg ((P.outcome act).charge_nonneg P.A)
  have hG := mul_le_mul_of_nonneg_left ((P.outcome act).success_le_charge P.G) P.g_nonneg
  have hb : P.payoff v act ≤ (v - P.g) * (P.outcome act).success := by
    simp only [Interim.Problem.payoff, CountLaw.utility_eq]
    linarith
  apply le_antisymm _ (P.outcome act).success_nonneg
  nlinarith

theorem ae_conditional_success_zero_below_fee (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hu : UsersOptimal Γ) :
    ∀ᵐ v ∂Γ.F, v < Γ.g → (conditionalTypeCountLaw Γ hm v).success = 0 := by
  filter_upwards [ae_all_iff.mpr hu] with v hv hvg
  rw [conditionalTypeCountLaw_success]
  have hz (i : Fin m) : (∫ act, ((problem Γ i).outcome act).success ∂Γ.σ v) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hv i] with act ha
    exact bestResponse_success_zero_below_fee (problem Γ i) v act ha hvg
  simp only [hz, Finset.sum_const_zero, zero_div]

theorem finiteCoverage_le_nonnegative_population (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hu : UsersOptimal Γ) :
    finiteCoverage Γ ≤ Γ.F.real (Ici Γ.g) := by
  classical
  rw [← integral_conditionalTypeCountLaw_success Γ hm, ← integral_indicator_one measurableSet_Ici]
  apply integral_mono_ae (integrable_conditionalTypeCountLaw_success Γ hm)
    ((integrable_const (1 : ℝ)).indicator measurableSet_Ici)
  filter_upwards [ae_conditional_success_zero_below_fee Γ hm hu] with v hv
  by_cases hgv : Γ.g ≤ v
  · simpa only [indicator_of_mem (show v ∈ Ici Γ.g from hgv), Pi.one_apply] using
      (conditionalTypeCountLaw Γ hm v).success_le_one
  · rw [indicator_of_notMem (show v ∉ Ici Γ.g from hgv), hv (lt_of_not_ge hgv)]

theorem finiteCoverage_le_positive_population (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hu : UsersOptimal Γ) (hg : Γ.F {Γ.g} = 0) :
    finiteCoverage Γ ≤ Γ.F.real (Ioi Γ.g) := by
  have he : Γ.F.real (Ici Γ.g) = Γ.F.real (Ioi Γ.g) :=
    measureReal_congr (Ioi_ae_eq_Ici' hg).symm
  rw [← he]
  exact finiteCoverage_le_nonnegative_population Γ hm hu

end FCAppendix.Bayes

namespace FCAppendix.CountLaw

variable {n : ℕ}

theorem duplicate_probability_le_excess_base (μ : CountLaw n) (G : Schedule n)
    (g d : ℝ)
    (hd : ∀ r, 2 ≤ r → r ≤ n → d ≤ g * (G.charge r - 1)) :
    d * μ.prob (fun r => 2 ≤ r.val) ≤ g * (μ.charge G - μ.success) := by
  classical
  rw [FiniteLaw.prob_eq_expect, ← μ.expect_const_mul]
  have he : g * (μ.charge G - μ.success) =
      μ.expect (fun r => g * (G.charge r.val - successIndicator r.val)) := by
    rw [μ.expect_const_mul, μ.expect_sub]
    rfl
  rw [he]
  apply μ.expect_mono
  intro r
  by_cases hr : 2 ≤ r.val
  · simpa only [if_pos hr, mul_one, successIndicator, if_neg (by omega : r.val ≠ 0)] using
      hd r.val hr (by omega)
  · rw [if_neg hr, mul_zero]
    by_cases hz : r.val = 0
    · simp [hz, G.zero, successIndicator]
    · have h1 : r.val = 1 := by omega
      simp [h1, G.one (by omega), successIndicator]

end FCAppendix.CountLaw

namespace FCAppendix.Ample

open Filter Topology
variable {n : ℕ}

theorem excess_base_le_deficit (P : Interim.Problem n) (w : ℝ) (hw : 0 ≤ w)
    (act : Game.JointAction n) (hbr : P.BestResponse (w + P.g) act) :
    P.g * ((P.outcome act).charge P.G - (P.outcome act).success) ≤ deficit P w := by
  have h := deficit_identity P w act hbr
  have h1 := mul_nonneg hw (sub_nonneg.mpr (P.outcome act).success_le_one)
  have h2 := mul_nonneg act.bid_nonneg ((P.outcome act).charge_nonneg P.A)
  linarith

theorem all_bestResponses_full_service_of_deficit
    (P : ℕ → Interim.Problem n) (w : ℝ) (hw : 0 < w)
    (hdef : Tendsto (fun k => deficit (P k) w) atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ act : Game.JointAction n,
      (P k).BestResponse (w + (P k).g) act →
      1 - ((P k).outcome act).success < ε ∧ act.bid < ε ∧
      (P k).g * (((P k).outcome act).charge (P k).G -
        ((P k).outcome act).success) < ε := by
  intro ε hε
  have hdw : Tendsto (fun k => deficit (P k) w / w) atTop (𝓝 0) := by
    simpa using hdef.div_const w
  filter_upwards [(tendsto_order.mp hdw).2 ε hε,
    (tendsto_order.mp hdw).2 (1 / 2) (by norm_num),
    (tendsto_order.mp hdef).2 (ε / 2) (half_pos hε),
    (tendsto_order.mp hdef).2 ε hε] with k h1 hhalf hbid hbase
  intro act hbr
  have hc := deficit_controls (P k) w hw act hbr
  have hS : (1 / 2 : ℝ) < ((P k).outcome act).success := by linarith
  have hrec := ((P k).outcome act).success_le_charge (P k).A
  have hmul := mul_le_mul_of_nonneg_left hrec act.bid_nonneg
  refine ⟨lt_of_le_of_lt hc.1 h1, ?_,
    (excess_base_le_deficit (P k) w hw.le act hbr).trans_lt hbase⟩
  nlinarith

end FCAppendix.Ample
