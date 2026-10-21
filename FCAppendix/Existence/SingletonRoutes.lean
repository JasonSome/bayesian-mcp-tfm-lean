import FCAppendix.Finite.NestedRouting
import FCAppendix.Probability.CountPushforward

noncomputable section
namespace FCAppendix.Existence.Singleton
open MeasureTheory Set Filter

theorem count_probability_ofMeasure {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] {n : ℕ}
    (K : Omega → Fin (n+1)) (hK : Measurable K) (P : Fin (n+1) → Prop) :
    (CountLaw.ofMeasure mu K hK).prob P=mu.real {omega | P (K omega)} := by
  classical
  rw [FiniteLaw.prob_eq_expect,CountLaw.expect_ofMeasure]
  have hset : MeasurableSet {omega | P (K omega)} := hK (Set.toFinite _).measurableSet
  simpa only [Set.indicator,Set.mem_setOf_eq,Pi.one_apply] using integral_indicator_one (μ:=mu) hset

theorem duplicate_probability_from_two_contacts {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] {n : ℕ}
    (K : Omega → Fin (n+1)) (hK : Measurable K) (E F : Set Omega)
    (_hE : MeasurableSet E) (hF : MeasurableSet F) (q0 : ℝ)
    (hleft : q0 ≤ mu.real E) (hright : q0 ≤ mu.real F)
    (hboth : ∀ᵐ omega ∂mu, omega ∈ E ∩ F → 2 ≤ (K omega).val) :
    2*q0-1 ≤ (CountLaw.ofMeasure mu K hK).prob (fun r => 2 ≤ r.val) := by
  have hu := measureReal_union_add_inter (μ:=mu) (s:=E) hF (measure_ne_top _ _) (measure_ne_top _ _)
  have hU : mu.real (E ∪ F) ≤ 1 := by
    have hh := measureReal_mono (μ:=mu) (subset_univ (E ∪ F))
    simpa only [probReal_univ] using hh
  have hi : 2*q0-1 ≤ mu.real (E ∩ F) := by linarith
  rw [count_probability_ofMeasure]
  exact hi.trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hboth))

theorem payoff_le_net_minus_duplicate_probability {n : ℕ} (law : CountLaw n)
    (A G : Schedule n) {v b g d : ℝ} (hb : 0 ≤ b) (_hg : 0 ≤ g) (hw : 0 ≤ v-g)
    (hG1 : G.charge 1=1)
    (hd : ∀ r : ℕ, 2 ≤ r → r ≤ n → d ≤ g*(G.charge r-1)) :
    law.utility v b g A G ≤ (v-g)-d*law.prob (fun r => 2 ≤ r.val) := by
  classical
  have hh : ∀ r : Fin (n+1), userPayoff v b g A.charge G.charge r.val ≤
      (v-g)-d*(if 2 ≤ r.val then (1:ℝ) else 0) := by
    intro r
    by_cases hr0 : r.val=0
    · rw [hr0,userPayoff_zero v b g A.charge G.charge A.zero G.zero]
      simpa only [show ¬(2:ℕ) ≤ 0 by omega,if_false,mul_zero,sub_zero] using hw
    · have hA := mul_nonneg hb (A.nonneg r.val (by omega))
      by_cases hr1 : r.val=1
      · rw [hr1] at hA
        simp only [hr1,userPayoff,successIndicator,Nat.one_ne_zero,if_false,hG1,mul_one,
          show ¬(2:ℕ) ≤ 1 by omega,mul_zero,sub_zero]
        linarith
      · have hdelta := hd r.val (by omega) (by omega)
        simp only [userPayoff,successIndicator,if_neg hr0,mul_one,if_pos (show 2 ≤ r.val by omega)]
        nlinarith
  have hi := law.expect_mono hh
  rw [law.expect_sub,law.expect_const,law.expect_const_mul,← FiniteLaw.prob_eq_expect] at hi
  exact hi

theorem all_duplicate_routes_strictly_worse {n : ℕ} (law : CountLaw n)
    (A G : Schedule n) {v b g d q0 H U : ℝ} (hb : 0 ≤ b) (hg : 0 ≤ g)
    (hw : 0 ≤ v-g) (hwH : v-g ≤ H) (hd0 : 0<d) (hq1 : q0 ≤ 1)
    (hG1 : G.charge 1=1)
    (hd : ∀ r : ℕ, 2 ≤ r → r ≤ n → d ≤ g*(G.charge r-1))
    (hpair : 2*q0-1 ≤ law.prob (fun r => 2 ≤ r.val))
    (hgap : H*(1-q0)<d*(2*q0-1)) (hU : (v-g)*q0 ≤ U) :
    law.utility v b g A G<U := by
  have hu := payoff_le_net_minus_duplicate_probability law A G hb hg hw hG1 hd
  have hp := mul_le_mul_of_nonneg_left hpair hd0.le
  have hH := mul_le_mul_of_nonneg_right hwH (sub_nonneg.mpr hq1)
  nlinarith

end FCAppendix.Existence.Singleton
