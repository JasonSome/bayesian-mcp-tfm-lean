import FCAppendix.Existence.SingletonRoutes
import FCAppendix.Finite.BalancedOrder

noncomputable section
namespace FCAppendix.Existence.Singleton
open MeasureTheory Game Bayes Set Filter
open scoped BigOperators

theorem native_load_le_duplicate_probability {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Gamma : FiniteGame m n c Seed) (i : Fin m) (act : JointAction n) (_hk : 1 ≤ act.routeCount) :
    ((problem Gamma i).outcome act).load ≤ 1+((act.routeCount:ℝ)-1)*
      ((problem Gamma i).outcome act).prob (fun r => 2 ≤ r.val) := by
  classical
  let mu := sampleLaw Gamma
  let K := focalCount Gamma i act
  have hK := measurable_focalCount Gamma i act
  have hpoint (omega : Sample m n Seed) : ((K omega).val:ℝ) ≤
      1+((act.routeCount:ℝ)-1)*(if 2 ≤ (K omega).val then (1:ℝ) else 0) := by
    by_cases hr : 2 ≤ (K omega).val
    · rw [if_pos hr,mul_one]
      have hle : ((K omega).val:ℝ) ≤ act.routeCount := by exact_mod_cast focalCount_le Gamma i act omega
      linarith
    · rw [if_neg hr,mul_zero,add_zero]
      exact_mod_cast (show (K omega).val ≤ 1 by omega)
  have hi : ((problem Gamma i).outcome act).expect (fun r => (r.val:ℝ)) ≤
      ((problem Gamma i).outcome act).expect (fun r =>
        1+((act.routeCount:ℝ)-1)*(if 2 ≤ r.val then (1:ℝ) else 0)) := by
    rw [problem_outcome,CountLaw.expect_ofMeasure,CountLaw.expect_ofMeasure]
    exact integral_mono_ae (CountLaw.integrable_comp mu K hK (fun r => (r.val:ℝ)))
      (CountLaw.integrable_comp mu K hK (fun r => 1+((act.routeCount:ℝ)-1)*
        (if 2 ≤ r.val then (1:ℝ) else 0))) (Eventually.of_forall hpoint)
  rw [FiniteLaw.expect_add,FiniteLaw.expect_const,FiniteLaw.expect_const_mul,
    ← FiniteLaw.prob_eq_expect] at hi
  exact hi

theorem native_duplicate_probability_of_contact_floor {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Gamma : FiniteGame m n c Seed) (hn : 0<n) (i : Fin m) (act : JointAction n)
    (hk : 2 ≤ act.routeCount) {q0 : ℝ} (hq0 : q0 ≤ 1)
    (hcontact : ∀ j, q0 ≤ acceptProb Gamma i act.bid j) :
    2*q0-1 ≤ ((problem Gamma i).outcome act).prob (fun r => 2 ≤ r.val) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hcontact j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  have hmean : q0 ≤ meanAcceptProb Gamma i act.bid := by
    dsimp only [meanAcceptProb]
    have hm := mul_le_mul_of_nonneg_left hsum (one_div_pos.mpr hnR).le
    simpa only [← mul_assoc,one_div_mul_cancel hnR.ne',one_mul] using hm
  have hload := mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg act.routeCount)
  rw [← load_eq_mean Gamma hn i act] at hload
  have hbound := native_load_le_duplicate_probability Gamma i act (by omega)
  have hkR : (2:ℝ) ≤ act.routeCount := by exact_mod_cast hk
  have hp : ((act.routeCount:ℝ)-1)*(2*q0-1) ≤ (act.routeCount:ℝ)*q0-1 := by
    have hh := mul_nonneg (sub_nonneg.mpr hkR) (sub_nonneg.mpr hq0)
    nlinarith
  have hmult : ((act.routeCount:ℝ)-1)*(2*q0-1) ≤
      ((act.routeCount:ℝ)-1)*((problem Gamma i).outcome act).prob (fun r => 2 ≤ r.val) := by
    linarith
  exact le_of_mul_le_mul_left hmult (by linarith)

end FCAppendix.Existence.Singleton
