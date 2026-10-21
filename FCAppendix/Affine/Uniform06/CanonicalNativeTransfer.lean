import FCAppendix.Affine.Uniform06.CanonicalPureTransfer
import FCAppendix.Affine.Uniform06.EntryNativeSource

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.CanonicalNativeTransfer

open MeasureTheory Set Game Bayes LowBody
open Uniform07 LiteralExperiment LiteralPrefixStieltjes CanonicalOptimizer
open CanonicalPureTransfer EntryNativeSource NativeLowRoute
open LiteralPureComponents

variable {Seed : Type*} [MeasurableSpace Seed]

theorem original_native_full_menu_gap (i : Row) (m : ℕ)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (g : GuardData) {H v b : ℝ}
    (hprefix : PrefixConditions (xi i) g H)
    (cm : (Fin (m-1) → Fin 4) → ℝ)
    (hvH : v≤ H) (hvcap : v≤ ReceiptGap.cap i)
    (hopt : Optimal (sourceCanonicalMarginal i m G g cm) v b)
    (hdom : budget i m G v+eta i*b*sourcePureDuplicate i m G b <
      two (eta i) (sourceCanonicalMarginal i m G g cm)
        (sourceCanonicalDuplicate i m G g cm) v b-
          one (sourceCanonicalMarginal i m G g cm) v b)
    (Γ : FiniteGame m 2 (capacity m) Seed) (focal : Fin m)
    (hT : CountTransport i G g cm Γ focal)
    (hA : Γ.A=Schedule.affine 2 (eta i) (eta_pos i).le
      (by cases i <;> norm_num [eta,etaQ])) (hg : Γ.g=0) :
    0<(problem Γ focal).payoff v (twoAction b) ∧
      ∀ a : JointAction 2,a.routeCount≤1 →
        (problem Γ focal).payoff v a<(problem Γ focal).payoff v (twoAction b) := by
  have hs := original_full_menu_gap i m G g hprefix cm hvH hopt hdom
  have hbcap : b∈Icc (0:ℝ) (ReceiptGap.cap i) :=
    ⟨hopt.1.1,hopt.1.2.trans hvcap⟩
  have hpay := every_fixed_value_payoffs i G g cm Γ focal hT hA hg
  have htwo : (problem Γ focal).payoff v (twoAction b)=broadcast i m G g cm v b := by
    change twoUtility Γ focal v b=broadcast i m G g cm v b
    simpa only [broadcast,Rank.payoff] using (hpay v b hbcap).2
  refine ⟨by rw [htwo]; exact hs.1,?_⟩
  intro a ha
  rw [htwo]
  rcases Nat.eq_zero_or_pos a.routeCount with hz | hp
  · rw [native_zero_route_payoff Γ focal a hz]
    exact hs.1
  · have hroute : a.routeCount=1 := by omega
    rw [singleton_payoff Γ (by norm_num) focal a hroute v,hg,sub_zero]
    by_cases hbv : a.bid≤ v
    · rw [mean_transport i G g cm Γ focal hT ⟨a.bid_nonneg,hbv.trans hvcap⟩]
      simpa only [single,mul_div_assoc] using hs.2 a.bid a.bid_nonneg
    · exact (mul_nonpos_of_nonpos_of_nonneg (by linarith)
        (meanAccept_nonnegative Γ focal a.bid)).trans_lt hs.1

theorem original_labeled_full_menu_gap (i : Row) (m : ℕ)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (g : GuardData) {H v b : ℝ}
    (hprefix : PrefixConditions (xi i) g H)
    (cm : (Fin (m-1) → Fin 4) → ℝ)
    (hvH : v≤ H) (hvcap : v≤ ReceiptGap.cap i)
    (hopt : Optimal (sourceCanonicalMarginal i m G g cm) v b)
    (hdom : budget i m G v+eta i*b*sourcePureDuplicate i m G b <
      two (eta i) (sourceCanonicalMarginal i m G g cm)
        (sourceCanonicalDuplicate i m G g cm) v b-
          one (sourceCanonicalMarginal i m G g cm) v b)
    (Γ : FiniteGame m 2 (capacity m) Seed) (focal : Fin m)
    (hT : CountTransport i G g cm Γ focal)
    (hrecipient : ∀ a∈Icc (0:ℝ) (ReceiptGap.cap i),∀ j : Fin 2,
      acceptProb Γ focal a j=(sourceSuccess i m G g cm a+sourceDuplicate i m G g cm a)/2)
    (hA : Γ.A=Schedule.affine 2 (eta i) (eta_pos i).le
      (by cases i <;> norm_num [eta,etaQ])) (hg : Γ.g=0) :
    0< twoUtility Γ focal v b ∧ ∀ j : Fin 2,∀ a≥0,
      recipientUtility Γ focal j v a< twoUtility Γ focal v b := by
  have hs := original_full_menu_gap i m G g hprefix cm hvH hopt hdom
  have htwo : twoUtility Γ focal v b=broadcast i m G g cm v b := by
    simpa only [broadcast,Rank.payoff] using
      (every_fixed_value_payoffs i G g cm Γ focal hT hA hg v b
        ⟨hopt.1.1,hopt.1.2.trans hvcap⟩).2
  refine ⟨by rw [htwo]; exact hs.1,?_⟩
  intro j a ha
  rw [htwo,recipientUtility]
  by_cases hav : a≤ v
  · rw [hrecipient a ⟨ha,hav.trans hvcap⟩ j]
    simpa only [single,mul_div_assoc] using hs.2 a ha
  · have hq : 0≤ acceptProb Γ focal a j := by unfold acceptProb; positivity
    exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) hq).trans_lt hs.1

end FCAppendix.Affine.Uniform06.CanonicalNativeTransfer
