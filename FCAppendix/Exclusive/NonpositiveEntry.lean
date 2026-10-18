import FCAppendix.Exclusive.SourceLowTypeOptimal

namespace FCAppendix.Bayes.ExclusiveConstruction
open MeasureTheory ProbabilityTheory Game Exclusive

theorem nonpositive_exclusiveTariffBestResponse
    {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m n c Seed) (a : UserTariff) (ha : a.Allowed)
    (i : Fin m) (v : ℝ) (hv : v ≤ Γ.g) :
    ExclusiveTariffBestResponse Γ a i v (Interim.abstain n) := by
  intro act
  rw [exclusiveTariffPayoff_abstain]
  let mu := (problem Γ i).outcome act
  have hb : 0 ≤ a.expected mu := mu.expect_nonneg fun r => a.charge_nonneg ha r.val
  have hG : mu.success ≤ mu.charge Γ.G := by
    exact mu.expect_mono fun r => by
      by_cases hr : r.val = 0
      · simp [hr, Γ.G.zero, successIndicator]
      · simp only [successIndicator, if_neg hr]
        exact Γ.G.lower r.val (by omega) (by have := r.isLt; omega)
  have hbase := mul_le_mul_of_nonneg_left hG Γ.g_nonneg
  have hvalue := mul_le_mul_of_nonneg_right hv mu.success_nonneg
  change v*mu.success-act.bid*a.expected mu-Γ.g*mu.charge Γ.G ≤ 0
  nlinarith [mul_nonneg act.bid_nonneg hb]

end FCAppendix.Bayes.ExclusiveConstruction
