import FCAppendix.Exclusive.SourceLowTypePrice
import FCAppendix.Exclusive.NarrowGlobalPriceNeighborhood

noncomputable section
namespace FCAppendix.Bayes.ExclusiveSource
open MeasureTheory ProbabilityTheory Game Exclusive ExclusiveNarrow Set Filter
open Exclusive.Narrow.Global

variable {Seed : Type*} [MeasurableSpace Seed]

theorem exists_actual_price_neighborhood (d : ℕ) (hd : 1 ≤ d)
    (h rho cap tolerance deltaCap : ℝ) (hh : 0 < h) (hrho : 0 < rho) (hrh : rho < h)
    (hcap : 0 < cap) (htol : 0 < tolerance) (hdeltaCap : 0 < deltaCap) :
    ∃ delta eta : ℝ, ∃ M0 : ℕ, 0 < delta ∧ delta ≤ deltaCap ∧ 0 < eta ∧ 0 < M0 ∧
      ∀ (m c : ℕ), M0 ≤ m+1 → ∀ (Γ : FiniteGame (m+1) (d+1) c Seed)
      (i : Fin (m+1)) (scale : ℝ), 0 < scale → scale ≤ cap →
      (∀ᵐ x ∂userProfileLaw Γ,
        BandRivals (scale*Real.exp (-delta)) (scale*Real.exp delta) i x) →
      |(c : ℝ)/((m : ℝ)+1)-rho| < eta → ∀ b : ℝ,
      (userProfileLaw Γ).real
        {x | focalPrice (d+1) (by omega) c i b x ∉
          Icc (scale*(1-rho/h)^d-tolerance) (scale*(1-rho/h)^d+tolerance)} ≤
      (userProfileLaw Γ).real
        {x | eta ≤ |(1+(submittedRivals i x : ℝ))/((m : ℝ)+1)-h|} := by
  obtain ⟨delta0,eta,M0,hdelta0,heta,hM0,hprice⟩ :=
    canonical_native_price_neighborhood d hd h rho cap tolerance hh hrho hrh hcap htol
  let delta := min delta0 deltaCap
  have hdelta : 0 < delta := lt_min hdelta0 hdeltaCap
  refine ⟨delta,eta,M0,hdelta,min_le_right _ _,heta,hM0,?_⟩
  intro m c hm Γ i scale hscale hscaleCap hband hcapacity b
  have hsubset :
      {x | focalPrice (d+1) (by omega) c i b x ∉
        Icc (scale*(1-rho/h)^d-tolerance) (scale*(1-rho/h)^d+tolerance)} ≤ᵐ[userProfileLaw Γ]
      {x | eta ≤ |(1+(submittedRivals i x : ℝ))/((m : ℝ)+1)-h|} := by
    filter_upwards [hband] with x hx hbad
    by_contra hnot
    have hgood : |((submittedRivals i x : ℝ)+1)/((m : ℝ)+1)-h| < eta := by
      simpa only [add_comm] using lt_of_not_ge hnot
    have hB := focalList_rival_band i b x hx
    have hB0 : ∀ j, j ≠ i → listBids (focalList i b x) j = 0 ∨
        listBids (focalList i b x) j ∈
          Icc (scale*Real.exp (-delta0)) (scale*Real.exp delta0) := by
      intro j hj
      rcases hB j hj with hz | hb
      · exact Or.inl hz
      · refine Or.inr ⟨?_,?_⟩
        · exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
            (neg_le_neg (min_le_left delta0 deltaCap))) hscale.le).trans hb.1
        · exact hb.2.trans (mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (min_le_left delta0 deltaCap)) hscale.le)
    have hN := (positiveRival_card_focalList i b x
      (mul_pos hscale (Real.exp_pos _)) hx.highRivals).trans
      (activeRivals_card_eq_submittedRivals i x)
    have hp := hprice (m+1) c hm (listBids (focalList i b x)) i scale hscale hscaleCap hB0
      (by simpa only [hN,Nat.cast_add,Nat.cast_one] using hgood)
      (by simpa only [Nat.cast_add,Nat.cast_one] using hcapacity)
    have hbounds := abs_lt.mp hp.2.2
    exact hbad ⟨by dsimp [focalPrice]; linarith,by dsimp [focalPrice]; linarith⟩
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsubset)

end FCAppendix.Bayes.ExclusiveSource
