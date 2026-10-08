import FCAppendix.PayOnce.LimitFormulas
import FCAppendix.PayOnce.BoundedEndpoint

namespace FCAppendix
namespace PayOnce

open MeasureTheory Filter Set
open scoped Topology

theorem pStar_bridge : ManyProposers.pStar = Limit.pStar := rfl

theorem demand_bridge (μW : Measure ℝ) (n : ℕ) (t : ℝ) :
    ∫ w, ManyProposers.pStar n t w ∂μW = Limit.demand μW n t := rfl

variable (μW : Measure ℝ) [IsProbabilityMeasure μW]

theorem positive_mass_real (hpos : 0 < μW (Ioi 0)) : 0 < μW.real (Ioi 0) :=
  ENNReal.toReal_pos (ne_of_gt hpos) (measure_ne_top μW _)

theorem eventually_capRoot_spec (hpos : 0 < μW (Ioi 0)) {β : ℝ} (hβ : 0 < β) :
    ∀ᶠ n : ℕ in atTop, 0 < Limit.capRoot μW n (β / n) ∧
      ∫ w, ManyProposers.pStar n (Limit.capRoot μW n (β / n)) w ∂μW = β / n := by
  have hP := positive_mass_real μW hpos
  have hlarge : ∀ᶠ n : ℕ in atTop, β / μW.real (Ioi 0) < n :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop _
  filter_upwards [hlarge, eventually_ge_atTop 2] with n hn hn2
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlt : β / n < μW.real (Ioi 0) := by
    rw [div_lt_iff₀ hnR]
    rw [div_lt_iff₀ hP] at hn
    linarith
  obtain ⟨h1, h2⟩ := Limit.capRoot_spec μW hn2 (div_pos hβ hnR) hlt
  exact ⟨h1, h2⟩

theorem cor_tails_ii_capRoot (hlog : Integrable ManyProposers.logPlus μW)
    (hpos : 0 < μW (Ioi 0)) {β : ℝ} (hβ : 0 < β) :
    ∃! T, 0 < T ∧ ∫ w, ManyProposers.logPlus (w / T) ∂μW = β ∧
      Tendsto (fun n : ℕ => Limit.capRoot μW n (β / n)) atTop (𝓝 T) ∧
      (∀ w, Tendsto (fun n : ℕ => (n : ℝ) * Limit.pStar n (Limit.capRoot μW n (β / n)) w)
        atTop (𝓝 (ManyProposers.logPlus (w / T)))) ∧
      (∀ w (j : ℕ), Tendsto (fun n => ManyProposers.binomialMass n
          (Limit.pStar n (Limit.capRoot μW n (β / n)) w) j) atTop
        (𝓝 ((ProbabilityTheory.poissonMeasure (ManyProposers.logPlus (w / T)).toNNReal).real {j}))) ∧
      Tendsto (fun n : ℕ => Limit.coverage μW n (Limit.capRoot μW n (β / n))) atTop
        (𝓝 (∫ w, (1 - Real.exp (-(ManyProposers.logPlus (w / T)))) ∂μW)) ∧
      Tendsto (fun n : ℕ => β / Limit.coverage μW n (Limit.capRoot μW n (β / n))) atTop
        (𝓝 (β / ∫ w, (1 - Real.exp (-(ManyProposers.logPlus (w / T)))) ∂μW)) := by
  obtain ⟨T, ⟨hT, hroot⟩, huniq⟩ := ManyProposers.existsUnique_logRoot μW hlog hpos hβ
  obtain ⟨T', ⟨hT', hroot', hall⟩, _⟩ := ManyProposers.cor_tails_ii μW hlog hpos hβ
  have hTT : T' = T := huniq T' ⟨hT', hroot'⟩
  obtain ⟨ht, hmul, _, hpois, hcov, hmu⟩ := hall _ (eventually_capRoot_spec μW hpos hβ)
  exact ⟨T', ⟨hT', hroot', ht, hmul, hpois, hcov, hmu⟩,
    fun y hy => (huniq y ⟨hy.1, hy.2.1⟩).trans hTT.symm⟩

theorem capRoot_family {n : ℕ} (hn : 2 ≤ n) :
    ∀ β ∈ Ioo 0 ((n : ℝ) * μW.real (Ioi 0)), 0 < Limit.capRoot μW n (β / n) ∧
      ∫ w, ManyProposers.pStar n (Limit.capRoot μW n (β / n)) w ∂μW = β / n := by
  intro β hβ
  obtain ⟨h0, hP⟩ := Limit.capacity_range μW hn hβ.1 hβ.2
  exact Limit.capRoot_spec μW hn h0 hP

theorem cor_tails_iii_bounded_capRoot {n : ℕ} (hn : 2 ≤ n) (hbdd : ∃ B, ∀ᵐ w ∂μW, w ≤ B)
    (hpos : 0 < μW (Ioi 0)) :
    ∃ M, 0 < M ∧ (∀ᵐ w ∂μW, w ≤ M) ∧ (∀ u > 0, 0 < μW (Ioi (M - u))) ∧
      Tendsto (fun β => Limit.capRoot μW n (β / n)) (𝓝[>] 0) (𝓝[<] M) ∧
      (∀ ε > 0, ∀ᶠ β in 𝓝[>] (0 : ℝ), ∀ w ≤ M,
        ManyProposers.pStar n (Limit.capRoot μW n (β / n)) w < ε) ∧
      Tendsto (fun β => Limit.multiplicity μW n β) (𝓝[>] 0) (𝓝 1) := by
  have hP := positive_mass_real μW hpos
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨M, hM, hle, hend, _, hroot, hsup, _, hmu⟩ :=
    BoundedEndpoint.cor_tails_iii_bounded μW hn hbdd hpos (mul_pos hnR hP)
      (capRoot_family μW hn)
  exact ⟨M, hM, hle, hend, hroot, hsup, hmu⟩

theorem cor_tails_iii_sqrt_capRoot {n : ℕ} (hn : 2 ≤ n) {M : ℝ} (hM : 0 < M)
    (hle : ∀ᵐ w ∂μW, w ≤ M) {u₀ : ℝ} {f : ℝ → ℝ} (hu₀ : 0 < u₀)
    (hf : ContinuousOn f (Icc (M - u₀) M)) (hfM : 0 < f M)
    (hdens : ∀ u ∈ Ioc 0 u₀, μW.real (Ioi (M - u)) = ∫ x in (M - u)..M, f x)
    (hpos : 0 < μW (Ioi 0)) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ᶠ β in 𝓝[>] (0 : ℝ),
      C₁ * Real.sqrt β ≤ Limit.multiplicity μW n β - 1 ∧
      Limit.multiplicity μW n β - 1 ≤ C₂ * Real.sqrt β := by
  have hP := positive_mass_real μW hpos
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact BoundedEndpoint.multiplicity_sub_one_theta_sqrt_of_density μW hn hM hle hu₀ hf hfM
    hdens (mul_pos hnR hP) (capRoot_family μW hn)

end PayOnce
end FCAppendix
