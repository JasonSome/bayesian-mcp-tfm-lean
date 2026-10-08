import FCAppendix.Finite.TruncatedValueTail

namespace FCAppendix.Affine

open Filter Topology

noncomputable def fixedFactor (n : ℕ) (η₀ : ℝ) : ℝ :=
  (1 + ((n : ℝ) - 1) * η₀) / n

theorem fixedFactor_pos (n : ℕ) (hn : 0 < n) (η₀ : ℝ) (hη₀ : 0 ≤ η₀) :
    0 < fixedFactor n η₀ := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold fixedFactor
  apply div_pos _ hnR
  nlinarith [mul_nonneg (sub_nonneg.mpr hn1) hη₀]

theorem fixedFactor_charge_lower (n : ℕ) (hn : 0 < n)
    (η₀ η : ℝ) (hη₀ : 0 ≤ η₀) (hη : η₀ ≤ η) (hη1 : η ≤ 1)
    (r : ℕ) (hr : 0 < r) (hrn : r ≤ n) :
    fixedFactor n η₀ * (r : ℝ) ≤ (Schedule.affine n η (hη₀.trans hη) hη1).charge r := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hrR : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hfac : fixedFactor n η₀ ≤ (1 + ((n : ℝ) - 1) * η) / n := by
    apply div_le_div_of_nonneg_right _ hnR.le
    have h := mul_le_mul_of_nonneg_left hη (sub_nonneg.mpr hn1)
    linarith
  have hratio := hfac.trans (Schedule.affine_ratio_lower n r hn hr hrn η
    (hη₀.trans hη) hη1)
  exact (le_div_iff₀ hrR).mp hratio

theorem transfer_le_of_envelope_error (w P S T U extra δ : ℝ)
    (hS0 : 0 ≤ S) (hS1 : S ≤ 1) (he : 0 ≤ extra)
    (hidentity : U = w * S - T - extra)
    (henv : max (w - P) 0 - δ ≤ U) : T ≤ P * S + δ := by
  by_cases hw : w ≤ P
  · rw [max_eq_right (sub_nonpos.mpr hw)] at henv
    have hmul := mul_le_mul_of_nonneg_right hw hS0
    linarith
  · have hwP : 0 ≤ w - P := sub_nonneg.mpr (le_of_not_ge hw)
    rw [max_eq_left hwP] at henv
    nlinarith [mul_nonneg hwP (sub_nonneg.mpr hS1)]

theorem transfer_le_of_envelope (w P S T U extra : ℝ)
    (hS0 : 0 ≤ S) (hS1 : S ≤ 1) (he : 0 ≤ extra)
    (hidentity : U = w * S - T - extra)
    (henv : max (w - P) 0 ≤ U) : T ≤ P * S := by
  have h := transfer_le_of_envelope_error w P S T U extra 0 hS0 hS1 he hidentity
    (by simpa using henv)
  simpa using h

theorem coverage_of_payment_sandwich (a β P Q T : ℝ) (hP : 0 < P)
    (hlower : a ^ 2 * P * β ≤ T) (hupper : T ≤ P * Q) : β * a ^ 2 ≤ Q := by
  nlinarith [hlower.trans hupper]

theorem duplicates_of_coverage (a β Q D : ℝ)
    (hD : D = β - Q) (hQ : β * a ^ 2 ≤ Q) : D ≤ β * (1 - a ^ 2) := by
  nlinarith

theorem multiplicity_of_coverage (n : ℕ) (a β Q μ : ℝ)
    (ha : 0 < a) (hβ : 0 < β) (hμ : μ = β / Q)
    (hQ : β * a ^ 2 ≤ Q) (hcount : β ≤ n * Q) :
    μ ≤ min (n : ℝ) ((a ^ 2)⁻¹) := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hQ0 : 0 < Q := lt_of_lt_of_le (mul_pos hβ ha2) hQ
  rw [hμ]
  apply le_min
  · exact (div_le_iff₀ hQ0).mpr hcount
  · apply (div_le_iff₀ hQ0).mpr
    have h := (div_le_div_of_nonneg_right hQ ha2.le)
    simpa only [mul_div_cancel_right₀ _ ha2.ne', div_eq_mul_inv, mul_comm] using h

theorem strict_baseline_comparison (a β Q Q₀ D D₀ μ μ₀ : ℝ)
    (hβ : 0 < β) (hQ₀ : 0 < Q₀) (hgap : Q₀ < β * a ^ 2)
    (hQ : β * a ^ 2 ≤ Q) (hD : D = β - Q) (hD₀ : D₀ = β - Q₀)
    (hμ : μ = β / Q) (hμ₀ : μ₀ = β / Q₀) :
    Q₀ < Q ∧ D < D₀ ∧ μ < μ₀ := by
  have hQQ : Q₀ < Q := hgap.trans_le hQ
  have hQpos : 0 < Q := hQ₀.trans hQQ
  refine ⟨hQQ, by linarith, ?_⟩
  rw [hμ, hμ₀]
  apply (div_lt_div_iff₀ hQpos hQ₀).mpr
  exact mul_lt_mul_of_pos_left hQQ hβ

theorem strict_gap_of_coefficient_threshold (n : ℕ) (hn : 2 ≤ n)
    (β Q₀ η₀ : ℝ) (hβ : 0 < β) (hQ₀ : 0 ≤ Q₀)
    (hthreshold : ((n : ℝ) * Real.sqrt (Q₀ / β) - 1) / ((n : ℝ) - 1) < η₀) :
    Q₀ < β * (fixedFactor n η₀) ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have h : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have ht := (div_lt_iff₀ hn1).mp hthreshold
  have hs : Real.sqrt (Q₀ / β) < fixedFactor n η₀ := by
    apply (lt_div_iff₀ hnR).mpr
    nlinarith
  have hs0 := Real.sqrt_nonneg (Q₀ / β)
  have ha : 0 < fixedFactor n η₀ := hs0.trans_lt hs
  have hsq := Real.sq_sqrt (div_nonneg hQ₀ hβ.le)
  have hprod := mul_pos (sub_pos.mpr hs) (add_pos_of_pos_of_nonneg ha hs0)
  have hquot : Q₀ / β < (fixedFactor n η₀) ^ 2 := by nlinarith
  have h := (div_lt_iff₀ hβ).mp hquot
  nlinarith

theorem eventually_strict_baseline {q q₀ d d₀ u u₀ : ℕ → ℝ}
    {Q Q₀ D D₀ μ μ₀ : ℝ}
    (hq : Tendsto q atTop (𝓝 Q)) (hq₀ : Tendsto q₀ atTop (𝓝 Q₀))
    (hd : Tendsto d atTop (𝓝 D)) (hd₀ : Tendsto d₀ atTop (𝓝 D₀))
    (hu : Tendsto u atTop (𝓝 μ)) (hu₀ : Tendsto u₀ atTop (𝓝 μ₀))
    (hQ : Q₀ < Q) (hD : D < D₀) (hμ : μ < μ₀) :
    ∀ᶠ k in atTop, q₀ k < q k ∧ d k < d₀ k ∧ u k < u₀ k := by
  have hqdiff : Tendsto (fun k => q k - q₀ k) atTop (𝓝 (Q - Q₀)) := hq.sub hq₀
  have hddiff : Tendsto (fun k => d₀ k - d k) atTop (𝓝 (D₀ - D)) := hd₀.sub hd
  have hudiff : Tendsto (fun k => u₀ k - u k) atTop (𝓝 (μ₀ - μ)) := hu₀.sub hu
  filter_upwards [(tendsto_order.mp hqdiff).1 0 (sub_pos.mpr hQ),
    (tendsto_order.mp hddiff).1 0 (sub_pos.mpr hD),
    (tendsto_order.mp hudiff).1 0 (sub_pos.mpr hμ)] with k hqk hdk huk
  exact ⟨sub_pos.mp hqk, sub_pos.mp hdk, sub_pos.mp huk⟩

end FCAppendix.Affine

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game
open scoped BigOperators ProbabilityTheory

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem affine_finiteTruncatedPayment_lower (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hn : 0 < n) (hc : 0 < c) (B : PosteriorSystem Γ)
    (hu : UsersOptimal Γ) (hB : BayesReceiptOptimalOnPath Γ B) (j₀ : Fin n)
    (η₀ η : ℝ) (hη₀ : 0 ≤ η₀) (hη : η₀ ≤ η) (hη1 : η ≤ 1)
    (hA : Γ.A = Schedule.affine n η (hη₀.trans hη) hη1)
    (t R ρ ε : ℝ) (ht : 0 ≤ t) (hR : 0 ≤ R) (hε : 0 ≤ ε)
    (hquant : ρ - ε ≤ alphaGt Γ j₀ t) :
    (Affine.fixedFactor n η₀ * t) *
      (finiteLoad Γ - n * Γ.F.real (Set.Ioi (Γ.g + R)) -
        n * (ε + |(c : ℝ) / m - ρ| + 1 / (2 * Real.sqrt m))) ≤
          finiteTruncatedPayment Γ R := by
  apply finiteTruncatedPayment_lower_quantitative Γ hm hc B hu hB j₀
    (Affine.fixedFactor n η₀) t R ρ ε (Affine.fixedFactor_pos n hn η₀ hη₀).le
    ht hR hε _ hquant
  intro r hr hrn
  rw [hA]
  exact Affine.fixedFactor_charge_lower n hn η₀ η hη₀ hη hη1 r hr hrn

end FCAppendix.Bayes
