import FCAppendix.AppendixRepair.GeneralLow.ExactLow
import FCAppendix.Affine.Hybrid.NativeZeroEnvelope

set_option maxHeartbeats 1200000
noncomputable section
namespace FCAppendix.AppendixRepair.GeneralLow.ExactLow
open MeasureTheory ProbabilityTheory Set Game Bayes Affine Affine.LowBody
open Existence.PayOnceBounded (listBids measurable_listBids)
open scoped BigOperators

attribute [local irreducible] Hybrid.NativeEqual.sample
variable {m : ℕ}

theorem template_eq_receivedTemplate (L : LocalList m) (r₀ r₁ : ℕ) :
    template L r₀ r₁ = Hybrid.NativeContinuation.receivedTemplate L r₀ r₁ := rfl

theorem template_eq_clipped_receivedTemplate (L : LocalList m) (r₀ r₁ : ℕ) :
    template L (min (visible L).card r₀) (min (visible L).card r₁) =
      (Hybrid.NativeContinuation.receivedTemplate L r₀ r₁).clipped := rfl

def seedAveragePayoff (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (L : LocalList m) (r₀ r₁ : ℕ) (i : Fin m) (w : ℝ) : ℝ :=
  ∫ s : Fin 2 → unitInterval,
    purePayoff (1 - ξ) w (listBids L)
      (select ξ hξ hξ1 L r₀ r₁ (s 0), select ξ hξ hξ1 L r₁ r₀ (s 1)) i
    ∂Measure.pi (fun _ : Fin 2 => (volume : Measure unitInterval))

theorem seedAveragePayoff_pure (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (L : LocalList m) (r₀ r₁ : ℕ) (i : Fin m) (w : ℝ) (hne : r₀ ≠ r₁) :
    seedAveragePayoff ξ hξ hξ1 L r₀ r₁ i w =
      purePayoff (1 - ξ) w (listBids L) (purePair (1 - ξ) L r₀ r₁) i := by
  simp only [seedAveragePayoff, select_pure_pair ξ hξ hξ1 L r₀ r₁ hne,
    integral_const, probReal_univ, smul_eq_mul, one_mul]

theorem seedAveragePayoff_equal (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (L : LocalList m) (r : ℕ) (i : Fin m) (w : ℝ) :
    seedAveragePayoff ξ hξ hξ1 L r r i w =
      equalPayoff ξ r i w (listBids L) := by
  have hf : Measurable (select ξ hξ hξ1 L r r) :=
    measurable_select ξ hξ hξ1 (fun _ : unitInterval => L) measurable_const
      (fun _ => r) (fun _ => r) measurable_const measurable_const id measurable_id
  unfold seedAveragePayoff
  rw [Hybrid.NativeContinuation.private_pair_expected_payoff ξ w (listBids L) i _ _ hf hf]
  change w * (acceptance ξ hξ hξ1 L r r i + acceptance ξ hξ hξ1 L r r i -
    acceptance ξ hξ hξ1 L r r i * acceptance ξ hξ hξ1 L r r i) -
    listBids L i * (acceptance ξ hξ hξ1 L r r i + acceptance ξ hξ hξ1 L r r i -
      2 * ξ * acceptance ξ hξ hξ1 L r r i * acceptance ξ hξ hξ1 L r r i) = _
  rw [acceptance_equal]
  unfold equalPayoff
  ring

theorem seed_average_payoff_eq_residualPayoff
    (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (L : LocalList m) (r₀ r₁ : ℕ) (i : Fin m) (w : ℝ)
    (hgeneric : ∀ P Q, (template L r₀ r₁).Feasible P →
      (template L r₀ r₁).Feasible Q →
      CompleteInformation.potential (1 - ξ) (listBids L) P.1 P.2 =
        CompleteInformation.potential (1 - ξ) (listBids L) Q.1 Q.2 →
      focalCopy P i = focalCopy Q i) :
    seedAveragePayoff ξ hξ hξ1 L r₀ r₁ i w =
      Hybrid.NativeContinuation.residualPayoff ξ (template L r₀ r₁) i w (listBids L) := by
  by_cases he : r₀ = r₁
  · subst r₁
    rw [seedAveragePayoff_equal]
    simp only [Hybrid.NativeContinuation.residualPayoff, template, if_true]
  · rw [seedAveragePayoff_pure ξ hξ hξ1 L r₀ r₁ i w he]
    have hf := (template_feasible L r₀ r₁ _).mpr
      (purePair_feasible (1 - ξ) L r₀ r₁)
    have hc := (template L r₀ r₁).maximizer_focalCopy_eq_selection
      (1 - ξ) (listBids L) i (purePair (1 - ξ) L r₀ r₁) hf
      (fun Q hQ => purePair_max (1 - ξ) L r₀ r₁ Q hQ) hgeneric
    change _ = if r₀ = r₁ then _ else _
    rw [if_neg he]
    exact purePayoff_eq_of_focalCopy_eq (1 - ξ) w (listBids L) _ _ i hc

theorem template_update (L : LocalList m) (i : Fin m) (hi : L i ≠ none)
    (y : ℝ) (r₀ r₁ : ℕ) :
    template (Function.update L i (some y)) r₀ r₁ = template L r₀ r₁ := by
  have hv : visible (Function.update L i (some y)) = visible L := by
    ext k
    by_cases hk : k = i
    · subst k
      simp [mem_visible, hi]
    · simp [mem_visible, Function.update_of_ne hk]
  simp only [template, hv]

theorem listBids_update (L : LocalList m) (i : Fin m) (y : ℝ) :
    listBids (Function.update L i (some y)) = Function.update (listBids L) i y := by
  funext k
  by_cases hk : k = i
  · subst k
    simp [listBids]
  · simp [listBids, Function.update_of_ne hk]

theorem zero_payoff_le_positive (ξ : ℝ) (hξ : 0 < ξ) (hξh : ξ ≤ 1 / 2)
    (L : LocalList m) (r₀ r₁ : ℕ) (i : Fin m) (hzero : L i = some 0)
    (w : ℝ) (hw : 0 ≤ w) (y : ℝ) (hy : 0 < y) :
    let hξ1 : ξ < 1 := by linarith
    seedAveragePayoff ξ hξ hξ1 L r₀ r₁ i w ≤
      seedAveragePayoff ξ hξ hξ1 (Function.update L i (some y)) r₀ r₁ i w + 2 * y := by
  dsimp only
  have hξ1 : ξ < 1 := by linarith
  let Y := Function.update L i (some y)
  have hb0 : listBids L i = 0 := by simp [listBids, hzero]
  have hby : listBids Y i = y := by simp [Y, listBids]
  by_cases he : r₀ = r₁
  · subst r₁
    rw [seedAveragePayoff_equal, seedAveragePayoff_equal]
    have hp0 : EqualCapacity.positiveMarginal ξ r₀ (listBids L) i = 0 :=
      Hybrid.NativeContinuation.positiveMarginal_zero_of_nonpos ξ r₀ _ i hb0.le
    have hp := EqualCapacity.positiveMarginal_spec ξ r₀ hξ hξ1 (listBids Y)
    have hpos := hp.1 i
    have hone := hp.2.1 i
    have hserv : 0 ≤ 2 * EqualCapacity.positiveMarginal ξ r₀ (listBids Y) i -
        (EqualCapacity.positiveMarginal ξ r₀ (listBids Y) i)^2 := by nlinarith
    have hwserv := mul_nonneg hw hserv
    have hcost := mul_nonneg (mul_nonneg hξ.le hy.le)
      (sq_nonneg (EqualCapacity.positiveMarginal ξ r₀ (listBids Y) i))
    unfold equalPayoff
    rw [hp0, hb0, hby]
    nlinarith
  · rw [seedAveragePayoff_pure ξ hξ hξ1 L r₀ r₁ i w he,
      seedAveragePayoff_pure ξ hξ hξ1 Y r₀ r₁ i w he]
    have ht : template Y r₀ r₁ = template L r₀ r₁ :=
      template_update L i (by simp [hzero]) y r₀ r₁
    have hP := (template_feasible L r₀ r₁ _).mpr
      (purePair_feasible (1 - ξ) L r₀ r₁)
    have hQ : (template L r₀ r₁).Feasible (purePair (1 - ξ) Y r₀ r₁) := by
      rw [← ht]
      exact (template_feasible Y r₀ r₁ _).mpr (purePair_feasible (1 - ξ) Y r₀ r₁)
    have hmQ : ∀ R, (template L r₀ r₁).Feasible R →
        CompleteInformation.potential (1 - ξ) (Function.update (listBids L) i y) R.1 R.2 ≤
          CompleteInformation.potential (1 - ξ) (Function.update (listBids L) i y)
            (purePair (1 - ξ) Y r₀ r₁).1 (purePair (1 - ξ) Y r₀ r₁).2 := by
      intro R hR
      rw [← listBids_update L i y]
      exact purePair_max (1 - ξ) Y r₀ r₁ R (ht.symm ▸ hR)
    have hh := Hybrid.NativeContinuation.zero_pair_payoff_le_new_max
      (template L r₀ r₁) (by linarith : 1 / 2 ≤ 1 - ξ)
      (by linarith : 1 - ξ ≤ 1) hw (listBids L) i hb0
      (purePair (1 - ξ) L r₀ r₁) (purePair (1 - ξ) Y r₀ r₁) hP hQ
      (fun R hR => purePair_max (1 - ξ) L r₀ r₁ R hR) y hy hmQ
    simpa only [← listBids_update L i y] using hh

end FCAppendix.AppendixRepair.GeneralLow.ExactLow
