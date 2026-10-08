import FCAppendix.Finite.ScarcityBounds
import FCAppendix.Finite.InterimPaymentError

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Filter Set Topology

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem exists_positive_price_subsequence
    (M C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (M k) n (C k) Seed) (j : Fin n)
    (F : Measure ℝ) [IsProbabilityMeasure F] (hF : ∀ k, (Γ k).F = F)
    (g : ℝ) (hg : ∀ k, (Γ k).g = g)
    (a : ℕ → ℝ) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ : ρ < 1)
    (hM : Tendsto M atTop atTop)
    (hcap : Tendsto (fun k => (C k : ℝ) / M k) atTop (𝓝 ρ))
    (ha : Tendsto a atTop (𝓝 1))
    (hΓ : ∀ k, IsAEEquilibrium (Γ k))
    (hp : ∀ k j, ProposerRationalAtFeasibleLists (Γ k) j)
    (hatom : ∀ k, PositiveVisibleAtomless (Γ k))
    (hA : ∀ k r, 0 < r → r ≤ n → a k * (r : ℝ) ≤ (Γ k).A.charge r)
    (hscarce : (n : ℝ) * ρ < F.real (Ioi g)) :
    ∃ p : ℝ, 0 < p ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ q : ℝ, 0 < q → q < ρ →
        Tendsto (fun k => TailQuantile.quantile (alphaGt (Γ (φ k)) j) q) atTop (𝓝 p)) ∧
      (∀ d > 0, Tendsto (fun k => alphaGt (Γ (φ k)) j (p + d)) atTop (𝓝 0)) ∧
      Tendsto (fun k => ∫ v, typePaymentError (Γ (φ k)) (a (φ k)) p v ∂F) atTop (𝓝 0) := by
  obtain ⟨p, hp0, φ, hφ, hquant⟩ := exists_common_visible_quantile_subsequence
    M C Γ j F hF a ρ hρ0 hρ hM hcap ha hΓ hp hatom hA
  have hcap' := hcap.comp hφ.tendsto_atTop
  have hM' := hM.comp hφ.tendsto_atTop
  have ha' := ha.comp hφ.tendsto_atTop
  have hpos := quantile_limit_pos_of_scarcity (M ∘ φ) (C ∘ φ) (fun k => Γ (φ k)) j
    F (fun k => hF (φ k)) g (fun k => hg (φ k)) (a ∘ φ) ρ (ρ / 2) p hρ
    (by positivity) (by linarith) hM' hcap' ha' (fun k => hΓ (φ k))
    (fun k => hp (φ k)) (fun k => hatom (φ k)) (fun k => hA (φ k))
    (hquant (ρ / 2) (by positivity) (by linarith)) hp0 hscarce
  refine ⟨p, hpos, φ, hφ, hquant, ?_, ?_⟩
  · have hC : ∀ᶠ k in atTop, 0 < C (φ k) := by
      filter_upwards [(tendsto_order.mp hcap').1 0 hρ0] with k hk
      by_contra hc
      have hz : C (φ k) = 0 := Nat.eq_zero_of_not_pos hc
      simp [hz] at hk
    exact visible_tail_above_common_quantile_limit (M ∘ φ) (C ∘ φ) (fun k => Γ (φ k))
      j hM' hC (fun k => hΓ (φ k)) ρ p hρ0 hquant
  · have htail := visible_tail_below_common_quantile_limit (M ∘ φ) (C ∘ φ)
      (fun k => Γ (φ k)) j ρ p hpos hquant
    have hh := tendsto_mean_typePaymentError_of_visible_tail (M ∘ φ) (C ∘ φ)
      (fun k => Γ (φ k)) j (a ∘ φ) p ρ hpos.le hρ0.le hM' ha' hcap'
      (fun k => (hΓ (φ k)).proposers) (fun k => hA (φ k)) htail
    simpa only [Function.comp_apply, hF] using hh

end FCAppendix.Bayes
