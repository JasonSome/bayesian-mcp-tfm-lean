import FCAppendix.Affine.FixedBounds

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Filter Topology
open scoped BigOperators ProbabilityTheory

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem eventually_truncatedPayment_lower_of_visible_tail
    (M C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (M k) n (C k) Seed)
    (B : ∀ k, PosteriorSystem (Γ k)) (j₀ : Fin n)
    (hu : ∀ k, UsersOptimal (Γ k))
    (hB : ∀ k, BayesReceiptOptimalOnPath (Γ k) (B k))
    (F : Measure ℝ) [IsProbabilityMeasure F] (hF : ∀ k, (Γ k).F = F)
    (g : ℝ) (hg : ∀ k, (Γ k).g = g)
    (a : ℕ → ℝ) (a₀ t ρ R : ℝ) (ha₀ : 0 < a₀) (ht : 0 < t)
    (hρ : 0 < ρ) (hR : 0 ≤ R)
    (hM : Tendsto M atTop atTop)
    (hcap : Tendsto (fun k => (C k : ℝ) / M k) atTop (𝓝 ρ))
    (ha : Tendsto a atTop (𝓝 a₀))
    (hA : ∀ k r, 0 < r → r ≤ n → a k * (r : ℝ) ≤ (Γ k).A.charge r)
    (htail : ∀ ε > 0, ∀ᶠ k in atTop, ρ - ε ≤ alphaGt (Γ k) j₀ t) :
    ∀ δ > 0, ∀ᶠ k in atTop,
      (a₀ * t) * ((n : ℝ) * ρ - n * F.real (Set.Ioi (g + R))) - δ <
        finiteTruncatedPayment (Γ k) R := by
  have hap : ∀ᶠ k in atTop, 0 < a k := (tendsto_order.mp ha).1 0 ha₀
  have hrat : ∀ k j, ProposerRationalOnPath (Γ k) j :=
    fun k j => ⟨posteriorCountBelief (Γ k) (B k) j, hB k j⟩
  have hL := tendsto_finiteLoad_of_visible_tail M C Γ j₀ a t ρ ht hM hap hcap
    hrat hA htail
  have hmc : Tendsto (fun k => (M k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hM
  have hs : Tendsto (fun k => 1 / (2 * Real.sqrt (M k))) atTop (𝓝 (0 : ℝ)) := by
    have h := (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hmc)).div_const 2
    simpa only [zero_div, one_div, mul_inv_rev, div_eq_mul_inv, Function.comp_def,
      one_mul, zero_mul] using h
  have hgcap : Tendsto (fun k => |(C k : ℝ) / M k - ρ|) atTop (𝓝 (0 : ℝ)) := by
    simpa using (hcap.sub_const ρ).abs
  intro δ hδ
  let ε : ℝ := δ / (2 * (a₀ * t * n + 1))
  have hcoef : 0 ≤ a₀ * t * n := mul_nonneg (mul_nonneg ha₀.le ht.le) (Nat.cast_nonneg n)
  have hden : 0 < 2 * (a₀ * t * n + 1) := by linarith
  have hε : 0 < ε := div_pos hδ hden
  have hεeq : ε * (2 * (a₀ * t * n + 1)) = δ := div_mul_cancel₀ _ hden.ne'
  have hgap : (a₀ * t) * ((n : ℝ) * ρ - n * F.real (Set.Ioi (g + R))) - δ <
      (a₀ * t) * ((n : ℝ) * ρ - n * F.real (Set.Ioi (g + R)) - n * ε) := by
    nlinarith
  have herror : Tendsto (fun k => (n : ℝ) *
      (ε + |(C k : ℝ) / M k - ρ| + 1 / (2 * Real.sqrt (M k))))
      atTop (𝓝 ((n : ℝ) * ε)) := by
    simpa using ((hgcap.const_add ε).add hs).const_mul (n : ℝ)
  have hlim : Tendsto (fun k => (a k * t) *
      (finiteLoad (Γ k) - n * F.real (Set.Ioi (g + R)) -
        n * (ε + |(C k : ℝ) / M k - ρ| + 1 / (2 * Real.sqrt (M k)))))
      atTop (𝓝 ((a₀ * t) * ((n : ℝ) * ρ - n * F.real (Set.Ioi (g + R)) - n * ε))) :=
    (ha.mul_const t).mul ((hL.sub_const _).sub herror)
  filter_upwards [hap, hM.eventually_gt_atTop 0,
    (tendsto_order.mp hcap).1 0 hρ, htail ε hε,
    (tendsto_order.mp hlim).1 _ hgap] with k hak hmk hck htk hlk
  have hmR : (0 : ℝ) < M k := Nat.cast_pos.mpr hmk
  have hcR : (0 : ℝ) < C k := by
    have hh := (lt_div_iff₀ hmR).mp hck
    simpa only [zero_mul] using hh
  have hc : 0 < C k := Nat.cast_pos.mp hcR
  have hh := finiteTruncatedPayment_lower_quantitative (Γ k) hmk hc (B k) (hu k)
    (hB k) j₀ (a k) t R ρ ε hak.le ht.le hR hε.le (hA k) htk
  rw [hF k, hg k] at hh
  exact hlk.trans_le hh

end FCAppendix.Bayes
