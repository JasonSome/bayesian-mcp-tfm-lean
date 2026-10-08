import FCAppendix.Finite.PaymentShortfall

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Filter
open scoped BigOperators ProbabilityTheory Topology

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem tendsto_paymentShortfall_of_visible_tail
    (M C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (M k) n (C k) Seed) (j₀ : Fin n)
    (a : ℕ → ℝ) (p ρ : ℝ) (hp : 0 ≤ p) (hρ : 0 ≤ ρ)
    (hM : Tendsto M atTop atTop)
    (ha : Tendsto a atTop (𝓝 1))
    (hcap : Tendsto (fun k => (C k : ℝ) / M k) atTop (𝓝 ρ))
    (hΓ : ∀ k j, ProposerRationalOnPath (Γ k) j)
    (hA : ∀ k r, 0 < r → r ≤ n → a k * (r : ℝ) ≤ (Γ k).A.charge r)
    (htail : ∀ t < p, ∀ ε > 0, ∀ᶠ k in atTop, ρ - ε ≤ alphaGt (Γ k) j₀ t) :
    Tendsto (fun k => (∫ ω, paymentShortfall (Γ k) (a k) p ω ∂backgroundLaw (Γ k)) / M k)
      atTop (𝓝 0) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnon (k : ℕ) : 0 ≤
      (∫ ω, paymentShortfall (Γ k) (a k) p ω ∂backgroundLaw (Γ k)) / M k := by
    apply div_nonneg _ (Nat.cast_nonneg _)
    apply integral_nonneg
    intro ω
    exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => le_max_right _ _))
  have hmc : Tendsto (fun k => (M k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hM
  have hs : Tendsto (fun k => 1 / (2 * Real.sqrt (M k))) atTop (𝓝 (0 : ℝ)) := by
    have hh := (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hmc)).div_const 2
    simpa only [zero_div, one_div, mul_inv_rev, div_eq_mul_inv, Function.comp_def, one_mul, zero_mul] using hh
  apply tendsto_order.mpr
  constructor
  · intro z hz
    exact Filter.Eventually.of_forall (fun k => hz.trans_le (hnon k))
  · intro z hz
    let K := (n : ℝ) * (p + ρ)
    have hK : 0 ≤ K := mul_nonneg hn (add_nonneg hp hρ)
    let δ := z / (2 * (K + 1))
    have hδ : 0 < δ := div_pos hz (by positivity)
    have hδz : δ * K < z := by
      have he : δ * (2 * (K + 1)) = z := div_mul_cancel₀ z (by positivity)
      nlinarith
    let b := p - δ
    let t := p - δ / 2
    have htp : t < p := by dsimp [t]; linarith
    have hbt : b < t := by dsimp [b, t]; linarith
    have hprod : Tendsto (fun k => a k * t) atTop (𝓝 t) := by simpa using ha.mul_const t
    have horder : ∀ᶠ k in atTop, b < a k * t := (tendsto_order.mp hprod).1 b hbt
    have hapos : ∀ᶠ k in atTop, 0 < a k := (tendsto_order.mp ha).1 0 zero_lt_one
    have hposM : ∀ᶠ k in atTop, 0 < M k := hM.eventually_gt_atTop 0
    have hbound : ∀ᶠ k in atTop,
        (∫ ω, paymentShortfall (Γ k) (a k) p ω ∂backgroundLaw (Γ k)) / M k ≤
        p * (n * (δ + |(C k : ℝ) / M k - ρ| + 1 / (2 * Real.sqrt (M k)))) +
        n * max (p - a k * b) 0 * ((C k : ℝ) / M k) := by
      filter_upwards [horder, hapos, hposM, htail t htp δ hδ] with k ho ha' hm ht
      exact integral_paymentShortfall_normalized_le (Γ k) hm (hΓ k) j₀
        (a k) p b t ρ δ ha' hp (hA k) ho hδ.le ht
    have hbase : Tendsto (fun k => δ + |(C k : ℝ) / M k - ρ| +
        1 / (2 * Real.sqrt (M k))) atTop (𝓝 δ) := by
      have hg : Tendsto (fun k => |(C k : ℝ) / M k - ρ|) atTop (𝓝 (0 : ℝ)) := by
        simpa using (hcap.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => ρ) atTop (𝓝 ρ))).abs
      simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => δ) atTop (𝓝 δ)).add hg).add hs
    have hmax : Tendsto (fun k => max (p - a k * b) 0) atTop (𝓝 δ) := by
      have hh := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => p) atTop (𝓝 p)).sub
        (ha.mul_const b)).max (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
      simpa only [one_mul, b, sub_sub_cancel, max_eq_left hδ.le] using hh
    have hright : Tendsto (fun k =>
        p * (n * (δ + |(C k : ℝ) / M k - ρ| + 1 / (2 * Real.sqrt (M k)))) +
        n * max (p - a k * b) 0 * ((C k : ℝ) / M k)) atTop (𝓝 (δ * K)) := by
      convert ((hbase.const_mul (n : ℝ)).const_mul p).add ((hmax.const_mul (n : ℝ)).mul hcap) using 1
      dsimp only [K]
      congr 1
      ring
    filter_upwards [hbound, (tendsto_order.mp hright).2 z hδz] with k hb' hz'
    exact hb'.trans_lt hz'

end FCAppendix.Bayes
