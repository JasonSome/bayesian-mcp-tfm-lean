import FCAppendix.Finite.QuantileComparison

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Filter Set Topology

theorem deviation_threshold_lower (m : ℕ) (hm : 2 ≤ m) (d e : ℝ)
    (hd : 0 < d) (he : 0 < e) :
    d * (m : ℝ) * e ^ 2 ≤ d / ((m - 1 : ℕ) / (4 * ((m : ℝ) * e / 2) ^ 2)) := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hN : (0 : ℝ) < (m - 1 : ℕ) := Nat.cast_pos.mpr (by omega)
  have hNM : ((m - 1 : ℕ) : ℝ) ≤ m := Nat.cast_le.mpr (Nat.sub_le _ _)
  have hh := div_le_div_of_nonneg_left
    (show 0 ≤ d * (4 * ((m : ℝ) * e / 2) ^ 2) by positivity) hN hNM
  calc
    _ = d * (4 * ((m : ℝ) * e / 2) ^ 2) / m := by
      field_simp
      ring
    _ ≤ d * (4 * ((m : ℝ) * e / 2) ^ 2) / (m - 1 : ℕ) := hh
    _ = _ := by rw [div_div_eq_mul_div]

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem eventually_quantile_comparison
    (M C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (M k) n (C k) Seed) (j : Fin n)
    (F : Measure ℝ) [IsProbabilityMeasure F] (hF : ∀ k, (Γ k).F = F)
    (a : ℕ → ℝ) (ρ : ℝ) (hρ : ρ < 1)
    (hM : Tendsto M atTop atTop)
    (hcap : Tendsto (fun k => (C k : ℝ) / M k) atTop (𝓝 ρ))
    (ha : ∀ᶠ k in atTop, 0 < a k)
    (hΓ : ∀ k, IsAEEquilibrium (Γ k))
    (hp : ∀ k j, ProposerRationalAtFeasibleLists (Γ k) j)
    (hatom : ∀ k, PositiveVisibleAtomless (Γ k))
    (hA : ∀ k r, 0 < r → r ≤ n → a k * (r : ℝ) ≤ (Γ k).A.charge r)
    (q q' d : ℝ) (hq : 0 < q) (hqr : q < ρ) (hq' : 0 < q') (hd : 0 < d) :
    ∀ᶠ k in atTop, TailQuantile.quantile (alphaGt (Γ k) j) q' ≤
      TailQuantile.quantile (alphaGt (Γ k) j) q / a k + 2 * d := by
  have he : 0 < ρ - q := sub_pos.mpr hqr
  have htF := (TailQuantile.tail_tendsto_zero F).eventually (gt_mem_nhds hq')
  obtain ⟨T, hT⟩ := eventually_atTop.mp htF
  have hmc : Tendsto (fun k => (M k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hM
  have hgrow : Tendsto (fun k => d * (M k : ℝ) * (ρ - q) ^ 2) atTop atTop :=
    (by
      have hh := hmc.const_mul_atTop (mul_pos hd (sq_pos_of_pos he))
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hh)
  have hlarge := hgrow.eventually_ge_atTop T
  have hbelow := (tendsto_order.mp hcap).2 1 hρ
  have habove := (tendsto_order.mp hcap).1 ((ρ + q) / 2) (by linarith)
  filter_upwards [ha, hlarge, hbelow, habove, hM.eventually_ge_atTop 2] with k ha hk hc hc' hm
  have hm0 : 0 < M k := by omega
  have hmR : (0 : ℝ) < M k := Nat.cast_pos.mpr hm0
  have hcR : (0 : ℝ) < C k := by
    have hh := (lt_div_iff₀ hmR).mp hc'
    have hmid : 0 < (ρ + q) / 2 := by linarith
    exact lt_of_lt_of_le (mul_pos hmid hmR) hh.le
  have hc0 : 0 < C k := Nat.cast_pos.mp hcR
  have hcM : C k ≤ M k := by
    have hh := (div_lt_iff₀ hmR).mp hc
    exact Nat.cast_le.mp (by linarith : (C k : ℝ) ≤ M k)
  let δ := (M k : ℝ) * (ρ - q) / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hgap : δ ≤ (C k : ℝ) - (M k - 1 : ℕ) * q := by
    have hh := (lt_div_iff₀ hmR).mp hc'
    have hn : ((M k - 1 : ℕ) : ℝ) ≤ M k := Nat.cast_le.mpr (Nat.sub_le _ _)
    dsimp [δ]
    nlinarith [mul_le_mul_of_nonneg_right hn hq.le]
  have hthreshold : T ≤ d / ((M k - 1 : ℕ) / (4 * δ ^ 2)) :=
    hk.trans (deviation_threshold_lower (M k) hm d (ρ - q) hd he)
  have htail : (Γ k).F.real (Ioi ((Γ k).g + d / ((M k - 1 : ℕ) / (4 * δ ^ 2)))) ≤ q' := by
    rw [hF k]
    apply le_trans (measureReal_mono (show Ioi ((Γ k).g + d / ((M k - 1 : ℕ) / (4 * δ ^ 2))) ⊆
      Ioi T from fun x hx => by have hg := (Γ k).g_nonneg; simp only [mem_Ioi] at *; linarith))
    exact (hT T le_rfl).le
  exact quantile_comparison_of_gap (Γ k) hm hc0 hcM (hΓ k) (hp k) (hatom k)
    ⟨0, hm0⟩ j (a k) ha (hA k) q q' d δ hq hd hδ hgap htail

end FCAppendix.Bayes

namespace FCAppendix.TailQuantile

open Filter Topology

theorem eventually_sub_lt_of_comparison
    (u v a : ℕ → ℝ) (B : ℝ)
    (hu : ∀ᶠ k in atTop, 0 ≤ u k ∧ u k ≤ B)
    (ha : Tendsto a atTop (𝓝 1))
    (hcompare : ∀ d > 0, ∀ᶠ k in atTop, v k ≤ u k / a k + 2 * d)
    (z : ℝ) (hz : 0 < z) : ∀ᶠ k in atTop, v k - u k < z := by
  have he : Tendsto (fun k => B * |(a k)⁻¹ - 1|) atTop (𝓝 (0 : ℝ)) := by
    simpa using (((ha.inv₀ one_ne_zero).sub_const 1).abs.const_mul B)
  have hesmall := (tendsto_order.mp he).2 (z / 2) (by linarith)
  filter_upwards [hu, hesmall, hcompare (z / 8) (by linarith)] with k hu he hc
  have hprod : u k * ((a k)⁻¹ - 1) ≤ B * |(a k)⁻¹ - 1| :=
    (mul_le_mul_of_nonneg_left (le_abs_self _) hu.1).trans
      (mul_le_mul_of_nonneg_right hu.2 (abs_nonneg _))
  rw [div_eq_mul_inv] at hc
  nlinarith

theorem tendsto_sub_zero_of_comparisons
    (u v a : ℕ → ℝ) (B D : ℝ)
    (hu : ∀ᶠ k in atTop, 0 ≤ u k ∧ u k ≤ B)
    (hv : ∀ᶠ k in atTop, 0 ≤ v k ∧ v k ≤ D)
    (ha : Tendsto a atTop (𝓝 1))
    (huv : ∀ d > 0, ∀ᶠ k in atTop, v k ≤ u k / a k + 2 * d)
    (hvu : ∀ d > 0, ∀ᶠ k in atTop, u k ≤ v k / a k + 2 * d) :
    Tendsto (fun k => u k - v k) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro z hz
    have hh := eventually_sub_lt_of_comparison u v a B hu ha huv (-z) (by linarith)
    exact hh.mono fun k hk => by linarith
  · intro z hz
    exact eventually_sub_lt_of_comparison v u a D hv ha hvu z hz

end FCAppendix.TailQuantile

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Filter Set Topology

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem eventually_bounded_visible_quantile
    (M C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (M k) n (C k) Seed) (j : Fin n)
    (F : Measure ℝ) [IsProbabilityMeasure F] (hF : ∀ k, (Γ k).F = F)
    (hM : Tendsto M atTop atTop) (hC : ∀ᶠ k in atTop, 0 < C k)
    (hΓ : ∀ k, IsAEEquilibrium (Γ k)) (q : ℝ) (hq : 0 < q) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in atTop,
      0 ≤ TailQuantile.quantile (alphaGt (Γ k) j) q ∧
      TailQuantile.quantile (alphaGt (Γ k) j) q ≤ B := by
  obtain ⟨B, hB, hFB⟩ := ((eventually_ge_atTop (0 : ℝ)).and
    ((TailQuantile.tail_tendsto_zero F).eventually (gt_mem_nhds hq))).exists
  refine ⟨B, hB, ?_⟩
  filter_upwards [hC, hM.eventually_gt_atTop 0] with k hc hm
  refine ⟨visible_quantile_nonneg (Γ k) hm hc (hΓ k) j q hq, ?_⟩
  apply TailQuantile.le_of_tail_le hB
  have hh := alphaGt_le_value_tail_onPath (Γ k) hm hc (hΓ k) j B hB
  rw [hF k] at hh
  have hmono : F.real (Ioi ((Γ k).g + B)) ≤ F.real (Ioi B) :=
    measureReal_mono (fun x hx => by have hg := (Γ k).g_nonneg; simp only [mem_Ioi] at *; linarith)
  exact hh.trans (hmono.trans hFB.le)

theorem tendsto_visible_quantile_sub_zero
    (M C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (M k) n (C k) Seed) (j : Fin n)
    (F : Measure ℝ) [IsProbabilityMeasure F] (hF : ∀ k, (Γ k).F = F)
    (a : ℕ → ℝ) (ρ : ℝ) (hρ : ρ < 1)
    (hM : Tendsto M atTop atTop)
    (hcap : Tendsto (fun k => (C k : ℝ) / M k) atTop (𝓝 ρ))
    (ha : Tendsto a atTop (𝓝 1))
    (hΓ : ∀ k, IsAEEquilibrium (Γ k))
    (hp : ∀ k j, ProposerRationalAtFeasibleLists (Γ k) j)
    (hatom : ∀ k, PositiveVisibleAtomless (Γ k))
    (hA : ∀ k r, 0 < r → r ≤ n → a k * (r : ℝ) ≤ (Γ k).A.charge r)
    (q q' : ℝ) (hq : 0 < q) (hqr : q < ρ) (hq' : 0 < q') (hq'r : q' < ρ) :
    Tendsto (fun k => TailQuantile.quantile (alphaGt (Γ k) j) q -
      TailQuantile.quantile (alphaGt (Γ k) j) q') atTop (𝓝 0) := by
  have hρ0 : 0 < ρ := hq.trans hqr
  have hC : ∀ᶠ k in atTop, 0 < C k := by
    filter_upwards [(tendsto_order.mp hcap).1 0 hρ0] with k hk
    by_contra hc
    have hz : C k = 0 := Nat.eq_zero_of_not_pos hc
    simp [hz] at hk
  obtain ⟨B, _, hu⟩ := eventually_bounded_visible_quantile M C Γ j F hF hM hC hΓ q hq
  obtain ⟨D, _, hv⟩ := eventually_bounded_visible_quantile M C Γ j F hF hM hC hΓ q' hq'
  have ha0 := (tendsto_order.mp ha).1 0 zero_lt_one
  apply TailQuantile.tendsto_sub_zero_of_comparisons _ _ a B D hu hv ha
  · exact fun d hd => eventually_quantile_comparison M C Γ j F hF a ρ hρ hM hcap
      ha0 hΓ hp hatom hA q q' d hq hqr hq' hd
  · exact fun d hd => eventually_quantile_comparison M C Γ j F hF a ρ hρ hM hcap
      ha0 hΓ hp hatom hA q' q d hq' hq'r hq hd

theorem exists_common_visible_quantile_subsequence
    (M C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (M k) n (C k) Seed) (j : Fin n)
    (F : Measure ℝ) [IsProbabilityMeasure F] (hF : ∀ k, (Γ k).F = F)
    (a : ℕ → ℝ) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ : ρ < 1)
    (hM : Tendsto M atTop atTop)
    (hcap : Tendsto (fun k => (C k : ℝ) / M k) atTop (𝓝 ρ))
    (ha : Tendsto a atTop (𝓝 1))
    (hΓ : ∀ k, IsAEEquilibrium (Γ k))
    (hp : ∀ k j, ProposerRationalAtFeasibleLists (Γ k) j)
    (hatom : ∀ k, PositiveVisibleAtomless (Γ k))
    (hA : ∀ k r, 0 < r → r ≤ n → a k * (r : ℝ) ≤ (Γ k).A.charge r) :
    ∃ p : ℝ, 0 ≤ p ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ q : ℝ, 0 < q → q < ρ →
        Tendsto (fun k => TailQuantile.quantile (alphaGt (Γ (φ k)) j) q) atTop (𝓝 p) := by
  have hC : ∀ᶠ k in atTop, 0 < C k := by
    filter_upwards [(tendsto_order.mp hcap).1 0 hρ0] with k hk
    by_contra hc
    have hz : C k = 0 := Nat.eq_zero_of_not_pos hc
    simp [hz] at hk
  obtain ⟨B, _, hu⟩ := eventually_bounded_visible_quantile M C Γ j F hF hM hC hΓ
    (ρ / 2) (by positivity)
  obtain ⟨p, hpB, φ, hφ, hconv⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) B)).tendsto_subseq' hu.frequently
  refine ⟨p, hpB.1, φ, hφ, ?_⟩
  intro q hq hqr
  have hd := (tendsto_visible_quantile_sub_zero M C Γ j F hF a ρ hρ hM hcap ha
    hΓ hp hatom hA q (ρ / 2) hq hqr (by positivity) (by linarith)).comp hφ.tendsto_atTop
  have hh := hd.add hconv
  simpa only [Function.comp_def, sub_add_cancel, zero_add] using hh

theorem visible_tail_below_common_quantile_limit
    (M C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (M k) n (C k) Seed) (j : Fin n)
    (ρ p : ℝ) (hp : 0 < p)
    (hquant : ∀ q : ℝ, 0 < q → q < ρ →
      Tendsto (fun k => TailQuantile.quantile (alphaGt (Γ k) j) q) atTop (𝓝 p)) :
    ∀ t < p, ∀ ε > 0, ∀ᶠ k in atTop, ρ - ε ≤ alphaGt (Γ k) j t := by
  intro t ht ε hε
  by_cases he : ρ ≤ ε
  · exact Filter.Eventually.of_forall (fun k =>
      (sub_nonpos.mpr he).trans (measureReal_nonneg (μ := userLaw (Γ k))))
  · have hq : 0 < ρ - ε := sub_pos.mpr (lt_of_not_ge he)
    have hqr : ρ - ε < ρ := by linarith
    have htp : max t 0 < p := max_lt ht hp
    have hu := (tendsto_order.mp (hquant (ρ - ε) hq hqr)).1 (max t 0) htp
    filter_upwards [hu] with k hk
    have hh := TailQuantile.lt_tail_below (le_max_right t 0) hk
    exact hh.le.trans (alphaGt_antitone (Γ k) j (le_max_left t 0))

theorem visible_tail_above_common_quantile_limit
    (M C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (M k) n (C k) Seed) (j : Fin n)
    (hM : Tendsto M atTop atTop) (hC : ∀ᶠ k in atTop, 0 < C k)
    (hΓ : ∀ k, IsAEEquilibrium (Γ k)) (ρ p : ℝ) (hρ : 0 < ρ)
    (hquant : ∀ q : ℝ, 0 < q → q < ρ →
      Tendsto (fun k => TailQuantile.quantile (alphaGt (Γ k) j) q) atTop (𝓝 p))
    (d : ℝ) (hd : 0 < d) :
    Tendsto (fun k => alphaGt (Γ k) j (p + d)) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro z hz
    exact Filter.Eventually.of_forall (fun _ => hz.trans_le measureReal_nonneg)
  · intro z hz
    let q := min ρ z / 2
    have hq : 0 < q := by dsimp [q]; positivity
    have hqr : q < ρ := by have hh := min_le_left ρ z; dsimp [q]; linarith
    have hqz : q < z := by have hh := min_le_right ρ z; dsimp [q]; linarith
    have hu := (tendsto_order.mp (hquant q hq hqr)).2 (p + d / 2) (by linarith)
    filter_upwards [hu, hC, hM.eventually_gt_atTop 0] with k hk hc hm
    have hh := alphaGt_above_quantile (Γ k) hm hc (hΓ k) j q (d / 2) hq (by linarith)
    have hb : TailQuantile.quantile (alphaGt (Γ k) j) q + d / 2 ≤ p + d := by linarith
    exact ((alphaGt_antitone (Γ k) j hb).trans hh).trans_lt hqz

end FCAppendix.Bayes
