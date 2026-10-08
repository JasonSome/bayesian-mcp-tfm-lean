import FCAppendix.Finite.ScarcityBounds

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Filter Set Topology

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem envelope_lower_at_price (Γ : FiniteGame m n c Seed) (hn : 0 < n)
    (i : Fin m) (act : JointAction n) (hk : act.routeCount = 1)
    (r p : ℝ) (hr : 0 ≤ r) (hq : 1 - r ≤ meanAcceptProb Γ i act.bid) (v : ℝ) :
    max (v - Γ.g - p) 0 - (|act.bid - p| + r * max (v - Γ.g) 0) ≤
      (problem Γ i).envelope v := by
  have hh := envelope_lower_singleton Γ hn i act hk r hr hq v
  have hmax : max (v - Γ.g - p) 0 ≤ max (v - Γ.g - act.bid) 0 + |act.bid - p| := by
    apply max_le
    · linarith [le_max_left (v - Γ.g - act.bid) 0, le_abs_self (act.bid - p)]
    · exact add_nonneg (le_max_right _ _) (abs_nonneg _)
  linarith

theorem eventually_singleton_success_varying_increment
    (M C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (M k) n (C k) Seed) (j : Fin n)
    (a d : ℕ → ℝ) (ρ q : ℝ) (hρ : ρ < 1) (hq : 0 < q) (hqr : q < ρ)
    (hd : ∀ᶠ k in atTop, 0 < d k)
    (hM : Tendsto M atTop atTop)
    (hcap : Tendsto (fun k => (C k : ℝ) / M k) atTop (𝓝 ρ))
    (ha : Tendsto a atTop (𝓝 1))
    (hΓ : ∀ k, IsAEEquilibrium (Γ k))
    (hp : ∀ k j, ProposerRationalAtFeasibleLists (Γ k) j)
    (hatom : ∀ k, PositiveVisibleAtomless (Γ k))
    (hA : ∀ k r, 0 < r → r ≤ n → a k * (r : ℝ) ≤ (Γ k).A.charge r) :
    ∀ᶠ k in atTop, 0 < TailQuantile.quantile (alphaGt (Γ k) j) q / a k + d k ∧
      ∀ i, 1 - (M k - 1 : ℕ) / (4 * ((M k : ℝ) * (ρ - q) / 2) ^ 2) ≤
        meanAcceptProb (Γ k) i (TailQuantile.quantile (alphaGt (Γ k) j) q / a k + d k) := by
  filter_upwards [hd, (tendsto_order.mp ha).1 0 zero_lt_one,
    (tendsto_order.mp hcap).2 1 hρ,
    (tendsto_order.mp hcap).1 ((ρ + q) / 2) (by linarith),
    hM.eventually_gt_atTop 0] with k hd ha hc hc' hm
  have hmR : (0 : ℝ) < M k := Nat.cast_pos.mpr hm
  have hcR : (0 : ℝ) < C k := by
    have hh := (lt_div_iff₀ hmR).mp hc'
    have hmid : 0 < (ρ + q) / 2 := by linarith
    exact lt_of_lt_of_le (mul_pos hmid hmR) hh.le
  have hc0 : 0 < C k := Nat.cast_pos.mp hcR
  have hcM : C k ≤ M k := by
    have hh := (div_lt_iff₀ hmR).mp hc
    exact Nat.cast_le.mp (by linarith : (C k : ℝ) ≤ M k)
  have hδ : 0 < (M k : ℝ) * (ρ - q) / 2 := by positivity
  have hgap : (M k : ℝ) * (ρ - q) / 2 ≤ (C k : ℝ) - (M k - 1 : ℕ) * q := by
    have hh := (lt_div_iff₀ hmR).mp hc'
    have hn : ((M k - 1 : ℕ) : ℝ) ≤ M k := Nat.cast_le.mpr (Nat.sub_le _ _)
    nlinarith [mul_le_mul_of_nonneg_right hn hq.le]
  exact singleton_success_of_quantile_gap (Γ k) hm hc0 hcM (hΓ k) (hp k) (hatom k)
    j (a k) ha (hA k) q (d k) ((M k : ℝ) * (ρ - q) / 2) hq hd hδ hgap

theorem exists_vanishing_singleton_error
    (M C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (M k) n (C k) Seed) (j : Fin n)
    (g : ℝ) (hg : ∀ k, (Γ k).g = g)
    (a : ℕ → ℝ) (ρ q p : ℝ) (hρ : ρ < 1) (hq : 0 < q) (hqr : q < ρ)
    (hM : Tendsto M atTop atTop)
    (hcap : Tendsto (fun k => (C k : ℝ) / M k) atTop (𝓝 ρ))
    (ha : Tendsto a atTop (𝓝 1))
    (hΓ : ∀ k, IsAEEquilibrium (Γ k))
    (hp : ∀ k j, ProposerRationalAtFeasibleLists (Γ k) j)
    (hatom : ∀ k, PositiveVisibleAtomless (Γ k))
    (hA : ∀ k r, 0 < r → r ≤ n → a k * (r : ℝ) ≤ (Γ k).A.charge r)
    (hu : Tendsto (fun k => TailQuantile.quantile (alphaGt (Γ k) j) q) atTop (𝓝 p)) :
    ∃ δ : ℕ → ℝ → ℝ, (∀ k v, 0 ≤ δ k v) ∧ (∀ k, Measurable (δ k)) ∧
      (∀ v, Tendsto (fun k => δ k v) atTop (𝓝 0)) ∧
      ∀ k (i : Fin (M k)) v, max (v - g - p) 0 - δ k v ≤ (problem (Γ k) i).envelope v := by
  classical
  let d : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hd : ∀ k, 0 < d k := fun k => by dsimp [d]; positivity
  have hd0 : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let t := fun k => TailQuantile.quantile (alphaGt (Γ k) j) q / a k + d k
  let r := fun k => (M k - 1 : ℕ) / (4 * ((M k : ℝ) * (ρ - q) / 2) ^ 2)
  have hr : ∀ k, 0 ≤ r k := fun k => by dsimp [r]; positivity
  have hr0 := singleton_failure_tendsto_zero M hM (ρ - q) (sub_pos.mpr hqr)
  have ht0 : Tendsto t atTop (𝓝 p) := by simpa [t] using (hu.div ha one_ne_zero).add hd0
  let good := fun k => 0 < t k ∧ ∀ i, 1 - r k ≤ meanAcceptProb (Γ k) i (t k)
  have hgood : ∀ᶠ k in atTop, good k := eventually_singleton_success_varying_increment
    M C Γ j a d ρ q hρ hq hqr (Eventually.of_forall hd) hM hcap ha hΓ hp hatom hA
  let δ := fun k v => if good k then |t k - p| + r k * max (v - g) 0
    else max (v - g - p) 0
  refine ⟨δ, ?_, ?_, ?_, ?_⟩
  · intro k v
    dsimp [δ]
    split
    · exact add_nonneg (abs_nonneg _) (mul_nonneg (hr k) (le_max_right _ _))
    · exact le_max_right _ _
  · intro k
    dsimp [δ]
    split
    · fun_prop
    · fun_prop
  · intro v
    have hh : Tendsto (fun k => |t k - p| + r k * max (v - g) 0) atTop (𝓝 0) := by
      simpa using ((ht0.sub_const p).abs).add (hr0.mul_const (max (v - g) 0))
    apply hh.congr'
    filter_upwards [hgood] with k hk
    simp only [δ, if_pos hk]
  · intro k i v
    by_cases hk : good k
    · let act : JointAction n := ⟨t k, hk.1.le, 1, Nat.zero_lt_of_lt j.isLt⟩
      have hh := envelope_lower_at_price (Γ k) (Nat.zero_lt_of_lt j.isLt) i act rfl
        (r k) p (hr k) (hk.2 i) v
      simpa only [δ, if_pos hk, act, hg k] using hh
    · simp only [δ, if_neg hk, sub_self]
      exact (problem (Γ k) i).envelope_nonneg v

end FCAppendix.Bayes
