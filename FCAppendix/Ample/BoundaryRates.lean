import FCAppendix.Ample.DeficitTransport
import FCAppendix.Ample.ShortageBounds

noncomputable section
namespace FCAppendix.Ample
open Filter Set Topology

theorem rival_fraction_tendsto_one (M : ℕ → ℕ) (hM : Tendsto M atTop atTop) :
    Tendsto (fun m => ((M m - 1 : ℕ) : ℝ) / M m) atTop (𝓝 1) := by
  have hi : Tendsto (fun m => (M m : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hM)
  have ht : Tendsto (fun m => 1 - (M m : ℝ)⁻¹) atTop (𝓝 1) := by
    simpa only [sub_zero] using hi.const_sub 1
  apply ht.congr'
  filter_upwards [hM.eventually_ge_atTop 1] with m hm
  have hmR : (M m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [Nat.cast_sub hm, Nat.cast_one]
  field_simp

theorem boundary_shortage_fraction_tendsto_zero
    (M C : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (hC : Tendsto (fun m => (C m : ℝ) / M m) atTop (𝓝 1))
    (hscarce : ∀ᶠ m in atTop, C m < M m) :
    Tendsto (fun m => ((M m - 1 - C m : ℕ) : ℝ) / M m) atTop (𝓝 0) := by
  have ht := (rival_fraction_tendsto_one M hM).sub hC
  simp only [sub_self] at ht
  apply ht.congr'
  filter_upwards [hscarce] with m hm
  have hc : C m ≤ M m - 1 := by omega
  rw [Nat.cast_sub hc, sub_div]

theorem boundary_rate_of_finite_bounds
    (M N d : ℕ → ℕ) (k : ℕ) (a p : ℕ → ℝ)
    (hM : Tendsto M atTop atTop)
    (hN : Tendsto (fun m => (N m : ℝ) / M m) atTop (𝓝 1))
    (hd : Tendsto (fun m => (d m : ℝ) / M m) atTop (𝓝 0))
    (ha01 : ∀ m, 0 ≤ a m ∧ a m ≤ 1)
    {a₀ : ℝ} (ha₀ : 0 < a₀) (ha : Tendsto a atTop (𝓝 a₀))
    (hlower : ∀ᶠ m in atTop, a m ^ N m ≤ p m)
    (hupper : ∀ θ : ℝ, 0 ≤ θ → ∀ᶠ m in atTop,
      p m ≤ Real.exp (θ * (k : ℝ) * d m) *
        (a m + (1 - a m) * Real.exp (-θ)) ^ N m) :
    (∀ᶠ m in atTop, 0 < p m) ∧
    Tendsto (fun m => populationLogRate (M m) (p m)) atTop (𝓝 (-Real.log a₀)) := by
  have hap : ∀ᶠ m in atTop, 0 < a m := ha.eventually (eventually_gt_nhds ha₀)
  have hpp : ∀ᶠ m in atTop, 0 < p m := by
    filter_upwards [hap, hlower] with m hm hl
    exact (pow_pos hm _).trans_le hl
  refine ⟨hpp, ?_⟩
  have hlog : Tendsto (fun m => Real.log (a m)) atTop (𝓝 (Real.log a₀)) :=
    (Real.continuousAt_log ha₀.ne').tendsto.comp ha
  have hU : Tendsto (fun m => -((N m : ℝ) / M m) * Real.log (a m))
      atTop (𝓝 (-Real.log a₀)) := by
    simpa only [neg_one_mul] using hN.neg.mul hlog
  have hupperRate : ∀ᶠ m in atTop,
      populationLogRate (M m) (p m) ≤ -((N m : ℝ) / M m) * Real.log (a m) := by
    filter_upwards [hap, hlower, hM.eventually_gt_atTop 0] with m hm hl hmM
    have hh := populationLogRate_anti hmM (pow_pos hm (N m)) hl
    have he : populationLogRate (M m) (a m ^ N m) =
        -((N m : ℝ) / M m) * Real.log (a m) := by
      unfold populationLogRate
      rw [Real.log_pow]
      ring
    rwa [he] at hh
  have ha₀1 : a₀ ≤ 1 := le_of_tendsto ha (Eventually.of_forall fun m => (ha01 m).2)
  let b (θ : ℝ) (m : ℕ) := a m + (1 - a m) * Real.exp (-θ)
  let b₀ (θ : ℝ) := a₀ + (1 - a₀) * Real.exp (-θ)
  have hb₀ (θ : ℝ) : 0 < b₀ θ := by
    exact add_pos_of_pos_of_nonneg ha₀
      (mul_nonneg (sub_nonneg.mpr ha₀1) (Real.exp_pos _).le)
  have hb (θ : ℝ) : Tendsto (b θ) atTop (𝓝 (b₀ θ)) :=
    ha.add ((ha.const_sub 1).mul_const (Real.exp (-θ)))
  have hL (θ : ℝ) : Tendsto
      (fun m => -(θ * (k : ℝ) * ((d m : ℝ) / M m) +
        ((N m : ℝ) / M m) * Real.log (b θ m)))
      atTop (𝓝 (-Real.log (b₀ θ))) := by
    have hh := (hd.const_mul (θ * (k : ℝ))).add
      (hN.mul ((Real.continuousAt_log (hb₀ θ).ne').tendsto.comp (hb θ)))
    simpa only [mul_zero, one_mul, zero_add, Function.comp_def] using hh.neg
  have hlowerRate (θ : ℝ) (hθ : 0 ≤ θ) : ∀ᶠ m in atTop,
      -(θ * (k : ℝ) * ((d m : ℝ) / M m) +
        ((N m : ℝ) / M m) * Real.log (b θ m)) ≤
          populationLogRate (M m) (p m) := by
    filter_upwards [hap, hpp, hupper θ hθ, hM.eventually_gt_atTop 0]
      with m hma hmp hmupper hmM
    have hmb : 0 < b θ m := add_pos_of_pos_of_nonneg hma
      (mul_nonneg (sub_nonneg.mpr (ha01 m).2) (Real.exp_pos _).le)
    have hh := populationLogRate_anti hmM hmp hmupper
    have he : populationLogRate (M m)
        (Real.exp (θ * (k : ℝ) * d m) * b θ m ^ N m) =
        -(θ * (k : ℝ) * ((d m : ℝ) / M m) +
          ((N m : ℝ) / M m) * Real.log (b θ m)) := by
      unfold populationLogRate
      rw [Real.log_mul (Real.exp_ne_zero _) (pow_ne_zero _ hmb.ne'),
        Real.log_exp, Real.log_pow]
      ring
    rwa [he] at hh
  have hθlim : Tendsto (fun θ : ℝ => -Real.log (b₀ θ)) atTop (𝓝 (-Real.log a₀)) := by
    have hbθ : Tendsto b₀ atTop (𝓝 a₀) := by
      simpa only [mul_zero, add_zero] using
        (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (1 - a₀)).const_add a₀
    exact ((Real.continuousAt_log ha₀.ne').tendsto.comp hbθ).neg
  apply tendsto_order.mpr
  constructor
  · intro l hl
    obtain ⟨θ, hθ, hθl⟩ := ((eventually_ge_atTop (0 : ℝ)).and
      ((tendsto_order.mp hθlim).1 l hl)).exists
    filter_upwards [hlowerRate θ hθ, (tendsto_order.mp (hL θ)).1 l hθl] with m hm hlm
    exact hlm.trans_le hm
  · intro u hu
    filter_upwards [hupperRate, (tendsto_order.mp hU).2 u hu] with m hm hmu
    exact hm.trans_lt hmu

theorem boundary_contact_logRate
    {n : ℕ} (μ : ℕ → FiniteLaw (Finset (Fin n)))
    (M C : ℕ → ℕ) (S : Finset (Fin n))
    (hM : Tendsto M atTop atTop)
    (hC : Tendsto (fun m => (C m : ℝ) / M m) atTop (𝓝 1))
    (hscarce : ∀ᶠ m in atTop, C m < M m)
    {a : ℝ} (ha : 0 < a)
    (hlim : Tendsto (fun m => Shortage.allMass (μ m) S) atTop (𝓝 a)) :
    (∀ᶠ m in atTop, 0 < Shortage.congestionProb (μ m) (M m - 1) (C m) S) ∧
    Tendsto (fun m => populationLogRate (M m)
      (Shortage.congestionProb (μ m) (M m - 1) (C m) S))
      atTop (𝓝 (-Real.log a)) := by
  apply boundary_rate_of_finite_bounds M (fun m => M m - 1)
    (fun m => M m - 1 - C m) S.card
    (fun m => Shortage.allMass (μ m) S)
    (fun m => Shortage.congestionProb (μ m) (M m - 1) (C m) S)
    hM (rival_fraction_tendsto_one M hM)
    (boundary_shortage_fraction_tendsto_zero M C hM hC hscarce)
    (fun m => ⟨(μ m).prob_nonneg _, (μ m).prob_le_one _⟩) ha hlim
  · filter_upwards [hscarce] with m hm
    exact (Shortage.finite_sandwich (μ m) (M m - 1) (C m) (by omega) S).1
  · intro θ hθ
    exact Eventually.of_forall fun m => Shortage.chernoff_shortage (μ m)
      (M m - 1) (C m) S hθ

end FCAppendix.Ample
