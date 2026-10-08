import FCAppendix.Finite.QuantileAsymptotics
import FCAppendix.Finite.CapacityFill
import FCAppendix.Finite.FixedReceiptFactor
import FCAppendix.Finite.TruncatedPaymentUpper

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Filter Set Topology

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

structure ReceiptSequenceAssumptions
    (M C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (M k) n (C k) Seed)
    (B : ∀ k, PosteriorSystem (Γ k)) (F : Measure ℝ) (g a ρ : ℝ) : Prop where
  proposers_pos : 0 < n
  common_values : ∀ k, (Γ k).F = F
  common_fee : ∀ k, (Γ k).g = g
  factor_pos : 0 < a
  ratio_pos : 0 < ρ
  ratio_lt_one : ρ < 1
  population_grows : Tendsto M atTop atTop
  capacity_ratio : Tendsto (fun k => (C k : ℝ) / M k) atTop (𝓝 ρ)
  users : ∀ k, UsersOptimal (Γ k)
  bayes_receipts : ∀ k, BayesReceiptOptimalOnPath (Γ k) (B k)
  feasible_continuations : ∀ k j, ProposerRationalAtFeasibleLists (Γ k) j
  visible_atomless : ∀ k, PositiveVisibleAtomless (Γ k)
  receipt_lower : ∀ k r, 0 < r → r ≤ n → a * (r : ℝ) ≤ (Γ k).A.charge r

structure FixedReceiptAssumptions
    (M C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (M k) n (C k) Seed)
    (B : ∀ k, PosteriorSystem (Γ k)) (F : Measure ℝ) (g a ρ : ℝ) : Prop
    extends ReceiptSequenceAssumptions M C Γ B F g a ρ where
  scarcity : (n : ℝ) * ρ < F.real (Ioi g)

namespace ReceiptSequenceAssumptions

variable {M C : ℕ → ℕ} {Γ : ∀ k, FiniteGame (M k) n (C k) Seed}
  {B : ∀ k, PosteriorSystem (Γ k)} {F : Measure ℝ} {g a ρ : ℝ}

theorem equilibria (h : ReceiptSequenceAssumptions M C Γ B F g a ρ) (k : ℕ) :
    IsAEEquilibrium (Γ k) :=
  posterior_isAEEquilibrium_onPath (Γ k) (B k) (h.users k) (h.bayes_receipts k)

theorem eventually_capacity_pos (h : ReceiptSequenceAssumptions M C Γ B F g a ρ) :
    ∀ᶠ k in atTop, 0 < C k := by
  filter_upwards [(tendsto_order.mp h.capacity_ratio).1 0 h.ratio_pos] with k hk
  by_contra hc
  have hz : C k = 0 := Nat.eq_zero_of_not_pos hc
  simp [hz] at hk

theorem along (h : ReceiptSequenceAssumptions M C Γ B F g a ρ)
    (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) :
    ReceiptSequenceAssumptions (M ∘ φ) (C ∘ φ) (fun k => Γ (φ k))
      (fun k => B (φ k)) F g a ρ where
  proposers_pos := h.proposers_pos
  common_values := fun k => h.common_values (φ k)
  common_fee := fun k => h.common_fee (φ k)
  factor_pos := h.factor_pos
  ratio_pos := h.ratio_pos
  ratio_lt_one := h.ratio_lt_one
  population_grows := h.population_grows.comp hφ
  capacity_ratio := h.capacity_ratio.comp hφ
  users := fun k => h.users (φ k)
  bayes_receipts := fun k => h.bayes_receipts (φ k)
  feasible_continuations := fun k => h.feasible_continuations (φ k)
  visible_atomless := fun k => h.visible_atomless (φ k)
  receipt_lower := fun k => h.receipt_lower (φ k)

end ReceiptSequenceAssumptions

namespace FixedReceiptAssumptions

variable {M C : ℕ → ℕ} {Γ : ∀ k, FiniteGame (M k) n (C k) Seed}
  {B : ∀ k, PosteriorSystem (Γ k)} {F : Measure ℝ} {g a ρ : ℝ}

theorem equilibria (h : FixedReceiptAssumptions M C Γ B F g a ρ) (k : ℕ) :
    IsAEEquilibrium (Γ k) := h.toReceiptSequenceAssumptions.equilibria k

theorem eventually_capacity_pos (h : FixedReceiptAssumptions M C Γ B F g a ρ) :
    ∀ᶠ k in atTop, 0 < C k := h.toReceiptSequenceAssumptions.eventually_capacity_pos

theorem along (h : FixedReceiptAssumptions M C Γ B F g a ρ)
    (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) :
    FixedReceiptAssumptions (M ∘ φ) (C ∘ φ) (fun k => Γ (φ k))
      (fun k => B (φ k)) F g a ρ where
  toReceiptSequenceAssumptions := h.toReceiptSequenceAssumptions.along φ hφ
  scarcity := h.scarcity

variable [IsProbabilityMeasure F]

theorem exists_positive_quantile_subsequence
    (h : FixedReceiptAssumptions M C Γ B F g a ρ)
    (j : Fin n) (q : ℝ) (hq : 0 < q) (hqr : q < ρ) :
    ∃ p : ℝ, 0 < p ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => TailQuantile.quantile (alphaGt (Γ (φ k)) j) q) atTop (𝓝 p) := by
  obtain ⟨D, _, hb⟩ := eventually_bounded_visible_quantile M C Γ j F h.common_values
    h.population_grows h.eventually_capacity_pos h.equilibria q hq
  obtain ⟨p, hpD, φ, hφ, hu⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) D)).tendsto_subseq' hb.frequently
  have h' := h.along φ hφ.tendsto_atTop
  have hp := quantile_factor_limit_pos_of_scarcity (M ∘ φ) (C ∘ φ)
    (fun k => Γ (φ k)) j F h'.common_values g h'.common_fee (fun _ => a) a h.factor_pos
    ρ q p h.ratio_lt_one hq hqr h'.population_grows h'.capacity_ratio tendsto_const_nhds
    h'.equilibria h'.feasible_continuations h'.visible_atomless h'.receipt_lower hu hpD.1 h.scarcity
  exact ⟨p, hp, φ, hφ, hu⟩

end FixedReceiptAssumptions

theorem exists_uniform_singleton_error_fixed_factor
    {M C : ℕ → ℕ} {Γ : ∀ k, FiniteGame (M k) n (C k) Seed}
    {B : ∀ k, PosteriorSystem (Γ k)} {F : Measure ℝ} {g a ρ : ℝ}
    (h : ReceiptSequenceAssumptions M C Γ B F g a ρ)
    (j : Fin n) (q p H : ℝ) (hq : 0 < q) (hqr : q < ρ)
    (hu : Tendsto (fun k => TailQuantile.quantile (alphaGt (Γ k) j) q) atTop (𝓝 p)) :
    ∃ e : ℕ → ℝ, (∀ k, 0 ≤ e k) ∧ Tendsto e atTop (𝓝 0) ∧
      ∀ᶠ k in atTop, ∀ (i : Fin (M k)) v, v ≤ H →
        max (v - g - p / a) 0 - e k ≤ (problem (Γ k) i).envelope v := by
  let d : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  let t : ℕ → ℝ := fun k => TailQuantile.quantile (alphaGt (Γ k) j) q / a + d k
  let r : ℕ → ℝ := fun k => (M k - 1 : ℕ) / (4 * ((M k : ℝ) * (ρ - q) / 2) ^ 2)
  let e : ℕ → ℝ := fun k => |t k - p / a| + r k * max (H - g) 0
  have hr : ∀ k, 0 ≤ r k := fun k => by dsimp [r]; positivity
  have hd : ∀ k, 0 < d k := fun k => by dsimp [d]; positivity
  have hd0 : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have ht0 : Tendsto t atTop (𝓝 (p / a)) := by simpa [t] using (hu.div_const a).add hd0
  have hr0 : Tendsto r atTop (𝓝 0) :=
    singleton_failure_tendsto_zero M h.population_grows (ρ - q) (sub_pos.mpr hqr)
  have he0 : Tendsto e atTop (𝓝 0) := by
    simpa [e] using ((ht0.sub_const (p / a)).abs).add (hr0.mul_const (max (H - g) 0))
  refine ⟨e, fun k => add_nonneg (abs_nonneg _) (mul_nonneg (hr k) (le_max_right _ _)), he0, ?_⟩
  have hgood := eventually_singleton_success_varying_increment_of_positive M C Γ j
    (fun _ => a) d ρ q h.ratio_lt_one hq hqr (Eventually.of_forall hd)
    h.population_grows h.capacity_ratio (Eventually.of_forall fun _ => h.factor_pos)
    h.equilibria h.feasible_continuations h.visible_atomless h.receipt_lower
  filter_upwards [hgood] with k hk
  intro i v hv
  let act : JointAction n := ⟨t k, hk.1.le, 1, h.proposers_pos⟩
  have hlo := envelope_lower_at_price (Γ k) h.proposers_pos i act rfl
    (r k) (p / a) (hr k) (hk.2 i) v
  rw [h.common_fee k] at hlo
  have herr := mul_le_mul_of_nonneg_left
    (max_le_max (sub_le_sub_right hv g) (show (0 : ℝ) ≤ 0 from le_rfl)) (hr k)
  dsimp only [e, act] at *
  linarith

noncomputable def marketShortageError (M C : ℕ → ℕ) (ρ : ℝ) (k : ℕ) : ℝ :=
  |(C k : ℝ) / M k - ρ| + 1 / (2 * Real.sqrt (M k))

theorem marketShortageError_nonneg (M C : ℕ → ℕ) (ρ : ℝ) (k : ℕ) :
    0 ≤ marketShortageError M C ρ k := by
  unfold marketShortageError
  positivity

theorem marketShortageError_tendsto_zero (M C : ℕ → ℕ) (ρ : ℝ)
    (hM : Tendsto M atTop atTop)
    (hcap : Tendsto (fun k => (C k : ℝ) / M k) atTop (𝓝 ρ)) :
    Tendsto (marketShortageError M C ρ) atTop (𝓝 0) := by
  have hmc : Tendsto (fun k => (M k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hM
  have hs : Tendsto (fun k => 1 / (2 * Real.sqrt (M k))) atTop (𝓝 (0 : ℝ)) := by
    have hh := (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hmc)).div_const 2
    simpa only [zero_div, one_div, mul_inv_rev, div_eq_mul_inv, Function.comp_def,
      one_mul, zero_mul] using hh
  have hg : Tendsto (fun k => |(C k : ℝ) / M k - ρ|) atTop (𝓝 (0 : ℝ)) := by
    simpa using (hcap.sub_const ρ).abs
  change Tendsto (fun k => |(C k : ℝ) / M k - ρ| + 1 / (2 * Real.sqrt (M k))) atTop (𝓝 0)
  simpa only [add_zero] using hg.add hs

theorem eventually_visible_tail_of_one_quantile
    (M C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (M k) n (C k) Seed)
    (j : Fin n) (q p t : ℝ) (ht0 : 0 ≤ t) (ht : t < p)
    (hu : Tendsto (fun k => TailQuantile.quantile (alphaGt (Γ k) j) q) atTop (𝓝 p)) :
    ∀ᶠ k in atTop, q ≤ alphaGt (Γ k) j t := by
  filter_upwards [(tendsto_order.mp hu).1 t ht] with k hk
  exact (TailQuantile.lt_tail_below ht0 hk).le

end FCAppendix.Bayes
