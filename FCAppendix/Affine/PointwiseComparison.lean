import FCAppendix.Finite.NearPPITheorem

namespace FCAppendix
open Filter Topology

theorem tendsto_row_limits_of_constrained_diagonals
    (f : ℕ → ℕ → ℝ) (L : ℕ → ℝ) (a : ℝ) (P : ℕ → ℕ → Prop)
    (hP : ∀ k, ∀ᶠ m in atTop, P k m)
    (hrow : ∀ k, Tendsto (f k) atTop (𝓝 (L k)))
    (hdiag : ∀ φ : ℕ → ℕ, Tendsto φ atTop atTop → (∀ k, P k (φ k)) →
      Tendsto (fun k => f k (φ k)) atTop (𝓝 a)) : Tendsto L atTop (𝓝 a) := by
  classical
  let e : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have he : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hchoice (k : ℕ) : ∃ r : ℕ, k ≤ r ∧ P k r ∧ dist (f k r) (L k) < e k := by
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      ((hP k).and (Metric.tendsto_nhds.mp (hrow k) (e k) (by dsimp [e]; positivity)))
    exact ⟨max k N, le_max_left _ _, hN _ (le_max_right _ _)⟩
  choose φ hφ hpres hclose using hchoice
  have hcofinal : Tendsto φ atTop atTop := by
    apply tendsto_atTop.mpr
    intro N
    filter_upwards [eventually_ge_atTop N] with k hk
    exact hk.trans (hφ k)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [(tendsto_order.mp he).2 (ε / 2) (half_pos hε),
    Metric.tendsto_nhds.mp (hdiag φ hcofinal hpres) (ε / 2) (half_pos hε)] with k hk hdk
  have hclose' : dist (L k) (f k (φ k)) < ε / 2 := by
    rw [dist_comm]
    exact (hclose k).trans hk
  exact (dist_triangle (L k) (f k (φ k)) a).trans_lt (by linarith)

theorem tendsto_row_limits_of_market_diagonals
    (M C : ℕ → ℕ → ℕ) (ρ : ℝ)
    (hMrow : ∀ r, Tendsto (M r) atTop atTop)
    (hCrow : ∀ r, Tendsto (fun m => (C r m : ℝ) / M r m) atTop (𝓝 ρ))
    (f : ℕ → ℕ → ℝ) (L : ℕ → ℝ) (a : ℝ)
    (hrow : ∀ r, Tendsto (f r) atTop (𝓝 (L r)))
    (hdiag : ∀ φ : ℕ → ℕ,
      Tendsto (fun k => M k (φ k)) atTop atTop →
      Tendsto (fun k => (C k (φ k) : ℝ) / M k (φ k)) atTop (𝓝 ρ) →
      Tendsto (fun k => f k (φ k)) atTop (𝓝 a)) : Tendsto L atTop (𝓝 a) := by
  let e : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have he : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let P : ℕ → ℕ → Prop := fun r m => r ≤ M r m ∧ |(C r m : ℝ) / M r m - ρ| < e r
  have hP (r : ℕ) : ∀ᶠ m in atTop, P r m := by
    filter_upwards [(hMrow r).eventually_ge_atTop r,
      Metric.tendsto_nhds.mp (hCrow r) (e r) (by dsimp [e]; positivity)] with m hmr hcr
    exact ⟨hmr, by simpa only [Real.dist_eq] using hcr⟩
  apply tendsto_row_limits_of_constrained_diagonals f L a P hP hrow
  intro φ _ hpres
  have hM : Tendsto (fun k => M k (φ k)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro N
    filter_upwards [eventually_ge_atTop N] with k hk
    exact hk.trans (hpres k).1
  have hC : Tendsto (fun k => (C k (φ k) : ℝ) / M k (φ k)) atTop (𝓝 ρ) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [(tendsto_order.mp he).2 ε hε] with k hk
    simpa only [Real.dist_eq] using (hpres k).2.trans hk
  exact hdiag φ hM hC

end FCAppendix

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Filter Set Topology

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
  {M C : ℕ → ℕ → ℕ} {Γ : ∀ r m, FiniteGame (M r m) n (C r m) Seed}
  {F : Measure ℝ} {g ρ vstar : ℝ}

theorem affine_rows_diagonal
    (h : ∀ r, CongestedAssumptions (M r) (C r) (Γ r) F g ρ vstar)
    (η : ℕ → ℝ) (hη0 : ∀ r, 0 ≤ η r) (hη1 : ∀ r, η r ≤ 1)
    (hη : Tendsto η atTop (𝓝 1))
    (hA : ∀ r m, (Γ r m).A = Schedule.affine n (η r) (hη0 r) (hη1 r))
    (φ : ℕ → ℕ)
    (hM : Tendsto (fun k => M k (φ k)) atTop atTop)
    (hC : Tendsto (fun k => (C k (φ k) : ℝ) / M k (φ k)) atTop (𝓝 ρ)) :
    NearPPIAssumptions (fun k => M k (φ k)) (fun k => C k (φ k)) (fun k => Γ k (φ k)) F g
      (fun k => (1 + ((n : ℝ) - 1) * η k) / n) ρ vstar := by
  have hd : CongestedAssumptions (fun k => M k (φ k)) (fun k => C k (φ k)) (fun k => Γ k (φ k)) F g ρ vstar := {
    proposers_two := (h 0).proposers_two
    capacity_lt_population := fun k => (h k).capacity_lt_population (φ k)
    common_values := fun k => (h k).common_values (φ k)
    common_fee := fun k => (h k).common_fee (φ k)
    ratio_pos := (h 0).ratio_pos
    ratio_lt_one := (h 0).ratio_lt_one
    population_grows := hM
    capacity_ratio := hC
    equilibria := fun k => (h k).equilibria (φ k)
    feasible_continuations := fun k => (h k).feasible_continuations (φ k)
    visible_atomless := fun k => (h k).visible_atomless (φ k)
    policy_symmetry := fun k => (h k).policy_symmetry (φ k)
    scarcity := (h 0).scarcity
    efficient_cutoff := (h 0).efficient_cutoff
    local_density := (h 0).local_density }
  exact hd.nearPPI_of_affine η hη0 hη1 hη (fun k => hA k (φ k))

variable [IsProbabilityMeasure F] [NullSingletonClass F]

theorem affine_pointwise_limit_test
    (h : ∀ r, CongestedAssumptions (M r) (C r) (Γ r) F g ρ vstar)
    (η : ℕ → ℝ) (hη0 : ∀ r, 0 ≤ η r) (hη1 : ∀ r, η r ≤ 1)
    (hη : Tendsto η atTop (𝓝 1))
    (hA : ∀ r m, (Γ r m).A = Schedule.affine n (η r) (hη0 r) (hη1 r))
    (i : ∀ r m, Fin (M r m)) (ν : ℕ → ℕ → Measure (JointAction n))
    [∀ r m, IsProbabilityMeasure (ν r m)] (v : ℝ) (hv : vstar < v)
    (hbr : ∀ r m, ∀ᵐ act ∂ν r m, (problem (Γ r m) (i r m)).BestResponse v act)
    (f : ℕ → ℝ) (L : ℕ → ℝ)
    (hL : ∀ r, Tendsto (fun m => (mixedCountLaw (Γ r m) (i r m) (ν r m)).expect
      (fun k => f k.val)) atTop (𝓝 (L r))) : Tendsto L atTop (𝓝 (f 1)) := by
  apply tendsto_row_limits_of_market_diagonals M C ρ
    (fun r => (h r).population_grows) (fun r => (h r).capacity_ratio) _ L (f 1) hL
  intro φ hM hC
  have hd := affine_rows_diagonal h η hη0 hη1 hη hA φ hM hC
  have hh := hd.mixed_count_limit (fun k => i k (φ k)) (fun k => ν k (φ k)) v
    (ne_of_gt hv) (fun k => hbr k (φ k)) f
  simpa only [if_pos hv] using hh

theorem affine_pointwise_limit_multiplicity
    (h : ∀ r, CongestedAssumptions (M r) (C r) (Γ r) F g ρ vstar)
    (η : ℕ → ℝ) (hη0 : ∀ r, 0 ≤ η r) (hη1 : ∀ r, η r ≤ 1)
    (hη : Tendsto η atTop (𝓝 1))
    (hA : ∀ r m, (Γ r m).A = Schedule.affine n (η r) (hη0 r) (hη1 r))
    (i : ∀ r m, Fin (M r m)) (ν : ℕ → ℕ → Measure (JointAction n))
    [∀ r m, IsProbabilityMeasure (ν r m)] (v : ℝ) (hv : vstar < v)
    (hbr : ∀ r m, ∀ᵐ act ∂ν r m, (problem (Γ r m) (i r m)).BestResponse v act)
    (μ : ℕ → ℝ)
    (hμ : ∀ r, Tendsto (fun m => (mixedCountLaw (Γ r m) (i r m) (ν r m)).load /
      (mixedCountLaw (Γ r m) (i r m) (ν r m)).success) atTop (𝓝 (μ r))) :
    Tendsto μ atTop (𝓝 1) := by
  apply tendsto_row_limits_of_market_diagonals M C ρ
    (fun r => (h r).population_grows) (fun r => (h r).capacity_ratio) _ μ 1 hμ
  intro φ hM hC
  have hd := affine_rows_diagonal h η hη0 hη1 hη hA φ hM hC
  have hs : Tendsto (fun k => (mixedCountLaw (Γ k (φ k)) (i k (φ k)) (ν k (φ k))).success)
      atTop (𝓝 1) := by
    have hh := hd.mixed_count_limit (fun k => i k (φ k)) (fun k => ν k (φ k)) v
      (ne_of_gt hv) (fun k => hbr k (φ k)) successIndicator
    simpa only [CountLaw.success, if_pos hv, successIndicator, Nat.one_ne_zero, if_false] using hh
  have hl : Tendsto (fun k => (mixedCountLaw (Γ k (φ k)) (i k (φ k)) (ν k (φ k))).load)
      atTop (𝓝 1) := by
    have hh := hd.mixed_count_limit (fun k => i k (φ k)) (fun k => ν k (φ k)) v
      (ne_of_gt hv) (fun k => hbr k (φ k)) (fun r => (r : ℝ))
    simpa only [CountLaw.load, if_pos hv, Nat.cast_one] using hh
  have hdiv := hl.div hs one_ne_zero
  change Tendsto (fun k => (mixedCountLaw (Γ k (φ k)) (i k (φ k)) (ν k (φ k))).load /
    (mixedCountLaw (Γ k (φ k)) (i k (φ k)) (ν k (φ k))).success) atTop (𝓝 ((1 : ℝ) / 1)) at hdiv
  simpa only [div_self one_ne_zero] using hdiv

theorem affine_finite_value_limits
    {V : Type*} [Finite V] (v : V → ℝ) (hv : ∀ x, vstar < v x)
    (h : ∀ r, CongestedAssumptions (M r) (C r) (Γ r) F g ρ vstar)
    (η : ℕ → ℝ) (hη0 : ∀ r, 0 ≤ η r) (hη1 : ∀ r, η r ≤ 1)
    (hη : Tendsto η atTop (𝓝 1))
    (hA : ∀ r m, (Γ r m).A = Schedule.affine n (η r) (hη0 r) (hη1 r))
    (i : ∀ (_x : V) r m, Fin (M r m)) (ν : V → ℕ → ℕ → Measure (JointAction n))
    [∀ x r m, IsProbabilityMeasure (ν x r m)]
    (hbr : ∀ x r m, ∀ᵐ act ∂ν x r m, (problem (Γ r m) (i x r m)).BestResponse (v x) act)
    (Q μ : V → ℕ → ℝ)
    (hQ : ∀ x r, Tendsto (fun m => (mixedCountLaw (Γ r m) (i x r m) (ν x r m)).success)
      atTop (𝓝 (Q x r)))
    (hμ : ∀ x r, Tendsto (fun m => (mixedCountLaw (Γ r m) (i x r m) (ν x r m)).load /
      (mixedCountLaw (Γ r m) (i x r m) (ν x r m)).success) atTop (𝓝 (μ x r))) :
    ∀ ε > 0, ∀ᶠ r in atTop, ∀ x, |Q x r - 1| < ε ∧ |μ x r - 1| < ε := by
  intro ε hε
  apply Filter.eventually_all.mpr
  intro x
  have hq : Tendsto (Q x) atTop (𝓝 1) := by
    simpa only [successIndicator, Nat.one_ne_zero, if_false] using
      affine_pointwise_limit_test h η hη0 hη1 hη hA (i x) (ν x) (v x) (hv x)
        (hbr x) successIndicator (Q x) (hQ x)
  have hm := affine_pointwise_limit_multiplicity h η hη0 hη1 hη hA (i x) (ν x)
    (v x) (hv x) (hbr x) (μ x) (hμ x)
  filter_upwards [Metric.tendsto_nhds.mp hq ε hε, Metric.tendsto_nhds.mp hm ε hε] with r hqr hmr
  exact ⟨by simpa only [Real.dist_eq] using hqr, by simpa only [Real.dist_eq] using hmr⟩

theorem affine_ae_actual_limits
    (h : ∀ r, CongestedAssumptions (M r) (C r) (Γ r) F g ρ vstar)
    (η : ℕ → ℝ) (hη0 : ∀ r, 0 ≤ η r) (hη1 : ∀ r, η r ≤ 1)
    (hη : Tendsto η atTop (𝓝 1))
    (hA : ∀ r m, (Γ r m).A = Schedule.affine n (η r) (hη0 r) (hη1 r)) :
    ∀ᵐ v ∂F, vstar < v → ∀ (i : ∀ r m, Fin (M r m)) (Q μ : ℕ → ℝ),
      (∀ r, Tendsto (fun m => (typeOutcome (Γ r m) (i r m) v).success)
        atTop (𝓝 (Q r))) →
      (∀ r, Tendsto (fun m => (typeOutcome (Γ r m) (i r m) v).load /
        (typeOutcome (Γ r m) (i r m) v).success) atTop (𝓝 (μ r))) →
      Tendsto Q atTop (𝓝 1) ∧ Tendsto μ atTop (𝓝 1) := by
  have hfull : ∀ᵐ v ∂F, ∀ r m (i : Fin (M r m)), ∀ᵐ act ∂(Γ r m).σ v,
      (problem (Γ r m) i).BestResponse v act := by
    apply ae_all_iff.mpr
    intro r
    exact ae_all_rows_bestResponse (M r) (C r) (Γ r) F (h r).common_values
      (fun m => ((h r).equilibria m).users)
  filter_upwards [hfull] with v hv
  intro hvstar i Q μ hQ hμ
  have hbr (r m : ℕ) : ∀ᵐ act ∂(Γ r m).σ v,
      (problem (Γ r m) (i r m)).BestResponse v act := hv r m (i r m)
  constructor
  · have hh := affine_pointwise_limit_test h η hη0 hη1 hη hA i
      (fun r m => (Γ r m).σ v) v hvstar hbr successIndicator Q hQ
    simpa only [successIndicator, Nat.one_ne_zero, if_false] using hh
  · exact affine_pointwise_limit_multiplicity h η hη0 hη1 hη hA i
      (fun r m => (Γ r m).σ v) v hvstar hbr μ hμ

end FCAppendix.Bayes
