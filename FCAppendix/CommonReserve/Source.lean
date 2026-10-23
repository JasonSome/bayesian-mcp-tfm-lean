import FCAppendix.CommonReserve.ActualEstimates
import FCAppendix.CommonReserve.UniformTies
import FCAppendix.CommonReserve.PriceIdentification

noncomputable section
namespace FCAppendix.CommonReserve
open Game MeasureTheory ProbabilityTheory Filter Set Topology

structure LocalCutoffDensity (F : Measure ℝ) (vstar : ℝ) : Prop where
  local_density : ∃ (f : ℝ → ℝ) (W : Set ℝ), Measurable f ∧ MeasurableSet W ∧
    W ∈ 𝓝 vstar ∧
    F.restrict W = (volume.withDensity (fun x => ENNReal.ofReal (f x))).restrict W ∧
    ContinuousAt f vstar ∧ 0 < f vstar

theorem LocalCutoffDensity.interval_mass {F : Measure ℝ} [IsFiniteMeasure F]
    {vstar : ℝ} (h : LocalCutoffDensity F vstar) :
    (∀ v < vstar, 0 < F.real (Ioo v vstar)) ∧
      (∀ v > vstar, 0 < F.real (Ioo vstar v)) := by
  obtain ⟨f, W, hf, hW, hWn, hF, hc, hp⟩ := h.local_density
  exact Bayes.cutoff_interval_mass_of_local_density F f hf vstar W hW hWn hF hc hp

variable {n : ℕ} {r : ℝ} {Seed : Type*} [MeasurableSpace Seed]

structure SourceAssumptions (M C : ℕ → ℕ)
    (Γ : ∀ k, FiniteGame (M k) n (C k) r Seed)
    (F : Measure ℝ) (g ρ vstar : ℝ) : Prop where
  proposers : 2 ≤ n
  users_pos : ∀ k, 0 < M k
  capacity_pos : ∀ k, 0 < C k
  capacity_lt_users : ∀ k, C k < M k
  law : ∀ k, (Γ k).F = F
  base : ∀ k, (Γ k).g = g
  rho_pos : 0 < ρ
  rho_lt_one : ρ < 1
  users_tendsto : Tendsto M atTop atTop
  capacity_tendsto : Tendsto (fun k => (C k : ℝ) / M k) atTop (𝓝 ρ)
  scarcity : (n : ℝ) * ρ < F.real (Ioi g)
  cutoff : F.real (Ioi vstar) = (n : ℝ) * ρ
  density : LocalCutoffDensity F vstar
  optimal : ∀ k, (Γ k).UsersOptimal
  uniform_ties : ∀ k j, UniformReserveRule (Γ k).seedLaw ((Γ k).policy j) r

structure Conclusions (M C : ℕ → ℕ)
    (Γ : ∀ k, FiniteGame (M k) n (C k) r Seed)
    (F : Measure ℝ) (g vstar : ℝ) : Prop where
  utility : ∀ (i : ∀ k, Fin (M k)) v,
    Tendsto (fun k => (Γ k).envelope (i k) v) atTop
      (𝓝 (max (v - g - max r (vstar - g)) 0))
  utility_compact : ∀ (i : ∀ k, Fin (M k)) (K : Set ℝ), IsCompact K →
    TendstoUniformlyOn (fun k v => (Γ k).envelope (i k) v)
      (fun v => max (v - g - max r (vstar - g)) 0) atTop K
  fixed_success : ∀ (i : ∀ k, Fin (M k)) v, v ≠ g + max r (vstar - g) →
    ∀ a : ℕ → Action n r,
    (∀ k b, (Γ k).purePayoff (i k) v b ≤ (Γ k).purePayoff (i k) v (a k)) →
    Tendsto (fun k => ((Γ k).outcome (i k) (a k)).success) atTop
      (𝓝 (if g + max r (vstar - g) < v then 1 else 0))
  fixed_payment : ∀ (i : ∀ k, Fin (M k)) v, v ≠ g + max r (vstar - g) →
    ∀ a : ℕ → Action n r,
    (∀ k b, (Γ k).purePayoff (i k) v b ≤ (Γ k).purePayoff (i k) v (a k)) →
    Tendsto (fun k => (Γ k).totalPayment (i k) (a k)) atTop
      (𝓝 ((g + max r (vstar - g)) * if g + max r (vstar - g) < v then 1 else 0))
  mixed_success : ∀ (i : ∀ k, Fin (M k)) (ν : ℕ → Measure (Action n r))
    [∀ k, IsProbabilityMeasure (ν k)] v, v ≠ g + max r (vstar - g) →
    (∀ k, ∀ᵐ a ∂ν k, ∀ b, (Γ k).purePayoff (i k) v b ≤ (Γ k).purePayoff (i k) v a) →
    Tendsto (fun k => ((Γ k).mixedOutcome (i k) (ν k)).success) atTop
      (𝓝 (if g + max r (vstar - g) < v then 1 else 0))
  mixed_payment_integrable : ∀ (i : ∀ k, Fin (M k)) (ν : ℕ → Measure (Action n r))
    [∀ k, IsProbabilityMeasure (ν k)] v,
    (∀ k, ∀ᵐ a ∂ν k, ∀ b, (Γ k).purePayoff (i k) v b ≤ (Γ k).purePayoff (i k) v a) →
    ∀ k, Integrable ((Γ k).totalPayment (i k)) (ν k)
  mixed_payment : ∀ (i : ∀ k, Fin (M k)) (ν : ℕ → Measure (Action n r))
    [∀ k, IsProbabilityMeasure (ν k)] v, v ≠ g + max r (vstar - g) →
    (∀ k, ∀ᵐ a ∂ν k, ∀ b, (Γ k).purePayoff (i k) v b ≤ (Γ k).purePayoff (i k) v a) →
    Tendsto (fun k => ∫ a, (Γ k).totalPayment (i k) a ∂ν k) atTop
      (𝓝 ((g + max r (vstar - g)) * if g + max r (vstar - g) < v then 1 else 0))
  actual_success : ∀ᵐ v ∂F, ∀ (i : ∀ k, Fin (M k)),
    Tendsto (fun k => ((Γ k).typeOutcome (i k) v).success) atTop
      (𝓝 (if g + max r (vstar - g) < v then 1 else 0))
  actual_payment : ∀ᵐ v ∂F, ∀ (i : ∀ k, Fin (M k)),
    Tendsto (fun k => ∫ a, (Γ k).totalPayment (i k) a ∂(Γ k).σ v) atTop
      (𝓝 ((g + max r (vstar - g)) * if g + max r (vstar - g) < v then 1 else 0))
  coverage : Tendsto (fun k => (Γ k).coverage) atTop
    (𝓝 (F.real (Ioi (g + max r (vstar - g)))))
  load : Tendsto (fun k => (Γ k).load) atTop
    (𝓝 (F.real (Ioi (g + max r (vstar - g)))))
  duplicates : Tendsto (fun k => (Γ k).load - (Γ k).coverage) atTop (𝓝 0)

end FCAppendix.CommonReserve
