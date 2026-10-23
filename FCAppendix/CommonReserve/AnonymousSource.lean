import FCAppendix.CommonReserve.Source
import FCAppendix.CommonReserve.AnonymousReserve

noncomputable section
namespace FCAppendix.CommonReserve
open Game MeasureTheory ProbabilityTheory Filter Set Topology

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

structure AnonymousSourceAssumptions (M C : ℕ → ℕ)
    (Γ : ∀ k, Bayes.FiniteGame (M k) n (C k) Seed)
    (F : Measure ℝ) (g r ρ vstar : ℝ) : Prop where
  proposers : 2 ≤ n
  users_pos : ∀ k, 0 < M k
  capacity_pos : ∀ k, 0 < C k
  capacity_lt_users : ∀ k, C k < M k
  law : ∀ k, (Γ k).F = F
  base : ∀ k, (Γ k).g = g
  reserve_nonneg : 0 ≤ r
  bid_charge : ∀ k, (Γ k).A = Schedule.ppi n
  rho_pos : 0 < ρ
  rho_lt_one : ρ < 1
  users_tendsto : Tendsto M atTop atTop
  capacity_tendsto : Tendsto (fun k => (C k : ℝ) / M k) atTop (𝓝 ρ)
  scarcity : (n : ℝ) * ρ < F.real (Ioi g)
  cutoff : F.real (Ioi vstar) = (n : ℝ) * ρ
  density : LocalCutoffDensity F vstar
  optimal : ∀ k, Bayes.UsersOptimal (Γ k)
  uniform_ties : ∀ k j, UniformReserveRule (Γ k).seedLaw ((Γ k).policy j) r

structure AnonymousConclusions (M C : ℕ → ℕ)
    (Γ : ∀ k, Bayes.FiniteGame (M k) n (C k) Seed)
    (F : Measure ℝ) (g r vstar : ℝ) : Prop where
  utility : ∀ (i : ∀ k, Fin (M k)) v,
    Tendsto (fun k => (Bayes.problem (Γ k) (i k)).envelope v) atTop
      (𝓝 (max (v - g - max r (vstar - g)) 0))
  utility_compact : ∀ (i : ∀ k, Fin (M k)) (K : Set ℝ), IsCompact K →
    TendstoUniformlyOn (fun k v => (Bayes.problem (Γ k) (i k)).envelope v)
      (fun v => max (v - g - max r (vstar - g)) 0) atTop K
  fixed_success : ∀ (i : ∀ k, Fin (M k)) v, v ≠ g + max r (vstar - g) →
    ∀ a : ℕ → JointAction n,
    (∀ k, (Bayes.problem (Γ k) (i k)).BestResponse v (a k)) →
    Tendsto (fun k => ((Bayes.problem (Γ k) (i k)).outcome (a k)).success) atTop
      (𝓝 (if g + max r (vstar - g) < v then 1 else 0))
  fixed_payment : ∀ (i : ∀ k, Fin (M k)) v, v ≠ g + max r (vstar - g) →
    ∀ a : ℕ → JointAction n,
    (∀ k, (Bayes.problem (Γ k) (i k)).BestResponse v (a k)) →
    Tendsto (fun k => anonymousCost (Γ k) (i k) (a k)) atTop
      (𝓝 ((g + max r (vstar - g)) * if g + max r (vstar - g) < v then 1 else 0))
  mixed_success : ∀ (i : ∀ k, Fin (M k)) (ν : ℕ → Measure (JointAction n))
    [∀ k, IsProbabilityMeasure (ν k)] v, v ≠ g + max r (vstar - g) →
    (∀ k, ∀ᵐ a ∂ν k, (Bayes.problem (Γ k) (i k)).BestResponse v a) →
    Tendsto (fun k => (Bayes.mixedCountLaw (Γ k) (i k) (ν k)).success) atTop
      (𝓝 (if g + max r (vstar - g) < v then 1 else 0))
  mixed_payment_integrable : ∀ (i : ∀ k, Fin (M k)) (ν : ℕ → Measure (JointAction n))
    [∀ k, IsProbabilityMeasure (ν k)] v,
    (∀ k, ∀ᵐ a ∂ν k, (Bayes.problem (Γ k) (i k)).BestResponse v a) →
    ∀ k, Integrable (anonymousCost (Γ k) (i k)) (ν k)
  mixed_payment : ∀ (i : ∀ k, Fin (M k)) (ν : ℕ → Measure (JointAction n))
    [∀ k, IsProbabilityMeasure (ν k)] v, v ≠ g + max r (vstar - g) →
    (∀ k, ∀ᵐ a ∂ν k, (Bayes.problem (Γ k) (i k)).BestResponse v a) →
    Tendsto (fun k => ∫ a, anonymousCost (Γ k) (i k) a ∂ν k) atTop
      (𝓝 ((g + max r (vstar - g)) * if g + max r (vstar - g) < v then 1 else 0))
  actual_success : ∀ᵐ v ∂F, ∀ (i : ∀ k, Fin (M k)),
    Tendsto (fun k => (Bayes.typeOutcome (Γ k) (i k) v).success) atTop
      (𝓝 (if g + max r (vstar - g) < v then 1 else 0))
  actual_payment : ∀ᵐ v ∂F, ∀ (i : ∀ k, Fin (M k)),
    Tendsto (fun k => ∫ a, anonymousCost (Γ k) (i k) a ∂(Γ k).σ v) atTop
      (𝓝 ((g + max r (vstar - g)) * if g + max r (vstar - g) < v then 1 else 0))
  coverage : Tendsto (fun k => Bayes.finiteCoverage (Γ k)) atTop
    (𝓝 (F.real (Ioi (g + max r (vstar - g)))))
  load : Tendsto (fun k => Bayes.finiteLoad (Γ k)) atTop
    (𝓝 (F.real (Ioi (g + max r (vstar - g)))))
  duplicates : Tendsto (fun k => Bayes.finiteLoad (Γ k) - Bayes.finiteCoverage (Γ k)) atTop (𝓝 0)

end FCAppendix.CommonReserve
