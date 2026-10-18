import FCAppendix.Exclusive.SourceStationaryGame
import FCAppendix.Exclusive.CompletionExistingSourceFamily
import FCAppendix.Exclusive.ScarceConstructedLimits

noncomputable section
namespace FCAppendix.Bayes.ExclusiveConstruction
open MeasureTheory ProbabilityTheory Game Exclusive Set Filter Topology
open Completion.Exclusive

structure ScarceEquilibriumFamily (d : ℕ) (G : Schedule (d+1)) (g rho h : ℝ) where
  F : Measure ℝ
  probability : IsProbabilityMeasure F
  atomless : NullSingletonClass F
  E : Set ℝ
  measurable_E : MeasurableSet E
  high_mass : F.real E = h
  positive_values : F.real (Ioi g) = 1
  H : ℝ
  eps : ℝ
  lowWidth : ℝ
  H_pos : 0 < H
  eps_pos : 0 < eps
  eps_lt_one : eps < 1
  lowWidth_pos : 0 < lowWidth
  high_set : E = Icc (H*(1-eps)) (H*(1+eps))
  separation : g+lowWidth < H*(1-eps)
  high_values : ∀ᵐ v ∂F.restrict E, v ∈ Icc (H*(1-eps)) (H*(1+eps))
  efficient_cutoff :
    let vStar := g+lowWidth*(1-((d+1:ℕ):ℝ)*rho)/(1-h)
    vStar ∈ Ioo g (g+lowWidth) ∧ F.real (Iic vStar)=1-((d+1:ℕ):ℝ)*rho ∧
      F.real (Ioi vStar)=((d+1:ℕ):ℝ)*rho
  M : ℕ → ℕ
  C : ℕ → ℕ
  population_positive : ∀ t, 0 < M t
  capacity_positive : ∀ t, 0 < C t
  population_grows : Tendsto M atTop atTop
  density : Tendsto (fun t => (C t : ℝ)/(M t : ℝ)) atTop (𝓝 rho)
  game : ∀ a : UserTariff, a.Allowed → ∀ t, FiniteGame (M t) (d+1) (C t) unitInterval
  posterior : ∀ a ha t, PosteriorSystem (game a ha t)
  common_values : ∀ a ha t, (game a ha t).F=F
  common_base : ∀ a ha t, (game a ha t).G=G
  common_fee : ∀ a ha t, (game a ha t).g=g
  users : ∀ a ha t, ExclusiveTariffUsersOptimal (game a ha t) a
  proposers : ∀ a ha t, ExclusivePosteriorOptimalAE (game a ha t) (posterior a ha t)
  symmetric : ∀ a ha t, SymmetricProposersOnPath (game a ha t)
  equivariant : ∀ a ha t, PolicyLawEquivariant (game a ha t)
  broadcast : ∀ a ha t, ExclusiveBroadcastOn (game a ha t) E
  finite_atomless : ∀ a ha t b,
    (Measure.map (fun x : ℝ × JointAction (d+1) => x.2.bid)
      ((F.restrict E) ⊗ₘ (game a ha t).σ)) {b}=0
  eta : ℝ
  l : ℝ
  u : ℝ
  priceLo : ℝ
  priceHi : ℝ
  eta_mem : eta ∈ Ioo (0:ℝ) 1
  exposure_bounds : 0 < l ∧ l < u ∧ u < 1
  price_bounds : 0 < priceLo ∧ priceLo ≤ priceHi
  source_limits : ∀ a ha, ∃ beta lam p,
    ExistingSourceFamilyConclusion (game a ha) F E a G g rho
      (H*Completion.Exclusive.sourceBid d a h rho*(1-eta))
      (H*Completion.Exclusive.sourceBid d a h rho*(1+eta))
      l u (H*priceLo) (H*priceHi) beta lam p

attribute [instance] ScarceEquilibriumFamily.probability ScarceEquilibriumFamily.atomless

theorem ScarceEquilibriumFamily.actual_limits {d : ℕ} {G : Schedule (d+1)}
    {g rho h target : ℝ} (D : ScarceEquilibriumFamily d G g rho h)
    (hd : 1 ≤ d) (hrho : 0 < rho) (hrh : rho < h)
    (htarget : target < ((d+1:ℕ):ℝ)*rho/(h*PayOnce.success (d+1) (rho/h)))
    (a : UserTariff) (ha : a.Allowed) :
    Tendsto (fun t => finiteLoad (D.game a ha t)) atTop (𝓝 (((d+1:ℕ):ℝ)*rho)) ∧
    (∀ᶠ t in atTop, 0 < finiteCoverage (D.game a ha t) ∧
      target < finiteMultiplicity (D.game a ha t) ∧ finiteMultiplicity (D.game a ha t) ≤ ((d+1:ℕ):ℝ)) ∧
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ Q mu : ℝ,
      0 < Q ∧ target < mu ∧ mu ≤ ((d+1:ℕ):ℝ) ∧ Q ≤ h*PayOnce.success (d+1) (rho/h) ∧
      Tendsto (fun t => finiteCoverage (D.game a ha (phi t))) atTop (𝓝 Q) ∧
      Tendsto (fun t => finiteLoad (D.game a ha (phi t))) atTop (𝓝 (((d+1:ℕ):ℝ)*rho)) ∧
      Tendsto (fun t => finiteMultiplicity (D.game a ha (phi t))) atTop (𝓝 mu) := by
  have hmass : ∀ t, (D.game a ha t).F.real D.E=h := by
    intro t
    rw [D.common_values,D.high_mass]
  have hopt : ∀ t, ExclusiveOptimalOnPath (D.game a ha t) (D.posterior a ha t) :=
    fun t => exclusiveOptimalOnPath_of_feasible _ _ (D.proposers a ha t)
  exact ⟨(exclusive_scarce_eventual_multiplicity (D.game a ha) hd D.population_grows
    (D.posterior a ha) hopt (D.symmetric a ha) D.E D.measurable_E (D.broadcast a ha)
    hmass D.density hrho hrh htarget).1,
    (exclusive_scarce_eventual_multiplicity (D.game a ha) hd D.population_grows
    (D.posterior a ha) hopt (D.symmetric a ha) D.E D.measurable_E (D.broadcast a ha)
    hmass D.density hrho hrh htarget).2,
    exists_scarce_actual_limit hd (D.game a ha) (D.posterior a ha) (D.proposers a ha)
      (D.symmetric a ha) D.E D.measurable_E (D.broadcast a ha) hmass D.population_grows
      D.density hrho hrh htarget⟩

end FCAppendix.Bayes.ExclusiveConstruction
