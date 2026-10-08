import FCAppendix.PayOnce.RareSurplusMass
import FCAppendix.PayOnce.ActualVanishingWindow

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open PayOnce PayOnce.AnalyticalKernel PayOnce.AnalyticalRareSuccess PayOnce.CompactifiedBidLaws
variable {N C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem actual_rare_surplus_mass_zero
    (Γ : ∀ t, FiniteGame (N t+1) (k+1) (C t) Seed)
    (hk : 1 ≤ k) (hNpos : ∀ t, 0 < N t) (hN : Tendsto N atTop atTop)
    (hcm : ∀ t, C t ≤ N t+1)
    (hA : ∀ t, (Γ t).A = Schedule.once (k+1)) (hG : ∀ t, (Γ t).G = Schedule.once (k+1))
    (hu : ∀ t, UsersOptimal (Γ t)) (B : ∀ t, PosteriorSystem (Γ t))
    (hB : ∀ t, PosteriorProposerOptimalAE (Γ t) (B t))
    (hsym : ∀ t, SymmetricProposersOnPath (Γ t)) (hatom : ∀ t, PositiveVisibleAtomless (Γ t))
    (hroute : ∀ t, ∀ᵐ z ∂((Γ t).F ⊗ₘ (Γ t).σ), z.2.routeCount = k+1)
    (hbid : ∀ t, ∀ᵐ z ∂((Γ t).F ⊗ₘ (Γ t).σ), 0 < z.2.bid)
    {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => bidLaw (Γ t)) atTop (𝓝 G₀))
    {ρ L : ℝ} (hρ : 0 < ρ) (hL : 0 < L)
    (hroot : KernelDemand.demand (k+1) (G₀ : Measure ENNReal) L = ρ)
    (hunique : ∀ T : ℝ, 0 < T → KernelDemand.demand (k+1) (G₀ : Measure ENNReal) T = ρ → T = L)
    (hcapacity : Tendsto (fun t => (C t : ℝ) / N t) atTop (𝓝 ρ))
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    Tendsto (fun t => ((Γ t).F ⊗ₘ (Γ t).σ)
      {z | δ ≤ z.1-(Γ t).g-z.2.bid ∧ z.2.bid ∈ Icc ε L}) atTop (𝓝 0) := by
  let G : ℕ → ProbabilityMeasure ℝ := fun t => ⟨realBidLaw (Γ t), inferInstance⟩
  have hraw t : scaledLaw (G t) 1 = bidLaw (Γ t) := by
    apply Subtype.ext
    change (realBidLaw (Γ t)).map (fun b : ℝ => ENNReal.ofReal (b/1)) = _
    simp only [div_one]
    exact (compactifiedBidLaw_eq_map_realBidLaw (Γ t) (by omega) (hroute t)).symm
  have hweakRaw : Tendsto (fun t => scaledLaw (G t) 1) atTop (𝓝 G₀) := by
    simpa only [hraw] using hweak
  choose T hTm hTp hTae hcompare using fun t =>
    exists_ae_scaled_analytical_comparisons (Γ t) hk (hcm t) (hA t) (hG t)
      (hu t) (B t) (hB t) (hsym t) (hatom t) (hroute t) (hbid t) ⟨0, by omega⟩ 1 zero_lt_one
  apply tendsto_rare_surplus_mass_zero N hNpos hN (by omega)
    (fun t => (Γ t).F ⊗ₘ (Γ t).σ) (fun _ z => z.2.bid) (fun t z => z.1-(Γ t).g)
    (fun _ => (measurable_bid (k+1)).comp measurable_snd) G
    (fun t => realBidLaw_eq_action_map (Γ t)) (fun t => ae_realBidLaw_pos (Γ t) (hbid t))
    hweakRaw hρ hL hroot hunique (fun t => by simpa using hcm t) hcapacity T _ hε hδ
  intro t
  filter_upwards [hcompare t] with z hz
  constructor
  · simpa only [div_one, rescaledRealLaw_one, Set.image_id', G] using hz.2.1
  · exact hz.2.2

theorem payOnce_rare_surplus_limit
    (Γ : ∀ t, FiniteGame (N t+1) (k+1) (C t) Seed)
    (hk : 1 ≤ k) (hc : ∀ t, 0 < C t) (hcm : ∀ t, C t < N t+1)
    (hN : Tendsto N atTop atTop)
    (hA : ∀ t, (Γ t).A = Schedule.once (k+1)) (hG : ∀ t, (Γ t).G = Schedule.once (k+1))
    (hu : ∀ t, UsersOptimal (Γ t)) (B : ∀ t, PosteriorSystem (Γ t))
    (hB : ∀ t, PosteriorProposerOptimalAE (Γ t) (B t))
    (hsym : ∀ t, SymmetricProposersOnPath (Γ t)) (hatom : ∀ t, PositiveVisibleAtomless (Γ t))
    (F : Measure ℝ) [IsProbabilityMeasure F] [NullSingletonClass F]
    (hF : ∀ t, (Γ t).F = F) {g : ℝ} (hg : ∀ t, (Γ t).g = g)
    (hactive : ∀ᵐ v ∂F, g < v)
    {ρ : ℝ} (hρ : Tendsto (fun t => (C t : ℝ)/(N t+1)) atTop (𝓝 ρ))
    (hρb : ρ ∈ Ioo (0:ℝ) 1) {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => bidLaw (Γ t)) atTop (𝓝 G₀)) :
    ∃! L, 0 < L ∧ KernelDemand.demand (k+1) (G₀ : Measure ENNReal) L = ρ ∧
      ∀ ε δ : ℝ, 0 < ε → 0 < δ →
        Tendsto (fun t => ((Γ t).F ⊗ₘ (Γ t).σ)
          {z | δ ≤ z.1-g-z.2.bid ∧ z.2.bid ∈ Icc ε L}) atTop (𝓝 0) := by
  have hNpos t : 0 < N t := by have := hc t; have := hcm t; omega
  have hM : Tendsto (fun t => N t+1) atTop atTop := (tendsto_add_atTop_nat 1).comp hN
  have hρM : Tendsto (fun t => (C t:ℝ)/((N t+1:ℕ):ℝ)) atTop (𝓝 ρ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hρ
  obtain ⟨_,L,hL,huniq⟩ := payOnce_positive_capacity_root Γ hk hc hcm hM hA hG hu B hB hsym hatom
    F hF hg hactive hρM hρb hweak
  refine ⟨L,⟨hL.1,hL.2,?_⟩,fun T hT => huniq T ⟨hT.1,hT.2.1⟩⟩
  intro ε δ hε hδ
  have hvalue t : PositiveValueAtomless (Γ t) := by
    intro v _
    rw [hF t]
    exact measure_singleton v
  have hfull t := ae_full_routes_positive_bids_of_active (Γ t) (hc t) (hcm t) (hA t) (hG t)
    (hu t) (B t) (hB t) (hsym t) (hvalue t) (by simpa only [hF t, hg t] using hactive)
  have hratio : Tendsto (fun t => ((N t:ℝ)+1)/N t) atTop (𝓝 1) := by
    have hh := (tendsto_const_nhds (x := (1:ℝ))).add
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hN))
    simp only [add_zero] at hh
    apply hh.congr
    intro t
    have hne : (N t:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hNpos t).ne'
    dsimp only [Function.comp_def]
    field_simp
  have hcap : Tendsto (fun t => (C t:ℝ)/N t) atTop (𝓝 ρ) := by
    have hh := hρ.mul hratio
    simp only [mul_one] at hh
    apply hh.congr
    intro t
    have hn : (0:ℝ) < N t := Nat.cast_pos.mpr (hNpos t)
    field_simp
  have hh := actual_rare_surplus_mass_zero Γ hk hNpos hN (fun t => (hcm t).le)
    hA hG hu B hB hsym hatom (fun t => (hfull t).mono fun _ hz => hz.2)
    (fun t => (hfull t).mono fun _ hz => hz.1) hweak hρb.1 hL.1 hL.2
    (fun T hT he => huniq T ⟨hT,he⟩) hcap hε hδ
  simpa only [hg] using hh

end FCAppendix.Bayes
