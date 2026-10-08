import FCAppendix.PayOnce.InactiveScaledComparisons
import FCAppendix.PayOnce.DummyVanishingWindow
import FCAppendix.PayOnce.InactivePositiveRoot
import FCAppendix.PayOnce.ActualVanishingWindow

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open PayOnce PayOnce.AnalyticalKernel PayOnce.DummyRareSuccess PayOnce.CompactifiedBidLaws
variable {N C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem inactive_vanishing_window_mass_zero
    (Γ : ∀ t, FiniteGame (N t+1) (k+1) (C t) Seed)
    (hk : 1 ≤ k) (hNpos : ∀ t, 0 < N t) (hN : Tendsto N atTop atTop)
    (hc : ∀ t, 0 < C t) (hcm : ∀ t, C t < N t+1)
    (hA : ∀ t, (Γ t).A = Schedule.once (k+1)) (hG : ∀ t, (Γ t).G = Schedule.once (k+1))
    (hu : ∀ t, UsersOptimal (Γ t)) (B : ∀ t, PosteriorSystem (Γ t))
    (hB : ∀ t, PosteriorProposerOptimalAE (Γ t) (B t))
    (hsym : ∀ t, SymmetricProposersOnPath (Γ t))
    (hvalue : ∀ t, PositiveValueAtomless (Γ t)) (hatom : ∀ t, PositiveVisibleAtomless (Γ t))
    (hinactive : ∀ t, InactiveAbstain (Γ t))
    {Gorig : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => bidLaw (Γ t)) atTop (𝓝 Gorig))
    {u ρ : ℝ} (hu0 : 0 < u) (hρ0 : 0 < ρ)
    (hmass : ρ < (Gorig : Measure ENNReal).real (Ioi (ENNReal.ofReal u)))
    (hcapacity : Tendsto (fun t => (C t : ℝ) / N t) atTop (𝓝 ρ))
    (a : ℕ → ℝ) (ha : ∀ t, 0 < a t) (ha0 : Tendsto a atTop (𝓝 0))
    {K : Set ℝ} (hK : IsCompact K) (hKpos : K ⊆ Ioi 0) {v : ℝ} (hv : 0 < v) :
    Tendsto (fun t => ((Γ t).F ⊗ₘ (Γ t).σ)
      {z | v ≤ z.1-(Γ t).g ∧ effectiveBid z.2/a t ∈ K}) atTop (𝓝 0) := by
  let G : ℕ → ProbabilityMeasure ℝ := fun t => PayOnce.BidScaling.realBidLaw (Γ t)
  have hraw t : scaledLaw (G t) 1 = bidLaw (Γ t) := by
    apply Subtype.ext
    change (PayOnce.BidScaling.realBidLaw (Γ t) : Measure ℝ).map (fun b : ℝ => ENNReal.ofReal (b/1)) = _
    simp only [div_one]
    exact (compactifiedBidLaw_eq_map_effectiveBidLaw (Γ t)).symm
  have hweakRaw : Tendsto (fun t => scaledLaw (G t) 1) atTop (𝓝 Gorig) := by
    simpa only [hraw] using hweak
  choose T hTm hTp hTae hcompare using fun t =>
    exists_ae_inactive_scaled_comparisons (Γ t) hk (hc t) (hcm t) (hA t) (hG t)
      (hu t) (B t) (hB t) (hsym t) (hvalue t) (hatom t) (hinactive t)
      ⟨0, by omega⟩ (a t) (ha t)
  apply tendsto_vanishing_window_mass_zero N hNpos hN (by omega : 2 ≤ k+1)
    (fun t => (Γ t).F ⊗ₘ (Γ t).σ) (fun _ z => effectiveBid z.2) (fun t z => z.1-(Γ t).g)
    (fun _ => (measurable_effectiveBid (k+1)).comp measurable_snd) G
    (fun t => realEffectiveBidLaw_eq_action_map (Γ t))
    (fun _ => Filter.Eventually.of_forall fun z => effectiveBid_nonneg z.2)
    a ha ha0 hweakRaw hu0 hρ0 hmass hcapacity T ?_ hK hKpos hv
  intro t
  filter_upwards [hcompare t,
    ae_effectiveBid_participation (Γ t) (hc t) (hcm t) (hA t) (hG t)
      (hu t) (B t) (hB t) (hsym t) (hvalue t)] with z hz hp hv
  have hv' := sub_pos.mp hv
  have hfull := hp.2.2 hv'
  have heff : effectiveBid z.2 = z.2.bid := by
    simp only [effectiveBid, hfull, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false]
  simpa only [heff] using hz hv'

theorem payOnce_inactive_vanishing_window_mass_zero
    (Γ : ∀ t, FiniteGame (N t+1) (k+1) (C t) Seed)
    (hk : 1 ≤ k) (hc : ∀ t, 0 < C t) (hcm : ∀ t, C t < N t+1)
    (hN : Tendsto N atTop atTop)
    (hA : ∀ t, (Γ t).A = Schedule.once (k+1)) (hG : ∀ t, (Γ t).G = Schedule.once (k+1))
    (hu : ∀ t, UsersOptimal (Γ t)) (B : ∀ t, PosteriorSystem (Γ t))
    (hB : ∀ t, PosteriorProposerOptimalAE (Γ t) (B t))
    (hsym : ∀ t, SymmetricProposersOnPath (Γ t))
    (hvalue : ∀ t, PositiveValueAtomless (Γ t)) (hatom : ∀ t, PositiveVisibleAtomless (Γ t))
    (hinactive : ∀ t, InactiveAbstain (Γ t))
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF : ∀ t, (Γ t).F = F) {g : ℝ} (hg : ∀ t, (Γ t).g = g)
    {ρ : ℝ} (hρ : Tendsto (fun t => (C t : ℝ)/(N t+1)) atTop (𝓝 ρ))
    (hρb : ρ ∈ Ioo (0:ℝ) (F.real (Ioi g))) {Gorig : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => bidLaw (Γ t)) atTop (𝓝 Gorig))
    (a : ℕ → ℝ) (ha : ∀ t, 0 < a t) (ha0 : Tendsto a atTop (𝓝 0))
    {K : Set ℝ} (hK : IsCompact K) (hKpos : K ⊆ Ioi 0) {v : ℝ} (hv : 0 < v) :
    Tendsto (fun t => ((Γ t).F ⊗ₘ (Γ t).σ)
      {z | v ≤ z.1-g ∧ effectiveBid z.2/a t ∈ K}) atTop (𝓝 0) := by
  have hNpos t : 0 < N t := by have := hc t; have := hcm t; omega
  have hM : Tendsto (fun t => N t+1) atTop atTop := (tendsto_add_atTop_nat 1).comp hN
  have hρM : Tendsto (fun t => (C t:ℝ)/((N t+1:ℕ):ℝ)) atTop (𝓝 ρ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hρ
  have hroot := payOnce_inactive_positive_capacity_root Γ hk hc hcm hM hA hG hu B hB hsym hvalue hatom hinactive
    F hF hg hρM hρb hweak
  obtain ⟨u, hu0, hmass⟩ := KernelDemand.exists_positive_tail_gt_capacity (by omega : 2 ≤ k+1)
    Gorig hroot.1
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
  have hh := inactive_vanishing_window_mass_zero Γ hk hNpos hN hc hcm
    hA hG hu B hB hsym hvalue hatom hinactive hweak hu0 hρb.1 hmass hcap a ha ha0 hK hKpos hv
  simpa only [hg] using hh

end FCAppendix.Bayes
