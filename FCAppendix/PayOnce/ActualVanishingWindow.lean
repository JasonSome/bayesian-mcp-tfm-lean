import FCAppendix.PayOnce.ActualScaledComparisons
import FCAppendix.PayOnce.VanishingWindow
import FCAppendix.PayOnce.PositiveRoot

namespace FCAppendix.PayOnce.KernelDemand
open MeasureTheory ProbabilityTheory Set Filter Topology CommonList KernelLawConvergence

theorem demand_le_tail_mass {n : ℕ} (hn : 2 ≤ n) (G : ProbabilityMeasure ENNReal)
    {L : ℝ} (hL : 0 < L) :
    demand n (G : Measure ENNReal) L ≤ (G : Measure ENNReal).real (Ioi (ENNReal.ofReal L)) := by
  have hh := integral_mono
    (CompactKernelRareSuccess.integrable_compactKernel hn (G : Measure ENNReal) hL)
    ((integrable_const (1:ℝ)).indicator measurableSet_Ioi) (fun b => by
      by_cases hb : b ∈ Ioi (ENNReal.ofReal L)
      · rw [indicator_of_mem hb]
        exact (compactKernel_bounds hn hL b).2
      · have hle : b ≤ ENNReal.ofReal L := le_of_not_gt hb
        have htop : b ≠ ⊤ := ne_of_lt (hle.trans_lt ENNReal.ofReal_lt_top)
        have hreal : b.toReal ≤ L := by
          simpa only [ENNReal.toReal_ofReal hL.le] using
            ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
        rw [indicator_of_notMem hb]
        simp only [compactKernel, if_neg htop, kernel_of_le n hreal, le_refl])
  simpa only [integral_indicator measurableSet_Ioi, setIntegral_const, smul_eq_mul,
    mul_one, demand] using hh

theorem exists_positive_tail_gt_capacity {n : ℕ} (hn : 2 ≤ n) (G : ProbabilityMeasure ENNReal)
    {ρ : ℝ} (hmass : ρ < (G : Measure ENNReal).real ({0}ᶜ)) :
    ∃ u : ℝ, 0 < u ∧ ρ < (G : Measure ENNReal).real (Ioi (ENNReal.ofReal u)) := by
  let L := fun m : ℕ => 1 / ((m:ℝ)+1)
  have hL m : 0 < L m := by dsimp only [L]; positivity
  have ht := tendsto_demand_zero hn (G : Measure ENNReal) hL
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨m, hm⟩ := (ht.eventually_const_lt hmass).exists
  exact ⟨L m, hL m, hm.trans_le (demand_le_tail_mass hn G (hL m))⟩

end FCAppendix.PayOnce.KernelDemand

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open PayOnce PayOnce.AnalyticalKernel PayOnce.AnalyticalRareSuccess PayOnce.CompactifiedBidLaws
variable {N C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem actual_vanishing_window_mass_zero
    (Γ : ∀ t, FiniteGame (N t+1) (k+1) (C t) Seed)
    (hk : 1 ≤ k) (hNpos : ∀ t, 0 < N t) (hN : Tendsto N atTop atTop)
    (hcm : ∀ t, C t ≤ N t+1)
    (hA : ∀ t, (Γ t).A = Schedule.once (k+1)) (hG : ∀ t, (Γ t).G = Schedule.once (k+1))
    (hu : ∀ t, UsersOptimal (Γ t)) (B : ∀ t, PosteriorSystem (Γ t))
    (hB : ∀ t, PosteriorProposerOptimalAE (Γ t) (B t))
    (hsym : ∀ t, SymmetricProposersOnPath (Γ t)) (hatom : ∀ t, PositiveVisibleAtomless (Γ t))
    (hroute : ∀ t, ∀ᵐ z ∂((Γ t).F ⊗ₘ (Γ t).σ), z.2.routeCount = k+1)
    (hbid : ∀ t, ∀ᵐ z ∂((Γ t).F ⊗ₘ (Γ t).σ), 0 < z.2.bid)
    {Gorig : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => bidLaw (Γ t)) atTop (𝓝 Gorig))
    {u ρ : ℝ} (hu0 : 0 < u) (hρ0 : 0 < ρ)
    (hmass : ρ < (Gorig : Measure ENNReal).real (Ioi (ENNReal.ofReal u)))
    (hcapacity : Tendsto (fun t => (C t : ℝ) / N t) atTop (𝓝 ρ))
    (a : ℕ → ℝ) (ha : ∀ t, 0 < a t) (ha0 : Tendsto a atTop (𝓝 0))
    {K : Set ℝ} (hK : IsCompact K) (hKpos : K ⊆ Ioi 0) {v : ℝ} (hv : 0 < v) :
    Tendsto (fun t => ((Γ t).F ⊗ₘ (Γ t).σ)
      {z | v ≤ z.1-(Γ t).g ∧ z.2.bid/a t ∈ K}) atTop (𝓝 0) := by
  let G : ℕ → ProbabilityMeasure ℝ := fun t => ⟨realBidLaw (Γ t), inferInstance⟩
  have hraw t : scaledLaw (G t) 1 = bidLaw (Γ t) := by
    apply Subtype.ext
    change (realBidLaw (Γ t)).map (fun b : ℝ => ENNReal.ofReal (b/1)) = _
    simp only [div_one]
    exact (compactifiedBidLaw_eq_map_realBidLaw (Γ t) (by omega) (hroute t)).symm
  have hweakRaw : Tendsto (fun t => scaledLaw (G t) 1) atTop (𝓝 Gorig) := by
    simpa only [hraw] using hweak
  choose T hTm hTp hTae hcompare using fun t =>
    exists_ae_scaled_analytical_comparisons (Γ t) hk (hcm t) (hA t) (hG t)
      (hu t) (B t) (hB t) (hsym t) (hatom t) (hroute t) (hbid t) ⟨0, by omega⟩ (a t) (ha t)
  exact tendsto_vanishing_window_mass_zero N hNpos hN (by omega)
    (fun t => (Γ t).F ⊗ₘ (Γ t).σ) (fun _ z => z.2.bid) (fun t z => z.1-(Γ t).g)
    (fun _ => (measurable_bid (k+1)).comp measurable_snd) G
    (fun t => realBidLaw_eq_action_map (Γ t)) hbid a ha ha0 hweakRaw hu0 hρ0 hmass
    (fun t => by simpa using hcm t) hcapacity T hTp
    (fun t => (hcompare t).mono fun _ hz => hz.2) hK hKpos hv

theorem payOnce_vanishing_window_mass_zero
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
    (hρb : ρ ∈ Ioo (0:ℝ) 1) {Gorig : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => bidLaw (Γ t)) atTop (𝓝 Gorig))
    (a : ℕ → ℝ) (ha : ∀ t, 0 < a t) (ha0 : Tendsto a atTop (𝓝 0))
    {K : Set ℝ} (hK : IsCompact K) (hKpos : K ⊆ Ioi 0) {v : ℝ} (hv : 0 < v) :
    Tendsto (fun t => ((Γ t).F ⊗ₘ (Γ t).σ)
      {z | v ≤ z.1-g ∧ z.2.bid/a t ∈ K}) atTop (𝓝 0) := by
  have hNpos t : 0 < N t := by have := hc t; have := hcm t; omega
  have hM : Tendsto (fun t => N t+1) atTop atTop := (tendsto_add_atTop_nat 1).comp hN
  have hρM : Tendsto (fun t => (C t:ℝ)/((N t+1:ℕ):ℝ)) atTop (𝓝 ρ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hρ
  have hroot := payOnce_positive_capacity_root Γ hk hc hcm hM hA hG hu B hB hsym hatom
    F hF hg hactive hρM hρb hweak
  obtain ⟨u, hu0, hmass⟩ := KernelDemand.exists_positive_tail_gt_capacity (by omega : 2 ≤ k+1)
    Gorig hroot.1
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
  have hh := actual_vanishing_window_mass_zero Γ hk hNpos hN (fun t => (hcm t).le)
    hA hG hu B hB hsym hatom (fun t => (hfull t).mono fun _ hz => hz.2)
    (fun t => (hfull t).mono fun _ hz => hz.1) hweak hu0 hρb.1 hmass hcap a ha ha0 hK hKpos hv
  simpa only [hg] using hh

end FCAppendix.Bayes
