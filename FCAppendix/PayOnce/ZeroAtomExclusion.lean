import FCAppendix.PayOnce.GoodQuantileSelection
import FCAppendix.PayOnce.ActualPureComparisons
import FCAppendix.PayOnce.VanishingQuantiles
import FCAppendix.PayOnce.VanishingBidBlock
import FCAppendix.PayOnce.SeparatedQuantileContradiction

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open PayOnce PayOnce.AnalyticalKernel PayOnce.CompactifiedBidLaws
variable {N C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_limit_no_zero_atom
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
    (hweak : Tendsto (fun t => bidLaw (Γ t)) atTop (𝓝 Gorig)) :
    (Gorig : Measure ENNReal) {0} = 0 := by
  by_contra hzero
  have hNpos t : 0 < N t := by have := hc t; have := hcm t; omega
  have hM : Tendsto (fun t => N t+1) atTop atTop := (tendsto_add_atTop_nat 1).comp hN
  have hρM : Tendsto (fun t => (C t:ℝ)/((N t+1:ℕ):ℝ)) atTop (𝓝 ρ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hρ
  have hroot := payOnce_positive_capacity_root Γ hk hc hcm hM hA hG hu B hB hsym hatom
    F hF hg hactive hρM hρb hweak
  have hvalue t : PositiveValueAtomless (Γ t) := by
    intro v _
    rw [hF t]
    exact measure_singleton v
  have hact t : ∀ᵐ v ∂(Γ t).F, (Γ t).g < v := by simpa only [hF t, hg t] using hactive
  choose bid hmono hmeas hbound hraw heq T hTa hT using fun t =>
    exists_monotone_analytical_IC (Γ t) hk (hc t) (hcm t) (hA t) (hG t)
      (hu t) (B t) (hB t) (hsym t) (hvalue t) (hact t)
  have hgood : ∀ᵐ v ∂F, ∀ t, v ∈ T t := ae_all_iff.mpr fun t => by
    simpa only [hF t] using hTa t
  let q := (Gorig : Measure ENNReal).real ({0}ᶜ)
  have hq0 : 0 ≤ q := measureReal_nonneg
  have hq1 : q < 1 := by
    have hp : 0 < (Gorig : Measure ENNReal).real {0} :=
      ENNReal.toReal_pos hzero (measure_ne_top _ _)
    dsimp only [q]
    rw [probReal_compl_eq_one_sub (measurableSet_singleton 0)]
    linarith
  obtain ⟨a, x, y, b, haG, hxG, hyG, hbG, hga, hax, hxy, hyb,
      haxMass, hxyMass, hybMass, hleft, hqb⟩ :=
    GoodQuantileSelection.exists_four_good_quantiles F hactive hq0 hq1 (fun v => ∀ t, v ∈ T t) hgood
  have hfull t := ae_full_routes_positive_bids_of_active (Γ t) (hc t) (hcm t) (hA t) (hG t)
    (hu t) (B t) (hB t) (hsym t) (hvalue t) (hact t)
  have hmap t : (bidLaw (Γ t) : Measure ENNReal) =
      F.map (fun v => ENNReal.ofReal (bid t v)) := by
    rw [compactifiedBidLaw_eq_map_realBidLaw (Γ t) (by omega) ((hfull t).mono fun _ hz => hz.2),
      hraw t, hF t, Measure.map_map ENNReal.measurable_ofReal (hmeas t)]
    rfl
  have hbTail : (Gorig : Measure ENNReal) ({0}ᶜ) < F (Ici b) := by
    apply (ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
    exact hqb.trans_le (measureReal_mono Ioi_subset_Ici_self)
  have hbZero := VanishingBidIC.tendsto_bid_zero_at_lower_quantile F bid hmono
    (fun t v => (hbound t v).1) (fun t => bidLaw (Γ t)) Gorig hmap hweak hbTail
  have hxZero : Tendsto (fun t => bid t x) atTop (𝓝 0) :=
    squeeze_zero (fun t => (hbound t x).1) (fun t => hmono t (hxy.trans hyb).le) hbZero
  have hsepX := payOnce_vanishing_bid_ratio_zero Γ hk hc hcm hN hA hG hu B hB hsym hatom
    F hF hg hactive hρ hρb hweak bid hmono hmeas heq hga (fun t => (hbound t a).1)
    (fun t => (hT t x (hxG t)).1) haxMass hxZero
  have hsepY := payOnce_vanishing_bid_ratio_zero Γ hk hc hcm hN hA hG hu B hB hsym hatom
    F hF hg hactive hρ hρb hweak bid hmono hmeas heq (hga.trans (hax.trans hxy))
    (fun t => (hbound t y).1) (fun t => (hT t b (hbG t)).1) hybMass hbZero
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
  have hpos t : ∀ᵐ v ∂F, 0 < bid t v := by
    have ht : ∀ᵐ v ∂F, v ∈ T t := by simpa only [hF t] using hTa t
    exact ht.mono fun v hv => (hT t v hv).1
  have hmean : ρ < F.real (Ioi y) := hroot.1.trans
    (hqb.trans_le (measureReal_mono (Ioi_subset_Ioi hyb.le)))
  have hCov := QuantileTailComparison.coverage_ratio_zero_of_separated_quantiles F N hNpos hN
    (by omega : 2 ≤ k+1) (fun t => by simpa using (hcm t).le) bid hmeas hmono hpos
    (fun t => bid t a) (fun t => bid t b) (fun t => (hT t a (haG t)).1)
    (fun t => (hT t b (hbG t)).1) hxy (fun t => (hT t x (hxG t)).1)
    hxyMass hleft hsepX hsepY hρb.1 hmean hcap
  apply QuantileTailComparison.not_coverage_ratio_zero_of_vanishing_IC (sub_pos.mpr hga)
    (fun t => integral_nonneg fun ω => (success_allocation_bounds (by omega) (by simpa using (hcm t).le)
      ω (bid t a)).1) (fun t => (hbound t a).1) hCov.1 hbZero _ hCov.2
  intro t
  simpa only [hF t, hg t, coverage] using (hT t a (haG t)).2 b (hbG t)

end FCAppendix.Bayes
