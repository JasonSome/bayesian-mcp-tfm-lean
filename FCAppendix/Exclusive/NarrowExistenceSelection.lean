import FCAppendix.Exclusive.NarrowExistenceWideActions
import FCAppendix.Exclusive.NarrowGlobalHighMarket

noncomputable section
namespace FCAppendix.Exclusive.Narrow.Existence
open MeasureTheory ProbabilityTheory Set Filter Topology
open Global

structure NarrowExistenceParameters (d : ℕ) (G : Schedule (d+1)) (h : unitInterval) (rho g : ℝ) where
  wide : UniformFiniteConstants d G h rho
  candidate : UniformFiniteConstants d G h rho
  H : ℝ
  gap : ℝ
  M0 : ℕ
  H_pos : 0 < H
  gap_pos : 0 < gap
  M0_pos : 0 < M0
  delta_le : candidate.delta ≤ wide.delta
  eps_le : candidate.eps ≤ wide.eps
  eta_le : candidate.eta ≤ wide.eta
  candidate_threshold : candidate.M0 ≤ M0
  wide_threshold : wide.M0 ≤ M0
  base : g/H ∈ Icc (0:ℝ) candidate.eps
  wide_bad : ∀ {m : ℕ}, M0 ≤ m+1 →
    ∀ (nu : Measure (ValueBand candidate.eps)) [IsProbabilityMeasure nu],
      (iidRivalLaw m h nu).real (goodCount m h wide.eta)ᶜ ≤ wide.kappa/(48*wide.B)
  global : ∀ (dhd : 1 ≤ d) (m c : ℕ), M0 ≤ m+1 →
    |(c:ℝ)/((m:ℝ)+1)-rho| < candidate.eta →
    ∀ (nu : Measure (ValueBand candidate.eps)) [IsProbabilityMeasure nu]
      (beta : ValueBand candidate.eps → ℝ), Measurable beta →
      (∀ u, beta u ∈ Icc (-candidate.delta) candidate.delta) →
    ∀ a : UserTariff, a.Allowed → ∀ v : ValueBand candidate.eps,
      let scale := referenceBidScale d a (rho/(h:ℝ))
      let payoff := fun k b => ∫ omega, LowType.binomialPayoff a G k (g/H) (v:ℝ) b
        (activeDemand (d+1) b (sampledPrice d dhd c scale beta b omega)) ∂iidRivalLaw m h nu
      gap ≤ payoff (d+1) scale ∧ ∀ k : ℕ, k ≤ d+1 → ∀ b : ℝ, 0 ≤ b →
        (k=d+1 → b ∉ Icc (scale*Real.exp (-wide.delta)) (scale*Real.exp wide.delta)) →
        payoff k b+gap ≤ payoff (d+1) scale

theorem exists_narrow_existence_parameters_bounded (d : ℕ) (hd : 1 ≤ d)
    (G : Schedule (d+1)) (h : unitInterval) (rho g : ℝ)
    (hh : 0 < (h:ℝ)) (hrho : 0 < rho) (hrh : rho < (h:ℝ)) (hg : 0 ≤ g)
    (deltaCap epsCap etaCap : ℝ) (hdeltaCap : 0 < deltaCap)
    (hepsCap : 0 < epsCap) (hetaCap : 0 < etaCap) :
    ∃ Q : NarrowExistenceParameters d G h rho g,
      Q.candidate.delta ≤ deltaCap ∧ Q.candidate.eps ≤ epsCap ∧ Q.candidate.eta ≤ etaCap := by
  obtain ⟨W⟩ := exists_uniform_finite_constants d hd G h rho hh h.property.2 hrho hrh
  have hp0 : 0 < rho/(h:ℝ) := div_pos hrho hh
  have hp1 : rho/(h:ℝ) < 1 := (div_lt_one hh).mpr hrh
  obtain ⟨scaleLo,cap,hlo,_hlocap,hscales⟩ :=
    Bayes.ExclusiveSource.exists_referenceBidScale_bounds d hd (rho/(h:ℝ)) hp0.le hp1
  have hscales' : ∀ a : UserTariff, a.Allowed →
      referenceCentralBid d a (rho/(h:ℝ)) ∈ Icc scaleLo cap := by
    simpa only [referenceCentralBid_eq_referenceBidScale] using hscales
  obtain ⟨dg,eg,etag,radius,gap,Mg,hdg,_hdgw,heg,_hegHalf,hetag,_hradius,hgap,_hMg,
    _hrawRadius,hglobal⟩ := exists_high_market_parameters d hd h rho W.delta scaleLo cap
      hh hrho hrh W.delta_pos hlo hscales'
  obtain ⟨U,hUd,hUe,hUt⟩ := exists_uniform_finite_constants_bounded d hd G h rho
    hh h.property.2 hrho hrh (min (min W.delta dg) deltaCap) (min (min W.eps eg) epsCap)
    (min (min W.eta etag) etaCap)
      (lt_min (lt_min W.delta_pos hdg) hdeltaCap) (lt_min (lt_min W.eps_pos heg) hepsCap)
      (lt_min (lt_min W.eta_pos hetag) hetaCap)
  have hUWd := hUd.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hUWε := hUe.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hUWη := hUt.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hUgd := hUd.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hUgε := hUe.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hUgη := hUt.trans ((min_le_left _ _).trans (min_le_right _ _))
  let H := g/U.eps+1
  have hH : 0 < H := by have hf := div_nonneg hg U.eps_pos.le; dsimp [H]; linarith
  have hbase : g/H ∈ Icc (0:ℝ) U.eps := by
    constructor
    · exact div_nonneg hg hH.le
    · apply (div_le_iff₀ hH).mpr
      have he : U.eps*H = g+U.eps := by dsimp [H]; field_simp [U.eps_pos.ne']
      rw [he]
      linarith [U.eps_pos]
  obtain ⟨Mw,hMw⟩ := W.exists_wide_action_count_threshold (V := ValueBand U.eps) h.property
  let M0 := max U.M0 (max W.M0 (max Mg (Mw+1)))
  have hMU : U.M0 ≤ M0 := le_max_left _ _
  have hMW : W.M0 ≤ M0 := (le_max_left _ _).trans (le_max_right _ _)
  have hMg : Mg ≤ M0 := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hMwide : Mw+1 ≤ M0 := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨{
    wide := W
    candidate := U
    H := H
    gap := gap
    M0 := M0
    H_pos := hH
    gap_pos := hgap
    M0_pos := U.M0_pos.trans_le hMU
    delta_le := hUWd
    eps_le := hUWε
    eta_le := hUWη
    candidate_threshold := hMU
    wide_threshold := hMW
    base := hbase
    wide_bad := ?_
    global := ?_ },?_,?_,?_⟩
  · intro m hm nu _
    apply hMw m (by omega) nu
  · intro dhd m c hm hC nu _ beta hbeta hband a ha v
    have hbg : ∀ u, beta u ∈ Icc (-dg) dg := fun u =>
      ⟨by linarith [(hband u).1], (hband u).2.trans hUgd⟩
    have hvg : (v:ℝ) ∈ Icc (1-eg) (1+eg) :=
      ⟨by linarith [v.property.1], by linarith [v.property.2]⟩
    have hhg := hglobal m c (hMg.trans hm) (hC.trans_le hUgη) nu beta hbeta hbg a ha G
      (g/H) (v:ℝ) ⟨hbase.1,hbase.2.trans hUgε⟩ hvg
    simpa only [referenceCentralBid_eq_referenceBidScale] using hhg
  · exact hUd.trans (min_le_right _ _)
  · exact hUe.trans (min_le_right _ _)
  · exact hUt.trans (min_le_right _ _)

theorem exists_narrow_existence_parameters (d : ℕ) (hd : 1 ≤ d)
    (G : Schedule (d+1)) (h : unitInterval) (rho g : ℝ)
    (hh : 0 < (h:ℝ)) (hrho : 0 < rho) (hrh : rho < (h:ℝ)) (hg : 0 ≤ g) :
    Nonempty (NarrowExistenceParameters d G h rho g) := by
  obtain ⟨Q,_⟩ := exists_narrow_existence_parameters_bounded d hd G h rho g hh hrho hrh hg
    1 1 1 (by norm_num) (by norm_num) (by norm_num)
  exact ⟨Q⟩

end FCAppendix.Exclusive.Narrow.Existence
