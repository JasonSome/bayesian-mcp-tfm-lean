import FCAppendix.Exclusive.SourceLowTypeOptimal
import FCAppendix.Exclusive.SourceLowTypeNeighborhood

noncomputable section
namespace FCAppendix.Bayes.ExclusiveSource
open MeasureTheory ProbabilityTheory Game Exclusive ExclusiveNarrow Set Filter

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem demand_scale (n : ℕ) {scale : ℝ} (hscale : scale ≠ 0) (b price : ℝ) :
    demand n (scale*b) (scale*price) = demand n b price := by
  have he : (scale*price)/(scale*b) = price/b := by field_simp
  simp only [demand,he]

theorem scaled_good_marginal_lower (hn : 2 ≤ n)
    {scaleLo scale t q tolerance b lam : ℝ}
    (hscaleLo : 0 < scaleLo) (hscale : scaleLo ≤ scale)
    (ht : 0 < t) (htol : 0 ≤ tolerance) (hlam : 0 ≤ lam)
    (hb : scale*t ≤ b) (hprice : lam ≤ scale*q+tolerance) :
    demand n t (q+tolerance/scaleLo) ≤ demand n b lam := by
  have hs : 0 < scale := hscaleLo.trans_le hscale
  have hsT : 0 < scale*t := mul_pos hs ht
  have hscaledTol : tolerance ≤ scale*(tolerance/scaleLo) := by
    have hh := mul_le_mul_of_nonneg_right hscale (div_nonneg htol hscaleLo.le)
    have he : scaleLo*(tolerance/scaleLo)=tolerance := by field_simp
    rwa [he] at hh
  have hupper : lam ≤ scale*(q+tolerance/scaleLo) := by nlinarith
  calc
    demand n t (q+tolerance/scaleLo) =
        demand n (scale*t) (scale*(q+tolerance/scaleLo)) :=
      (demand_scale n hs.ne' t (q+tolerance/scaleLo)).symm
    _ ≤ demand n (scale*t) lam := demand_antitone n hn hsT hlam hupper
    _ ≤ demand n b lam := demand_mono_bid n hn hsT hb hlam

theorem source_actual_large_bid_negative_uniform (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hn : 2 ≤ n) (hc : 0 < c)
    (fallback : LocalPolicy m c Seed)
    (hfallback : Measurable (fun p : LocalList m × Seed => (fallback p.1 p.2).val))
    (hcanonical : ∀ ℓ, FiniteLaw.ofMeasure Γ.seedLaw (fun s => (fallback ℓ s).val)
      (hfallback.comp (measurable_const.prodMk measurable_id)) =
        canonicalLottery n hn c (listBids ℓ))
    {scaleLo scale t q tolerance lowUpper : ℝ}
    (hscaleLo : 0 < scaleLo) (hscale : scaleLo ≤ scale) (ht : 0 < t) (hq : 0 < q)
    (htol : 0 < tolerance) (hsep : q+tolerance/scaleLo < t)
    (hL : 0 ≤ lowUpper)
    (hlow : lowUpper < min (scaleLo*t) (scaleLo*q-tolerance))
    (hpolicy : ∀ j ℓ s, (Γ.policy j ℓ s).val =
      (Marker.sourceContinuation hm hn hc (scale*t) fallback ℓ s).val)
    (tariff : UserTariff) (ha : tariff.Allowed) (i : Fin m)
    (hd : ∀ᵐ d ∂userProfileLaw Γ, HighRivals (scale*t) i d)
    (v : ℝ) (a : JointAction n) (hk : 1 ≤ a.routeCount) (hb : scale*t ≤ a.bid)
    (hv : v-Γ.g ≤ lowUpper)
    (hbad : (userProfileLaw Γ).real
      {d | focalPrice n hn c i a.bid d ∉ Icc (scale*q-tolerance) (scale*q+tolerance)} <
      (demand n t (q+tolerance/scaleLo)*(min (scaleLo*t) (scaleLo*q-tolerance)-lowUpper))/
        (lowUpper+demand n t (q+tolerance/scaleLo)*
          (min (scaleLo*t) (scaleLo*q-tolerance)-lowUpper))) :
    exclusiveTariffPayoff Γ tariff i v a < 0 := by
  let pmin := demand n t (q+tolerance/scaleLo)
  let floor := min (scaleLo*t) (scaleLo*q-tolerance)
  have hs : 0 < scale := hscaleLo.trans_le hscale
  have hb0 : 0 < a.bid := (mul_pos hs ht).trans_le hb
  have hqTol : 0 < q+tolerance/scaleLo := by positivity
  have hpmin : 0 < pmin := (demand_pos_iff n hn ht hqTol.le).mpr hsep
  have hfloor : lowUpper < floor := hlow
  have hmargin : 0 < pmin*(floor-lowUpper) := mul_pos hpmin (sub_pos.mpr hfloor)
  let E := {d : UserProfile m n | focalPrice n hn c i a.bid d ∈
    Icc (scale*q-tolerance) (scale*q+tolerance)}
  have hE : MeasurableSet E := (measurable_focalPrice hn hc i a.bid) measurableSet_Icc
  rw [source_actual_payoff_large_bid Γ hm hn hc (scale*t) fallback hfallback hcanonical
    hpolicy tariff i hd v a hb]
  apply LowType.integral_negative_of_good_event (userProfileLaw Γ) E hE _
    (LowType.integrable_binomialPayoff (userProfileLaw Γ) tariff Γ.G a.routeCount
      Γ.g v a.bid (focalMarginal n hn c i a.bid) (measurable_focalMarginal hn hc i a.bid)
      (fun d => focalMarginal_bounds hn i a.bid d)) hL hmargin
  · exact Eventually.of_forall fun d => LowType.payoff_le_low_upper tariff ha Γ.G
      a.routeCount_le Γ.g_nonneg a.bid_nonneg (focalMarginal_bounds hn i a.bid d).1
      (focalMarginal_bounds hn i a.bid d).2 hL hv
  · apply Eventually.of_forall
    intro d hdE
    let lam := focalPrice n hn c i a.bid d
    have hlam0 : 0 < lam := by
      have hfloor0 : 0 < scaleLo*q-tolerance :=
        (hL.trans_lt hlow).trans_le (min_le_right _ _)
      have hscQ := mul_le_mul_of_nonneg_right hscale hq.le
      have := hdE.1
      dsimp only [lam]
      linarith
    have hsepScale : scale*q+tolerance < scale*t := by
      have hmul := mul_lt_mul_of_pos_left hsep hscaleLo
      have he : scaleLo*(q+tolerance/scaleLo)=scaleLo*q+tolerance := by field_simp
      rw [he] at hmul
      have hh := mul_le_mul_of_nonneg_right hscale (sub_pos.mpr
        ((lt_add_of_pos_right q (div_pos htol hscaleLo)).trans hsep)).le
      nlinarith
    have hprice : a.bid*(1-focalMarginal n hn c i a.bid d)^(n-1)=lam := by
      rw [focalMarginal_eq_demand hn i hb0,demand_receipt n hn hb0 hlam0,
        min_eq_right ((hdE.2.trans hsepScale.le).trans hb)]
    have hpm : pmin ≤ focalMarginal n hn c i a.bid d := by
      rw [focalMarginal_eq_demand hn i hb0]
      exact scaled_good_marginal_lower hn hscaleLo hscale ht htol.le hlam0.le hb hdE.2
    have hfloorPrice : scaleLo*q-tolerance ≤ lam := by
      have hscQ := mul_le_mul_of_nonneg_right hscale hq.le
      have := hdE.1
      dsimp only [lam]
      linarith
    have hfloorBid : scaleLo*t ≤ a.bid :=
      (mul_le_mul_of_nonneg_right hscale ht.le).trans hb
    simpa only [neg_mul] using LowType.good_event_payoff_upper tariff ha Γ.G hk
      a.routeCount_le Γ.g_nonneg (focalMarginal_bounds hn i a.bid d).1
      (focalMarginal_bounds hn i a.bid d).2 a.bid_nonneg hprice hfloorPrice
      hfloorBid hv hlow hpm
  · exact hbad

end FCAppendix.Bayes.ExclusiveSource
