import FCAppendix.Exclusive.SourceLowTypeUniform
import FCAppendix.Exclusive.SourceLowTypeActualBand

noncomputable section
namespace FCAppendix.Bayes.ExclusiveSource
open MeasureTheory ProbabilityTheory Game Exclusive ExclusiveNarrow Set Filter
open Exclusive.Narrow.Existence ExclusiveConstruction

variable {Seed V : Type*} [MeasurableSpace Seed] [MeasurableSpace V]

theorem exists_source_low_market_parameters (d : ℕ) (hd : 1 ≤ d)
    (h : unitInterval) (rho scaleLo cap t tolerance lowUpper deltaCap : ℝ)
    (hh : 0 < (h : ℝ)) (hrho : 0 < rho) (hrh : rho < (h : ℝ))
    (hscaleLo : 0 < scaleLo) (hcap : 0 < cap)
    (htol : 0 < tolerance) (hL : 0 ≤ lowUpper)
    (hsep : (1-rho/(h : ℝ))^d+tolerance/scaleLo < t)
    (hlow : lowUpper < min (scaleLo*t) (scaleLo*(1-rho/(h : ℝ))^d-tolerance))
    (hdeltaCap : 0 < deltaCap) (hmarkerFloor : t ≤ Real.exp (-deltaCap))
    (hmarkerThreshold : t ≤ Real.exp (-deltaCap)*(1-1/((d+1 : ℕ):ℝ))^d) :
    ∃ delta eta : ℝ, ∃ M0 : ℕ, 0 < delta ∧ delta ≤ deltaCap ∧ 0 < eta ∧
      ∀ (m c : ℕ), M0 ≤ m → ∀ hc : 0 < c,
      |(c : ℝ)/((m : ℝ)+1)-rho| < eta →
      ∀ (Γ : FiniteGame (m+1) (d+1) c Seed) (scale : ℝ),
      scale ∈ Icc scaleLo cap →
      ∀ (fallback : LocalPolicy (m+1) c Seed)
      (hfallback : Measurable (fun p : LocalList (m+1) × Seed => (fallback p.1 p.2).val)),
      (∀ ℓ, FiniteLaw.ofMeasure Γ.seedLaw (fun s => (fallback ℓ s).val)
        (hfallback.comp (measurable_const.prodMk measurable_id)) =
          canonicalLottery (d+1) (by omega) c (listBids ℓ)) →
      (∀ j ℓ s, (Γ.policy j ℓ s).val =
        (Marker.sourceContinuation (m := m+1) (n := d+1) (c := c)
          (by omega) (by omega) hc (scale*t) fallback ℓ s).val) →
      ∀ (V : Type*) [MeasurableSpace V] (i : Fin (m+1)) (nu : Measure V) [IsProbabilityMeasure nu]
      [NullSingletonClass nu] [MeasurableEq V] (highBid : V → ℝ),
      Measurable highBid →
      (∀ v, highBid v ∈ Icc (scale*Real.exp (-delta)) (scale*Real.exp delta)) →
      Function.Injective highBid →
      (userProfileLaw Γ).map (fun x j => (x (i.succAbove j)).1.2) =
        (iidRivalLaw m h nu).map (fun omega j => flagAction (d+1) highBid (omega j)) →
      ∀ (tariff : UserTariff), tariff.Allowed → ∀ v : ℝ, v-Γ.g ≤ lowUpper →
        ExclusiveTariffBestResponse Γ tariff i v (Interim.abstain (d+1)) := by
  let q := (1-rho/(h : ℝ))^d
  have hq0 : 0 < 1-rho/(h : ℝ) := by
    have hh' := (div_lt_one hh).mpr hrh
    linarith
  have hq : 0 < q := pow_pos hq0 d
  have ht : 0 < t := by
    have hp : 0 < q+tolerance/scaleLo := by positivity
    exact hp.trans hsep
  let pmin := demand (d+1) t (q+tolerance/scaleLo)
  let D := pmin*(min (scaleLo*t) (scaleLo*q-tolerance)-lowUpper)
  have hpmin : 0 < pmin := (demand_pos_iff (d+1) (by omega) ht
    (by positivity : 0 ≤ q+tolerance/scaleLo)).mpr hsep
  have hD : 0 < D := mul_pos hpmin (sub_pos.mpr hlow)
  have hprob : 0 < D/(lowUpper+D) := div_pos hD (by linarith)
  obtain ⟨delta,eta,Mprice,hdelta,hdeltaCap',heta,_,hprice⟩ :=
    exists_actual_price_neighborhood (Seed := Seed) d hd (h : ℝ) rho cap tolerance deltaCap
      hh hrho hrh hcap htol hdeltaCap
  obtain ⟨Mcount,hcount⟩ := exists_actual_count_bad_probability_bound (Seed := Seed)
    h heta hprob
  refine ⟨delta,eta,max Mprice Mcount,hdelta,hdeltaCap',heta,?_⟩
  intro m c hm hc hcapacity Γ scale hscale fallback hfallback hcanonical hpolicy
    V _ i nu _ _ _ highBid hmeas hband hinj hActions tariff ha v hv
  have hs : 0 < scale := hscaleLo.trans_le hscale.1
  have hhigh : 0 < scale*Real.exp (-delta) := mul_pos hs (Real.exp_pos _)
  have hbandActual := ae_actual_bandRivals Γ i h nu highBid hmeas hhigh hband hActions
  have hdistinct := ae_actual_activeRivals_distinct Γ i h nu highBid hmeas
    (fun u => hhigh.trans_le (hband u).1) hinj hActions
  have hexp : Real.exp (-deltaCap) ≤ Real.exp (-delta) :=
    Real.exp_le_exp.mpr (neg_le_neg hdeltaCap')
  have hcutFloor : scale*t ≤ scale*Real.exp (-delta) :=
    mul_le_mul_of_nonneg_left (hmarkerFloor.trans hexp) hs.le
  have hcrit : 0 ≤ (1-1/((d+1 : ℕ):ℝ))^d := by
    have hnR : (1 : ℝ) < (d+1 : ℕ) := by exact_mod_cast (show 1 < d+1 by omega)
    have := (div_lt_one (by positivity : (0 : ℝ) < (d+1 : ℕ))).mpr hnR
    exact pow_nonneg (by linarith) _
  have hcutThreshold : scale*t ≤
      (scale*Real.exp (-delta))*(1-1/((d+1 : ℕ):ℝ))^d := by
    have hh := hmarkerThreshold.trans (mul_le_mul_of_nonneg_right hexp hcrit)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh hs.le
  have hgood : ∀ᵐ x ∂userProfileLaw Γ,
      HighRivals (scale*Real.exp (-delta)) i x ∧
      Set.InjOn (fun j => (x j).1.2.bid) (activeRivals i x) := by
    filter_upwards [hbandActual,hdistinct] with x hx hdx
    exact ⟨hx.highRivals,hdx⟩
  intro act
  rw [exclusiveTariffPayoff_abstain]
  by_cases hk : act.routeCount = 0
  · exact (exclusiveTariffPayoff_zero_routes Γ tariff i v act hk).le
  · by_cases hb : act.bid < scale*t
    · exact (source_actual_small_bid_zero Γ (by omega) (by omega) hc (scale*t)
        fallback hfallback hcanonical hpolicy tariff i hhigh hcutFloor
        (by simpa only [Nat.add_sub_cancel] using hcutThreshold) hgood v act hb).le
    · have hR : ∀ᵐ x ∂userProfileLaw Γ, HighRivals (scale*t) i x := hgood.mono fun x hx => by
        intro j hj
        rcases hx.1 j hj with hz | ⟨hr,hbid⟩
        · exact Or.inl hz
        · exact Or.inr ⟨hr,hcutFloor.trans hbid⟩
      apply le_of_lt
      apply source_actual_large_bid_negative_uniform Γ (by omega) (by omega) hc fallback
        hfallback hcanonical hscaleLo hscale.1 ht hq htol hsep hL hlow hpolicy tariff ha i hR
        v act (by omega) (le_of_not_gt hb) hv
      have hp := hprice m c (by have := (le_max_left Mprice Mcount).trans hm; omega)
        Γ i scale hs hscale.2 hbandActual hcapacity act.bid
      exact hp.trans_lt (hcount m ((le_max_right Mprice Mcount).trans hm) (d+1) c Γ i
        (by omega) V nu highBid hmeas hActions)

end FCAppendix.Bayes.ExclusiveSource
