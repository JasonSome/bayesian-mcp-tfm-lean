import FCAppendix.Exclusive.SourceStationaryGame

noncomputable section
namespace FCAppendix.Bayes.ExclusiveConstruction
open MeasureTheory ProbabilityTheory Game Exclusive Set Filter
open Exclusive.Narrow.Existence ExclusiveSource

theorem low_band_separation_of_small_base {n : ℕ} {scaleLo q H g eps : ℝ}
    (K : LowMarketConstants n scaleLo q) (hscaleH : scaleLo ≤ H) (hH : 0 < H)
    (heps : eps < 1/4) (hg : g/H < 1/4) : g+K.lowUpper < H*(1-eps) := by
  have hlow : K.lowUpper < H/2 := K.low_lt_half_scaleLo.trans_le
    (div_le_div_of_nonneg_right hscaleH (by norm_num))
  have hgH := (div_lt_iff₀ hH).mp hg
  have hepsH := mul_lt_mul_of_pos_left heps hH
  nlinarith

theorem exists_bandSource_low_parameters (d : ℕ) (hd : 1 ≤ d)
    (h : unitInterval) (rho scaleLo cap : ℝ)
    (hh : 0 < (h : ℝ)) (hrho : 0 < rho) (hrh : rho < (h : ℝ))
    (hscaleLo : 0 < scaleLo) (hcap : 0 < cap)
    (K : LowMarketConstants (d+1) scaleLo ((1-rho/(h : ℝ))^d)) :
    ∃ delta eta : ℝ, ∃ M0 : ℕ, 0 < delta ∧ delta ≤ K.deltaCap ∧ 0 < eta ∧
      ∀ (m c : ℕ), M0 ≤ m → ∀ hc : 0 < c,
      |(c : ℝ)/((m : ℝ)+1)-rho| < eta →
      ∀ {eps : ℝ} (heps : 0 ≤ eps) (H : ℝ), 0 < H →
      ∀ (scale : ℝ), scale ∈ Icc scaleLo cap →
      ∀ (beta : ValueBand eps → ℝ) (hbeta : Continuous beta),
      (∀ u, beta u ∈ Icc (-delta) delta) → StrictMono beta →
      ∀ (nu : Measure (ValueBand eps)) [IsProbabilityMeasure nu] [NullSingletonClass nu]
      (A G : Schedule (d+1)) (g : ℝ) (hg : 0 ≤ g),
      g+K.lowUpper < H*(1-eps) →
      ∀ (tariff : UserTariff), tariff.Allowed → ∀ (i : Fin (m+1)) (v : ℝ),
      v-g ≤ K.lowUpper →
      ExclusiveTariffBestResponse
        (bandSourceGame (m+1) (d+1) c (by omega) (by omega) hc h heps H scale beta
          hbeta nu A G g hg K.lowUpper (scale*K.t))
        tariff i v (Interim.abstain (d+1)) := by
  obtain ⟨delta,eta,M0,hdelta,hdeltaCap,heta,hLow⟩ :=
    exists_source_low_market_parameters (Seed := unitInterval) d hd h rho scaleLo cap
      K.t K.tolerance K.lowUpper K.deltaCap hh hrho hrh hscaleLo hcap K.tolerance_pos
      K.low_pos.le K.separation K.low_margin K.width_pos K.marker_floor
      (by simpa only [Nat.add_sub_cancel] using K.marker_threshold)
  refine ⟨delta,eta,M0,hdelta,hdeltaCap,heta,?_⟩
  intro m c hm hc hC eps heps H hH scale hscale beta hbeta hband hmono nu _ _
    A G g hg hseparate tariff ha i v hv
  let Γ := bandSourceGame (m+1) (d+1) c (by omega) (by omega) hc h heps H scale beta
    hbeta nu A G g hg K.lowUpper (scale*K.t)
  have hs : 0 < scale := hscaleLo.trans_le hscale.1
  have hmeas : Measurable (fun u : ValueBand eps => scale*Real.exp (beta u)) :=
    (continuous_const.mul (Real.continuous_exp.comp hbeta)).measurable
  have hbidband (u : ValueBand eps) : scale*Real.exp (beta u) ∈
      Icc (scale*Real.exp (-delta)) (scale*Real.exp delta) :=
    ⟨mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hband u).1) hs.le,
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hband u).2) hs.le⟩
  have hinj : Function.Injective (fun u : ValueBand eps => scale*Real.exp (beta u)) := by
    intro u w he
    exact hmono.injective (Real.exp_injective (mul_left_cancel₀ hs.ne' he))
  exact hLow m c hm hc hC Γ scale hscale
    (chosenCanonicalPolicy (m+1) (d+1) c (by omega) hc)
    (measurable_chosenCanonicalPolicy (m+1) (d+1) c (by omega) hc)
    (chosenCanonicalPolicy_law (m+1) (d+1) c (by omega) hc) (fun _ _ _ => rfl)
    (ValueBand eps) i nu (fun u => scale*Real.exp (beta u)) hmeas hbidband hinj
    (bandSourceGame_rival_action_law (by omega) (by omega) hc h heps hH scale beta hbeta
      nu A G g hg K.low_pos (scale*K.t) hseparate i) tariff ha v hv

end FCAppendix.Bayes.ExclusiveConstruction
