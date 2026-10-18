import FCAppendix.Exclusive.SourceHomogeneousLowSample

noncomputable section
namespace FCAppendix.Bayes.ExclusiveConstruction
open MeasureTheory ProbabilityTheory Game Exclusive ExclusiveNarrow Set Filter
open Exclusive.Narrow.Existence Exclusive.Narrow.Global ExclusiveSource

theorem homogeneous_low_band_separation_of_small_base {n : ℕ} {scaleLo q H g eps : ℝ}
    (K : LowMarketConstants n scaleLo q) (hscaleOne : scaleLo ≤ 1) (hH : 0 < H)
    (heps : eps < 1/4) (hg : g/H < 1/4) : g+H*K.lowUpper < H*(1-eps) := by
  have hlow : K.lowUpper < 1/2 := K.low_lt_half_scaleLo.trans_le
    (div_le_div_of_nonneg_right hscaleOne (by norm_num))
  have hlowH := mul_lt_mul_of_pos_left hlow hH
  have hgH := (div_lt_iff₀ hH).mp hg
  have hepsH := mul_lt_mul_of_pos_left heps hH
  nlinarith

theorem exists_bandSource_homogeneous_low_parameters (d : ℕ) (hd : 1 ≤ d)
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
      g+H*K.lowUpper < H*(1-eps) →
      ∀ (tariff : UserTariff), tariff.Allowed → ∀ (i : Fin (m+1)) (v : ℝ),
      v-g ≤ H*K.lowUpper →
      ExclusiveTariffBestResponse
        (bandSourceGame (m+1) (d+1) c (by omega) (by omega) hc h heps H (H*scale) beta
          hbeta nu A G g hg (H*K.lowUpper) (H*scale*K.t))
        tariff i v (Interim.abstain (d+1)) := by
  obtain ⟨delta,eta,M0,hdelta,hdeltaCap,heta,hNeg⟩ :=
    exists_sampled_low_parameters d hd h rho scaleLo cap hh hrho hrh hscaleLo hcap K
  refine ⟨delta,eta,M0,hdelta,hdeltaCap,heta,?_⟩
  intro m c hm hc hC eps heps H hH scale hscale beta hbeta hband hmono nu _ _
    A G g hg hseparate tariff ha i v hv
  let Gamma := bandSourceGame (m+1) (d+1) c (by omega) (by omega) hc h heps H (H*scale) beta
    hbeta nu A G g hg (H*K.lowUpper) (H*scale*K.t)
  let fallback := chosenCanonicalPolicy (m+1) (d+1) c (by omega) hc
  have hfallback := measurable_chosenCanonicalPolicy (m+1) (d+1) c (by omega) hc
  have hcanonical : ∀ L, FiniteLaw.ofMeasure Gamma.seedLaw (fun s => (fallback L s).val)
      (hfallback.comp (measurable_const.prodMk measurable_id)) =
        canonicalLottery (d+1) (by omega) c (listBids L) :=
    chosenCanonicalPolicy_law (m+1) (d+1) c (by omega) hc
  have hpolicy : ∀ j L s, (Gamma.policy j L s).val =
      (Marker.sourceContinuation (m := m+1) (n := d+1) (c := c)
        (by omega) (by omega) hc (H*scale*K.t) fallback L s).val := fun _ _ _ => rfl
  have hs : 0 < scale := hscaleLo.trans_le hscale.1
  have hsH : 0 < H*scale := mul_pos hH hs
  have hrawmeas : Measurable (fun u : ValueBand eps => H*scale*Real.exp (beta u)) :=
    (continuous_const.mul (Real.continuous_exp.comp hbeta)).measurable
  have hrawband (u : ValueBand eps) : H*scale*Real.exp (beta u) ∈
      Icc (H*scale*Real.exp (-delta)) (H*scale*Real.exp delta) :=
    ⟨mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hband u).1) hsH.le,
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hband u).2) hsH.le⟩
  have hrawinj : Function.Injective (fun u : ValueBand eps => H*scale*Real.exp (beta u)) := by
    intro u w he
    exact hmono.injective (Real.exp_injective (mul_left_cancel₀ hsH.ne' he))
  have hLaw := bandSourceGame_rival_action_law (by omega) (by omega) hc h heps hH (H*scale)
    beta hbeta nu A G g hg (mul_pos hH K.low_pos) (H*scale*K.t) hseparate i
  have hhigh : 0 < H*scale*Real.exp (-delta) := mul_pos hsH (Real.exp_pos _)
  have hbandActual := ae_actual_bandRivals Gamma i h nu _ hrawmeas hhigh hrawband hLaw
  have hdistinct := ae_actual_activeRivals_distinct Gamma i h nu _ hrawmeas
    (fun u => hhigh.trans_le (hrawband u).1) hrawinj hLaw
  have hexp : Real.exp (-K.deltaCap) ≤ Real.exp (-delta) :=
    Real.exp_le_exp.mpr (neg_le_neg hdeltaCap)
  have hcutFloor : H*scale*K.t ≤ H*scale*Real.exp (-delta) :=
    mul_le_mul_of_nonneg_left (K.marker_floor.trans hexp) hsH.le
  have hcrit : 0 ≤ (1-1/((d+1 : ℕ):ℝ))^d := by
    have hnR : (1 : ℝ) < (d+1 : ℕ) := by exact_mod_cast (show 1 < d+1 by omega)
    have := (div_lt_one (by positivity : (0 : ℝ) < (d+1 : ℕ))).mpr hnR
    exact pow_nonneg (by linarith) _
  have hcutThreshold : H*scale*K.t ≤
      (H*scale*Real.exp (-delta))*(1-1/((d+1 : ℕ):ℝ))^d := by
    have hmarker : K.t ≤ Real.exp (-K.deltaCap)*(1-1/((d+1 : ℕ):ℝ))^d := by
      simpa only [Nat.add_sub_cancel] using K.marker_threshold
    have hh : K.t ≤ Real.exp (-delta)*(1-1/((d+1 : ℕ):ℝ))^d :=
      hmarker.trans (mul_le_mul_of_nonneg_right hexp hcrit)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh hsH.le
  have hgood : ∀ᵐ x ∂userProfileLaw Gamma,
      HighRivals (H*scale*Real.exp (-delta)) i x ∧
      Set.InjOn (fun j => (x j).1.2.bid) (activeRivals i x) := by
    filter_upwards [hbandActual,hdistinct] with x hx hdx
    exact ⟨hx.highRivals,hdx⟩
  intro action
  rw [exclusiveTariffPayoff_abstain]
  by_cases hk : action.routeCount = 0
  · exact (exclusiveTariffPayoff_zero_routes Gamma tariff i v action hk).le
  · by_cases hb : action.bid < H*scale*K.t
    · exact (source_actual_small_bid_zero Gamma (by omega) (by omega) hc (H*scale*K.t)
        fallback hfallback hcanonical hpolicy tariff i hhigh hcutFloor
        (by simpa only [Nat.add_sub_cancel] using hcutThreshold) hgood v action hb).le
    · have hR : ∀ᵐ x ∂userProfileLaw Gamma, HighRivals (H*scale*K.t) i x :=
        hgood.mono fun x hx => by
          intro j hj
          rcases hx.1 j hj with hz | ⟨hr,hbid⟩
          · exact Or.inl hz
          · exact Or.inr ⟨hr,hcutFloor.trans hbid⟩
      have hbN : scale*K.t ≤ action.bid/H :=
        (le_div_iff₀ hH).mpr (by simpa only [mul_assoc,mul_comm H] using le_of_not_gt hb)
      have hvN : v/H-g/H ≤ K.lowUpper := by
        rw [← sub_div]
        exact (div_le_iff₀ hH).mpr (by simpa only [mul_comm] using hv)
      have hneg := hNeg m c hm hc hC nu beta hbeta.measurable hband scale hscale
        tariff ha G (g/H) (v/H) (div_nonneg hg hH.le) hvN action.routeCount (by omega)
        action.routeCount_le (action.bid/H) hbN
      have hcharge : Gamma.g=H*(g/H) := by change g=H*(g/H); field_simp
      have hpay := source_menu_payoff_sampled Gamma hd hc (H*scale*K.t) fallback hfallback
        hcanonical hpolicy i hR tariff H scale (g/H) (v/H) hH hs hcharge h nu beta
        hbeta.measurable action (le_of_not_gt hb) hLaw
      have hvEq : H*(v/H)=v := by field_simp
      rw [hvEq] at hpay
      rw [hpay]
      exact (mul_neg_of_pos_of_neg hH hneg).le

end FCAppendix.Bayes.ExclusiveConstruction
