import FCAppendix.Exclusive.NarrowExistenceNativeSampled
import FCAppendix.Exclusive.NarrowExistenceNativeUtility
import FCAppendix.Exclusive.NarrowExistenceWideActions
import FCAppendix.Exclusive.NarrowGlobalHighMarket
import FCAppendix.Exclusive.SourceStationaryGame
import FCAppendix.Exclusive.SourceLowTypeActualBand

noncomputable section
namespace FCAppendix.Bayes.ExclusiveConstruction
open MeasureTheory ProbabilityTheory Game Exclusive ExclusiveNarrow Set Filter
open Exclusive.Narrow.Finite Exclusive.Narrow.Existence Exclusive.Narrow.Global ExclusiveSource

lemma jointAction_eq_of_bid_route {n : ℕ} (a b : JointAction n)
    (hb : a.bid=b.bid) (hk : a.routeCount=b.routeCount) : a=b := by
  cases a
  cases b
  cases hb
  cases hk
  rfl

lemma bandSourceGame_corridorPlay {m n c : ℕ}
    (hm : 0 < m) (hn : 2 ≤ n) (hc : 0 < c)
    (h : unitInterval) {eps : ℝ} (heps : 0 ≤ eps) (H scale : ℝ) (hs : 0 < scale)
    (beta : ValueBand eps → ℝ) (hbeta : Continuous beta)
    (nu : Measure (ValueBand eps)) [IsProbabilityMeasure nu]
    (A G : Schedule n) (g : ℝ) (hg : 0 ≤ g) (L cutoff : ℝ) (P : Corridor n m c)
    (hband : ∀ u, scale*Real.exp (beta u) ∈ Icc P.lower P.upper) :
    CorridorPlay (bandSourceGame m n c hm hn hc h heps H scale beta hbeta nu A G g hg L cutoff) P := by
  let bid := extendedSourceBid eps heps H scale beta
  have hb : Measurable bid := (continuous_extendedSourceBid eps heps H scale beta hbeta).measurable
  let Γ := bandSourceGame m n c hm hn hc h heps H scale beta hbeta nu A G g hg L cutoff
  have hlaw : Γ.F ⊗ₘ Γ.σ = (bandPrimitive h H nu g L).map
      (fun v => (v,pureAction n (bandHighSet eps H) bid v)) :=
    value_action_law measurableSet_Icc hb A G g hg (chosenSourcePolicy hm hn hc cutoff)
      (measurable_chosenSourcePolicy hm hn hc cutoff)
  unfold CorridorPlay
  change ∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ, _
  rw [hlaw]
  have hset : MeasurableSet {x : ℝ×JointAction n | x.2.routeCount=0 ∨
      (x.2.routeCount=n ∧ x.2.bid ∈ Icc P.lower P.upper)} := by
    have hk : Measurable (fun x : ℝ×JointAction n => x.2.routeCount) := (measurable_routeCount n).comp measurable_snd
    have hbi : Measurable (fun x : ℝ×JointAction n => x.2.bid) := (measurable_bid n).comp measurable_snd
    exact (measurableSet_eq_fun hk measurable_const).union
      ((measurableSet_eq_fun hk measurable_const).inter (hbi measurableSet_Icc))
  apply (ae_map_iff (measurable_id.prodMk (measurable_pureAction n measurableSet_Icc hb)).aemeasurable hset).mpr
  apply Eventually.of_forall
  intro v
  by_cases hv : v ∈ bandHighSet eps H
  · have hpos : 0 < bid v := extendedSourceBid_pos heps H hs beta v
    have ha := pureAction_active (n := n) hv hpos
    exact Or.inr ⟨ha.2,by
      change (pureAction n (bandHighSet eps H) bid v).bid ∈ Icc P.lower P.upper
      rw [ha.1]
      exact hband (normalizedType eps heps (v/H))⟩
  · exact Or.inl (pureAction_inactive hv)

lemma bandSource_high_action_eq {n : ℕ} {eps H scale : ℝ}
    (heps : 0 ≤ eps) (hH : 0 < H) (hscale : 0 < scale)
    (beta : ValueBand eps → ℝ) (u : ValueBand eps) :
    pureAction n (bandHighSet eps H) (extendedSourceBid eps heps H scale beta) (H*(u:ℝ)) =
      (⟨scale*Real.exp (beta u),(mul_pos hscale (Real.exp_pos _)).le,n,le_rfl⟩ : JointAction n) := by
  have hu : H*(u:ℝ) ∈ bandHighSet eps H :=
    ⟨mul_le_mul_of_nonneg_left u.property.1 hH.le,mul_le_mul_of_nonneg_left u.property.2 hH.le⟩
  apply jointAction_eq_of_bid_route
  · simp [pureAction,hu,extendedSourceBid_high heps hH.ne' scale beta u,
      max_eq_left (mul_pos hscale (Real.exp_pos (beta u))).le]
  · simp [pureAction,hu]

theorem exists_bandSource_high_parameters (d : ℕ) (hd : 1 ≤ d) (G : Schedule (d+1))
    (h : unitInterval) (rho scaleLo cap : ℝ)
    (hh : 0 < (h:ℝ)) (hrho : 0 < rho) (hrh : rho < (h:ℝ)) (hlo : 0 < scaleLo)
    (hscales : ∀ a : UserTariff, a.Allowed → referenceBidScale d a (rho/(h:ℝ)) ∈ Icc scaleLo cap)
    (K : LowMarketConstants (d+1) scaleLo ((1-rho/(h:ℝ))^d))
    (W : UniformFiniteConstants d G (h:ℝ) rho) (hWcap : W.delta ≤ K.deltaCap) :
    ∃ delta epsCap eta : ℝ, ∃ M0 : ℕ,
      0 < delta ∧ delta ≤ W.delta ∧ 0 < epsCap ∧ epsCap ≤ W.eps ∧ 0 < eta ∧
      ∀ (m c : ℕ), M0 ≤ m+1 → ∀ hc : 0 < c,
      |(c:ℝ)/((m:ℝ)+1)-rho| < eta → ∀ {eps : ℝ} (heps : 0 ≤ eps), eps ≤ epsCap →
      ∀ H : ℝ, 0 < H → ∀ (g : ℝ) (hg : 0 ≤ g), g/H ≤ eps →
      g+H*K.lowUpper < H*(1-eps) →
      ∀ (nu : Measure (ValueBand eps)) [IsProbabilityMeasure nu] [NullSingletonClass nu]
      (a : UserTariff), a.Allowed →
      ∀ (beta : ValueBand eps → ℝ) (hbeta : Continuous beta),
      (∀ u, beta u ∈ Icc (-delta) delta) → StrictMono beta →
      (∀ u : ValueBand eps, finiteExpectedScore (m := m) d c a G (rho/(h:ℝ)) (g/H)
        h nu beta (u:ℝ) (beta u)=0) → ∀ (A : Schedule (d+1)) (i : Fin (m+1)) (u : ValueBand eps),
      let scale := H*referenceBidScale d a (rho/(h:ℝ))
      ExclusiveTariffBestResponse
        (bandSourceGame (m+1) (d+1) c (by omega) (by omega) hc h heps H scale beta hbeta nu
          A G g hg (H*K.lowUpper) (scale*K.t)) a i (H*(u:ℝ))
        (pureAction (d+1) (bandHighSet eps H) (extendedSourceBid eps heps H scale beta) (H*(u:ℝ))) := by
  let p0 := rho/(h:ℝ)
  have hp0 : 0 < p0 := div_pos hrho hh
  have hp1 : p0 < 1 := (div_lt_one hh).mpr hrh
  obtain ⟨dg,eg,etg,_radius,gap,Mg,hdg,_hdgw,heg,_hegh,hetg,_hradius,hgap,_hMg,_hraw,hglobal⟩ :=
    exists_high_market_parameters d hd h rho W.delta scaleLo cap hh hrho hrh W.delta_pos hlo
      (fun a ha => by rw [referenceCentralBid_eq_referenceBidScale]; exact hscales a ha)
  obtain ⟨Mw,hwideCount⟩ := exists_count_bad_probability_bound_all_types h W.eta_pos
    (probability := W.kappa/(48*W.B)) (div_pos W.kappa_pos (mul_pos (by norm_num : (0:ℝ)<48) W.B_pos))
  let delta := min dg W.delta
  let epsCap := min eg W.eps
  let eta := min etg W.eta
  let M0 := max Mg (max W.M0 (Mw+1))
  refine ⟨delta,epsCap,eta,M0,lt_min hdg W.delta_pos,min_le_right _ _,lt_min heg W.eps_pos,
    min_le_right _ _,lt_min hetg W.eta_pos,?_⟩
  intro m c hm hc hC eps heps hep H hH g hg hgH hsep nu _ _ a ha beta hbeta hband hmono hroot A i u
  let scale0 := referenceBidScale d a p0
  let B := H*scale0
  have hs0 : 0 < scale0 := referenceBidScale_pos d hd a ha p0 hp0.le hp1
  have hB : 0 < B := mul_pos hH hs0
  have hMg : Mg ≤ m+1 := (le_max_left _ _).trans hm
  have hWM : W.M0 ≤ m+1 := ((le_max_left _ _).trans (le_max_right _ _)).trans hm
  have hMw : Mw ≤ m := by have := ((le_max_right _ _).trans (le_max_right Mg (max W.M0 (Mw+1)))).trans hm; omega
  have hCW : |(c:ℝ)/((m:ℝ)+1)-rho| < W.eta := hC.trans_le (min_le_right _ _)
  have heW : eps ≤ W.eps := hep.trans (min_le_right _ _)
  have heG : eps ≤ eg := hep.trans (min_le_left _ _)
  have hbandW : ∀ t, beta t ∈ Icc (-W.delta) W.delta := fun t =>
    ⟨by have := (hband t).1; have := min_le_right dg W.delta; linarith,
      (hband t).2.trans (min_le_right _ _)⟩
  have hbandG : ∀ t, beta t ∈ Icc (-dg) dg := fun t =>
    ⟨by have := (hband t).1; have := min_le_left dg W.delta; linarith,
      (hband t).2.trans (min_le_left _ _)⟩
  have hgNorm : g/H ∈ Icc (0:ℝ) eps := ⟨div_nonneg hg hH.le,hgH⟩
  have hbaseW : g/H ∈ Icc (0:ℝ) W.eps := ⟨hgNorm.1,hgH.trans heW⟩
  have hvW : (u:ℝ) ∈ Icc (1-W.eps) (1+W.eps) :=
    ⟨by linarith only [u.property.1,heW],by linarith only [u.property.2,heW]⟩
  have hstat := hglobal m c hMg (hC.trans_le (min_le_left _ _)) nu beta hbeta.measurable hbandG a ha
    G (g/H) (u:ℝ) ⟨hgNorm.1,hgH.trans heG⟩
      ⟨by linarith only [u.property.1,heG],by linarith only [u.property.2,heG]⟩
  simp only [referenceCentralBid_eq_referenceBidScale] at hstat
  let payoff := fun k b => ∫ omega, LowType.binomialPayoff a G k (g/H) (u:ℝ) b
    (activeDemand (d+1) b (sampledPrice d hd c scale0 beta b omega)) ∂iidRivalLaw m h nu
  change gap ≤ payoff (d+1) scale0 ∧ _ at hstat
  have hbadW : (iidRivalLaw m h nu).real (goodCount m (h:ℝ) W.eta)ᶜ ≤ W.kappa/(48*W.B) := by
    simpa only [goodCount,compl_setOf,not_lt] using (hwideCount (ValueBand eps) m hMw nu).le
  have hsafe : (1-(c:ℝ)/(m+1:ℕ))*Real.exp (2*(1/(d:ℝ))*W.delta) < 1 := by
    simpa only [Nat.cast_add,Nat.cast_one] using W.safe c hWM hCW
  let P := logCorridor d (m+1) c hd (by omega) hc B W.delta hB W.delta_pos hsafe
  let cutoff := B*K.t
  let Γ := bandSourceGame (m+1) (d+1) c (by omega) (by omega) hc h heps H B beta hbeta nu
    A G g hg (H*K.lowUpper) cutoff
  have hFallback := chosenCanonicalPolicy_law (m+1) (d+1) c (by omega) hc
  let fallback := chosenCanonicalPolicy (m+1) (d+1) c (by omega) hc
  have hFallbackMeas := measurable_chosenCanonicalPolicy (m+1) (d+1) c (by omega) hc
  have hpolicy : ∀ j L s, (Γ.policy j L s).val =
      (Marker.sourceContinuation (m := m+1) (n := d+1) (c := c) (by omega) (by omega) hc cutoff fallback L s).val :=
    fun _ _ _ => rfl
  have hExp : Real.exp (-K.deltaCap) ≤ Real.exp (-W.delta) := Real.exp_le_exp.mpr (neg_le_neg hWcap)
  have hcut : cutoff ≤ P.lower := by
    exact mul_le_mul_of_nonneg_left (K.marker_floor.trans hExp) hB.le
  have hcrit : 0 ≤ (1-1/((d+1:ℕ):ℝ))^d := by
    apply pow_nonneg
    have hn : (1:ℝ) < (d+1:ℕ) := by exact_mod_cast (show 1 < d+1 by omega)
    have hh := (div_lt_one (by positivity : (0:ℝ)<(d+1:ℕ))).mpr hn
    linarith only [hh]
  have hthreshold : cutoff ≤ P.lower*(1-1/((d+1:ℕ):ℝ))^((d+1)-1) := by
    have ht0 : K.t ≤ Real.exp (-K.deltaCap)*(1-1/((d+1:ℕ):ℝ))^d := by
      simpa only [Nat.add_sub_cancel] using K.marker_threshold
    have ht := ht0.trans (mul_le_mul_of_nonneg_right hExp hcrit)
    simpa only [P,logCorridor,cutoff,Nat.add_sub_cancel,mul_assoc] using
      mul_le_mul_of_nonneg_left ht hB.le
  have hbids : ∀ t, B*Real.exp (beta t) ∈ Icc P.lower P.upper := fun t =>
    mem_logCorridor d (m+1) c hd (by omega) hc B W.delta hB W.delta_pos hsafe
      (beta t) (hbandW t)
  have hplay : CorridorPlay Γ P := bandSourceGame_corridorPlay (by omega) (by omega) hc h heps H B hB
    beta hbeta nu A G g hg (H*K.lowUpper) cutoff P hbids
  have hActions := bandSourceGame_rival_action_law (by omega) (by omega) hc h heps hH B beta hbeta
    nu A G g hg (mul_pos hH K.low_pos) cutoff hsep i
  have hBidMeas : Measurable (fun t => B*Real.exp (beta t)) :=
    (continuous_const.mul (Real.continuous_exp.comp hbeta)).measurable
  have hRivals := ae_actual_bandRivals Γ i h nu _ hBidMeas P.lower_pos hbids hActions
  have hDistinct := ae_actual_activeRivals_distinct Γ i h nu _ hBidMeas
    (fun t => mul_pos hB (Real.exp_pos _))
    (fun t w he => hmono.injective (Real.exp_injective (mul_left_cancel₀ hB.ne' he))) hActions
  have hsmallGood : ∀ᵐ x ∂userProfileLaw Γ, HighRivals P.lower i x ∧
      Set.InjOn (fun j => (x j).1.2.bid) (activeRivals i x) := by
    filter_upwards [hRivals,hDistinct] with x hx hy
    exact ⟨hx.highRivals,hy⟩
  have hHigh : ∀ᵐ x ∂userProfileLaw Γ, HighRivals cutoff i x := hsmallGood.mono fun x hx => by
    intro j hj
    rcases hx.1 j hj with hz | ⟨hr,hb⟩
    · exact Or.inl hz
    · exact Or.inr ⟨hr,hcut.trans hb⟩
  have hcharge : Γ.g=H*(g/H) := by change g=H*(g/H); field_simp
  let action := fun z : ℝ => (⟨B*Real.exp z,(mul_pos hB (Real.exp_pos z)).le,d+1,le_rfl⟩ : JointAction (d+1))
  have hnorm (z : ℝ) (hz : z ∈ Icc (-W.delta) W.delta) :
      exclusiveTariffPayoff Γ a i (H*(u:ℝ)) (action z) =
        B*finiteExpectedUtility (m := m) d c a G p0 (g/H) h nu beta (u:ℝ) z := by
    exact source_full_payoff_normalization Γ P hplay cutoff hcut fallback hFallbackMeas hFallback hpolicy
      i a ha p0 H (g/H) hp0.le hp1 hH hcharge h nu beta hbeta (u:ℝ) z
        (mem_logCorridor d (m+1) c hd (by omega) hc B W.delta hB W.delta_pos hsafe z hz) hActions
  have hwmax (z : ℝ) (hz : z ∈ Icc (-W.delta) W.delta) :
      exclusiveTariffPayoff Γ a i (H*(u:ℝ)) (action z) ≤
        exclusiveTariffPayoff Γ a i (H*(u:ℝ)) (action (beta u)) := by
    rw [hnorm z hz,hnorm (beta u) (hbandW u)]
    apply mul_le_mul_of_nonneg_left _ hB.le
    exact W.wide_utility_maximizes_of_root h.property c hWM hCW nu a ha (g/H) hbaseW
      beta hbeta hbandW hbadW (u:ℝ) (beta u) hvW (hbandW u) (hroot u) z hz
  have hz0 : (0:ℝ) ∈ Icc (-W.delta) W.delta := ⟨by linarith [W.delta_pos],W.delta_pos.le⟩
  have hcenterCut : cutoff ≤ (action 0).bid := hcut.trans
    (by simpa only [action,Real.exp_zero,mul_one] using
      (mem_logCorridor d (m+1) c hd (by omega) hc B W.delta hB W.delta_pos hsafe 0 hz0).1)
  have hmenu (act : JointAction (d+1)) (hb : cutoff ≤ act.bid) :
      exclusiveTariffPayoff Γ a i (H*(u:ℝ)) act=H*payoff act.routeCount (act.bid/H) := by
    exact source_menu_payoff_sampled Γ hd hc cutoff fallback hFallbackMeas hFallback hpolicy i hHigh
      a H scale0 (g/H) (u:ℝ) hH hs0 hcharge h nu beta hbeta.measurable act hb hActions
  have hcenter : exclusiveTariffPayoff Γ a i (H*(u:ℝ)) (action 0)=H*payoff (d+1) scale0 := by
    rw [hmenu _ hcenterCut]
    congr 2
    dsimp [action,B]
    rw [Real.exp_zero,mul_one,mul_div_cancel_left₀ _ hH.ne']
  have hcenterPos : 0 < exclusiveTariffPayoff Γ a i (H*(u:ℝ)) (action 0) := by
    rw [hcenter]
    exact mul_pos hH (hgap.trans_le hstat.1)
  change ExclusiveTariffBestResponse Γ a i (H*(u:ℝ))
    (pureAction (d+1) (bandHighSet eps H) (extendedSourceBid eps heps H B beta) (H*(u:ℝ)))
  rw [bandSource_high_action_eq heps hH hB beta u]
  change ∀ act, exclusiveTariffPayoff Γ a i (H*(u:ℝ)) act ≤
    exclusiveTariffPayoff Γ a i (H*(u:ℝ)) (action (beta u))
  intro act
  by_cases hsmall : act.bid < cutoff
  · rw [source_actual_small_bid_zero Γ (by omega) (by omega) hc cutoff fallback hFallbackMeas hFallback
      hpolicy a i P.lower_pos hcut hthreshold hsmallGood (H*(u:ℝ)) act hsmall]
    exact hcenterPos.le.trans (hwmax 0 hz0)
  · have hbcut : cutoff ≤ act.bid := le_of_not_gt hsmall
    by_cases hin : act.routeCount=d+1 ∧ act.bid ∈ Icc P.lower P.upper
    · have hpos : 0 < act.bid := P.lower_pos.trans_le hin.2.1
      let z := Real.log (act.bid/B)
      have hratio : 0 < act.bid/B := div_pos hpos hB
      have hquot : act.bid/B ∈ Icc (Real.exp (-W.delta)) (Real.exp W.delta) :=
        ⟨(le_div_iff₀ hB).mpr (by simpa only [P,logCorridor,mul_comm] using hin.2.1),
         (div_le_iff₀ hB).mpr (by simpa only [P,logCorridor,mul_comm] using hin.2.2)⟩
      have hz : z ∈ Icc (-W.delta) W.delta :=
        ⟨(Real.le_log_iff_exp_le hratio).mpr hquot.1,(Real.log_le_iff_le_exp hratio).mpr hquot.2⟩
      have he : act=action z := by
        apply jointAction_eq_of_bid_route
        · dsimp [action,z]
          rw [Real.exp_log hratio,mul_div_cancel₀ _ hB.ne']
        · exact hin.1
      rw [he]
      exact hwmax z hz
    · have hout : act.routeCount=d+1 → act.bid/H ∉
          Icc (scale0*Real.exp (-W.delta)) (scale0*Real.exp W.delta) := by
        intro hk hnormBid
        apply hin
        refine ⟨hk,?_⟩
        have hloB := mul_le_mul_of_nonneg_left hnormBid.1 hH.le
        have hupB := mul_le_mul_of_nonneg_left hnormBid.2 hH.le
        rw [mul_div_cancel₀ _ hH.ne'] at hloB hupB
        exact ⟨by simpa only [P,logCorridor,B,mul_assoc] using hloB,
          by simpa only [P,logCorridor,B,mul_assoc] using hupB⟩
      have hglo := hstat.2 act.routeCount act.routeCount_le (act.bid/H)
        (div_nonneg act.bid_nonneg hH.le) hout
      have hcmp : exclusiveTariffPayoff Γ a i (H*(u:ℝ)) act ≤
          exclusiveTariffPayoff Γ a i (H*(u:ℝ)) (action 0) := by
        rw [hmenu act hbcut,hcenter]
        apply mul_le_mul_of_nonneg_left _ hH.le
        linarith only [hglo,hgap.le]
      exact hcmp.trans (hwmax 0 hz0)

end FCAppendix.Bayes.ExclusiveConstruction
