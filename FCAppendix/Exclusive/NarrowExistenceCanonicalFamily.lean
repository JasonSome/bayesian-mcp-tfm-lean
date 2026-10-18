import FCAppendix.Exclusive.NarrowExistenceCanonicalGame
import FCAppendix.Exclusive.NarrowExistenceSelection
import FCAppendix.Exclusive.NativeHighOptimal

noncomputable section
namespace FCAppendix.Bayes.ExclusiveConstruction
open MeasureTheory ProbabilityTheory Game Exclusive ExclusiveNarrow Set Filter
open Exclusive.Narrow.Existence Exclusive.Narrow.Finite Exclusive.Narrow.Global

theorem narrow_high_bestResponse {d : ℕ} (hd : 1 ≤ d) (G : Schedule (d+1))
    (h : unitInterval) (rho g : ℝ) (hh : 0 < (h:ℝ)) (hrho : 0 < rho)
    (hrh : rho < (h:ℝ)) (hg : 0 ≤ g) (Q : NarrowExistenceParameters d G h rho g)
    {m : ℕ} (c : ℕ) (hM : Q.M0 ≤ m+1)
    (hC : |(c:ℝ)/((m:ℝ)+1)-rho| < Q.candidate.eta)
    (nu : Measure (ValueBand Q.candidate.eps)) [IsProbabilityMeasure nu]
    (a : UserTariff) (ha : a.Allowed)
    (beta : ValueBand Q.candidate.eps → ℝ) (hbeta : Continuous beta)
    (hband : ∀ u, beta u ∈ Icc (-Q.candidate.delta) Q.candidate.delta)
    (hroot : ∀ u : ValueBand Q.candidate.eps,
      finiteExpectedScore (m := m) d c a G (rho/(h:ℝ)) (g/Q.H) h nu beta (u:ℝ) (beta u)=0)
    (A : Schedule (d+1)) (i : Fin (m+1)) (u : ValueBand Q.candidate.eps) :
    let hc := Q.candidate.capacity_pos c (Q.candidate_threshold.trans hM) hC
    let scale := Q.H*referenceBidScale d a (rho/(h:ℝ))
    ExclusiveTariffBestResponse
      (narrowCanonicalGame (m+1) d c hd hc h Q.candidate.eps_pos.le Q.H scale beta hbeta nu A G g hg)
      a i (Q.H*(u:ℝ)) (pureAction (d+1) (bandHighSet Q.candidate.eps Q.H)
        (extendedSourceBid Q.candidate.eps Q.candidate.eps_pos.le Q.H scale beta) (Q.H*(u:ℝ))) := by
  let W := Q.wide
  let U := Q.candidate
  let H := Q.H
  let p0 := rho/(h:ℝ)
  let scale0 := referenceBidScale d a p0
  let B := H*scale0
  have hp0 : 0 < p0 := div_pos hrho hh
  have hp1 : p0 < 1 := (div_lt_one hh).mpr hrh
  have hH : 0 < H := Q.H_pos
  have hs0 : 0 < scale0 := referenceBidScale_pos d hd a ha p0 hp0.le hp1
  have hB : 0 < B := mul_pos hH hs0
  have hUM := Q.candidate_threshold.trans hM
  have hWM := Q.wide_threshold.trans hM
  have hc : 0 < c := U.capacity_pos c hUM hC
  have hCW : |(c:ℝ)/((m:ℝ)+1)-rho| < W.eta := hC.trans_le Q.eta_le
  have hbandW : ∀ t, beta t ∈ Icc (-W.delta) W.delta := fun t =>
    ⟨by linarith [(hband t).1,Q.delta_le],(hband t).2.trans Q.delta_le⟩
  have hbaseW : g/H ∈ Icc (0:ℝ) W.eps := ⟨Q.base.1,Q.base.2.trans Q.eps_le⟩
  have hvW : (u:ℝ) ∈ Icc (1-W.eps) (1+W.eps) :=
    ⟨by linarith [u.property.1,Q.eps_le],by linarith [u.property.2,Q.eps_le]⟩
  have hstat := Q.global hd m c hM hC nu beta hbeta.measurable hband a ha u
  let payoff := fun k b => ∫ omega, LowType.binomialPayoff a G k (g/H) (u:ℝ) b
    (activeDemand (d+1) b (sampledPrice d hd c scale0 beta b omega)) ∂iidRivalLaw m h nu
  change Q.gap ≤ payoff (d+1) scale0 ∧ _ at hstat
  have hbadW := Q.wide_bad hM nu
  have hsafe : (1-(c:ℝ)/((m+1:ℕ):ℝ))*Real.exp (2*(1/(d:ℝ))*W.delta) < 1 := by
    simpa only [Nat.cast_add,Nat.cast_one] using W.safe c hWM hCW
  let P := logCorridor d (m+1) c hd (by omega) hc B W.delta hB W.delta_pos hsafe
  let Gamma := narrowCanonicalGame (m+1) d c hd hc h U.eps_pos.le H B beta hbeta nu A G g hg
  let bid := extendedSourceBid U.eps U.eps_pos.le H B beta
  have hBidMeas : Measurable bid := (continuous_extendedSourceBid U.eps U.eps_pos.le H B beta hbeta).measurable
  have hplay : CorridorPlay Gamma P := by
    apply canonicalGame_corridorPlay hd hc (narrowPrimitive h H nu) (bandHighSet U.eps H)
      measurableSet_Icc bid hBidMeas A G g hg P
    intro v _
    exact extendedSourceBid_band U.eps_pos.le H hB.le beta hbandW v
  let Bpost : PosteriorSystem Gamma := canonicalPosterior (by omega) hc (narrowPrimitive h H nu)
    (bandHighSet U.eps H) measurableSet_Icc bid hBidMeas A G g hg
  have hcont : BroadcastCorridorContinuation Gamma Bpost P :=
    (canonicalGame_rawBandContinuation (by omega) hc (narrowPrimitive h H nu) (bandHighSet U.eps H)
      measurableSet_Icc bid hBidMeas A G g hg P.lower P.upper).toCorridor P rfl rfl
  have hActions := narrowCanonicalGame_rival_action_law hd hc h U.eps_pos.le U.eps_lt_one
    hH B beta hbeta nu A G g hg i
  have hcanonical : ∀ j L, seedLottery Gamma j L = canonicalLottery (d+1) (by omega) c (listBids L) :=
    canonicalGame_seedLottery (by omega) hc (narrowPrimitive h H nu) (bandHighSet U.eps H)
      measurableSet_Icc bid hBidMeas A G g hg
  have hHigh := narrowCanonicalGame_highRivals_zero hd hc h U.eps_pos.le H B beta hbeta nu A G g hg i
  have hcharge : Gamma.g = H*(g/H) := by change g=H*(g/H); field_simp
  let action := fun z : ℝ => (⟨B*Real.exp z,(mul_pos hB (Real.exp_pos z)).le,d+1,le_rfl⟩ : JointAction (d+1))
  have hnorm (z : ℝ) (hz : z ∈ Icc (-W.delta) W.delta) :
      exclusiveTariffPayoff Gamma a i (H*(u:ℝ)) (action z) =
        B*finiteExpectedUtility (m := m) d c a G p0 (g/H) h nu beta (u:ℝ) z :=
    full_payoff_normalization_of_continuation Gamma P hplay Bpost hcont i a ha p0 H (g/H)
      hp0.le hp1 hH hcharge h nu beta hbeta (u:ℝ) z
      (mem_logCorridor d (m+1) c hd (by omega) hc B W.delta hB W.delta_pos hsafe z hz) hActions
  have hwmax (z : ℝ) (hz : z ∈ Icc (-W.delta) W.delta) :
      exclusiveTariffPayoff Gamma a i (H*(u:ℝ)) (action z) ≤
        exclusiveTariffPayoff Gamma a i (H*(u:ℝ)) (action (beta u)) := by
    rw [hnorm z hz,hnorm (beta u) (hbandW u)]
    apply mul_le_mul_of_nonneg_left _ hB.le
    exact W.wide_utility_maximizes_of_root h.property c hWM hCW nu a ha (g/H) hbaseW beta hbeta
      hbandW hbadW (u:ℝ) (beta u) hvW (hbandW u) (hroot u) z hz
  have hz0 : (0:ℝ) ∈ Icc (-W.delta) W.delta := ⟨by linarith [W.delta_pos],W.delta_pos.le⟩
  have hmenu (act : JointAction (d+1)) :
      exclusiveTariffPayoff Gamma a i (H*(u:ℝ)) act = H*payoff act.routeCount (act.bid/H) :=
    canonical_menu_payoff_sampled Gamma hd hc hcanonical i hHigh a H scale0 (g/H) (u:ℝ) hH hs0
      hcharge h nu beta hbeta.measurable act hActions
  have hcenter : exclusiveTariffPayoff Gamma a i (H*(u:ℝ)) (action 0) = H*payoff (d+1) scale0 := by
    rw [hmenu]
    congr 2
    dsimp [action,B]
    rw [Real.exp_zero,mul_one,mul_div_cancel_left₀ _ hH.ne']
  change ExclusiveTariffBestResponse Gamma a i (H*(u:ℝ))
    (pureAction (d+1) (bandHighSet U.eps H) (extendedSourceBid U.eps U.eps_pos.le H B beta) (H*(u:ℝ)))
  rw [bandSource_high_action_eq U.eps_pos.le hH hB beta u]
  change ∀ act, exclusiveTariffPayoff Gamma a i (H*(u:ℝ)) act ≤
    exclusiveTariffPayoff Gamma a i (H*(u:ℝ)) (action (beta u))
  intro act
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
    have hcmp : exclusiveTariffPayoff Gamma a i (H*(u:ℝ)) act ≤
        exclusiveTariffPayoff Gamma a i (H*(u:ℝ)) (action 0) := by
      rw [hmenu,hcenter]
      apply mul_le_mul_of_nonneg_left _ hH.le
      linarith [Q.gap_pos]
    exact hcmp.trans (hwmax 0 hz0)

theorem exists_native_narrow_equilibrium {d : ℕ} (hd : 1 ≤ d) (G : Schedule (d+1))
    (h : unitInterval) (rho g : ℝ) (hh : 0 < (h:ℝ)) (hrho : 0 < rho)
    (hrh : rho < (h:ℝ)) (hg : 0 ≤ g) (Q : NarrowExistenceParameters d G h rho g)
    {m : ℕ} (c : ℕ) (hM : Q.M0 ≤ m+1)
    (hC : |(c:ℝ)/((m:ℝ)+1)-rho| < Q.candidate.eta)
    (nu : Measure (ValueBand Q.candidate.eps)) [IsProbabilityMeasure nu] [NullSingletonClass nu]
    (a : UserTariff) (ha : a.Allowed) :
    ∃ beta : Exclusive.Existence.bidBand (ValueBand Q.candidate.eps) (-Q.candidate.delta) Q.candidate.delta,
      StrictMono beta.val ∧
      (∀ u, 0 < Q.H*referenceBidScale d a (rho/(h:ℝ))*Real.exp (beta.val u)) ∧
      NullSingletonClass (nu.map (fun u => Q.H*referenceBidScale d a (rho/(h:ℝ))*Real.exp (beta.val u))) ∧
      let hc := Q.candidate.capacity_pos c (Q.candidate_threshold.trans hM) hC
      let Gamma := narrowCanonicalGame (m+1) d c hd hc h Q.candidate.eps_pos.le Q.H
        (Q.H*referenceBidScale d a (rho/(h:ℝ))) beta.val beta.val.continuous nu (Schedule.once (d+1)) G g hg
      ExclusiveTariffUsersOptimal Gamma a ∧
      ExclusiveBroadcastOn Gamma (bandHighSet Q.candidate.eps Q.H) ∧
      SymmetricProposersOnPath Gamma ∧ PolicyLawEquivariant Gamma ∧
      ∃ Bpost : PosteriorSystem Gamma, ExclusivePosteriorOptimalAE Gamma Bpost ∧
        ∀ lo hi : ℝ, Completion.Exclusive.RawBandContinuation Gamma Bpost lo hi := by
  have hp0 : 0 < rho/(h:ℝ) := div_pos hrho hh
  have hp1 : rho/(h:ℝ) < 1 := (div_lt_one hh).mpr hrh
  obtain ⟨beta,hmono,hroot⟩ := Q.candidate.exists_pure_stationary hd h.property hp0.le hp1 c
    (Q.candidate_threshold.trans hM) hC nu a ha (g/Q.H) Q.base
  let H := Q.H
  let B := H*referenceBidScale d a (rho/(h:ℝ))
  have hB : 0 < B := mul_pos Q.H_pos (referenceBidScale_pos d hd a ha _ hp0.le hp1)
  have hc := Q.candidate.capacity_pos c (Q.candidate_threshold.trans hM) hC
  let bid := extendedSourceBid Q.candidate.eps Q.candidate.eps_pos.le H B beta.val
  have hb : Measurable bid :=
    (continuous_extendedSourceBid Q.candidate.eps Q.candidate.eps_pos.le H B beta.val beta.val.continuous).measurable
  let Gamma := narrowCanonicalGame (m+1) d c hd hc h Q.candidate.eps_pos.le H B beta.val beta.val.continuous
    nu (Schedule.once (d+1)) G g hg
  let Bpost : PosteriorSystem Gamma := canonicalPosterior (by omega) hc (narrowPrimitive h H nu)
    (bandHighSet Q.candidate.eps H) measurableSet_Icc bid hb (Schedule.once (d+1)) G g hg
  refine ⟨beta,hmono,(fun u => mul_pos hB (Real.exp_pos _)),
    normalizedHighBid_atomless hB nu beta.val beta.val.continuous hmono,?_,?_,?_,?_,Bpost,?_,?_⟩
  · apply narrowCanonicalGame_users_optimal hd hc h Q.candidate.eps_pos.le Q.candidate.eps_lt_one Q.H_pos
      B beta.val beta.val.continuous nu (Schedule.once (d+1)) G g hg a ha
    exact fun i u => narrow_high_bestResponse hd G h rho g hh hrho hrh hg Q c hM hC nu a ha
      beta.val beta.val.continuous beta.property hroot (Schedule.once (d+1)) i u
  · exact canonicalGame_broadcast (by omega) hc (narrowPrimitive h H nu) (bandHighSet Q.candidate.eps H)
      measurableSet_Icc bid hb (Schedule.once (d+1)) G g hg
        (Eventually.of_forall fun v _ => extendedSourceBid_pos Q.candidate.eps_pos.le H hB beta.val v)
  · exact canonicalGame_symmetric (by omega) hc (narrowPrimitive h H nu) (bandHighSet Q.candidate.eps H)
      measurableSet_Icc bid hb (Schedule.once (d+1)) G g hg
  · exact canonicalGame_equivariant (by omega) hc (narrowPrimitive h H nu) (bandHighSet Q.candidate.eps H)
      measurableSet_Icc bid hb (Schedule.once (d+1)) G g hg
  · exact canonicalGame_proposer_optimal (by omega) hc (narrowPrimitive h H nu) (bandHighSet Q.candidate.eps H)
      measurableSet_Icc bid hb (Schedule.once (d+1)) G g hg
  · intro lo hi
    exact canonicalGame_rawBandContinuation (by omega) hc (narrowPrimitive h H nu)
      (bandHighSet Q.candidate.eps H) measurableSet_Icc bid hb (Schedule.once (d+1)) G g hg lo hi

theorem exists_finite_narrow_equilibria (d : ℕ) (hd : 1 ≤ d) (G : Schedule (d+1))
    (h : unitInterval) (rho g : ℝ) (hh : 0 < (h:ℝ)) (hrho : 0 < rho)
    (hrh : rho < (h:ℝ)) (hg : 0 ≤ g) :
    ∃ Q : NarrowExistenceParameters d G h rho g,
      ∀ (m c : ℕ) (hM : Q.M0 ≤ m+1) (hC : |(c:ℝ)/((m:ℝ)+1)-rho| < Q.candidate.eta),
      ∀ (nu : Measure (ValueBand Q.candidate.eps)) [IsProbabilityMeasure nu] [NullSingletonClass nu]
        (a : UserTariff), a.Allowed →
      ∃ beta : Exclusive.Existence.bidBand (ValueBand Q.candidate.eps) (-Q.candidate.delta) Q.candidate.delta,
        StrictMono beta.val ∧
        let hc := Q.candidate.capacity_pos c (Q.candidate_threshold.trans hM) hC
        let Gamma := narrowCanonicalGame (m+1) d c hd hc h Q.candidate.eps_pos.le Q.H
          (Q.H*referenceBidScale d a (rho/(h:ℝ))) beta.val beta.val.continuous nu (Schedule.once (d+1)) G g hg
        ExclusiveTariffUsersOptimal Gamma a ∧ ExclusiveBroadcastOn Gamma (bandHighSet Q.candidate.eps Q.H) ∧
          ∃ Bpost : PosteriorSystem Gamma, ExclusivePosteriorOptimalAE Gamma Bpost := by
  obtain ⟨Q⟩ := exists_narrow_existence_parameters d hd G h rho g hh hrho hrh hg
  refine ⟨Q,?_⟩
  intro m c hM hC nu _ _ a ha
  obtain ⟨beta,hm,_hpos,_hatom,huser,hbroadcast,_hsym,_hequiv,Bpost,hpost,_hraw⟩ :=
    exists_native_narrow_equilibrium hd G h rho g hh hrho hrh hg Q c hM hC nu a ha
  exact ⟨beta,hm,huser,hbroadcast,Bpost,hpost⟩

end FCAppendix.Bayes.ExclusiveConstruction
