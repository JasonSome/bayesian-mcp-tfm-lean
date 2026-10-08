import FCAppendix.PayOnce.ActiveAllocationConcentration
import FCAppendix.PayOnce.InactiveSampledFOC
import FCAppendix.PayOnce.EffectiveSampledTransport

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Filter Topology Set Game
open PayOnce PayOnce.CovarianceConcentration PayOnce.TruncatedFOC PayOnce.RareSuccessSlope PayOnce.OwnImpact
open scoped BigOperators ProbabilityTheory

theorem payOnce_inactive_not_weak_zero
    {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (hk : 1 ≤ k) (hc : ∀ t, 0 < C t) (hcm : ∀ t, C t < M t)
    (hM : Tendsto M atTop atTop)
    (hA : ∀ t, (Γ t).A = Schedule.once (k+1))
    (hG : ∀ t, (Γ t).G = Schedule.once (k+1))
    (hu : ∀ t, UsersOptimal (Γ t)) (B : ∀ t, PosteriorSystem (Γ t))
    (hB : ∀ t, PosteriorProposerOptimalAE (Γ t) (B t))
    (hsym : ∀ t, SymmetricProposersOnPath (Γ t))
    (hvalue : ∀ t, PositiveValueAtomless (Γ t))
    (hatom : ∀ t, PositiveVisibleAtomless (Γ t))
    (hinactive : ∀ t, InactiveAbstain (Γ t))
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF : ∀ t, (Γ t).F = F) {g : ℝ} (hg : ∀ t, (Γ t).g = g)
    {ρ : ℝ} (hρ : Tendsto (fun t => (C t : ℝ)/(M t)) atTop (𝓝 ρ))
    (hρb : ρ ∈ Ioo (0 : ℝ) (F.real (Ioi g))) :
    ¬ Tendsto (fun t => CompactifiedBidLaws.bidLaw (Γ t)) atTop
      (𝓝 (⟨Measure.dirac 0, inferInstance⟩ : ProbabilityMeasure ENNReal)) := by
  intro hweak
  have hm t := (hc t).trans (hcm t)
  letI (t : ℕ) : Nonempty (Fin (M t)) := ⟨⟨0, hm t⟩⟩
  have hn : 2 ≤ k+1 := by omega
  have hπ : 0 < F.real (Ioi g) := hρb.1.trans hρb.2
  let r := ρ/F.real (Ioi g)
  have hrb : r ∈ Ioo (0:ℝ) 1 := ⟨div_pos hρb.1 hπ, (div_lt_one hπ).mpr hρb.2⟩
  choose bid hmono hmeas hbound heff hprop using fun t =>
    exists_monotone_effective_bid_bestResponse_all (Γ t) hk (hc t) (hcm t) (hA t) (hG t)
      (hu t) (B t) (hB t) (hsym t) (hvalue t) (hinactive t)
  have hzero := VanishingBidIC.ae_effective_bid_zero_of_weak_zero Γ F hF bid
    hmono (fun t v => (hbound t v).1) heff hweak
  let P := fun t => populationLaw (ι := Fin (M t)) (userProfileLaw (Γ t))
  let p0 := fun t (z : UserProfile (M t) (k+1) × Fin (M t)) =>
    dummyProfileMarginal (Γ t) hn z.1 z.2
  let p := fun t (z : UserProfile (M t) (k+1) × Fin (M t)) =>
    if g < (z.1 z.2).1.1 then p0 t z else r
  let T := fun t (z : UserProfile (M t) (k+1) × Fin (M t)) => profileTruncatedValue (Γ t) z.1 z.2
  let D := fun t (z : UserProfile (M t) (k+1) × Fin (M t)) => profileEffectiveTruncatedBid (Γ t) z.1 z.2
  have hvm t : Measurable (fun z : UserProfile (M t) (k+1) × Fin (M t) => (z.1 z.2).1.1) :=
    measurable_from_prod_countable_left (fun i => measurable_fst.comp (measurable_fst.comp (measurable_pi_apply i)))
  have hp0m t : Measurable (p0 t) := measurable_from_prod_countable_left
    (fun i => measurable_dummyProfileMarginal (Γ t) hn i)
  have hpm t : Measurable (p t) := (hp0m t).ite (measurableSet_lt measurable_const (hvm t)) measurable_const
  have hpb t z : p t z ∈ Icc (0:ℝ) 1 := by
    dsimp only [p]
    split_ifs
    · exact dummyProfileMarginal_bounds (Γ t) hn z.1 z.2
    · exact ⟨hrb.1.le,hrb.2.le⟩
  have htm t : Measurable (T t) := measurable_from_prod_countable_left (measurable_profileTruncatedValue (Γ t))
  have hdm t : Measurable (D t) := measurable_from_prod_countable_left (measurable_profileEffectiveTruncatedBid (Γ t))
  choose weight hw hwb hcorr hfirst using fun t =>
    exists_sampled_inactive_FOC (Γ t) hk (hc t) (hcm t) (hA t) (hG t) (hu t) (B t)
      (hB t) (hsym t) (hvalue t) (hatom t) (hinactive t)
  have hTzero t z (hz : ¬ g < (z.1 z.2).1.1) : T t z = 0 := by
    simp only [T,profileTruncatedValue,hg t,truncatedValue,
      max_eq_right (sub_nonpos.mpr (le_of_not_gt hz)),mul_zero]
  have hDzero t : ∀ᵐ z ∂P t, ¬ g < (z.1 z.2).1.1 → D t z = 0 := by
    have hh := (measurePreserving_fst (μ := userProfileLaw (Γ t))
      (ν := uniformOn (Set.univ : Set (Fin (M t))))).quasiMeasurePreserving.ae
        (ae_all_profile_effectiveBids_eq_type (Γ t) (bid t) (heff t))
    filter_upwards [hh] with z hz hnot
    have hb : bid t (z.1 z.2).1.1 = 0 := by
      have hb := hbound t (z.1 z.2).1.1
      rw [hg t,max_eq_right (sub_nonpos.mpr (le_of_not_gt hnot))] at hb
      exact le_antisymm hb.2 hb.1
    simp only [D,profileEffectiveTruncatedBid,hz z.2,hb,truncatedBid,mul_zero,max_self,min_eq_right zero_le_one]
  have hTtransfer t (f : ℝ → ℝ) : (fun z => T t z*f (p t z)) = fun z => T t z*f (p0 t z) := by
    funext z
    by_cases hz : g < (z.1 z.2).1.1
    · simp only [p,if_pos hz]
    · simp only [hTzero t z hz,zero_mul]
  have hDtransfer t (f : (UserProfile (M t) (k+1) × Fin (M t)) → ℝ → ℝ) :
      (fun z => D t z*f z (p t z)) =ᵐ[P t] fun z => D t z*f z (p0 t z) := by
    filter_upwards [hDzero t] with z hz
    by_cases ha : g < (z.1 z.2).1.1
    · simp only [p,if_pos ha]
    · simp only [hz ha,zero_mul]
  have hTweight t : (fun z => T t z*weightedSlope (k+1) (p t z) (weight t z)) =
      fun z => T t z*weightedSlope (k+1) (p0 t z) (weight t z) := by
    funext z
    by_cases hz : g < (z.1 z.2).1.1
    · simp only [p,if_pos hz]
    · simp only [hTzero t z hz,zero_mul]
  have hcorr' t : (∫ z, T t z*baseSlope (k+1) (p t z) ∂P t) ≤
      (∫ z, T t z*weightedSlope (k+1) (p t z) (weight t z) ∂P t)+(k+1:ℝ)^2/(M t) := by
    rw [hTtransfer t,hTweight t]
    exact hcorr t
  have hfirst' t : (∫ z, T t z*weightedSlope (k+1) (p t z) (weight t z) ∂P t) =
      ∫ z, D t z*(success (k+1) (p t z)+weightedSlope (k+1) (p t z) (weight t z)) ∂P t := by
    rw [hTweight t,integral_congr_ae (hDtransfer t (fun z q => success (k+1) q+weightedSlope (k+1) q (weight t z)))]
    exact hfirst t
  have hpmean : Tendsto (fun t => ∫ z, |p t z-r| ∂P t) atTop (𝓝 0) := by
    have hconc := active_profile_allocation_concentration_of_weak_zero Γ hk hc hcm hM hA hG hu B hB hsym
      hvalue hinactive F hF hg hρ hρb hweak
    apply hconc.congr
    intro t
    symm
    have he : (fun z => |p t z-r|) = fun z => (if g < (z.1 z.2).1.1 then (1:ℝ) else 0)*|p0 t z-r| := by
      funext z
      simp only [p]
      split_ifs <;> simp
    rw [he]
    exact integral_populationLaw (userProfileLaw (Γ t))
      (fun d i => (if g < (d i).1.1 then (1:ℝ) else 0)*|dummyProfileMarginal (Γ t) hn d i-r|)
      (integrable_populationLaw_of_bound (userProfileLaw (Γ t)) _ (C := 1)
        (fun i => by
          have hs : Measurable (fun d : UserProfile (M t) (k+1) => if g < (d i).1.1 then (1:ℝ) else 0) :=
            measurable_const.ite (measurableSet_lt measurable_const
              (measurable_fst.comp (measurable_fst.comp (measurable_pi_apply i)))) measurable_const
          exact hs.mul (((measurable_dummyProfileMarginal (Γ t) hn i).sub_const r).abs))
        (fun d i => by
          change ‖(if g < (d i).1.1 then (1:ℝ) else 0)*|dummyProfileMarginal (Γ t) hn d i-r|‖ ≤ 1
          split_ifs
          · rw [one_mul,Real.norm_eq_abs,abs_abs]
            exact abs_le.mpr ⟨by linarith [(dummyProfileMarginal_bounds (Γ t) hn d i).1,hrb.2],
              by linarith [(dummyProfileMarginal_bounds (Γ t) hn d i).2,hrb.1]⟩
          · simp))
  let tval := ∫ v, truncatedValue (v-g) ∂F
  have htvmeas : Measurable (fun v => truncatedValue (v-g)) := measurable_truncatedValue.comp (measurable_id.sub_const g)
  have htvi : Integrable (fun v => truncatedValue (v-g)) F :=
    UnitInterval.integrable F _ htvmeas (fun v => (truncatedValue_bounds _).1) (fun v => (truncatedValue_bounds _).2)
  have htpos : 0 < tval := by
    apply (integral_pos_iff_support_of_nonneg (fun v => (truncatedValue_bounds (v-g)).1) htvi).mpr
    have hs : Ioi g ⊆ Function.support (fun v => truncatedValue (v-g)) := by
      intro v hv
      exact (truncatedValue_pos (sub_pos.mpr hv)).ne'
    exact lt_of_lt_of_le (ENNReal.toReal_pos_iff.mp hπ).1 (measure_mono hs)
  have hTeq t : (∫ z, T t z ∂P t) = tval := by
    have he := integral_sampled_effective_statistic (Γ t) (hm t)
      (fun x : ℝ × ℝ => truncatedValue (x.1-(Γ t).g))
      (measurable_truncatedValue.comp (measurable_fst.sub_const (Γ t).g))
      (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (truncatedValue_bounds _).1]
        exact (truncatedValue_bounds _).2) (bid t) (heff t)
    simpa only [T, P, profileTruncatedValue, hF t, hg t, tval] using he
  have hDeq t : (∫ z, D t z ∂P t) = ∫ v, truncatedBid (v-g) (bid t v) ∂F := by
    have he := integral_sampled_effective_statistic (Γ t) (hm t)
      (fun x : ℝ × ℝ => truncatedBid (x.1-(Γ t).g) x.2)
      (measurable_truncatedBid.comp ((measurable_fst.sub_const (Γ t).g).prodMk
        measurable_snd))
      (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (truncatedBid_bounds _ _).1]
        exact (truncatedBid_bounds _ _).2) (bid t) (heff t)
    simpa only [D, P, profileEffectiveTruncatedBid, hF t, hg t] using he
  have hDmean : Tendsto (fun t => ∫ z, D t z ∂P t) atTop (𝓝 0) := by
    have hpoint : ∀ᵐ v ∂F, Tendsto (fun t => truncatedBid (v-g) (bid t v)) atTop (𝓝 0) := by
      filter_upwards [hzero] with v hz
      exact squeeze_zero (fun t => (truncatedBid_bounds _ _).1)
        (fun t => truncatedBid_le_bid (hbound t v).1) hz
    have hh := tendsto_integral_of_dominated_convergence (fun _ : ℝ => (1:ℝ))
      (fun t => (measurable_truncatedBid.comp ((measurable_id.sub_const g).prodMk (hmeas t))).aestronglyMeasurable)
      (integrable_const _) (fun t => Eventually.of_forall fun v => by
        change ‖truncatedBid (v-g) (bid t v)‖ ≤ 1
        rw [Real.norm_eq_abs, abs_of_nonneg (truncatedBid_bounds _ _).1]
        exact (truncatedBid_bounds _ _).2) hpoint
    simpa only [hDeq, integral_zero, Function.comp_apply, id_eq] using hh
  have hr : Tendsto (fun t => (k+1:ℝ)^2/(M t)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hM)).const_mul ((k+1:ℝ)^2)
  exact not_all_bids_vanish P hn p T D weight hpm htm hdm hw zero_le_one hrb htpos
    hpb
    (fun t z => truncatedValue_bounds _) (fun t z => truncatedBid_bounds _ _) hwb hpmean
    (by simpa only [hTeq] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => tval) atTop (𝓝 tval)))
    hDmean hr hcorr' hfirst'

end FCAppendix.Bayes
