import FCAppendix.PayOnce.ActualConcentration
import FCAppendix.PayOnce.ActualTruncatedFOC
import FCAppendix.PayOnce.PopulationSampling

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Filter Topology Set Game
open PayOnce PayOnce.CovarianceConcentration PayOnce.TruncatedFOC PayOnce.RareSuccessSlope PayOnce.OwnImpact
open scoped BigOperators ProbabilityTheory

theorem exists_sampled_actual_FOC
    {m c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m (k+1) c Seed) (hk : 1 ≤ k) (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A = Schedule.once (k+1)) (hG : Γ.G = Schedule.once (k+1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hatom : PositiveVisibleAtomless Γ)
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = k+1)
    (hbid : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.bid) :
    let P := populationLaw (ι := Fin m) (userProfileLaw Γ)
    let p := fun z : UserProfile m (k+1) × Fin m => analyticalProfileMarginal Γ (by omega) hcm.le z.1 z.2
    let T := fun z : UserProfile m (k+1) × Fin m => profileTruncatedValue Γ z.1 z.2
    let D := fun z : UserProfile m (k+1) × Fin m => profileTruncatedBid Γ z.1 z.2
    ∃ weight : UserProfile m (k+1) × Fin m → ℝ,
      Measurable weight ∧ (∀ z, weight z ∈ Icc (0 : ℝ) 1) ∧
      (∫ z, T z*baseSlope (k+1) (p z) ∂P) ≤
        (∫ z, T z*weightedSlope (k+1) (p z) (weight z) ∂P)+(k+1:ℝ)^2/m ∧
      (∫ z, T z*weightedSlope (k+1) (p z) (weight z) ∂P) =
        ∫ z, D z*(success (k+1) (p z)+weightedSlope (k+1) (p z) (weight z)) ∂P := by
  have hm : 0 < m := hc.trans hcm
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  let n := k+1
  have hn : 2 ≤ n := by omega
  let p := analyticalProfileMarginal Γ hn hcm.le
  let T := profileTruncatedValue Γ
  let D := profileTruncatedBid Γ
  obtain ⟨weight, hw, hwb, hsum, hfirst⟩ :=
    exists_bounded_actual_profile_FOC Γ hk hc hcm hA hG hu B hB hsym hatom hroute hbid
  have hp := fun i => measurable_analyticalProfileMarginal Γ hn hcm.le i
  have ht := measurable_profileTruncatedValue Γ
  have hd := measurable_profileTruncatedBid Γ
  have htb d i : T d i ∈ Icc (0:ℝ) 1 := truncatedValue_bounds _
  have hdb d i : D d i ∈ Icc (0:ℝ) 1 := truncatedBid_bounds _ _
  have hf0 i : Measurable (fun d => T d i*baseSlope n (p d i)) :=
    (ht i).mul ((measurable_baseSlope n).comp (hp i))
  have hf1 i : Measurable (fun d => T d i*weightedSlope n (p d i) (weight d i)) :=
    (ht i).mul ((measurable_weightedSlope n).comp ((hp i).prodMk (hw i)))
  have hf2 i : Measurable (fun d => D d i*(success n (p d i)+weightedSlope n (p d i) (weight d i))) :=
    (hd i).mul (((continuous_success n).measurable.comp (hp i)).add
      ((measurable_weightedSlope n).comp ((hp i).prodMk (hw i))))
  have hb0 d i : ‖T d i*baseSlope n (p d i)‖ ≤ (n:ℝ)^2 := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (htb d i).1,
      abs_of_nonneg (baseSlope_bounds hn (analyticalProfileMarginal_bounds Γ hn hcm.le d i)).1]
    exact (mul_le_mul_of_nonneg_right (htb d i).2
      (baseSlope_bounds hn (analyticalProfileMarginal_bounds Γ hn hcm.le d i)).1).trans
      (by simpa using (baseSlope_bounds hn (analyticalProfileMarginal_bounds Γ hn hcm.le d i)).2)
  have hb1 d i : ‖T d i*weightedSlope n (p d i) (weight d i)‖ ≤ (n:ℝ)^2 := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (htb d i).1,
      abs_of_nonneg (weightedSlope_bounds hn (analyticalProfileMarginal_bounds Γ hn hcm.le d i) (hwb d i)).1]
    exact (mul_le_mul_of_nonneg_right (htb d i).2
      (weightedSlope_bounds hn (analyticalProfileMarginal_bounds Γ hn hcm.le d i) (hwb d i)).1).trans
      (by simpa using (weightedSlope_bounds hn (analyticalProfileMarginal_bounds Γ hn hcm.le d i) (hwb d i)).2)
  have hb2 d i : ‖D d i*(success n (p d i)+weightedSlope n (p d i) (weight d i))‖ ≤ 1+(n:ℝ)^2 := by
    have hs := success_mem_unit (n := n) (analyticalProfileMarginal_bounds Γ hn hcm.le d i)
    have hws := weightedSlope_bounds hn (analyticalProfileMarginal_bounds Γ hn hcm.le d i) (hwb d i)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hdb d i).1,
      abs_of_nonneg (add_nonneg hs.1 hws.1)]
    exact (mul_le_mul_of_nonneg_right (hdb d i).2 (add_nonneg hs.1 hws.1)).trans
      (by simpa using add_le_add hs.2 hws.2)
  have hi0 := integrable_populationLaw_of_bound (userProfileLaw Γ) _ hf0 hb0
  have hi1 := integrable_populationLaw_of_bound (userProfileLaw Γ) _ hf1 hb1
  have hi2 := integrable_populationLaw_of_bound (userProfileLaw Γ) _ hf2 hb2
  refine ⟨fun z => weight z.1 z.2, measurable_from_prod_countable_left hw,
    fun z => hwb z.1 z.2, ?_, ?_⟩
  · change (∫ z, T z.1 z.2*baseSlope n (p z.1 z.2) ∂populationLaw (userProfileLaw Γ)) ≤
      (∫ z, T z.1 z.2*weightedSlope n (p z.1 z.2) (weight z.1 z.2) ∂populationLaw (userProfileLaw Γ)) + (k+1:ℝ)^2/m
    rw [integral_populationLaw _ (fun d i => T d i*baseSlope n (p d i)) hi0,
      integral_populationLaw _ (fun d i => T d i*weightedSlope n (p d i) (weight d i)) hi1]
    simpa only [populationMean, Fintype.card_fin, one_mul, n, Nat.cast_add, Nat.cast_one] using
      integral_average_correction_le (userProfileLaw Γ) hn p T weight hp ht hw zero_le_one
        (fun d i => analyticalProfileMarginal_bounds Γ hn hcm.le d i)
        (fun d i => truncatedValue_bounds _) hwb hsum (Nat.cast_pos.mpr hm)
  · change (∫ z, T z.1 z.2*weightedSlope n (p z.1 z.2) (weight z.1 z.2) ∂populationLaw (userProfileLaw Γ)) =
      ∫ z, D z.1 z.2*(success n (p z.1 z.2)+weightedSlope n (p z.1 z.2) (weight z.1 z.2)) ∂populationLaw (userProfileLaw Γ)
    rw [integral_populationLaw _ (fun d i => T d i*weightedSlope n (p d i) (weight d i)) hi1,
      integral_populationLaw _ (fun d i => D d i*(success n (p d i)+weightedSlope n (p d i) (weight d i))) hi2]
    rw [integral_populationMean _ _ (fun i => Integrable.of_bound (hf1 i).aestronglyMeasurable _
      (Eventually.of_forall fun d => hb1 d i)),
      integral_populationMean _ _ (fun i => Integrable.of_bound (hf2 i).aestronglyMeasurable _
      (Eventually.of_forall fun d => hb2 d i))]
    exact congrArg populationMean (funext hfirst)

theorem integral_sampled_action_of_pure
    {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (f : ℝ × JointAction n → ℝ) (hf : Measurable f) {C : ℝ} (hb : ∀ x, ‖f x‖ ≤ C)
    (bid : ℝ → ℝ) (hpure : ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂Γ.σ v, a = safeFullBid n (bid v)) :
    (∫ z : UserProfile m n × Fin m, f (z.1 z.2).1 ∂populationLaw (userProfileLaw Γ)) =
      ∫ v, f (v, safeFullBid n (bid v)) ∂Γ.F := by
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hm' i : Measurable (fun d : UserProfile m n => f (d i).1) :=
    hf.comp (measurable_fst.comp (measurable_pi_apply i))
  have hi i : Integrable (fun d : UserProfile m n => f (d i).1) (userProfileLaw Γ) :=
    Integrable.of_bound (hm' i).aestronglyMeasurable C (Eventually.of_forall fun d => hb _)
  rw [integral_populationLaw (userProfileLaw Γ) (fun (d : UserProfile m n) (i : Fin m) => f (d i).1)
    (integrable_populationLaw_of_bound _ _ hm' (fun d i => hb _)), integral_populationMean _ _ hi]
  have he i : (∫ d : UserProfile m n, f (d i).1 ∂userProfileLaw Γ) =
      ∫ v, f (v, safeFullBid n (bid v)) ∂Γ.F := by
    simpa only [integral_const, probReal_univ, one_smul] using
      integral_profile_statistic_eq_type_rivals Γ i (fun z => f z.1)
        (hf.comp measurable_fst) C (fun z => hb z.1) bid hpure
  simp only [populationMean, he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast hm.ne' : (m : ℝ) ≠ 0)

theorem payOnce_not_weak_zero
    {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (hk : 1 ≤ k) (hc : ∀ t, 0 < C t) (hcm : ∀ t, C t < M t)
    (hM : Tendsto M atTop atTop)
    (hA : ∀ t, (Γ t).A = Schedule.once (k+1))
    (hG : ∀ t, (Γ t).G = Schedule.once (k+1))
    (hu : ∀ t, UsersOptimal (Γ t)) (B : ∀ t, PosteriorSystem (Γ t))
    (hB : ∀ t, PosteriorProposerOptimalAE (Γ t) (B t))
    (hsym : ∀ t, SymmetricProposersOnPath (Γ t))
    (hatom : ∀ t, PositiveVisibleAtomless (Γ t))
    (F : Measure ℝ) [IsProbabilityMeasure F] [NullSingletonClass F]
    (hF : ∀ t, (Γ t).F = F) {g : ℝ} (hg : ∀ t, (Γ t).g = g)
    (hactive : ∀ᵐ v ∂F, g < v)
    {ρ : ℝ} (hρ : Tendsto (fun t => (C t : ℝ)/(M t)) atTop (𝓝 ρ))
    (hρb : ρ ∈ Ioo (0 : ℝ) 1) :
    ¬ Tendsto (fun t => CompactifiedBidLaws.bidLaw (Γ t)) atTop
      (𝓝 (⟨Measure.dirac 0, inferInstance⟩ : ProbabilityMeasure ENNReal)) := by
  intro hweak
  have hm t := (hc t).trans (hcm t)
  letI (t : ℕ) : Nonempty (Fin (M t)) := ⟨⟨0, hm t⟩⟩
  have hn : 2 ≤ k+1 := by omega
  have hv t : PositiveValueAtomless (Γ t) := by
    intro v _
    rw [hF t]
    exact measure_singleton v
  have ha t : ∀ᵐ v ∂(Γ t).F, (Γ t).g < v := by simpa only [hF t, hg t] using hactive
  choose bid hmono hmeas hbound hprop using fun t =>
    exists_monotone_bid_bestResponse_all (Γ t) hk (hc t) (hcm t) (hA t) (hG t)
      (hu t) (B t) (hB t) (hsym t) (hv t) (ha t)
  have hpure t : ∀ᵐ v ∂(Γ t).F, ∀ᵐ a ∂(Γ t).σ v,
      a = safeFullBid (k+1) (bid t v) := (hprop t).mono fun _ hx => hx.2.2.2
  have hroute t : ∀ᵐ x ∂((Γ t).F ⊗ₘ (Γ t).σ), x.2.routeCount = k+1 := by
    apply Measure.ae_compProd_of_ae_ae
      (measurableSet_eq_fun ((measurable_routeCount (k+1)).comp measurable_snd) measurable_const)
    filter_upwards [hpure t] with v hvi
    filter_upwards [hvi] with a hai
    simp only [hai, safeFullBid, fullBid, Function.comp_apply]
  have hbid t : ∀ᵐ x ∂((Γ t).F ⊗ₘ (Γ t).σ), 0 < x.2.bid := by
    apply Measure.ae_compProd_of_ae_ae
      (measurableSet_lt measurable_const ((measurable_bid (k+1)).comp measurable_snd))
    filter_upwards [hprop t] with v hvi
    filter_upwards [hvi.2.2.2] with a hai
    simp only [hai, safeFullBid, fullBid, max_eq_left (hbound t v).1]
    exact hvi.1
  have hzero := VanishingBidIC.ae_bid_zero_of_actual_weak_zero Γ (by omega) F hF bid
    hmono (fun t v => (hbound t v).1) hpure hroute hweak
  let P := fun t => populationLaw (ι := Fin (M t)) (userProfileLaw (Γ t))
  let p := fun t (z : UserProfile (M t) (k+1) × Fin (M t)) =>
    analyticalProfileMarginal (Γ t) hn (hcm t).le z.1 z.2
  let T := fun t (z : UserProfile (M t) (k+1) × Fin (M t)) => profileTruncatedValue (Γ t) z.1 z.2
  let D := fun t (z : UserProfile (M t) (k+1) × Fin (M t)) => profileTruncatedBid (Γ t) z.1 z.2
  have hpm t : Measurable (p t) := measurable_from_prod_countable_left
    (fun i => measurable_analyticalProfileMarginal (Γ t) hn (hcm t).le i)
  have htm t : Measurable (T t) := measurable_from_prod_countable_left (measurable_profileTruncatedValue (Γ t))
  have hdm t : Measurable (D t) := measurable_from_prod_countable_left (measurable_profileTruncatedBid (Γ t))
  choose weight hw hwb hcorr hfirst using fun t =>
    exists_sampled_actual_FOC (Γ t) hk (hc t) (hcm t) (hA t) (hG t) (hu t) (B t)
      (hB t) (hsym t) (hatom t) (hroute t) (hbid t)
  have hpmean : Tendsto (fun t => ∫ z, |p t z-ρ| ∂P t) atTop (𝓝 0) := by
    have hconc := actual_profile_concentration_of_weak_zero Γ hk hc hcm hM hA hG hu B hB hsym F hF hg hactive hweak hρ
    apply hconc.congr
    intro t
    symm
    exact integral_populationLaw _ (fun d i => |analyticalProfileMarginal (Γ t) hn (hcm t).le d i-ρ|)
      (integrable_populationLaw_of_bound _ _ (C := 1)
        (fun i => ((measurable_analyticalProfileMarginal (Γ t) hn (hcm t).le i).sub_const ρ).abs)
        (fun d i => by
          rw [Real.norm_eq_abs, abs_abs]
          exact abs_le.mpr ⟨by linarith [(analyticalProfileMarginal_bounds (Γ t) hn (hcm t).le d i).1, hρb.2],
            by linarith [(analyticalProfileMarginal_bounds (Γ t) hn (hcm t).le d i).2, hρb.1]⟩))
  let tval := ∫ v, truncatedValue (v-g) ∂F
  have htvmeas : Measurable (fun v => truncatedValue (v-g)) := measurable_truncatedValue.comp (measurable_id.sub_const g)
  have htvi : Integrable (fun v => truncatedValue (v-g)) F :=
    UnitInterval.integrable F _ htvmeas (fun v => (truncatedValue_bounds _).1) (fun v => (truncatedValue_bounds _).2)
  have htpos : 0 < tval := by
    apply (integral_pos_iff_support_of_nonneg (fun v => (truncatedValue_bounds (v-g)).1) htvi).mpr
    have hs : F (Function.support (fun v => truncatedValue (v-g))) = 1 := by
      rw [← measure_univ (μ := F)]
      apply measure_congr
      filter_upwards [hactive] with v hv'
      exact propext ⟨fun _ => trivial, fun _ => (truncatedValue_pos (sub_pos.mpr hv')).ne'⟩
    rw [hs]
    exact zero_lt_one
  have hTeq t : (∫ z, T t z ∂P t) = tval := by
    have he := integral_sampled_action_of_pure (Γ t) (hm t)
      (fun x => truncatedValue (x.1-(Γ t).g))
      (measurable_truncatedValue.comp (measurable_fst.sub_const (Γ t).g))
      (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (truncatedValue_bounds _).1]
        exact (truncatedValue_bounds _).2) (bid t) (hpure t)
    simpa only [T, P, profileTruncatedValue, hF t, hg t, tval] using he
  have hDeq t : (∫ z, D t z ∂P t) = ∫ v, truncatedBid (v-g) (bid t v) ∂F := by
    have he := integral_sampled_action_of_pure (Γ t) (hm t)
      (fun x => truncatedBid (x.1-(Γ t).g) x.2.bid)
      (measurable_truncatedBid.comp ((measurable_fst.sub_const (Γ t).g).prodMk
        ((measurable_bid (k+1)).comp measurable_snd)))
      (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (truncatedBid_bounds _ _).1]
        exact (truncatedBid_bounds _ _).2) (bid t) (hpure t)
    simpa only [D, P, profileTruncatedBid, hF t, hg t, safeFullBid, fullBid,
      max_eq_left (hbound t _).1] using he
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
  exact not_all_bids_vanish P hn p T D weight hpm htm hdm hw zero_le_one hρb htpos
    (fun t z => analyticalProfileMarginal_bounds (Γ t) hn (hcm t).le z.1 z.2)
    (fun t z => truncatedValue_bounds _) (fun t z => truncatedBid_bounds _ _) hwb hpmean
    (by simpa only [hTeq] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => tval) atTop (𝓝 tval)))
    hDmean hr hcorr hfirst

end FCAppendix.Bayes
