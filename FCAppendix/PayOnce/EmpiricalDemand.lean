import FCAppendix.PayOnce.ActualBidFloor
import FCAppendix.PayOnce.KernelDemand

namespace FCAppendix.PayOnce.KernelDemand
open MeasureTheory Set Filter Topology CommonList KernelTailEvent KernelLawConvergence
open scoped BigOperators

theorem sum_positive_kernel_deficit {ι : Type*} [Fintype ι] {n : ℕ}
    (hn : 2 ≤ n) (b : ι → ℝ) {L T : ℝ} (hL : 0 < L) (hT : 0 < T) :
    (∑ i, max (kernel n (b i) L-kernel n (b i) T) 0) =
      max ((∑ i, kernel n (b i) L)-(∑ i, kernel n (b i) T)) 0 := by
  rcases le_total L T with h | h
  · have hh i := kernel_antitone_price hn (b := b i) hL hT h
    simp_rw [max_eq_left (sub_nonneg.mpr (hh _))]
    rw [Finset.sum_sub_distrib, max_eq_left (sub_nonneg.mpr (Finset.sum_le_sum fun i _ => hh i))]
  · have hh i := kernel_antitone_price hn (b := b i) hT hL h
    simp_rw [max_eq_right (sub_nonpos.mpr (hh _))]
    rw [Finset.sum_const_zero, max_eq_right (sub_nonpos.mpr (Finset.sum_le_sum fun i _ => hh i))]

end FCAppendix.PayOnce.KernelDemand

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Set Filter Topology Game CommonList
open PayOnce PayOnce.KernelTailEvent PayOnce.KernelLawConvergence PayOnce.CovarianceConcentration
open scoped BigOperators ProbabilityTheory
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def profileKernelDemand (_Γ : FiniteGame m n c Seed) (L : ℝ)
    (d : UserProfile m n) : ℝ := populationMean (fun i => kernel n (d i).1.2.bid L)

theorem kernel_unit_bounds (hn : 2 ≤ n) {L : ℝ} (hL : 0 < L) (b : ℝ) :
    kernel n b L ∈ Icc (0 : ℝ) 1 := by
  by_cases hb : 0 < b
  · exact ⟨kernel_nonneg n hn hb hL, kernel_le_one n hn hb hL⟩
  · rw [kernel_of_le n ((le_of_not_gt hb).trans hL.le)]
    exact ⟨le_rfl, zero_le_one⟩

theorem measurable_profileKernelDemand (Γ : FiniteGame m n c Seed) (hn : 2 ≤ n)
    {L : ℝ} (hL : 0 < L) : Measurable (profileKernelDemand Γ L) :=
  (Finset.measurable_sum _ fun i _ => (continuous_kernel_bid hn hL).measurable.comp
    ((measurable_bid n).comp (measurable_snd.comp (measurable_fst.comp (measurable_pi_apply i))))).div_const _

theorem profile_kernel_deficit (Γ : FiniteGame m n c Seed) (hn : 2 ≤ n)
    (hcm : c ≤ m) {L : ℝ} (hL : 0 < L)
    (d : UserProfile m n) (hpos : ∀ i, 0 < (d i).1.2.bid) :
    populationMean (fun i => max (kernel n (d i).1.2.bid L-
      analyticalProfileMarginal Γ hn hcm d i) 0) = max (profileKernelDemand Γ L d-(c:ℝ)/m) 0 := by
  obtain ⟨T,hT,hp,hcap⟩ := exists_common_profile_root Γ hn hcm d hpos
  have he := KernelDemand.sum_positive_kernel_deficit hn (fun i => (d i).1.2.bid) hL hT
  simp_rw [← hp] at he
  rw [hcap] at he
  simp only [profileKernelDemand, populationMean, Fintype.card_fin, he]
  rw [← sub_div]
  simpa only [zero_div] using (max_div_div_right (Nat.cast_nonneg m) ((∑ i, kernel n (d i).1.2.bid L)-(c:ℝ)) 0).symm

theorem tendsto_actual_kernel_mean
    {M C : ℕ → ℕ} (Γ : ∀ t, FiniteGame (M t) n (C t) Seed)
    (hn : 2 ≤ n) (hroute : ∀ t, ∀ᵐ x ∂((Γ t).F ⊗ₘ (Γ t).σ), x.2.routeCount = n)
    {G : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => CompactifiedBidLaws.bidLaw (Γ t)) atTop (𝓝 G))
    {L : ℝ} (hL : 0 < L) :
    Tendsto (fun t => ∫ d : UserDraw n, kernel n d.1.2.bid L ∂userLaw (Γ t)) atTop
      (𝓝 (KernelDemand.demand n (G : Measure ENNReal) L)) := by
  let f : BoundedContinuousFunction ENNReal ℝ := BoundedContinuousFunction.mkOfCompact ⟨fun b => compactKernel n b L,
    continuous_compactKernel hn hL⟩
  have he t : (∫ b, f b ∂(CompactifiedBidLaws.bidLaw (Γ t) : Measure ENNReal)) =
      ∫ d : UserDraw n, kernel n d.1.2.bid L ∂userLaw (Γ t) := by
    rw [compactifiedBidLaw_eq_map_realBidLaw (Γ t) (by omega) (hroute t),
      integral_map ENNReal.measurable_ofReal.aemeasurable f.continuous.aestronglyMeasurable]
    unfold realBidLaw
    rw [integral_map measurable_drawBid.aemeasurable]
    · apply integral_congr_ae
      exact Eventually.of_forall fun d => by
        simp only [f, BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.coe_mk,
          compactKernel, ENNReal.ofReal_ne_top, if_false, ENNReal.toReal_ofReal d.1.2.bid_nonneg]
    · exact (f.continuous.measurable.comp ENNReal.measurable_ofReal).aestronglyMeasurable
  have hh := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak f
  simp_rw [he] at hh
  exact hh

theorem tendsto_integral_profileKernelDemand_error
    {M C : ℕ → ℕ} (Γ : ∀ t, FiniteGame (M t) n (C t) Seed)
    (hn : 2 ≤ n) (hM : Tendsto M atTop atTop)
    (hroute : ∀ t, ∀ᵐ x ∂((Γ t).F ⊗ₘ (Γ t).σ), x.2.routeCount = n)
    {G : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => CompactifiedBidLaws.bidLaw (Γ t)) atTop (𝓝 G))
    {L : ℝ} (hL : 0 < L) :
    Tendsto (fun t => ∫ d, |profileKernelDemand (Γ t) L d-
      KernelDemand.demand n (G : Measure ENNReal) L| ∂userProfileLaw (Γ t)) atTop (𝓝 0) := by
  let a := fun t => ∫ d : UserDraw n, kernel n d.1.2.bid L ∂userLaw (Γ t)
  have ha : Tendsto a atTop (𝓝 (KernelDemand.demand n (G : Measure ENNReal) L)) :=
    tendsto_actual_kernel_mean Γ hn hroute hweak hL
  have ht := Probability.iid_empiricalMean_L1_tendsto_zero (fun t => userLaw (Γ t))
    (fun _ (d : UserDraw n) => kernel n d.1.2.bid L)
    (fun _ => ((continuous_kernel_bid hn hL).measurable.comp measurable_drawBid).aestronglyMeasurable)
    1 zero_le_one (fun _ => Eventually.of_forall fun d => by
      rw [abs_of_nonneg (kernel_unit_bounds hn hL d.1.2.bid).1]
      exact (kernel_unit_bounds hn hL d.1.2.bid).2) M hM
  have ht' : Tendsto (fun t => ∫ d, |profileKernelDemand (Γ t) L d-a t| ∂userProfileLaw (Γ t)) atTop (𝓝 0) := by
    simpa only [profileKernelDemand, populationMean, Fintype.card_fin, userProfileLaw, a] using ht
  have hI t (r : ℝ) : Integrable (fun d => |profileKernelDemand (Γ t) L d-r|) (userProfileLaw (Γ t)) := by
    apply Integrable.abs
    apply Integrable.sub _ (integrable_const _)
    apply Integrable.div_const
    apply integrable_finsetSum
    intro i _
    exact UnitInterval.integrable _ _ ((continuous_kernel_bid hn hL).measurable.comp
      ((measurable_bid n).comp (measurable_snd.comp (measurable_fst.comp (measurable_pi_apply i)))))
      (fun d => (kernel_unit_bounds hn hL (d i).1.2.bid).1)
      (fun d => (kernel_unit_bounds hn hL (d i).1.2.bid).2)
  apply squeeze_zero (fun t => integral_nonneg fun _ => abs_nonneg _)
    (fun t => ?_) (show Tendsto (fun t => (∫ d, |profileKernelDemand (Γ t) L d-a t| ∂userProfileLaw (Γ t))+
      |a t-KernelDemand.demand n (G : Measure ENNReal) L|) atTop (𝓝 0) from by
        simpa only [sub_self, abs_zero, add_zero] using ht'.add ((ha.sub_const (KernelDemand.demand n (G : Measure ENNReal) L)).abs))
  have hh := integral_mono (hI t (KernelDemand.demand n (G : Measure ENNReal) L))
    ((hI t (a t)).add (integrable_const |a t-KernelDemand.demand n (G : Measure ENNReal) L|))
    (fun d => abs_sub_le (profileKernelDemand (Γ t) L d) (a t) (KernelDemand.demand n (G : Measure ENNReal) L))
  simpa only [Pi.add_apply, integral_add (hI t (a t)) (integrable_const _),
    integral_const, probReal_univ, one_smul] using hh

theorem tendsto_actual_kernel_deficit_zero
    {M C : ℕ → ℕ} (Γ : ∀ t, FiniteGame (M t) n (C t) Seed)
    (hn : 2 ≤ n) (hcm : ∀ t, C t ≤ M t)
    (hM : Tendsto M atTop atTop)
    (hroute : ∀ t, ∀ᵐ x ∂((Γ t).F ⊗ₘ (Γ t).σ), x.2.routeCount = n)
    (hbid : ∀ t, ∀ᵐ x ∂((Γ t).F ⊗ₘ (Γ t).σ), 0 < x.2.bid)
    {G : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => CompactifiedBidLaws.bidLaw (Γ t)) atTop (𝓝 G))
    {ρ : ℝ} (hρ : Tendsto (fun t => (C t : ℝ)/(M t)) atTop (𝓝 ρ))
    {L : ℝ} (hL : 0 < L) (hD : KernelDemand.demand n (G : Measure ENNReal) L ≤ ρ) :
    Tendsto (fun t => ∫ d, populationMean (fun i => max (kernel n (d i).1.2.bid L-
      analyticalProfileMarginal (Γ t) hn (hcm t) d i) 0) ∂userProfileLaw (Γ t)) atTop (𝓝 0) := by
  let D := KernelDemand.demand n (G : Measure ENNReal) L
  let f := fun t (d : UserProfile (M t) n) i => max (kernel n (d i).1.2.bid L-
    analyticalProfileMarginal (Γ t) hn (hcm t) d i) 0
  have hfm t i : Measurable (fun d => f t d i) :=
    (((continuous_kernel_bid hn hL).measurable.comp ((measurable_bid n).comp
      (measurable_snd.comp (measurable_fst.comp (measurable_pi_apply i))))).sub
      (measurable_analyticalProfileMarginal (Γ t) hn (hcm t) i)).max measurable_const
  have hfb t d i : f t d i ∈ Icc (0 : ℝ) 1 := by
    refine ⟨le_max_right _ _, max_le ?_ zero_le_one⟩
    linarith [(kernel_unit_bounds hn hL (d i).1.2.bid).2,
      (analyticalProfileMarginal_bounds (Γ t) hn (hcm t) d i).1]
  have hfi t : Integrable (fun d => populationMean (f t d)) (userProfileLaw (Γ t)) :=
    (integrable_finsetSum _ (fun i _ => UnitInterval.integrable _ _ (hfm t i)
      (fun d => (hfb t d i).1) (fun d => (hfb t d i).2))).div_const _
  have hdi t : Integrable (fun d => |profileKernelDemand (Γ t) L d-D|) (userProfileLaw (Γ t)) := by
    apply Integrable.abs
    apply Integrable.sub _ (integrable_const _)
    apply Integrable.div_const
    apply integrable_finsetSum
    intro i _
    exact UnitInterval.integrable _ _ ((continuous_kernel_bid hn hL).measurable.comp
      ((measurable_bid n).comp (measurable_snd.comp (measurable_fst.comp (measurable_pi_apply i)))))
      (fun d => (kernel_unit_bounds hn hL (d i).1.2.bid).1)
      (fun d => (kernel_unit_bounds hn hL (d i).1.2.bid).2)
  have hu : Tendsto (fun t => (∫ d, |profileKernelDemand (Γ t) L d-D| ∂userProfileLaw (Γ t))+
      |(C t:ℝ)/(M t)-ρ|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero, add_zero] using
      (tendsto_integral_profileKernelDemand_error Γ hn hM hroute hweak hL).add ((hρ.sub_const ρ).abs)
  apply squeeze_zero (fun t => integral_nonneg fun d => div_nonneg
    (Finset.sum_nonneg fun i _ => (hfb t d i).1) (Nat.cast_nonneg _)) _ hu
  intro t
  have hh := integral_mono_ae (hfi t) ((hdi t).add (integrable_const |(C t:ℝ)/(M t)-ρ|))
    ((ae_all_profile_bids_pos (Γ t) (hbid t)).mono fun d hd => by
      change populationMean (f t d) ≤ |profileKernelDemand (Γ t) L d-D|+|(C t:ℝ)/(M t)-ρ|
      rw [show populationMean (f t d) = max (profileKernelDemand (Γ t) L d-(C t:ℝ)/(M t)) 0 from
        profile_kernel_deficit (Γ t) hn (hcm t) hL d hd]
      apply max_le
      · have h1 := le_abs_self (profileKernelDemand (Γ t) L d-D)
        have h2 := neg_le_abs ((C t:ℝ)/(M t)-ρ)
        change D ≤ ρ at hD
        change profileKernelDemand (Γ t) L d-(C t:ℝ)/(M t) ≤
          |profileKernelDemand (Γ t) L d-D|+|(C t:ℝ)/(M t)-ρ|
        linarith
      · exact add_nonneg (abs_nonneg _) (abs_nonneg _))
  simpa only [Pi.add_apply, integral_add (hdi t) (integrable_const _), integral_const,
    probReal_univ, one_smul, populationMean] using hh

theorem actual_group_deficit_lower
    {k : ℕ} (Γ : FiniteGame m (k+1) c Seed) (hk : 1 ≤ k) (hcm : c ≤ m)
    (hA : Γ.A = Schedule.once (k+1)) (hG : Γ.G = Schedule.once (k+1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hatom : PositiveVisibleAtomless Γ)
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = k+1)
    (hbid : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.bid) (i : Fin m)
    {L ε M : ℝ} (hL : 0 < L) (hε : 0 < ε) (hM : 0 ≤ M) (hnL : ((k+1:ℕ):ℝ)*L ≤ ε) :
    (ε/(ε+M*((k+1:ℕ):ℝ)^2)) * (Γ.F ⊗ₘ Γ.σ).real
      {x : ℝ × JointAction (k+1) | ε ≤ x.2.bid ∧ x.1-Γ.g ≤ M} ≤
      ∫ d, max (kernel (k+1) (d i).1.2.bid L-
        analyticalProfileMarginal Γ (by omega) hcm d i) 0 ∂userProfileLaw Γ := by
  classical
  let hn : 2 ≤ k+1 := by omega
  let hc : c ≤ Fintype.card (Rival i)+1 := by simpa only [card_rival_add_one] using hcm
  let E : Set (ℝ × JointAction (k+1)) := {x | ε ≤ x.2.bid ∧ x.1-Γ.g ≤ M}
  let γ := ε/(ε+M*((k+1:ℕ):ℝ)^2)
  have hE : MeasurableSet E := (measurableSet_le measurable_const
    ((measurable_bid (k+1)).comp measurable_snd)).inter
    (measurableSet_le (measurable_fst.sub_const Γ.g) measurable_const)
  let p := fun z : (ℝ × JointAction (k+1)) × (Rival i → ℝ) =>
    AnalyticalKernel.allocation (k+1) c hn hc z.2 z.1.2.bid
  have hp : Measurable p := (AnalyticalKernel.measurable_allocation_joint hn hc).comp
    ((((measurable_bid (k+1)).comp measurable_snd).comp measurable_fst).prodMk measurable_snd)
  have hpb z : p z ∈ Icc (0:ℝ) 1 := AnalyticalKernel.allocation_bounds hn hc _ _
  let f := fun z : (ℝ × JointAction (k+1)) × (Rival i → ℝ) =>
    (Prod.fst ⁻¹' E).indicator (fun z => 1-p z) z
  have hf : Measurable f := (measurable_const.sub hp).indicator (measurable_fst hE)
  have hfb z : f z ∈ Icc (0:ℝ) 1 := by
    by_cases hz : z.1 ∈ E
    · simp only [f, indicator_of_mem (show z ∈ Prod.fst ⁻¹' E from hz)]
      exact ⟨sub_nonneg.mpr (hpb z).2, by linarith [(hpb z).1]⟩
    · simp only [f, indicator_of_notMem (show z ∉ Prod.fst ⁻¹' E from hz)]
      exact ⟨le_rfl, zero_le_one⟩
  have hfi := UnitInterval.integrable ((Γ.F ⊗ₘ Γ.σ).prod (analyticalRivalLaw Γ i)) f hf
    (fun z => (hfb z).1) (fun z => (hfb z).2)
  have hcond (x : ℝ × JointAction (k+1)) :
      (∫ r, f (x,r) ∂analyticalRivalLaw Γ i) =
      E.indicator (fun x => 1-∫ r, p (x,r) ∂analyticalRivalLaw Γ i) x := by
    by_cases hx : x ∈ E
    · have he : (fun r => f (x,r)) = fun r => 1-p (x,r) := by
        funext r
        exact indicator_of_mem (show (x,r) ∈ Prod.fst ⁻¹' E from hx) _
      have hpi : Integrable (fun r => p (x,r)) (analyticalRivalLaw Γ i) :=
        UnitInterval.integrable _ _ (hp.comp (measurable_const.prodMk measurable_id))
          (fun r => (hpb (x,r)).1) (fun r => (hpb (x,r)).2)
      rw [he, indicator_of_mem hx, integral_sub (integrable_const _) hpi]
      simp only [integral_const, probReal_univ, one_smul]
    · have he : (fun r => f (x,r)) = 0 := by
        funext r
        exact indicator_of_notMem (show (x,r) ∉ Prod.fst ⁻¹' E from hx) _
      rw [he, indicator_of_notMem hx]
      exact integral_zero _ _
  have hlo : γ*(Γ.F ⊗ₘ Γ.σ).real E ≤ ∫ z, f z ∂((Γ.F ⊗ₘ Γ.σ).prod (analyticalRivalLaw Γ i)) := by
    rw [integral_prod _ hfi]
    have hi := integral_mono_ae ((integrable_const γ).indicator hE) hfi.integral_prod_left
      ((ae_actual_mean_marginal_bound Γ hk hcm hA hG hu B hB hsym hatom hroute hbid i hε hM).mono
        fun x hx => by
          change E.indicator (fun _ => γ) x ≤ ∫ r, f (x,r) ∂analyticalRivalLaw Γ i
          rw [hcond]
          by_cases he : x ∈ E
          · rw [indicator_of_mem he, indicator_of_mem he]
            exact RareSuccessSlope.gap_le_one_sub_of_mean_bound hε hM (hx he.1 he.2)
          · rw [indicator_of_notMem he, indicator_of_notMem he])
    simpa only [integral_indicator hE, setIntegral_const, smul_eq_mul, mul_comm] using hi
  have hpres := focalAction_rivalBids_measurePreserving Γ i
  have he : (∫ d, f ((d i).1,rivalBids i d) ∂userProfileLaw Γ) =
      ∫ z, f z ∂((Γ.F ⊗ₘ Γ.σ).prod (analyticalRivalLaw Γ i)) := by
    rw [← hpres.map_eq]
    exact (integral_map hpres.measurable.aemeasurable hf.aestronglyMeasurable).symm
  rw [← he] at hlo
  apply hlo.trans
  have htarget : Measurable (fun d => max (kernel (k+1) (d i).1.2.bid L-
      analyticalProfileMarginal Γ hn hcm d i) 0) :=
    (((continuous_kernel_bid hn hL).measurable.comp ((measurable_bid (k+1)).comp
      (measurable_snd.comp (measurable_fst.comp (measurable_pi_apply i))))).sub
      (measurable_analyticalProfileMarginal Γ hn hcm i)).max measurable_const
  have htargetb d : max (kernel (k+1) (d i).1.2.bid L-
      analyticalProfileMarginal Γ hn hcm d i) 0 ∈ Icc (0:ℝ) 1 := by
    refine ⟨le_max_right _ _, max_le ?_ zero_le_one⟩
    linarith [(kernel_unit_bounds hn hL (d i).1.2.bid).2,
      (analyticalProfileMarginal_bounds Γ hn hcm d i).1]
  apply integral_mono (UnitInterval.integrable _ _ (hf.comp hpres.measurable)
    (fun d => (hfb _).1) (fun d => (hfb _).2))
    (UnitInterval.integrable _ _ htarget (fun d => (htargetb d).1) (fun d => (htargetb d).2))
  intro d
  change f ((d i).1,rivalBids i d) ≤ max (kernel (k+1) (d i).1.2.bid L-analyticalProfileMarginal Γ hn hcm d i) 0
  by_cases hd : (d i).1 ∈ E
  · rw [show f ((d i).1,rivalBids i d) = 1-analyticalProfileMarginal Γ hn hcm d i from
      indicator_of_mem (show ((d i).1,rivalBids i d) ∈ Prod.fst ⁻¹' E from hd) _]
    rw [kernel_of_ge (k+1) hn hL (hnL.trans hd.1)]
    exact le_max_left _ _
  · rw [show f ((d i).1,rivalBids i d) = 0 from
      indicator_of_notMem (show ((d i).1,rivalBids i d) ∉ Prod.fst ⁻¹' E from hd) _]
    exact le_max_right _ _

theorem actual_group_average_deficit_lower
    {k : ℕ} (Γ : FiniteGame m (k+1) c Seed) (hk : 1 ≤ k) (hm : 0 < m) (hcm : c ≤ m)
    (hA : Γ.A = Schedule.once (k+1)) (hG : Γ.G = Schedule.once (k+1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hatom : PositiveVisibleAtomless Γ)
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = k+1)
    (hbid : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.bid)
    {L ε M : ℝ} (hL : 0 < L) (hε : 0 < ε) (hM : 0 ≤ M) (hnL : ((k+1:ℕ):ℝ)*L ≤ ε) :
    (ε/(ε+M*((k+1:ℕ):ℝ)^2)) * (Γ.F ⊗ₘ Γ.σ).real
      {x : ℝ × JointAction (k+1) | ε ≤ x.2.bid ∧ x.1-Γ.g ≤ M} ≤
      ∫ d, populationMean (fun i => max (kernel (k+1) (d i).1.2.bid L-
        analyticalProfileMarginal Γ (by omega) hcm d i) 0) ∂userProfileLaw Γ := by
  have hn : 2 ≤ k+1 := by omega
  have hfi i : Integrable (fun d => max (kernel (k+1) (d i).1.2.bid L-
      analyticalProfileMarginal Γ hn hcm d i) 0) (userProfileLaw Γ) := by
    apply UnitInterval.integrable _ _
      ((((continuous_kernel_bid hn hL).measurable.comp ((measurable_bid (k+1)).comp
        (measurable_snd.comp (measurable_fst.comp (measurable_pi_apply i))))).sub
        (measurable_analyticalProfileMarginal Γ hn hcm i)).max measurable_const)
    · exact fun _ => le_max_right _ _
    · intro d
      change max (kernel (k+1) (d i).1.2.bid L-analyticalProfileMarginal Γ hn hcm d i) 0 ≤ 1
      apply max_le _ zero_le_one
      linarith [(kernel_unit_bounds hn hL (d i).1.2.bid).2,
        (analyticalProfileMarginal_bounds Γ hn hcm d i).1]
  rw [integral_populationMean _ _ hfi]
  have hh := div_le_div_of_nonneg_right (Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) =>
    actual_group_deficit_lower Γ hk hcm hA hG hu B hB hsym hatom hroute hbid i hL hε hM hnL)
    (Nat.cast_nonneg m : (0:ℝ) ≤ m)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_div_cancel_left₀ _ (by exact_mod_cast hm.ne' : (m:ℝ) ≠ 0), populationMean] using hh

theorem tendsto_actual_saturated_group_mass_zero
    {M C : ℕ → ℕ} {k : ℕ} (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (hk : 1 ≤ k) (hm : ∀ t, 0 < M t) (hcm : ∀ t, C t ≤ M t)
    (hM : Tendsto M atTop atTop)
    (hA : ∀ t, (Γ t).A = Schedule.once (k+1)) (hG : ∀ t, (Γ t).G = Schedule.once (k+1))
    (hu : ∀ t, UsersOptimal (Γ t)) (B : ∀ t, PosteriorSystem (Γ t))
    (hB : ∀ t, PosteriorProposerOptimalAE (Γ t) (B t))
    (hsym : ∀ t, SymmetricProposersOnPath (Γ t)) (hatom : ∀ t, PositiveVisibleAtomless (Γ t))
    (hroute : ∀ t, ∀ᵐ x ∂((Γ t).F ⊗ₘ (Γ t).σ), x.2.routeCount = k+1)
    (hbid : ∀ t, ∀ᵐ x ∂((Γ t).F ⊗ₘ (Γ t).σ), 0 < x.2.bid)
    {G : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => CompactifiedBidLaws.bidLaw (Γ t)) atTop (𝓝 G))
    {ρ : ℝ} (hρ : Tendsto (fun t => (C t : ℝ)/(M t)) atTop (𝓝 ρ))
    {L ε R : ℝ} (hL : 0 < L) (hε : 0 < ε) (hR : 0 ≤ R) (hnL : ((k+1:ℕ):ℝ)*L ≤ ε)
    (hD : KernelDemand.demand (k+1) (G : Measure ENNReal) L ≤ ρ) :
    Tendsto (fun t => ((Γ t).F ⊗ₘ (Γ t).σ).real
      {x : ℝ × JointAction (k+1) | ε ≤ x.2.bid ∧ x.1-(Γ t).g ≤ R}) atTop (𝓝 0) := by
  have hγ := RareSuccessSlope.saturation_gap_pos (n := k+1) hε hR
  have hzero := tendsto_actual_kernel_deficit_zero Γ (by omega) hcm hM hroute hbid hweak hρ hL hD
  have hbound := hzero.div_const (ε/(ε+R*((k+1:ℕ):ℝ)^2))
  simp only [zero_div] at hbound
  apply squeeze_zero (fun t => measureReal_nonneg) _ hbound
  intro t
  apply (le_div_iff₀ hγ).mpr
  simpa only [mul_comm] using actual_group_average_deficit_lower (Γ t) hk (hm t) (hcm t)
    (hA t) (hG t) (hu t) (B t) (hB t) (hsym t) (hatom t) (hroute t) (hbid t) hL hε hR hnL

end FCAppendix.Bayes
