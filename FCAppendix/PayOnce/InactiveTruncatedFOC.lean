import FCAppendix.PayOnce.InactiveProfileWeights
import FCAppendix.PayOnce.DummyFirstOrder
import FCAppendix.PayOnce.ActualTruncatedFOC

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Filter Topology Set Game
open PayOnce PayOnce.DummyKernel PayOnce.TruncatedFOC PayOnce.OwnImpact
open PayOnce.RareSuccessSlope PayOnce.CompactifiedBidLaws
open scoped BigOperators ProbabilityTheory
variable {m c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def profileEffectiveTruncatedBid {n : ℕ} (Γ : FiniteGame m n c Seed)
    (d : UserProfile m n) (i : Fin m) : ℝ :=
  truncatedBid ((d i).1.1-Γ.g) (effectiveBid (d i).1.2)

theorem measurable_profileEffectiveTruncatedBid {n : ℕ}
    (Γ : FiniteGame m n c Seed) (i : Fin m) :
    Measurable (fun d => profileEffectiveTruncatedBid Γ d i) :=
  measurable_truncatedBid.comp
    (((measurable_fst.comp (measurable_fst.comp (measurable_pi_apply i))).sub_const Γ.g).prodMk
      ((measurable_effectiveBid n).comp (measurable_snd.comp (measurable_fst.comp (measurable_pi_apply i)))))

theorem ae_inactive_truncated_identity (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A = Schedule.once (k+1)) (hG : Γ.G = Schedule.once (k+1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ) (hB : PosteriorProposerOptimalAE Γ B)
    (hsym : SymmetricProposersOnPath Γ) (hvalue : PositiveValueAtomless Γ)
    (hatom : PositiveVisibleAtomless Γ) (hinactive : InactiveAbstain Γ)
    (i : Fin m) (weight : ℝ × (Rival i → ℝ) → ℝ)
    (hderiv : ∀ᵐ b ∂(BidScaling.realBidLaw Γ : Measure ℝ), 0 < b →
      HasDerivAt (coverage (k+1) c (by omega)
        (Measure.pi fun _ : Rival i => (BidScaling.realBidLaw Γ : Measure ℝ)))
        ((∫ r, weightedSlope (k+1) (allocation (k+1) c (by omega) r b)
          (weight (b,r)) ∂Measure.pi (fun _ : Rival i => (BidScaling.realBidLaw Γ : Measure ℝ)))/b) b) :
    let hn : 2 ≤ k+1 := by omega
    let ν := Measure.pi fun _ : Rival i => (BidScaling.realBidLaw Γ : Measure ℝ)
    let Q := coverage (k+1) c hn ν
    let D := fun b => ∫ r, weightedSlope (k+1) (allocation (k+1) c hn r b) (weight (b,r)) ∂ν
    ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ),
      truncatedValue (x.1-Γ.g)*D (effectiveBid x.2) =
        truncatedBid (x.1-Γ.g) (effectiveBid x.2)*(Q (effectiveBid x.2)+D (effectiveBid x.2)) := by
  dsimp only
  have hfoc := ae_inactive_payOnce_first_order Γ hk hc hcm hA hG hu B hB hsym hvalue hatom hinactive i
  rw [realEffectiveBidLaw_eq_action_map] at hderiv
  have hd := ae_of_ae_map ((measurable_effectiveBid (k+1)).comp measurable_snd).aemeasurable hderiv
  filter_upwards [hfoc,hd,ae_effectiveBid_participation Γ hc hcm hA hG hu B hB hsym hvalue]
    with x hf hd hp
  rw [truncatedBid_eq (effectiveBid_nonneg x.2) hp.2.1]
  by_cases hv : Γ.g < x.1
  · have hfull := hp.2.2 hv
    have heff : effectiveBid x.2 = x.2.bid := by
      simp only [effectiveBid,hfull,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,if_false]
    have hb : 0 < x.2.bid := heff ▸ hp.1.mpr hv
    have hD := hd (hp.1.mpr hv)
    simp only [Function.comp_def,← realEffectiveBidLaw_eq_action_map,heff] at hD
    have hfirst := (hf hv).2
    rw [hD.deriv] at hfirst
    have hm := congrArg (fun z : ℝ => z*x.2.bid) hfirst
    field_simp [hb.ne'] at hm
    have ht := congrArg (fun z : ℝ => truncationFactor (x.1-Γ.g)*z) hm
    rw [heff]
    simp only [truncatedValue,max_eq_left (sub_pos.mpr hv).le]
    nlinarith [ht]
  · have hw : x.1-Γ.g ≤ 0 := sub_nonpos.mpr (le_of_not_gt hv)
    have hb : effectiveBid x.2 = 0 := le_antisymm
      (hp.2.1.trans (by rw [max_eq_right hw])) (effectiveBid_nonneg x.2)
    simp only [truncatedValue,max_eq_right hw,hb,mul_zero,zero_mul]

theorem integral_inactive_truncated_FOC (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A = Schedule.once (k+1)) (hG : Γ.G = Schedule.once (k+1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ) (hB : PosteriorProposerOptimalAE Γ B)
    (hsym : SymmetricProposersOnPath Γ) (hvalue : PositiveValueAtomless Γ)
    (hatom : PositiveVisibleAtomless Γ) (hinactive : InactiveAbstain Γ)
    (i : Fin m) (weight : ℝ × (Rival i → ℝ) → ℝ) (hw : Measurable weight)
    (hwb : ∀ z, weight z ∈ Icc (0:ℝ) 1)
    (hderiv : ∀ᵐ b ∂(BidScaling.realBidLaw Γ : Measure ℝ), 0 < b →
      HasDerivAt (coverage (k+1) c (by omega)
        (Measure.pi fun _ : Rival i => (BidScaling.realBidLaw Γ : Measure ℝ)))
        ((∫ r, weightedSlope (k+1) (allocation (k+1) c (by omega) r b)
          (weight (b,r)) ∂Measure.pi (fun _ : Rival i => (BidScaling.realBidLaw Γ : Measure ℝ)))/b) b) :
    let p := fun d : UserProfile m (k+1) => dummyProfileMarginal Γ (by omega) d i
    let D := fun d : UserProfile m (k+1) => weightedSlope (k+1) (p d)
      (weight (effectiveBid (d i).1.2,effectiveRivalBids i d))
    (∫ d, profileTruncatedValue Γ d i*D d ∂userProfileLaw Γ) =
      ∫ d, profileEffectiveTruncatedBid Γ d i*(success (k+1) (p d)+D d) ∂userProfileLaw Γ := by
  dsimp only
  let hn : 2 ≤ k+1 := by omega
  let ν := Measure.pi fun _ : Rival i => (BidScaling.realBidLaw Γ : Measure ℝ)
  let T := fun x : ℝ × JointAction (k+1) => truncatedValue (x.1-Γ.g)
  let V := fun x : ℝ × JointAction (k+1) => truncatedBid (x.1-Γ.g) (effectiveBid x.2)
  let p := fun z : (ℝ × JointAction (k+1)) × (Rival i → ℝ) => allocation (k+1) c hn z.2 (effectiveBid z.1.2)
  let D := fun z : (ℝ × JointAction (k+1)) × (Rival i → ℝ) => weightedSlope (k+1) (p z) (weight (effectiveBid z.1.2,z.2))
  let S := fun z : (ℝ × JointAction (k+1)) × (Rival i → ℝ) => success (k+1) (p z)
  have hm : Measurable (fun z : (ℝ × JointAction (k+1)) × (Rival i → ℝ) => (effectiveBid z.1.2,z.2)) :=
    ((measurable_effectiveBid (k+1)).comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd
  have hp : Measurable p := (measurable_allocation_joint hn).comp hm
  have hD : Measurable D := (measurable_weightedSlope (k+1)).comp (hp.prodMk (hw.comp hm))
  have hS : Measurable S := (continuous_success (k+1)).measurable.comp hp
  have hT : Measurable T := measurable_truncatedValue.comp (measurable_fst.sub_const Γ.g)
  have hV : Measurable V := measurable_truncatedBid.comp
    ((measurable_fst.sub_const Γ.g).prodMk ((measurable_effectiveBid (k+1)).comp measurable_snd))
  have hTI : Integrable T (Γ.F ⊗ₘ Γ.σ) :=
    UnitInterval.integrable _ _ hT (fun _ => (truncatedValue_bounds _).1) (fun _ => (truncatedValue_bounds _).2)
  have hVI : Integrable V (Γ.F ⊗ₘ Γ.σ) :=
    UnitInterval.integrable _ _ hV (fun _ => (truncatedBid_bounds _ _).1) (fun _ => (truncatedBid_bounds _ _).2)
  have hDb (z) : D z ∈ Icc (0:ℝ) (((k+1:ℕ):ℝ)^2) :=
    TruncatedFOC.weightedSlope_bounds hn (allocation_bounds hn z.2 (effectiveBid z.1.2)) (hwb _)
  have hSb (z) : S z ∈ Icc (0:ℝ) 1 := by
    have hb := allocation_bounds (c := c) hn z.2 (effectiveBid z.1.2)
    refine ⟨?_,success_le_one (k+1) _ hb.2⟩
    change 0 ≤ 1-(1-p z)^(k+1)
    exact sub_nonneg.mpr (pow_le_one₀ (sub_nonneg.mpr hb.2) (by linarith [hb.1]))
  have hDI (x : ℝ × JointAction (k+1)) : Integrable (fun r => D (x,r)) ν :=
    Integrable.of_bound (hD.comp measurable_prodMk_left).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun r => by
        rw [Real.norm_eq_abs,abs_of_nonneg (hDb _).1]
        exact (hDb _).2)
  have hSI (x : ℝ × JointAction (k+1)) : Integrable (fun r => S (x,r)) ν :=
    Integrable.of_bound (hS.comp measurable_prodMk_left).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun r => by
        rw [Real.norm_eq_abs,abs_of_nonneg (hSb _).1]
        exact (hSb _).2)
  have hleft : Integrable (fun z => T z.1*D z) ((Γ.F ⊗ₘ Γ.σ).prod ν) :=
    (hTI.comp_fst ν).mul_bdd hD.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs,abs_of_nonneg (hDb z).1]
        exact (hDb z).2)
  have hright : Integrable (fun z => V z.1*(S z+D z)) ((Γ.F ⊗ₘ Γ.σ).prod ν) :=
    (hVI.comp_fst ν).mul_bdd (hS.add hD).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs,abs_of_nonneg (add_nonneg (hSb z).1 (hDb z).1)]
        exact add_le_add (hSb z).2 (hDb z).2)
  have hpres := focalAction_effectiveRivals_measurePreserving Γ i
  have htransport (f : (ℝ × JointAction (k+1)) × (Rival i → ℝ) → ℝ) (hf : Measurable f) :
      (∫ d, f ((d i).1,effectiveRivalBids i d) ∂userProfileLaw Γ) =
        ∫ z, f z ∂((Γ.F ⊗ₘ Γ.σ).prod ν) := by
    rw [← hpres.map_eq]
    exact (integral_map hpres.measurable.aemeasurable hf.aestronglyMeasurable).symm
  change (∫ d, T (d i).1*D ((d i).1,effectiveRivalBids i d) ∂userProfileLaw Γ) =
    ∫ d, V (d i).1*(S ((d i).1,effectiveRivalBids i d)+D ((d i).1,effectiveRivalBids i d)) ∂userProfileLaw Γ
  have htleft := htransport (fun z => T z.1*D z) ((hT.comp measurable_fst).mul hD)
  have htright := htransport (fun z => V z.1*(S z+D z)) ((hV.comp measurable_fst).mul (hS.add hD))
  rw [htleft,htright,integral_prod _ hleft,integral_prod _ hright]
  apply integral_congr_ae
  filter_upwards [ae_inactive_truncated_identity Γ hk hc hcm hA hG hu B hB hsym hvalue hatom hinactive i weight hderiv]
    with x hx
  rw [integral_const_mul,integral_const_mul,integral_add (hSI x) (hDI x)]
  exact hx

theorem exists_bounded_inactive_profile_FOC (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A = Schedule.once (k+1)) (hG : Γ.G = Schedule.once (k+1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ) (hB : PosteriorProposerOptimalAE Γ B)
    (hsym : SymmetricProposersOnPath Γ) (hvalue : PositiveValueAtomless Γ)
    (hatom : PositiveVisibleAtomless Γ) (hinactive : InactiveAbstain Γ) :
    let p := dummyProfileMarginal Γ (by omega)
    ∃ weight : UserProfile m (k+1) → Fin m → ℝ,
      (∀ i, Measurable (fun d => weight d i)) ∧
      (∀ d i, weight d i ∈ Icc (0:ℝ) 1) ∧
      (∀ᵐ d ∂userProfileLaw Γ, ∑ i ∈ interiorSet (p d), weight d i ≤ 1) ∧
      (∀ i, (∫ d, profileTruncatedValue Γ d i*
        weightedSlope (k+1) (p d i) (weight d i) ∂userProfileLaw Γ) =
        ∫ d, profileEffectiveTruncatedBid Γ d i*
          (success (k+1) (p d i)+weightedSlope (k+1) (p d i) (weight d i)) ∂userProfileLaw Γ) := by
  dsimp only
  obtain ⟨weight,hw,hwb,_,hderiv,_,hsum⟩ := exists_dummy_profile_weights Γ hk
    (fun b hb => realEffectiveBidLaw_positive_atomless Γ hc hcm hA hG hu B hB hsym hvalue hatom hb)
  refine ⟨fun d i => weight i (effectiveBid (d i).1.2,effectiveRivalBids i d),
    fun i => (hw i).comp (effectiveFocalBid_rivals_measurePreserving Γ i).measurable,
    fun d i => hwb i _,hsum,?_⟩
  intro i
  exact integral_inactive_truncated_FOC Γ hk hc hcm hA hG hu B hB hsym hvalue hatom hinactive i
    (weight i) (hw i) (hwb i) (hderiv i)

end FCAppendix.Bayes
