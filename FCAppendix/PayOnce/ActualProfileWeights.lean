import FCAppendix.PayOnce.TruncatedFOC
import FCAppendix.PayOnce.FocalProfileTransport
import FCAppendix.PayOnce.ActualFirstOrder

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Filter Topology Set Game
open PayOnce PayOnce.AnalyticalKernel PayOnce.RareSuccessSlope PayOnce.OwnImpact
open scoped ProbabilityTheory BigOperators
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def analyticalProfileMarginal {n : ℕ} (_Γ : FiniteGame m n c Seed)
    (hn : 2 ≤ n) (hcm : c ≤ m) (d : UserProfile m n) (i : Fin m) : ℝ :=
  allocation n c hn (by simpa only [card_rival_add_one] using hcm) (rivalBids i d) (d i).1.2.bid

theorem measurable_analyticalProfileMarginal {n : ℕ} (Γ : FiniteGame m n c Seed)
    (hn : 2 ≤ n) (hcm : c ≤ m) (i : Fin m) :
    Measurable (fun d => analyticalProfileMarginal Γ hn hcm d i) :=
  (measurable_allocation_joint hn _).comp (focalBid_rivalBids_measurePreserving Γ i).measurable

theorem analyticalProfileMarginal_bounds {n : ℕ} (Γ : FiniteGame m n c Seed)
    (hn : 2 ≤ n) (hcm : c ≤ m) (d : UserProfile m n) (i : Fin m) :
    analyticalProfileMarginal Γ hn hcm d i ∈ Icc (0 : ℝ) 1 :=
  allocation_bounds hn _ _ _

theorem exists_actual_profile_weights {k : ℕ} (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hcm : c ≤ m) (hatom : PositiveVisibleAtomless Γ)
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = k+1)
    (hbid : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.bid) :
    let hn : 2 ≤ k+1 := by omega
    let hc : ∀ i : Fin m, c ≤ Fintype.card (Rival i)+1 := fun i => by simpa only [card_rival_add_one] using hcm
    let p := fun (d : UserProfile m (k+1)) (i : Fin m) =>
      allocation (k+1) c hn (hc i) (rivalBids i d) (d i).1.2.bid
    ∃ weight : (i : Fin m) → ℝ × (Rival i → ℝ) → ℝ,
      (∀ i, Measurable (weight i)) ∧
      (∀ i z, weight i z ∈ Icc (0 : ℝ) 1) ∧
      (∀ i z, 1 / (((k+1 : ℕ) : ℝ)^3+1) ≤ 1-weight i z) ∧
      (∀ i, ∀ᵐ b ∂realBidLaw Γ,
        HasDerivAt (coverage (k+1) c hn (hc i) (analyticalRivalLaw Γ i))
          ((∫ rivals, weightedSlope (k+1) (allocation (k+1) c hn (hc i) rivals b)
            (weight i (b,rivals)) ∂analyticalRivalLaw Γ i)/b) b) ∧
      (∀ᵐ d ∂userProfileLaw Γ, ∀ i,
        (d i).1.2.bid * deriv (fun x => success (k+1)
          (allocation (k+1) c hn (hc i) (rivalBids i d) x)) (d i).1.2.bid =
          weightedSlope (k+1) (p d i) (weight i ((d i).1.2.bid, rivalBids i d))) ∧
      (∀ᵐ d ∂userProfileLaw Γ,
        ∑ i ∈ interiorSet (p d), weight i ((d i).1.2.bid, rivalBids i d) ≤ 1) := by
  dsimp only
  let hn : 2 ≤ k+1 := by omega
  let hc : ∀ i : Fin m, c ≤ Fintype.card (Rival i)+1 := fun i => by
    simpa only [card_rival_add_one] using hcm
  let p := fun (d : UserProfile m (k+1)) (i : Fin m) =>
    allocation (k+1) c hn (hc i) (rivalBids i d) (d i).1.2.bid
  letI := nullSingleton_realBidLaw_of_full_routes Γ (by omega) hatom hroute hbid
  have hb := ae_realBidLaw_pos Γ hbid
  choose weight hw hwb hwgap he hd using fun i : Fin m =>
    exists_joint_measurable_weight (ι := Rival i) (realBidLaw Γ) hn (hc i) hb
  have hnorm : ∀ᵐ d ∂userProfileLaw Γ, ∀ i,
      (d i).1.2.bid * deriv (fun x => success (k+1)
        (allocation (k+1) c hn (hc i) (rivalBids i d) x)) (d i).1.2.bid =
        weightedSlope (k+1) (p d i) (weight i ((d i).1.2.bid, rivalBids i d)) := by
    apply ae_all_iff.mpr
    intro i
    exact (focalBid_rivalBids_measurePreserving Γ i).quasiMeasurePreserving.ae (he i)
  refine ⟨weight, hw, hwb, hwgap, ?_, hnorm, ?_⟩
  · intro i
    simpa only [analyticalRivalLaw_eq_pi] using hd i
  · have hmp := measurePreserving_pi (fun _ : Fin m => userLaw Γ)
      (fun _ : Fin m => realBidLaw Γ)
      (fun _ => show MeasurePreserving (fun d : UserDraw (k+1) => d.1.2.bid) (userLaw Γ) (realBidLaw Γ) from
        ⟨measurable_drawBid, rfl⟩)
    have hreg := hmp.quasiMeasurePreserving.ae
      (PayOnce.NullClipping.ae_positive_regularRoot (ι := Fin m) (realBidLaw Γ) hn (by simpa using hcm) hb)
    filter_upwards [hnorm, hreg] with d hnorm hdreg
    obtain ⟨hpos, L, hL, hcap, hclip0, hclip1⟩ := hdreg
    let bids := fun i : Fin m => (d i).1.2.bid
    have hp (i : Fin m) : p d i = CommonList.kernel (k+1) (bids i) L :=
      allocation_eq_kernel hn (hc i) (rivalBids i d) (fun j => hpos j.val) (hpos i) hL
        ((sum_focal_rivals i (fun j => CommonList.kernel (k+1) (bids j) L)).trans hcap)
    have hpeq : p d = fun i => CommonList.kernel (k+1) (bids i) L := funext hp
    have hsum : (∑ i ∈ interiorSet (p d), weight i ((d i).1.2.bid, rivalBids i d)) =
        ∑ i ∈ interiorSet (p d), impactWeight (k+1) bids (p d) i := by
      apply Finset.sum_congr rfl
      intro i hi
      have hip : CommonList.kernel (k+1) (bids i) L ∈ Ioo (0 : ℝ) 1 := by
        simpa only [interiorSet, Finset.mem_filter, Finset.mem_univ, true_and, hp i, mem_Ioo] using hi
      rw [hpeq]
      apply weight_eq_impactWeight_of_derivative hn bids hpos hL hcap i hip hclip0 hclip1 (hc i)
      rw [← hp i]
      exact hnorm i
    rw [hsum]
    exact sum_impactWeight_le_one (k+1) bids (p d)

theorem ae_actual_truncated_identity {k : ℕ} (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hcm : c ≤ m)
    (hA : Γ.A = Schedule.once (k+1)) (hG : Γ.G = Schedule.once (k+1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hatom : PositiveVisibleAtomless Γ)
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = k+1)
    (hbid : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.bid)
    (i : Fin m) (τ : ℝ → ℝ) (weight : ℝ × (Rival i → ℝ) → ℝ)
    (hderiv : ∀ᵐ b ∂realBidLaw Γ,
      HasDerivAt (coverage (k+1) c (by omega) (by simpa only [card_rival_add_one] using hcm)
        (analyticalRivalLaw Γ i))
        ((∫ rivals, weightedSlope (k+1)
          (allocation (k+1) c (by omega) (by simpa only [card_rival_add_one] using hcm) rivals b)
          (weight (b,rivals)) ∂analyticalRivalLaw Γ i)/b) b) :
    let hn : 2 ≤ k+1 := by omega
    let hc : c ≤ Fintype.card (Rival i)+1 := by simpa only [card_rival_add_one] using hcm
    let Q := coverage (k+1) c hn hc (analyticalRivalLaw Γ i)
    let D := fun b => ∫ rivals, weightedSlope (k+1) (allocation (k+1) c hn hc rivals b)
      (weight (b,rivals)) ∂analyticalRivalLaw Γ i
    ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ),
      (τ x.1*(x.1-Γ.g))*D x.2.bid = (τ x.1*x.2.bid)*(Q x.2.bid+D x.2.bid) := by
  dsimp only
  have hfoc := ae_actual_payOnce_first_order Γ hk hcm hA hG hu B hB hsym hatom hroute hbid i
  rw [realBidLaw_eq_action_map] at hderiv
  have hd := ae_of_ae_map ((measurable_bid (k+1)).comp measurable_snd).aemeasurable hderiv
  filter_upwards [hfoc, hd, hbid] with x hfirst hD hb
  simp only [Function.comp_def] at hD
  rw [hD.deriv] at hfirst
  have he := hfirst.2
  have hm := congrArg (fun z : ℝ => z*x.2.bid) he
  field_simp [hb.ne'] at hm
  have ht := congrArg (fun z : ℝ => τ x.1*z) hm
  nlinarith [ht]

theorem integral_actual_truncated_FOC {k : ℕ} (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hcm : c ≤ m)
    (hA : Γ.A = Schedule.once (k+1)) (hG : Γ.G = Schedule.once (k+1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hatom : PositiveVisibleAtomless Γ)
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = k+1)
    (hbid : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.bid)
    (i : Fin m) (τ : ℝ → ℝ) (hτ : Measurable τ)
    (hτw : Integrable (fun x : ℝ × JointAction (k+1) => τ x.1*(x.1-Γ.g)) (Γ.F ⊗ₘ Γ.σ))
    (hτb : Integrable (fun x : ℝ × JointAction (k+1) => τ x.1*x.2.bid) (Γ.F ⊗ₘ Γ.σ))
    (weight : ℝ × (Rival i → ℝ) → ℝ) (hw : Measurable weight)
    (hwb : ∀ z, weight z ∈ Icc (0 : ℝ) 1)
    (hderiv : ∀ᵐ b ∂realBidLaw Γ,
      HasDerivAt (coverage (k+1) c (by omega) (by simpa only [card_rival_add_one] using hcm)
        (analyticalRivalLaw Γ i))
        ((∫ rivals, weightedSlope (k+1)
          (allocation (k+1) c (by omega) (by simpa only [card_rival_add_one] using hcm) rivals b)
          (weight (b,rivals)) ∂analyticalRivalLaw Γ i)/b) b) :
    let p := fun d : UserProfile m (k+1) => analyticalProfileMarginal Γ (by omega) hcm d i
    let D := fun d : UserProfile m (k+1) => weightedSlope (k+1) (p d)
      (weight ((d i).1.2.bid, rivalBids i d))
    (∫ d, (τ (d i).1.1*((d i).1.1-Γ.g))*D d ∂userProfileLaw Γ) =
      ∫ d, (τ (d i).1.1*(d i).1.2.bid)*(success (k+1) (p d)+D d) ∂userProfileLaw Γ := by
  dsimp only
  let hn : 2 ≤ k+1 := by omega
  let hc : c ≤ Fintype.card (Rival i)+1 := by simpa only [card_rival_add_one] using hcm
  let ν := analyticalRivalLaw Γ i
  let T := fun x : ℝ × JointAction (k+1) => τ x.1*(x.1-Γ.g)
  let V := fun x : ℝ × JointAction (k+1) => τ x.1*x.2.bid
  let p := fun z : (ℝ × JointAction (k+1)) × (Rival i → ℝ) => allocation (k+1) c hn hc z.2 z.1.2.bid
  let D := fun z : (ℝ × JointAction (k+1)) × (Rival i → ℝ) => weightedSlope (k+1) (p z) (weight (z.1.2.bid,z.2))
  let S := fun z : (ℝ × JointAction (k+1)) × (Rival i → ℝ) => success (k+1) (p z)
  have hm : Measurable (fun z : (ℝ × JointAction (k+1)) × (Rival i → ℝ) => (z.1.2.bid,z.2)) :=
    ((measurable_bid (k+1)).comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd
  have hp : Measurable p := (measurable_allocation_joint hn hc).comp hm
  have hD : Measurable D := (measurable_weightedSlope (k+1)).comp (hp.prodMk (hw.comp hm))
  have hS : Measurable S := (continuous_success (k+1)).measurable.comp hp
  have hT : Measurable T := (hτ.comp measurable_fst).mul (measurable_fst.sub_const Γ.g)
  have hV : Measurable V := (hτ.comp measurable_fst).mul ((measurable_bid (k+1)).comp measurable_snd)
  have hDb (z) : D z ∈ Icc (0 : ℝ) (((k+1 : ℕ) : ℝ)^2) :=
    TruncatedFOC.weightedSlope_bounds hn (allocation_bounds hn hc z.2 z.1.2.bid) (hwb _)
  have hSb (z) : S z ∈ Icc (0 : ℝ) 1 :=
    success_allocation_bounds hn hc z.2 z.1.2.bid
  have hDI (x : ℝ × JointAction (k+1)) : Integrable (fun rivals => D (x,rivals)) ν :=
    Integrable.of_bound (hD.comp measurable_prodMk_left).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun rivals => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hDb _).1]
        exact (hDb _).2)
  have hSI (x : ℝ × JointAction (k+1)) : Integrable (fun rivals => S (x,rivals)) ν :=
    Integrable.of_bound (hS.comp measurable_prodMk_left).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun rivals => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hSb _).1]
        exact (hSb _).2)
  have hleft : Integrable (fun z => T z.1*D z) ((Γ.F ⊗ₘ Γ.σ).prod ν) :=
    (hτw.comp_fst ν).mul_bdd hD.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hDb z).1]
        exact (hDb z).2)
  have hright : Integrable (fun z => V z.1*(S z+D z)) ((Γ.F ⊗ₘ Γ.σ).prod ν) :=
    (hτb.comp_fst ν).mul_bdd (hS.add hD).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (hSb z).1 (hDb z).1)]
        exact add_le_add (hSb z).2 (hDb z).2)
  have hpres := focalAction_rivalBids_measurePreserving Γ i
  have htransport (f : (ℝ × JointAction (k+1)) × (Rival i → ℝ) → ℝ) (hf : Measurable f) :
      (∫ d, f ((d i).1,rivalBids i d) ∂userProfileLaw Γ) =
        ∫ z, f z ∂((Γ.F ⊗ₘ Γ.σ).prod ν) := by
    rw [← hpres.map_eq]
    exact (integral_map hpres.measurable.aemeasurable hf.aestronglyMeasurable).symm
  change (∫ d, T (d i).1*D ((d i).1,rivalBids i d) ∂userProfileLaw Γ) =
    ∫ d, V (d i).1*(S ((d i).1,rivalBids i d)+D ((d i).1,rivalBids i d)) ∂userProfileLaw Γ
  have htleft := htransport (fun z => T z.1*D z) ((hT.comp measurable_fst).mul hD)
  have htright := htransport (fun z => V z.1*(S z+D z)) ((hV.comp measurable_fst).mul (hS.add hD))
  rw [htleft, htright, integral_prod _ hleft, integral_prod _ hright]
  apply integral_congr_ae
  filter_upwards [ae_actual_truncated_identity Γ hk hcm hA hG hu B hB hsym hatom hroute hbid i τ weight hderiv]
    with x hx
  rw [integral_const_mul, integral_const_mul, integral_add (hSI x) (hDI x)]
  exact hx

end FCAppendix.Bayes
