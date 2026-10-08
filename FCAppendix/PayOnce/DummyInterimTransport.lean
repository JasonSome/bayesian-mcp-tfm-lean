import FCAppendix.PayOnce.DummyInterimKernel

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set
open PayOnce PayOnce.CompactifiedBidLaws
variable {m c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem ae_interim_countMass_eq_dummy (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hA : Γ.A = Schedule.once (k+1)) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = 0 ∨ (0 < x.2.bid ∧ x.2.routeCount = k+1))
    (i : Fin m) (j : ℕ) :
    ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), ((problem Γ i).outcome x.2).prob (fun r => r.val = j) =
      ∫ rivals, ManyProposers.binomialMass (k+1)
        (DummyKernel.allocation (k+1) c (by omega) rivals (effectiveBid x.2)) j
          ∂Measure.pi (fun _ : Rival i => (BidScaling.realBidLaw Γ : Measure ℝ)) := by
  classical
  have hp := (ae_profileCountLaw_eq_dummy_binomial Γ hk hA B hB hsym hroute).mono fun d hd =>
    congrArg (fun μ : CountLaw (k+1) => μ.prob (fun r => r.val = j)) (hd i)
  simp only [ManyProposers.binomial_prob_eq_binomialMass] at hp
  have hpres : MeasurePreserving (fun z : UserDraw (k+1) × UserProfile m (k+1) =>
      Function.update z.2 i z.1) ((userLaw Γ).prod (userProfileLaw Γ)) (userProfileLaw Γ) :=
    ⟨Resample.measurable_update_pair i,Resample.map_update_eq (userLaw Γ) i⟩
  have hup := Measure.ae_ae_of_ae_prod (hpres.quasiMeasurePreserving.ae hp)
  have hx := Measure.ae_ae_of_ae_prod hup
  filter_upwards [hx] with x hx
  rw [FiniteLaw.prob_eq_expect,interim_expect_eq_profile_update Γ i x]
  have he : ∀ᵐ r ∂permLaw (k+1),
      (∫ d, (profileCountLaw Γ (Function.update d i (x,r)) i).expect
        (fun s => if s.val = j then (1:ℝ) else 0) ∂userProfileLaw Γ) =
      ∫ rivals, ManyProposers.binomialMass (k+1)
        (DummyKernel.allocation (k+1) c (by omega) rivals (effectiveBid x.2)) j
          ∂Measure.pi (fun _ : Rival i => (BidScaling.realBidLaw Γ : Measure ℝ)) := by
    filter_upwards [hx] with r hr
    rw [← (effectiveRivalBids_measurePreserving Γ i).map_eq]
    have hm : Measurable (fun rivals : Rival i → ℝ => ManyProposers.binomialMass (k+1)
        (DummyKernel.allocation (k+1) c (by omega) rivals (effectiveBid x.2)) j) :=
      (ManyProposers.continuous_binomialMass (k+1) j).measurable.comp
        (DummyKernel.measurable_allocation_fixed_bid (by omega) _)
    rw [integral_map (measurable_effectiveRivalBids i).aemeasurable hm.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [hr] with d hd
    rw [← FiniteLaw.prob_eq_expect,hd]
    apply congrArg (fun p => ManyProposers.binomialMass (k+1) p j)
    unfold DummyKernel.profileMarginal effectiveRivalBids
    simp only [Function.update_self]
    congr 1
    funext l
    rw [Function.update_of_ne l.property]
  rw [integral_congr_ae he]
  simp only [integral_const,probReal_univ,one_smul]

theorem ae_interim_success_eq_dummy (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hA : Γ.A = Schedule.once (k+1)) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = 0 ∨ (0 < x.2.bid ∧ x.2.routeCount = k+1))
    (i : Fin m) :
    ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), ((problem Γ i).outcome x.2).success =
      DummyKernel.coverage (k+1) c (by omega)
        (Measure.pi fun _ : Rival i => (BidScaling.realBidLaw Γ : Measure ℝ)) (effectiveBid x.2) := by
  classical
  have hp := (ae_profileCountLaw_eq_dummy_binomial Γ hk hA B hB hsym hroute).mono fun d hd =>
    congrArg (fun μ : CountLaw (k+1) => μ.success) (hd i)
  simp only [IndependentCounts.binomial_success] at hp
  have hpres : MeasurePreserving (fun z : UserDraw (k+1) × UserProfile m (k+1) =>
      Function.update z.2 i z.1) ((userLaw Γ).prod (userProfileLaw Γ)) (userProfileLaw Γ) :=
    ⟨Resample.measurable_update_pair i,Resample.map_update_eq (userLaw Γ) i⟩
  have hup := Measure.ae_ae_of_ae_prod (hpres.quasiMeasurePreserving.ae hp)
  have hx := Measure.ae_ae_of_ae_prod hup
  filter_upwards [hx] with x hx
  rw [interim_success_eq_profile_update Γ i x]
  have he : ∀ᵐ r ∂permLaw (k+1),
      (∫ d, (profileCountLaw Γ (Function.update d i (x,r)) i).success ∂userProfileLaw Γ) =
      DummyKernel.coverage (k+1) c (by omega)
        (Measure.pi fun _ : Rival i => (BidScaling.realBidLaw Γ : Measure ℝ)) (effectiveBid x.2) := by
    filter_upwards [hx] with r hr
    unfold DummyKernel.coverage
    rw [← (effectiveRivalBids_measurePreserving Γ i).map_eq]
    have hm : Measurable (fun rivals : Rival i → ℝ => success (k+1)
        (DummyKernel.allocation (k+1) c (by omega) rivals (effectiveBid x.2))) :=
      (show Continuous (success (k+1)) from by unfold success; fun_prop).measurable.comp
        (DummyKernel.measurable_allocation_fixed_bid (by omega) _)
    rw [integral_map (measurable_effectiveRivalBids i).aemeasurable hm.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [hr] with d hd
    rw [hd]
    apply congrArg (success (k+1))
    unfold DummyKernel.profileMarginal effectiveRivalBids
    simp only [Function.update_self]
    congr 1
    funext l
    rw [Function.update_of_ne l.property]
  rw [integral_congr_ae he]
  simp only [integral_const,probReal_univ,one_smul]

end FCAppendix.Bayes

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set
open PayOnce PayOnce.CompactifiedBidLaws
variable {m N c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem ae_typeOutcome_countMass_eq_dummy (Γ : FiniteGame (N+1) (k+1) c Seed)
    (hk : 1 ≤ k) (hA : Γ.A = Schedule.once (k+1)) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = 0 ∨ (0 < x.2.bid ∧ x.2.routeCount = k+1))
    (b : ℝ → ℝ) (heq : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), effectiveBid x.2 = b x.1) (j : ℕ) :
    ∀ᵐ v ∂Γ.F, ∀ i : Fin (N+1), (typeOutcome Γ i v).prob (fun r => r.val = j) =
      ∫ rivals : Fin N → ℝ, ManyProposers.binomialMass (k+1)
        (DummyKernel.allocation (k+1) c (by omega) rivals (b v)) j
          ∂Measure.pi (fun _ : Fin N => (BidScaling.realBidLaw Γ : Measure ℝ)) := by
  classical
  have ha i : ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂Γ.σ v,
      ((problem Γ i).outcome a).prob (fun r => r.val = j) =
        ∫ rivals : Rival i → ℝ, ManyProposers.binomialMass (k+1)
          (DummyKernel.allocation (k+1) c (by omega) rivals (b v)) j
            ∂Measure.pi (fun _ : Rival i => (BidScaling.realBidLaw Γ : Measure ℝ)) := by
    have hx : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ),
        ((problem Γ i).outcome x.2).prob (fun r => r.val = j) =
          ∫ rivals : Rival i → ℝ, ManyProposers.binomialMass (k+1)
            (DummyKernel.allocation (k+1) c (by omega) rivals (b x.1)) j
              ∂Measure.pi (fun _ : Rival i => (BidScaling.realBidLaw Γ : Measure ℝ)) := by
      filter_upwards [ae_interim_countMass_eq_dummy Γ hk hA B hB hsym hroute i j,heq]
        with x hx hb
      simpa only [hb] using hx
    exact Measure.ae_ae_of_ae_compProd hx
  filter_upwards [ae_all_iff.mpr ha] with v hv
  intro i
  rw [FiniteLaw.prob_eq_expect,typeOutcome_expect]
  simp_rw [← FiniteLaw.prob_eq_expect]
  have hconst := integral_congr_ae (hv i)
  rw [integral_const,probReal_univ,one_smul] at hconst
  change (∫ a, ((problem Γ i).outcome a).prob (fun r => r.val = j) ∂Γ.σ v) = _
  rw [hconst]
  have hcard : Fintype.card (Fin N) = Fintype.card (Rival i) := by
    have hh := card_rival_add_one i
    simp only [Fintype.card_fin]
    omega
  let e : Fin N ≃ Rival i := Fintype.equivOfCardEq hcard
  exact (DummyKernel.integral_allocation_test_equiv e (by omega)
    (BidScaling.realBidLaw Γ : Measure ℝ) (b v)
    (fun p => ManyProposers.binomialMass (k+1) p j)).symm

theorem exists_common_dummy_agreement_set (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hA : Γ.A = Schedule.once (k+1)) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = 0 ∨ (0 < x.2.bid ∧ x.2.routeCount = k+1))
    (i : Fin m) :
    let Q := DummyKernel.coverage (k+1) c (by omega)
      (Measure.pi fun _ : Rival i => (BidScaling.realBidLaw Γ : Measure ℝ))
    ∃ S : Set ℝ, MeasurableSet S ∧
      (∀ᵐ b ∂(BidScaling.realBidLaw Γ : Measure ℝ), 0 < b → b ∈ S) ∧
      (∀ b ∈ S, 0 < b) ∧
      ∀ b ∈ S, ∀ a : JointAction (k+1), a.bid = b → a.routeCount = k+1 →
        ((problem Γ i).outcome a).success = Q b := by
  dsimp only
  let Q := DummyKernel.coverage (k+1) c (by omega)
    (Measure.pi fun _ : Rival i => (BidScaling.realBidLaw Γ : Measure ℝ))
  let S := {b : ℝ | 0 < b ∧ ((problem Γ i).outcome (safeFullBid (k+1) b)).success = Q b}
  have hm : MeasurableSet S := (measurableSet_lt measurable_const measurable_id).inter
    (measurableSet_eq_fun ((measurable_success Γ i).comp (measurable_safeFullBid (k+1)))
      (DummyKernel.measurable_coverage _ _))
  have hae : ∀ᵐ b ∂(BidScaling.realBidLaw Γ : Measure ℝ), 0 < b → b ∈ S := by
    rw [realEffectiveBidLaw_eq_action_map]
    have hms : MeasurableSet {b : ℝ | 0 < b → b ∈ S} := by
      convert (measurableSet_Ioi (a := (0:ℝ))).compl.union hm using 1
      ext b
      simp only [mem_setOf_eq,mem_union,mem_compl_iff,mem_Ioi,imp_iff_not_or]
    apply (ae_map_iff ((measurable_effectiveBid (k+1)).comp measurable_snd).aemeasurable hms).mpr
    filter_upwards [ae_interim_success_eq_dummy Γ hk hA B hB hsym hroute i,hroute] with x hx hr hb
    change 0 < effectiveBid x.2 at hb
    have hfull : x.2.routeCount = k+1 := by
      rcases hr with hz | hp
      · simp only [effectiveBid,hz,if_true] at hb
        exact (lt_irrefl _ hb).elim
      · exact hp.2
    have heff : effectiveBid x.2 = x.2.bid := by
      simp only [effectiveBid,hfull,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,if_false]
    refine ⟨hb,?_⟩
    change ((problem Γ i).outcome (safeFullBid (k+1) (effectiveBid x.2))).success = Q (effectiveBid x.2)
    rw [heff,safeFullBid_eq_of_fullRoute x.2 hfull]
    simpa only [heff] using hx
  refine ⟨S,hm,hae,fun b hb => hb.1,?_⟩
  intro b hb a hab har
  have he : safeFullBid (k+1) b = a := hab ▸ safeFullBid_eq_of_fullRoute a har
  exact he ▸ hb.2

end FCAppendix.Bayes
