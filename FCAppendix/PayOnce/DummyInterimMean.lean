import FCAppendix.PayOnce.DummyInterimTransport
import FCAppendix.PayOnce.InactiveEventualPureBids

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel
variable {m c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem ae_interim_load_eq_dummy (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hA : Γ.A = Schedule.once (k+1)) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = 0 ∨
      (0 < x.2.bid ∧ x.2.routeCount = k+1)) (i : Fin m) :
    ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), ((problem Γ i).outcome x.2).load =
      ((k+1:ℕ):ℝ)*(∫ rivals, allocation (k+1) c (by omega) rivals (effectiveBid x.2)
        ∂Measure.pi (fun _ : Rival i => (BidScaling.realBidLaw Γ : Measure ℝ))) := by
  have hp := (ae_profileCountLaw_eq_dummy_binomial Γ hk hA B hB hsym hroute).mono fun d hd =>
    congrArg (fun μ : CountLaw (k+1) => μ.load) (hd i)
  simp only [IndependentCounts.binomial_load] at hp
  have hpres : MeasurePreserving (fun z : UserDraw (k+1) × UserProfile m (k+1) =>
      Function.update z.2 i z.1) ((userLaw Γ).prod (userProfileLaw Γ)) (userProfileLaw Γ) :=
    ⟨Resample.measurable_update_pair i,Resample.map_update_eq (userLaw Γ) i⟩
  have hup := Measure.ae_ae_of_ae_prod (hpres.quasiMeasurePreserving.ae hp)
  have hx := Measure.ae_ae_of_ae_prod hup
  filter_upwards [hx] with x hx
  rw [CountLaw.load,interim_expect_eq_profile_update Γ i x]
  have he : ∀ᵐ r ∂permLaw (k+1),
      (∫ d, (profileCountLaw Γ (Function.update d i (x,r)) i).load ∂userProfileLaw Γ) =
      ((k+1:ℕ):ℝ)*(∫ rivals, allocation (k+1) c (by omega) rivals (effectiveBid x.2)
        ∂Measure.pi (fun _ : Rival i => (BidScaling.realBidLaw Γ : Measure ℝ))) := by
    filter_upwards [hx] with r hr
    rw [← integral_const_mul,← (effectiveRivalBids_measurePreserving Γ i).map_eq]
    have hm : Measurable (fun rivals : Rival i → ℝ => ((k+1:ℕ):ℝ)*
        allocation (k+1) c (by omega) rivals (effectiveBid x.2)) :=
      (measurable_allocation_fixed_bid (by omega) _).const_mul _
    rw [integral_map (measurable_effectiveRivalBids i).aemeasurable hm.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [hr] with d hd
    rw [hd]
    apply congrArg (fun p : ℝ => ((k+1:ℕ):ℝ)*p)
    unfold profileMarginal effectiveRivalBids
    simp only [Function.update_self]
    congr 1
    funext l
    rw [Function.update_of_ne l.property]
  change (∫ r, ∫ d, (profileCountLaw Γ (Function.update d i (x,r)) i).load
    ∂userProfileLaw Γ ∂permLaw (k+1)) = _
  rw [integral_congr_ae he]
  simp only [integral_const,probReal_univ,one_smul]

theorem ae_typeOutcome_mean_eq_dummy (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hA : Γ.A = Schedule.once (k+1)) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = 0 ∨
      (0 < x.2.bid ∧ x.2.routeCount = k+1))
    (b : ℝ → ℝ) (heq : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), effectiveBid x.2 = b x.1) :
    ∀ᵐ v ∂Γ.F, ∀ i : Fin m, (typeOutcome Γ i v).load/((k+1:ℕ):ℝ) =
      ∫ rivals : Fin (m-1) → ℝ, allocation (k+1) c (by omega) rivals (b v)
        ∂Measure.pi (fun _ : Fin (m-1) => (BidScaling.realBidLaw Γ : Measure ℝ)) := by
  have ha i := Measure.ae_ae_of_ae_compProd ((ae_interim_load_eq_dummy Γ hk hA B hB hsym hroute i).and heq)
  filter_upwards [ae_all_iff.mpr ha] with v hv
  intro i
  have he : ∀ᵐ a ∂Γ.σ v, ((problem Γ i).outcome a).load =
      ((k+1:ℕ):ℝ)*(∫ rivals : Rival i → ℝ, allocation (k+1) c (by omega) rivals (b v)
        ∂Measure.pi (fun _ : Rival i => (BidScaling.realBidLaw Γ : Measure ℝ))) := by
    filter_upwards [hv i] with a ha
    simpa only [ha.2] using ha.1
  rw [CountLaw.load,typeOutcome_expect]
  change (∫ a, ((problem Γ i).outcome a).load ∂Γ.σ v)/((k+1:ℕ):ℝ) = _
  rw [integral_congr_ae he,integral_const,probReal_univ,one_smul,
    mul_div_cancel_left₀ _ (by positivity : (((k+1:ℕ):ℝ)) ≠ 0)]
  have hcard : Fintype.card (Fin (m-1)) = Fintype.card (Rival i) := by
    have hh := card_rival_add_one i
    simp only [Fintype.card_fin]
    omega
  let e : Fin (m-1) ≃ Rival i := Fintype.equivOfCardEq hcard
  exact (integral_allocation_test_equiv e (by omega)
    (BidScaling.realBidLaw Γ : Measure ℝ) (b v) id).symm

end FCAppendix.Bayes

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_eventual_type_mean
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (b : ℕ → ℝ → ℝ)
    (heq : ∀ᶠ t in atTop, ∀ᵐ z ∂((Γ t).F ⊗ₘ (Γ t).σ), effectiveBid z.2 = b t z.1) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    ∀ᶠ t in atTop, ∀ᵐ v ∂F, ∀ i : Fin (M t), (typeOutcome (Γ t) i v).load/((k+1:ℕ):ℝ) =
      ∫ rivals : Fin (M t-1) → ℝ, allocation (k+1) (C t) hn rivals (b t v)
        ∂Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)) := by
  dsimp only
  filter_upwards [h.eventually_scarce,heq] with t ht he
  have hr := ae_positive_broadcast_or_abstain (Γ t) ht.1 ht.2 (h.action_schedule t)
    (h.base_schedule t) (h.users t) (B t) (h.proposers t) (h.symmetry t)
    (h.positive_values_atomless t) (h.inactive_abstain t)
  simpa only [h.common_values t] using ae_typeOutcome_mean_eq_dummy (Γ t) h.proposers_two
    (h.action_schedule t) (B t) (h.proposers t) (h.symmetry t) hr (b t) he

end FCAppendix.Bayes
