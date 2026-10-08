import FCAppendix.PayOnce.DummyInterimTransport
import FCAppendix.PayOnce.DummyWeightedDerivative
import FCAppendix.PayOnce.SupportedFOC

namespace FCAppendix.PayOnce.SupportedFOC
open MeasureTheory Filter Topology Set

theorem nullSingleton_positive_restrict (G : Measure ℝ)
    (hatom : ∀ b : ℝ, 0 < b → G {b} = 0) : NullSingletonClass (G.restrict (Ioi 0)) := by
  constructor
  intro b
  rw [Measure.restrict_apply (measurableSet_singleton b)]
  by_cases hb : 0 < b
  · rw [Set.singleton_inter_of_mem (show b ∈ Ioi (0:ℝ) from hb)]
    exact hatom b hb
  · rw [Set.singleton_inter_of_notMem (show b ∉ Ioi (0:ℝ) from hb),measure_empty]

theorem ae_positive_two_sided_accumulation (G : Measure ℝ)
    (hatom : ∀ b : ℝ, 0 < b → G {b} = 0) {S : Set ℝ}
    (hS : ∀ᵐ b ∂G, 0 < b → b ∈ S) :
    ∀ᵐ b ∂G, 0 < b → (𝓝[S ∩ Iio b] b).NeBot ∧ (𝓝[S ∩ Ioi b] b).NeBot := by
  letI := nullSingleton_positive_restrict G hatom
  have hh : ∀ᵐ b ∂G.restrict (Ioi 0), b ∈ S := (ae_restrict_iff' measurableSet_Ioi).mpr hS
  exact (ae_restrict_iff' measurableSet_Ioi).mp (ae_two_sided_accumulation _ hh)

end FCAppendix.PayOnce.SupportedFOC

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set
open PayOnce PayOnce.CompactifiedBidLaws
variable {m c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem ae_dummy_payOnce_first_order (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hA : Γ.A = Schedule.once (k+1)) (hG : Γ.G = Schedule.once (k+1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ) (hB : PosteriorProposerOptimalAE Γ B)
    (hsym : SymmetricProposersOnPath Γ)
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = 0 ∨ (0 < x.2.bid ∧ x.2.routeCount = k+1))
    (hatom : ∀ b : ℝ, 0 < b → (BidScaling.realBidLaw Γ : Measure ℝ) {b} = 0) (i : Fin m) :
    let Q := DummyKernel.coverage (k+1) c (by omega)
      (Measure.pi fun _ : Rival i => (BidScaling.realBidLaw Γ : Measure ℝ))
    ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < effectiveBid x.2 →
      HasDerivAt Q (deriv Q x.2.bid) x.2.bid ∧
      Q x.2.bid = (x.1-Γ.g-x.2.bid)*deriv Q x.2.bid := by
  dsimp only
  let Q := DummyKernel.coverage (k+1) c (by omega)
    (Measure.pi fun _ : Rival i => (BidScaling.realBidLaw Γ : Measure ℝ))
  obtain ⟨S,_,hS,hposS,hagree⟩ := exists_common_dummy_agreement_set Γ hk hA B hB hsym hroute i
  have hside := SupportedFOC.ae_positive_two_sided_accumulation
    (BidScaling.realBidLaw Γ : Measure ℝ) hatom hS
  have hderiv := DummyKernel.ae_hasDerivAt_coverage (ι := Rival i) (c := c)
    (BidScaling.realBidLaw Γ : Measure ℝ) hatom (by omega : 2 ≤ k+1)
  rw [realEffectiveBidLaw_eq_action_map] at hS hside hderiv
  have hS' := ae_of_ae_map ((measurable_effectiveBid (k+1)).comp measurable_snd).aemeasurable hS
  have hside' := ae_of_ae_map ((measurable_effectiveBid (k+1)).comp measurable_snd).aemeasurable hside
  have hderiv' := ae_of_ae_map ((measurable_effectiveBid (k+1)).comp measurable_snd).aemeasurable hderiv
  filter_upwards [hS',hside',hderiv',hroute,ae_bestResponse_compProd Γ hu i]
    with x hx hs hd hr hbest hpos
  have hfull : x.2.routeCount = k+1 := by
    rcases hr with hz | hp
    · simp only [effectiveBid,hz,if_true] at hpos
      exact (lt_irrefl _ hpos).elim
    · exact hp.2
  have heff : effectiveBid x.2 = x.2.bid := by
    simp only [effectiveBid,hfull,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,if_false]
  have hxS : x.2.bid ∈ S := heff ▸ hx hpos
  have hsideS := hs hpos
  simp only [Function.comp_def,heff] at hsideS
  have hQ : HasDerivAt Q (deriv Q x.2.bid) x.2.bid := by
    simpa only [Function.comp_def,← realEffectiveBidLaw_eq_action_map,heff] using hd hpos
  refine ⟨hQ,?_⟩
  apply SupportedFOC.payOnce_first_order_condition hQ hsideS.1 hsideS.2
  intro b hbS
  let a := fullBid (k+1) b (hposS b hbS).le
  have ha : a.bid = b := rfl
  have har : a.routeCount = k+1 := rfl
  have hqa := hagree b hbS a ha har
  have hqx := hagree x.2.bid hxS x.2 rfl hfull
  have hcmp := hbest a
  rw [payoff_once Γ hA hG,payoff_once Γ hA hG,hqa,hqx,ha] at hcmp
  change (x.1-b-Γ.g)*Q b ≤ (x.1-x.2.bid-Γ.g)*Q x.2.bid at hcmp
  convert hcmp using 1 <;> ring

theorem ae_inactive_payOnce_first_order (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A = Schedule.once (k+1)) (hG : Γ.G = Schedule.once (k+1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ) (hB : PosteriorProposerOptimalAE Γ B)
    (hsym : SymmetricProposersOnPath Γ) (hvalue : PositiveValueAtomless Γ)
    (hatom : PositiveVisibleAtomless Γ) (hinactive : InactiveAbstain Γ) (i : Fin m) :
    let Q := DummyKernel.coverage (k+1) c (by omega)
      (Measure.pi fun _ : Rival i => (BidScaling.realBidLaw Γ : Measure ℝ))
    ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), Γ.g < x.1 →
      HasDerivAt Q (deriv Q x.2.bid) x.2.bid ∧
      Q x.2.bid = (x.1-Γ.g-x.2.bid)*deriv Q x.2.bid := by
  have hr := ae_positive_broadcast_or_abstain Γ hc hcm hA hG hu B hB hsym hvalue hinactive
  have hf := ae_dummy_payOnce_first_order Γ hk hA hG hu B hB hsym hr
    (fun b hb => realEffectiveBidLaw_positive_atomless Γ hc hcm hA hG hu B hB hsym hvalue hatom hb) i
  filter_upwards [hf,ae_effectiveBid_participation Γ hc hcm hA hG hu B hB hsym hvalue]
    with x hx hp hv
  exact hx (hp.1.mpr hv)

end FCAppendix.Bayes

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set
open PayOnce PayOnce.CompactifiedBidLaws
variable {m c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem ae_inactive_payOnce_weighted_first_order (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A = Schedule.once (k+1)) (hG : Γ.G = Schedule.once (k+1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ) (hB : PosteriorProposerOptimalAE Γ B)
    (hsym : SymmetricProposersOnPath Γ) (hvalue : PositiveValueAtomless Γ)
    (hatom : PositiveVisibleAtomless Γ) (hinactive : InactiveAbstain Γ) (i : Fin m) :
    let hn : 2 ≤ k+1 := by omega
    let μ := Measure.pi fun _ : Rival i => (BidScaling.realBidLaw Γ : Measure ℝ)
    let p := DummyKernel.allocation (k+1) c hn
    let Q := DummyKernel.coverage (k+1) c hn μ
    ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), Γ.g < x.1 → ∃ weight : (Rival i → ℝ) → ℝ,
      Measurable weight ∧ (∀ r, weight r ∈ Icc (0:ℝ) 1) ∧
      (∀ r, 1/(((k+1:ℕ):ℝ)^3+1) ≤ 1-weight r) ∧
      HasDerivAt Q
        ((∫ r, RareSuccessSlope.weightedSlope (k+1) (p r x.2.bid) (weight r) ∂μ)/x.2.bid) x.2.bid ∧
      Q x.2.bid = (x.1-Γ.g-x.2.bid)*
        ((∫ r, RareSuccessSlope.weightedSlope (k+1) (p r x.2.bid) (weight r) ∂μ)/x.2.bid) := by
  dsimp only
  have ha b hb := realEffectiveBidLaw_positive_atomless Γ hc hcm hA hG hu B hB hsym hvalue hatom (b := b) hb
  have hreg := DummyKernel.ae_regularClearing (ι := Rival i) (c := c)
    (BidScaling.realBidLaw Γ : Measure ℝ) ha (by omega : 2 ≤ k+1)
  rw [realEffectiveBidLaw_eq_action_map] at hreg
  have hr := ae_of_ae_map ((measurable_effectiveBid (k+1)).comp measurable_snd).aemeasurable hreg
  have hf := ae_inactive_payOnce_first_order Γ hk hc hcm hA hG hu B hB hsym hvalue hatom hinactive i
  filter_upwards [hr,hf,ae_effectiveBid_participation Γ hc hcm hA hG hu B hB hsym hvalue]
    with x hx hf hp hv
  have hfull := hp.2.2 hv
  have heff : effectiveBid x.2 = x.2.bid := by
    simp only [effectiveBid,hfull,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,if_false]
  have hpos := hp.1.mpr hv
  have hxb : 0 < x.2.bid := heff ▸ hpos
  have hrr : ∀ᵐ r ∂Measure.pi (fun _ : Rival i => (BidScaling.realBidLaw Γ : Measure ℝ)),
      DummyKernel.RegularClearing (k+1) c r x.2.bid := by
    simpa only [Function.comp_def,← realEffectiveBidLaw_eq_action_map,heff] using hx hpos
  obtain ⟨weight,hw,hbound,hgap,_,hD⟩ :=
    DummyKernel.exists_measurable_weight_coverage_derivative (by omega : 2 ≤ k+1) _ hxb hrr
  exact ⟨weight,hw,hbound,hgap,hD,by simpa only [hD.deriv] using (hf hv).2⟩

end FCAppendix.Bayes
