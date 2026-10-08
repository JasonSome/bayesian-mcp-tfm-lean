import FCAppendix.PayOnce.DummyInterimMean

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel
variable {m c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem ae_type_success_envelope_eq_dummy
    (Γ : FiniteGame m (k+1) c Seed) (hk : 1 ≤ k) (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A=Schedule.once (k+1)) (hG : Γ.G=Schedule.once (k+1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hvalue : PositiveValueAtomless Γ) (hinactive : InactiveAbstain Γ)
    (b : ℝ → ℝ) (heq : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), effectiveBid x.2=b x.1) :
    let Q := coverage (k+1) c (by omega)
      (Measure.pi fun _ : Fin (m-1) => (BidScaling.realBidLaw Γ : Measure ℝ))
    ∀ᵐ v ∂Γ.F, Γ.g<v → ∀ i : Fin m,
      (typeOutcome Γ i v).success=Q (b v) ∧
      (problem Γ i).envelope v=(v-Γ.g-b v)*Q (b v) ∧
      ∀ᵐ a ∂Γ.σ v, a.bid=b v ∧ a.routeCount=k+1 := by
  dsimp only
  have hr := ae_positive_broadcast_or_abstain Γ hc hcm hA hG hu B hB hsym hvalue hinactive
  have hp := ae_effectiveBid_participation Γ hc hcm hA hG hu B hB hsym hvalue
  have ha i := Measure.ae_ae_of_ae_compProd
    ((ae_interim_success_eq_dummy Γ hk hA B hB hsym hr i).and (heq.and hp))
  filter_upwards [ae_all_iff.mpr ha,ae_all_iff.mpr hu] with v hv hbest hvg
  intro i
  have hcard : Fintype.card (Fin (m-1))=Fintype.card (Rival i) := by
    have hh := card_rival_add_one i
    simp only [Fintype.card_fin]
    omega
  let e : Fin (m-1) ≃ Rival i := Fintype.equivOfCardEq hcard
  let Q := coverage (k+1) c (by omega)
    (Measure.pi fun _ : Fin (m-1) => (BidScaling.realBidLaw Γ : Measure ℝ))
  have hQ : Q (b v)=coverage (k+1) c (by omega)
      (Measure.pi fun _ : Rival i => (BidScaling.realBidLaw Γ : Measure ℝ)) (b v) :=
    integral_allocation_test_equiv e (by omega) (BidScaling.realBidLaw Γ : Measure ℝ) (b v) (success (k+1))
  have he : ∀ᵐ a ∂Γ.σ v, a.bid=b v ∧ a.routeCount=k+1 ∧
      ((problem Γ i).outcome a).success=Q (b v) := by
    filter_upwards [hv i] with a ha
    have hfull := ha.2.2.2.2 hvg
    have heff : effectiveBid a=a.bid := by
      simp only [effectiveBid,hfull,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,if_false]
    refine ⟨heff.symm.trans ha.2.1,hfull,?_⟩
    rw [ha.1,ha.2.1,← hQ]
  refine ⟨?_,?_,he.mono fun _ ha => ⟨ha.1,ha.2.1⟩⟩
  · rw [CountLaw.success,typeOutcome_expect]
    change (∫ a, ((problem Γ i).outcome a).success ∂Γ.σ v)=Q (b v)
    rw [integral_congr_ae (he.mono fun _ ha => ha.2.2)]
    simp only [integral_const,probReal_univ,one_smul]
  · obtain ⟨a,ha,hba⟩ := (he.and (hbest i)).exists
    rw [← ((problem Γ i).bestResponse_iff_attains v a).mp hba,payoff_once Γ hA hG,ha.1,ha.2.2]
    ring

end FCAppendix.Bayes

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_eventual_type_success_envelope
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) (b : ℕ → ℝ → ℝ)
    (heq : ∀ᶠ t in atTop, ∀ᵐ z ∂((Γ t).F ⊗ₘ (Γ t).σ), effectiveBid z.2=b t z.1) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let Q := fun t => coverage (k+1) (C t) hn
      (Measure.pi fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
    ∀ᶠ t in atTop, ∀ᵐ v ∂F, g<v → ∀ i : Fin (M t),
      (typeOutcome (Γ t) i v).success=Q t (b t v) ∧
      (problem (Γ t) i).envelope v=(v-g-b t v)*Q t (b t v) ∧
      ∀ᵐ a ∂(Γ t).σ v, a.bid=b t v ∧ a.routeCount=k+1 := by
  dsimp only
  filter_upwards [h.eventually_scarce,heq] with t ht he
  simpa only [h.common_values t,h.common_fee t] using
    ae_type_success_envelope_eq_dummy (Γ t) h.proposers_two ht.1 ht.2 (h.action_schedule t)
      (h.base_schedule t) (h.users t) (B t) (h.proposers t) (h.symmetry t)
      (h.positive_values_atomless t) (h.inactive_abstain t) (b t) he

end FCAppendix.Bayes
