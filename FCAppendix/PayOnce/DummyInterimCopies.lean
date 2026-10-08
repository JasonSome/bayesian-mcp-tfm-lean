import FCAppendix.PayOnce.DummyInterimMean

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel
variable {m c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem ae_typeOutcome_countMass_eq_dummy_population (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hA : Γ.A = Schedule.once (k+1)) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = 0 ∨
      (0 < x.2.bid ∧ x.2.routeCount = k+1))
    (b : ℝ → ℝ) (heq : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), effectiveBid x.2 = b x.1) :
    ∀ᵐ v ∂Γ.F, ∀ i : Fin m, ∀ j : ℕ, (typeOutcome Γ i v).prob (fun r => r.val=j) =
      ∫ rivals : Fin (m-1) → ℝ, ManyProposers.binomialMass (k+1)
        (allocation (k+1) c (by omega) rivals (b v)) j
        ∂Measure.pi (fun _ : Fin (m-1) => (BidScaling.realBidLaw Γ : Measure ℝ)) := by
  classical
  have ha i j := Measure.ae_ae_of_ae_compProd
    ((ae_interim_countMass_eq_dummy Γ hk hA B hB hsym hroute i j).and heq)
  filter_upwards [ae_all_iff.mpr fun i => ae_all_iff.mpr (ha i)] with v hv
  intro i j
  have he : ∀ᵐ a ∂Γ.σ v, ((problem Γ i).outcome a).prob (fun r => r.val=j) =
      ∫ rivals : Rival i → ℝ, ManyProposers.binomialMass (k+1)
        (allocation (k+1) c (by omega) rivals (b v)) j
        ∂Measure.pi (fun _ : Rival i => (BidScaling.realBidLaw Γ : Measure ℝ)) := by
    filter_upwards [hv i j] with a ha
    simpa only [ha.2] using ha.1
  rw [FiniteLaw.prob_eq_expect,typeOutcome_expect]
  simp_rw [← FiniteLaw.prob_eq_expect]
  change (∫ a, ((problem Γ i).outcome a).prob (fun r => r.val=j) ∂Γ.σ v) = _
  rw [integral_congr_ae he,integral_const,probReal_univ,one_smul]
  have hcard : Fintype.card (Fin (m-1)) = Fintype.card (Rival i) := by
    have hh := card_rival_add_one i
    simp only [Fintype.card_fin]
    omega
  let e : Fin (m-1) ≃ Rival i := Fintype.equivOfCardEq hcard
  exact (integral_allocation_test_equiv e (by omega) (BidScaling.realBidLaw Γ : Measure ℝ) (b v)
    (fun p => ManyProposers.binomialMass (k+1) p j)).symm

end FCAppendix.Bayes

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_eventual_type_countMass
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (b : ℕ → ℝ → ℝ)
    (heq : ∀ᶠ t in atTop, ∀ᵐ z ∂((Γ t).F ⊗ₘ (Γ t).σ), effectiveBid z.2 = b t z.1) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    ∀ᶠ t in atTop, ∀ᵐ v ∂F, ∀ i : Fin (M t), ∀ j : ℕ,
      (typeOutcome (Γ t) i v).prob (fun r => r.val=j) =
      ∫ rivals : Fin (M t-1) → ℝ, ManyProposers.binomialMass (k+1)
        (allocation (k+1) (C t) hn rivals (b t v)) j
        ∂Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)) := by
  dsimp only
  filter_upwards [h.eventually_scarce,heq] with t ht he
  have hr := ae_positive_broadcast_or_abstain (Γ t) ht.1 ht.2 (h.action_schedule t)
    (h.base_schedule t) (h.users t) (B t) (h.proposers t) (h.symmetry t)
    (h.positive_values_atomless t) (h.inactive_abstain t)
  simpa only [h.common_values t] using ae_typeOutcome_countMass_eq_dummy_population (Γ t) h.proposers_two
    (h.action_schedule t) (B t) (h.proposers t) (h.symmetry t) hr (b t) he

end FCAppendix.Bayes
