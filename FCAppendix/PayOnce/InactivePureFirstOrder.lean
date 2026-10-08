import FCAppendix.PayOnce.DummyFirstOrder
import FCAppendix.PayOnce.InactiveEventualPureBids

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel
variable {m c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem ae_inactive_pure_first_order (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A = Schedule.once (k+1)) (hG : Γ.G = Schedule.once (k+1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ) (hB : PosteriorProposerOptimalAE Γ B)
    (hsym : SymmetricProposersOnPath Γ) (hvalue : PositiveValueAtomless Γ)
    (hatom : PositiveVisibleAtomless Γ) (hinactive : InactiveAbstain Γ)
    (b : ℝ → ℝ) (heq : ∀ᵐ z ∂(Γ.F ⊗ₘ Γ.σ), effectiveBid z.2 = b z.1) :
    let Q := coverage (k+1) c (by omega)
      (Measure.pi fun _ : Fin (m-1) => (BidScaling.realBidLaw Γ : Measure ℝ))
    ∀ᵐ v ∂Γ.F, Γ.g < v → 0 < b v ∧
      HasDerivAt Q (deriv Q (b v)) (b v) ∧
      Q (b v) = (v-Γ.g-b v)*deriv Q (b v) := by
  dsimp only
  let i : Fin m := ⟨0,by omega⟩
  have hcard : Fintype.card (Fin (m-1)) = Fintype.card (Rival i) := by
    have hh := card_rival_add_one i
    simp only [Fintype.card_fin]
    omega
  let e : Fin (m-1) ≃ Rival i := Fintype.equivOfCardEq hcard
  have hQ : coverage (k+1) c (by omega)
      (Measure.pi fun _ : Fin (m-1) => (BidScaling.realBidLaw Γ : Measure ℝ)) =
      coverage (k+1) c (by omega)
        (Measure.pi fun _ : Rival i => (BidScaling.realBidLaw Γ : Measure ℝ)) := by
    funext x
    exact integral_allocation_test_equiv e (by omega)
      (BidScaling.realBidLaw Γ : Measure ℝ) x (success (k+1))
  have hf := ae_inactive_payOnce_first_order Γ hk hc hcm hA hG hu B hB hsym
    hvalue hatom hinactive i
  dsimp only at hf
  rw [← hQ] at hf
  have hp := ae_effectiveBid_participation Γ hc hcm hA hG hu B hB hsym hvalue
  have hh := Measure.ae_ae_of_ae_compProd (heq.and (hp.and hf))
  filter_upwards [hh] with v hv hvg
  obtain ⟨a,ha,hpa,hfa⟩ := hv.exists
  have hr := hpa.2.2 hvg
  have heff : effectiveBid a = a.bid := by
    simp only [effectiveBid,hr,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,if_false]
  have hab : a.bid = b v := heff.symm.trans ha
  refine ⟨ha ▸ hpa.1.mpr hvg,?_⟩
  simpa only [hab] using hfa hvg

end FCAppendix.Bayes

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_eventual_pure_first_order
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (b : ℕ → ℝ → ℝ)
    (heq : ∀ᶠ t in atTop, ∀ᵐ z ∂((Γ t).F ⊗ₘ (Γ t).σ), effectiveBid z.2 = b t z.1) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let Q := fun t => coverage (k+1) (C t) hn
      (Measure.pi fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
    ∀ᶠ t in atTop, ∀ᵐ v ∂F, g < v → 0 < b t v ∧
      HasDerivAt (Q t) (deriv (Q t) (b t v)) (b t v) ∧
      Q t (b t v) = (v-g-b t v)*deriv (Q t) (b t v) := by
  dsimp only
  filter_upwards [h.eventually_scarce,heq] with t ht he
  simpa only [h.common_values t,h.common_fee t] using
    ae_inactive_pure_first_order (Γ t) h.proposers_two ht.1 ht.2
      (h.action_schedule t) (h.base_schedule t) (h.users t) (B t) (h.proposers t)
      (h.symmetry t) (h.positive_values_atomless t) (h.visible_atomless t)
      (h.inactive_abstain t) (b t) he

end FCAppendix.Bayes
