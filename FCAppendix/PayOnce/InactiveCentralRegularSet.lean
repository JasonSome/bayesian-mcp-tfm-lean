import FCAppendix.PayOnce.DummyInterimUtility
import FCAppendix.PayOnce.InactivePureFirstOrder

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def InactiveCentralRegular
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed) (hn : 2 ≤ k+1)
    (g : ℝ) (b : ℕ → ℝ → ℝ) (t : ℕ) (v : ℝ) : Prop :=
  let μ := Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
  let Q := coverage (k+1) (C t) hn μ
  Q (b t v)=(v-g-b t v)*deriv Q (b t v) ∧
  ∀ i : Fin (M t),
    (typeOutcome (Γ t) i v).success=Q (b t v) ∧
    (typeOutcome (Γ t) i v).load=(∫ r, ((k+1:ℕ):ℝ)*allocation (k+1) (C t) hn r (b t v) ∂μ) ∧
    (problem (Γ t) i).envelope v=(v-g-b t v)*Q (b t v) ∧
    ∀ᵐ a ∂(Γ t).σ v, a.bid=b t v ∧ a.routeCount=k+1

theorem payOnce_inactive_central_regular_set
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) (b : ℕ → ℝ → ℝ)
    (heq : ∀ᶠ t in atTop, ∀ᵐ z ∂((Γ t).F ⊗ₘ (Γ t).σ), effectiveBid z.2=b t z.1) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    ∃ A : Set ℝ, (∀ᵐ v ∂F, v ∈ A) ∧
      ∀ᶠ t in atTop, ∀ v ∈ A, g<v → InactiveCentralRegular Γ hn g b t v := by
  dsimp only
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  have he : ∀ᶠ t in atTop, ∀ᵐ v ∂F, g<v → InactiveCentralRegular Γ hn g b t v := by
    filter_upwards [payOnce_inactive_eventual_pure_first_order Γ B F g ρ h b heq,
      payOnce_inactive_eventual_type_success_envelope Γ B F g ρ h b heq,
      payOnce_inactive_eventual_type_mean Γ B F g ρ h b heq] with t hf hs hm
    filter_upwards [hf,hs,hm] with v hfv hsv hmv hvg
    refine ⟨(hfv hvg).2.2,fun i => ⟨(hsv hvg i).1,?_,(hsv hvg i).2⟩⟩
    rw [integral_const_mul]
    have hh := (div_eq_iff (by positivity : (((k+1:ℕ):ℝ)) ≠ 0)).mp (hmv i)
    simpa only [mul_comm] using hh
  obtain ⟨T,hT⟩ := eventually_atTop.mp he
  let A := {v | ∀ t, T≤t → g<v → InactiveCentralRegular Γ hn g b t v}
  have hA : ∀ᵐ v ∂F, v ∈ A :=
    ae_all_iff.mpr fun t => ae_all_iff.mpr fun ht => hT t ht
  refine ⟨A,hA,?_⟩
  filter_upwards [eventually_ge_atTop T] with t ht v hv hvg
  exact hv t ht hvg

end FCAppendix.Bayes
