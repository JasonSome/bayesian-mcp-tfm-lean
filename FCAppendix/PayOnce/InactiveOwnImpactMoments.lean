import FCAppendix.PayOnce.DummyGoodEventImpact
import FCAppendix.PayOnce.InactivePriceConcentration
import FCAppendix.PayOnce.DummyFixedFocalRegularity

namespace FCAppendix.Probability
open MeasureTheory Set

theorem unitInterval_power_moment_le_of_goodSet
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {w : Ω → ℝ} (hm : Measurable w) (hw : ∀ x, w x ∈ Icc (0:ℝ) 1)
    {E : Set Ω} (hE : MeasurableSet E) {A : ℝ} (hA : 0 ≤ A)
    (hgood : ∀ᵐ x ∂μ, x ∈ E → w x ≤ A) (a : ℕ) :
    Integrable (fun x => w x^a) μ ∧
      (∫ x, w x^a ∂μ) ≤ A^a+μ.real Eᶜ := by
  have hi : Integrable (fun x => w x^a) μ := Integrable.of_bound
    (hm.pow_const a).aestronglyMeasurable 1 (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (hw x).1 a)]
      exact pow_le_one₀ (hw x).1 (hw x).2)
  refine ⟨hi,?_⟩
  have hj : Integrable (fun x => A^a+Eᶜ.indicator (fun _ => (1:ℝ)) x) μ :=
    (integrable_const _).add ((integrable_const (1:ℝ)).indicator hE.compl)
  calc
    (∫ x, w x^a ∂μ) ≤ ∫ x, A^a+Eᶜ.indicator (fun _ => (1:ℝ)) x ∂μ := by
      apply integral_mono_ae hi hj
      filter_upwards [hgood] with x hx
      by_cases he : x ∈ E
      · simpa [he] using pow_le_pow_left₀ (hw x).1 (hx he) a
      · simp only [mem_compl_iff,he,not_false_eq_true,indicator_of_mem]
        have hh := pow_le_one₀ (hw x).1 (hw x).2 (n := a)
        linarith [pow_nonneg hA a]
    _ = _ := by rw [integral_add (integrable_const _) ((integrable_const (1:ℝ)).indicator hE.compl)]; rw [integral_indicator_const _ hE.compl]; simp

end FCAppendix.Probability

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.DummyKernel PayOnce.PriceConcentration PayOnce.RareSuccessSlope
open scoped BigOperators
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_ownImpact_moments
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let μ := fun t => Measure.pi (fun _ : Fin (M t-1) =>
      (BidScaling.realBidLaw (Γ t) : Measure ℝ))
    ∃ q d : ℝ, 0 < q ∧ 0 < d ∧ ∀ᶠ t in atTop, 0 < M t-1 ∧
      ∀ b : ℝ, 0 < b → ∃ w : (Fin (M t-1) → ℝ) → ℝ,
        Measurable w ∧ (∀ r, w r ∈ Icc (0:ℝ) 1) ∧
        (∀ r, 1/(((k+1:ℕ):ℝ)^3+1) ≤ 1-w r) ∧
        (∀ p : ENNReal, MemLp w p (μ t)) ∧
        HasDerivAt (coverage (k+1) (C t) hn (μ t))
          ((∫ r, weightedSlope (k+1) (allocation (k+1) (C t) hn r b) (w r) ∂μ t)/b) b ∧
        ∀ a : ℕ, Integrable (fun r => w r^a) (μ t) ∧
          (∫ r, w r^a ∂μ t) ≤ (((k+1:ℕ):ℝ)^3/(q*((M t-1:ℕ):ℝ)))^a+
            3*Real.exp (-d*((M t-1:ℕ):ℝ)) := by
  dsimp only
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  obtain ⟨ℓ,u,a,z,q,d,hℓ,_hℓL,hLu,hua,_haz,hzℓ,hq,hd,he⟩ :=
    payOnce_inactive_price_good_event Γ B F g ρ h
  have hL := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  refine ⟨q,d,hq,hd,?_⟩
  filter_upwards [he,h.eventually_scarce] with t ht hscarce
  refine ⟨ht.1,?_⟩
  intro b hb
  let μ := Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
  have ha (x : ℝ) (hx : 0 < x) : (BidScaling.realBidLaw (Γ t) : Measure ℝ) {x} = 0 :=
    realEffectiveBidLaw_positive_atomless (Γ t) hscarce.1 hscarce.2 (h.action_schedule t)
      (h.base_schedule t) (h.users t) (B t) (h.proposers t) (h.symmetry t)
      (h.positive_values_atomless t) (h.visible_atomless t) hx
  have hreg := ae_regularClearing_fixed_bid (ι := Fin (M t-1)) (c := C t)
    (BidScaling.realBidLaw (Γ t) : Measure ℝ) ha hn hb
  obtain ⟨w,hm,hw,hgap,hactive,hweight,hderiv⟩ :=
    exists_measurable_activeWeight_coverage_derivative hn μ hb hreg
  refine ⟨w,hm,hw,hgap,?_,hderiv,?_⟩
  · intro p
    exact MemLp.of_bound hm.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun r => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (hw r).1] using (hw r).2)
  · intro power
    have hgood : ∀ᵐ r ∂μ, r ∈ goodEvent (k+1) (M t-1) (C t) ℓ u a z q →
        w r ≤ ((k+1:ℕ):ℝ)^3/(q*((M t-1:ℕ):ℝ)) := by
      filter_upwards [hreg,hweight] with r hr hwr hg
      rw [hactive r]
      exact activeWeight_le_of_goodEvent ht.1 hn r hb hr hℓ (hL.trans hLu) hua hzℓ hq hg hwr
    have hp := Probability.unitInterval_power_moment_le_of_goodSet μ hm hw ht.2.1
      (show 0 ≤ ((k+1:ℕ):ℝ)^3/(q*((M t-1:ℕ):ℝ)) by positivity) hgood power
    exact ⟨hp.1,hp.2.trans (add_le_add_right ht.2.2.1 _)⟩

end FCAppendix.Bayes
