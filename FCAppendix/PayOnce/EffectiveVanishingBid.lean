import FCAppendix.PayOnce.EffectivePureBid
import FCAppendix.PayOnce.VanishingBidLaw
import Mathlib.Probability.ConditionalProbability

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open PayOnce PayOnce.CompactifiedBidLaws
open scoped ProbabilityTheory BigOperators
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem compactifiedBidLaw_eq_map_effectiveBidLaw (Γ : FiniteGame m n c Seed) :
    (bidLaw Γ : Measure ENNReal) = (BidScaling.realBidLaw Γ : Measure ℝ).map ENNReal.ofReal := by
  change (userLaw Γ).map (fun d => ENNReal.ofReal (effectiveBid d.1.2)) =
    ((userLaw Γ).map (fun d => effectiveBid d.1.2)).map ENNReal.ofReal
  rw [Measure.map_map ENNReal.measurable_ofReal
    (show Measurable (fun d : UserDraw n => effectiveBid d.1.2) from
      (measurable_effectiveBid n).comp (measurable_snd.comp measurable_fst))]
  rfl

theorem exists_monotone_effective_bid_bestResponse_all {k : ℕ}
    (Γ : FiniteGame m (k+1) c Seed) (hk : 1 ≤ k) (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A = Schedule.once (k+1)) (hG : Γ.G = Schedule.once (k+1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ) (hB : PosteriorProposerOptimalAE Γ B)
    (hsym : SymmetricProposersOnPath Γ) (hvalue : PositiveValueAtomless Γ)
    (hinactive : InactiveAbstain Γ) :
    ∃ bid : ℝ → ℝ, Monotone bid ∧ Measurable bid ∧
      (∀ v, 0 ≤ bid v ∧ bid v ≤ max (v-Γ.g) 0) ∧
      (∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), effectiveBid x.2 = bid x.1) ∧
      ∀ᵐ v ∂Γ.F, Γ.g < v → 0 < bid v ∧ bid v < v-Γ.g ∧
        (∀ i, (problem Γ i).BestResponse v (safeFullBid (k+1) (bid v))) ∧
        ∀ᵐ a ∂Γ.σ v, a = safeFullBid (k+1) (bid v) := by
  obtain ⟨bid,hmono,hmeas,hbound,heff,htype⟩ :=
    exists_monotone_effective_pure_bid Γ hk hc hcm hA hG hu B hB hsym hvalue hinactive ⟨0,by omega⟩
  refine ⟨bid,hmono,hmeas,hbound,heff,?_⟩
  have hall := ae_all_iff.mpr hu
  filter_upwards [htype,hall] with v hv hbest hactive
  obtain ⟨hb,hbw,hpure⟩ := hv hactive
  have he : ∀ᵐ a ∂Γ.σ v, a = safeFullBid (k+1) (bid v) := by
    filter_upwards [hpure] with a ha
    exact (ha.1 ▸ safeFullBid_eq_of_fullRoute a ha.2).symm
  refine ⟨hb,hbw,?_,he⟩
  intro j
  obtain ⟨a,ha,hea⟩ := ((hbest j).and he).exists
  exact hea ▸ ha

end FCAppendix.Bayes

namespace FCAppendix.PayOnce.VanishingBidIC
open MeasureTheory ProbabilityTheory Set Filter Topology
open CompactifiedBidLaws

theorem ae_effective_bid_zero_of_weak_zero {M C : ℕ → ℕ} {k : ℕ}
    {Seed : Type*} [MeasurableSpace Seed]
    (Γ : ∀ t, Bayes.FiniteGame (M t) (k+1) (C t) Seed)
    (F : Measure ℝ) [IsProbabilityMeasure F] (hF : ∀ t, (Γ t).F = F)
    (bid : ℕ → ℝ → ℝ) (hmono : ∀ t, Monotone (bid t)) (hpos : ∀ t v, 0 ≤ bid t v)
    (hpure : ∀ t, ∀ᵐ x ∂((Γ t).F ⊗ₘ (Γ t).σ), effectiveBid x.2 = bid t x.1)
    (hweak : Tendsto (fun t => bidLaw (Γ t)) atTop
      (𝓝 (⟨Measure.dirac 0,inferInstance⟩ : ProbabilityMeasure ENNReal))) :
    ∀ᵐ v ∂F, Tendsto (fun t => bid t v) atTop (𝓝 0) := by
  apply ae_tendsto_bid_zero_of_monotone_tail F bid hmono hpos
  intro ε hε
  have ht := tendsto_real_tails_zero_of_compactified_weak_zero
    (fun t => (BidScaling.realBidLaw (Γ t) : Measure ℝ)) (fun t => bidLaw (Γ t))
    (fun t => Bayes.compactifiedBidLaw_eq_map_effectiveBidLaw (Γ t)) hweak hε
  have he (t : ℕ) : (BidScaling.realBidLaw (Γ t) : Measure ℝ).real (Ici ε) = F.real {v | ε ≤ bid t v} := by
    rw [Bayes.realEffectiveBidLaw_eq_pure_map (Γ t) (bid t) (hmono t).measurable (hpure t),hF t]
    unfold Measure.real
    rw [Measure.map_apply (hmono t).measurable measurableSet_Ici]
    rfl
  simpa only [he] using ht

theorem nullSingleton_cond_positive (F : Measure ℝ) (g : ℝ)
    (hatom : ∀ v : ℝ, g < v → F {v} = 0) :
    NullSingletonClass (ProbabilityTheory.cond F (Ioi g)) := by
  constructor
  intro v
  rw [ProbabilityTheory.cond_apply measurableSet_Ioi]
  by_cases hv : g < v
  · rw [Set.inter_singleton_of_mem (show v ∈ Ioi g from hv),hatom v hv,mul_zero]
  · rw [Set.inter_singleton_of_notMem (show v ∉ Ioi g from hv),measure_empty,mul_zero]

end FCAppendix.PayOnce.VanishingBidIC

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open PayOnce PayOnce.CompactifiedBidLaws
open scoped ProbabilityTheory BigOperators

theorem exists_positive_success_equalization_of_weak_zero
    {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (hk : 1 ≤ k) (hc : ∀ t, 0 < C t) (hcm : ∀ t, C t < M t)
    (hA : ∀ t, (Γ t).A = Schedule.once (k+1))
    (hG : ∀ t, (Γ t).G = Schedule.once (k+1))
    (hu : ∀ t, UsersOptimal (Γ t)) (B : ∀ t, PosteriorSystem (Γ t))
    (hB : ∀ t, PosteriorProposerOptimalAE (Γ t) (B t))
    (hsym : ∀ t, SymmetricProposersOnPath (Γ t))
    (hvalue : ∀ t, PositiveValueAtomless (Γ t)) (hinactive : ∀ t, InactiveAbstain (Γ t))
    (F : Measure ℝ) [IsProbabilityMeasure F] (hF : ∀ t, (Γ t).F = F)
    {g : ℝ} (hg : ∀ t, (Γ t).g = g) (hactive : F (Ioi g) ≠ 0)
    (hweak : Tendsto (fun t => bidLaw (Γ t)) atTop
      (𝓝 (⟨Measure.dirac 0,inferInstance⟩ : ProbabilityMeasure ENNReal))) :
    ∃ bid : ℕ → ℝ → ℝ,
      (∀ t, Monotone (bid t)) ∧ (∀ t, Measurable (bid t)) ∧
      (∀ t v, 0 ≤ bid t v ∧ bid t v ≤ max (v-g) 0) ∧
      (∀ t, ∀ᵐ x ∂((Γ t).F ⊗ₘ (Γ t).σ), effectiveBid x.2 = bid t x.1) ∧
      (∀ᵐ v ∂F, Tendsto (fun t => bid t v) atTop (𝓝 0)) ∧
      (∀ t, ∀ᵐ v ∂F, g < v →
        (∀ i, (problem (Γ t) i).BestResponse v (safeFullBid (k+1) (bid t v))) ∧
        ∀ᵐ a ∂(Γ t).σ v, a = safeFullBid (k+1) (bid t v)) ∧
      ∀ᵐ z ∂(ProbabilityTheory.cond F (Ioi g)).prod (ProbabilityTheory.cond F (Ioi g)),
        Tendsto (fun t => averageTypeSuccess (Γ t) (bid t) z.2-
          averageTypeSuccess (Γ t) (bid t) z.1) atTop (𝓝 0) := by
  choose bid hmono hmeas hbound hpure hprop using fun t =>
    exists_monotone_effective_bid_bestResponse_all (Γ t) hk (hc t) (hcm t) (hA t) (hG t)
      (hu t) (B t) (hB t) (hsym t) (hvalue t) (hinactive t)
  have hzero := VanishingBidIC.ae_effective_bid_zero_of_weak_zero Γ F hF bid hmono
    (fun t v => (hbound t v).1) hpure hweak
  have hb t : ∀ᵐ v ∂F, g < v →
      (∀ i, (problem (Γ t) i).BestResponse v (safeFullBid (k+1) (bid t v))) ∧
      ∀ᵐ a ∂(Γ t).σ v, a = safeFullBid (k+1) (bid t v) := by
    have hh := (hprop t).mono fun v hv hpos => (hv hpos).2.2
    simpa only [hF t,hg t] using hh
  refine ⟨bid,hmono,hmeas,(fun t v => by simpa only [hg t] using hbound t v),hpure,hzero,hb,?_⟩
  let H := ProbabilityTheory.cond F (Ioi g)
  haveI : IsProbabilityMeasure H := ProbabilityTheory.cond_isProbabilityMeasure hactive
  have hpos : ∀ᵐ v ∂H, g < v := ProbabilityTheory.ae_cond_mem measurableSet_Ioi
  have hbest t : ∀ᵐ v ∂H, ∀ i, (problem (Γ t) i).BestResponse v (safeFullBid (k+1) (bid t v)) := by
    have hh : ∀ᵐ v ∂H, g < v →
        (∀ i, (problem (Γ t) i).BestResponse v (safeFullBid (k+1) (bid t v))) ∧
        ∀ᵐ a ∂(Γ t).σ v, a = safeFullBid (k+1) (bid t v) :=
      (ProbabilityTheory.cond_absolutelyContinuous (μ := F) (s := Ioi g)).ae_le (hb t)
    filter_upwards [hh,hpos] with v hv hp
    exact (hv hp).1
  exact ae_pair_average_success_gap_zero Γ (fun t => (hc t).trans (hcm t)) hA hG H hg hpos bid
    (fun t v => (hbound t v).1) hbest ((ProbabilityTheory.cond_absolutelyContinuous (μ := F) (s := Ioi g)).ae_le hzero)

end FCAppendix.Bayes
