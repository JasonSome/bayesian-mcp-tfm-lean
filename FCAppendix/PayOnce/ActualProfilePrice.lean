import FCAppendix.PayOnce.ProfilePriceCLT
import FCAppendix.PayOnce.EffectiveBidLaw

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set CommonList
open PayOnce PayOnce.DummyKernel PayOnce.CompactifiedBidLaws KernelTailEvent
variable {m c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def actualProfilePrice (_Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hm : 0 < m) (d : UserProfile m (k+1)) : ℝ :=
  profilePrice (k+1) c (by omega) hm (fun i => effectiveBid (d i).1.2)

theorem measurable_actualProfilePrice (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hm : 0 < m) : Measurable (actualProfilePrice Γ hk hm) :=
  (measurable_profilePrice (by omega) hm).comp
    (effectiveBid_profile_measurePreserving Γ).measurable

theorem actualProfilePrice_map_eq (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hm : 0 < m) :
    (userProfileLaw Γ).map (actualProfilePrice Γ hk hm) =
      (Measure.pi (fun _ : Fin m => (BidScaling.realBidLaw Γ : Measure ℝ))).map
        (profilePrice (k+1) c (by omega) hm) := by
  rw [← (effectiveBid_profile_measurePreserving Γ).map_eq,
    Measure.map_map (measurable_profilePrice (by omega) hm)
      (effectiveBid_profile_measurePreserving Γ).measurable]
  rfl

noncomputable def actualSampleProfilePrice (_Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (d : UserProfile m (k+1)) : ℝ :=
  sampleProfilePrice (k+1) c (by omega) (fun i => effectiveBid (d i).1.2)

theorem measurable_actualSampleProfilePrice (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) : Measurable (actualSampleProfilePrice Γ hk) :=
  (measurable_sampleProfilePrice (by omega)).comp
    (effectiveBid_profile_measurePreserving Γ).measurable

theorem actualSampleProfilePrice_map_eq (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) :
    (userProfileLaw Γ).map (actualSampleProfilePrice Γ hk) =
      (Measure.pi (fun _ : Fin m => (BidScaling.realBidLaw Γ : Measure ℝ))).map
        (sampleProfilePrice (k+1) c (by omega)) := by
  rw [← (effectiveBid_profile_measurePreserving Γ).map_eq,
    Measure.map_map (measurable_sampleProfilePrice (by omega))
      (effectiveBid_profile_measurePreserving Γ).measurable]
  rfl

theorem integral_actualSampleProfilePrice (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ d, f (actualSampleProfilePrice Γ hk d) ∂userProfileLaw Γ) =
      ∫ z, f (sampleProfilePrice (k+1) c (by omega) z)
        ∂(Measure.pi (fun _ : Fin m => (BidScaling.realBidLaw Γ : Measure ℝ))) := by
  rw [← integral_map (measurable_actualSampleProfilePrice Γ hk).aemeasurable
      hf.aestronglyMeasurable, actualSampleProfilePrice_map_eq Γ hk,
    integral_map (measurable_sampleProfilePrice (by omega)).aemeasurable
      hf.aestronglyMeasurable]

theorem integrable_actualSampleProfilePrice_iff (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (f : ℝ → ℝ) (hf : Measurable f) :
    Integrable (fun d => f (actualSampleProfilePrice Γ hk d)) (userProfileLaw Γ) ↔
      Integrable (fun z => f (sampleProfilePrice (k+1) c (by omega) z))
        (Measure.pi (fun _ : Fin m => (BidScaling.realBidLaw Γ : Measure ℝ))) := by
  change Integrable (f ∘ actualSampleProfilePrice Γ hk) _ ↔
    Integrable (f ∘ sampleProfilePrice (k+1) c (by omega)) _
  rw [← integrable_map_measure hf.aestronglyMeasurable
      (measurable_actualSampleProfilePrice Γ hk).aemeasurable,
    actualSampleProfilePrice_map_eq Γ hk,
    integrable_map_measure hf.aestronglyMeasurable
      (measurable_sampleProfilePrice (by omega)).aemeasurable]

theorem actualSampleProfilePrice_eq (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hm : 0 < m) (d : UserProfile m (k+1)) :
    actualSampleProfilePrice Γ hk d = actualProfilePrice Γ hk hm d :=
  congrFun (sampleProfilePrice_eq (n := k+1) (c := c) (by omega) hm) _

theorem ae_profileCountLaw_eq_actualPrice_binomial (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hm : 0 < m) (hA : Γ.A = Schedule.once (k+1))
    (B : PosteriorSystem Γ) (hB : PosteriorProposerOptimalAE Γ B)
    (hsym : SymmetricProposersOnPath Γ)
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ),
      x.2.routeCount = 0 ∨ (0 < x.2.bid ∧ x.2.routeCount = k+1)) :
    ∀ᵐ d ∂userProfileLaw Γ, ∀ i,
      profileCountLaw Γ d i = IndependentCounts.binomial (k+1)
        (kernel (k+1) (effectiveBid (d i).1.2) (actualProfilePrice Γ hk hm d))
        (kernel_bounds (by omega) (profilePrice_spec (by omega) hm _).1 _).1
        (kernel_bounds (by omega) (profilePrice_spec (by omega) hm _).1 _).2 := by
  filter_upwards [ae_profileCountLaw_eq_dummy_binomial Γ hk hA B hB hsym hroute] with d hd
  intro i
  have he := (profilePrice_spec (c := c) (by omega : 2 ≤ k+1) hm
    (fun j => effectiveBid (d j).1.2)).2.1 i
  simpa only [he,actualProfilePrice] using hd i

end FCAppendix.Bayes
