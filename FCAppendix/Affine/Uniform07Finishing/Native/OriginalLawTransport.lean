import FCAppendix.Affine.Uniform07Finishing.Native.VisibleBids
import FCAppendix.Game.PosteriorExistence

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Classical
open scoped BigOperators

local instance (n : ℕ) : MeasurableSingletonClass (JointAction n) := by
  constructor
  intro a
  convert (jointActionCode n).measurable (measurableSet_singleton (jointActionCode n a)) using 1
  ext b
  simp

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def withStrategy (Γ : FiniteGame m n c Seed)
    (κ : Kernel ℝ (JointAction n)) [IsMarkovKernel κ] : FiniteGame m n c Seed :=
  { Γ with σ := κ, hσ := inferInstance }

theorem withStrategy_joint_law (Γ : FiniteGame m n c Seed)
    (κ : Kernel ℝ (JointAction n)) [IsMarkovKernel κ]
    (hκ : κ =ᵐ[Γ.F] Γ.σ) :
    (withStrategy Γ κ).F ⊗ₘ (withStrategy Γ κ).σ = Γ.F ⊗ₘ Γ.σ :=
  Measure.compProd_congr hκ

theorem withStrategy_user_law (Γ : FiniteGame m n c Seed)
    (κ : Kernel ℝ (JointAction n)) [IsMarkovKernel κ]
    (hκ : κ =ᵐ[Γ.F] Γ.σ) : userLaw (withStrategy Γ κ) = userLaw Γ := by
  unfold userLaw
  rw [withStrategy_joint_law Γ κ hκ]

theorem withStrategy_background_law (Γ : FiniteGame m n c Seed)
    (κ : Kernel ℝ (JointAction n)) [IsMarkovKernel κ]
    (hκ : κ =ᵐ[Γ.F] Γ.σ) :
    backgroundLaw (withStrategy Γ κ) = backgroundLaw Γ := by
  unfold backgroundLaw
  rw [withStrategy_user_law Γ κ hκ]
  rfl

theorem withStrategy_sample_law (Γ : FiniteGame m n c Seed)
    (κ : Kernel ℝ (JointAction n)) [IsMarkovKernel κ]
    (hκ : κ =ᵐ[Γ.F] Γ.σ) : sampleLaw (withStrategy Γ κ) = sampleLaw Γ := by
  unfold sampleLaw
  rw [withStrategy_background_law Γ κ hκ]

theorem withStrategy_focal_count (Γ : FiniteGame m n c Seed)
    (κ : Kernel ℝ (JointAction n)) [IsMarkovKernel κ]
    (i : Fin m) (a : JointAction n) (ω : Sample m n Seed) :
    focalCount (withStrategy Γ κ) i a ω = focalCount Γ i a ω := rfl

theorem withStrategy_outcome (Γ : FiniteGame m n c Seed)
    (κ : Kernel ℝ (JointAction n)) [IsMarkovKernel κ]
    (hκ : κ =ᵐ[Γ.F] Γ.σ) (i : Fin m) (a : JointAction n) :
    (problem (withStrategy Γ κ) i).outcome a = (problem Γ i).outcome a := by
  apply FiniteLaw.ext_expect
  intro f
  simp only [problem_outcome, CountLaw.expect_ofMeasure]
  rw [withStrategy_sample_law Γ κ hκ]
  rfl

theorem withStrategy_typeOutcome (Γ : FiniteGame m n c Seed)
    (κ : Kernel ℝ (JointAction n)) [IsMarkovKernel κ]
    (hκ : κ =ᵐ[Γ.F] Γ.σ) (i : Fin m) (v : ℝ) :
    typeOutcome (withStrategy Γ κ) i v =
      FiniteLaw.average (κ v) (problem Γ i).outcome
        (measurable_outcome_mass Γ i) := by
  apply FiniteLaw.ext
  intro r
  change (∫ a, ((problem (withStrategy Γ κ) i).outcome a).mass r ∂κ v) =
    (∫ a, ((problem Γ i).outcome a).mass r ∂κ v)
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun a => by
    dsimp only
    rw [withStrategy_outcome Γ κ hκ]

theorem withStrategy_conditional_count_law (Γ : FiniteGame m n c Seed)
    (κ : Kernel ℝ (JointAction n)) [IsMarkovKernel κ]
    (hκ : κ =ᵐ[Γ.F] Γ.σ) (hm : 0 < m) (v : ℝ) :
    conditionalTypeCountLaw (withStrategy Γ κ) hm v =
      FiniteLaw.uniformAverage hm (fun i =>
        FiniteLaw.average (κ v) (problem Γ i).outcome
          (measurable_outcome_mass Γ i)) := by
  unfold conditionalTypeCountLaw
  congr 1
  funext i
  exact withStrategy_typeOutcome Γ κ hκ i v

theorem withStrategy_typeOutcome_of_kernel_eq (Γ : FiniteGame m n c Seed)
    (κ : Kernel ℝ (JointAction n)) [IsMarkovKernel κ]
    (hκ : κ =ᵐ[Γ.F] Γ.σ) (i : Fin m) (v : ℝ)
    (hv : κ v = Γ.σ v) :
    typeOutcome (withStrategy Γ κ) i v = typeOutcome Γ i v := by
  rw [withStrategy_typeOutcome Γ κ hκ i v]
  apply FiniteLaw.ext
  intro r
  change (∫ a, ((problem Γ i).outcome a).mass r ∂κ v) =
    (∫ a, ((problem Γ i).outcome a).mass r ∂Γ.σ v)
  rw [hv]

theorem withStrategy_typeOutcome_ae (Γ : FiniteGame m n c Seed)
    (κ : Kernel ℝ (JointAction n)) [IsMarkovKernel κ]
    (hκ : κ =ᵐ[Γ.F] Γ.σ) :
    ∀ᵐ v ∂Γ.F, ∀ i : Fin m,
      typeOutcome (withStrategy Γ κ) i v = typeOutcome Γ i v := by
  filter_upwards [hκ] with v hv
  intro i
  exact withStrategy_typeOutcome_of_kernel_eq Γ κ hκ i v hv

theorem withStrategy_conditional_count_law_ae (Γ : FiniteGame m n c Seed)
    (κ : Kernel ℝ (JointAction n)) [IsMarkovKernel κ]
    (hκ : κ =ᵐ[Γ.F] Γ.σ) (hm : 0 < m) :
    ∀ᵐ v ∂Γ.F,
      conditionalTypeCountLaw (withStrategy Γ κ) hm v =
        conditionalTypeCountLaw Γ hm v := by
  filter_upwards [withStrategy_typeOutcome_ae Γ κ hκ] with v hv
  unfold conditionalTypeCountLaw
  congr 1
  funext i
  exact hv i

theorem withStrategy_integral_conditional_count_expect
    (Γ : FiniteGame m n c Seed)
    (κ : Kernel ℝ (JointAction n)) [IsMarkovKernel κ]
    (hκ : κ =ᵐ[Γ.F] Γ.σ) (hm : 0 < m) (f : Fin (n + 1) → ℝ) :
    (∫ v, (conditionalTypeCountLaw (withStrategy Γ κ) hm v).expect f
      ∂(withStrategy Γ κ).F) =
      ∫ v, (conditionalTypeCountLaw Γ hm v).expect f ∂Γ.F := by
  change (∫ v, (conditionalTypeCountLaw (withStrategy Γ κ) hm v).expect f ∂Γ.F) = _
  apply integral_congr_ae
  filter_upwards [withStrategy_conditional_count_law_ae Γ κ hκ hm] with v hv
  rw [hv]

theorem withStrategy_finite_coverage (Γ : FiniteGame m n c Seed)
    (κ : Kernel ℝ (JointAction n)) [IsMarkovKernel κ]
    (hκ : κ =ᵐ[Γ.F] Γ.σ) (hm : 0 < m) :
    finiteCoverage (withStrategy Γ κ) = finiteCoverage Γ := by
  rw [← integral_conditionalTypeCountLaw_success (withStrategy Γ κ) hm,
    ← integral_conditionalTypeCountLaw_success Γ hm]
  exact withStrategy_integral_conditional_count_expect Γ κ hκ hm _

theorem withStrategy_finite_load (Γ : FiniteGame m n c Seed)
    (κ : Kernel ℝ (JointAction n)) [IsMarkovKernel κ]
    (hκ : κ =ᵐ[Γ.F] Γ.σ) (hm : 0 < m) :
    finiteLoad (withStrategy Γ κ) = finiteLoad Γ := by
  rw [← integral_conditionalTypeCountLaw_load (withStrategy Γ κ) hm,
    ← integral_conditionalTypeCountLaw_load Γ hm]
  exact withStrategy_integral_conditional_count_expect Γ κ hκ hm _

theorem withStrategy_finite_duplicates (Γ : FiniteGame m n c Seed)
    (κ : Kernel ℝ (JointAction n)) [IsMarkovKernel κ]
    (hκ : κ =ᵐ[Γ.F] Γ.σ) (hm : 0 < m) :
    finiteLoad (withStrategy Γ κ) - finiteCoverage (withStrategy Γ κ) =
      finiteLoad Γ - finiteCoverage Γ := by
  rw [withStrategy_finite_load Γ κ hκ hm,
    withStrategy_finite_coverage Γ κ hκ hm]

theorem withStrategy_finite_multiplicity (Γ : FiniteGame m n c Seed)
    (κ : Kernel ℝ (JointAction n)) [IsMarkovKernel κ]
    (hκ : κ =ᵐ[Γ.F] Γ.σ) (hm : 0 < m) :
    finiteMultiplicity (withStrategy Γ κ) = finiteMultiplicity Γ := by
  unfold finiteMultiplicity
  rw [withStrategy_finite_load Γ κ hκ hm,
    withStrategy_finite_coverage Γ κ hκ hm]

theorem withStrategy_payoff (Γ : FiniteGame m n c Seed)
    (κ : Kernel ℝ (JointAction n)) [IsMarkovKernel κ]
    (hκ : κ =ᵐ[Γ.F] Γ.σ) (i : Fin m) (v : ℝ) (a : JointAction n) :
    (problem (withStrategy Γ κ) i).payoff v a = (problem Γ i).payoff v a := by
  unfold Interim.Problem.payoff
  rw [withStrategy_outcome Γ κ hκ]
  rfl

theorem withStrategy_users_optimal (Γ : FiniteGame m n c Seed)
    (κ : Kernel ℝ (JointAction n)) [IsMarkovKernel κ]
    (hκ : κ =ᵐ[Γ.F] Γ.σ) (hu : UsersOptimal Γ) :
    UsersOptimal (withStrategy Γ κ) := by
  apply (usersOptimal_iff_common_all_actions (withStrategy Γ κ)).mpr
  rw [withStrategy_joint_law Γ κ hκ]
  filter_upwards [(usersOptimal_iff_common_all_actions Γ).mp hu] with x hx
  intro i a
  simpa only [withStrategy_payoff Γ κ hκ] using hx i a

theorem withStrategy_user_profile_law (Γ : FiniteGame m n c Seed)
    (κ : Kernel ℝ (JointAction n)) [IsMarkovKernel κ]
    (hκ : κ =ᵐ[Γ.F] Γ.σ) :
    userProfileLaw (withStrategy Γ κ) = userProfileLaw Γ := by
  unfold userProfileLaw
  rw [withStrategy_user_law Γ κ hκ]

def withStrategyPosterior (Γ : FiniteGame m n c Seed)
    (κ : Kernel ℝ (JointAction n)) [IsMarkovKernel κ]
    (hκ : κ =ᵐ[Γ.F] Γ.σ) (B : PosteriorSystem Γ) :
    PosteriorSystem (withStrategy Γ κ) where
  posterior := B.posterior
  markov := B.markov
  on_path j := by
    simpa only [observedListLaw, withStrategy_user_profile_law Γ κ hκ] using B.on_path j
  feasible := B.feasible

theorem withStrategy_posterior_count (Γ : FiniteGame m n c Seed)
    (κ : Kernel ℝ (JointAction n)) [IsMarkovKernel κ]
    (hκ : κ =ᵐ[Γ.F] Γ.σ) (B : PosteriorSystem Γ)
    (j : Fin n) (L : LocalList m) (i : Fin m) :
    posteriorCountBelief (withStrategy Γ κ) (withStrategyPosterior Γ κ hκ B) j L i =
      posteriorCountBelief Γ B j L i := rfl

theorem withStrategy_bayesian_equilibrium (Γ : FiniteGame m n c Seed)
    (κ : Kernel ℝ (JointAction n)) [IsMarkovKernel κ]
    (hκ : κ =ᵐ[Γ.F] Γ.σ) (hΓ : IsBayesianEquilibrium Γ) :
    IsBayesianEquilibrium (withStrategy Γ κ) := by
  refine ⟨withStrategy_users_optimal Γ κ hκ hΓ.users, ?_⟩
  obtain ⟨B, hB⟩ := hΓ.beliefs
  refine ⟨withStrategyPosterior Γ κ hκ B, ?_⟩
  intro j L s
  exact hB j L s

theorem withStrategy_visible_bid_measure (Γ : FiniteGame m n c Seed)
    (κ : Kernel ℝ (JointAction n)) [IsMarkovKernel κ]
    (hκ : κ =ᵐ[Γ.F] Γ.σ) (j : Fin n) :
    visibleBidMeasure (withStrategy Γ κ) j = visibleBidMeasure Γ j := by
  unfold visibleBidMeasure
  rw [withStrategy_user_law Γ κ hκ]

theorem withStrategy_visible_atomless (Γ : FiniteGame m n c Seed)
    (κ : Kernel ℝ (JointAction n)) [IsMarkovKernel κ]
    (hκ : κ =ᵐ[Γ.F] Γ.σ) (hΓ : VisibleAtomless Γ) :
    VisibleAtomless (withStrategy Γ κ) := by
  intro j
  rw [withStrategy_visible_bid_measure Γ κ hκ j]
  exact hΓ j

def patchStrategy (Γ : FiniteGame m n c Seed) (s : Set ℝ) (hs : MeasurableSet s)
    (a : ℝ → JointAction n) (ha : Measurable a) : Kernel ℝ (JointAction n) :=
  Kernel.piecewise hs (Kernel.deterministic a ha) Γ.σ

instance patchStrategy_markov (Γ : FiniteGame m n c Seed)
    (s : Set ℝ) (hs : MeasurableSet s) (a : ℝ → JointAction n) (ha : Measurable a) :
    IsMarkovKernel (patchStrategy Γ s hs a ha) := by
  unfold patchStrategy
  infer_instance

theorem patchStrategy_ae_eq (Γ : FiniteGame m n c Seed)
    (s : Set ℝ) (hs : MeasurableSet s) (hnull : Γ.F s = 0)
    (a : ℝ → JointAction n) (ha : Measurable a) :
    patchStrategy Γ s hs a ha =ᵐ[Γ.F] Γ.σ := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with v hv
  simp only [patchStrategy, Kernel.piecewise_apply, if_neg hv]

theorem patchStrategy_at (Γ : FiniteGame m n c Seed)
    (s : Set ℝ) (hs : MeasurableSet s) (a : ℝ → JointAction n) (ha : Measurable a)
    {v : ℝ} (hv : v ∈ s) :
    patchStrategy Γ s hs a ha v = Measure.dirac (a v) := by
  simp only [patchStrategy, Kernel.piecewise_apply, if_pos hv, Kernel.deterministic_apply]

theorem patchStrategy_off (Γ : FiniteGame m n c Seed)
    (s : Set ℝ) (hs : MeasurableSet s) (a : ℝ → JointAction n) (ha : Measurable a)
    {v : ℝ} (hv : v ∉ s) :
    patchStrategy Γ s hs a ha v = Γ.σ v := by
  simp only [patchStrategy, Kernel.piecewise_apply, if_neg hv]

theorem patched_typeOutcome (Γ : FiniteGame m n c Seed)
    (s : Set ℝ) (hs : MeasurableSet s) (hnull : Γ.F s = 0)
    (a : ℝ → JointAction n) (ha : Measurable a) (i : Fin m)
    {v : ℝ} (hv : v ∈ s) :
    typeOutcome (withStrategy Γ (patchStrategy Γ s hs a ha)) i v =
      (problem Γ i).outcome (a v) := by
  apply FiniteLaw.ext
  intro r
  change (∫ b, ((problem (withStrategy Γ (patchStrategy Γ s hs a ha)) i).outcome b).mass r
    ∂patchStrategy Γ s hs a ha v) = _
  rw [patchStrategy_at Γ s hs a ha hv, integral_dirac,
    withStrategy_outcome Γ _ (patchStrategy_ae_eq Γ s hs hnull a ha)]

theorem unpatched_typeOutcome (Γ : FiniteGame m n c Seed)
    (s : Set ℝ) (hs : MeasurableSet s) (hnull : Γ.F s = 0)
    (a : ℝ → JointAction n) (ha : Measurable a) (i : Fin m)
    {v : ℝ} (hv : v ∉ s) :
    typeOutcome (withStrategy Γ (patchStrategy Γ s hs a ha)) i v =
      typeOutcome Γ i v :=
  withStrategy_typeOutcome_of_kernel_eq Γ _ (patchStrategy_ae_eq Γ s hs hnull a ha)
    i v (patchStrategy_off Γ s hs a ha hv)

theorem patched_conditional_count_law (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (s : Set ℝ) (hs : MeasurableSet s) (hnull : Γ.F s = 0)
    (a : ℝ → JointAction n) (ha : Measurable a)
    {v : ℝ} (hv : v ∈ s) :
    conditionalTypeCountLaw (withStrategy Γ (patchStrategy Γ s hs a ha)) hm v =
      FiniteLaw.uniformAverage hm (fun i => (problem Γ i).outcome (a v)) := by
  unfold conditionalTypeCountLaw
  congr 1
  funext i
  exact patched_typeOutcome Γ s hs hnull a ha i hv

theorem unpatched_conditional_count_law (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (s : Set ℝ) (hs : MeasurableSet s) (hnull : Γ.F s = 0)
    (a : ℝ → JointAction n) (ha : Measurable a)
    {v : ℝ} (hv : v ∉ s) :
    conditionalTypeCountLaw (withStrategy Γ (patchStrategy Γ s hs a ha)) hm v =
      conditionalTypeCountLaw Γ hm v := by
  unfold conditionalTypeCountLaw
  congr 1
  funext i
  exact unpatched_typeOutcome Γ s hs hnull a ha i hv

theorem patched_typeOutcome_cases (Γ : FiniteGame m n c Seed)
    (s : Set ℝ) (hs : MeasurableSet s) (hnull : Γ.F s = 0)
    (a : ℝ → JointAction n) (ha : Measurable a) (i : Fin m) (v : ℝ) :
    typeOutcome (withStrategy Γ (patchStrategy Γ s hs a ha)) i v =
      if v ∈ s then (problem Γ i).outcome (a v) else typeOutcome Γ i v := by
  classical
  by_cases hv : v ∈ s
  · rw [if_pos hv]
    exact patched_typeOutcome Γ s hs hnull a ha i hv
  · rw [if_neg hv]
    exact unpatched_typeOutcome Γ s hs hnull a ha i hv

theorem patched_conditional_count_law_cases (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (s : Set ℝ) (hs : MeasurableSet s) (hnull : Γ.F s = 0)
    (a : ℝ → JointAction n) (ha : Measurable a) (v : ℝ) :
    conditionalTypeCountLaw (withStrategy Γ (patchStrategy Γ s hs a ha)) hm v =
      if v ∈ s then FiniteLaw.uniformAverage hm (fun i => (problem Γ i).outcome (a v))
      else conditionalTypeCountLaw Γ hm v := by
  classical
  by_cases hv : v ∈ s
  · rw [if_pos hv]
    exact patched_conditional_count_law Γ hm s hs hnull a ha hv
  · rw [if_neg hv]
    exact unpatched_conditional_count_law Γ hm s hs hnull a ha hv

theorem patched_fixed_value_best_response (Γ : FiniteGame m n c Seed)
    (s : Set ℝ) (hs : MeasurableSet s) (hnull : Γ.F s = 0)
    (a : ℝ → JointAction n) (ha : Measurable a)
    {v : ℝ} (hv : v ∈ s)
    (hbest : ∀ i : Fin m, (problem Γ i).BestResponse v (a v)) :
    ∀ᵐ b ∂(withStrategy Γ (patchStrategy Γ s hs a ha)).σ v,
      ∀ i : Fin m, ∀ b' : JointAction n,
        (problem (withStrategy Γ (patchStrategy Γ s hs a ha)) i).payoff v b' ≤
          (problem (withStrategy Γ (patchStrategy Γ s hs a ha)) i).payoff v b := by
  change ∀ᵐ b ∂patchStrategy Γ s hs a ha v, _
  rw [patchStrategy_at Γ s hs a ha hv]
  have hb : ∀ᵐ b ∂Measure.dirac (a v), b = a v := by simp
  filter_upwards [hb] with b hb
  subst b
  intro i b'
  simpa only [withStrategy_payoff Γ _ (patchStrategy_ae_eq Γ s hs hnull a ha)]
    using hbest i b'

end FCAppendix.Affine.Uniform07Finishing
