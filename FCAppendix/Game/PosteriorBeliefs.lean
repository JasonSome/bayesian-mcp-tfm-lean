import FCAppendix.Game.Bayesian
import FCAppendix.Probability.FinitePushforward

namespace FCAppendix
namespace Bayes

open MeasureTheory ProbabilityTheory Game
open scoped ProbabilityTheory BigOperators

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

abbrev UserProfile (m n : ℕ) := Fin m → UserDraw n

noncomputable def userProfileLaw (Γ : FiniteGame m n c Seed) : Measure (UserProfile m n) :=
  Measure.pi fun _ : Fin m => userLaw Γ

instance (Γ : FiniteGame m n c Seed) : IsProbabilityMeasure (userProfileLaw Γ) := by
  unfold userProfileLaw
  infer_instance

theorem measurable_observe_draws (j : Fin n) :
    Measurable (fun d : UserProfile m n => observe (drawsRealization d) j) := by
  classical
  rw [measurable_pi_iff]
  intro i
  have hdraw : Measurable (fun d : UserProfile m n => d i) := measurable_pi_apply i
  have hact : Measurable (fun d : UserProfile m n => (d i).1.2) :=
    measurable_snd.comp (measurable_fst.comp hdraw)
  change Measurable (fun d : UserProfile m n =>
    if j ∈ firstK (d i).2 (d i).1.2.routeCount then some (d i).1.2.bid else none)
  refine Measurable.ite ?_ (measurable_some.comp ((measurable_bid n).comp hact))
    measurable_const
  exact ((measurable_snd.comp hdraw).prodMk ((measurable_routeCount n).comp hact))
    (measurableSet_mem_firstK j)

noncomputable def observedListLaw (Γ : FiniteGame m n c Seed) (j : Fin n) :
    Measure (LocalList m) :=
  (userProfileLaw Γ).map (fun d => observe (drawsRealization d) j)

instance (Γ : FiniteGame m n c Seed) (j : Fin n) :
    IsProbabilityMeasure (observedListLaw Γ j) :=
  Measure.isProbabilityMeasure_map (measurable_observe_draws j).aemeasurable

def FeasibleObservedList (j : Fin n) (ℓ : LocalList m) : Prop :=
  ∃ d : UserProfile m n, observe (drawsRealization d) j = ℓ

structure PosteriorSystem (Γ : FiniteGame m n c Seed) where
  posterior : Fin n → Kernel (LocalList m) (UserProfile m n)
  markov : ∀ j, IsMarkovKernel (posterior j)
  on_path : ∀ j,
    (userProfileLaw Γ).map (fun d => (observe (drawsRealization d) j, d)) =
      (observedListLaw Γ j) ⊗ₘ (posterior j)
  feasible : ∀ j ℓ, FeasibleObservedList j ℓ →
    ∀ᵐ d ∂(posterior j ℓ), observe (drawsRealization d) j = ℓ

attribute [instance] PosteriorSystem.markov

private def listEntryCode : Option ℝ → ℝ × ℝ
  | none => (0, 0)
  | some b => (1, b)

private theorem measurable_listEntryCode : Measurable listEntryCode := by
  intro s hs
  change MeasurableSet ((fun b : ℝ => ((1 : ℝ), b)) ⁻¹' s)
  exact (measurable_const.prodMk measurable_id) hs

private theorem listEntryCode_injective : Function.Injective listEntryCode := by
  intro a b h
  cases a <;> cases b <;> simp_all [listEntryCode]

instance : MeasurableEq (Option ℝ) where
  measurableSet_diagonal := by
    have he : Set.diagonal (Option ℝ) =
        {p : Option ℝ × Option ℝ | listEntryCode p.1 = listEntryCode p.2} := by
      ext p
      change (p.1 = p.2) ↔ listEntryCode p.1 = listEntryCode p.2
      exact ⟨congrArg listEntryCode, fun h => listEntryCode_injective h⟩
    rw [he]
    exact measurableSet_eq_fun (measurable_listEntryCode.comp measurable_fst)
      (measurable_listEntryCode.comp measurable_snd)

theorem measurableSet_eq_lists {Ω : Type*} [MeasurableSpace Ω]
    {f g : Ω → LocalList m} (hf : Measurable f) (hg : Measurable g) :
    MeasurableSet {x | f x = g x} := by
  have he : {x | f x = g x} = ⋂ i, {x | f x i = g x i} := by
    ext x
    simp [funext_iff]
  rw [he]
  exact MeasurableSet.iInter fun i =>
    measurableSet_eq_fun ((measurable_pi_apply i).comp hf) ((measurable_pi_apply i).comp hg)

theorem PosteriorSystem.ae_posterior_of_ae (Γ : FiniteGame m n c Seed)
    (B : PosteriorSystem Γ) (j : Fin n) (P : UserProfile m n → Prop)
    (hP : MeasurableSet {d | P d}) (h : ∀ᵐ d ∂userProfileLaw Γ, P d) :
    ∀ᵐ ℓ ∂observedListLaw Γ j, ∀ᵐ d ∂B.posterior j ℓ, P d := by
  apply Measure.ae_ae_of_ae_compProd (μ := observedListLaw Γ j) (κ := B.posterior j)
    (p := fun p => P p.2)
  rw [← B.on_path j]
  exact (ae_map_iff ((measurable_observe_draws j).prodMk measurable_id).aemeasurable
    (measurable_snd hP)).mpr h

theorem PosteriorSystem.ae_observation (Γ : FiniteGame m n c Seed)
    (B : PosteriorSystem Γ) (j : Fin n) :
    ∀ᵐ ℓ ∂observedListLaw Γ j,
      ∀ᵐ d ∂B.posterior j ℓ, observe (drawsRealization d) j = ℓ := by
  apply Measure.ae_ae_of_ae_compProd (μ := observedListLaw Γ j) (κ := B.posterior j)
    (p := fun p => observe (drawsRealization p.2) j = p.1)
  rw [← B.on_path j]
  apply (ae_map_iff ((measurable_observe_draws j).prodMk measurable_id).aemeasurable
    (measurableSet_eq_lists ((measurable_observe_draws j).comp measurable_snd)
      measurable_fst)).mpr
  exact Filter.Eventually.of_forall fun _ => rfl

theorem PosteriorSystem.ae_commonLists (Γ : FiniteGame m n c Seed)
    (B : PosteriorSystem Γ) (j : Fin n)
    (hcommon : ∀ᵐ d ∂userProfileLaw Γ,
      ∀ l, observe (drawsRealization d) l = observe (drawsRealization d) j) :
    ∀ᵐ ℓ ∂observedListLaw Γ j,
      ∀ᵐ d ∂B.posterior j ℓ, ∀ l, observe (drawsRealization d) l = ℓ := by
  have hmeas : MeasurableSet {d : UserProfile m n |
      ∀ l, observe (drawsRealization d) l = observe (drawsRealization d) j} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun l =>
      measurableSet_eq_lists (measurable_observe_draws l) (measurable_observe_draws j)
  filter_upwards [B.ae_posterior_of_ae Γ j _ hmeas hcommon, B.ae_observation Γ j]
    with ℓ hℓ hobs
  filter_upwards [hℓ, hobs] with d hd ho
  exact fun l => (hd l).trans ho

theorem observe_eq_of_zero_or_full_routes (d : UserProfile m n)
    (hd : ∀ i, (d i).1.2.routeCount = 0 ∨ (d i).1.2.routeCount = n)
    (j l : Fin n) : observe (drawsRealization d) j = observe (drawsRealization d) l := by
  classical
  funext i
  rcases hd i with hi | hi <;> simp [observe, drawsRealization, mem_firstK, hi]

theorem ae_commonLists_of_zero_or_full_routes (Γ : FiniteGame m n c Seed)
    (hroute : ∀ᵐ p ∂(Γ.F ⊗ₘ Γ.σ), p.2.routeCount = 0 ∨ p.2.routeCount = n)
    (j : Fin n) : ∀ᵐ d ∂userProfileLaw Γ,
      ∀ l, observe (drawsRealization d) l = observe (drawsRealization d) j := by
  have huser : ∀ᵐ d ∂userLaw Γ, d.1.2.routeCount = 0 ∨ d.1.2.routeCount = n :=
    (measurePreserving_fst (μ := Γ.F ⊗ₘ Γ.σ) (ν := permLaw n)).quasiMeasurePreserving.ae hroute
  have hprofile : ∀ᵐ d ∂userProfileLaw Γ,
      ∀ i, (d i).1.2.routeCount = 0 ∨ (d i).1.2.routeCount = n :=
    ae_all_iff.mpr fun i =>
      (measurePreserving_eval (fun _ : Fin m => userLaw Γ) i).quasiMeasurePreserving.ae huser
  filter_upwards [hprofile] with d hd
  exact fun l => observe_eq_of_zero_or_full_routes d hd l j

noncomputable def posteriorBackground (Γ : FiniteGame m n c Seed)
    (B : PosteriorSystem Γ) (j : Fin n) (ℓ : LocalList m) : Measure (Background m n Seed) :=
  (B.posterior j ℓ).prod (Measure.pi fun _ : Fin n => Γ.seedLaw)

instance (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ) (j : Fin n)
    (ℓ : LocalList m) : IsProbabilityMeasure (posteriorBackground Γ B j ℓ) := by
  unfold posteriorBackground
  infer_instance

theorem measurable_allocation_draws (Γ : FiniteGame m n c Seed) (j : Fin n) :
    Measurable (fun ω : Background m n Seed =>
      allocation (drawsRealization ω.1) Γ.policy ω.2 j) := by
  exact (Γ.policy_measurable j).comp
    (((measurable_observe_draws j).comp measurable_fst).prodMk
      ((measurable_pi_apply j).comp measurable_snd))

noncomputable def otherInclusionCount (Γ : FiniteGame m n c Seed)
    (j : Fin n) (i : Fin m) (ω : Background m n Seed) : Fin n := by
  classical
  let S := (Finset.univ.erase j).filter (fun l =>
    i ∈ allocation (drawsRealization ω.1) Γ.policy ω.2 l)
  refine ⟨S.card, ?_⟩
  have h := Finset.card_le_card (Finset.filter_subset
    (fun l => i ∈ allocation (drawsRealization ω.1) Γ.policy ω.2 l) (Finset.univ.erase j))
  have hn := j.isLt
  have he : (Finset.univ.erase j).card = n - 1 := by simp
  change S.card ≤ _ at h
  omega

theorem otherInclusionCount_eq_sum (Γ : FiniteGame m n c Seed)
    (j : Fin n) (i : Fin m) (ω : Background m n Seed) :
    (otherInclusionCount Γ j i ω).val =
      ∑ l ∈ Finset.univ.erase j,
        if i ∈ allocation (drawsRealization ω.1) Γ.policy ω.2 l then 1 else 0 := by
  classical
  simp [otherInclusionCount, Finset.sum_boole]

theorem measurable_otherInclusionCount (Γ : FiniteGame m n c Seed)
    (j : Fin n) (i : Fin m) : Measurable (otherInclusionCount Γ j i) := by
  classical
  have hval : Measurable (fun ω : Background m n Seed =>
      (otherInclusionCount Γ j i ω).val) := by
    simp_rw [otherInclusionCount_eq_sum]
    refine Finset.measurable_sum _ (fun l _ => ?_)
    refine Measurable.ite ?_ measurable_const measurable_const
    exact (measurable_allocation_draws Γ l)
      (MeasurableSet.of_discrete : MeasurableSet {S : Finset (Fin m) | i ∈ S})
  apply measurable_to_countable'
  intro r
  have he : otherInclusionCount Γ j i ⁻¹' {r} =
      (fun ω => (otherInclusionCount Γ j i ω).val) ⁻¹' {r.val} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨congrArg Fin.val, Fin.ext⟩
  rw [he]
  exact hval (measurableSet_singleton _)

noncomputable def posteriorCountBelief (Γ : FiniteGame m n c Seed)
    (B : PosteriorSystem Γ) (j : Fin n) (ℓ : LocalList m) (i : Fin m) : FiniteLaw (Fin n) :=
  FiniteLaw.ofMeasure (posteriorBackground Γ B j ℓ) (otherInclusionCount Γ j i)
    (measurable_otherInclusionCount Γ j i)

theorem posterior_receipt_eq_integral (Γ : FiniteGame m n c Seed)
    (B : PosteriorSystem Γ) (j : Fin n) (ℓ : LocalList m) (i : Fin m) (b : ℝ) :
    Finite.conditionalReceipt Γ.A (posteriorCountBelief Γ B j ℓ i) b =
      ∫ ω, b * Γ.A.charge ((otherInclusionCount Γ j i ω).val + 1) /
        (((otherInclusionCount Γ j i ω).val : ℝ) + 1) ∂(posteriorBackground Γ B j ℓ) :=
  FiniteLaw.expect_ofMeasure _ _ _ _

def PosteriorProposerOptimal (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ) : Prop :=
  ∀ j ℓ s, Finite.Optimal c
    (beliefReceipts Γ.A (posteriorCountBelief Γ B j ℓ) ℓ) (Γ.policy j ℓ s).val

structure IsBayesianEquilibrium (Γ : FiniteGame m n c Seed) : Prop where
  users : UsersOptimal Γ
  beliefs : ∃ B : PosteriorSystem Γ, PosteriorProposerOptimal Γ B

theorem IsBayesianEquilibrium.isEquilibrium (Γ : FiniteGame m n c Seed)
    (hΓ : IsBayesianEquilibrium Γ) : IsEquilibrium Γ := by
  obtain ⟨B, hB⟩ := hΓ.beliefs
  exact ⟨hΓ.users, fun j => ⟨posteriorCountBelief Γ B j, hB j⟩⟩

end Bayes
end FCAppendix
