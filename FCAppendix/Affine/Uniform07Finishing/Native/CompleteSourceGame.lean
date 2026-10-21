import FCAppendix.Affine.Uniform07Finishing.Native.SourceNativeGame
import FCAppendix.Affine.Uniform07Finishing.Native.AllLists

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Classical
open StrictNative
variable {m : ℕ} [Nonempty (Fin m)]
  (i : Uniform07.Row) (hc:1≤ Uniform07.capacity m)
  (R Λ : ℝ) (hΛ:0<Λ) (PL : ProbabilityMeasure (ℝ×JointAction 2))
  (α : ClassifiedContext m→ unitInterval) (hα:Measurable α)

def completeSourceNativeGame : FiniteGame m 2 (Uniform07.capacity m) unitInterval :=
  AllLists.game (sourceNativeGame i hc R Λ hΛ PL α hα)

lemma completeSourceNativeGame_allocation (x : Realization m 2)
    (s : Fin 2→ unitInterval) (j : Fin 2) :
    allocation x (completeSourceNativeGame i hc R Λ hΛ PL α hα).policy s j=
      allocation x (sourceNativeGame i hc R Λ hΛ PL α hα).policy s j :=
  AllLists.allocation_eq _ x s j

lemma completeSourceNativeGame_focalCount (u : Fin m) (a : JointAction 2)
    (ω : Sample m 2 unitInterval) :
    focalCount (completeSourceNativeGame i hc R Λ hΛ PL α hα) u a ω=
      focalCount (sourceNativeGame i hc R Λ hΛ PL α hα) u a ω :=
  AllLists.focalCount_eq _ u a ω

lemma completeSourceNativeGame_outcome (u : Fin m) (a : JointAction 2) :
    (problem (completeSourceNativeGame i hc R Λ hΛ PL α hα) u).outcome a=
      (problem (sourceNativeGame i hc R Λ hΛ PL α hα) u).outcome a :=
  AllLists.outcome_eq _ u a

lemma completeSourceNativeGame_payoff (u : Fin m) (v : ℝ) (a : JointAction 2) :
    (problem (completeSourceNativeGame i hc R Λ hΛ PL α hα) u).payoff v a=
      (problem (sourceNativeGame i hc R Λ hΛ PL α hα) u).payoff v a :=
  AllLists.payoff_eq _ u v a

lemma completeSourceNativeGame_conditional_count (hm:0< m) (v : ℝ) :
    conditionalTypeCountLaw (completeSourceNativeGame i hc R Λ hΛ PL α hα) hm v=
      conditionalTypeCountLaw (sourceNativeGame i hc R Λ hΛ PL α hα) hm v :=
  AllLists.conditional_count_eq _ hm v

variable (hm:2≤ m) (hR:0< R) (hUR:Early.bidCap i< R) (hRt:R< Uniform07.cutoff i)
  (hLvalue:(PL : Measure (ℝ×JointAction 2)).map Prod.fst=(sourceLowerValueLaw i : Measure ℝ))
  (hLroute:∀ᵐx∂(PL : Measure (ℝ×JointAction 2)),x.2.bid≤ Early.bidCap i ∧ x.2.routeCount=2)

include hm hR hRt hLvalue hLroute in
theorem completeSourceNativeGame_joint_law :
    (completeSourceNativeGame i hc R Λ hΛ PL α hα).F⊗ₘ
      (completeSourceNativeGame i hc R Λ hΛ PL α hα).σ=
        (sourcePopulation i m hc R PL : Measure (ℝ×JointAction 2)) :=
  sourceNativeGame_joint_law i hm hc hR hRt hΛ PL hLvalue hLroute α hα

include hm hR hUR hRt hLvalue hLroute in

theorem completeSourceNativeGame_proposer_optimal :
    ∃B : PosteriorSystem (completeSourceNativeGame i hc R Λ hΛ PL α hα),
      PosteriorProposerOptimal (completeSourceNativeGame i hc R Λ hΛ PL α hα) B := by
  let Γ:=sourceNativeGame i hc R Λ hΛ PL α hα
  let B:=sourceNativePosterior i hm hc hR hUR hRt hΛ PL hLvalue hLroute α hα
  exact ⟨AllLists.posterior Γ B,AllLists.proposer_optimal_all_lists Γ B
    (sourceNativeGame_proposer_optimal_feasible i hm hc hR hUR hRt hΛ PL hLvalue hLroute α hα)⟩

include hm hR hUR hRt hLvalue hLroute in

theorem completeSourceNativeGame_equilibrium
    (hu:∀ᵐx∂(sourcePopulation i m hc R PL : Measure (ℝ×JointAction 2)),
      ∀u : Fin m,∀a : JointAction 2,
        (problem (sourceNativeGame i hc R Λ hΛ PL α hα) u).payoff x.1 a≤
          (problem (sourceNativeGame i hc R Λ hΛ PL α hα) u).payoff x.1 x.2) :
    IsBayesianEquilibrium (completeSourceNativeGame i hc R Λ hΛ PL α hα) := by
  have husers:UsersOptimal (sourceNativeGame i hc R Λ hΛ PL α hα) := by
    apply (usersOptimal_iff_common_all_actions _).mpr
    rwa [sourceNativeGame_joint_law i hm hc hR hRt hΛ PL hLvalue hLroute α hα]
  exact ⟨AllLists.users_optimal _ husers,
    completeSourceNativeGame_proposer_optimal i hc R Λ hΛ PL α hα hm hR hUR hRt hLvalue hLroute⟩

end FCAppendix.Affine.Uniform07Finishing
