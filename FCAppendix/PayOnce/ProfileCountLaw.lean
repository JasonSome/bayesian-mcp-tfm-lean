import FCAppendix.PayOnce.ActualProfileWeights

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set CommonList
open PayOnce PayOnce.AnalyticalKernel
open scoped ProbabilityTheory BigOperators
variable {m c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem ae_profileCountLaw_eq_binomial (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hcm : c ≤ m)
    (hA : Γ.A = Schedule.once (k+1)) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = k+1)
    (hbid : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.bid) :
    ∀ᵐ d ∂userProfileLaw Γ, ∀ i,
      profileCountLaw Γ d i = IndependentCounts.binomial (k+1)
        (analyticalProfileMarginal Γ (by omega) hcm d i)
        (analyticalProfileMarginal_bounds Γ (by omega) hcm d i).1
        (analyticalProfileMarginal_bounds Γ (by omega) hcm d i).2 := by
  let j : Fin (k+1) := ⟨0,by omega⟩
  have hgame := ae_fullList_equilibrium_of_full_routes Γ hA B hB hsym hroute j
  have huserbid := (measurePreserving_fst (μ := Γ.F ⊗ₘ Γ.σ)
    (ν := permLaw (k+1))).quasiMeasurePreserving.ae hbid
  have hdrawbid : ∀ᵐ d ∂userProfileLaw Γ, ∀ l, 0 < (d l).1.2.bid :=
    ae_all_iff.mpr fun l => (measurePreserving_eval (fun _ : Fin m => userLaw Γ) l).quasiMeasurePreserving.ae huserbid
  filter_upwards [hgame,hdrawbid] with d hg hb
  intro i
  let ℓ := observe (drawsRealization d) j
  let μ := seedLottery Γ j ℓ
  have hlaw := profileCountLaw_binomial Γ d ℓ hg.1 μ hg.2.1 i
  obtain ⟨L,hL,he,hcap⟩ := CommonList.equilibrium_kernel (k+1) (by omega)
    (fun l => (d l).1.2.bid) hb c (by simpa using hcm) μ hg.2.2
  have hp : Proposer.marginal μ i = analyticalProfileMarginal Γ (by omega) hcm d i := by
    rw [he i]
    symm
    apply allocation_eq_kernel _ _ (rivalBids i d) (fun l => hb l.val) (hb i) hL
    exact (sum_focal_rivals i (fun l => kernel (k+1) (d l).1.2.bid L)).trans hcap
  simpa only [hp] using hlaw

end FCAppendix.Bayes
