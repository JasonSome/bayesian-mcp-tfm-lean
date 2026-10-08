import FCAppendix.PayOnce.DummyInterimCopies

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel
variable {m c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def TypeProfileMarginalAgreement (Γ : FiniteGame m (k+1) c Seed) (hn : 2 ≤ k+1) (b v : ℝ) : Prop :=
  ∀ i : Fin m, ∀ᵐ a ∂Γ.σ v, ∀ᵐ r ∂permLaw (k+1), ∀ᵐ d ∂userProfileLaw Γ,
    (profileCountLaw Γ (Function.update d i ((v,a),r)) i).load/((k+1:ℕ):ℝ)=
      allocation (k+1) c hn (effectiveRivalBids i d) b

theorem ae_type_profileMarginal_eq_dummy (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hA : Γ.A = Schedule.once (k+1)) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = 0 ∨
      (0 < x.2.bid ∧ x.2.routeCount = k+1))
    (b : ℝ → ℝ) (heq : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), effectiveBid x.2=b x.1) :
    ∀ᵐ v ∂Γ.F, ∀ i : Fin m, ∀ᵐ a ∂Γ.σ v, ∀ᵐ r ∂permLaw (k+1), ∀ᵐ d ∂userProfileLaw Γ,
      (profileCountLaw Γ (Function.update d i ((v,a),r)) i).load/((k+1:ℕ):ℝ)=
        allocation (k+1) c (by omega) (effectiveRivalBids i d) (b v) := by
  have hprofile := ae_profileCountLaw_eq_dummy_binomial Γ hk hA B hB hsym hroute
  have hi (i : Fin m) : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), ∀ᵐ r ∂permLaw (k+1), ∀ᵐ d ∂userProfileLaw Γ,
      (profileCountLaw Γ (Function.update d i (x,r)) i).load/((k+1:ℕ):ℝ)=
        allocation (k+1) c (by omega) (effectiveRivalBids i d) (b x.1) := by
    have hp := hprofile.mono fun d hd => congrArg (fun μ : CountLaw (k+1) => μ.load) (hd i)
    simp only [IndependentCounts.binomial_load] at hp
    have hpres : MeasurePreserving (fun z : UserDraw (k+1) × UserProfile m (k+1) =>
        Function.update z.2 i z.1) ((userLaw Γ).prod (userProfileLaw Γ)) (userProfileLaw Γ) :=
      ⟨Resample.measurable_update_pair i,Resample.map_update_eq (userLaw Γ) i⟩
    have hup := Measure.ae_ae_of_ae_prod (hpres.quasiMeasurePreserving.ae hp)
    have hx := Measure.ae_ae_of_ae_prod hup
    filter_upwards [hx,heq] with x hxx he
    filter_upwards [hxx] with r hr
    filter_upwards [hr] with d hd
    rw [hd,mul_div_cancel_left₀ _ (by positivity : (((k+1:ℕ):ℝ)) ≠ 0)]
    unfold profileMarginal effectiveRivalBids
    simp only [Function.update_self,he]
    congr 1
    funext l
    rw [Function.update_of_ne l.property]
  exact ae_all_iff.mpr fun i => Measure.ae_ae_of_ae_compProd (hi i)

end FCAppendix.Bayes

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_eventual_type_profileMarginal
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (b : ℕ → ℝ → ℝ)
    (heq : ∀ᶠ t in atTop, ∀ᵐ z ∂((Γ t).F ⊗ₘ (Γ t).σ), effectiveBid z.2=b t z.1) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    ∀ᶠ t in atTop, ∀ᵐ v ∂F, ∀ i : Fin (M t), ∀ᵐ a ∂(Γ t).σ v,
      ∀ᵐ r ∂permLaw (k+1), ∀ᵐ d ∂userProfileLaw (Γ t),
        (profileCountLaw (Γ t) (Function.update d i ((v,a),r)) i).load/((k+1:ℕ):ℝ)=
          allocation (k+1) (C t) hn (effectiveRivalBids i d) (b t v) := by
  dsimp only
  filter_upwards [h.eventually_scarce,heq] with t ht he
  have hr := ae_positive_broadcast_or_abstain (Γ t) ht.1 ht.2 (h.action_schedule t)
    (h.base_schedule t) (h.users t) (B t) (h.proposers t) (h.symmetry t)
    (h.positive_values_atomless t) (h.inactive_abstain t)
  simpa only [h.common_values t] using ae_type_profileMarginal_eq_dummy (Γ t) h.proposers_two
    (h.action_schedule t) (B t) (h.proposers t) (h.symmetry t) hr (b t) he

end FCAppendix.Bayes
