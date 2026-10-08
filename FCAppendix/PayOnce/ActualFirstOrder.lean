import FCAppendix.PayOnce.KernelAgreement
import FCAppendix.PayOnce.NullClipping
import FCAppendix.PayOnce.SupportedFOC

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set
open scoped ProbabilityTheory BigOperators
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem ae_actual_payOnce_first_order {k : ℕ} (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hcm : c ≤ m)
    (hA : Γ.A = Schedule.once (k+1)) (hG : Γ.G = Schedule.once (k+1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hatom : PositiveVisibleAtomless Γ)
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = k+1)
    (hbid : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.bid) (i : Fin m) :
    let Q := PayOnce.AnalyticalKernel.coverage (k+1) c (by omega)
      (by simpa only [card_rival_add_one] using hcm) (analyticalRivalLaw Γ i)
    ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ),
      HasDerivAt Q (deriv Q x.2.bid) x.2.bid ∧
      Q x.2.bid = (x.1 - Γ.g - x.2.bid) * deriv Q x.2.bid := by
  dsimp only
  let Q := PayOnce.AnalyticalKernel.coverage (k+1) c (by omega)
    (by simpa only [card_rival_add_one] using hcm) (analyticalRivalLaw Γ i)
  letI := nullSingleton_realBidLaw_of_full_routes Γ (by omega) hatom hroute hbid
  obtain ⟨S, _, hS, hposS, hagree⟩ :=
    exists_common_analytical_agreement_set Γ hk hcm hA B hB hsym hroute hbid i
  have hside := PayOnce.SupportedFOC.ae_two_sided_accumulation (realBidLaw Γ) hS
  have hreg := PayOnce.NullClipping.ae_regularClearing (ι := Rival i) (realBidLaw Γ)
    (by omega : 2 ≤ k+1) (by simpa only [card_rival_add_one] using hcm) (ae_realBidLaw_pos Γ hbid)
  rw [← analyticalRivalLaw_eq_pi Γ i] at hreg
  rw [realBidLaw_eq_action_map] at hside hS hreg
  have hside' := ae_of_ae_map ((measurable_bid (k+1)).comp measurable_snd).aemeasurable hside
  have hS' := ae_of_ae_map ((measurable_bid (k+1)).comp measurable_snd).aemeasurable hS
  have hreg' := ae_of_ae_map ((measurable_bid (k+1)).comp measurable_snd).aemeasurable hreg
  filter_upwards [hside', hS', hreg', hbid, hroute, ae_bestResponse_compProd Γ hu i]
    with x hside hS hr hb hroute hbest
  have hD := PayOnce.AnalyticalKernel.hasDerivAt_coverage_of_regular
    (by omega : 2 ≤ k+1) (by simpa only [card_rival_add_one] using hcm)
    (analyticalRivalLaw Γ i) hb hr
  have hQ : HasDerivAt Q (deriv Q x.2.bid) x.2.bid := hD.2.differentiableAt.hasDerivAt
  refine ⟨hQ, ?_⟩
  apply PayOnce.SupportedFOC.payOnce_first_order_condition hQ hside.1 hside.2
  intro b hbS
  let a := fullBid (k+1) b (hposS b hbS).le
  have ha : a.bid = b := rfl
  have har : a.routeCount = k+1 := rfl
  have hqa := hagree b hbS a ha har
  have hqx := hagree x.2.bid hS x.2 rfl hroute
  have hcmp := hbest a
  rw [payoff_once Γ hA hG, payoff_once Γ hA hG, hqa, hqx, ha] at hcmp
  change (x.1 - b - Γ.g) * Q b ≤ (x.1 - x.2.bid - Γ.g) * Q x.2.bid at hcmp
  convert hcmp using 1 <;> ring

theorem ae_active_payOnce_first_order {k : ℕ} (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A = Schedule.once (k+1)) (hG : Γ.G = Schedule.once (k+1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hatom : PositiveVisibleAtomless Γ) (hvalue : PositiveValueAtomless Γ)
    (hactive : ∀ᵐ v ∂Γ.F, Γ.g < v) (i : Fin m) :
    let Q := PayOnce.AnalyticalKernel.coverage (k+1) c (by omega)
      (by simpa only [card_rival_add_one] using hcm.le) (analyticalRivalLaw Γ i)
    ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ),
      HasDerivAt Q (deriv Q x.2.bid) x.2.bid ∧
      Q x.2.bid = (x.1 - Γ.g - x.2.bid) * deriv Q x.2.bid := by
  have hfull := ae_full_routes_positive_bids_of_active Γ hc hcm hA hG hu B hB hsym hvalue hactive
  exact ae_actual_payOnce_first_order Γ hk hcm.le hA hG hu B hB hsym hatom
    (hfull.mono fun _ h => h.2) (hfull.mono fun _ h => h.1) i

end FCAppendix.Bayes

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set
open scoped ProbabilityTheory BigOperators
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem ae_actual_payOnce_weighted_first_order {k : ℕ} (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hcm : c ≤ m)
    (hA : Γ.A = Schedule.once (k+1)) (hG : Γ.G = Schedule.once (k+1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hatom : PositiveVisibleAtomless Γ)
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = k+1)
    (hbid : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.bid) (i : Fin m) :
    let hn : 2 ≤ k+1 := by omega
    let hc : c ≤ Fintype.card (Rival i)+1 := by simpa only [card_rival_add_one] using hcm
    let μ := analyticalRivalLaw Γ i
    let p := PayOnce.AnalyticalKernel.allocation (k+1) c hn hc
    let Q := PayOnce.AnalyticalKernel.coverage (k+1) c hn hc μ
    ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), ∃ weight : (Rival i → ℝ) → ℝ,
      Measurable weight ∧ (∀ rivals, weight rivals ∈ Icc (0 : ℝ) 1) ∧
      (∀ rivals, 1 / (((k+1 : ℕ) : ℝ)^3+1) ≤ 1-weight rivals) ∧
      HasDerivAt Q
        ((∫ rivals, PayOnce.RareSuccessSlope.weightedSlope (k+1) (p rivals x.2.bid) (weight rivals) ∂μ) / x.2.bid) x.2.bid ∧
      Q x.2.bid = (x.1 - Γ.g - x.2.bid) *
        ((∫ rivals, PayOnce.RareSuccessSlope.weightedSlope (k+1) (p rivals x.2.bid) (weight rivals) ∂μ) / x.2.bid) := by
  dsimp only
  letI := nullSingleton_realBidLaw_of_full_routes Γ (by omega) hatom hroute hbid
  have hreg := PayOnce.NullClipping.ae_regularClearing (ι := Rival i) (realBidLaw Γ)
    (by omega : 2 ≤ k+1) (by simpa only [card_rival_add_one] using hcm) (ae_realBidLaw_pos Γ hbid)
  rw [← analyticalRivalLaw_eq_pi Γ i, realBidLaw_eq_action_map] at hreg
  have hr := ae_of_ae_map ((measurable_bid (k+1)).comp measurable_snd).aemeasurable hreg
  have hfoc := ae_actual_payOnce_first_order Γ hk hcm hA hG hu B hB hsym hatom hroute hbid i
  filter_upwards [hr, hfoc, hbid] with x hx hf hb
  obtain ⟨weight, hw, hbound, hgap, _, hD⟩ :=
    PayOnce.AnalyticalKernel.exists_measurable_weight_coverage_derivative
      (by omega : 2 ≤ k+1) (by simpa only [card_rival_add_one] using hcm)
      (analyticalRivalLaw Γ i) hb hx
  exact ⟨weight, hw, hbound, hgap, hD, by simpa only [hD.deriv] using hf.2⟩

end FCAppendix.Bayes
