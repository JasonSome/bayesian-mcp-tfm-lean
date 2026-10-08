import FCAppendix.PayOnce.InactiveEventualPopulation
import FCAppendix.PayOnce.EffectiveFocalTransport
import FCAppendix.PayOnce.ActiveProfileMeans
import FCAppendix.PayOnce.InactiveAllocationMoments

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList Real
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel PayOnce.CovarianceConcentration
open scoped BigOperators
variable {m n c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem integral_dummy_marginal_eq_pure_mean (Γ : FiniteGame m n c Seed) (hn : 2 ≤ n)
    (i : Fin m) (b : ℝ → ℝ)
    (heq : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), effectiveBid x.2 = b x.1) :
    (∫ d, dummyProfileMarginal Γ hn d i ∂userProfileLaw Γ) =
      ∫ v, ∫ r : Fin (m-1) → ℝ, allocation n c hn r (b v)
        ∂Measure.pi (fun _ : Fin (m-1) => (BidScaling.realBidLaw Γ : Measure ℝ)) ∂Γ.F := by
  let μ := Measure.pi (fun _ : Rival i => (BidScaling.realBidLaw Γ : Measure ℝ))
  let p := fun z : (ℝ × JointAction n) × (Rival i → ℝ) => allocation n c hn z.2 (effectiveBid z.1.2)
  have hp : Measurable p := (measurable_allocation_joint hn).comp
    ((((measurable_effectiveBid n).comp measurable_snd).comp measurable_fst).prodMk measurable_snd)
  have hi : Integrable p ((Γ.F ⊗ₘ Γ.σ).prod μ) := UnitInterval.integrable _ _ hp
    (fun z => (allocation_bounds hn z.2 (effectiveBid z.1.2)).1)
    (fun z => (allocation_bounds hn z.2 (effectiveBid z.1.2)).2)
  have hpres := focalAction_effectiveRivals_measurePreserving Γ i
  have hcard : Fintype.card (Fin (m-1)) = Fintype.card (Rival i) := by
    have hh := card_rival_add_one i
    simp only [Fintype.card_fin]
    omega
  let e : Fin (m-1) ≃ Rival i := Fintype.equivOfCardEq hcard
  calc
    _ = ∫ z, p z ∂((Γ.F ⊗ₘ Γ.σ).prod μ) := by
      rw [← hpres.map_eq]
      exact (integral_map hpres.measurable.aemeasurable hp.aestronglyMeasurable).symm
    _ = ∫ x, ∫ r, p (x,r) ∂μ ∂(Γ.F ⊗ₘ Γ.σ) := integral_prod _ hi
    _ = ∫ v, ∫ a, ∫ r, p ((v,a),r) ∂μ ∂Γ.σ v ∂Γ.F :=
      Measure.integral_compProd hi.integral_prod_left
    _ = ∫ v, ∫ r, allocation n c hn r (b v) ∂μ ∂Γ.F := by
      apply integral_congr_ae
      filter_upwards [Measure.ae_ae_of_ae_compProd heq] with v hv
      have hh : (fun a : JointAction n => ∫ r, p ((v,a),r) ∂μ) =ᵐ[Γ.σ v]
          fun _ => ∫ r, allocation n c hn r (b v) ∂μ := by
        filter_upwards [hv] with a ha
        simp only [p,ha]
      rw [integral_congr_ae hh]
      simp only [integral_const,probReal_univ,one_smul]
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun v =>
        (integral_allocation_test_equiv e hn (BidScaling.realBidLaw Γ : Measure ℝ) (b v) id).symm

theorem integral_dummy_population_mean_eq_pure_mean (Γ : FiniteGame m n c Seed)
    (hn : 2 ≤ n) (hm : 0 < m) (b : ℝ → ℝ)
    (heq : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), effectiveBid x.2 = b x.1) :
    (∫ d, populationMean (dummyProfileMarginal Γ hn d) ∂userProfileLaw Γ) =
      ∫ v, ∫ r : Fin (m-1) → ℝ, allocation n c hn r (b v)
        ∂Measure.pi (fun _ : Fin (m-1) => (BidScaling.realBidLaw Γ : Measure ℝ)) ∂Γ.F := by
  have hi i : Integrable (fun d => dummyProfileMarginal Γ hn d i) (userProfileLaw Γ) :=
    UnitInterval.integrable _ _ (measurable_dummyProfileMarginal Γ hn i)
      (fun d => (dummyProfileMarginal_bounds Γ hn d i).1)
      (fun d => (dummyProfileMarginal_bounds Γ hn d i).2)
  rw [integral_populationMean _ _ hi]
  simp only [populationMean,integral_dummy_marginal_eq_pure_mean Γ hn _ b heq,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hm.ne')

theorem integral_pure_mean_eq_load_div (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A = Schedule.once (k+1)) (hG : Γ.G = Schedule.once (k+1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ) (hB : PosteriorProposerOptimalAE Γ B)
    (hsym : SymmetricProposersOnPath Γ) (hvalue : PositiveValueAtomless Γ)
    (hinactive : InactiveAbstain Γ) (b : ℝ → ℝ)
    (heq : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), effectiveBid x.2 = b x.1) :
    (∫ v, ∫ r : Fin (m-1) → ℝ, allocation (k+1) c (by omega) r (b v)
      ∂Measure.pi (fun _ : Fin (m-1) => (BidScaling.realBidLaw Γ : Measure ℝ)) ∂Γ.F) =
      finiteLoad Γ/((k+1:ℕ):ℝ) := by
  rw [← integral_dummy_population_mean_eq_pure_mean Γ (by omega) (hc.trans hcm) b heq]
  have hh : (fun d => populationMean (dummyProfileMarginal Γ (by omega) d)) =ᵐ[userProfileLaw Γ]
      fun d => profileLoad Γ d/((k+1:ℕ):ℝ) := by
    filter_upwards [ae_dummy_marginal_active_capacity Γ hk hc hcm hA hG hu B hB hsym hvalue,
      ae_profileLoad_eq_activeCapacity Γ hk hc hcm hA hG hu B hB hsym hvalue hinactive] with d hd hl
    simp only [populationMean,Fintype.card_fin,hd.2,hl]
    field_simp
  rw [integral_congr_ae hh,integral_div]
  rfl

theorem payOnce_inactive_pure_mean_capacity_exponential
    {M C : ℕ → ℕ} (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) (b : ℕ → ℝ → ℝ)
    (heq : ∀ᶠ t in atTop, ∀ᵐ x ∂((Γ t).F ⊗ₘ (Γ t).σ), effectiveBid x.2 = b t x.1) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    ∃ q : ℝ, 0 < q ∧ ∀ᶠ t in atTop,
      0 ≤ (C t:ℝ)/(M t)-(∫ v, ∫ r : Fin (M t-1) → ℝ, allocation (k+1) (C t) hn r (b t v)
        ∂Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)) ∂F) ∧
      (C t:ℝ)/(M t)-(∫ v, ∫ r : Fin (M t-1) → ℝ, allocation (k+1) (C t) hn r (b t v)
        ∂Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)) ∂F) ≤
        exp (-q*(M t:ℝ)) := by
  dsimp only
  obtain ⟨q,hq,hunder⟩ := activeUserCount_underfill_exponential Γ h.population_grows F
    h.common_values h.common_fee h.capacity_ratio h.capacity_bounds.2
  refine ⟨q,hq,?_⟩
  filter_upwards [heq,h.eventually_scarce,hunder] with t hp ht hu
  have he := integral_pure_mean_eq_load_div (Γ t) h.proposers_two ht.1 ht.2
    (h.action_schedule t) (h.base_schedule t) (h.users t) (B t) (h.proposers t)
    (h.symmetry t) (h.positive_values_atomless t) (h.inactive_abstain t) (b t) hp
  rw [h.common_values t] at he
  rw [he]
  have hdef := payOnce_load_shortfall_bound (Γ t) h.proposers_two ht.1 ht.2
    (h.action_schedule t) (h.base_schedule t) (h.users t) (B t) (h.proposers t)
    (h.symmetry t) (h.positive_values_atomless t) (h.inactive_abstain t)
  have hnR : (0:ℝ) < (k+1:ℕ) := by positivity
  have hid : (C t:ℝ)/(M t)-finiteLoad (Γ t)/((k+1:ℕ):ℝ) =
      (((k+1:ℕ):ℝ)*(C t:ℝ)/(M t)-finiteLoad (Γ t))/((k+1:ℕ):ℝ) := by
    rw [sub_div,mul_div_assoc,mul_div_cancel_left₀ _ hnR.ne']
  rw [hid]
  refine ⟨div_nonneg hdef.1 hnR.le,?_⟩
  apply (div_le_iff₀ hnR).mpr
  exact hdef.2.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hu hnR.le)

theorem payOnce_inactive_pure_mean_capacity_isLittleO
    {M C : ℕ → ℕ} (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) (b : ℕ → ℝ → ℝ)
    (heq : ∀ᶠ t in atTop, ∀ᵐ x ∂((Γ t).F ⊗ₘ (Γ t).σ), effectiveBid x.2 = b t x.1) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    (fun t => (∫ v, ∫ r : Fin (M t-1) → ℝ, allocation (k+1) (C t) hn r (b t v)
      ∂Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)) ∂F)-
        (C t:ℝ)/(M t)) =o[atTop] (fun t => (M t:ℝ)^(-(1:ℝ)/2)) := by
  dsimp only
  obtain ⟨q,hq,hdef⟩ := payOnce_inactive_pure_mean_capacity_exponential Γ B F g ρ h b heq
  have hexp := (isLittleO_exp_neg_mul_rpow_atTop hq (-(1:ℝ)/2)).comp_tendsto
    (tendsto_natCast_atTop_atTop.comp h.population_grows)
  have hbig : (fun t => (C t:ℝ)/(M t)-
      (∫ v, ∫ r : Fin (M t-1) → ℝ, allocation (k+1) (C t)
        (by have := h.proposers_two; omega) r (b t v)
        ∂Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)) ∂F))
      =O[atTop] (fun t => exp (-q*(M t:ℝ))) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [hdef] with t ht
    simpa only [Real.norm_eq_abs,abs_of_nonneg ht.1,abs_of_pos (exp_pos _),one_mul] using ht.2
  simpa only [Pi.neg_apply,neg_sub,Function.comp_def] using (hbig.trans_isLittleO hexp).neg_left

end FCAppendix.Bayes
