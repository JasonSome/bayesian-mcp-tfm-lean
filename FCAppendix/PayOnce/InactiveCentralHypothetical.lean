import FCAppendix.PayOnce.InactiveCentralApproximation

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList Real
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel Probability
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_central_hypothetical_success_utility
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (x : ℕ → ℝ) {x₀ : ℝ} (hx : Tendsto x atTop (𝓝 x₀))
    (i : ∀ t, Fin (M t)) (a : ℕ → JointAction (k+1))
    (ha : ∀ᶠ t in atTop, (problem (Γ t) (i t)).BestResponse
      (inactiveCentralValue M C F (k+1) g ρ (x t) t) (a t)) :
    Tendsto (fun t => ((problem (Γ t) (i t)).outcome (a t)).success /
      inactiveGaussianScale M F (k+1) g ρ t) atTop
        (𝓝 (inactiveCentralLimit F (k+1) g ρ x₀ 1)) ∧
    Tendsto (fun t => (problem (Γ t) (i t)).envelope
      (inactiveCentralValue M C F (k+1) g ρ (x t) t) /
        (inactiveGaussianScale M F (k+1) g ρ t)^2) atTop
          (𝓝 (inactiveCentralLimit F (k+1) g ρ x₀ 3)) := by
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  obtain ⟨_hL,_hD,b,hmono,_hmeas,hbound,heq,hlim⟩ := payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h
  obtain ⟨A,hA,hregular⟩ := payOnce_inactive_central_regular_set Γ B F g ρ h b heq
  let P := fun t v => v ∈ A ∧ ∀ᵐ act ∂(Γ t).σ v, (problem (Γ t) (i t)).BestResponse v act
  have hP t : ∀ᵐ v ∂F, P t v := by
    have hh := h.users t (i t)
    rw [h.common_values t] at hh
    exact hA.and hh
  obtain ⟨l,r,hl,hr,hbr⟩ := payOnce_inactive_central_regular_brackets Γ B F g ρ h hlocal P hP x hx
  have hprof (z : ℕ → ℝ) (hz : Tendsto z atTop (𝓝 x₀))
      (hAz : ∀ᶠ t in atTop, inactiveCentralValue M C F (k+1) g ρ (z t) t ∈ A) (j : Fin 4) :
      Tendsto (fun t => inactiveActualCentralObservables Γ F g ρ b t (i t) (z t) j)
        atTop (𝓝 (inactiveCentralLimit F (k+1) g ρ x₀ j)) := by
    have hpos := (payOnce_inactive_central_value_tendsto Γ B F g ρ h z hz).eventually
      (Ioi_mem_nhds _hL)
    have hreg : ∀ᶠ t in atTop, InactiveCentralRegular Γ hn g b t
        (inactiveCentralValue M C F (k+1) g ρ (z t) t) := by
      filter_upwards [hregular,hAz,hpos] with t ht htz hp
      exact ht _ htz (by linarith)
    have hh := payOnce_inactive_central_profiles_tendsto Γ B F g ρ h hlocal b hmono
      (fun t v => (hbound t v).2) hlim z hz (hreg.mono fun _ ht => ht.1) j
    apply hh.congr'
    filter_upwards [hreg] with t ht
    exact congrFun (inactiveActualCentralObservables_eq Γ hn F g ρ b t (z t) ht (i t)).symm j
  have hlA := hbr.mono fun _ ht => ht.2.2.1.1
  have hrA := hbr.mono fun _ ht => ht.2.2.2.1
  have hbounds : ∀ᶠ t in atTop,
      (typeOutcome (Γ t) (i t) (inactiveCentralValue M C F (k+1) g ρ (l t) t)).success ≤
        ((problem (Γ t) (i t)).outcome (a t)).success ∧
      ((problem (Γ t) (i t)).outcome (a t)).success ≤
        (typeOutcome (Γ t) (i t) (inactiveCentralValue M C F (k+1) g ρ (r t) t)).success ∧
      (problem (Γ t) (i t)).envelope (inactiveCentralValue M C F (k+1) g ρ (l t) t) ≤
        (problem (Γ t) (i t)).envelope (inactiveCentralValue M C F (k+1) g ρ (x t) t) ∧
      (problem (Γ t) (i t)).envelope (inactiveCentralValue M C F (k+1) g ρ (x t) t) ≤
        (problem (Γ t) (i t)).envelope (inactiveCentralValue M C F (k+1) g ρ (r t) t) := by
    filter_upwards [hbr,ha,h.population_grows.eventually_gt_atTop 0] with t ht hat hmt
    have hs := payOnce_inactive_gaussian_scale_pos Γ B F g ρ h hlocal hmt
    have hlo : inactiveCentralValue M C F (k+1) g ρ (l t) t <
        inactiveCentralValue M C F (k+1) g ρ (x t) t := by
      dsimp only [inactiveCentralValue]; nlinarith [ht.1]
    have hhi : inactiveCentralValue M C F (k+1) g ρ (x t) t <
        inactiveCentralValue M C F (k+1) g ρ (r t) t := by
      dsimp only [inactiveCentralValue]; nlinarith [ht.2.1]
    refine ⟨?_,?_,(problem (Γ t) (i t)).envelope_monotone hlo.le,
      (problem (Γ t) (i t)).envelope_monotone hhi.le⟩
    · simp only [CountLaw.success,typeOutcome_expect]
      change (∫ act, ((problem (Γ t) (i t)).outcome act).success ∂(Γ t).σ _) ≤ _
      have hh := integral_mono_ae (integrable_success_strategy (Γ t) (i t) _)
        (integrable_const (((problem (Γ t) (i t)).outcome (a t)).success))
        (ht.2.2.1.2.mono fun act hact => (problem (Γ t) (i t)).success_order _ _ hlo act (a t) hact hat)
      simpa only [integral_const,probReal_univ,one_smul,CountLaw.success] using hh
    · simp only [CountLaw.success,typeOutcome_expect]
      change _ ≤ (∫ act, ((problem (Γ t) (i t)).outcome act).success ∂(Γ t).σ _)
      have hh := integral_mono_ae
        (integrable_const (((problem (Γ t) (i t)).outcome (a t)).success))
        (integrable_success_strategy (Γ t) (i t) _)
        (ht.2.2.2.2.mono fun act hact => (problem (Γ t) (i t)).success_order _ _ hhi (a t) act hat hact)
      simpa only [integral_const,probReal_univ,one_smul,CountLaw.success] using hh
  have hspos : ∀ᶠ t in atTop, 0 < inactiveGaussianScale M F (k+1) g ρ t :=
    (h.population_grows.eventually_gt_atTop 0).mono fun t ht =>
      payOnce_inactive_gaussian_scale_pos Γ B F g ρ h hlocal ht
  constructor
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (hprof l hl hlA 1) (hprof r hr hrA 1)
    · filter_upwards [hbounds,hspos] with t ht hs
      exact div_le_div_of_nonneg_right ht.1 hs.le
    · filter_upwards [hbounds,hspos] with t ht hs
      exact div_le_div_of_nonneg_right ht.2.1 hs.le
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (hprof l hl hlA 3) (hprof r hr hrA 3)
    · filter_upwards [hbounds] with t ht
      exact div_le_div_of_nonneg_right ht.2.2.1 (sq_nonneg _)
    · filter_upwards [hbounds] with t ht
      exact div_le_div_of_nonneg_right ht.2.2.2 (sq_nonneg _)

theorem payOnce_inactive_central_hypothetical_bid
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (x : ℕ → ℝ) {x₀ : ℝ} (hx : Tendsto x atTop (𝓝 x₀))
    (i : ∀ t, Fin (M t)) (a : ℕ → JointAction (k+1))
    (ha : ∀ᶠ t in atTop, (problem (Γ t) (i t)).BestResponse
      (inactiveCentralValue M C F (k+1) g ρ (x t) t) (a t)) :
    Tendsto (fun t => ((a t).bid-inactiveValuePrice M C F (k+1) g t)/
      inactiveGaussianScale M F (k+1) g ρ t) atTop
        (𝓝 (GaussianResponse.response x₀)) := by
  obtain ⟨hS,hU⟩ := payOnce_inactive_central_hypothetical_success_utility Γ B F g ρ h hlocal x hx i a ha
  have hL := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  have hn : (1:ℝ) < (k+1:ℕ) := by exact_mod_cast (show 1 < k+1 by have := h.proposers_two; omega)
  have hQ : 0 < inactiveCentralLimit F (k+1) g ρ x₀ 1 := by
    dsimp only [inactiveCentralLimit]
    have hT := GaussianResponse.successPrimitive_pos (GaussianResponse.response x₀)
    exact mul_pos (mul_pos (lt_trans zero_lt_one hn)
      (div_pos (by norm_num) (mul_pos (sub_pos.mpr hn) hL))) hT
  have hh := hx.sub (hU.div hS hQ.ne')
  have he : x₀-inactiveCentralLimit F (k+1) g ρ x₀ 3 /
      inactiveCentralLimit F (k+1) g ρ x₀ 1=GaussianResponse.response x₀ := by
    have heq : inactiveCentralLimit F (k+1) g ρ x₀ 3=
      (x₀-GaussianResponse.response x₀)*inactiveCentralLimit F (k+1) g ρ x₀ 1 := rfl
    rw [heq,mul_div_cancel_right₀ _ hQ.ne']
    ring
  rw [he] at hh
  apply hh.congr'
  filter_upwards [ha,h.population_grows.eventually_gt_atTop 0,
    hS.eventually (Ioi_mem_nhds hQ)] with t hat hmt hqt
  have hs := payOnce_inactive_gaussian_scale_pos Γ B F g ρ h hlocal hmt
  have hst : 0 < ((problem (Γ t) (i t)).outcome (a t)).success :=
    (div_pos_iff.mp hqt).resolve_right (fun hh => (not_lt_of_ge hs.le hh.2)) |>.1
  have hu := ((problem (Γ t) (i t)).bestResponse_iff_attains _ _).mp hat
  rw [payoff_once (Γ t) (h.action_schedule t) (h.base_schedule t),h.common_fee t] at hu
  dsimp only [Pi.div_apply]
  rw [← hu]
  dsimp only [inactiveCentralValue]
  field_simp [hs.ne',hst.ne']
  ring

end FCAppendix.Bayes
