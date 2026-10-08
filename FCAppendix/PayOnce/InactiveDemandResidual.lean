import FCAppendix.PayOnce.InactiveCapacityResidual
import FCAppendix.PayOnce.InactiveUniformResponse
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace FCAppendix.Probability
open MeasureTheory Filter Topology Real

theorem integral_isLittleO_of_ae_scaled_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : ℕ → Ω → ℝ) (s : ℕ → ℝ) (D : ℝ)
    (hf : ∀ t, AEStronglyMeasurable (f t) μ)
    (hs : ∀ᶠ t in atTop, 0 < s t)
    (hbound : ∀ᶠ t in atTop, ∀ᵐ x ∂μ, |f t x| ≤ D*s t)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun t => f t x/s t) atTop (𝓝 0)) :
    (fun t => ∫ x, f t x ∂μ) =o[atTop] s := by
  apply (Asymptotics.isLittleO_iff_tendsto' (hs.mono fun _ ht hz => (ht.ne' hz).elim)).mpr
  have hh := tendsto_integral_filter_of_dominated_convergence (μ := μ)
    (F := fun t x => f t x/s t) (f := fun _ => (0:ℝ)) (fun _ => D)
    (Eventually.of_forall fun t => by
      convert (hf t).const_smul (s t)⁻¹ using 1
      funext x
      simp only [Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm])
    (show ∀ᶠ t in atTop, ∀ᵐ x ∂μ, ‖f t x/s t‖ ≤ D from by
      filter_upwards [hs,hbound] with t ht hb
      filter_upwards [hb] with x hx
      rw [Real.norm_eq_abs,abs_div,abs_of_pos ht]
      exact (div_le_iff₀ ht).mpr hx)
    (integrable_const D) hlim
  simpa only [integral_div,integral_zero] using hh

end FCAppendix.Probability

namespace FCAppendix.PayOnce.DummyKernel
open MeasureTheory Set CommonList
variable {N n c : ℕ}

theorem measurable_mean_allocation (hn : 2 ≤ n)
    (μ : Measure (Fin N → ℝ)) [SFinite μ] {b : ℝ → ℝ} (hb : Measurable b) :
    Measurable (fun v => ∫ r, allocation n c hn r (b v) ∂μ) := by
  have hm : Measurable (fun z : ℝ × (Fin N → ℝ) => allocation n c hn z.2 (b z.1)) :=
    (measurable_allocation_joint hn).comp ((hb.comp measurable_fst).prodMk measurable_snd)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem integrable_mean_allocation (hn : 2 ≤ n)
    (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ]
    (F : Measure ℝ) [IsProbabilityMeasure F] {b : ℝ → ℝ} (hb : Measurable b) :
    Integrable (fun v => ∫ r, allocation n c hn r (b v) ∂μ) F := by
  apply UnitInterval.integrable F _ (measurable_mean_allocation hn μ hb)
  · intro v
    exact integral_nonneg fun r => (allocation_bounds hn r (b v)).1
  · intro v
    have hi := UnitInterval.integrable μ _ (measurable_allocation_fixed_bid hn (b v))
      (fun r => (allocation_bounds (c := c) hn r (b v)).1)
      (fun r => (allocation_bounds (c := c) hn r (b v)).2)
    have hh := integral_mono hi (integrable_const (1:ℝ))
      (fun r => (allocation_bounds hn r (b v)).2)
    simpa only [integral_const,probReal_univ,one_smul] using hh

end FCAppendix.PayOnce.DummyKernel

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList Real
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_demand_residual_of_pointwise
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (b : ℕ → ℝ → ℝ) (hmono : ∀ t, Monotone (b t))
    (hbound : ∀ t v, 0 ≤ b t v ∧ b t v ≤ max (v-g) 0)
    (heq : ∀ᶠ t in atTop, ∀ᵐ z ∂((Γ t).F ⊗ₘ (Γ t).σ), effectiveBid z.2 = b t z.1)
    (hlim : ∀ᵐ v ∂F, Tendsto (fun t => b t v) atTop
      (𝓝 (Limit.bidStar (k+1)
        (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ) (max (v-g) 0))))
    (hpoint : ∀ᵐ v ∂F, Tendsto (fun t =>
      ((∫ r : Fin (M t-1) → ℝ, allocation (k+1) (C t) (by have := h.proposers_two; omega) r (b t v)
        ∂Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)))-
          Limit.pStar (k+1) (KernelDemand.populationPrice (k+1)
            (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))) (max (v-g) 0)) /
              (M t:ℝ)^(-(1:ℝ)/2)) atTop (𝓝 0)) :
    (fun t => Limit.demand (F.map (fun v => max (v-g) 0)) (k+1)
      (KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t)))-
        (C t:ℝ)/(M t)) =o[atTop] (fun t => (M t:ℝ)^(-(1:ℝ)/2)) := by
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  let bar := fun t => KernelDemand.populationPrice (k+1)
    (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
  let μ := fun t => Measure.pi (fun _ : Fin (M t-1) =>
    (BidScaling.realBidLaw (Γ t) : Measure ℝ))
  let a := fun t v => ∫ r, allocation (k+1) (C t) hn r (b t v) ∂μ t
  let p := fun t v => Limit.pStar (k+1) (bar t) (max (v-g) 0)
  let δ := fun t => (M t:ℝ)^(-(1:ℝ)/2)
  have hnet : Measurable (fun v : ℝ => max (v-g) 0) :=
    (measurable_id.sub_const g).max measurable_const
  have ha t : Measurable (a t) := measurable_mean_allocation hn (μ t) (hmono t).measurable
  have hp t : Measurable (p t) := (Limit.measurable_pStar (k+1) (bar t)).comp hnet
  have hδ : ∀ᶠ t in atTop, 0 < δ t := by
    filter_upwards [h.population_grows.eventually_gt_atTop 0] with t ht
    exact rpow_pos_of_pos (Nat.cast_pos.mpr ht) _
  obtain ⟨D,_hD,hD⟩ := payOnce_inactive_response_error_for_pure Γ B F g ρ h hlocal
    b hmono hbound heq hlim
  have herr : (fun t => ∫ v, a t v-p t v ∂F) =o[atTop] δ :=
    Probability.integral_isLittleO_of_ae_scaled_tendsto F (fun t v => a t v-p t v) δ D
      (fun t => ((ha t).sub (hp t)).aestronglyMeasurable) hδ hD hpoint
  have hL := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  have hbarpos := (payOnce_inactive_population_price Γ B F g ρ h).2.eventually_const_lt hL
  have hid : ∀ᶠ t in atTop, (∫ v, a t v-p t v ∂F) =
      (∫ v, a t v ∂F)-Limit.demand (F.map (fun v => max (v-g) 0)) (k+1) (bar t) := by
    filter_upwards [hbarpos] with t ht
    have hpi : Integrable (p t) F := UnitInterval.integrable F _ (hp t)
      (fun _ => Limit.pStar_nonneg) (fun _ => Limit.pStar_le_one ht.le)
    rw [integral_sub (integrable_mean_allocation hn (μ t) F (hmono t).measurable) hpi]
    congr 1
    exact (integral_map hnet.aemeasurable
      (Limit.measurable_pStar (k+1) (bar t)).aestronglyMeasurable).symm
  have herr' := herr.congr' hid (Eventually.of_forall fun _ => rfl)
  have hmass := payOnce_inactive_pure_mean_capacity_isLittleO Γ B F g ρ h b heq
  apply (hmass.sub herr').congr' _ (Eventually.of_forall fun _ => rfl)
  exact Eventually.of_forall fun t => by dsimp only [a,bar,μ]; ring

end FCAppendix.Bayes
