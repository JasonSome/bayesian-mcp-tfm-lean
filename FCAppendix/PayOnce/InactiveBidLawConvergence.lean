import FCAppendix.PayOnce.InactiveEventualPureBids

namespace FCAppendix.PayOnce
open MeasureTheory ProbabilityTheory Filter Topology

theorem tendsto_probability_map_of_ae_tendsto
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    (μ : ProbabilityMeasure Ω) (f : ℕ → Ω → X) (hf : ∀ t, Measurable (f t))
    (q : Ω → X) (hq : Measurable q)
    (hlim : ∀ᵐ ω ∂(μ : Measure Ω), Tendsto (fun t => f t ω) atTop (𝓝 (q ω))) :
    Tendsto (fun t => μ.map (hf t).aemeasurable) atTop (𝓝 (μ.map hq.aemeasurable)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro test
  change Tendsto (fun t => ∫ x, test x ∂Measure.map (f t) (μ : Measure Ω)) atTop
    (𝓝 (∫ x, test x ∂Measure.map q (μ : Measure Ω)))
  simp_rw [integral_map (hf _).aemeasurable test.continuous.aestronglyMeasurable,
    integral_map hq.aemeasurable test.continuous.aestronglyMeasurable]
  apply tendsto_integral_of_dominated_convergence (fun _ : Ω => ‖test‖)
  · intro t
    exact (test.continuous.measurable.comp (hf t)).aestronglyMeasurable
  · exact integrable_const _
  · intro t
    exact Eventually.of_forall fun ω => test.norm_coe_le_norm (f t ω)
  · filter_upwards [hlim] with ω hω
    exact test.continuous.continuousAt.tendsto.comp hω

end FCAppendix.PayOnce

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CompactifiedBidLaws
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem measurable_inactiveLimitBid (n : ℕ) (g L : ℝ) :
    Measurable (fun v : ℝ => Limit.bidStar n L (max (v-g) 0)) := by
  have hb : Measurable (Limit.bidStar n L) := by
    unfold Limit.bidStar
    exact Measurable.ite (measurableSet_le measurable_id measurable_const)
      (measurable_id.max measurable_const)
      (measurable_const.div ((continuous_H n).measurable.comp (Limit.measurable_pStar n L)))
  exact hb.comp ((measurable_id.sub_const g).max measurable_const)

noncomputable def inactiveLimitBidLaw (F : Measure ℝ) [IsProbabilityMeasure F]
    (n : ℕ) (g L : ℝ) : ProbabilityMeasure ENNReal :=
  ProbabilityMeasure.map (⟨F,inferInstance⟩ : ProbabilityMeasure ℝ)
    (ENNReal.measurable_ofReal.comp (measurable_inactiveLimitBid n g L)).aemeasurable

theorem inactiveLimitBidLaw_toMeasure (F : Measure ℝ) [IsProbabilityMeasure F]
    (n : ℕ) (g L : ℝ) :
    (inactiveLimitBidLaw F n g L : Measure ENNReal) =
      F.map (fun v => ENNReal.ofReal (Limit.bidStar n L (max (v-g) 0))) := rfl

theorem bidLaw_eq_map_of_effective_pure
    {m n c : ℕ} (Γ : FiniteGame m n c Seed) (b : ℝ → ℝ) (hb : Measurable b)
    (heq : ∀ᵐ z ∂(Γ.F ⊗ₘ Γ.σ), effectiveBid z.2 = b z.1) :
    (bidLaw Γ : Measure ENNReal) = Γ.F.map (fun v => ENNReal.ofReal (b v)) := by
  have hreal : (BidScaling.realBidLaw Γ : Measure ℝ) = Γ.F.map b := by
    rw [realEffectiveBidLaw_eq_action_map]
    calc
      (Γ.F ⊗ₘ Γ.σ).map (fun z => effectiveBid z.2) =
          (Γ.F ⊗ₘ Γ.σ).map (fun z => b z.1) := Measure.map_congr heq
      _ = Γ.F.map b := by
        conv_rhs => rw [← Measure.fst_compProd Γ.F Γ.σ]
        exact (Measure.map_map hb measurable_fst).symm
  rw [compactifiedBidLaw_eq_map_effectiveBidLaw,hreal,Measure.map_map ENNReal.measurable_ofReal hb]
  rfl

theorem payOnce_inactive_bidLaw_tendsto
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) :
    let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
    Tendsto (fun t => bidLaw (Γ t)) atTop (𝓝 (inactiveLimitBidLaw F (k+1) g L)) := by
  dsimp only
  let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
  obtain ⟨_,_,b,_,hb,_,heq,hlim⟩ := payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h
  let P : ProbabilityMeasure ℝ := ⟨F,inferInstance⟩
  have hweak := tendsto_probability_map_of_ae_tendsto P
    (fun t v => ENNReal.ofReal (b t v)) (fun t => ENNReal.measurable_ofReal.comp (hb t))
    (fun v => ENNReal.ofReal (Limit.bidStar (k+1) L (max (v-g) 0)))
    (ENNReal.measurable_ofReal.comp (measurable_inactiveLimitBid (k+1) g L))
    (hlim.mono fun _ hv => ENNReal.continuous_ofReal.continuousAt.tendsto.comp hv)
  apply hweak.congr'
  filter_upwards [heq] with t ht
  apply Subtype.ext
  change F.map (fun v => ENNReal.ofReal (b t v)) = (bidLaw (Γ t) : Measure ENNReal)
  simpa only [h.common_values t] using (bidLaw_eq_map_of_effective_pure (Γ t) (b t) (hb t) ht).symm

end FCAppendix.Bayes
