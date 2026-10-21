import FCAppendix.Affine.Uniform06.SourcePrefixConstructor
import FCAppendix.Affine.Uniform06.SharpPureMeasure

noncomputable section
namespace FCAppendix.Affine.Uniform06.SourceRankFamily

open MeasureTheory Set Filter Topology
open Uniform07 LowBody Rank LiteralExperiment LiteralPrefixStieltjes
open LowRankMeasures CrossoverRankDensity SourcePrefixConstructor
open SharpPureDerivative SharpPureMeasure PureRankCounts PurePivotalSource

section Family
variable {C : ℕ → Type*}
    (G : ∀ m,C m → ProbabilityMeasure (ℝ × ℝ))
    (g : ∀ m,C m → GuardData)
    (cm : ∀ m,C m → (Fin (m-1) → Fin 4) → ℝ)

theorem eventually_source_rank_chain (i : Row)
    (hvalue : ∀ m (E : C m),(G m E:Measure (ℝ × ℝ)).map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hmenu : ∀ m (E : C m),∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),
      p.2 ∈ Icc (LowChernoff.physicalFloor i p.1) (min p.1 (ReceiptGap.cap i)))
    (hatom : ∀ m (E : C m) b,((G m E:Measure (ℝ × ℝ)).map Prod.snd) {b}=0)
    (hfields : ∀ m (E : C m),LiteralFields i (g m E))
    (hpsi : ∀ m (E : C m),
      (∫ p,PrefixRoot.sourcePsi i (g m E).rejectionRoot p.2 ∂(G m E:Measure (ℝ × ℝ)))=
        3*PrefixRoot.requiredDemand i)
    (hroot : ∀ ε > (0:ℝ),∀ᶠ m in atTop,∀ E : C m,|(g m E).multiplier-entry i| < ε)
    (hactive : ∀ a > (0:ℝ),∀ ε > (0:ℝ),∀ᶠ m in atTop,∀ E : C m,
      ∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),p.1 ∈ Ioc (entry i+a) (cutoff i) →
        |p.2-ActiveGraphComponent.activeBid i p.1| ≤ ε)
    (hIC : ∀ m (E : C m),∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),
      ∀ a ∈ Icc (LowChernoff.physicalFloor i p.1) (min p.1 (ReceiptGap.cap i)),
      payoff (eta i) p.1 a (sourceSuccess i m (G m E) (g m E) (cm m E) a)
        (sourceDuplicate i m (G m E) (g m E) (cm m E) a) ≤
      payoff (eta i) p.1 p.2 (sourceSuccess i m (G m E) (g m E) (cm m E) p.2)
        (sourceDuplicate i m (G m E) (g m E) (cm m E) p.2)) :
    ∃ γ : ℝ,0 < γ ∧ ∀ᶠ m in atTop,∀ E : C m,
      lowBidMeasure i (G m E) (crossoverEnd i) ≪ volume ∧
      (∀ lo : ℝ,0 < lo → ∀ A : Set ℝ,MeasurableSet A → A ⊆ Icc lo (crossoverEnd i) →
        (lowBidMeasure i (G m E) (crossoverEnd i)).real A ≤
          densityCoefficient i m (g m E) (crossoverEnd i)*
            (volume.real A/(1-contraction i m*kappa i)+
              (∫ b in A,1/b)/(1-contraction i m))) ∧
      ∀ lo : ℝ,0 < lo → kappa i*ReceiptGap.cap i < lo → lo < crossoverEnd i →
        (∃ F : StieltjesFunction ℝ,Continuous F ∧ (∀ b,F b ∈ Icc (0:ℝ) 1) ∧
          (∀ b ∈ Icc lo (crossoverEnd i),F b=
            expectedUnequalPureFirst (m-1) (capacity m) (kappa i) (cutoff i)
              ((G m E:Measure (ℝ × ℝ)).map Prod.snd) b) ∧
          F.measure.restrict (Ioc lo (crossoverEnd i)) ≪ volume) ∧
        (∀ᵐ b ∂(bidMeasure i (G m E)).restrict (Ioo lo (crossoverEnd i)),
          DifferentiableAt ℝ (sourceRank (cutoff i) ((G m E:Measure (ℝ × ℝ)).map Prod.snd)) b ∧
          DifferentiableAt ℝ (expectedUnequalPureFirst (m-1) (capacity m) (kappa i) (cutoff i)
            ((G m E:Measure (ℝ × ℝ)).map Prod.snd)) b ∧
          |deriv (expectedUnequalPureFirst (m-1) (capacity m) (kappa i) (cutoff i)
              ((G m E:Measure (ℝ × ℝ)).map Prod.snd)) b-
            2*rankSlope i m (sourceRank (cutoff i) ((G m E:Measure (ℝ × ℝ)).map Prod.snd) b)*
              deriv (sourceRank (cutoff i) ((G m E:Measure (ℝ × ℝ)).map Prod.snd)) b| ≤
            2*rankSlope i m (sourceRank (cutoff i) ((G m E:Measure (ℝ × ℝ)).map Prod.snd) b)*
              deriv (sourceRank (cutoff i) ((G m E:Measure (ℝ × ℝ)).map Prod.snd)) b*
                relativeError γ m) := by
  obtain ⟨γ,hγ,hder⟩ := eventually_source_used_pure_derivative i
  refine ⟨γ,hγ,?_⟩
  have ht := cutoff_pos i
  have ha : 0 < cutoff i/40000 := by positivity
  have he : 0 < activeError i := by unfold activeError; positivity
  filter_upwards [eventually_source_crossover_rank_density i,hder,
    hroot (cutoff i/40000) ha,hactive (cutoff i/40000) ha (activeError i) he]
    with m hd hderm hr hac
  intro E
  let μ : Measure (ℝ × ℝ) := G m E
  let Gb := μ.map Prod.snd
  letI : IsProbabilityMeasure Gb := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hA : ∀ᵐ p ∂μ,p.1 ∈ Icc (sortEnd i) (cutoff i) →
      |p.2-ActiveGraphComponent.activeBid i p.1| ≤ activeError i := by
    filter_upwards [hac E] with p hp hv
    apply hp ⟨?_,hv.2⟩
    unfold sortEnd at hv
    linarith only [hv.1,ht]
  have hp := original_prefix_constructor i μ (hvalue m E) (g m E) (hfields m E)
    (hr E) (hpsi m E) hA
  obtain ⟨hH,_,hHZ,hZK,hZcap,hK,hKfloor,hgap,_,_⟩ := band_geometry i
  have hfull := hd μ inferInstance (hvalue m E) (hmenu m E) (hatom m E)
    (g m E) (crossoverEnd i) (SourcePrefixConstructor.extensionEnd i) (sortEnd i)
    (activeError i) (cm m E) hH hHZ hZK hZcap hK hKfloor hp.1 hp.2 hgap hA (hIC m E)
  have hcap : ∀ᵐ b ∂Gb,b ≤ ReceiptGap.cap i :=
    (source_bid_support i μ (hmenu m E)).mono fun _ hb => hb.2
  have hceilA : ∀ᵐ p ∂μ,p.1 ∈ Ioc (EarlyRankCeiling.ceilingValue i) (cutoff i) →
      |p.2-ActiveGraphComponent.activeBid i p.1| ≤ cutoff i/10000 := by
    filter_upwards [hA] with p hp hv
    have hvK : sortEnd i ≤ p.1 := by
      have hv0 := hv.1
      unfold sortEnd EarlyRankCeiling.ceilingValue entry at *
      linarith only [hv0,ht]
    have hh := hp ⟨hvK,hv.2⟩
    unfold activeError at hh
    linarith
  have hceil := EarlyRankCeiling.source_early_rank_ceiling i μ (hvalue m E) hceilA
  have hHceil : crossoverEnd i ≤ EarlyRankCeiling.prefixEnd i := by
    unfold crossoverEnd EarlyRankCeiling.prefixEnd
    linarith
  have hM : ∀ b,b ≤ crossoverEnd i → sourceRank (cutoff i) Gb b ≤ RankCutoff.Mstar i :=
    fun b hb => (hceil b (hb.trans hHceil)).le
  refine ⟨hfull.1,hfull.2,?_⟩
  intro lo hlo hκlo hloH
  have hAC : (ENNReal.ofReal (cutoff i) • Gb).restrict (Ioc lo (crossoverEnd i)) ≪ volume := by
    intro A hA0
    have hz := hfull.1 hA0
    have hsub : (bidMeasure i μ).restrict (Ioc lo (crossoverEnd i)) ≤
        (bidMeasure i μ).restrict (Ioc (0:ℝ) (crossoverEnd i)) :=
      Measure.restrict_mono_set _ (fun _ hx => ⟨hlo.trans hx.1,hx.2⟩)
    exact le_antisymm ((hsub A).trans hz.le) bot_le
  exact ⟨source_pure_measure_AC i Gb hcap (hatom m E) (m-1) (capacity m)
    hlo hκlo hloH.le hAC,
    hderm Gb inferInstance hcap (hatom m E) lo (crossoverEnd i) hlo hκlo hloH hM hAC⟩

end Family
end FCAppendix.Affine.Uniform06.SourceRankFamily
