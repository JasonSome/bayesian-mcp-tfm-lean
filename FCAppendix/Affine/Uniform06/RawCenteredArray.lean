import FCAppendix.Affine.Uniform06.RawTiltedSource
import FCAppendix.Affine.Uniform06.PhysicalExposureLimit

noncomputable section
namespace FCAppendix.Affine.Uniform06.RawCenteredArray

open MeasureTheory Filter Set
open scoped Topology
open MixedIntervalLLT CharacteristicExpansion MixedSpectralLimit BoundedMixedGaussian
open RawTiltedSource RawMixedSource

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]

private theorem preserving_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure Ω} {ν : Measure Ξ} {f : Ω → Ξ} (hf : MeasurePreserving f μ ν)
    {g : Ξ → E} (hg : AEStronglyMeasurable g ν) :
    (∫ x, g (f x) ∂μ)=∫ y, g y ∂ν := by
  have hgmap : AEStronglyMeasurable g (μ.map f) := by rw [hf.map_eq]; exact hg
  simpa only [hf.map_eq,Function.comp_def] using
    (integral_map hf.measurable.aemeasurable hgmap).symm

def pullback (A : CenteredArray Ξ) (μ : ℕ → Measure Ω)
    (hμ : ∀ n,IsProbabilityMeasure (μ n)) (f : ℕ → Ω → Ξ)
    (hf : ∀ n,MeasurePreserving (f n) (μ n) (A.law n)) : CenteredArray Ω where
  law := μ
  probability := hμ
  X := fun n ω => A.X n (f n ω)
  Y := fun n ω => A.Y n (f n ω)
  N := A.N
  d := A.d
  measurable_X := fun n => (A.measurable_X n).comp (hf n).measurable
  measurable_Y := fun n => (A.measurable_Y n).comp (hf n).measurable
  bounded := fun n => (hf n).quasiMeasurePreserving.ae (A.bounded n)
  mean_X := by
    intro n
    rw [preserving_integral (hf n) (A.measurable_X n).aestronglyMeasurable,A.mean_X]
  mean_Y := by
    intro n
    change (∫ ω, A.realY n (f n ω) ∂μ n)=0
    rw [preserving_integral (hf n) (A.measurable_realY n).aestronglyMeasurable]
    exact A.mean_Y n
  covariance := by
    intro n
    change (∫ ω, (A.X n*A.realY n) (f n ω) ∂μ n)=0
    rw [preserving_integral (hf n)
      ((A.measurable_X n).mul (A.measurable_realY n)).aestronglyMeasurable]
    exact A.covariance n
  d_nonneg := A.d_nonneg
  d_zero := A.d_zero
  scale := A.scale
  market := A.market
  vX := A.vX
  vY := A.vY
  lowerVariance := A.lowerVariance
  lowerVariance_pos := A.lowerVariance_pos
  variance_X_lower := by
    intro n
    rw [preserving_integral (hf n) ((A.measurable_X n).pow_const 2).aestronglyMeasurable]
    exact A.variance_X_lower n
  variance_Y_lower := by
    intro n
    change A.lowerVariance ≤ ∫ ω, A.realY n (f n ω)^2 ∂μ n
    rw [preserving_integral (hf n) ((A.measurable_realY n).pow_const 2).aestronglyMeasurable]
    exact A.variance_Y_lower n
  variance_X_limit := by
    have he : (fun n => ∫ ω,A.X n (f n ω)^2 ∂μ n)=fun n => ∫ x,A.X n x^2 ∂A.law n := by
      funext n
      exact preserving_integral (hf n) ((A.measurable_X n).pow_const 2).aestronglyMeasurable
    rw [he]
    exact A.variance_X_limit
  variance_Y_limit := by
    have he : (fun n => ∫ ω,(A.Y n (f n ω):ℝ)^2 ∂μ n)=
        fun n => ∫ x,(A.Y n x:ℝ)^2 ∂A.law n := by
      funext n
      exact preserving_integral (hf n) ((A.measurable_realY n).pow_const 2).aestronglyMeasurable
    rw [he]
    exact A.variance_Y_limit

theorem pullback_gap (A : CenteredArray Ξ) (hgap : A.CompactGap)
    (μ : ℕ → Measure Ω) (hμ : ∀ n,IsProbabilityMeasure (μ n)) (f : ℕ → Ω → Ξ)
    (hf : ∀ n,MeasurePreserving (f n) (μ n) (A.law n)) :
    (pullback A μ hμ f hf).CompactGap := by
  intro T hT
  obtain ⟨r,hr0,hr1,he⟩ := hgap T hT
  refine ⟨r,hr0,hr1,?_⟩
  filter_upwards [he] with n hn
  intro q hq
  have htest : Measurable (fun x => phase (projection (A.X n) (A.realY n) q x)) := by
    exact continuous_phase.measurable.comp
      (((A.measurable_X n).const_mul q.1).add ((A.measurable_realY n).const_mul q.2))
  have hh := preserving_integral (hf n) htest.aestronglyMeasurable
  change rowCharacteristic (μ n)
    (projection ((pullback A μ hμ f hf).X n) ((pullback A μ hμ f hf).realY n) q)=
      rowCharacteristic (A.law n) (projection (A.X n) (A.realY n) q) at hh
  change ‖rowCharacteristic (μ n)
    (projection ((pullback A μ hμ f hf).X n) ((pullback A μ hμ f hf).realY n) q)‖ ≤ r
  rw [hh]
  exact hn q hq

theorem exists_raw_array_from_early_joint_limit (i : Uniform07.Row)
    (G : ℕ → ProbabilityMeasure (ℝ × ℝ)) (G0 : ProbabilityMeasure (ℝ × ℝ))
    (hG : Tendsto G atTop (𝓝 G0))
    (hvalue : (G0:Measure (ℝ × ℝ)).map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hbelow : ∀ᵐ p ∂(G0:Measure (ℝ × ℝ)), p.2 ≤ p.1)
    (hactive : ∀ᵐ p ∂(G0:Measure (ℝ × ℝ)),
      p.1 ∈ Ioc (Uniform07.entry i) (Uniform07.cutoff i) →
        p.2=ActiveGraphComponent.activeBid i p.1)
    (b θ : ℕ → ℝ) (hb : ∀ n,0 < b n)
    {z : ℝ} (hz : z ∈ Ico (1/2:ℝ) (Uniform07.x i))
    (hblim : Tendsto b atTop (𝓝 (z*Uniform07.cutoff i)))
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (hmatch : ∀ᶠ n in atTop,
      SubentryTilt.mean (MixedLaw.law i (MixedLaw.physicalLowerLaw i (b n)
        (G n:Measure (ℝ × ℝ)))) Prod.fst (θ n)=
          (Uniform07.capacity (m n):ℝ)/((m n-1:ℕ):ℝ)) :
    ∃ θ0 > (0:ℝ), Tendsto θ atTop (𝓝 θ0) ∧
      ∃ n0 : ℕ, ∃ A : CenteredArray LowBody.RowRival,
        A.N=(fun n => m (n+n0)-1) ∧
        A.law=(fun n => tiltedSource i (G (n+n0):Measure (ℝ × ℝ)) (b (n+n0)) (θ (n+n0))) ∧
        A.X=(fun n r => demand (Uniform07.xi i) (b (n+n0)) r-
          LiteralCenteredArray.mean i
            (PhysicalExposureLimit.lowerProbability i (G (n+n0)) (b (n+n0)) (hb _))
              (-θ (n+n0))) ∧
        A.Y=(fun _ => RawTiltedSource.integerSign) ∧ A.CompactGap := by
  obtain ⟨θ0,hθ0,hθ,n0,A,hAN,hAlaw,hAX,hAY,hgap⟩ :=
    PhysicalExposureLimit.source_array_from_early_joint_limit i G G0 hG hvalue hbelow hactive
      b θ hb hz hblim m hm hmatch
  let μ := fun n => tiltedSource i (G (n+n0):Measure (ℝ × ℝ)) (b (n+n0)) (θ (n+n0))
  have hμ (n : ℕ) : IsProbabilityMeasure (μ n) :=
    tiltedSource_probability i (G (n+n0):Measure (ℝ × ℝ)) (hb _) _
  let f := fun n => point (Uniform07.xi i) (b (n+n0))
  have hf (n : ℕ) : MeasurePreserving (f n) (μ n) (A.law n) := by
    rw [hAlaw]
    exact tilted_point_preserving i (G (n+n0):Measure (ℝ × ℝ)) (hb _) _
  let R := pullback A μ hμ f hf
  refine ⟨θ0,hθ0,hθ,n0,R,hAN,rfl,?_,?_,pullback_gap A hgap μ hμ f hf⟩
  · funext n r
    change A.X n (f n r)=_
    rw [hAX]
    rfl
  · funext n r
    change A.Y n (f n r)=_
    rw [hAY]
    exact integerSign_point _ _ _

end FCAppendix.Affine.Uniform06.RawCenteredArray
