import FCAppendix.Affine.LowBody.NoisySupportedLimit

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set Classical
open Existence.Distributional

theorem ae_injective_ne {X Y : Type*} [MeasurableSpace X]
    (mu : Measure X) [NullSingletonClass mu] (f : X→Y) (hf : Function.Injective f) (t : Y) :
    ∀ᵐx ∂mu,f x≠t := by
  by_cases he : ∃x,f x=t
  · obtain ⟨x,hx⟩:=he
    filter_upwards [mu.ae_ne x] with y hy heq
    exact hy (hf (heq.trans hx.symm))
  · exact ae_of_all _ (fun x hx=>he ⟨x,hx⟩)

theorem noisyBid_injective_noise {d ε : ℝ} (hε : 0<ε) (hsmall : ε≤1/2)
    (w : LowValue d) (q : unitInterval) (hw : 0<w.1) :
    Function.Injective (fun z : unitInterval=>noisyBid d ε hε hsmall ((w,q),z)) := by
  intro z z' he
  have hh:=congrArg Subtype.val he
  change w.1*bidRatio ε q*(1+ε*z.1)=w.1*bidRatio ε q*(1+ε*z'.1) at hh
  have hr:=hε.trans_le (bidRatio_bounds hε hsmall q).1
  have hcoeff : 0<w.1*bidRatio ε q*ε:=mul_pos (mul_pos hw hr) hε
  apply Subtype.ext
  nlinarith

theorem implementedBidLaw_singleton {d ε : ℝ} (hε : 0<ε) (hsmall : ε≤1/2)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A:=unitInterval) mu) (hmu : ∀ᵐw ∂mu,0<w.1) (b : LowValue d) :
    (implementedBidLaw d ε hε hsmall mu pi : Measure (LowValue d)) {b}=0 := by
  have hpos : ∀ᵐx ∂(pi.1 : Measure (LowValue d×unitInterval)),0<x.1.1 := by
    have hp : MeasurableSet {w : LowValue d | 0<w.1}:=
      measurableSet_lt measurable_const measurable_subtype_coe
    have hm : (pi.1 : Measure (LowValue d×unitInterval)).map Prod.fst=mu:=pi.property
    apply (ae_map_iff measurable_fst.aemeasurable hp).mp
    rwa [hm]
  let psi : (LowValue d×unitInterval)×unitInterval→LowValue d×LowValue d :=
    fun x=>(x.1.1,noisyBid d ε hε hsmall x)
  have hm : Measurable psi:=(measurable_fst.comp measurable_fst).prodMk
    (continuous_noisyBid d ε hε hsmall).measurable
  have hS : MeasurableSet {x : LowValue d×LowValue d | x.2≠b}:=
    (measurableSet_eq_fun measurable_snd measurable_const).compl
  have hraw : ∀ᵐx ∂((pi.1 : Measure (LowValue d×unitInterval)).prod
      (volume : Measure unitInterval)),noisyBid d ε hε hsmall x≠b := by
    apply (Measure.ae_prod_iff_ae_ae (hS.preimage hm)).mpr
    filter_upwards [hpos] with x hx
    exact ae_injective_ne volume _ (noisyBid_injective_noise hε hsmall x.1 x.2 hx) b
  have hactual : ∀ᵐx ∂((lowNoisyLaw d ε hε hsmall mu pi).1 : Measure (LowValue d×LowValue d)),x.2≠b := by
    change ∀ᵐx ∂(((pi.1 : Measure (LowValue d×unitInterval)).prod
      (volume : Measure unitInterval)).map psi),x.2≠b
    exact (ae_map_iff hm.aemeasurable hS).mpr hraw
  change (((lowNoisyLaw d ε hε hsmall mu pi).1 : Measure (LowValue d×LowValue d)).map Prod.snd) {b}=0
  rw [Measure.map_apply measurable_snd (measurableSet_singleton b)]
  exact measure_eq_zero_iff_ae_notMem.mpr hactual

end FCAppendix.Affine.LowBody
