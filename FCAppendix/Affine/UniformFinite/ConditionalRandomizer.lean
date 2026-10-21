import FCAppendix.Affine.UniformFinite.SeedConditioning

noncomputable section
namespace FCAppendix.Affine.UniformFinite.Literal
open MeasureTheory ProbabilityTheory Set Filter Classical

theorem conditional_randomizer_replacement
    {X R : Type*} [MeasurableSpace X] [MeasurableSpace R]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure R) [IsProbabilityMeasure ν]
    (T : X→ unitInterval) (hT : Measurable T)
    (keep : X→ R) (hkeep : Measurable keep)
    (hjoint : μ.map (fun x=>(T x,keep x))=(volume : Measure unitInterval).prod ν)
    (F : X→ unitInterval→ℝ) (hF : Measurable (Function.uncurry F))
    (D : R→ unitInterval→ℝ) (hD : Measurable (Function.uncurry D))
    (C CD : ℝ) (hC : ∀x u,|F x u|≤ C) (hCD : ∀r u,|D r u|≤ CD)
    (hdiff : ∀ᵐx∂μ,∀u,F x u-F x 0=D (keep x) u) :
    (∫x,F x (T x) ∂μ)=∫u : unitInterval,∫x,F x u ∂μ := by
  have hkLaw : μ.map keep=ν := by
    have hh:=congrArg (fun ρ : Measure (unitInterval×R)=>ρ.map Prod.snd) hjoint
    rw [Measure.map_map measurable_snd (hT.prodMk hkeep),Measure.map_snd_prod,
      measure_univ,one_smul] at hh
    exact hh
  have hFT : Integrable (fun x=> F x (T x)) μ :=
    Integrable.of_bound (hF.comp (measurable_id.prodMk hT)).aestronglyMeasurable C
      (Eventually.of_forall (fun x=> hC x (T x)))
  have hF0 : Integrable (fun x=> F x 0) μ :=
    Integrable.of_bound (hF.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable C
      (Eventually.of_forall (fun x=> hC x 0))
  have hFu (u : unitInterval) : Integrable (fun x=> F x u) μ :=
    Integrable.of_bound (hF.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable C
      (Eventually.of_forall (fun x=> hC x u))
  have hFp : Integrable (fun p : unitInterval×X=> F p.2 p.1)
      ((volume : Measure unitInterval).prod μ) :=
    Integrable.of_bound (hF.comp measurable_swap).aestronglyMeasurable C
      (Eventually.of_forall (fun p=> hC p.2 p.1))
  have hDp : Integrable (fun p : unitInterval×R=> D p.2 p.1)
      ((volume : Measure unitInterval).prod ν) :=
    Integrable.of_bound (hD.comp measurable_swap).aestronglyMeasurable CD
      (Eventually.of_forall (fun p=> hCD p.2 p.1))
  have hDactual : (∫x,D (keep x) (T x) ∂μ)=∫u : unitInterval,∫r,D r u ∂ν := by
    calc
      _=∫p : unitInterval×R,D p.2 p.1 ∂μ.map (fun x=>(T x,keep x)) :=
        (integral_map (hT.prodMk hkeep).aemeasurable
          (hD.comp measurable_swap).aestronglyMeasurable).symm
      _=_ := by rw [hjoint,integral_prod _ hDp]
  have hDu (u : unitInterval) : (∫x,D (keep x) u ∂μ)=∫r,D r u ∂ν := by
    have hm : Measurable (fun r => D r u) :=
      hD.comp (measurable_id.prodMk measurable_const)
    have hh := integral_map (μ := μ) hkeep.aemeasurable hm.aestronglyMeasurable
    rw [hkLaw] at hh
    convert! hh.symm using 1
  have hleft : (∫x,F x (T x) ∂μ)-(∫x,F x 0 ∂μ)=∫u : unitInterval,∫r,D r u ∂ν := by
    rw [← integral_sub hFT hF0]
    calc
      _=∫x,D (keep x) (T x) ∂μ := integral_congr_ae (hdiff.mono (fun x hx=> hx (T x)))
      _=_ := hDactual
  have hright : (∫u : unitInterval,∫x,F x u ∂μ)-(∫x,F x 0 ∂μ)=
      ∫u : unitInterval,∫r,D r u ∂ν := by
    have hc : (∫u : unitInterval,(∫x,F x 0 ∂μ))=∫x,F x 0 ∂μ := by simp
    rw [← hc,← integral_sub hFp.integral_prod_left (integrable_const _)]
    apply integral_congr_ae
    apply ae_of_all
    intro u
    change (∫x,F x u ∂μ)-(∫x,F x 0 ∂μ)=∫r,D r u ∂ν
    have he : (∫x,F x u-F x 0 ∂μ)=∫x,D (keep x) u ∂μ :=
      integral_congr_ae (hdiff.mono (fun x hx=> hx u))
    rw [← integral_sub (hFu u) hF0,he,hDu u]
  linarith

end FCAppendix.Affine.UniformFinite.Literal
