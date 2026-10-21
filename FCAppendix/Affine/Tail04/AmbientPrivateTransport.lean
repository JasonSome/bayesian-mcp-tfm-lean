import FCAppendix.Affine.Tail04.PrivateScalarIntegral

noncomputable section
namespace FCAppendix.Affine.Tail04.AmbientPrivateTransport
open MeasureTheory ProbabilityTheory Set Classical
open Existence.Distributional EqualPrivateSignal CompactSourceBidLaws FixedAmbientNoise
open SourceAmbientLaws EqualPrivateAmbient FiniteTailNoisyGame SourceTailNoisyFixedPoint
open BoundedProbabilityIntegral (measurable_integral)

private lemma measurable_private_integral {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] (ν : Measure Y) [SFinite ν]
    (f : X×(Y×unitInterval)→ℝ) (hf : Measurable f) :
    Measurable (fun x=>∫y,∫u : unitInterval,f (x,y,u) ∂volume ∂ν) := by
  have h : Measurable (fun z : (X×Y)×unitInterval=>f (z.1.1,z.1.2,z.2)) :=
    hf.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  exact measurable_integral ν _ (measurable_integral volume _ h)

variable (D : Data) (A H : ℕ) (μP : ProbabilityMeasure (Icc D.R D.Up))
  (μA : ProbabilityMeasure (Icc (1:ℝ) D.U))

theorem positive (e : Noise D.eps) (he : 0<(e:ℝ)) (hes : (e:ℝ)< D.eps)
    (f : (Fin A→ Icc (1:ℝ) D.B)×(Signal H D.R D.V×unitInterval)→ℝ)
    (hf : Measurable f) {C : ℝ} (hC : ∀z,|f z|≤ C) :
    (∫b,∫s,∫u : unitInterval,f (b,s,u) ∂(volume : Measure unitInterval)
      ∂(privateRaw D H e μP : Measure _)
      ∂(rowLaw A (SourceAmbientLaws.common D e μA) : Measure _))=
    ∫base,∫z : Fin A→ unitInterval,∫s,∫u : unitInterval,
      f ((fun i=> widen (upper_mono (by norm_num) D.hU e)
        (OriginalNoiseProduct.physicalRow (by norm_num) he.le A (base,z) i)),
        signal (upper_mono D.hR D.hRUp e) s,u)
      ∂(volume : Measure unitInterval) ∂(ProbabilityMeasure.toMeasure ((atNoise D e he hes).privateFocalRow H μP))
      ∂Measure.pi (fun _ : Fin A=>(volume : Measure unitInterval))
      ∂(ProbabilityMeasure.toMeasure (rowLaw A μA)) := by
  let embed : (Fin A→ Icc (1:ℝ) (D.U*(1+(e:ℝ))))×
      (Signal H D.R (D.Up*(1+(e:ℝ)))×unitInterval)→
      (Fin A→ Icc (1:ℝ) D.B)×(Signal H D.R D.V×unitInterval) :=
    fun z=>((fun i=> widen (upper_mono (by norm_num) D.hU e) (z.1 i)),
      signal (upper_mono D.hR D.hRUp e) z.2.1,z.2.2)
  have hemb : Measurable embed :=
    (measurable_pi_lambda _ fun i=>(continuous_widen
      (upper_mono (by norm_num) D.hU e)).measurable.comp
        ((measurable_pi_apply i).comp measurable_fst)).prodMk
      (((continuous_signal (upper_mono D.hR D.hRUp e)).measurable.comp
        measurable_snd.fst).prodMk measurable_snd.snd)
  let θ : ProbabilityMeasure (Signal H D.R (D.Up*(1+(e:ℝ)))) :=
    (atNoise D e he hes).privateFocalRow H μP
  let g:=fun b=>∫s,∫u : unitInterval,f (embed (b,s,u)) ∂(volume : Measure unitInterval)
    ∂(ProbabilityMeasure.toMeasure θ)
  have hg : Measurable g := measurable_private_integral _ _ (hf.comp hemb)
  have hb (b) : |g b|≤ C := BoundedProbabilityIntegral.bound _ _ (fun s=>
    BoundedProbabilityIntegral.bound _ _ (fun u=> hC _))
  calc
    _=∫b,g b ∂(rowLaw A (noisyBidLaw (by norm_num) he.le μA) : Measure _) := by
      rw [SourceAmbientLaws.common_positive D e he hes μA]
      erw [SourceNoiseIntegration.widen_row A _ _ _
        (measurable_private_integral _ f hf)]
      apply integral_congr_ae
      refine ae_of_all _ fun b=>?_
      erw [raw_positive D H e he hes μP]
      dsimp only [g,embed]
      exact integral_map (continuous_signal _).measurable.aemeasurable
        (measurable_integral volume _
          (hf.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable
    _=_ := SourceNoiseIntegration.common A (by norm_num) he.le μA g hg hb

theorem zero (f : (Fin A→ Icc (1:ℝ) D.B)×(Signal H D.R D.V×unitInterval)→ℝ)
    (hf : Measurable f) :
    (∫b,∫s,∫u : unitInterval,f (b,s,u) ∂(volume : Measure unitInterval)
      ∂(privateRaw D H (FixedAmbientNoise.zero D.eps D.heps.le) μP : Measure _)
      ∂(rowLaw A (SourceAmbientLaws.common D (FixedAmbientNoise.zero D.eps D.heps.le) μA) : Measure _))=
    ∫b,∫s,∫u : unitInterval,
      f ((fun i=> widen (base_le_upper (by norm_num) D.hU D.heps.le) (b i)),
        signal (base_le_upper D.hR D.hRUp D.heps.le) s,u)
      ∂(volume : Measure unitInterval) ∂(ZeroNoiseFiniteGame.privateRow D H μP : Measure _)
      ∂(ProbabilityMeasure.toMeasure (rowLaw A μA)) := by
  rw [SourceAmbientLaws.common_zero D μA]
  erw [SourceNoiseIntegration.widen_row A _ _ _
    (measurable_private_integral _ f hf)]
  apply integral_congr_ae
  refine ae_of_all _ fun b=>?_
  erw [raw_zero D H μP]
  exact integral_map (continuous_signal _).measurable.aemeasurable
    (measurable_integral volume _
      (hf.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable

end FCAppendix.Affine.Tail04.AmbientPrivateTransport
