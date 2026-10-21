import FCAppendix.Affine.Tail04.EqualNoisyUtilities
import FCAppendix.Affine.Tail04.PrivatePartialSorting

noncomputable section
namespace FCAppendix.Affine.Tail04.EqualPartialOriginalIntegral
open MeasureTheory ProbabilityTheory Set Classical
open EqualPrivateSignal EqualPrivateUpper PrivatePayoffContinuity
open AtypicalPartialNoisy (originalSignalLaw)

variable {N H c : ℕ} {ξ B R U eps Rm : ℝ}

def samplerValue (hξ : ξ∈Icc (0:ℝ) 1) (hR : 0< R) (heps : 0≤ eps)
    (hVB : U*(1+eps)≤ B) (hBRm : B< Rm) (hRm : 0< Rm)
    (p : PolicyParameters N H R (U*(1+eps)) 1 B)
    (row : Row H R (U*(1+eps)) Rm) (j : Fin H) (price : Icc R U)
    (σ : unitInterval→ Equiv.Perm (Fin H)) (v : ℝ) (z u : unitInterval) : ℝ :=
  (v-Hybrid.activeNoisyRealBid eps price z)*
    (if Sum.inr ((σ z).symm j)∈AllCountHighPolicy.equalBase N H c ξ B R (U*(1+eps)) Rm
      hξ hR.le hVB hBRm hRm
      (p,PrivatePartialSorting.reindexRow (σ z)
        (AtypicalPartialNoisy.noisyRow hR heps j price row z)) u then 1 else 0)

theorem sampler_ownNoise_integral
    (hξ : ξ∈Icc (0:ℝ) 1) (hR : 0< R) (heps : 0< eps)
    (hVB : U*(1+eps)≤ B) (hBRm : B< Rm) (hRm : 0< Rm)
    (p : PolicyParameters N H R (U*(1+eps)) 1 B)
    (row : Row H R (U*(1+eps)) Rm) (j : Fin H) (price : Icc R U)
    (σ : unitInterval→ Equiv.Perm (Fin H)) (v : ℝ) :
    (∫ z : unitInterval,∫ u : unitInterval,
      samplerValue (c:=c) hξ hR heps.le hVB hBRm hRm p row j price σ v z u)=
      v*smoothedInclusion (c:=c) hR heps.le ξ j
        (focalPolicyInput (c:=c) (ξ:=ξ) p price (signal row))-
      smoothedPayment (c:=c) hR heps.le ξ j
        (focalPolicyInput (c:=c) (ξ:=ξ) p price (signal row)) := by
  let q := focalPolicyInput (c:=c) (ξ:=ξ) p price (signal row)
  let f := fun z : unitInterval => privateValue (c:=c) ξ j (noisyInput hR heps.le j q z)
  let pay := fun z : unitInterval => Hybrid.activeNoisyRealBid eps price z*f z
  have hf : Measurable f := (measurable_privateValue ξ j).comp
    ((continuous_noisyInput hR heps.le j).comp
      (continuous_const.prodMk continuous_id)).measurable
  have hi : Integrable f (volume : Measure unitInterval) :=
    Integrable.of_bound hf.aestronglyMeasurable 1 (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (privateValue_bounds (c:=c) ξ j _).1]
      exact (privateValue_bounds (c:=c) ξ j _).2)
  have hp : Integrable pay (volume : Measure unitInterval) := by
    apply Integrable.of_bound
      (((by unfold Hybrid.activeNoisyRealBid;fun_prop :
        Measurable (fun z : unitInterval => Hybrid.activeNoisyRealBid eps price z)).mul hf).aestronglyMeasurable) |U*(1+eps)|
    exact ae_of_all _ fun z => by
      have hprice := Hybrid.activeNoisyRealBid_mem hR heps.le price z
      have hval := privateValue_bounds (c:=c) ξ j (noisyInput hR heps.le j q z)
      change ‖Hybrid.activeNoisyRealBid eps price z*f z‖≤_
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hR.le.trans hprice.1) hval.1)]
      exact (mul_le_of_le_one_right (hR.le.trans hprice.1) hval.2).trans
        (hprice.2.trans (le_abs_self _))
  calc
    _=∫ z : unitInterval,v*f z-pay z := by
      apply integral_congr_ae
      filter_upwards [PrivatePartialSorting.ae_equalBase_reindexed_privateValue N H c
        hξ hR heps hVB hBRm hRm p row j price σ] with z hz
      simp only [samplerValue,hz,integral_const,MeasureTheory.probReal_univ,one_smul]
      dsimp only [f,pay,q]
      ring
    _=_ := by
      rw [integral_sub (hi.const_mul v) hp,integral_const_mul]
      rfl

private theorem signal_integrable (θ : Measure (Row H R (U*(1+eps)) Rm))
    [IsProbabilityMeasure θ] (f : Signal H R (U*(1+eps))→ℝ) (hf : Continuous f) :
    Integrable (fun row => f (signal row)) θ := by
  let g := ContinuousMap.equivBoundedOfCompact _ _
    (⟨f,hf⟩ : C(Signal H R (U*(1+eps)),ℝ))
  exact Integrable.of_bound (hf.measurable.comp continuous_signal.measurable).aestronglyMeasurable
    ‖g‖ (ae_of_all _ fun row => g.norm_coe_le_norm (signal row))

theorem sampler_original_integral
    (hξ : ξ∈Icc (0:ℝ) 1) (hR : 0< R) (heps : 0< eps)
    (hVB : U*(1+eps)≤ B) (hBRm : B< Rm) (hRm : 0< Rm)
    (p : PolicyParameters N H R (U*(1+eps)) 1 B)
    (θ : Measure (Row H R (U*(1+eps)) Rm)) [IsProbabilityMeasure θ]
    (j : Fin H) (price : Icc R U)
    (σ : Row H R (U*(1+eps)) Rm→ unitInterval→ Equiv.Perm (Fin H)) (v : ℝ) :
    (∫ row,∫ z : unitInterval,∫ u : unitInterval,
      samplerValue (c:=c) hξ hR heps.le hVB hBRm hRm p row j price (σ row) v z u
        ∂(volume : Measure unitInterval) ∂(volume : Measure unitInterval) ∂θ)=
      v*averagedInclusion (c:=c) hR heps.le ξ j
        (averagingInput (c:=c) (ξ:=ξ) (p,price,originalSignalLaw θ))-
      averagedPayment (c:=c) hR heps.le ξ j
        (averagingInput (c:=c) (ξ:=ξ) (p,price,originalSignalLaw θ)) := by
  let q : Signal H R (U*(1+eps))→ FocalInput N H R U eps :=
    focalPolicyInput (c:=c) (ξ:=ξ) p price
  have hq : Continuous q := by
    unfold q focalPolicyInput
    exact continuous_const.prodMk (continuous_const.prodMk (continuous_const.prodMk continuous_id))
  have hI := (continuous_smoothedInclusion (c:=c) hR heps ξ j).comp hq
  have hP := (continuous_smoothedPayment (c:=c) hR heps ξ j).comp hq
  have hi := signal_integrable θ _ hI
  have hp := signal_integrable θ _ hP
  simp_rw [sampler_ownNoise_integral (c:=c) hξ hR heps hVB hBRm hRm]
  change (∫ row, v*((smoothedInclusion (c:=c) hR heps.le ξ j) ∘ q) (signal row)-
    ((smoothedPayment (c:=c) hR heps.le ξ j) ∘ q) (signal row) ∂θ)=_
  rw [integral_sub (hi.const_mul v) hp,integral_const_mul]
  have hmI := integral_map (μ:=θ) continuous_signal.measurable.aemeasurable
    hI.measurable.aestronglyMeasurable
  have hmP := integral_map (μ:=θ) continuous_signal.measurable.aemeasurable
    hP.measurable.aestronglyMeasurable
  change _=v*(∫ s, ((smoothedInclusion (c:=c) hR heps.le ξ j) ∘ q) s ∂θ.map signal)-
    ∫ s, ((smoothedPayment (c:=c) hR heps.le ξ j) ∘ q) s ∂θ.map signal
  rw [hmI,hmP]

theorem utility_eq_original_integral {Uc : ℝ}
    (hξ : ξ∈Icc (0:ℝ) 1) (hR : 0< R) (heps : 0< eps)
    (hVB : U*(1+eps)≤ Uc*(1+eps)) (hBRm : Uc*(1+eps)< Rm) (hRm : 0< Rm)
    (base : Fin N→ Icc (1:ℝ) Uc)
    (bayes : ProbabilityMeasure (Signal H R (U*(1+eps))))
    (θ : Measure (Row H R (U*(1+eps)) Rm)) [IsProbabilityMeasure θ]
    (j : Fin H) (price : Icc R U)
    (σ : (Fin N→ unitInterval)→ Row H R (U*(1+eps)) Rm→ unitInterval→ Equiv.Perm (Fin H))
    (v : ℝ) :
    EqualNoisyUtilities.privateUtility (c:=c) hR heps.le ξ j
      (v,((base,bayes),price,originalSignalLaw θ))=
      ∫ commonNoise : Fin N→ unitInterval,∫ row,∫ z : unitInterval,∫ u : unitInterval,
        samplerValue (c:=c) hξ hR heps.le hVB hBRm hRm
          (EqualNoisyUtilities.parameter heps.le (base,bayes) commonNoise)
          row j price (σ commonNoise row) v z u
            ∂(volume : Measure unitInterval) ∂(volume : Measure unitInterval) ∂θ
        ∂Measure.pi (fun _ : Fin N => (volume : Measure unitInterval)) := by
  unfold EqualNoisyUtilities.privateUtility
  apply integral_congr_ae
  exact ae_of_all _ fun commonNoise =>
    (sampler_original_integral (c:=c) hξ hR heps hVB hBRm hRm
      (EqualNoisyUtilities.parameter heps.le (base,bayes) commonNoise)
      θ j price (σ commonNoise) v).symm

end FCAppendix.Affine.Tail04.EqualPartialOriginalIntegral
