import FCAppendix.Affine.Tail04.PartialPublicWeights

noncomputable section
namespace FCAppendix.Affine.Tail04.UnequalPartialOriginalIntegral
open MeasureTheory ProbabilityTheory Set Classical
open EqualPrivateSignal EqualPrivateUpper AtypicalPartialNoisy AllCountAtypical
open AllNoiseFiniteSelector

private lemma signal_integrable {H : ℕ} {R V Rm : ℝ}
    (θ : Measure (Row H R V Rm)) [IsProbabilityMeasure θ]
    (f : Signal H R V → ℝ) (hf : Continuous f) :
    Integrable (fun row => f (signal row)) θ := by
  let g := ContinuousMap.equivBoundedOfCompact _ _ (⟨f,hf⟩ : C(Signal H R V,ℝ))
  exact Integrable.of_bound (hf.measurable.comp continuous_signal.measurable).aestronglyMeasurable
    ‖g‖ (ae_of_all _ fun row => g.norm_coe_le_norm (signal row))

private lemma scalar_integral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (p I : Ω → ℝ) (hp : Integrable p μ)
    (hI : Integrable I μ) (hpI : Integrable (fun z => p z*I z) μ)
    (v w a : ℝ) :
    (∫ z,(v-p z)*(w*a+(1-w)*I z) ∂μ)=
      v*(w*a+(1-w)*(∫ z,I z ∂μ))-
        (w*a*(∫ z,p z ∂μ)+(1-w)*(∫ z,p z*I z ∂μ)) := by
  have he (z : Ω) : (v-p z)*(w*a+(1-w)*I z)=
      (v*w*a-w*a*p z)+(1-w)*(v*I z-p z*I z) := by ring
  simp_rw [he]
  erw [integral_add ((integrable_const _).sub (hp.const_mul _))
      ((hI.const_mul v).sub hpI |>.const_mul (1-w)),
    integral_sub (integrable_const _) (hp.const_mul _),integral_const,
    integral_const_mul,integral_const_mul,
    integral_sub (hI.const_mul v) hpI,integral_const_mul]
  simp only [probReal_univ,one_smul]
  ring

def branchValue (N H0 H1 c : ℕ) {ξ R U eps Rm : ℝ}
    (side reg : Bool) (b : Fin N → ℝ)
    (hR : 0< R) (heps : 0≤ eps) (j : Fin (ownCount H0 H1 side))
    (price : Icc R U) (v w : ℝ)
    (row : Row (ownCount H0 H1 side) R (U*(1+eps)) Rm) (u : unitInterval) : ℝ :=
  (v-Hybrid.activeNoisyRealBid eps price u)*
    (w*(if reg then 0 else 1)+(1-w)*
      (if Sum.inr j∈AllCountAtypical.select N H0 H1 c ξ b side
        (noisyRow hR heps j price row u) then 1 else 0))

theorem branchValue_integral (N H0 H1 c : ℕ) {ξ B R U eps Rm : ℝ}
    (side reg : Bool) (b : Fin N → ℝ)
    (row : Row (ownCount H0 H1 side) R (U*(1+eps)) Rm)
    (hξ : ξ∈Icc (0:ℝ) 1) (hb : ∀ i,b i∈Icc (1:ℝ) B)
    (hR : 0< R) (heps : 0< eps) (hRRm : R≤ Rm) (hV : U*(1+eps)<1)
    (hgap : (1-ξ)*B< R) (hfloor : U*(1+eps)< Rm)
    (j : Fin (ownCount H0 H1 side)) (price : Icc R U) (v w : ℝ) :
    (∫ u : unitInterval,branchValue N H0 H1 c (ξ:=ξ) side reg b hR heps.le j price v w row u)=
      v*(w*(if reg then 0 else 1)+(1-w)*smoothedInclusion N H0 H1 c side j (price,signal row))-
        (w*(if reg then 0 else ∫ u : unitInterval,Hybrid.activeNoisyRealBid eps price u)+
          (1-w)*smoothedPayment N H0 H1 c side j (price,signal row)) := by
  let p : unitInterval → ℝ := fun u => Hybrid.activeNoisyRealBid eps price u
  let I : unitInterval → ℝ := fun u => rankInclusion N H0 H1 c side j (inputAt (price,signal row) u)
  have hp : Continuous p := by unfold p Hybrid.activeNoisyRealBid;fun_prop
  have hIp : Measurable I := (measurable_rankInclusion N H0 H1 c side j).comp
    ((continuous_inputAt.comp (continuous_const.prodMk continuous_id)).measurable)
  have hi : Integrable I (volume : Measure unitInterval) :=
    Integrable.of_bound hIp.aestronglyMeasurable 1 (ae_of_all _ fun u => by
      rw [Real.norm_eq_abs,abs_of_nonneg (rankInclusion_bounds N H0 H1 c side j _).1]
      exact (rankInclusion_bounds N H0 H1 c side j _).2)
  have hpi : Integrable (fun u => p u*I u) (volume : Measure unitInterval) := by
    apply Integrable.of_bound (hp.measurable.mul hIp).aestronglyMeasurable |U*(1+eps)|
    exact ae_of_all _ fun u => by
      have hpb := Hybrid.activeNoisyRealBid_mem hR heps.le price u
      have hpn : 0≤ p u := hR.le.trans hpb.1
      change ‖p u*I u‖≤|U*(1+eps)|
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hpn
        (rankInclusion_bounds N H0 H1 c side j _).1)]
      exact (mul_le_of_le_one_right hpn (rankInclusion_bounds N H0 H1 c side j _).2).trans
        (hpb.2.trans (le_abs_self _))
  have hp' : Integrable p (volume : Measure unitInterval) :=
    (ContinuousMap.equivBoundedOfCompact _ _ (⟨p,hp⟩ : C(unitInterval,ℝ))).integrable _
  calc
    _ = ∫ u : unitInterval,(v-p u)*(w*(if reg then 0 else 1)+(1-w)*I u) := by
      apply integral_congr_ae
      filter_upwards [ae_actual_inclusion_eq_rank N H0 H1 c side b row hξ hb hR heps
        hRRm hV hgap hfloor j price] with u hu
      simp only [branchValue,hu,p,I]
    _ = _ := by
      rw [scalar_integral volume p I hp' hi hpi v w (if reg then 0 else 1)]
      cases reg <;> simp only [Bool.false_eq_true,if_false,if_true,mul_one,mul_zero,
        smoothedInclusion,smoothedPayment,inputAt,p,I,zero_mul]

theorem original_branch_integral (N H0 H1 c : ℕ) {ξ B R U eps Rm : ℝ}
    (side reg : Bool) (b : Fin N → ℝ)
    (θ : Measure (Row (ownCount H0 H1 side) R (U*(1+eps)) Rm)) [IsProbabilityMeasure θ]
    (hξ : ξ∈Icc (0:ℝ) 1) (hb : ∀ i,b i∈Icc (1:ℝ) B)
    (hR : 0< R) (heps : 0< eps) (hRRm : R≤ Rm) (hV : U*(1+eps)<1)
    (hgap : (1-ξ)*B< R) (hfloor : U*(1+eps)< Rm)
    (j : Fin (ownCount H0 H1 side)) (price : Icc R U) (v w : ℝ) :
    (∫ row,∫ u : unitInterval,branchValue N H0 H1 c (ξ:=ξ) side reg b hR heps.le j price v w row u
      ∂(volume : Measure unitInterval) ∂θ)=
      v*(w*(if reg then 0 else 1)+(1-w)*averagedInclusion N H0 H1 c side j
        (price,originalSignalLaw θ))-
        (w*(if reg then 0 else ∫ u : unitInterval,Hybrid.activeNoisyRealBid eps price u)+
          (1-w)*averagedPayment N H0 H1 c side j (price,originalSignalLaw θ)) := by
  have hI := signal_integrable θ
    (fun s => smoothedInclusion N H0 H1 c side j (price,s))
    ((continuous_smoothedInclusion N H0 H1 c hR heps.ne' side j).comp
      (continuous_const.prodMk continuous_id))
  have hP := signal_integrable θ
    (fun s => smoothedPayment N H0 H1 c side j (price,s))
    ((continuous_smoothedPayment N H0 H1 c hR heps side j).comp
      (continuous_const.prodMk continuous_id))
  have hImap : (∫ row,smoothedInclusion N H0 H1 c side j (price,signal row) ∂θ)=
      averagedInclusion N H0 H1 c side j (price,originalSignalLaw θ) := by
    unfold averagedInclusion originalSignalLaw
    exact (integral_map continuous_signal.measurable.aemeasurable
      (((continuous_smoothedInclusion N H0 H1 c hR heps.ne' side j).comp
        (continuous_const.prodMk continuous_id)).measurable.aestronglyMeasurable)).symm
  have hPmap : (∫ row,smoothedPayment N H0 H1 c side j (price,signal row) ∂θ)=
      averagedPayment N H0 H1 c side j (price,originalSignalLaw θ) := by
    unfold averagedPayment originalSignalLaw
    exact (integral_map continuous_signal.measurable.aemeasurable
      (((continuous_smoothedPayment N H0 H1 c hR heps side j).comp
        (continuous_const.prodMk continuous_id)).measurable.aestronglyMeasurable)).symm
  simp_rw [branchValue_integral N H0 H1 c side reg b _ hξ hb hR heps hRRm hV hgap hfloor j price v w]
  erw [integral_sub (((integrable_const _).add (hI.const_mul _)).const_mul v)
      ((integrable_const _).add (hP.const_mul _)),integral_const_mul,
    integral_add (integrable_const _) (hI.const_mul _),
    integral_add (integrable_const _) (hP.const_mul _),integral_const,
    integral_const]
  simp only [integral_const_mul,hImap,hPmap,probReal_univ,one_smul]

def originalUtility (N H0 H1 c : ℕ) {ξ B R U eps Rm : ℝ}
    (width e0 F : ℝ) (side reg lowPresent : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (hR : 0< R) (heps : 0≤ eps) (j : Fin (ownCount H0 H1 side))
    (price : Icc R U) (v : ℝ) (base : Fin N → ℝ)
    (θ : Measure (Row (ownCount H0 H1 side) R (U*(1+eps)) Rm)) : ℝ :=
  ∫ z : Fin N → unitInterval,∫ row,∫ u : unitInterval,
    branchValue N H0 H1 c (ξ:=ξ) side reg (noisyBids eps base z) hR heps j price v
      (UnequalPartialCountPayoff.rawWeight N H0 H1 c ξ B R (U*(1+eps)) width e0 F
        reg lowPresent ν0 ν1 (noisyBids eps base z)) row u ∂(volume : Measure unitInterval) ∂θ
    ∂Measure.pi (fun _ : Fin N => (volume : Measure unitInterval))

theorem utility_eq_original_integral (N H0 H1 c : ℕ) {ξ Uc R U eps Rm : ℝ}
    (width e0 F : ℝ) (side reg lowPresent : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (θ : Measure (Row (ownCount H0 H1 side) R (U*(1+eps)) Rm)) [IsProbabilityMeasure θ]
    (hξ : ξ∈Icc (0:ℝ) 1) (hR : 0< R) (heps : 0< eps)
    (hRRm : R≤ Rm) (hV : U*(1+eps)<1) (hgap : (1-ξ)*(Uc*(1+eps))< R)
    (hfloor : U*(1+eps)< Rm) (j : Fin (ownCount H0 H1 side))
    (price : Icc R U) (v : ℝ) (base : Fin N → Icc (1:ℝ) Uc) :
    UnequalPartialCountPayoff.utility N H0 H1 c ξ (Uc*(1+eps)) R U width e0 F eps
      side reg lowPresent ν0 ν1 j (v,(fun k => (base k:ℝ)),price,originalSignalLaw θ)=
    originalUtility N H0 H1 c (ξ:=ξ) (B:=Uc*(1+eps)) width e0 F side reg lowPresent ν0 ν1 hR heps.le j price v
      (fun k => (base k:ℝ)) θ := by
  let w : (Fin N → unitInterval) → ℝ := fun z =>
    UnequalPartialCountPayoff.rawWeight N H0 H1 c ξ (Uc*(1+eps)) R (U*(1+eps)) width e0 F
      reg lowPresent ν0 ν1 (noisyBids eps (fun k => (base k:ℝ)) z)
  have hw : Measurable w :=
    (UnequalPartialCountPayoff.measurable_rawWeight N H0 H1 c ξ (Uc*(1+eps)) R (U*(1+eps))
      width e0 F reg lowPresent ν0 ν1).comp
      ((continuous_noisyBids eps).comp (continuous_const.prodMk continuous_id)).measurable
  have hwi : Integrable w (Measure.pi (fun _ : Fin N => (volume : Measure unitInterval))) :=
    Integrable.of_bound hw.aestronglyMeasurable 1 (ae_of_all _ fun z => by
      have hh := UnequalPartialCountPayoff.rawWeight_bounds N H0 H1 c ξ (Uc*(1+eps)) R
        (U*(1+eps)) width e0 F reg lowPresent ν0 ν1 (noisyBids eps (fun k => (base k:ℝ)) z)
      rw [Real.norm_eq_abs,abs_of_nonneg hh.1]
      exact hh.2)
  have hb (z : Fin N → unitInterval) (k : Fin N) :
      noisyBids eps (fun k => (base k:ℝ)) z k∈Icc (1:ℝ) (Uc*(1+eps)) :=
    Hybrid.activeNoisyRealBid_mem (by norm_num) heps.le (base k) (z k)
  unfold originalUtility
  simp_rw [original_branch_integral N H0 H1 c side reg _ θ hξ (hb _) hR heps
    hRRm hV hgap hfloor j price v]
  change _=∫ z,v*(w z*(if reg then 0 else 1)+(1-w z)*
      averagedInclusion N H0 H1 c side j (price,originalSignalLaw θ))-
    (w z*(if reg then 0 else ∫ u : unitInterval,Hybrid.activeNoisyRealBid eps price u)+
      (1-w z)*averagedPayment N H0 H1 c side j (price,originalSignalLaw θ))
      ∂Measure.pi (fun _ : Fin N => (volume : Measure unitInterval))
  erw [integral_sub ((hwi.mul_const _).add
      (((integrable_const (1:ℝ)).sub hwi).mul_const _)|>.const_mul v)
      ((hwi.mul_const _).add (((integrable_const (1:ℝ)).sub hwi).mul_const _)),
    integral_const_mul,integral_add (hwi.mul_const _) (((integrable_const (1:ℝ)).sub hwi).mul_const _),
    integral_add (hwi.mul_const _) (((integrable_const (1:ℝ)).sub hwi).mul_const _),
    integral_mul_const,integral_mul_const,integral_mul_const,integral_mul_const,
    integral_sub (integrable_const (1:ℝ)) hwi,integral_const]
  simp only [probReal_univ,one_smul]
  rfl

end FCAppendix.Affine.Tail04.UnequalPartialOriginalIntegral
