import FCAppendix.Affine.Tail04.SourceAmbientPayoff

noncomputable section
namespace FCAppendix.Affine.Tail04.PrivateScalarIntegral
open MeasureTheory ProbabilityTheory Set Classical
open EqualPrivateSignal PrivatePayoffContinuity Existence.Distributional
open scoped BigOperators

theorem equal_average {N H c : ℕ} {R U eps B ξ : ℝ}
    (hR : 0< R) (heps : 0≤ eps) (p : PolicyParameters N H R (U*(1+eps)) 1 B)
    (θ : ProbabilityMeasure (Signal H R (U*(1+eps)))) (j : Fin H) (price : Icc R U) (v : ℝ) :
    (∫s,∫u : unitInterval,(v-Hybrid.activeNoisyRealBid eps price u)*
      privateValue (c:=c) ξ j (noisyInput hR heps j
        (focalPolicyInput (c:=c) (ξ:=ξ) p price s) u)
      ∂(volume : Measure unitInterval) ∂(ProbabilityMeasure.toMeasure θ))=
    v*averagedInclusion (c:=c) hR heps ξ j (averagingInput (c:=c) (ξ:=ξ) (p,price,θ))-
      averagedPayment (c:=c) hR heps ξ j (averagingInput (c:=c) (ξ:=ξ) (p,price,θ)) := by
  let F : Signal H R (U*(1+eps))×unitInterval→ Input N H R (U*(1+eps)):=
    fun z=> noisyInput hR heps j (focalPolicyInput (c:=c) (ξ:=ξ) p price z.1) z.2
  have hF : Continuous F := (continuous_noisyInput hR heps j).comp
    ((continuous_const.prodMk (continuous_const.prodMk
      (continuous_const.prodMk continuous_fst))).prodMk continuous_snd)
  let I:=fun z=> privateValue (c:=c) ξ j (F z)
  let charge:=fun z : Signal H R (U*(1+eps))×unitInterval=> Hybrid.activeNoisyRealBid eps price z.2
  have hI : Measurable I := (measurable_privateValue ξ j).comp hF.measurable
  have hq (z) : I z∈Icc (0:ℝ) 1:=privateValue_bounds (c:=c) ξ j (F z)
  have hp : Measurable charge := by unfold charge Hybrid.activeNoisyRealBid;fun_prop
  have hb (z) : |charge z|≤|U*(1+eps)| := by
    have hh:=Hybrid.activeNoisyRealBid_mem hR heps price z.2
    rw [abs_of_nonneg (hR.le.trans hh.1)]
    exact hh.2.trans (le_abs_self _)
  have hsur:=BoundedProbabilityIntegral.surplus ((ProbabilityMeasure.toMeasure θ).prod volume)
    charge I hp hI hb hq v
  have hi:=BoundedProbabilityIntegral.integrable ((ProbabilityMeasure.toMeasure θ).prod volume) I hI
    (fun z=> by rw [abs_of_nonneg (hq z).1];exact (hq z).2)
  have hpi:=BoundedProbabilityIntegral.integrable ((ProbabilityMeasure.toMeasure θ).prod volume)
    (fun z=> charge z*I z) (hp.mul hI) (fun z=> by
      rw [abs_mul,abs_of_nonneg (hq z).1]
      exact (mul_le_of_le_one_right (abs_nonneg _) (hq z).2).trans (hb z))
  have hs : Integrable (fun z=>(v-charge z)*I z) ((ProbabilityMeasure.toMeasure θ).prod volume) := by
    convert! ((hi.const_mul v).sub hpi) using 1
    funext z
    change (v-charge z)*I z=v*I z-charge z*I z
    ring
  rw [integral_prod _ hs,integral_prod _ hi,integral_prod _ hpi] at hsur
  exact hsur

theorem unequal_average (N H0 H1 c : ℕ) {R U eps : ℝ} (hR : 0< R) (heps : 0≤ eps)
    (side reg : Bool) (θ : ProbabilityMeasure (Signal (AllCountAtypical.ownCount H0 H1 side) R (U*(1+eps))))
    (j : Fin (AllCountAtypical.ownCount H0 H1 side)) (price : Icc R U) (v w : ℝ) :
    (∫s,∫u : unitInterval,(v-Hybrid.activeNoisyRealBid eps price u)*
      (w*(if reg then 0 else 1)+(1-w)*AtypicalPartialNoisy.rankInclusion N H0 H1 c side j
        (Hybrid.activeNoisyRealBid eps price u,s))
      ∂(volume : Measure unitInterval) ∂(ProbabilityMeasure.toMeasure θ))=
    v*(w*(if reg then 0 else 1)+(1-w)*AtypicalPartialNoisy.averagedInclusion N H0 H1 c side j (price,θ))-
      (w*(if reg then 0 else ∫u : unitInterval,Hybrid.activeNoisyRealBid eps price u)+
        (1-w)*AtypicalPartialNoisy.averagedPayment N H0 H1 c side j (price,θ)) := by
  let Ω:=Signal (AllCountAtypical.ownCount H0 H1 side) R (U*(1+eps))×unitInterval
  let charge:=fun z : Ω=> Hybrid.activeNoisyRealBid eps price z.2
  let I:=fun z : Ω=> AtypicalPartialNoisy.rankInclusion N H0 H1 c side j (charge z,z.1)
  have hp : Measurable charge:=by unfold charge Hybrid.activeNoisyRealBid;fun_prop
  have hI : Measurable I:=(AtypicalPartialNoisy.measurable_rankInclusion N H0 H1 c side j).comp
    (hp.prodMk measurable_fst)
  have hq (z) : I z∈Icc (0:ℝ) 1:=AtypicalPartialNoisy.rankInclusion_bounds N H0 H1 c side j _
  have hb (z) : |charge z|≤|U*(1+eps)| := by
    have hh:=Hybrid.activeNoisyRealBid_mem hR heps price z.2
    rw [abs_of_nonneg (hR.le.trans hh.1)]
    exact hh.2.trans (le_abs_self _)
  have hs:=BoundedProbabilityIntegral.branch ((ProbabilityMeasure.toMeasure θ).prod volume)
    charge I hp hI hb hq v w (if reg then 0 else 1)
  have hi:=BoundedProbabilityIntegral.integrable ((ProbabilityMeasure.toMeasure θ).prod volume) I hI
    (fun z=> by rw [abs_of_nonneg (hq z).1];exact (hq z).2)
  have hpi:=BoundedProbabilityIntegral.integrable ((ProbabilityMeasure.toMeasure θ).prod volume)
    (fun z=> charge z*I z) (hp.mul hI) (fun z=> by
      rw [abs_mul,abs_of_nonneg (hq z).1]
      exact (mul_le_of_le_one_right (abs_nonneg _) (hq z).2).trans (hb z))
  have hc:=BoundedProbabilityIntegral.integrable ((ProbabilityMeasure.toMeasure θ).prod volume) charge hp hb
  have hwhole : Integrable (fun z=>(v-charge z)*(w*(if reg then 0 else 1)+(1-w)*I z))
      ((ProbabilityMeasure.toMeasure θ).prod volume) := by
    have hh:=(((integrable_const (v*w*(if reg then 0 else 1))).sub (hc.const_mul (w*(if reg then 0 else 1)))).add
      (((hi.const_mul v).sub hpi).const_mul (1-w)))
    convert! hh using 1
    funext z
    change (v-charge z)*(w*(if reg then 0 else 1)+(1-w)*I z)=
      (v*w*(if reg then 0 else 1)-(w*(if reg then 0 else 1))*charge z)+
        (1-w)*(v*I z-charge z*I z)
    ring
  rw [integral_prod _ hwhole,integral_prod _ hi,integral_prod _ hpi,integral_prod _ hc] at hs
  simp only [charge,integral_const,probReal_univ,one_smul] at hs
  cases reg <;> simpa only [Bool.false_eq_true,ite_false,ite_true,mul_one,mul_zero,zero_mul,
    AtypicalPartialNoisy.averagedInclusion,AtypicalPartialNoisy.averagedPayment,
    AtypicalPartialNoisy.smoothedInclusion,AtypicalPartialNoisy.smoothedPayment,
    AtypicalPartialNoisy.inputAt,I,charge] using hs

theorem weight_average {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (w : X→ℝ) (hw : Integrable w μ) (v a I P Q : ℝ) :
    (∫x,v*(w x*a+(1-w x)*I)-(w x*P+(1-w x)*Q) ∂μ)=
      v*((∫x,w x ∂μ)*a+(1-(∫x,w x ∂μ))*I)-
        ((∫x,w x ∂μ)*P+(1-(∫x,w x ∂μ))*Q) := by
  have he (x : X) : v*(w x*a+(1-w x)*I)-(w x*P+(1-w x)*Q)=
      (v*I-Q)+(v*a-v*I-P+Q)*w x := by ring
  simp_rw [he]
  rw [integral_add (integrable_const _) (hw.const_mul _),integral_const,integral_const_mul]
  simp only [probReal_univ,one_smul]
  ring

theorem equal_common {N H c : ℕ} {R U Uc eps ξ : ℝ}
    (hR : 0< R) (heps : 0≤ eps)
    (base : Fin N→ Icc (1:ℝ) Uc)
    (bayes θ : ProbabilityMeasure (Signal H R (U*(1+eps))))
    (j : Fin H) (price : Icc R U) (v : ℝ) :
    (∫z : Fin N→ unitInterval,∫s,∫u : unitInterval,(v-Hybrid.activeNoisyRealBid eps price u)*
      privateValue (c:=c) ξ j (noisyInput hR heps j
        (focalPolicyInput (c:=c) (ξ:=ξ) (EqualNoisyUtilities.parameter heps (base,bayes) z) price s) u)
      ∂(volume : Measure unitInterval) ∂(ProbabilityMeasure.toMeasure θ)
      ∂Measure.pi (fun _ : Fin N=>(volume : Measure unitInterval)))=
    EqualNoisyUtilities.privateUtility (c:=c) hR heps ξ j (v,((base,bayes),price,θ)) := by
  simp_rw [equal_average hR heps]
  rfl

theorem unequal_common (N H0 H1 c : ℕ) {ξ B R U eps width e0 F : ℝ}
    (hR : 0< R) (heps : 0≤ eps) (side reg low : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (base : Fin N→ℝ)
    (θ : ProbabilityMeasure (Signal (AllCountAtypical.ownCount H0 H1 side) R (U*(1+eps))))
    (j : Fin (AllCountAtypical.ownCount H0 H1 side)) (price : Icc R U) (v : ℝ) :
    (∫z : Fin N→ unitInterval,∫s,∫u : unitInterval,(v-Hybrid.activeNoisyRealBid eps price u)*
      (UnequalPartialCountPayoff.rawWeight N H0 H1 c ξ B R (U*(1+eps)) width e0 F
        reg low ν0 ν1 (AllNoiseFiniteSelector.noisyBids eps base z)*(if reg then 0 else 1)+
      (1-UnequalPartialCountPayoff.rawWeight N H0 H1 c ξ B R (U*(1+eps)) width e0 F
        reg low ν0 ν1 (AllNoiseFiniteSelector.noisyBids eps base z))*
        AtypicalPartialNoisy.rankInclusion N H0 H1 c side j (Hybrid.activeNoisyRealBid eps price u,s))
      ∂(volume : Measure unitInterval) ∂(ProbabilityMeasure.toMeasure θ)
      ∂Measure.pi (fun _ : Fin N=>(volume : Measure unitInterval)))=
    UnequalPartialCountPayoff.utility N H0 H1 c ξ B R U width e0 F eps side reg low ν0 ν1 j
      (v,base,price,θ) := by
  let w:=fun z : Fin N→ unitInterval=> UnequalPartialCountPayoff.rawWeight N H0 H1 c ξ B R
    (U*(1+eps)) width e0 F reg low ν0 ν1 (AllNoiseFiniteSelector.noisyBids eps base z)
  have hw : Integrable w (Measure.pi (fun _ : Fin N=>(volume : Measure unitInterval))) :=
    BoundedProbabilityIntegral.integrable _ w
      ((UnequalPartialCountPayoff.measurable_rawWeight N H0 H1 c ξ B R (U*(1+eps)) width e0 F
        reg low ν0 ν1).comp ((AllNoiseFiniteSelector.continuous_noisyBids eps).comp
          (continuous_const.prodMk continuous_id)).measurable)
      (fun z=> by
        rw [abs_of_nonneg (UnequalPartialCountPayoff.rawWeight_bounds N H0 H1 c ξ B R
          (U*(1+eps)) width e0 F reg low ν0 ν1 _).1]
        exact (UnequalPartialCountPayoff.rawWeight_bounds N H0 H1 c ξ B R (U*(1+eps)) width e0 F
          reg low ν0 ν1 _).2)
  simp_rw [unequal_average N H0 H1 c hR heps side reg θ j price v]
  rw [weight_average _ w hw v (if reg then 0 else 1)
    (AtypicalPartialNoisy.averagedInclusion N H0 H1 c side j (price,θ))
    (if reg then 0 else ∫u : unitInterval,Hybrid.activeNoisyRealBid eps price u)
    (AtypicalPartialNoisy.averagedPayment N H0 H1 c side j (price,θ))]
  rfl

end FCAppendix.Affine.Tail04.PrivateScalarIntegral
