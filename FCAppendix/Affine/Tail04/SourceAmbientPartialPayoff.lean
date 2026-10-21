import FCAppendix.Affine.Tail04.AmbientPrivateTransport

noncomputable section
namespace FCAppendix.Affine.Tail04.SourceAmbientPartialPayoff
open MeasureTheory ProbabilityTheory Set Classical
open Existence.Distributional EqualPrivateSignal CompactSourceBidLaws FixedAmbientNoise
open FiniteTailNoisyGame SourceTailNoisyFixedPoint AmbientFiniteGame SourceAmbientPayoff

variable (D : Data) (A H0 H1 : ℕ) (side reg low : Bool)
  (j : Fin (AllCountAtypical.ownCount H0 H1 side))
  (μP : ProbabilityMeasure (Icc D.R D.Up)) (μA : ProbabilityMeasure (Icc (1:ℝ) D.U))

theorem partial_positive (e : Noise D.eps) (he : 0<(e:ℝ)) (hes : (e:ℝ)< D.eps)
    (v : ℝ) (price : Icc D.R D.Up) :
    AmbientFiniteGame.«partial» D A H0 H1 side reg low j e μP μA v price=
      ∫b,(atNoise D e he hes).partialFiber A H0 H1 side low reg j ((v,price,μP),b)
        ∂(ProbabilityMeasure.toMeasure (rowLaw A μA)) := by
  by_cases h : H0=H1
  · simp only [AmbientFiniteGame.«partial»,Data.partialFiber,dif_pos h]
    let jj : Fin H0:=Fin.cast (by cases side <;> simp [AllCountAtypical.ownCount,h]) j
    erw [AmbientPrivateTransport.positive D A H0 μP μA e he hes
      (fun z=> equalPrivateValue D A H0 jj e μP v price z.1 z.2.1 z.2.2)
      (measurable_equalPrivateValue D A H0 jj e μP v price)
      (fun z=> equalPrivateValue_bound D A H0 jj e μP v price z.1 z.2.1 z.2.2)]
    simp_rw [equal_value_positive D A e he hes μP H0 jj v price]
    apply integral_congr_ae
    refine ae_of_all _ fun base=>?_
    simpa only [EqualNoisyUtilities.parameter,EqualNoisyUtilities.physical,
      OriginalNoiseProduct.physicalRow,PrivatePayoffContinuity.noisyInput,
      PrivatePayoffContinuity.focalPolicyInput,
      EqualPrivateMeasurable.bids,EqualPrivateMeasurable.forget,
      EqualPrivateContinuity.parameterBids,CompactSourceBidLaws.noisyBid,
      SourceTailNoisyFixedPoint.atNoise,Data.B,Data.V,jj] using!
      PrivateScalarIntegral.equal_common (c:=D.c) (ξ:=D.ξ)
        (U:=D.Up) (Uc:=D.U) (eps:=(e:ℝ)) D.hR he.le base
        ((atNoise D e he hes).privateBayes H0 μP)
        ((atNoise D e he hes).privateFocalRow H0 μP) jj price v
  · simp only [AmbientFiniteGame.«partial»,Data.partialFiber,dif_neg h]
    erw [AmbientPrivateTransport.positive D A (AllCountAtypical.ownCount H0 H1 side) μP μA e he hes
      (fun z=> unequalPrivateValue D A H0 H1 side reg low j e v price z.1 z.2.1 z.2.2)
      (measurable_unequalPrivateValue D A H0 H1 side reg low j e v price)
      (fun z=> unequalPrivateValue_bound D A H0 H1 side reg low j e v price z.1 z.2.1 z.2.2)]
    simp_rw [unequal_value_positive D A H0 H1 reg low e side j v price]
    apply integral_congr_ae
    refine ae_of_all _ fun base=>?_
    simpa only [OriginalNoiseProduct.physicalRow,CompactSourceBidLaws.noisyBid,
      AllNoiseFiniteSelector.noisyBids,Hybrid.activeNoisyRealBid,
      SourceTailNoisyFixedPoint.atNoise,Data.B,Data.V,Data.e0,Data.marksLaw] using!
      PrivateScalarIntegral.unequal_common A H0 H1 D.c (ξ:=D.ξ)
        (B:=D.U*(1+(e:ℝ))) (U:=D.Up) (eps:=(e:ℝ)) (width:=D.width) (e0:=D.e0 reg) (F:=D.F)
        D.hR he.le side reg low (D.marksLaw H0) (D.marksLaw H1) (fun i=>(base i:ℝ))
        ((atNoise D e he hes).privateFocalRow (AllCountAtypical.ownCount H0 H1 side) μP) j price v

theorem partial_zero (v : ℝ) (price : Icc D.R D.Up) :
    AmbientFiniteGame.«partial» D A H0 H1 side reg low j (zero D.eps D.heps.le) μP μA v price=
      ∫b,ZeroNoiseFiniteGame.partialFiber D A H0 H1 side low reg j ((v,price,μP),b)
        ∂(ProbabilityMeasure.toMeasure (rowLaw A μA)) := by
  by_cases h : H0=H1
  · simp only [AmbientFiniteGame.«partial»,ZeroNoiseFiniteGame.partialFiber,dif_pos h]
    let jj : Fin H0:=Fin.cast (by cases side <;> simp [AllCountAtypical.ownCount,h]) j
    erw [AmbientPrivateTransport.zero D A H0 μP μA
      (fun z=> equalPrivateValue D A H0 jj (zero D.eps D.heps.le) μP v price z.1 z.2.1 z.2.2)
      (measurable_equalPrivateValue D A H0 jj (zero D.eps D.heps.le) μP v price)]
    simp_rw [equal_value_zero D A μP H0 jj v price]
    simp only [integral_const,probReal_univ,one_smul,integral_const_mul]
    rfl
  · simp only [AmbientFiniteGame.«partial»,ZeroNoiseFiniteGame.partialFiber,dif_neg h]
    erw [AmbientPrivateTransport.zero D A (AllCountAtypical.ownCount H0 H1 side) μP μA
      (fun z=> unequalPrivateValue D A H0 H1 side reg low j (zero D.eps D.heps.le) v price z.1 z.2.1 z.2.2)
      (measurable_unequalPrivateValue D A H0 H1 side reg low j (zero D.eps D.heps.le) v price)]
    simp_rw [unequal_value_zero D A H0 H1 reg low side j v price]
    simp only [integral_const,probReal_univ,one_smul,integral_const_mul]

    apply congrArg (fun z : ℝ => (v-(price:ℝ))*z)
    apply integral_congr_ae
    refine ae_of_all _ fun b=>?_
    have hi:=BoundedProbabilityIntegral.integrable
      (ProbabilityMeasure.toMeasure
        (ZeroNoiseFiniteGame.privateRow D (AllCountAtypical.ownCount H0 H1 side) μP))
      (fun s : Signal (AllCountAtypical.ownCount H0 H1 side) D.R D.Up =>
        AtypicalPartialNoisy.rankInclusion A H0 H1 D.c side j ((price:ℝ),s))
      ((AtypicalPartialNoisy.measurable_rankInclusion A H0 H1 D.c side j).comp
        (measurable_const.prodMk measurable_id)) (fun s=> by
          rw [abs_of_nonneg (AtypicalPartialNoisy.rankInclusion_bounds A H0 H1 D.c side j _).1]
          exact (AtypicalPartialNoisy.rankInclusion_bounds A H0 H1 D.c side j _).2)
    dsimp only
    rw [integral_add (integrable_const _) (hi.const_mul _),integral_const,integral_const_mul]
    simp only [probReal_univ,one_smul]

end FCAppendix.Affine.Tail04.SourceAmbientPartialPayoff
