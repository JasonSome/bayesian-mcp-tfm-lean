import FCAppendix.Affine.Tail04.ZeroPrivateScalar
import FCAppendix.Affine.Tail04.ZeroCommonRowLaw
import FCAppendix.Affine.Tail04.ZeroNoiseFiniteGame
import FCAppendix.Affine.Hybrid.RankReciprocalSampling

noncomputable section
namespace FCAppendix.Affine.Tail04.ZeroPartialC1Integral
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation CompactSourceBidLaws
open NativeZeroNoiseSource ZeroNativeBindings SourceTailNoisyFixedPoint
open NativeLocalPolicy NativePartialExperiment NativePartialProductReduction
open EqualPrivateSignal EqualPrivateUpper PrivatePayoffContinuity PrivatePartialSorting
open PrivateRowSorting SortedAllNoise ZeroPrivateScalar
open scoped BigOperators

private lemma integral_affine {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (f : X→ℝ) (hf : Integrable f ν) (a b : ℝ) :
    (∫ x,a+b*f x ∂ν)=a+b*(∫ x,f x ∂ν) := by
  rw [integral_add (integrable_const _) (hf.const_mul _),integral_const_mul]
  simp only [integral_const,probReal_univ,one_smul]

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (hdR : P.d0< D.R) (H : ℝ) (hUH : D.U< H)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht) (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hfloor : ∀ v,t< v→ H≤ upperBid v) (N : ℕ)
  (hrare : (1-D.ξ)*D.U+D.ξ*D.U*((N+1:ℕ)*
    ((activeMass P.theta*P.zeta*powerTail P.M 10 t)/
      (partialMass+activeMass P.theta*P.zeta*powerTail P.M 10 t)))≤ D.R)

local notation "E" => regions D P hdR H hUH
local notation "K" => localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
local notation "Q" => publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor
local notation "Ds" => installOriginal D P t ht
private lemma region_d : (regions D P hdR H hUH).d=P.d0 := rfl
local notation "ρ" => OriginalPrivateSource.originalEntryLaw E P (region_d D P hdR H hUH) t ht.le πL
  («partial» D P t ht π) (active D P t ht π) upperBid hupperBid hfloor
set_option quotPrecheck false in
local notation "μP" => bidMarginal (π 2).1
set_option quotPrecheck false in
local notation "μA" => bidMarginal (active D P t ht π).1
set_option quotPrecheck false in
local notation "C" => IndependentCounts.bernoulli (Q).θ (Q).θ_nonneg (Q).θ_le_one

theorem integral_signal (h : ℕ) (f : Signal h D.R D.Up→ℝ) (hf : Measurable f) :
    (∫ row,f (signal row) ∂(ProbabilityMeasure.toMeasure (originalIid E h ρ)))=
      ∫ s,f s ∂(ProbabilityMeasure.toMeasure (ZeroNoiseFiniteGame.privateRow Ds h μP)) := by
  have hm := integral_map continuous_signal.measurable.aemeasurable hf.aestronglyMeasurable
    (μ:=(ProbabilityMeasure.toMeasure (originalIid E h ρ)))
  rw [ZeroNativeRowLaws.original_raw_private_signal D P t ht hdR H hUH πL π
    upperBid hupperBid hfloor h] at hm
  exact hm.symm

variable (A : ℕ) (H0 H1 : Fin (N+2)) (side low : Bool)
  (j : Fin (ownH H0 H1 side).val) (v : ℝ) (price : Icc D.R D.Up)

set_option quotPrecheck false in
local notation "θ" => (ProbabilityMeasure.toMeasure (originalIid E (ownH H0 H1 side).val ρ))

def originalIntegral (common : Fin A→ Icc (1:ℝ) D.U) : ℝ :=
  ∫ row,∫ pub : unitInterval,∫ u : unitInterval,
    value K A H0 H1 Q side low j v price common
      (Function.update row j (Sum.inr price)) pub u
        ∂(volume : Measure unitInterval) ∂(volume : Measure unitInterval) ∂θ

theorem measurable_originalIntegral : Measurable
    (originalIntegral D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
      A H0 H1 side low j v price) := by
  let Common:=Fin A→ Icc (1:ℝ) D.U
  let Raw:=Row (ownH H0 H1 side).val D.R D.Up H
  let f : ((Common×Raw)×unitInterval)×unitInterval→ℝ := fun x=>
    value K A H0 H1 Q side low j v price x.1.1.1
      (Function.update x.1.1.2 j (Sum.inr price)) x.1.2 x.2
  have hf : Measurable f := (ZeroPrivateScalar.measurable_value K A H0 H1 Q side low j v).comp
    (by fun_prop : Measurable (fun x : ((Common×Raw)×unitInterval)×unitInterval=>
      (price,(x.1.1.1,(Function.update x.1.1.2 j (Sum.inr price),(x.1.2,x.2))))))
  exact measurable_integral θ _ (measurable_integral volume _ (measurable_integral volume f hf))

theorem originalIntegral_bound (common : Fin A→ Icc (1:ℝ) D.U) :
    ‖originalIntegral D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
      A H0 H1 side low j v price common‖≤|v|+D.Up :=
  integral_bound θ _ _ (fun _row=> integral_bound volume _ _ (fun pub=>
    integral_bound volume _ _ (fun u=> value_bound K A H0 H1 Q side low j v price common _ pub u)))

variable [NullSingletonClass ((ProbabilityMeasure.toMeasure (π 2).1).map (fun x=>(x.2:ℝ)))]

omit [NullSingletonClass ((ProbabilityMeasure.toMeasure (π 2).1).map (fun x=>(x.2:ℝ)))] in
theorem unequal_row_integral (hne : H0≠H1) (common : Fin A→ Icc (1:ℝ) D.U)
    (row : Row (ownH H0 H1 side).val D.R D.Up H)
    (hrow : ∀ l,numericalEntry (row l)≠(price:ℝ)) :
    (∫ pub : unitInterval,∫ u : unitInterval,
      value K A H0 H1 Q side low j v price common
        (Function.update row j (Sum.inr price)) pub u)=
      (v-price)*(C).expect (fun reg=>
        let w:=UnequalPartialCountPayoff.rawWeight A H0.val H1.val D.c D.ξ D.U D.R D.Up
          D.width (D.e0 reg) D.F reg low ((Ds).marksLaw H0.val) ((Ds).marksLaw H1.val)
          (fun q=>(common q:ℝ))
        w*(if reg then 0 else 1)+(1-w)*
          AtypicalPartialNoisy.rankInclusion A H0.val H1.val D.c side j ((price:ℝ),signal row)) := by
  let I:=AtypicalPartialNoisy.rankInclusion A H0.val H1.val D.c side j ((price:ℝ),signal row)
  have he (pub u : unitInterval) :
      value K A H0 H1 Q side low j v price common (Function.update row j (Sum.inr price)) pub u=
      (v-price)*JoinedPartialPublicIntegral.publicRule Q H0.val H1.val D.width
        (sortedBox common) ((K).signalLaw H0) I
        (JoinedPartialPublicIntegral.choice Q H0.val H1.val
          (fun q=>(sortedBox common q:ℝ)) low pub) := by
    have hs := unequal_inclusion K A H0 H1 hne Q side low j price common
      (Function.update row j (Sum.inr price)) (Function.update_self _ _ _)
      (fun l hl=> by simpa only [Function.update_of_ne hl] using! hrow l)
      (base_receipt_gap D) pub u
    change _ = if _ then _ else AtypicalPartialNoisy.rankInclusion A H0.val H1.val D.c
      side j ((price:ℝ),signal (Function.update row j (Sum.inr price))) at hs
    rw [value,hs,rank_signal_update A H0.val H1.val D.c side j row price]
    simp only [JoinedPartialPublicIntegral.publicRule,publicParameter,
      NativeHighExperiment.choice,JoinedPartialPublicIntegral.choice,
      publicData_marksLaw D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare H0,
      publicData_marksLaw D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare H1,
      localData_marksLaw D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare,I]
    rfl
  simp_rw [he]
  simp only [integral_const,probReal_univ,one_smul]
  rw [integral_const_mul,JoinedPartialPublicIntegral.public_rule_integral]
  congr 1
  apply FiniteLaw.expect_congr
  intro reg
  rw [show (fun q=>(sortedBox common q:ℝ))=SortedAllNoise.sorted (fun q=>(common q:ℝ)) from rfl,
    PartialPublicWeights.rawWeight_sorted]
  simp only [publicData_marksLaw D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare H0,
    publicData_marksLaw D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare H1,
    localData_marksLaw D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare]
  rfl

theorem originalIntegral_unequal (hne : H0≠H1) (common : Fin A→ Icc (1:ℝ) D.U) :
    originalIntegral D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
      A H0 H1 side low j v price common=
    ZeroNoiseFiniteGame.partialRegimeFiber Ds A H0.val H1.val side low j ((v,price,μP),common) := by
  have hnat : H0.val≠H1.val := fun he=> hne (Fin.ext he)
  let f := fun s : Signal (ownH H0 H1 side).val D.R D.Up=>
    AtypicalPartialNoisy.rankInclusion A H0.val H1.val D.c side j ((price:ℝ),s)
  have hf : Measurable f := (AtypicalPartialNoisy.measurable_rankInclusion A H0.val H1.val D.c side j).comp (measurable_const.prodMk measurable_id)
  have hsf : Measurable (fun row : Row (ownH H0 H1 side).val D.R D.Up H=> f (signal row)) :=
    hf.comp continuous_signal.measurable
  have hi : Integrable (fun row : Row (ownH H0 H1 side).val D.R D.Up H=> f (signal row)) θ :=
    integrable_bounded θ _ hsf 1 (fun row=> by
      rw [Real.norm_eq_abs,abs_of_nonneg (AtypicalPartialNoisy.rankInclusion_bounds A H0.val H1.val D.c side j _).1]
      exact (AtypicalPartialNoisy.rankInclusion_bounds A H0.val H1.val D.c side j _).2)
  have hr := ZeroPrivateRegularity.source_raw_numerical D P t ht hdR H hUH πL π
    upperBid hupperBid hfloor (ownH H0 H1 side).val price
  unfold originalIntegral
  calc
    _=∫ row,(v-price)*(C).expect (fun reg=>
        let w:=UnequalPartialCountPayoff.rawWeight A H0.val H1.val D.c D.ξ D.U D.R D.Up
          D.width (D.e0 reg) D.F reg low ((Ds).marksLaw H0.val) ((Ds).marksLaw H1.val)
          (fun q=>(common q:ℝ))
        w*(if reg then 0 else 1)+(1-w)*f (signal row)) ∂θ := by
      apply integral_congr_ae
      exact hr.mono fun row hrow=> unequal_row_integral D P t ht hdR H hUH πL π upperBid hupperBid
        hfloor N hrare A H0 H1 side low j v price hne common row hrow
    _=_ := by
      let weight : Bool→ℝ := fun reg => UnequalPartialCountPayoff.rawWeight A H0.val H1.val D.c
        D.ξ D.U D.R D.Up D.width (D.e0 reg) D.F reg low ((Ds).marksLaw H0.val) ((Ds).marksLaw H1.val)
          (fun q=>(common q:ℝ))
      have hiw := Hybrid.integral_finite_expect θ C
        (fun row reg => weight reg*(if reg then 0 else 1)+(1-weight reg)*f (signal row))
        (fun _ => (integrable_const _).add (hi.const_mul _))
      have his := integral_signal D P t ht hdR H hUH πL π upperBid hupperBid hfloor
        (ownH H0 H1 side).val f hf
      calc
        _ = (v-price)*(C).expect (fun reg => ∫ row,
            weight reg*(if reg then 0 else 1)+(1-weight reg)*f (signal row) ∂θ) := by
          exact (integral_const_mul (v-price) _).trans (congrArg (fun z : ℝ => (v-price)*z) hiw)
        _ = (v-price)*(C).expect (fun reg => weight reg*(if reg then 0 else 1)+
            (1-weight reg)*(∫ row,f (signal row) ∂θ)) := by
          congr 1
          apply FiniteLaw.expect_congr
          intro reg
          simpa using! integral_affine θ (fun row => f (signal row)) hi
            (weight reg*(if reg then 0 else 1)) (1-weight reg)
        _ = (v-price)*(C).expect (fun reg => weight reg*(if reg then 0 else 1)+
            (1-weight reg)*(∫ rawSignal,f rawSignal
              ∂(ProbabilityMeasure.toMeasure (ZeroNoiseFiniteGame.privateRow Ds (ownH H0 H1 side).val μP)))) :=
          congrArg (fun z : ℝ => (v-price)*(C).expect
            (fun reg => weight reg*(if reg then 0 else 1)+(1-weight reg)*z)) his
        _ = _ := by
          let privateIntegral := ∫ rawSignal,f rawSignal
            ∂(ProbabilityMeasure.toMeasure (ZeroNoiseFiniteGame.privateRow Ds (ownH H0 H1 side).val μP))
          simp only [IndependentCounts.expect_bernoulli,ZeroNoiseFiniteGame.partialRegimeFiber,
            ZeroNoiseFiniteGame.partialFiber,dif_neg hnat]
          let regimeValueScalar := fun reg : Bool =>
            weight reg*(if reg then 0 else 1)+(1-weight reg)*privateIntegral
          change (v-price)*((1-(D.regimeShare:ℝ))*regimeValueScalar false+
            (D.regimeShare:ℝ)*regimeValueScalar true)=
            (1-(D.regimeShare:ℝ))*((v-price)*regimeValueScalar false)+
              (D.regimeShare:ℝ)*((v-price)*regimeValueScalar true)
          ring

include P t ht hdR H hUH πL A π upperBid hupperBid hfloor hrare low v price in
theorem originalIntegral_equal_zero (h : Fin (N+2)) (common : Fin A→ Icc (1:ℝ) D.U)
    (q : Fin h.val)
    (hc : ∀ l,EqualReceiptLaw.receipt (c:=D.c) (ξ:=D.ξ) ((K).signalLaw h)
      (sortedBox common) l≠(price:ℝ)) :
    originalIntegral D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
      A h h false low q v price common=
    ZeroNoiseFiniteGame.partialRegimeFiber Ds A h.val h.val false low q ((v,price,μP),common) := by
  let f := fun s : Signal h.val D.R D.Up=> privateValue (c:=D.c) D.ξ q
    (policyInput (c:=D.c) (ξ:=D.ξ) (sortedBox common,(K).signalLaw h)
      (Function.update s q (Sum.inr price)))
  have hf : Measurable f := (measurable_privateValue D.ξ q).comp
    (by unfold policyInput;fun_prop)
  have hmap := integral_signal D P t ht hdR H hUH πL π upperBid hupperBid hfloor h.val f hf
  have hr := ZeroPrivateRegularity.source_raw_numerical D P t ht hdR H hUH πL π
    upperBid hupperBid hfloor h.val price
  have heq : originalIntegral D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
      A h h false low q v price common=(v-price)*(∫ s,f s ∂(ProbabilityMeasure.toMeasure (ZeroNoiseFiniteGame.privateRow Ds h.val μP))) := by
    rw [←hmap,←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hr] with row hrow
    have hreg := ZeroPrivateRegularity.regular_focal D.hR (sortedBox common) ((K).signalLaw h)
      (Function.update row q (Sum.inr price)) q price (Function.update_self _ _ _) hc
      (fun l hl=> by simpa only [Function.update_of_ne hl] using! hrow l)
    have hpoint (pub u : unitInterval) := equal_value_zero K A h Q low q price v common
      (Function.update row q (Sum.inr price)) (Function.update_self _ _ _) hreg pub u
    change (∫ pub : unitInterval,∫ u : unitInterval,_)=_
    trans (∫ _pub : unitInterval,∫ _u : unitInterval,(v-price)*f (signal row))
    · apply integral_congr_ae
      exact ae_of_all _ fun pub => integral_congr_ae (ae_of_all _ fun u => by
        simpa only [signal_update,f] using! hpoint pub u)
    · simp only [integral_const,probReal_univ,one_smul]
  rw [heq]
  simp only [ZeroNoiseFiniteGame.partialRegimeFiber,ZeroNoiseFiniteGame.partialFiber,
    dite_true,AllCountAtypical.ownCount]
  have hfEq : f=ZeroNoiseFiniteGame.equalPartialValue Ds A h.val q common μP price := by
    funext s
    have he := congrArg (fun lawPrivate : WeakProbability.Law (Signal h.val D.R D.Up) =>
      privateValue (c:=D.c) D.ξ q (policyInput (c:=D.c) (ξ:=D.ξ)
        (sortedBox common,lawPrivate) (Function.update s q (Sum.inr price))))
      (localData_signal D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare h)
    simpa only [f,ZeroNoiseFiniteGame.equalPartialValue,policyInput] using! he
  rw [hfEq]
  simp only [Fin.cast,Fin.eta]
  ring

include P t ht hdR H hUH πL A π upperBid hupperBid hfloor hrare low v price in
theorem originalIntegral_equal_one (h : Fin (N+2)) (common : Fin A→ Icc (1:ℝ) D.U)
    (q : Fin h.val)
    (hc : ∀ l,EqualReceiptLaw.receipt (c:=D.c) (ξ:=D.ξ) ((K).signalLaw h)
      (sortedBox common) l≠(price:ℝ)) :
    originalIntegral D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
      A h h true low q v price common=
    ZeroNoiseFiniteGame.partialRegimeFiber Ds A h.val h.val true low q ((v,price,μP),common) := by
  have hh := originalIntegral_equal_zero D P t ht hdR H hUH πL π upperBid hupperBid hfloor
    N hrare A low v price h common q hc
  simpa only [originalIntegral,value,NativePartialExperiment.inclusion,sampler_true,(K).oneSampler_equal,sampler_false,(K).zeroSampler_equal,
    ZeroNoiseFiniteGame.partialRegimeFiber,ZeroNoiseFiniteGame.partialFiber,dite_true,
    Fin.cast_eq_self,AllCountAtypical.ownCount,ownH,ite_false,ite_true] using! hh

variable [NullSingletonClass (ProbabilityMeasure.toMeasure (bidMarginal (active D P t ht π).1))]

theorem originalIntegral_eq :
    ∀ᵐ common ∂Measure.pi (fun _ : Fin A=>(ProbabilityMeasure.toMeasure μA)),
      originalIntegral D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
        A H0 H1 side low j v price common=
      ZeroNoiseFiniteGame.partialRegimeFiber Ds A H0.val H1.val side low j ((v,price,μP),common) := by
  by_cases h : H0=H1
  · subst H1
    filter_upwards [ZeroPrivateRegularity.source_common_receipts D P t ht hdR H hUH πL π
      upperBid hupperBid hfloor N hrare A H0 price] with common hc
    cases side
    · exact originalIntegral_equal_zero D P t ht hdR H hUH πL π upperBid hupperBid hfloor
        N hrare A low v price H0 common j hc
    · exact originalIntegral_equal_one D P t ht hdR H hUH πL π upperBid hupperBid hfloor
        N hrare A low v price H0 common j hc
  · exact ae_of_all _ fun common=> originalIntegral_unequal D P t ht hdR H hUH πL π upperBid
      hupperBid hfloor N hrare A H0 H1 side low j v price h common

include hdR H hUH πL upperBid hupperBid hfloor hrare in
theorem integrable_regime : Integrable (fun common : Fin A→ Icc (1:ℝ) D.U=>
    ZeroNoiseFiniteGame.partialRegimeFiber Ds A H0.val H1.val side low j ((v,price,μP),common))
      (Measure.pi (fun _ : Fin A=>(ProbabilityMeasure.toMeasure μA))) := by
  have hi := integrable_bounded (Measure.pi (fun _ : Fin A=>(ProbabilityMeasure.toMeasure μA)))
    (originalIntegral D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
      A H0 H1 side low j v price)
    (measurable_originalIntegral D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
      A H0 H1 side low j v price) (|v|+D.Up)
    (originalIntegral_bound D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
      A H0 H1 side low j v price)
  exact hi.congr (originalIntegral_eq D P t ht hdR H hUH πL π upperBid hupperBid hfloor
    N hrare A H0 H1 side low j v price)

end FCAppendix.Affine.Tail04.ZeroPartialC1Integral
