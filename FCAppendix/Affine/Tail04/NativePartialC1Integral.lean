import FCAppendix.Affine.Tail04.NativePartialProductReduction

noncomputable section
namespace FCAppendix.Affine.Tail04.NativePartialC1Integral
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation CompactSourceBidLaws
open NativeNoisySource NativeNoisyBindings SourceTailNoisyFixedPoint
open NativeLocalPolicy NativePartialExperiment NativePartialProductReduction
open EqualPrivateSignal EqualPrivateUpper JoinedHighPolicy JoinedPartialNoisy
open AtypicalPartialNoisy UnequalPartialOriginalIntegral PrivateRowSorting SortedAllNoise
open scoped BigOperators

local instance (α : Type*) : MeasurableSpace (Finset α) := ⊤

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht)
  (upperBid : ℝ → ℝ) (hupperBid : Measurable upperBid)
  (hfloor : ∀ v,t< v → H≤ upperBid v) (N : ℕ)
variable (hrare : (1-D.ξ)*D.B+D.ξ*D.B*(((N+1):ℝ)*((activeMass P.theta*P.zeta*powerTail P.M 10 t)/(partialMass+(activeMass P.theta*P.zeta*powerTail P.M 10 t))))≤ D.R)

def partialBidLaw : ProbabilityMeasure (Icc (installOriginal D P t ht).R (installOriginal D P t ht).Up) :=
  bidMarginal (π 2).1

lemma rawSignalLaw_eq (h : ℕ) :
    originalSignalLaw (ProbabilityMeasure.toMeasure (originalIid (regions D P hdR H hBH) h (NoisyNativeFiberProduct.privateRowLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor)))=(installOriginal D P t ht).privateFocalRow h (partialBidLaw D P t ht π) := by
  apply ProbabilityMeasure.toMeasure_injective
  exact NoisyNativeRowLaws.original_raw_private_signal D P t ht hdR H hBH πL π
    upperBid hupperBid hfloor h

lemma bayesLaw_eq (h : Fin ((N+1)+1)) : (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).signalLaw h=WeakProbability.mk ((installOriginal D P t ht).privateBayes h.val (partialBidLaw D P t ht π)) := by
  rw [←WeakProbability.mk_val ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).signalLaw h),
    localData_signalProbability D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare]
  rfl

variable (A : ℕ) (H0 H1 : Fin ((N+1)+1)) (side low : Bool)
  (j : Fin (ownH H0 H1 side).val) (v : ℝ) (price : Icc D.R D.Up)

def branch (reg : Bool) (x : (Fin A→ Icc (1:ℝ) (regions D P hdR H hBH).U)×
    (Row (ownH H0 H1 side).val (regions D P hdR H hBH).R (regions D P hdR H hBH).Rp (regions D P hdR H hBH).H×unitInterval)) : ℝ :=
  let _source := (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare)
  branchValue A H0.val H1.val D.c (ξ:=D.ξ) side reg (fun k => (x.1 k:ℝ)) D.hR D.heps.le
    j price v (UnequalPartialCountPayoff.rawWeight A H0.val H1.val D.c D.ξ D.B D.R D.V
      D.width (D.e0 reg) D.F reg low ((installOriginal D P t ht).marksLaw H0.val) ((installOriginal D P t ht).marksLaw H1.val)
        (fun k => (x.1 k:ℝ))) x.2.1 x.2.2

lemma measurable_branch (reg : Bool) : Measurable
    (branch D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare A H0 H1 side low j v price reg) := by
  have hb : Measurable (fun x : (Fin A→ Icc (1:ℝ) (regions D P hdR H hBH).U)×
      (Row (ownH H0 H1 side).val (regions D P hdR H hBH).R (regions D P hdR H hBH).Rp (regions D P hdR H hBH).H×unitInterval) => fun k => (x.1 k:ℝ)) :=
    measurable_pi_lambda _ (fun k => ((measurable_pi_apply k).comp measurable_fst).subtype_val)
  have hp : Measurable (fun x : (Fin A→Icc (1:ℝ) (regions D P hdR H hBH).U)×(Row (ownH H0 H1 side).val (regions D P hdR H hBH).R (regions D P hdR H hBH).Rp (regions D P hdR H hBH).H×unitInterval) => noisyPrice (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) D.heps.le rfl price x.2.2) :=
    (measurable_noisyPrice (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) D.heps.le rfl price).comp measurable_snd.snd
  have hr : Measurable (fun x : (Fin A→ Icc (1:ℝ) (regions D P hdR H hBH).U)×
      (Row (ownH H0 H1 side).val (regions D P hdR H hBH).R (regions D P hdR H hBH).Rp (regions D P hdR H hBH).H×unitInterval) =>
      noisyRow D.hR D.heps.le j price x.2.1 x.2.2) := by
    have hinput : Measurable (fun x : (Fin A→Icc (1:ℝ) (regions D P hdR H hBH).U)×(Row (ownH H0 H1 side).val (regions D P hdR H hBH).R (regions D P hdR H hBH).Rp (regions D P hdR H hBH).H×unitInterval) =>
        (x.2.1,(Sum.inr (noisyPrice (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) D.heps.le rfl price x.2.2) : Ici (regions D P hdR H hBH).H⊕Icc (regions D P hdR H hBH).R (regions D P hdR H hBH).Rp))) :=
      measurable_snd.fst.prodMk (measurable_inr.comp hp)
    have hup : Measurable (fun z : Row (ownH H0 H1 side).val (regions D P hdR H hBH).R (regions D P hdR H hBH).Rp (regions D P hdR H hBH).H×
        (Ici (regions D P hdR H hBH).H⊕Icc (regions D P hdR H hBH).R (regions D P hdR H hBH).Rp) => Function.update z.1 j z.2) := measurable_update'
    have hh := hup.comp hinput
    exact hh
  have hs := (AllCountAtypical.measurable_select A H0.val H1.val D.c D.ξ side).comp (hb.prodMk hr)
  have hi : Measurable (fun x : (Fin A→Icc (1:ℝ) (regions D P hdR H hBH).U)×(Row (ownH H0 H1 side).val (regions D P hdR H hBH).R (regions D P hdR H hBH).Rp (regions D P hdR H hBH).H×unitInterval) => if Sum.inr j∈AllCountAtypical.select A H0.val H1.val D.c D.ξ
      (fun k => (x.1 k:ℝ)) side (noisyRow D.hR D.heps.le j price x.2.1 x.2.2)
      then (1:ℝ) else 0) :=
    Measurable.ite (hs (Set.to_countable {S : Finset (Fin A⊕Fin (ownH H0 H1 side).val) | Sum.inr j∈S}).measurableSet) measurable_const measurable_const
  have hw := (UnequalPartialCountPayoff.measurable_rawWeight A H0.val H1.val D.c D.ξ D.B D.R D.V
    D.width (D.e0 reg) D.F reg low ((installOriginal D P t ht).marksLaw H0.val) ((installOriginal D P t ht).marksLaw H1.val)).comp hb
  exact (measurable_const.sub hp.subtype_val).mul
    ((hw.mul measurable_const).add ((measurable_const.sub hw).mul hi))

lemma branch_bound (reg : Bool) (x) :
    |branch D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare A H0 H1 side low j v price reg x|
      ≤|v|+D.V := by
  have hw := UnequalPartialCountPayoff.rawWeight_bounds A H0.val H1.val D.c D.ξ D.B D.R D.V
    D.width (D.e0 reg) D.F reg low ((installOriginal D P t ht).marksLaw H0.val) ((installOriginal D P t ht).marksLaw H1.val)
      (fun k => (x.1 k:ℝ))
  have hp := Hybrid.activeNoisyRealBid_mem D.hR D.heps.le price x.2.2
  let I : ℝ := if Sum.inr j∈AllCountAtypical.select A H0.val H1.val D.c D.ξ
    (fun k => (x.1 k:ℝ)) side (noisyRow D.hR D.heps.le j price x.2.1 x.2.2) then 1 else 0
  have hI : I∈Icc (0:ℝ) 1 := by unfold I;split_ifs <;> norm_num
  let w := UnequalPartialCountPayoff.rawWeight A H0.val H1.val D.c D.ξ D.B D.R D.V
    D.width (D.e0 reg) D.F reg low ((installOriginal D P t ht).marksLaw H0.val) ((installOriginal D P t ht).marksLaw H1.val)
      (fun k => (x.1 k:ℝ))
  have hfactor : w*(if reg then (0:ℝ) else 1)+(1-w)*I∈Icc (0:ℝ) 1 := by
    cases reg <;> simp only [Bool.false_eq_true,ite_false,ite_true,mul_zero,mul_one]
    all_goals constructor <;> nlinarith [hw.1,hw.2,hI.1,hI.2]
  change |(v-Hybrid.activeNoisyRealBid D.eps price x.2.2)*
    (w*(if reg then (0:ℝ) else 1)+(1-w)*I)|≤_
  rw [abs_mul,abs_of_nonneg hfactor.1]
  calc
    _≤|v-Hybrid.activeNoisyRealBid D.eps price x.2.2| :=
      mul_le_of_le_one_right (abs_nonneg _) hfactor.2
    _≤|v|+|Hybrid.activeNoisyRealBid D.eps price x.2.2| := abs_sub _ _
    _≤|v|+D.V := by
      rw [abs_of_nonneg (D.hR.le.trans hp.1)]
      exact add_le_add le_rfl hp.2

def branchMean (reg : Bool) (b : Fin A→ Icc (1:ℝ) (regions D P hdR H hBH).U)
    (row : Row (ownH H0 H1 side).val (regions D P hdR H hBH).R (regions D P hdR H hBH).Rp (regions D P hdR H hBH).H) : ℝ :=
  ∫ a : unitInterval,branch D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare A H0 H1
    side low j v price reg (b,(row,a))

lemma measurable_branchMean (reg : Bool) : Measurable
    (Function.uncurry (branchMean D P t ht hdR H hBH πL π upperBid hupperBid hfloor
      N hrare A H0 H1 side low j v price reg)) :=
  measurable_integral volume _ ((measurable_branch D P t ht hdR H hBH πL π upperBid hupperBid
    hfloor N hrare A H0 H1 side low j v price reg).comp
      (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)))

lemma branchMean_bound (reg : Bool) (b) (row) :
    ‖branchMean D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare A H0 H1 side low j v price reg b row‖
      ≤|v|+D.V := integral_bound volume _ _ (fun _ =>
    branch_bound D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare A H0 H1 side low j v price reg _)

theorem branchMean_sorted (reg : Bool) (b : Fin A→ Icc (1:ℝ) (regions D P hdR H hBH).U)
    (row : Row (ownH H0 H1 side).val (regions D P hdR H hBH).R (regions D P hdR H hBH).Rp (regions D P hdR H hBH).H) :
    branchMean D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare A H0 H1 side low j v price reg
      (sortedBox b) row=
    branchMean D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare A H0 H1 side low j v price reg b row := by
  unfold branchMean branch
  dsimp only
  have hs : (fun k => (sortedBox b k:ℝ))=SortedAllNoise.sorted (fun k => (b k:ℝ)) := rfl
  rw [hs,PartialPublicWeights.rawWeight_sorted,←hs]
  have hleft := branchValue_integral A H0.val H1.val D.c side reg _ row ⟨D.hξ.le,D.hξ1.le⟩
      (fun k => (sortedBox b k).2) D.hR D.heps
      ((regions D P hdR H hBH).R_le_Rp.trans (regions D P hdR H hBH).Rp_lt_H.le) D.hRp D.hgap (regions D P hdR H hBH).Rp_lt_H j price v (UnequalPartialCountPayoff.rawWeight A H0.val H1.val D.c D.ξ D.B D.R D.V D.width (D.e0 reg) D.F reg low ((installOriginal D P t ht).marksLaw H0.val) ((installOriginal D P t ht).marksLaw H1.val) (fun k => (b k:ℝ)))
  have hright := branchValue_integral A H0.val H1.val D.c side reg _ row ⟨D.hξ.le,D.hξ1.le⟩
      (fun k => (b k).2) D.hR D.heps
      ((regions D P hdR H hBH).R_le_Rp.trans (regions D P hdR H hBH).Rp_lt_H.le) D.hRp D.hgap (regions D P hdR H hBH).Rp_lt_H j price v (UnequalPartialCountPayoff.rawWeight A H0.val H1.val D.c D.ξ D.B D.R D.V D.width (D.e0 reg) D.F reg low ((installOriginal D P t ht).marksLaw H0.val) ((installOriginal D P t ht).marksLaw H1.val) (fun k => (b k:ℝ)))
  exact hleft.trans hright.symm

lemma sampler_unequal (h : H0≠H1) :
    sampler (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) A H0 H1 side=
      unequalSide A H0.val H1.val D.c D.ξ (regions D P hdR H hBH).U (regions D P hdR H hBH).R (regions D P hdR H hBH).Rp (regions D P hdR H hBH).H D.width
        ((publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor).marksLaw H0.val) ((publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor).marksLaw H1.val) side := by
  cases side
  · exact (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).zeroSampler_unequal A H0 H1 h
  · exact (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).oneSampler_unequal A H0 H1 h

theorem unequal_row_integral (h : H0≠H1) (b : Fin A→ Icc (1:ℝ) (regions D P hdR H hBH).U)
    (row : Row (ownH H0 H1 side).val (regions D P hdR H hBH).R (regions D P hdR H hBH).Rp (regions D P hdR H hBH).H) :
    (∫ a : unitInterval,∫ pub : unitInterval,∫ u : unitInterval,
      noisyValue (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) A H0 H1 D.heps.le rfl (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor) side low j v price b row a pub u)=
      (IndependentCounts.bernoulli (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor).θ (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor).θ_nonneg (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor).θ_le_one).expect (fun reg => branchMean D P t ht hdR H hBH πL π upperBid hupperBid hfloor
        N hrare A H0 H1 side low j v price reg b row) := by
  have he (a pub u : unitInterval) : noisyValue (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) A H0 H1 D.heps.le rfl (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor) side low j v price b row a pub u=
      JoinedPartialPublicIntegral.samplerValue (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor) H0.val H1.val D.width side low
        (sortedBox b) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).signalLaw H0) D.hR D.heps.le j price row (fun _ => Equiv.refl _) v a pub u := by
    unfold noisyValue value NativePartialExperiment.inclusion
    rw [sampler_unequal D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare A H0 H1 side h]
    rfl
  simp_rw [he]
  rw [JoinedPartialPublicIntegral.sampler_ownNoise_integral (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor) H0.val H1.val D.width side low
    (sortedBox b) ((localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).signalLaw H0) D.hξ D.hξ1.le D.hw D.hR D.heps
    ((regions D P hdR H hBH).R_le_Rp.trans (regions D P hdR H hBH).Rp_lt_H.le) D.hRp D.hgap (regions D P hdR H hBH).Rp_lt_H j price row (fun _ => Equiv.refl _) v]
  erw [publicData_marksLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare H0,
    publicData_marksLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare H1,
    localData_marksLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare H0,
    localData_marksLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare H1]
  change (∫ a : unitInterval,(IndependentCounts.bernoulli (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor).θ (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor).θ_nonneg (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor).θ_le_one).expect (fun reg =>
    branch D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare A H0 H1 side low j v price reg
      (sortedBox b,(row,a))))=_
  erw [integral_finite_expect (IndependentCounts.bernoulli (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor).θ (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor).θ_nonneg (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor).θ_le_one) volume
    (fun reg a => branch D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare A H0 H1 side low j v price reg (sortedBox b,(row,a)))
    (fun reg => (measurable_branch D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare
      A H0 H1 side low j v price reg).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
    (|v|+D.V) (fun reg a => branch_bound D P t ht hdR H hBH πL π upperBid hupperBid hfloor
      N hrare A H0 H1 side low j v price reg _)]
  exact FiniteLaw.expect_congr (IndependentCounts.bernoulli (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor).θ (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor).θ_nonneg (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor).θ_le_one) (fun reg => branchMean_sorted D P t ht hdR H hBH πL π
    upperBid hupperBid hfloor N hrare A H0 H1 side low j v price reg b row)

def originalIntegral (base : Fin A→ Icc (1:ℝ) D.U) : ℝ :=
  ∫ commonNoise : Fin A→ unitInterval,∫ row,∫ a : unitInterval,∫ pub : unitInterval,∫ u : unitInterval,
    noisyValue (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) A H0 H1 D.heps.le rfl (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor) side low j v price
      (EqualNoisyUtilities.physical D.heps.le base commonNoise) row a pub u
        ∂(volume : Measure unitInterval) ∂(volume : Measure unitInterval)
        ∂(volume : Measure unitInterval) ∂(ProbabilityMeasure.toMeasure (originalIid (regions D P hdR H hBH) (ownH H0 H1 side).val (NoisyNativeFiberProduct.privateRowLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor))) ∂(Measure.pi (fun _ : Fin A => (volume : Measure unitInterval)))

theorem originalIntegral_unequal (h : H0≠H1) (base : Fin A→ Icc (1:ℝ) D.U) :
    originalIntegral D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare
      A H0 H1 side low j v price base=
      (installOriginal D P t ht).partialRegimeFiber A H0.val H1.val side low j ((v,price,(partialBidLaw D P t ht π)),base) := by
  have hnat : H0.val≠H1.val := fun he => h (Fin.ext he)
  unfold originalIntegral
  simp_rw [unequal_row_integral D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare
    A H0 H1 side low j v price h]
  let ff := fun reg : Bool => fun x : (Fin A→ unitInterval)×
      Row (ownH H0 H1 side).val (regions D P hdR H hBH).R (regions D P hdR H hBH).Rp (regions D P hdR H hBH).H =>
    branchMean D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare A H0 H1 side low j v price reg
      (EqualNoisyUtilities.physical D.heps.le base x.1) x.2
  have hf (reg : Bool) : Measurable (ff reg) := by
    have hin : Measurable (fun x : (Fin A→unitInterval)×
        Row (ownH H0 H1 side).val (regions D P hdR H hBH).R (regions D P hdR H hBH).Rp (regions D P hdR H hBH).H =>
        (EqualNoisyUtilities.physical D.heps.le base x.1,x.2)) :=
      (((EqualNoisyUtilities.continuous_physical D.heps.le).comp
        (continuous_const.prodMk continuous_id)).measurable.comp measurable_fst).prodMk measurable_snd
    have hb := measurable_branchMean D P t ht hdR H hBH πL π upperBid hupperBid hfloor
      N hrare A H0 H1 side low j v price reg
    have hh := hb.comp hin
    exact hh
  have hb (reg x) : ‖ff reg x‖≤|v|+D.V :=
    branchMean_bound D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare A H0 H1 side low j v price reg _ _
  rw [integral_finite_expect_two (IndependentCounts.bernoulli (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor).θ (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor).θ_nonneg (publicData D P t ht hdR H hBH πL π upperBid hupperBid hfloor).θ_le_one) (Measure.pi (fun _ : Fin A => (volume : Measure unitInterval))) (ProbabilityMeasure.toMeasure (originalIid (regions D P hdR H hBH) (ownH H0 H1 side).val (NoisyNativeFiberProduct.privateRowLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor))) ff hf (|v|+D.V) hb]
  have hu (reg : Bool) :
      (∫ commonNoise : Fin A→ unitInterval,∫ row,ff reg (commonNoise,row) ∂(ProbabilityMeasure.toMeasure (originalIid (regions D P hdR H hBH) (ownH H0 H1 side).val (NoisyNativeFiberProduct.privateRowLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor))) ∂(Measure.pi (fun _ : Fin A => (volume : Measure unitInterval))))=
        (installOriginal D P t ht).partialFiber A H0.val H1.val side low reg j ((v,price,(partialBidLaw D P t ht π)),base) := by
    have h := UnequalPartialOriginalIntegral.utility_eq_original_integral A H0.val H1.val D.c
      D.width (D.e0 reg) D.F side reg low ((installOriginal D P t ht).marksLaw H0.val) ((installOriginal D P t ht).marksLaw H1.val) (ProbabilityMeasure.toMeasure (originalIid (regions D P hdR H hBH) (ownH H0 H1 side).val (NoisyNativeFiberProduct.privateRowLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor)))
      ⟨D.hξ.le,D.hξ1.le⟩ D.hR D.heps ((regions D P hdR H hBH).R_le_Rp.trans (regions D P hdR H hBH).Rp_lt_H.le) D.hRp D.hgap (regions D P hdR H hBH).Rp_lt_H
      j price v base
    erw [rawSignalLaw_eq D P t ht hdR H hBH πL π upperBid hupperBid hfloor (ownH H0 H1 side).val] at h
    simpa only [ff,branchMean,branch,UnequalPartialOriginalIntegral.originalUtility,
      EqualNoisyUtilities.physical,CompactSourceBidLaws.noisyBid,
      AllNoiseFiniteSelector.noisyBids,FiniteTailNoisyGame.Data.partialFiber,dif_neg hnat] using! h.symm
  simp_rw [hu]
  rw [IndependentCounts.expect_bernoulli]
  rfl

theorem originalIntegral_equal (h : H0=H1) (base : Fin A→ Icc (1:ℝ) D.U) :
    originalIntegral D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare
      A H0 H1 side low j v price base=
      (installOriginal D P t ht).partialRegimeFiber A H0.val H1.val side low j ((v,price,(partialBidLaw D P t ht π)),base) := by
  subst H1
  have hBayes := bayesLaw_eq D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare H0
  have mixIdentity (z s : ℝ) : z=(1-s)*z+s*z := by ring
  cases side
  all_goals
    have h := EqualPartialOriginalIntegral.utility_eq_original_integral (c:=D.c)
      ⟨D.hξ.le,D.hξ1.le⟩ D.hR D.heps ((regions D P hdR H hBH).Rp_lt_one.le.trans (regions D P hdR H hBH).one_le_U) hBH
      (((by norm_num : (0:ℝ)<1).trans_le (regions D P hdR H hBH).one_le_U).trans hBH)
      base ((installOriginal D P t ht).privateBayes H0.val (partialBidLaw D P t ht π)) (ProbabilityMeasure.toMeasure (originalIid (regions D P hdR H hBH) H0.val (NoisyNativeFiberProduct.privateRowLaw D P t ht hdR H hBH πL π upperBid hupperBid hfloor))) j price
      (fun _ _ _ => Equiv.refl _) v
    erw [rawSignalLaw_eq D P t ht hdR H hBH πL π upperBid hupperBid hfloor H0.val] at h
    have hi : originalIntegral D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare
        A H0 H0 _ low j v price base=
      EqualNoisyUtilities.privateUtility (c:=D.c) D.hR D.heps.le D.ξ j
        (v,((base,(installOriginal D P t ht).privateBayes H0.val (partialBidLaw D P t ht π)),price,(installOriginal D P t ht).privateFocalRow H0.val (partialBidLaw D P t ht π))) := by
      erw [h]
      unfold originalIntegral
      apply integral_congr_ae
      refine ae_of_all _ fun commonNoise => ?_
      apply integral_congr_ae
      refine ae_of_all _ fun row => ?_
      apply integral_congr_ae
      refine ae_of_all _ fun a => ?_
      simp only [noisyValue,value,NativePartialExperiment.inclusion,sampler,
        (localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).zeroSampler_equal,(localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare).oneSampler_equal,Data.equalSampler,AllCountHighPolicy.equalSample,
        JoinedHighPolicy.equalParameter,publicParameter,JoinedPartialPublicIntegral.parameters,hBayes,
        EqualPartialOriginalIntegral.samplerValue,EqualNoisyUtilities.parameter,
        Equiv.refl_symm,Equiv.refl_apply,noisyPrice,
        AtypicalPartialNoisy.noisyRow,integral_const,probReal_univ,one_smul]
      rfl
    rw [hi]
    simp [FiniteTailNoisyGame.Data.partialRegimeFiber,FiniteTailNoisyGame.Data.partialFiber]
    exact mixIdentity _ _

theorem originalIntegral_eq (base : Fin A→ Icc (1:ℝ) D.U) :
    originalIntegral D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare
      A H0 H1 side low j v price base=
      (installOriginal D P t ht).partialRegimeFiber A H0.val H1.val side low j ((v,price,(partialBidLaw D P t ht π)),base) := by
  by_cases h : H0=H1
  · exact originalIntegral_equal D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare
      A H0 H1 side low j v price h base
  · exact originalIntegral_unequal D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare
      A H0 H1 side low j v price h base

end FCAppendix.Affine.Tail04.NativePartialC1Integral
