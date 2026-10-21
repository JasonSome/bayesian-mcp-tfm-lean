import FCAppendix.Affine.UniformFinite.NativeRowLaw
import FCAppendix.Affine.UniformFinite.RawCounts
import FCAppendix.Probability.FiniteAveraging

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology Classical
open Existence.Distributional
open scoped BigOperators

theorem measurable_native_draw {M : ℕ} [NeZero M] (i : Row) (row : Source.CountRow M) :
    Measurable (fun x : SourceContinuity.State i M×NativeRow.Seeds=> NativeRow.draw i row x.1 x.2) := by
  convert! ((NativeRow.select_measurable i row 0).comp
    ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd.fst)).prodMk
      ((NativeRow.select_measurable i row 1).comp
        ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd.snd)) using 1

theorem measurable_continuation_expect {M : ℕ} [NeZero M] (i : Row)
    (row : Source.CountRow M) (f : Allocation M→ℝ) :
    Measurable (fun x : SourceContinuity.State i M=>
      (continuationLaw i x.1 row (SourceContinuity.bids i x)).expect f) := by
  simp_rw [← NativeRow.draw_integral i row _ f]
  exact ((measurable_of_countable f).comp (measurable_native_draw i row)).stronglyMeasurable.integral_prod_right'.measurable

theorem measurable_rowCount_mass {M : ℕ} [NeZero M] (i : Row)
    (row : Source.CountRow M) (a : Fin M) (k : Fin 3) :
    Measurable (fun x : SourceContinuity.State i M=>
      (rowCountLaw i x.1 row (SourceContinuity.bids i x) a).mass k) := by
  have h:=measurable_continuation_expect i row (fun P=> if pairCount a P=k then 1 else 0)
  have he (x : SourceContinuity.State i M) :
      (rowCountLaw i x.1 row (SourceContinuity.bids i x) a).mass k =
      (continuationLaw i x.1 row (SourceContinuity.bids i x)).expect
        (fun P=>if pairCount a P=k then 1 else 0) := by
    rw [← FiniteLaw.expect_singleton,rowCountLaw,FiniteLaw.expect_map]
  simpa only [he] using h

theorem measurable_rawCount_row_mass (i : Row) (N : ℕ) (G : Uniform05.RestrictedLaw i)
    (kind : Fin N→ Fin 3) (k : Fin 3) :
    Measurable (fun p : Bid i×(Fin N→ Bid i)=>
      (rowCountLaw i G (focalRow kind) (focalBids i kind p.1 p.2) 0).mass k) := by
  have h:=(measurable_rowCount_mass i (focalRow kind) 0 k).comp
    ((SourceContinuity.measurable_fixedLawState i G).comp
      (ActualSurplus.continuous_cappedFocalBids i kind).measurable)
  have he (p : Bid i×(Fin N→Bid i)) : SourceContinuity.bids i
      (SourceContinuity.fixedLawState i G (ActualSurplus.cappedFocalBids i kind p.1 p.2)) =
      focalBids i kind p.1 p.2 := ActualSurplus.cappedFocalBids_val i kind p.1 p.2
  change Measurable (fun p : Bid i×(Fin N→Bid i)=>
    (rowCountLaw i G (focalRow kind) (SourceContinuity.bids i
      (SourceContinuity.fixedLawState i G (ActualSurplus.cappedFocalBids i kind p.1 p.2))) 0).mass k) at h
  simpa only [he] using h

def rawCountLaw (i : Row) (N : ℕ) (G : Uniform05.RestrictedLaw i) (own : Bid i) : CountLaw 2 :=
  FiniteLaw.average (FiniteLaw.probabilityMeasure (categoryRowLaw i N))
    (fun kind=> FiniteLaw.average (rowLaw N G.bidLaw : Measure (Fin N→ Bid i))
      (fun b=> rowCountLaw i G (focalRow kind) (focalBids i kind own b) 0)
      (fun k=>by
        convert! (measurable_rawCount_row_mass i N G kind k).comp
          ((measurable_const (a := own)).prodMk measurable_id) using 1))
    (fun _=> measurable_of_countable _)

theorem rawCountLaw_expect (i : Row) (N : ℕ) (G : Uniform05.RestrictedLaw i)
    (own : Bid i) (f : Fin 3→ℝ) :
    (rawCountLaw i N G own).expect f=
      (categoryRowLaw i N).expect (fun kind=>
        ∫b : Fin N→ Bid i,(rowCountLaw i G (focalRow kind) (focalBids i kind own b) 0).expect f
          ∂(rowLaw N G.bidLaw : Measure (Fin N→ Bid i))) := by
  rw [rawCountLaw,FiniteLaw.expect_average,LowBody.integral_probabilityMeasure]
  apply FiniteLaw.expect_congr
  intro kind
  exact FiniteLaw.expect_average _ _ _ f

theorem measurable_rawCountLaw_mass (i : Row) (N : ℕ) (G : Uniform05.RestrictedLaw i)
    (k : Fin 3) : Measurable (fun b : Bid i=>(rawCountLaw i N G b).mass k) := by
  simp_rw [← FiniteLaw.expect_singleton,rawCountLaw_expect]
  apply Finset.measurable_sum
  intro kind _
  apply measurable_const.mul
  simpa only [FiniteLaw.expect_singleton] using
    (measurable_rawCount_row_mass i N G kind k).stronglyMeasurable.integral_prod_right'.measurable

lemma pairCount_success {M : ℕ} (a : Fin M) (P : Allocation M) :
    successIndicator (pairCount a P).val=Literal.firstCopy a P := by
  by_cases h0 : a∈P.1 <;> by_cases h1 : a∈P.2 <;>
    simp [pairCount,Literal.firstCopy,WeightedSampling.indicator,successIndicator,h0,h1]

lemma pairCount_duplicate {M : ℕ} (a : Fin M) (P : Allocation M) :
    ((pairCount a P).val:ℝ)-successIndicator (pairCount a P).val=Literal.duplicateCopy a P := by
  by_cases h0 : a∈P.1 <;> by_cases h1 : a∈P.2 <;>
    simp [pairCount,Literal.duplicateCopy,WeightedSampling.indicator,successIndicator,h0,h1]; norm_num

theorem rawCountLaw_success (i : Row) (N : ℕ) (G : Uniform05.RestrictedLaw i) (own : Bid i) :
    (rawCountLaw i N G own).success=rawSuccess i N G own := by
  rw [CountLaw.success,rawCountLaw_expect]
  simp only [rowCountLaw,FiniteLaw.expect_map,pairCount_success,rawSuccess,successProbability]

theorem rawCountLaw_duplicate (i : Row) (N : ℕ) (G : Uniform05.RestrictedLaw i) (own : Bid i) :
    (rawCountLaw i N G own).duplicates=rawDuplicate i N G own := by
  rw [CountLaw.duplicates_eq_expect,rawCountLaw_expect]
  simp only [rowCountLaw,FiniteLaw.expect_map,pairCount_duplicate,rawDuplicate,duplicateProbability]

lemma pairPayoff_as_count {M : ℕ} (i : Row) (v b : ℝ) (a : Fin M) (P : Allocation M) :
    pairPayoff (Uniform05.eta i) v b a P=
      userPayoff v b 0 (Schedule.affine 2 (Uniform05.eta i)
        (Uniform05.eta_range i).1.le (Uniform05.eta_range i).2.le).charge
        (Schedule.once 2).charge (pairCount a P).val := by
  by_cases h0 : a∈P.1 <;> by_cases h1 : a∈P.2 <;>
    simp [pairCount,pairPayoff,Literal.firstCopy,Literal.duplicateCopy,WeightedSampling.indicator,
      userPayoff,Schedule.affine,Schedule.once,successIndicator,h0,h1]; ring

theorem rawCountLaw_utility (i : Row) (N : ℕ) (G : Uniform05.RestrictedLaw i)
    (v : ℝ) (own : Bid i) :
    (rawCountLaw i N G own).utility v own 0
      (Schedule.affine 2 (Uniform05.eta i) (Uniform05.eta_range i).1.le (Uniform05.eta_range i).2.le)
      (Schedule.once 2)=rawUtility i N G v own := by
  rw [CountLaw.utility,rawCountLaw_expect]
  simp only [rowCountLaw,FiniteLaw.expect_map,← pairPayoff_as_count,focalBids_zero,
    rawUtility,rowPayoff]

def typeCountLaw (i : Row) (N : ℕ) (pi : Joint i)
    (sigma : Kernel (Value i) unitInterval) [IsMarkovKernel sigma] (v : Value i) : CountLaw 2 :=
  FiniteLaw.average (sigma v) (fun q=> rawCountLaw i N (restrictedLaw i (0,pi)) (baseBid i (v,q)))
    (fun k=>by
      convert! (measurable_rawCountLaw_mass i N (restrictedLaw i (0,pi)) k).comp
        ((continuous_baseBid i).comp ((continuous_const (y := v)).prodMk continuous_id)).measurable using 1)

theorem typeCountLaw_expect (i : Row) (N : ℕ) (pi : Joint i)
    (sigma : Kernel (Value i) unitInterval) [IsMarkovKernel sigma]
    (v : Value i) (f : Fin 3→ℝ) :
    (typeCountLaw i N pi sigma v).expect f=
      ∫q,(rawCountLaw i N (restrictedLaw i (0,pi)) (baseBid i (v,q))).expect f ∂sigma v :=
  FiniteLaw.expect_average _ _ _ f

theorem original_typeCountLaw_integral (i : Row) (N : ℕ) (pi : Joint i)
    (sigma : Kernel (Value i) unitInterval) [IsMarkovKernel sigma]
    (hsigma : lowerMeasure i⊗ₘsigma=(pi.1 : Measure (Value i×unitInterval)))
    (f : Fin 3→ℝ) :
    (∫v,(typeCountLaw i N pi sigma v).expect f ∂lowerMeasure i)=
      ∫p,(rawCountLaw i N (restrictedLaw i (0,pi)) (baseBid i p)).expect f
        ∂(pi.1 : Measure (Value i×unitInterval)) := by
  have hm (k : Fin 3) : Measurable (fun p : Value i×unitInterval=>
      (rawCountLaw i N (restrictedLaw i (0,pi)) (baseBid i p)).mass k) :=
    (measurable_rawCountLaw_mass i N (restrictedLaw i (0,pi)) k).comp
      (continuous_baseBid i).measurable
  have hi:=FiniteLaw.integrable_expect (lowerMeasure i⊗ₘsigma)
    (fun p=> rawCountLaw i N (restrictedLaw i (0,pi)) (baseBid i p)) hm f
  simp_rw [typeCountLaw_expect]
  rw [← Measure.integral_compProd hi,hsigma]

end FCAppendix.Affine.UniformFinite
