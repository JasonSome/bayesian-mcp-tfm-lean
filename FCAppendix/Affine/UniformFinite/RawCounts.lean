import FCAppendix.Affine.UniformFinite.NumericInterims
import FCAppendix.Affine.UniformFinite.ActualSurplus
import FCAppendix.Affine.UniformFinite.LocalInformation

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory
open Existence.Distributional

lemma firstCopy_bounds {M : ℕ} (a : Fin M) (P : Allocation M) :
    Literal.firstCopy a P∈Icc (0:ℝ) 1 := by
  by_cases h0 : a∈P.1 <;> by_cases h1 : a∈P.2 <;>
    simp [Literal.firstCopy,WeightedSampling.indicator,h0,h1]

lemma duplicateCopy_bounds {M : ℕ} (a : Fin M) (P : Allocation M) :
    Literal.duplicateCopy a P∈Icc (0:ℝ) (Literal.firstCopy a P) := by
  by_cases h0 : a∈P.1 <;> by_cases h1 : a∈P.2 <;>
    simp [Literal.firstCopy,Literal.duplicateCopy,WeightedSampling.indicator,h0,h1]

lemma successProbability_bounds {M : ℕ} [NeZero M] (i : Row)
    (G : Uniform05.RestrictedLaw i) (row : Source.CountRow M)
    (b : Fin M→ℝ) (a : Fin M) : successProbability i G row b a∈Icc (0:ℝ) 1 :=
  ⟨FiniteLaw.expect_nonneg _ (fun P=>(firstCopy_bounds a P).1),
    FiniteLaw.expect_le_const _ (fun P=>(firstCopy_bounds a P).2)⟩

lemma row_value_difference {M : ℕ} [NeZero M] (i : Row)
    (G : Uniform05.RestrictedLaw i) (row : Source.CountRow M)
    (b : Fin M→ℝ) (a : Fin M) (v w : ℝ) :
    rowPayoff i G row v b a-rowPayoff i G row w b a=
      (v-w)*successProbability i G row b a := by
  rw [rowPayoff_success_duplicate,rowPayoff_success_duplicate]
  ring

def rawSuccess (i : Row) (N : ℕ) (G : Uniform05.RestrictedLaw i) (own : ℝ) : ℝ :=
  (categoryRowLaw i N).expect (fun kind=>
    ∫b : Fin N→ Bid i,successProbability i G (focalRow kind)
      (focalBids i kind own b) 0 ∂(rowLaw N G.bidLaw : Measure (Fin N→ Bid i)))

def rawDuplicate (i : Row) (N : ℕ) (G : Uniform05.RestrictedLaw i) (own : ℝ) : ℝ :=
  (categoryRowLaw i N).expect (fun kind=>
    ∫b : Fin N→ Bid i,duplicateProbability i G (focalRow kind)
      (focalBids i kind own b) 0 ∂(rowLaw N G.bidLaw : Measure (Fin N→ Bid i)))

def routeIndicator {M : ℕ} (j : Fin 2) (a : Fin M) (P : Allocation M) : ℝ :=
  if j=0 then WeightedSampling.indicator a P.1 else WeightedSampling.indicator a P.2

def rowRoutePayoff {M : ℕ} [NeZero M] (i : Row)
    (G : Uniform05.RestrictedLaw i) (row : Source.CountRow M)
    (j : Fin 2) (v : ℝ) (b : Fin M→ℝ) (a : Fin M) : ℝ :=
  (continuationLaw i G row b).expect (fun P=>(v-b a)*routeIndicator j a P)

def rawRouteUtility (i : Row) (N : ℕ) (G : Uniform05.RestrictedLaw i)
    (j : Fin 2) (v own : ℝ) : ℝ :=
  (categoryRowLaw i N).expect (fun kind=>
    ∫b : Fin N→ Bid i,rowRoutePayoff i G (focalRow kind) j v
      (focalBids i kind own b) 0 ∂(rowLaw N G.bidLaw : Measure (Fin N→ Bid i)))

def oneRouteRawUtility (i : Row) (N : ℕ) (G : Uniform05.RestrictedLaw i)
    (v own : ℝ) : ℝ :=
  (rawRouteUtility i N G 0 v own+rawRouteUtility i N G 1 v own)/2

lemma measurable_raw_row (i : Row) (N : ℕ) (G : Uniform05.RestrictedLaw i)
    (kind : Fin N→ Fin 3) (v : ℝ) (own : Bid i) :
    Measurable (fun b : Fin N→ Bid i=> rowPayoff i G (focalRow kind) v
      (focalBids i kind own b) 0) := by
  have hb := (ActualSurplus.continuous_cappedFocalBids i kind).measurable.comp
    ((measurable_const (a := own)).prodMk measurable_id)
  have hs := (SourceContinuity.measurable_fixedLawState i G).comp hb
  have hm := (SourceContinuity.measurable_rowPayoff i (focalRow kind) 0
    (ActualSurplus.focalRow_focal_mem kind)).comp
      ((measurable_const (a := v)).prodMk hs)
  have he (b : Fin N→Bid i) : SourceContinuity.bids i
      (SourceContinuity.fixedLawState i G (ActualSurplus.cappedFocalBids i kind own b)) =
      focalBids i kind own b := ActualSurplus.cappedFocalBids_val i kind own b
  change Measurable (fun b : Fin N→Bid i=>rowPayoff i G (focalRow kind) v
    (SourceContinuity.bids i
      (SourceContinuity.fixedLawState i G (ActualSurplus.cappedFocalBids i kind own b))) 0) at hm
  simpa only [he] using hm

lemma integrable_raw_row (i : Row) (N : ℕ) (G : Uniform05.RestrictedLaw i)
    (kind : Fin N→ Fin 3) (v : ℝ) (own : Bid i) :
    Integrable (fun b : Fin N→ Bid i=> rowPayoff i G (focalRow kind) v
      (focalBids i kind own b) 0) (rowLaw N G.bidLaw : Measure (Fin N→ Bid i)) :=
  Integrable.of_bound (measurable_raw_row i N G kind v own).aestronglyMeasurable
    (|v|+(1+|Uniform05.eta i|)*|(own:ℝ)|) (ae_of_all _ (fun b=> by
      simpa only [Real.norm_eq_abs,focalBids_zero] using
        rowPayoff_bound i G (focalRow kind) v (focalBids i kind own b) 0))

lemma measurable_raw_success_row (i : Row) (N : ℕ) (G : Uniform05.RestrictedLaw i)
    (kind : Fin N→ Fin 3) (own : Bid i) :
    Measurable (fun b : Fin N→ Bid i=> successProbability i G (focalRow kind)
      (focalBids i kind own b) 0) := by
  have hh := (measurable_raw_row i N G kind 1 own).sub
    (measurable_raw_row i N G kind 0 own)
  change Measurable (fun b : Fin N→Bid i=>
    rowPayoff i G (focalRow kind) 1 (focalBids i kind own b) 0-
    rowPayoff i G (focalRow kind) 0 (focalBids i kind own b) 0) at hh
  simpa only [row_value_difference,sub_zero,one_mul] using hh

lemma integrable_raw_success_row (i : Row) (N : ℕ) (G : Uniform05.RestrictedLaw i)
    (kind : Fin N→ Fin 3) (own : Bid i) :
    Integrable (fun b : Fin N→ Bid i=> successProbability i G (focalRow kind)
      (focalBids i kind own b) 0) (rowLaw N G.bidLaw : Measure (Fin N→ Bid i)) :=
  Integrable.of_bound (measurable_raw_success_row i N G kind own).aestronglyMeasurable 1
    (ae_of_all _ (fun b=> by
      have h:=successProbability_bounds i G (focalRow kind) (focalBids i kind own b) 0
      simpa only [Real.norm_eq_abs,abs_of_nonneg h.1] using h.2))

theorem raw_value_difference (i : Row) (N : ℕ) (G : Uniform05.RestrictedLaw i)
    (own : Bid i) (v w : ℝ) :
    rawUtility i N G v own-rawUtility i N G w own=(v-w)*rawSuccess i N G own := by
  unfold rawUtility rawSuccess
  rw [← FiniteLaw.expect_sub,← FiniteLaw.expect_const_mul]
  apply FiniteLaw.expect_congr
  intro kind
  rw [← integral_sub (integrable_raw_row i N G kind v own)
    (integrable_raw_row i N G kind w own)]
  simp only [row_value_difference]
  rw [integral_const_mul]

theorem rawSuccess_bounds (i : Row) (N : ℕ) (G : Uniform05.RestrictedLaw i)
    (own : Bid i) : rawSuccess i N G own∈Icc (0:ℝ) 1 := by
  constructor
  · apply FiniteLaw.expect_nonneg
    intro kind
    exact integral_nonneg (fun b=>(successProbability_bounds i G (focalRow kind)
      (focalBids i kind own b) 0).1)
  · apply FiniteLaw.expect_le_const
    intro kind
    calc
      _ ≤ ∫_ : Fin N→ Bid i,(1:ℝ) ∂(rowLaw N G.bidLaw : Measure (Fin N→ Bid i)) :=
        integral_mono (integrable_raw_success_row i N G kind own) (integrable_const 1)
          (fun b=>(successProbability_bounds i G (focalRow kind) (focalBids i kind own b) 0).2)
      _ = 1 := by simp

lemma routeIndicator_le_first {M : ℕ} (j : Fin 2) (a : Fin M) (P : Allocation M) :
    routeIndicator j a P∈Icc (0:ℝ) (Literal.firstCopy a P) := by
  by_cases hj : j=0 <;> by_cases h0 : a∈P.1 <;> by_cases h1 : a∈P.2 <;>
    simp [routeIndicator,Literal.firstCopy,WeightedSampling.indicator,hj,h0,h1]

lemma rowRoutePayoff_le_success {M : ℕ} [NeZero M] (i : Row)
    (G : Uniform05.RestrictedLaw i) (row : Source.CountRow M)
    (j : Fin 2) (v T : ℝ) (b : Fin M→ℝ) (a : Fin M)
    (hT : 0≤ T) (hv : v≤ T) (hb : 0≤ b a) :
    rowRoutePayoff i G row j v b a≤ T*successProbability i G row b a := by
  rw [rowRoutePayoff,successProbability,← FiniteLaw.expect_const_mul]
  apply FiniteLaw.expect_mono
  intro P
  have h:=routeIndicator_le_first j a P
  calc
    (v-b a)*routeIndicator j a P≤ T*routeIndicator j a P :=
      mul_le_mul_of_nonneg_right (by linarith) h.1
    _≤ T*Literal.firstCopy a P := mul_le_mul_of_nonneg_left h.2 hT

lemma integral_le_integrable_nonneg {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g : X→ℝ) (hg : Integrable g μ)
    (hg0 : ∀x,0≤ g x) (hle : ∀x,f x≤ g x) : (∫x,f x ∂μ)≤∫x,g x ∂μ := by
  by_cases hf : Integrable f μ
  · exact integral_mono hf hg hle
  · rw [integral_undef hf]
    exact integral_nonneg hg0

theorem rawRouteUtility_le_success (i : Row) (N : ℕ) (G : Uniform05.RestrictedLaw i)
    (j : Fin 2) (v : ℝ) (own : Bid i) (hv : v≤ Uniform05.t i) :
    rawRouteUtility i N G j v own≤ Uniform05.t i*rawSuccess i N G own := by
  unfold rawRouteUtility rawSuccess
  rw [← FiniteLaw.expect_const_mul]
  apply FiniteLaw.expect_mono
  intro kind
  rw [← integral_const_mul]
  exact integral_le_integrable_nonneg _ _ _
    ((integrable_raw_success_row i N G kind own).const_mul _)
    (fun b=> mul_nonneg (Uniform05.t_pos i).le
      (successProbability_bounds i G (focalRow kind) (focalBids i kind own b) 0).1)
    (fun b=> rowRoutePayoff_le_success i G (focalRow kind) j v (Uniform05.t i)
      (focalBids i kind own b) 0 (Uniform05.t_pos i).le hv
      (by simpa only [focalBids_zero] using own.property.1))

theorem oneRouteRawUtility_le_success (i : Row) (N : ℕ) (G : Uniform05.RestrictedLaw i)
    (v : ℝ) (own : Bid i) (hv : v≤ Uniform05.t i) :
    oneRouteRawUtility i N G v own≤ Uniform05.t i*rawSuccess i N G own := by
  have h0:=rawRouteUtility_le_success i N G 0 v own hv
  have h1:=rawRouteUtility_le_success i N G 1 v own hv
  unfold oneRouteRawUtility
  linarith

end FCAppendix.Affine.UniformFinite
