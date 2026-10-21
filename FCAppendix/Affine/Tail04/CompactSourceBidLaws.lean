import FCAppendix.Affine.Tail04.SortedPrivateMarks
import FCAppendix.Existence.R01CompactProduct
import FCAppendix.Affine.Hybrid.ActiveNoisyCompactLimit

noncomputable section
namespace FCAppendix.Affine.Tail04.CompactSourceBidLaws
open MeasureTheory ProbabilityTheory Set Classical
open Existence.Distributional EqualPrivateSignal
open scoped BigOperators

section Mixture
variable {X : Type*} [MeasurableSpace X]

def mixture (p : unitInterval) (μ ν : ProbabilityMeasure X) : ProbabilityMeasure X := by
  refine ⟨ENNReal.ofReal (p:ℝ) • (μ : Measure X)+
    ENNReal.ofReal (1-(p:ℝ)) • (ν : Measure X),?_⟩
  constructor
  simp only [Measure.add_apply,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
  rw [←ENNReal.ofReal_add p.2.1 (sub_nonneg.mpr p.2.2)]
  norm_num

lemma integral_mixture (p : unitInterval) (μ ν : ProbabilityMeasure X)
    (f : X → ℝ) (hμ : Integrable f (μ : Measure X)) (hν : Integrable f (ν : Measure X)) :
    (∫ x,f x ∂(mixture p μ ν : Measure X))=
      (p:ℝ)*(∫ x,f x ∂(μ : Measure X))+(1-(p:ℝ))*(∫ x,f x ∂(ν : Measure X)) := by
  change (∫ x,f x ∂(ENNReal.ofReal (p:ℝ) • (μ : Measure X)+
    ENNReal.ofReal (1-(p:ℝ)) • (ν : Measure X)))=_
  rw [integral_add_measure (hμ.smul_measure ENNReal.ofReal_ne_top)
    (hν.smul_measure ENNReal.ofReal_ne_top),integral_smul_measure,integral_smul_measure,
    ENNReal.toReal_ofReal p.2.1,ENNReal.toReal_ofReal (sub_nonneg.mpr p.2.2)]
  simp only [smul_eq_mul]

variable [TopologicalSpace X] [BorelSpace X] [CompactSpace X]

theorem continuous_mixture (p : unitInterval) :
    Continuous (fun q : ProbabilityMeasure X×ProbabilityMeasure X => mixture p q.1 q.2) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuousMap_continuous_integral.mpr
  intro f
  have hi (μ : ProbabilityMeasure X) : Integrable (fun x => f x) (μ : Measure X) :=
    (ContinuousMap.equivBoundedOfCompact _ _ f).integrable _
  simp_rw [integral_mixture p _ _ f (hi _) (hi _)]
  exact (continuous_const.mul ((ProbabilityMeasure.continuous_integral_continuousMap f).comp
    continuous_fst)).add (continuous_const.mul
      ((ProbabilityMeasure.continuous_integral_continuousMap f).comp continuous_snd))
end Mixture

def uniformLaw : ProbabilityMeasure unitInterval := ⟨volume,inferInstance⟩

def bidMarginal {T A : Type*} [TopologicalSpace T] [MeasurableSpace T]
    [TopologicalSpace A] [MeasurableSpace A] [BorelSpace T] [BorelSpace A]
    (μ : ProbabilityMeasure (T×A)) : ProbabilityMeasure A := μ.map measurable_snd.aemeasurable

theorem continuous_bidMarginal {T A : Type*} [TopologicalSpace T] [MeasurableSpace T]
    [TopologicalSpace A] [MeasurableSpace A] [BorelSpace T] [BorelSpace A]
    [OpensMeasurableSpace (T × A)] :
    Continuous (bidMarginal (T:=T) (A:=A)) := ProbabilityMeasure.continuous_map continuous_snd

def extendBid {L U V : ℝ} (hUV : U≤ V) (b : Icc L U) : Icc L V :=
  ⟨b.1,b.2.1,b.2.2.trans hUV⟩
lemma continuous_extendBid {L U V : ℝ} (hUV : U≤ V) : Continuous (extendBid (L:=L) hUV) :=
  continuous_subtype_val.subtype_mk _

def activeBaseLaw {u U : ℝ} (huU : 1+u≤ U) (bulkShare : unitInterval)
    (μB : ProbabilityMeasure (Icc (1:ℝ) (1+u))) (μT : ProbabilityMeasure (Icc (1:ℝ) U)) :
    ProbabilityMeasure (Icc (1:ℝ) U) :=
  mixture bulkShare (μB.map (continuous_extendBid huU).measurable.aemeasurable) μT

theorem continuous_activeBaseLaw {u U : ℝ} (huU : 1+u≤ U) (bulkShare : unitInterval) :
    Continuous (fun p : ProbabilityMeasure (Icc (1:ℝ) (1+u))×ProbabilityMeasure (Icc (1:ℝ) U) =>
      activeBaseLaw huU bulkShare p.1 p.2) :=
  (continuous_mixture bulkShare).comp
    (((ProbabilityMeasure.continuous_map (continuous_extendBid huU)).comp continuous_fst).prodMk continuous_snd)

def noisyBid {L U eps : ℝ} (hL : 0< L) (heps : 0≤ eps)
    (p : Icc L U×unitInterval) : Icc L (U*(1+eps)) :=
  ⟨Hybrid.activeNoisyRealBid eps p.1 p.2,Hybrid.activeNoisyRealBid_mem hL heps p.1 p.2⟩

lemma continuous_noisyBid {L U eps : ℝ} (hL : 0< L) (heps : 0≤ eps) :
    Continuous (noisyBid (U:=U) hL heps) := by
  apply Continuous.subtype_mk
  unfold Hybrid.activeNoisyRealBid
  fun_prop

def noisyBidLaw {L U eps : ℝ} (hL : 0< L) (heps : 0≤ eps)
    (μ : ProbabilityMeasure (Icc L U)) : ProbabilityMeasure (Icc L (U*(1+eps))) :=
  (productLaw μ uniformLaw).map (continuous_noisyBid hL heps).measurable.aemeasurable

theorem continuous_noisyBidLaw {L U eps : ℝ} (hL : 0< L) (heps : 0≤ eps) :
    Continuous (noisyBidLaw (U:=U) hL heps) :=
  (ProbabilityMeasure.continuous_map (continuous_noisyBid hL heps)).comp
    (continuous_productLaw.comp (continuous_id.prodMk continuous_const))

def privateEntryLaw {R U eps : ℝ} (hR : 0< R) (heps : 0≤ eps) (upperShare : unitInterval)
    (μP : ProbabilityMeasure (Icc R U)) : ProbabilityMeasure (Unit⊕Icc R (U*(1+eps))) :=
  mixture upperShare ⟨Measure.dirac (Sum.inl ()),Measure.dirac.isProbabilityMeasure⟩
    ((noisyBidLaw hR heps μP).map continuous_inr.measurable.aemeasurable)

theorem continuous_privateEntryLaw {R U eps : ℝ} (hR : 0< R) (heps : 0≤ eps)
    (upperShare : unitInterval) : Continuous (privateEntryLaw (U:=U) hR heps upperShare) :=
  (continuous_mixture upperShare).comp (continuous_const.prodMk
    ((ProbabilityMeasure.continuous_map continuous_inr).comp (continuous_noisyBidLaw hR heps)))

def rawPrivateRow {R U eps : ℝ} (hR : 0< R) (heps : 0≤ eps) (upperShare : unitInterval)
    (H : ℕ) (μP : ProbabilityMeasure (Icc R U)) : ProbabilityMeasure (Signal H R (U*(1+eps))) :=
  rowLaw H (privateEntryLaw hR heps upperShare μP)

theorem continuous_rawPrivateRow {R U eps : ℝ} (hR : 0< R) (heps : 0≤ eps)
    (upperShare : unitInterval) (H : ℕ) : Continuous (rawPrivateRow (U:=U) hR heps upperShare H) :=
  (continuous_rowLaw H).comp (continuous_privateEntryLaw hR heps upperShare)

def rowCast {R V W : ℝ} (hVW : W=V) (H : ℕ) (t : Signal H R V) : Signal H R W :=
  fun i => Sum.map id (fun b : Icc R V =>
    (⟨b.1,b.2.1,by rw [hVW];exact b.2.2⟩ : Icc R W)) (t i)

lemma continuous_rowCast {R V W : ℝ} (hVW : W=V) (H : ℕ) :
    Continuous (rowCast (R:=R) hVW H) := by
  subst W
  have he : rowCast (R:=R) (V:=V) (W:=V) rfl H=id := by
    funext t i
    cases ht : t i <;> simp [rowCast, ht]
  rw [he]
  exact continuous_id

def privateBayesLaw (E : Observable.Regions) {U eps : ℝ}
    (hR : 0< E.R) (heps : 0≤ eps) (hEV : E.Rp=U*(1+eps))
    (upperShare : unitInterval) (H : ℕ) (μP : ProbabilityMeasure (Icc E.R U)) :
    ProbabilityMeasure (Signal H E.R E.Rp) :=
  (rawPrivateRow hR heps upperShare H μP).map
    ((PrivateRowSorting.continuous_sortSignal E H).comp
      (continuous_rowCast hEV H)).measurable.aemeasurable

theorem continuous_privateBayesLaw (E : Observable.Regions) {U eps : ℝ}
    (hR : 0< E.R) (heps : 0≤ eps) (hEV : E.Rp=U*(1+eps))
    (upperShare : unitInterval) (H : ℕ) :
    Continuous (privateBayesLaw E hR heps hEV upperShare H) :=
  (ProbabilityMeasure.continuous_map ((PrivateRowSorting.continuous_sortSignal E H).comp
    (continuous_rowCast hEV H))).comp (continuous_rawPrivateRow hR heps upperShare H)

end FCAppendix.Affine.Tail04.CompactSourceBidLaws
