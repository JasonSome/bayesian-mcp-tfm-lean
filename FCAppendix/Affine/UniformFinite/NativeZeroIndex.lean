import FCAppendix.Affine.UniformFinite.NativeIndexedSource

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology Classical Game Bayes
open Existence.Distributional
open Uniform05 SourceContinuity
open scoped BigOperators

namespace NativeProfile
variable {N : ℕ}

lemma numericFocal_draw (i : Row) (G : RestrictedLaw i) (own : Bid i)
    (kind : Fin N→ Fin 3) (b : Fin N→ Bid i) (s : unitInterval×unitInterval) :
    draw i G (Fin.cons (Sum.inl own) (encodeCategoryRow i N (kind,b))) s=
      NativeCounts.rowDraw i G own kind b s := by
  have hr : numericRow i (Fin.cons (Sum.inl own) (encodeCategoryRow i N (kind,b)))=
      focalRow kind := by
    change Source.countRowOfKind (fun a=>numericKind i
      ((Fin.cons (Sum.inl own) (encodeCategoryRow i N (kind,b)) : Fin (N+1)→NumericObservation i) a))=
        Source.countRowOfKind (Fin.cons 0 kind)
    apply congrArg Source.countRowOfKind
    funext a
    refine Fin.cases ?_ (fun j=>?_) a
    · rfl
    · simp [encodeCategoryRow]
  have hb : numericBids i (Fin.cons (Sum.inl own) (encodeCategoryRow i N (kind,b)))=
      Noisy.cappedFocalBids i kind own b := by
    funext a
    refine Fin.cases ?_ (fun j=>?_) a
    · rfl
    · by_cases hj : kind j=0 <;>
        simp [numericBids,numericCapped,encodeCategoryRow,encodeCategory,
          Noisy.cappedFocalBids,hj]
      split_ifs <;> rfl
  simp only [draw,hr,hb,NativeCounts.rowDraw]

lemma insert_zero (i : Row) (own : Bid i) (z : Fin (N+1)→ NumericObservation i) :
    insert 0 own z=Fin.cons (Sum.inl own) (fun j : Fin N=> z j.succ) := by
  funext a
  refine Fin.cases ?_ (fun j=>?_) a <;> simp [insert]

lemma measurable_numericFocal (i : Row) (own : Bid i) :
    Measurable (fun z : Fin N→ NumericObservation i=>
      (Fin.cons (Sum.inl own) z : Fin (N+1)→NumericObservation i)) := by
  apply measurable_pi_lambda
  intro a
  refine Fin.cases ?_ (fun j=>?_) a
  · exact measurable_const
  · exact measurable_pi_apply j

def focalCountTest (i : Row) (G : RestrictedLaw i) (own : Bid i) (f : Fin 3→ℝ)
    (z : Fin N→ NumericObservation i) : ℝ :=
  ∫s,f (pairCount 0 (draw i G (Fin.cons (Sum.inl own) z) s))
    ∂((volume : Measure unitInterval).prod volume)

lemma measurable_focalCountTest (i : Row) (G : RestrictedLaw i) (own : Bid i)
    (f : Fin 3→ℝ) : Measurable (focalCountTest (N:=N) i G own f) := by
  have h:=((measurable_of_countable (fun P : Allocation (N+1)=> f (pairCount 0 P))).comp
    ((measurable_draw i G).comp (((measurable_numericFocal i own).comp measurable_fst).prodMk
      measurable_snd)))
  convert! h.stronglyMeasurable.integral_prod_right'.measurable using 1
  infer_instance

lemma focalCountTest_bound (i : Row) (G : RestrictedLaw i) (own : Bid i)
    (f : Fin 3→ℝ) (z : Fin N→ NumericObservation i) :
    |focalCountTest i G own f z|≤∑r,|f r| := by
  have hb (privateSeed : unitInterval×unitInterval) :
      |f (pairCount 0 (draw i G (Fin.cons (Sum.inl own) z) privateSeed))|≤∑r,|f r| :=
    Finset.single_le_sum (s:=Finset.univ) (f:=fun r : Fin 3=>|f r|)
      (fun r _=>abs_nonneg (f r)) (Finset.mem_univ _)
  simpa only [focalCountTest,Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (f:=fun privateSeed : unitInterval×unitInterval=>
      f (pairCount 0 (draw i G (Fin.cons (Sum.inl own) z) privateSeed)))
      (ae_of_all ((volume : Measure unitInterval).prod volume)
        (fun privateSeed=> by simpa only [Real.norm_eq_abs] using hb privateSeed))

theorem indexedLaw_zero (i : Row) (G : RestrictedLaw i)
    [NullSingletonClass (G.bidLaw : Measure (Bid i))] (own : Bid i) :
    indexedLaw i G (0 : Fin (N+1)) own=rawCountLaw i N G own := by
  let μ:=numericObservationLaw i G
  let tail : (Fin (N+1)→ NumericObservation i)→(Fin N→ NumericObservation i):=
    fun z j=> z j.succ
  have htail : MeasurePreserving tail (Measure.pi (fun _ : Fin (N+1)=>μ))
      (Measure.pi (fun _ : Fin N=>μ)) :=
    (measurePreserving_snd (μ:=μ) (ν:=Measure.pi (fun _ : Fin N=>μ))).comp
      (measurePreserving_piFinSuccAbove (fun _ : Fin (N+1)=>μ) 0)
  apply FiniteLaw.ext_expect
  intro f
  have hm:=measurable_focalCountTest (N:=N) i G own f
  have hi : Integrable (fun p=> focalCountTest i G own f (encodeCategoryRow i N p))
      ((FiniteLaw.probabilityMeasure (categoryRowLaw i N)).prod
        (rowLaw N G.bidLaw : Measure (Fin N→ Bid i))) :=
    Integrable.of_bound (hm.comp (measurable_encodeCategoryRow i N)).aestronglyMeasurable
      (∑r,|f r|) (ae_of_all _ (fun p=> by
        simpa only [Real.norm_eq_abs] using focalCountTest_bound i G own f _))
  rw [indexedLaw_expect,rawCountLaw_expect]
  simp_rw [count,insert_zero]
  change (∫z,focalCountTest i G own f (tail z) ∂Measure.pi (fun _ : Fin (N+1)=>μ))=_
  calc
    _=∫z,focalCountTest i G own f z ∂Measure.pi (fun _ : Fin N=>μ) := by
      rw [← htail.map_eq]
      exact (integral_map htail.measurable.aemeasurable hm.aestronglyMeasurable).symm
    _=_ := by
      rw [show μ=numericObservationLaw i G from rfl,← encodeCategoryRow_law i G N,
        integral_map (measurable_encodeCategoryRow i N).aemeasurable hm.aestronglyMeasurable,
        integral_prod _ hi,LowBody.integral_probabilityMeasure]
      apply FiniteLaw.expect_congr
      intro kind
      simpa only [focalCountTest,numericFocal_draw] using
        NativeCounts.row_count_integral i G own kind f

end NativeProfile

namespace NativeIndexed

theorem utility_zero (i : Row) (N : ℕ) (G : RestrictedLaw i)
    [NullSingletonClass (G.bidLaw : Measure (Bid i))] (v : ℝ) (own : Bid i) :
    utility i G (0 : Fin (N+1)) v own=rawUtility i N G v own := by
  rw [utility,NativeProfile.indexedLaw_zero,rawCountLaw_utility]

end NativeIndexed
end FCAppendix.Affine.UniformFinite
