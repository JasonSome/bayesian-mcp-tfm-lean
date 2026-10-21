import FCAppendix.Affine.UniformFinite.Late.ExceptionalRelabel
import FCAppendix.Affine.UniformFinite.NativeIdentity

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine.UniformFinite.Late.ExceptionalIndexed
open Set MeasureTheory ProbabilityTheory Filter Topology Classical Game Bayes
open Existence.Distributional
open Uniform05 SourceContinuity
open scoped BigOperators
variable {M : ℕ}

abbrev fixedRow (a : Fin M) (kind : Fin M→ Fin 3) := NativeIndexed.fixedRow a kind

def coordinate (i : Row) (a : Fin M) (own : ℝ) (kind : Fin M→ Fin 3)
    (j : Fin M) (b : Bid i) : ℝ := if j=a then own else if kind j=0 then (b:ℝ) else 0

def fixedBids (i : Row) (a : Fin M) (own : ℝ) (kind : Fin M→ Fin 3)
    (b : Fin M→ Bid i) : Fin M→ℝ := fun j=> coordinate i a own kind j (b j)

@[simp] theorem fixedBids_self (i : Row) (a : Fin M) (own : ℝ)
    (kind : Fin M→ Fin 3) (b : Fin M→ Bid i) : fixedBids i a own kind b a=own := by
  simp [fixedBids,coordinate]

theorem measurable_coordinate (i : Row) (a : Fin M) (own : ℝ)
    (kind : Fin M→ Fin 3) (j : Fin M) : Measurable (coordinate i a own kind j) := by
  unfold coordinate
  split_ifs <;> first | exact measurable_const | exact measurable_subtype_coe

theorem continuous_fixedBids (i : Row) (a : Fin M) (kind : Fin M→ Fin 3) :
    Continuous (fun p : ℝ×(Fin M→ Bid i)=> fixedBids i a p.1 kind p.2) := by
  apply continuous_pi
  intro j
  unfold fixedBids coordinate
  split_ifs
  · exact continuous_fst
  · exact continuous_subtype_val.comp ((continuous_apply j).comp continuous_snd)
  · exact continuous_const

def coordinateLaw (i : Row) (G : RestrictedLaw i) (a : Fin M) (own : ℝ)
    (kind : Fin M→ Fin 3) (j : Fin M) : Measure ℝ :=
  (G.bidLaw : Measure (Bid i)).map (coordinate i a own kind j)

instance coordinateLaw_probability (i : Row) (G : RestrictedLaw i) (a : Fin M) (own : ℝ)
    (kind : Fin M→ Fin 3) (j : Fin M) : IsProbabilityMeasure (coordinateLaw i G a own kind j) :=
  Measure.isProbabilityMeasure_map (measurable_coordinate i a own kind j).aemeasurable

@[simp] theorem coordinateLaw_self (i : Row) (G : RestrictedLaw i) (a : Fin M)
    (own : ℝ) (kind : Fin M→ Fin 3) : coordinateLaw i G a own kind a=Measure.dirac own := by
  have hc : coordinate i a own kind a=(fun _ : Bid i=>own) := by
    funext b; simp [coordinate]
  simp only [coordinateLaw,hc,Measure.map_const,measure_univ,one_smul]

theorem coordinateLaw_lower (i : Row) (G : RestrictedLaw i) (a : Fin M) (own : ℝ)
    (kind : Fin M→ Fin 3) (j : Fin M) (hj : j∈(fixedRow a kind).lower) (hne : j≠a) :
    coordinateLaw i G a own kind j=ExceptionalSeed.bidMeasure i G := by
  have hk := (NativeIndexed.fixedRow_other a j kind hne).mp hj
  have hc : coordinate i a own kind j=(fun b : Bid i=>(b:ℝ)) := by
    funext b; simp only [coordinate,if_neg hne,if_pos hk]
  simp only [coordinateLaw,hc,ExceptionalSeed.bidMeasure]

theorem fixedBids_law (i : Row) (G : RestrictedLaw i) (a : Fin M) (own : ℝ)
    (kind : Fin M→ Fin 3) :
    (Measure.pi (fun _ : Fin M=>(G.bidLaw : Measure (Bid i)))).map (fixedBids i a own kind)=
      Measure.pi (coordinateLaw i G a own kind) :=
  Measure.pi_map_pi (fun j=>(measurable_coordinate i a own kind j).aemeasurable)

theorem encode_row (i : Row) (a : Fin M) (kind : Fin M→ Fin 3) (b : Fin M→ Bid i) :
    ExceptionalProfile.numericRow i a (encodeCategoryRow i M (kind,b))=fixedRow a kind :=
  NativeIndexed.encode_insert_row i a (Noisy.zeroBid i) kind b

theorem encode_bids (i : Row) (a : Fin M) (own : ℝ)
    (kind : Fin M→ Fin 3) (b : Fin M→ Bid i) :
    ExceptionalProfile.numericBids i a own (encodeCategoryRow i M (kind,b))=fixedBids i a own kind b := by
  funext j
  by_cases hj : j=a
  · subst j
    simp [ExceptionalProfile.numericBids,fixedBids,coordinate]
  · by_cases hk : kind j=0
    · simp [ExceptionalProfile.numericBids,fixedBids,coordinate,hj,hk,
        encodeCategoryRow,encodeCategory,numericBid]
    · by_cases hk1 : kind j=1 <;>
        simp [ExceptionalProfile.numericBids,fixedBids,coordinate,hj,hk,hk1,
          encodeCategoryRow,encodeCategory,numericBid]

variable [NeZero M]

theorem fixed_allocation_integral (i : Row) (G : RestrictedLaw i)
    [NullSingletonClass (G.bidLaw : Measure (Bid i))]
    (a : Fin M) (own : ℝ) (hown : cap i< own) (kind : Fin M→ Fin 3) (f : Allocation M→ℝ) :
    (∫b : Fin M→ Bid i,∫s,f (ExceptionalProfile.draw i G a own (encodeCategoryRow i M (kind,b)) s)
      ∂((volume : Measure unitInterval).prod volume)
      ∂(rowLaw M G.bidLaw : Measure (Fin M→ Bid i)))=
      ∫b : Fin M→ Bid i,(Exceptional.continuationLaw i G (fixedRow a kind)
        (fixedBids i a own kind b) a).expect f ∂(rowLaw M G.bidLaw : Measure (Fin M→ Bid i)) := by
  have h := ExceptionalSeed.fixed_exception_integral i G (fixedRow a kind) a
    (NativeIndexed.fixedRow_self a kind) own hown (coordinateLaw i G a own kind)
    (coordinateLaw_self i G a own kind) (coordinateLaw_lower i G a own kind) f
  have hm : Measurable (fixedBids i a own kind) := by
    convert! (continuous_fixedBids i a kind).measurable.comp
      (measurable_const.prodMk measurable_id) using 1
  rw [← fixedBids_law i G a own kind,
    integral_map hm.aemeasurable (ExceptionalSeed.measurable_test i G (fixedRow a kind) a f).aestronglyMeasurable,
    integral_map hm.aemeasurable
      (ExceptionalSeed.measurable_continuation_expect i G (fixedRow a kind) a f).aestronglyMeasurable] at h
  simpa only [rowLaw_eq_pi,ExceptionalProfile.draw,encode_row,encode_bids,ExceptionalSeed.test] using h

theorem indexedLaw_source (i : Row) (G : RestrictedLaw i)
    [NullSingletonClass (G.bidLaw : Measure (Bid i))]
    (a : Fin M) (own : ℝ) (hown : cap i< own) (f : Fin 3→ℝ) :
    (ExceptionalProfile.indexedLaw i G a own).expect f=
      (categoryRowLaw i M).expect (fun kind=>∫b : Fin M→ Bid i,
        (Exceptional.continuationLaw i G (fixedRow a kind) (fixedBids i a own kind b) a).expect
          (fun P=> f (pairCount a P)) ∂(rowLaw M G.bidLaw : Measure (Fin M→ Bid i))) := by
  let F : (Fin M→ NumericObservation i)→ℝ := fun z=>
    ∫s,f (ExceptionalProfile.count i G a own (z,s)) ∂((volume : Measure unitInterval).prod volume)
  have hm : Measurable F := by
    convert! ((measurable_of_countable f).comp
      (ExceptionalProfile.measurable_count i G a own)).stronglyMeasurable.integral_prod_right'.measurable using 1
    infer_instance
  have hB : ∀z,|F z|≤∑r,|f r| := by
    intro z
    have hb (privateSeed : unitInterval×unitInterval) :
        |f (ExceptionalProfile.count i G a own (z,privateSeed))|≤∑r,|f r| :=
      Finset.single_le_sum (s:=Finset.univ) (f:=fun r : Fin 3=>|f r|)
        (fun r _=>abs_nonneg (f r)) (Finset.mem_univ _)
    simpa only [F,Real.norm_eq_abs,probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const
        (f:=fun privateSeed : unitInterval×unitInterval=>f (ExceptionalProfile.count i G a own (z,privateSeed)))
        (ae_of_all ((volume : Measure unitInterval).prod volume)
          (fun privateSeed=>by simpa only [Real.norm_eq_abs] using hb privateSeed))
  have hi : Integrable (fun p=> F (encodeCategoryRow i M p))
      ((FiniteLaw.probabilityMeasure (categoryRowLaw i M)).prod
        (rowLaw M G.bidLaw : Measure (Fin M→ Bid i))) :=
    Integrable.of_bound (hm.comp (measurable_encodeCategoryRow i M)).aestronglyMeasurable
      (∑r,|f r|) (ae_of_all _ (fun p=> by simpa only [Real.norm_eq_abs] using hB _))
  rw [ExceptionalProfile.indexedLaw_expect]
  change (∫z,F z ∂Measure.pi (fun _ : Fin M=> numericObservationLaw i G))=_
  rw [← encodeCategoryRow_law i G M,integral_map
    (measurable_encodeCategoryRow i M).aemeasurable hm.aestronglyMeasurable,
    integral_prod _ hi,LowBody.integral_probabilityMeasure]
  exact FiniteLaw.expect_congr _ (fun kind=> fixed_allocation_integral i G a own hown kind
    (fun P=> f (pairCount a P)))

def countTest (i : Row) (G : RestrictedLaw i) (a : Fin M) (own : ℝ) (f : Fin 3→ℝ)
    (p : (Fin M→ Fin 3)×(Fin M→ Bid i)) : ℝ :=
  (Exceptional.continuationLaw i G (fixedRow a p.1) (fixedBids i a own p.1 p.2) a).expect
    (fun P=> f (pairCount a P))

theorem measurable_countTest (i : Row) (G : RestrictedLaw i) (a : Fin M) (own : ℝ) (f : Fin 3→ℝ) :
    Measurable (countTest i G a own f) := by
  apply measurable_from_prod_countable_right
  intro kind
  have hm : Measurable (fixedBids i a own kind) := by
    convert! (continuous_fixedBids i a kind).measurable.comp
      (measurable_const.prodMk measurable_id) using 1
  convert! (ExceptionalSeed.measurable_continuation_expect i G (fixedRow a kind) a
    (fun P=> f (pairCount a P))).comp hm using 1

theorem countTest_bound (i : Row) (G : RestrictedLaw i) (a : Fin M) (own : ℝ) (f : Fin 3→ℝ)
    (p : (Fin M→ Fin 3)×(Fin M→ Bid i)) : |countTest i G a own f p|≤∑k,|f k| := by
  apply (WeightedSampling.abs_expect_le _ _).trans
  apply FiniteLaw.expect_le_const
  intro P
  exact Finset.single_le_sum (fun k _=> abs_nonneg (f k)) (Finset.mem_univ (pairCount a P))

theorem integrable_countTest (i : Row) (G : RestrictedLaw i) (a : Fin M) (own : ℝ) (f : Fin 3→ℝ) :
    Integrable (countTest i G a own f)
      ((FiniteLaw.probabilityMeasure (categoryRowLaw i M)).prod
        (rowLaw M G.bidLaw : Measure (Fin M→ Bid i))) :=
  Integrable.of_bound (measurable_countTest i G a own f).aestronglyMeasurable (∑k,|f k|)
    (ae_of_all _ (fun p=> by simpa only [Real.norm_eq_abs] using countTest_bound i G a own f p))

theorem indexedLaw_source_integral (i : Row) (G : RestrictedLaw i)
    [NullSingletonClass (G.bidLaw : Measure (Bid i))]
    (a : Fin M) (own : ℝ) (hown : cap i< own) (f : Fin 3→ℝ) :
    (ExceptionalProfile.indexedLaw i G a own).expect f=
      ∫p,countTest i G a own f p ∂((FiniteLaw.probabilityMeasure (categoryRowLaw i M)).prod
        (rowLaw M G.bidLaw : Measure (Fin M→ Bid i))) := by
  rw [integral_prod _ (integrable_countTest i G a own f),LowBody.integral_probabilityMeasure,
    indexedLaw_source i G a own hown f]
  rfl

end FCAppendix.Affine.UniformFinite.Late.ExceptionalIndexed
