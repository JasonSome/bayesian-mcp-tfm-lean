import FCAppendix.Affine.UniformFinite.NativeProfile

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology Classical Game Bayes
open Existence.Distributional
open Uniform05 SourceContinuity
open scoped BigOperators

namespace NativeIndexed
variable {M : ℕ}

def fixedKind (a : Fin M) (kind : Fin M→ Fin 3) : Fin M→ Fin 3 :=
  Function.update kind a 0

def fixedRow (a : Fin M) (kind : Fin M→ Fin 3) : Source.CountRow M :=
  Source.countRowOfKind (fixedKind a kind)

def coordinate (i : Row) (a : Fin M) (own : Bid i) (kind : Fin M→ Fin 3)
    (j : Fin M) (b : Bid i) : Bid i :=
  if j=a then own else if kind j=0 then b else Noisy.zeroBid i

def fixedBids (i : Row) (a : Fin M) (own : Bid i) (kind : Fin M→ Fin 3)
    (b : Fin M→ Bid i) : Fin M→ Bid i := fun j=> coordinate i a own kind j (b j)

@[simp] lemma fixedRow_self (a : Fin M) (kind : Fin M→ Fin 3) :
    a∈(fixedRow a kind).lower := by
  simp [fixedRow,Source.countRowOfKind,fixedKind]

@[simp] lemma fixedBids_self (i : Row) (a : Fin M) (own : Bid i)
    (kind : Fin M→ Fin 3) (b : Fin M→ Bid i) : fixedBids i a own kind b a=own := by
  simp [fixedBids,coordinate]

lemma fixedRow_other (a j : Fin M) (kind : Fin M→ Fin 3) (hj : j≠a) :
    j∈(fixedRow a kind).lower↔kind j=0 := by
  simp [fixedRow,Source.countRowOfKind,fixedKind,Function.update_of_ne hj]

lemma measurable_coordinate (i : Row) (a : Fin M) (own : Bid i)
    (kind : Fin M→ Fin 3) (j : Fin M) : Measurable (coordinate i a own kind j) := by
  unfold coordinate
  split_ifs <;> first | exact measurable_const | exact measurable_id

lemma continuous_fixedBids (i : Row) (a : Fin M) (kind : Fin M→ Fin 3) :
    Continuous (fun p : Bid i×(Fin M→ Bid i)=> fixedBids i a p.1 kind p.2) := by
  apply continuous_pi
  intro j
  unfold fixedBids coordinate
  split_ifs
  · exact continuous_fst
  · exact (continuous_apply j).comp continuous_snd
  · exact continuous_const

def coordinateLaw (i : Row) (G : RestrictedLaw i) (a : Fin M) (own : Bid i)
    (kind : Fin M→ Fin 3) (j : Fin M) : Measure (Bid i) :=
  (G.bidLaw : Measure (Bid i)).map (coordinate i a own kind j)

instance coordinateLaw_probability (i : Row) (G : RestrictedLaw i) (a : Fin M) (own : Bid i)
    (kind : Fin M→ Fin 3) (j : Fin M) : IsProbabilityMeasure (coordinateLaw i G a own kind j) :=
  Measure.isProbabilityMeasure_map (measurable_coordinate i a own kind j).aemeasurable

@[simp] lemma coordinateLaw_self (i : Row) (G : RestrictedLaw i) (a : Fin M)
    (own : Bid i) (kind : Fin M→ Fin 3) : coordinateLaw i G a own kind a=Measure.dirac own := by
  have he : coordinate i a own kind a=(fun _ : Bid i=>own) := by
    funext x
    simp [coordinate]
  rw [coordinateLaw,he]
  simp

lemma coordinateLaw_lower (i : Row) (G : RestrictedLaw i) (a : Fin M) (own : Bid i)
    (kind : Fin M→ Fin 3) (j : Fin M) (hj : j∈(fixedRow a kind).lower) (hne : j≠a) :
    coordinateLaw i G a own kind j=(G.bidLaw : Measure (Bid i)) := by
  have hk:=(fixedRow_other a j kind hne).mp hj
  have he : coordinate i a own kind j=id := by funext x; simp [coordinate,hne,hk]
  rw [coordinateLaw,he,Measure.map_id]

lemma fixedBids_law (i : Row) (G : RestrictedLaw i) (a : Fin M) (own : Bid i)
    (kind : Fin M→ Fin 3) :
    (Measure.pi (fun _ : Fin M=>(G.bidLaw : Measure (Bid i)))).map
      (fixedBids i a own kind)=Measure.pi (coordinateLaw i G a own kind) :=
  Measure.pi_map_pi (fun j=>(measurable_coordinate i a own kind j).aemeasurable)

lemma encode_insert_row (i : Row) (a : Fin M) (own : Bid i)
    (kind : Fin M→ Fin 3) (b : Fin M→ Bid i) :
    NativeProfile.numericRow i (NativeProfile.insert a own (encodeCategoryRow i M (kind,b)))=
      fixedRow a kind := by
  change Source.countRowOfKind (fun j=>numericKind i
    (NativeProfile.insert a own (encodeCategoryRow i M (kind,b)) j))=
      Source.countRowOfKind (fixedKind a kind)
  apply congrArg Source.countRowOfKind
  funext j
  by_cases hj : j=a
  · subst j
    simp [NativeProfile.insert,fixedKind,numericKind]
  · simp [NativeProfile.insert,fixedKind,
      Function.update_of_ne hj,encodeCategoryRow]

lemma encode_insert_bids (i : Row) (a : Fin M) (own : Bid i)
    (kind : Fin M→ Fin 3) (b : Fin M→ Bid i) :
    NativeProfile.numericBids i (NativeProfile.insert a own (encodeCategoryRow i M (kind,b)))=
      fixedBids i a own kind b := by
  funext j
  by_cases hj : j=a
  · subst j
    simp [NativeProfile.numericBids,NativeProfile.numericCapped,NativeProfile.insert,fixedBids,coordinate]
  · by_cases hk : kind j=0 <;>
      simp [NativeProfile.numericBids,NativeProfile.numericCapped,NativeProfile.insert,fixedBids,
        coordinate,hj,hk,encodeCategoryRow,encodeCategory]
    split_ifs <;> rfl

variable [NeZero M]

lemma measurable_source_expect (i : Row) (G : RestrictedLaw i) (a : Fin M)
    (own : Bid i) (kind : Fin M→ Fin 3) (f : Fin 3→ℝ) :
    Measurable (fun b : Fin M→ Bid i=>
      (rowCountLaw i G (fixedRow a kind) (bids i (G,fixedBids i a own kind b)) a).expect f) := by
  have hb : Measurable (fixedBids i a own kind) :=
    (continuous_fixedBids i a kind).measurable.comp ((measurable_const (a:=own)).prodMk measurable_id)
  convert! (measurable_continuation_expect i (fixedRow a kind) (fun P=> f (pairCount a P))).comp
    ((measurable_fixedLawState i G).comp hb) using 1
  simp only [rowCountLaw,FiniteLaw.expect_map]
  rfl

theorem fixed_trace_integral (i : Row) (G : RestrictedLaw i)
    [NullSingletonClass (G.bidLaw : Measure (Bid i))]
    (a : Fin M) (own : Bid i) (kind : Fin M→ Fin 3) (g : Bool×Bool→ℝ) :
    (∫b : Fin M→ Bid i,∫s,g (NativeRow.focalTrace a
      (NativeProfile.draw i G (NativeProfile.insert a own (encodeCategoryRow i M (kind,b))) s))
        ∂((volume : Measure unitInterval).prod volume)
        ∂(rowLaw M G.bidLaw : Measure (Fin M→ Bid i)))=
      ∫b : Fin M→ Bid i,
        (continuationLaw i G (fixedRow a kind) (bids i (G,fixedBids i a own kind b))).expect
          (fun P=> g (NativeRow.focalTrace a P))
        ∂(rowLaw M G.bidLaw : Measure (Fin M→ Bid i)) := by
  let f : Allocation M→ℝ:=fun P=> g (NativeRow.focalTrace a P)
  have h:=NativeSeed.fixed_focal_trace_integral i G (fixedRow a kind) a
    (fixedRow_self a kind) own (coordinateLaw i G a own kind)
    (coordinateLaw_self i G a own kind) (coordinateLaw_lower i G a own kind) g
  have hm : Measurable (fixedBids i a own kind) :=
    (continuous_fixedBids i a kind).measurable.comp ((measurable_const (a:=own)).prodMk measurable_id)
  have ht:=NativeSeed.measurable_test i G (fixedRow a kind) f
  have hp : Measurable (fun b : Fin M→Bid i=>
      (continuationLaw i G (fixedRow a kind) (bids i (G,b))).expect f) :=
    (measurable_continuation_expect i (fixedRow a kind) f).comp (measurable_fixedLawState i G)
  rw [← fixedBids_law i G a own kind] at h
  have hleft := integral_map (μ:=Measure.pi (fun _ : Fin M=>(G.bidLaw : Measure (Bid i))))
    hm.aemeasurable ht.aestronglyMeasurable
  have hright := integral_map (μ:=Measure.pi (fun _ : Fin M=>(G.bidLaw : Measure (Bid i))))
    hm.aemeasurable hp.aestronglyMeasurable
  change (∫b,NativeSeed.test i G (fixedRow a kind) f b
      ∂(Measure.pi (fun _ : Fin M=>(G.bidLaw : Measure (Bid i)))).map (fixedBids i a own kind))=
    ∫b,(continuationLaw i G (fixedRow a kind) (bids i (G,b))).expect f
      ∂(Measure.pi (fun _ : Fin M=>(G.bidLaw : Measure (Bid i)))).map (fixedBids i a own kind) at h
  have h' := hleft.symm.trans (h.trans hright)
  simpa only [rowLaw_eq_pi,NativeProfile.draw,encode_insert_row,encode_insert_bids,
    NativeSeed.test,f] using h'

theorem fixed_count_integral (i : Row) (G : RestrictedLaw i)
    [NullSingletonClass (G.bidLaw : Measure (Bid i))]
    (a : Fin M) (own : Bid i) (kind : Fin M→ Fin 3) (f : Fin 3→ℝ) :
    (∫b : Fin M→ Bid i,∫s,f (NativeProfile.count i G a own (encodeCategoryRow i M (kind,b),s))
        ∂((volume : Measure unitInterval).prod volume)
        ∂(rowLaw M G.bidLaw : Measure (Fin M→ Bid i)))=
      ∫b : Fin M→ Bid i,
        (rowCountLaw i G (fixedRow a kind) (bids i (G,fixedBids i a own kind b)) a).expect f
        ∂(rowLaw M G.bidLaw : Measure (Fin M→ Bid i)) := by
  simpa only [NativeProfile.count,rowCountLaw,FiniteLaw.expect_map,NativeCounts.pairCount_trace] using
    fixed_trace_integral i G a own kind (fun r=> f (NativeCounts.traceCount r))

theorem indexedLaw_source (i : Row) (G : RestrictedLaw i)
    [NullSingletonClass (G.bidLaw : Measure (Bid i))]
    (a : Fin M) (own : Bid i) (f : Fin 3→ℝ) :
    (NativeProfile.indexedLaw i G a own).expect f=
      (categoryRowLaw i M).expect (fun kind=>
        ∫b : Fin M→ Bid i,
          (rowCountLaw i G (fixedRow a kind) (bids i (G,fixedBids i a own kind b)) a).expect f
          ∂(rowLaw M G.bidLaw : Measure (Fin M→ Bid i))) := by
  let F : (Fin M→ NumericObservation i)→ℝ:=fun z=>
    ∫s,f (NativeProfile.count i G a own (z,s)) ∂((volume : Measure unitInterval).prod volume)
  have hm : Measurable F := by
    convert! ((measurable_of_countable f).comp
      (NativeProfile.measurable_count i G a own)).stronglyMeasurable.integral_prod_right'.measurable using 1
    infer_instance
  have hB : ∀z,|F z|≤∑r,|f r| := by
    intro z
    have hb (privateSeed : unitInterval×unitInterval) :
        |f (NativeProfile.count i G a own (z,privateSeed))|≤∑r,|f r| :=
      Finset.single_le_sum (s:=Finset.univ) (f:=fun r : Fin 3=>|f r|)
        (fun r _=>abs_nonneg (f r)) (Finset.mem_univ _)
    simpa only [F,Real.norm_eq_abs,probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const (f:=fun s : unitInterval×unitInterval=>
        f (NativeProfile.count i G a own (z,s))) (ae_of_all ((volume : Measure unitInterval).prod volume)
        (fun privateSeed=> by simpa only [Real.norm_eq_abs] using hb privateSeed))
  have hi : Integrable (fun p=> F (encodeCategoryRow i M p))
      ((FiniteLaw.probabilityMeasure (categoryRowLaw i M)).prod
        (rowLaw M G.bidLaw : Measure (Fin M→ Bid i))) :=
    Integrable.of_bound (hm.comp (measurable_encodeCategoryRow i M)).aestronglyMeasurable
      (∑r,|f r|) (ae_of_all _ (fun p=> by simpa only [Real.norm_eq_abs] using hB _))
  rw [NativeProfile.indexedLaw_expect]
  change (∫z,F z ∂Measure.pi (fun _ : Fin M=> numericObservationLaw i G))=_
  rw [← encodeCategoryRow_law i G M,integral_map
    (measurable_encodeCategoryRow i M).aemeasurable hm.aestronglyMeasurable,
    integral_prod _ hi,LowBody.integral_probabilityMeasure]
  exact FiniteLaw.expect_congr _ (fun kind=> fixed_count_integral i G a own kind f)

def utility (i : Row) (G : RestrictedLaw i) (a : Fin M) (v : ℝ) (own : Bid i) : ℝ :=
  (NativeProfile.indexedLaw i G a own).utility v own 0
    (Schedule.affine 2 (eta i) (eta_range i).1.le (eta_range i).2.le) (Schedule.once 2)

theorem utility_source (i : Row) (G : RestrictedLaw i)
    [NullSingletonClass (G.bidLaw : Measure (Bid i))]
    (a : Fin M) (v : ℝ) (own : Bid i) :
    utility i G a v own=(categoryRowLaw i M).expect (fun kind=>
      ∫b : Fin M→ Bid i,rowPayoff i G (fixedRow a kind) v
        (bids i (G,fixedBids i a own kind b)) a
        ∂(rowLaw M G.bidLaw : Measure (Fin M→ Bid i))) := by
  rw [utility,CountLaw.utility,indexedLaw_source]
  simp only [rowCountLaw,FiniteLaw.expect_map,← pairPayoff_as_count,
    rowPayoff,SourceContinuity.bids,fixedBids_self]

lemma measurable_row_utility (i : Row) (G : RestrictedLaw i) (a : Fin M)
    (v : ℝ) (own : Bid i) (kind : Fin M→ Fin 3) :
    Measurable (fun b : Fin M→ Bid i=> rowPayoff i G (fixedRow a kind) v
      (bids i (G,fixedBids i a own kind b)) a) := by
  have hb : Measurable (fixedBids i a own kind) :=
    (continuous_fixedBids i a kind).measurable.comp ((measurable_const (a:=own)).prodMk measurable_id)
  convert! (SourceContinuity.measurable_rowPayoff i (fixedRow a kind) a (fixedRow_self a kind)).comp
    ((measurable_const (a:=v)).prodMk ((measurable_fixedLawState i G).comp hb)) using 1

lemma integrable_row_utility (i : Row) (G : RestrictedLaw i) (a : Fin M)
    (v : ℝ) (own : Bid i) (kind : Fin M→ Fin 3) :
    Integrable (fun b : Fin M→ Bid i=> rowPayoff i G (fixedRow a kind) v
      (bids i (G,fixedBids i a own kind b)) a)
        (rowLaw M G.bidLaw : Measure (Fin M→ Bid i)) :=
  Integrable.of_bound (measurable_row_utility i G a v own kind).aestronglyMeasurable
    (|v|+(1+|eta i|)*|(own:ℝ)|) (ae_of_all _ (fun b=> by
      simpa only [Real.norm_eq_abs,SourceContinuity.bids,fixedBids_self] using
        rowPayoff_bound i G (fixedRow a kind) v (bids i (G,fixedBids i a own kind b)) a))

theorem game_payoff {i : Row} {R : ℝ} (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i< R)
    (a : Fin M) (v : ℝ) (own : Bid i) :
    (problem (OriginalPopulation.game E H) a).payoff v (Hybrid.lowBroadcast own)=
      utility i E.law a v own := by
  change ((problem (OriginalPopulation.game E H) a).outcome (Hybrid.lowBroadcast own)).utility
    v own 0 (Schedule.affine 2 (eta i) (eta_range i).1.le (eta_range i).2.le) (Schedule.once 2)=_
  rw [OriginalPopulation.game_broadcast_outcome E H hR a own]
  rfl

end NativeIndexed
end FCAppendix.Affine.UniformFinite
