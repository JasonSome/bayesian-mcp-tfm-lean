import FCAppendix.Affine.UniformFinite.Late.ExceptionalIndexedSource

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine.UniformFinite.Late.ExceptionalIndexed
open Set MeasureTheory ProbabilityTheory Filter Topology Classical Game Bayes
open Existence.Distributional
open Uniform05 SourceContinuity LowBody
open scoped BigOperators
variable {M : ℕ}

theorem fixedBids_relabel (e : Equiv.Perm (Fin M)) (i : Row) (a : Fin M)
    (own : ℝ) (k : Fin M→ Fin 3) (b : Fin M→ Bid i) :
    fixedBids i (e a) own (k∘e.symm) (b∘e.symm)=fixedBids i a own k b∘e.symm := by
  funext j
  by_cases hj : e.symm j=a
  · have he : j=e a := by simpa using congrArg e hj
    simp [fixedBids,coordinate,he]
  · have he : j≠e a := fun h=> hj (by simp [h])
    simp [fixedBids,coordinate,hj,he]

theorem fixed_lowerBids (i : Row) (a : Fin M) (own : ℝ)
    (k : Fin M→ Fin 3) (b : Fin M→ Bid i) :
    Source.lowerBids (fixedRow a k) (fixedBids i a own k b)=fixedBids i a own k b := by
  funext j
  by_cases hj : j=a
  · subst j
    exact Source.lowerBids_of_mem _ _ (NativeIndexed.fixedRow_self a k)
  · by_cases hk : k j=0
    · exact Source.lowerBids_of_mem _ _ ((NativeIndexed.fixedRow_other a j k hj).mpr hk)
    · have hn : j∉(fixedRow a k).lower :=
        fun h=> hk ((NativeIndexed.fixedRow_other a j k hj).mp h)
      simp [Source.lowerBids,hn,fixedBids,coordinate,hj,hk]

theorem fixedBids_good (i : Row) (a : Fin M) (own : ℝ) (hown : 0≤ own)
    (k : Fin M→ Fin 3) (b : Fin M→ Bid i) :
    NativeExceptionalRow.Good i (fixedRow a k) a (fixedBids i a own k b) := by
  refine ⟨NativeIndexed.fixedRow_self a k,?_,?_⟩
  · intro j hj
    by_cases hja : j=a
    · subst j
      simpa only [fixedBids_self] using hown
    · have hk := (NativeIndexed.fixedRow_other a j k hja).mp hj
      simpa only [fixedBids,coordinate,if_neg hja,if_pos hk] using (b j).property.1
  · intro j hj hja
    have hk := (NativeIndexed.fixedRow_other a j k hja).mp hj
    simpa only [fixedBids,coordinate,if_neg hja,if_pos hk] using (b j).property.2

theorem fixed_potential_difference (i : Row) (a : Fin M)
    (own : ℝ) (k : Fin M→ Fin 3) (b : Fin M→ Bid i) (P Q : Allocation M) :
    CompleteInformation.potential (kappa i)
        (Source.lowerBids (fixedRow a k) (fixedBids i a own k b)) P.1 P.2-
      CompleteInformation.potential (kappa i)
        (Source.lowerBids (fixedRow a k) (fixedBids i a own k b)) Q.1 Q.2=
      (copyCoefficient (kappa i) P a-copyCoefficient (kappa i) Q a)*own+
        ∑j,NativeIndexed.tieCoefficient (kappa i) a k P Q j*(b j:ℝ) := by
  rw [fixed_lowerBids,potential_eq_copyCoefficient,potential_eq_copyCoefficient,
    ← Finset.sum_sub_distrib]
  have he (j : Fin M) :
      copyCoefficient (kappa i) P j*fixedBids i a own k b j-
        copyCoefficient (kappa i) Q j*fixedBids i a own k b j=
      (if j=a then (copyCoefficient (kappa i) P a-copyCoefficient (kappa i) Q a)*own else 0)+
        NativeIndexed.tieCoefficient (kappa i) a k P Q j*(b j:ℝ) := by
    by_cases hj : j=a
    · subst j
      simp [fixedBids,coordinate,NativeIndexed.tieCoefficient]
      ring
    · by_cases hk : k j=0 <;>
        simp [fixedBids,coordinate,NativeIndexed.tieCoefficient,hj,hk]; ring
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp

theorem ae_fixed_generic (i : Row) (G : RestrictedLaw i)
    [NullSingletonClass (G.bidLaw : Measure (Bid i))]
    (a : Fin M) (own : ℝ) (hown : 0< own) (k : Fin M→ Fin 3) :
    ∀ᵐb∂(rowLaw M G.bidLaw : Measure (Fin M→ Bid i)),∀P Q : Allocation M,
      CompleteInformation.potential (kappa i)
        (Source.lowerBids (fixedRow a k) (fixedBids i a own k b)) P.1 P.2=
      CompleteInformation.potential (kappa i)
        (Source.lowerBids (fixedRow a k) (fixedBids i a own k b)) Q.1 Q.2→
      focalCopy P a=focalCopy Q a := by
  rw [rowLaw_eq_pi]
  apply ae_all_iff.mpr
  intro P
  apply ae_all_iff.mpr
  intro Q
  by_cases hcopy : focalCopy P a=focalCopy Q a
  · exact ae_of_all _ (fun _ _=> hcopy)
  · have hκ : 0< kappa i := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) (ActualAtoms.kappa_ge_half i)
    have ha : copyCoefficient (kappa i) P a-copyCoefficient (kappa i) Q a≠0 :=
      sub_ne_zero.mpr (copyCoefficient_ne_of_focalCopy_ne hκ P Q a hcopy)
    by_cases hr : ∃j,NativeIndexed.tieCoefficient (kappa i) a k P Q j≠0
    · obtain ⟨j,hj⟩:=hr
      filter_upwards [ae_iid_linear_ne (G.bidLaw : Measure (Bid i))
        (NativeIndexed.tieCoefficient (kappa i) a k P Q) j hj
        (-(copyCoefficient (kappa i) P a-copyCoefficient (kappa i) Q a)*own)]
        with b hb hpot
      apply False.elim (hb ?_)
      have h:=fixed_potential_difference i a own k b P Q
      rw [hpot,sub_self] at h
      linarith
    · have hz : ∀j,NativeIndexed.tieCoefficient (kappa i) a k P Q j=0 := by
        simpa only [not_exists,not_not] using hr
      apply ae_of_all
      intro b hpot
      have h:=fixed_potential_difference i a own k b P Q
      rw [hpot,sub_self] at h
      simp only [hz,zero_mul,Finset.sum_const_zero,add_zero] at h
      exact False.elim ((mul_ne_zero ha hown.ne') h.symm)

variable [NeZero M]

theorem indexedLaw_relabel (i : Row) (G : RestrictedLaw i)
    [NullSingletonClass (G.bidLaw : Measure (Bid i))]
    (e : Equiv.Perm (Fin M)) (a : Fin M) (own : ℝ) (hown : cap i< own) :
    ExceptionalProfile.indexedLaw i G (e a) own=ExceptionalProfile.indexedLaw i G a own := by
  let μ:=(FiniteLaw.probabilityMeasure (categoryRowLaw i M)).prod
    (rowLaw M G.bidLaw : Measure (Fin M→ Bid i))
  let reindex : ((Fin M→ Fin 3)×(Fin M→ Bid i))→((Fin M→ Fin 3)×(Fin M→ Bid i)) :=
    fun p=>(p.1∘e.symm,p.2∘e.symm)
  have hp : MeasurePreserving reindex μ μ :=
    (NativeIndexed.category_relabel_preserving i e).prod
      (NativeIndexed.bids_relabel_preserving i G e)
  have ho : 0< own := (cap_pos i).trans hown
  apply FiniteLaw.ext_expect
  intro f
  rw [indexedLaw_source_integral i G (e a) own hown f,
    indexedLaw_source_integral i G a own hown f]
  calc
    _=∫p,countTest i G (e a) own f (reindex p) ∂μ := by
      have hmap:=integral_map (μ:=μ) hp.measurable.aemeasurable
        (measurable_countTest i G (e a) own f).aestronglyMeasurable
      rw [hp.map_eq] at hmap
      exact hmap
    _=∫p,countTest i G a own f p ∂μ := by
      have hnew : Integrable (fun p=> countTest i G (e a) own f (reindex p)) μ :=
        hp.integrable_comp_of_integrable (integrable_countTest i G (e a) own f)
      rw [show μ=(FiniteLaw.probabilityMeasure (categoryRowLaw i M)).prod
        (rowLaw M G.bidLaw : Measure (Fin M→ Bid i)) from rfl,
        integral_prod _ hnew,integral_prod _ (integrable_countTest i G a own f)]
      apply integral_congr_ae
      apply ae_of_all
      intro k
      apply integral_congr_ae
      filter_upwards [ae_fixed_generic i G a own ho k] with b hb
      have h:=ExceptionalRelabel.continuation_count_relabel e i G (fixedRow a k)
        (fixedBids i a own k b) a (fixedBids_good i a own ho.le k b) hb f
      simpa only [countTest,reindex,NativeIndexed.fixedRow_relabel,fixedBids_relabel,
        Function.comp_apply] using h

end FCAppendix.Affine.UniformFinite.Late.ExceptionalIndexed

namespace FCAppendix.Affine.UniformFinite.Late.ExceptionalProfile
open Set MeasureTheory ProbabilityTheory Filter Topology Classical Game Bayes
open Existence.Distributional
open Uniform05 SourceContinuity
open scoped BigOperators
variable {N : ℕ}

theorem numericFocal_row (i : Row) (z : Fin N→ NumericObservation i) :
    numericRow i (0 : Fin (N+1)) (Fin.cons (Sum.inl (Noisy.zeroBid i)) z)=
      NativeProfile.numericRow i (Fin.cons (Sum.inl (Noisy.zeroBid i)) z) := by
  simp only [numericRow,NativeProfile.insert]
  congr 1
  funext a
  refine Fin.cases ?_ (fun j=>?_) a <;> simp

theorem numericFocal_draw (i : Row) (G : RestrictedLaw i) (own : ℝ)
    (kind : Fin N→ Fin 3) (b : Fin N→ Bid i) (s : unitInterval×unitInterval) :
    draw i G (0 : Fin (N+1)) own
        (Fin.cons (Sum.inl (Noisy.zeroBid i)) (encodeCategoryRow i N (kind,b))) s=
      ExceptionalCounts.rowDraw i G own kind b s := by
  have hr : numericRow i (0 : Fin (N+1))
      (Fin.cons (Sum.inl (Noisy.zeroBid i)) (encodeCategoryRow i N (kind,b)))=focalRow kind := by
    rw [numericFocal_row]
    unfold NativeProfile.numericRow focalRow
    apply congrArg Source.countRowOfKind
    funext a
    refine Fin.cases ?_ (fun j=>?_) a
    · rfl
    · simp [encodeCategoryRow]
  have hb : numericBids i (0 : Fin (N+1)) own
      (Fin.cons (Sum.inl (Noisy.zeroBid i)) (encodeCategoryRow i N (kind,b)))=
      focalBids i kind own b := by
    funext a
    refine Fin.cases ?_ (fun j=>?_) a
    · simp only [numericBids,Function.update_self,focalBids,Fin.cons_zero]
    · by_cases hj : kind j=0
      · simp [numericBids,encodeCategoryRow,encodeCategory,numericBid,focalBids,hj]
      · by_cases hj1 : kind j=1 <;>
          simp [numericBids,encodeCategoryRow,encodeCategory,numericBid,focalBids,hj,hj1]
  simp only [draw,hr,hb,ExceptionalCounts.rowDraw]

theorem draw_zero_tail (i : Row) (G : RestrictedLaw i) (own : ℝ)
    (z : Fin (N+1)→ NumericObservation i) (s : unitInterval×unitInterval) :
    draw i G 0 own z s=draw i G 0 own
      (Fin.cons (Sum.inl (Noisy.zeroBid i)) (fun j : Fin N=> z j.succ)) s := by
  have hr : numericRow i (0 : Fin (N+1)) z=
      numericRow i 0 (Fin.cons (Sum.inl (Noisy.zeroBid i)) (fun j : Fin N=> z j.succ)) := by
    rw [numericFocal_row]
    exact congrArg (NativeProfile.numericRow i) (NativeProfile.insert_zero i (Noisy.zeroBid i) z)
  have hb : numericBids i (0 : Fin (N+1)) own z=
      numericBids i 0 own (Fin.cons (Sum.inl (Noisy.zeroBid i)) (fun j : Fin N=> z j.succ)) := by
    funext a
    refine Fin.cases ?_ (fun j=>?_) a <;> simp [numericBids]
  simp only [draw,hr,hb]

def focalCountTest (i : Row) (G : RestrictedLaw i) (own : ℝ) (f : Fin 3→ℝ)
    (z : Fin N→ NumericObservation i) : ℝ :=
  ∫s,f (pairCount 0 (draw i G 0 own (Fin.cons (Sum.inl (Noisy.zeroBid i)) z) s))
    ∂((volume : Measure unitInterval).prod volume)

theorem measurable_focalCountTest (i : Row) (G : RestrictedLaw i) (own : ℝ)
    (f : Fin 3→ℝ) : Measurable (focalCountTest (N:=N) i G own f) := by
  have h:=((measurable_of_countable (fun P : Allocation (N+1)=> f (pairCount 0 P))).comp
    ((measurable_draw i G 0 own).comp
      (((NativeProfile.measurable_numericFocal i (Noisy.zeroBid i)).comp measurable_fst).prodMk
        measurable_snd)))
  convert! h.stronglyMeasurable.integral_prod_right'.measurable using 1
  infer_instance

theorem focalCountTest_bound (i : Row) (G : RestrictedLaw i) (own : ℝ)
    (f : Fin 3→ℝ) (z : Fin N→ NumericObservation i) :
    |focalCountTest i G own f z|≤∑r,|f r| := by
  have hb (privateSeed : unitInterval×unitInterval) :
      |f (pairCount 0 (draw i G 0 own (Fin.cons (Sum.inl (Noisy.zeroBid i)) z) privateSeed))|≤∑r,|f r| :=
    Finset.single_le_sum (s:=Finset.univ) (f:=fun r : Fin 3=>|f r|)
      (fun r _=>abs_nonneg (f r)) (Finset.mem_univ _)
  simpa only [focalCountTest,Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const
      (f:=fun privateSeed : unitInterval×unitInterval=>
        f (pairCount 0 (draw i G 0 own (Fin.cons (Sum.inl (Noisy.zeroBid i)) z) privateSeed)))
      (ae_of_all ((volume : Measure unitInterval).prod volume)
        (fun privateSeed=>by simpa only [Real.norm_eq_abs] using hb privateSeed))

theorem indexedLaw_zero (i : Row) (G : RestrictedLaw i)
    [NullSingletonClass (G.bidLaw : Measure (Bid i))] (own : ℝ) (hown : cap i< own) :
    indexedLaw i G (0 : Fin (N+1)) own=ExceptionalCounts.actualCountLaw i N G own := by
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
  rw [indexedLaw_expect,ExceptionalCounts.actualCountLaw_expect i N G own hown f]
  have hf (z : Fin (N+1)→ NumericObservation i) :
      (∫s,f (count i G 0 own (z,s)) ∂((volume : Measure unitInterval).prod volume))=
        focalCountTest i G own f (tail z) := by
    apply integral_congr_ae
    exact ae_of_all _ (fun s=> by
      dsimp only [count,focalCountTest,tail]
      rw [draw_zero_tail i G own z s])
  simp_rw [hf]
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
        ExceptionalCounts.row_integral i G own hown kind (fun P=> f (pairCount 0 P))

theorem indexedLaw_eq_actual (i : Row) (G : RestrictedLaw i)
    [NullSingletonClass (G.bidLaw : Measure (Bid i))]
    (a : Fin (N+1)) (own : ℝ) (hown : cap i< own) :
    indexedLaw i G a own=ExceptionalCounts.actualCountLaw i N G own := by
  have h:=ExceptionalIndexed.indexedLaw_relabel i G
    (Hybrid.NativeContinuation.focalIndex a) 0 own hown
  rw [Hybrid.NativeContinuation.focalIndex_zero,indexedLaw_zero i G own hown] at h
  exact h

end FCAppendix.Affine.UniformFinite.Late.ExceptionalProfile
