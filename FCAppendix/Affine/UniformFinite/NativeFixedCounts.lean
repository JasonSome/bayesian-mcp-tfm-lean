import FCAppendix.Affine.UniformFinite.NativeConditional

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology Classical Game
open Existence.Distributional
open Uniform05 SourceContinuity
open scoped BigOperators

namespace NativeCounts

def fullCoordinateLaw (i : Row) {N : ℕ} (G : RestrictedLaw i)
    (kind : Fin N→ Fin 3) (own : Bid i) : Fin (N+1)→ Measure (Bid i) :=
  Fin.cons (Measure.dirac own) (fun j=> if kind j=0 then
    (G.bidLaw : Measure (Bid i)) else Measure.dirac (Noisy.zeroBid i))

instance fullCoordinate_probability (i : Row) {N : ℕ} (G : RestrictedLaw i)
    (kind : Fin N→ Fin 3) (own : Bid i) (a : Fin (N+1)) :
    IsProbabilityMeasure (fullCoordinateLaw i G kind own a) := by
  refine Fin.cases ?_ (fun j=>?_) a
  · change IsProbabilityMeasure (Measure.dirac own)
    infer_instance
  · change IsProbabilityMeasure (if kind j=0 then (G.bidLaw : Measure (Bid i)) else _)
    split_ifs <;> infer_instance

theorem cappedFocalBids_law (i : Row) {N : ℕ} (G : RestrictedLaw i)
    (kind : Fin N→ Fin 3) (own : Bid i) :
    (rowLaw N G.bidLaw : Measure (Fin N→ Bid i)).map
      (Noisy.cappedFocalBids i kind own)=Measure.pi (fullCoordinateLaw i G kind own) := by
  rw [rowLaw_eq_pi]
  symm
  apply Measure.pi_eq
  intro E hE
  have hm : Measurable (Noisy.cappedFocalBids i kind own) :=
    (Noisy.continuous_cappedFocalBids i kind).measurable.comp
      ((measurable_const (a:=own)).prodMk measurable_id)
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hE)]
  by_cases ho : own∈E 0
  · have hpre : Noisy.cappedFocalBids i kind own ⁻¹' Set.univ.pi E=
        Set.univ.pi (fun j : Fin N=>
          (fun b : Bid i=> if kind j=0 then b else Noisy.zeroBid i) ⁻¹' E j.succ) := by
      ext b
      simp only [mem_preimage,Set.mem_pi,mem_univ,true_implies]
      constructor
      · intro hb j
        exact hb j.succ
      · intro hb a
        exact Fin.cases ho (fun j=> hb j) a
    rw [hpre,Measure.pi_pi,Fin.prod_univ_succ]
    simp only [fullCoordinateLaw,Fin.cons_zero,Fin.cons_succ,
      Measure.dirac_apply' own (hE 0),Set.indicator_of_mem ho,Pi.one_apply,one_mul]
    apply Finset.prod_congr rfl
    intro j _
    by_cases hj : kind j=0
    · simp only [if_pos hj]
      rfl
    · simp only [if_neg hj,Measure.dirac_apply' (Noisy.zeroBid i) (hE j.succ)]
      by_cases hzero : Noisy.zeroBid i∈E j.succ
      · rw [Set.preimage_const_of_mem hzero]
        simp [hzero]
      · rw [Set.preimage_const_of_notMem hzero]
        simp [hzero]
  · have hpre : Noisy.cappedFocalBids i kind own ⁻¹' Set.univ.pi E=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro b hb
      exact ho (hb 0 (mem_univ 0))
    rw [hpre,measure_empty,Fin.prod_univ_succ]
    simp [fullCoordinateLaw,Measure.dirac_apply' own (hE 0),ho]

lemma fullCoordinate_lower (i : Row) {N : ℕ} (G : RestrictedLaw i)
    (kind : Fin N→ Fin 3) (own : Bid i) (a : Fin (N+1))
    (ha : a∈(focalRow kind).lower) (hne : a≠0) :
    fullCoordinateLaw i G kind own a=(G.bidLaw : Measure (Bid i)) := by
  revert ha hne
  refine Fin.cases ?_ (fun j=>?_) a
  · intro _ hne
    exact False.elim (hne rfl)
  intro ha _
  have hj : kind j=0 := by simpa [focalRow,Source.countRowOfKind] using ha
  simp only [fullCoordinateLaw,Fin.cons_succ,if_pos hj]

def rowDraw (i : Row) {N : ℕ} (G : RestrictedLaw i) (own : Bid i)
    (kind : Fin N→ Fin 3) (b : Fin N→ Bid i) (s : unitInterval×unitInterval) : Allocation (N+1) :=
  let full:=Noisy.cappedFocalBids i kind own b
  NativeRow.draw i (focalRow kind) (G,full) (NativeSeed.common i G (focalRow kind) full,s)

lemma measurable_rowDraw (i : Row) {N : ℕ} (G : RestrictedLaw i) (own : Bid i)
    (kind : Fin N→ Fin 3) : Measurable (Function.uncurry (rowDraw i G own kind)) := by
  have hb : Measurable (fun x : (Fin N→ Bid i)×(unitInterval×unitInterval)=>
      Noisy.cappedFocalBids i kind own x.1) :=
    (Noisy.continuous_cappedFocalBids i kind).measurable.comp
      ((measurable_const (a:=own)).prodMk measurable_fst)
  convert! (NativeRow.draw_joint_measurable i (focalRow kind)).comp
    (((measurable_fixedLawState i G).comp hb).prodMk
      (((NativeSeed.measurable_common i G (focalRow kind)).comp hb).prodMk measurable_snd)) using 1

theorem row_trace_integral (i : Row) {N : ℕ} (G : RestrictedLaw i)
    [NullSingletonClass (G.bidLaw : Measure (Bid i))]
    (own : Bid i) (kind : Fin N→ Fin 3) (g : Bool×Bool→ℝ) :
    (∫b : Fin N→ Bid i,∫s,g (NativeRow.focalTrace 0 (rowDraw i G own kind b s))
      ∂((volume : Measure unitInterval).prod volume)
      ∂(rowLaw N G.bidLaw : Measure (Fin N→ Bid i)))=
      ∫b : Fin N→ Bid i,(continuationLaw i G (focalRow kind) (focalBids i kind own b)).expect
        (fun P=> g (NativeRow.focalTrace 0 P))
        ∂(rowLaw N G.bidLaw : Measure (Fin N→ Bid i)) := by
  let f : Allocation (N+1)→ℝ:=fun P=> g (NativeRow.focalTrace 0 P)
  have h:=NativeSeed.fixed_focal_trace_integral i G (focalRow kind) 0
    (Noisy.focal_mem_lower kind) own (fullCoordinateLaw i G kind own) rfl
    (fullCoordinate_lower i G kind own) g
  have hm : Measurable (Noisy.cappedFocalBids i kind own) :=
    (Noisy.continuous_cappedFocalBids i kind).measurable.comp
      ((measurable_const (a:=own)).prodMk measurable_id)
  have ht := NativeSeed.measurable_test i G (focalRow kind) f
  have hp : Measurable (fun b : Fin (N+1)→Bid i=>
      (continuationLaw i G (focalRow kind) (bids i (G,b))).expect f) :=
    (measurable_continuation_expect i (focalRow kind) f).comp (measurable_fixedLawState i G)
  rw [← cappedFocalBids_law i G kind own] at h
  have hmleft := integral_map (μ:=(rowLaw N G.bidLaw : Measure (Fin N→Bid i)))
    hm.aemeasurable ht.aestronglyMeasurable
  have hmright := integral_map (μ:=(rowLaw N G.bidLaw : Measure (Fin N→Bid i)))
    hm.aemeasurable hp.aestronglyMeasurable
  change (∫b,NativeSeed.test i G (focalRow kind) f b
      ∂(rowLaw N G.bidLaw : Measure (Fin N→Bid i)).map (Noisy.cappedFocalBids i kind own))=
    ∫b,(continuationLaw i G (focalRow kind) (bids i (G,b))).expect f
      ∂(rowLaw N G.bidLaw : Measure (Fin N→Bid i)).map (Noisy.cappedFocalBids i kind own) at h
  have h' := hmleft.symm.trans (h.trans hmright)
  calc
    _ = ∫b,(continuationLaw i G (focalRow kind)
        (bids i (show State i (N+1) from (G,Noisy.cappedFocalBids i kind own b)))).expect f
        ∂(rowLaw N G.bidLaw : Measure (Fin N→Bid i)) := by
      convert! h' using 1
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun b=> congrArg
        (fun w=> (continuationLaw i G (focalRow kind) w).expect f)
        (Noisy.cappedFocalBids_real i kind own b))

def traceCount (r : Bool×Bool) : Fin 3 :=
  ⟨(if r.1 then 1 else 0)+(if r.2 then 1 else 0),by cases r with | mk x y=> cases x <;> cases y <;> decide⟩

lemma pairCount_trace {M : ℕ} (a : Fin M) (P : Allocation M) :
    pairCount a P=traceCount (NativeRow.focalTrace a P) := by
  apply Fin.ext
  by_cases h0 : a∈P.1 <;> by_cases h1 : a∈P.2 <;>
    simp [pairCount,traceCount,NativeRow.focalTrace,h0,h1]

theorem row_count_integral (i : Row) {N : ℕ} (G : RestrictedLaw i)
    [NullSingletonClass (G.bidLaw : Measure (Bid i))]
    (own : Bid i) (kind : Fin N→ Fin 3) (f : Fin 3→ℝ) :
    (∫b : Fin N→ Bid i,∫s,f (pairCount 0 (rowDraw i G own kind b s))
      ∂((volume : Measure unitInterval).prod volume)
      ∂(rowLaw N G.bidLaw : Measure (Fin N→ Bid i)))=
      ∫b : Fin N→ Bid i,(rowCountLaw i G (focalRow kind) (focalBids i kind own b) 0).expect f
        ∂(rowLaw N G.bidLaw : Measure (Fin N→ Bid i)) := by
  simpa only [rowCountLaw,FiniteLaw.expect_map,pairCount_trace] using
    row_trace_integral i G own kind (fun r=> f (traceCount r))

abbrev Sample (i : Row) (N : ℕ) :=
  ((Fin N→ Fin 3)×(Fin N→ Bid i))×(unitInterval×unitInterval)

def law (i : Row) (N : ℕ) (G : RestrictedLaw i) : Measure (Sample i N) :=
  ((FiniteLaw.probabilityMeasure (categoryRowLaw i N)).prod
    (rowLaw N G.bidLaw : Measure (Fin N→ Bid i))).prod
      ((volume : Measure unitInterval).prod volume)

instance law_probability (i : Row) (N : ℕ) (G : RestrictedLaw i) :
    IsProbabilityMeasure (law i N G) := by unfold law; infer_instance

def count (i : Row) {N : ℕ} (G : RestrictedLaw i) (own : Bid i) (x : Sample i N) : Fin 3 :=
  pairCount 0 (rowDraw i G own x.1.1 x.1.2 x.2)

lemma measurable_count (i : Row) {N : ℕ} (G : RestrictedLaw i) (own : Bid i) :
    Measurable (count (N:=N) i G own) := by
  have hrow : Measurable (fun x : (Fin N→ Fin 3)×((Fin N→ Bid i)×(unitInterval×unitInterval))=>
      rowDraw i G own x.1 x.2.1 x.2.2) :=
    measurable_from_prod_countable_right (measurable_rowDraw i G own)
  convert! (measurable_of_countable (pairCount 0)).comp
    (hrow.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))) using 1

theorem actual_count_law (i : Row) (N : ℕ) (G : RestrictedLaw i)
    [NullSingletonClass (G.bidLaw : Measure (Bid i))] (own : Bid i) :
    FiniteLaw.ofMeasure (law i N G) (count i G own) (measurable_count i G own)=
      rawCountLaw i N G own := by
  apply FiniteLaw.ext_expect
  intro f
  rw [FiniteLaw.expect_ofMeasure,rawCountLaw_expect]
  have hi : Integrable (fun x=> f (count i G own x)) (law i N G) :=
    Integrable.of_bound ((measurable_of_countable f).comp (measurable_count i G own)).aestronglyMeasurable
      (∑k,|f k|) (ae_of_all _ (fun x=> Finset.single_le_sum
        (fun k _=> abs_nonneg (f k)) (Finset.mem_univ (count i G own x))))
  rw [law,integral_prod _ hi,integral_prod _ hi.integral_prod_left,
    LowBody.integral_probabilityMeasure]
  exact FiniteLaw.expect_congr _ (fun kind=> row_count_integral i G own kind f)

end NativeCounts
end FCAppendix.Affine.UniformFinite
