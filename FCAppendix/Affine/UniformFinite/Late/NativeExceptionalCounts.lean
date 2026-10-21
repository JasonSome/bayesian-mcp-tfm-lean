import FCAppendix.Affine.UniformFinite.Late.NativeExceptionalConditional
import FCAppendix.Affine.UniformFinite.Late.ExceptionalRoutes
import FCAppendix.Affine.UniformFinite.NativeFixedCounts

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine.UniformFinite.Late.ExceptionalCounts
open Set MeasureTheory ProbabilityTheory Filter Topology Classical Game
open Uniform05 Existence.Distributional
open scoped BigOperators

def fullCoordinateLaw (i : Row) {N : ℕ} (G : RestrictedLaw i)
    (kind : Fin N→ Fin 3) (own : ℝ) : Fin (N+1)→ Measure ℝ :=
  Fin.cons (Measure.dirac own) (fun j=> if kind j=0 then
    ExceptionalSeed.bidMeasure i G else Measure.dirac 0)

instance fullCoordinate_probability (i : Row) {N : ℕ} (G : RestrictedLaw i)
    (kind : Fin N→ Fin 3) (own : ℝ) (a : Fin (N+1)) :
    IsProbabilityMeasure (fullCoordinateLaw i G kind own a) := by
  refine Fin.cases ?_ (fun j=>?_) a
  · change IsProbabilityMeasure (Measure.dirac own)
    infer_instance
  · change IsProbabilityMeasure (if kind j=0 then ExceptionalSeed.bidMeasure i G else _)
    split_ifs <;> infer_instance

theorem focalBids_law (i : Row) {N : ℕ} (G : RestrictedLaw i)
    (kind : Fin N→ Fin 3) (own : ℝ) :
    (rowLaw N G.bidLaw : Measure (Fin N→ Bid i)).map (focalBids i kind own)=
      Measure.pi (fullCoordinateLaw i G kind own) := by
  rw [rowLaw_eq_pi]
  symm
  apply Measure.pi_eq
  intro E hE
  have hm : Measurable (focalBids i kind own) :=
    (continuous_focalBids i kind).measurable.comp (measurable_const.prodMk measurable_id)
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hE)]
  by_cases ho : own∈E 0
  · have hpre : focalBids i kind own ⁻¹' Set.univ.pi E=
        Set.univ.pi (fun j : Fin N=>
          (fun b : Bid i=> if kind j=0 then (b:ℝ) else 0) ⁻¹' E j.succ) := by
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
    · simp only [if_pos hj,ExceptionalSeed.bidMeasure,Measure.map_apply measurable_subtype_coe (hE j.succ)]
    · simp only [if_neg hj,Measure.dirac_apply' (0:ℝ) (hE j.succ)]
      by_cases hz : (0:ℝ)∈E j.succ <;>
        simp [hz,Set.indicator]
  · have hpre : focalBids i kind own ⁻¹' Set.univ.pi E=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro b hb
      exact ho (hb 0 (mem_univ 0))
    rw [hpre,measure_empty,Fin.prod_univ_succ]
    simp [fullCoordinateLaw,Measure.dirac_apply' own (hE 0),ho]

theorem fullCoordinate_lower (i : Row) {N : ℕ} (G : RestrictedLaw i)
    (kind : Fin N→ Fin 3) (own : ℝ) (a : Fin (N+1))
    (ha : a∈(focalRow kind).lower) (hne : a≠0) :
    fullCoordinateLaw i G kind own a=ExceptionalSeed.bidMeasure i G := by
  revert ha hne
  refine Fin.cases ?_ (fun j=>?_) a
  · intro _ hne; exact False.elim (hne rfl)
  · intro ha _
    have hj : kind j=0 := by simpa [focalRow,Source.countRowOfKind] using ha
    simp only [fullCoordinateLaw,Fin.cons_succ,if_pos hj]

def rowDraw (i : Row) {N : ℕ} (G : RestrictedLaw i) (own : ℝ)
    (kind : Fin N→ Fin 3) (b : Fin N→ Bid i) (s : unitInterval×unitInterval) : Allocation (N+1) :=
  let full := focalBids i kind own b
  NativeExceptionalRow.draw i G (focalRow kind) 0 full
    (ExceptionalSeed.common i G (focalRow kind) full,s)

theorem measurable_rowDraw (i : Row) {N : ℕ} (G : RestrictedLaw i) (own : ℝ)
    (kind : Fin N→ Fin 3) : Measurable (Function.uncurry (rowDraw i G own kind)) := by
  have hb : Measurable (fun x : (Fin N→Bid i)×(unitInterval×unitInterval)=>
      focalBids i kind own x.1) := by
    convert! (continuous_focalBids i kind).measurable.comp
      (measurable_const.prodMk measurable_fst) using 1
  convert! (NativeExceptionalRow.draw_joint_measurable i G (focalRow kind) 0).comp
    (hb.prodMk (((ExceptionalSeed.measurable_common i G (focalRow kind)).comp hb).prodMk measurable_snd)) using 1

theorem row_integral (i : Row) {N : ℕ} (G : RestrictedLaw i)
    [NullSingletonClass (G.bidLaw : Measure (Bid i))]
    (own : ℝ) (hown : cap i< own) (kind : Fin N→ Fin 3) (f : Allocation (N+1)→ℝ) :
    (∫b : Fin N→ Bid i,∫s,f (rowDraw i G own kind b s)
      ∂((volume : Measure unitInterval).prod volume)
      ∂(rowLaw N G.bidLaw : Measure (Fin N→ Bid i)))=
      ∫b : Fin N→ Bid i,(Exceptional.continuationLaw i G (focalRow kind)
        (focalBids i kind own b) 0).expect f ∂(rowLaw N G.bidLaw : Measure (Fin N→ Bid i)) := by
  have h := ExceptionalSeed.fixed_exception_integral i G (focalRow kind) 0
    (Noisy.focal_mem_lower kind) own hown (fullCoordinateLaw i G kind own) rfl
    (fullCoordinate_lower i G kind own) f
  have hm : Measurable (focalBids i kind own) := by
    convert! (continuous_focalBids i kind).measurable.comp
      (measurable_const.prodMk measurable_id) using 1
  rw [← focalBids_law i G kind own,
    integral_map hm.aemeasurable (ExceptionalSeed.measurable_test i G (focalRow kind) 0 f).aestronglyMeasurable,
    integral_map hm.aemeasurable
      (ExceptionalSeed.measurable_continuation_expect i G (focalRow kind) 0 f).aestronglyMeasurable] at h
  exact h

abbrev Sample (i : Row) (N : ℕ) := NativeCounts.Sample i N

def draw (i : Row) {N : ℕ} (G : RestrictedLaw i) (own : ℝ) (x : Sample i N) : Allocation (N+1) :=
  rowDraw i G own x.1.1 x.1.2 x.2

theorem measurable_draw (i : Row) {N : ℕ} (G : RestrictedLaw i) (own : ℝ) :
    Measurable (draw (N:=N) i G own) := by
  have hrow : Measurable (fun x : (Fin N→ Fin 3)×((Fin N→ Bid i)×(unitInterval×unitInterval))=>
      rowDraw i G own x.1 x.2.1 x.2.2) :=
    measurable_from_prod_countable_right (measurable_rowDraw i G own)
  convert! hrow.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)) using 1

theorem draw_integral (i : Row) (N : ℕ) (G : RestrictedLaw i)
    [NullSingletonClass (G.bidLaw : Measure (Bid i))] (own : ℝ) (hown : cap i< own)
    (f : Allocation (N+1)→ℝ) :
    (∫x,f (draw i G own x) ∂NativeCounts.law i N G)=
      (categoryRowLaw i N).expect (fun kind=>∫b : Fin N→ Bid i,
        (Exceptional.continuationLaw i G (focalRow kind) (focalBids i kind own b) 0).expect f
        ∂(rowLaw N G.bidLaw : Measure (Fin N→ Bid i))) := by
  have hi : Integrable (fun x=> f (draw i G own x)) (NativeCounts.law i N G) :=
    Integrable.of_bound ((measurable_of_countable f).comp (measurable_draw i G own)).aestronglyMeasurable
      (∑P,|f P|) (ae_of_all _ (fun x=> NativeRow.finite_bound f _))
  rw [NativeCounts.law,integral_prod _ hi,integral_prod _ hi.integral_prod_left,
    LowBody.integral_probabilityMeasure]
  exact FiniteLaw.expect_congr _ (fun kind=> row_integral i G own hown kind f)

def actualCountLaw (i : Row) (N : ℕ) (G : RestrictedLaw i) (own : ℝ) : FiniteLaw (Fin 3) :=
  FiniteLaw.ofMeasure (NativeCounts.law i N G) (fun x=> pairCount 0 (draw i G own x))
    ((measurable_of_countable (pairCount 0)).comp (measurable_draw i G own))

theorem actualCountLaw_expect (i : Row) (N : ℕ) (G : RestrictedLaw i)
    [NullSingletonClass (G.bidLaw : Measure (Bid i))] (own : ℝ) (hown : cap i< own) (f : Fin 3→ℝ) :
    (actualCountLaw i N G own).expect f=
      (categoryRowLaw i N).expect (fun kind=>∫b : Fin N→ Bid i,
        (Exceptional.continuationLaw i G (focalRow kind) (focalBids i kind own b) 0).expect
          (fun P=> f (pairCount 0 P)) ∂(rowLaw N G.bidLaw : Measure (Fin N→ Bid i))) := by
  rw [actualCountLaw,FiniteLaw.expect_ofMeasure]
  convert! draw_integral i N G own hown (fun P=>f (pairCount 0 P)) using 1

theorem broadcast_utility (i : Row) (N : ℕ) (G : RestrictedLaw i)
    [NullSingletonClass (G.bidLaw : Measure (Bid i))]
    (v own : ℝ) (hown : cap i< own) :
    (∫x,pairPayoff (eta i) v own 0 (draw i G own x) ∂NativeCounts.law i N G)=
      Exceptional.rawUtility i N G v own := by
  rw [draw_integral i N G own hown]
  simp only [Exceptional.rawUtility,Exceptional.rowPayoff,focalBids_zero]

theorem named_recipient_utility (i : Row) (N : ℕ) (G : RestrictedLaw i)
    [NullSingletonClass (G.bidLaw : Measure (Bid i))]
    (j : Fin 2) (v own : ℝ) (hown : cap i< own) :
    (∫x,(v-own)*routeIndicator j 0 (draw i G own x) ∂NativeCounts.law i N G)=
      Exceptional.rawRouteUtility i N G j v own := by
  have h:=draw_integral i N G own hown (fun P=>(v-own)*routeIndicator j 0 P)
  simpa only [Exceptional.rawRouteUtility,Exceptional.rowRoutePayoff,focalBids_zero] using h

end FCAppendix.Affine.UniformFinite.Late.ExceptionalCounts
