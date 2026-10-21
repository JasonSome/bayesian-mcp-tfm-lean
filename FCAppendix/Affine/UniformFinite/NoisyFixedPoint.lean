import FCAppendix.Affine.UniformFinite.FiniteExperiment
import FCAppendix.Affine.UniformFinite.SourcePayoffContinuity
import FCAppendix.Affine.LowBody.BoundedNullWeakIntegral
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Sequences

set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 1000

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology Classical TopologicalSpace
open Existence.Distributional
open scoped BigOperators

namespace Noisy

def Parameter (i : Row) := Joint i × (Value i × unitInterval)

instance parameterTopology (i : Row) : TopologicalSpace (Parameter i) :=
  inferInstanceAs (TopologicalSpace (Joint i × (Value i × unitInterval)))

instance parameterMeasurableSpace (i : Row) : MeasurableSpace (Parameter i) := borel (Parameter i)

instance parameterBorel (i : Row) : BorelSpace (Parameter i) := ⟨rfl⟩

instance parameterCompact (i : Row) : CompactSpace (Parameter i) :=
  inferInstanceAs (CompactSpace (Joint i × (Value i × unitInterval)))

instance parameterMetrizable (i : Row) : MetrizableSpace (Parameter i) :=
  inferInstanceAs (MetrizableSpace (Joint i × (Value i × unitInterval)))
abbrev Sample (i : Row) (N : ℕ) := Parameter i × ((Fin N → Bid i) × unitInterval)

def zeroBid (i : Row) : Bid i := ⟨0, le_rfl, (Uniform05.cap_pos i).le⟩

def cappedFocalBids (i : Row) {N : ℕ} (kind : Fin N → Fin 3)
    (own : Bid i) (b : Fin N → Bid i) : Fin (N+1) → Bid i :=
  Fin.cons own (fun j => if kind j=0 then b j else zeroBid i)

theorem continuous_cappedFocalBids (i : Row) {N : ℕ} (kind : Fin N → Fin 3) :
    Continuous (fun p : Bid i × (Fin N → Bid i) => cappedFocalBids i kind p.1 p.2) := by
  apply continuous_pi
  intro a
  refine Fin.cases ?_ (fun j => ?_) a
  · exact continuous_fst
  · by_cases hj : kind j=0
    · simpa [cappedFocalBids, hj, Function.comp_def] using (continuous_apply j).comp continuous_snd
    · simp only [cappedFocalBids, Fin.cons_succ, if_neg hj]
      exact continuous_const

theorem cappedFocalBids_real (i : Row) {N : ℕ} (kind : Fin N → Fin 3)
    (own : Bid i) (b : Fin N → Bid i) :
    (fun a => (cappedFocalBids i kind own b a : ℝ)) = focalBids i kind own b := by
  funext a
  refine Fin.cases ?_ (fun j => ?_) a
  · rfl
  · by_cases hj : kind j=0 <;> simp [cappedFocalBids, focalBids, zeroBid, hj]

theorem focal_mem_lower {N : ℕ} (kind : Fin N → Fin 3) :
    (0 : Fin (N+1)) ∈ (focalRow kind).lower := by
  simp [focalRow, Source.countRowOfKind]

theorem lowerBids_focalBids (i : Row) {N : ℕ} (kind : Fin N → Fin 3)
    (own : ℝ) (b : Fin N → Bid i) :
    Source.lowerBids (focalRow kind) (focalBids i kind own b) = focalBids i kind own b := by
  funext a
  refine Fin.cases ?_ (fun j => ?_) a
  · simp [Source.lowerBids, focal_mem_lower]
  · by_cases hj : kind j=0 <;>
      simp [Source.lowerBids, focalRow, Source.countRowOfKind, focalBids, hj]

def environment (i : Row) (eps : unitInterval) (p : Parameter i) : Uniform05.RestrictedLaw i :=
  restrictedLaw i (eps,p.1)

theorem continuous_environment (i : Row) (eps : unitInterval) : Continuous (environment i eps) :=
  (continuous_restrictedLaw i).comp (continuous_const.prodMk continuous_fst)

def input (i : Row) {N : ℕ} (eps : unitInterval) (kind : Fin N → Fin 3)
    (x : Sample i N) : ℝ × SourceContinuity.State i (N+1) :=
  ((x.1.2.1 : ℝ), environment i eps x.1,
    cappedFocalBids i kind (noisyBid i (eps,(x.1.2,x.2.2))) x.2.1)

theorem continuous_input (i : Row) {N : ℕ} (eps : unitInterval) (kind : Fin N → Fin 3) :
    Continuous (input i eps kind) := by
  have hown : Continuous (fun x : Sample i N => noisyBid i (eps,(x.1.2,x.2.2))) :=
    (continuous_noisyBid i).comp (by fun_prop)
  exact (continuous_subtype_val.comp (continuous_fst.snd.fst)).prodMk
    (((continuous_environment i eps).comp continuous_fst).prodMk
      ((continuous_cappedFocalBids i kind).comp (hown.prodMk continuous_snd.fst)))

def rowFunction (i : Row) {N : ℕ} (eps : unitInterval) (kind : Fin N → Fin 3)
    (x : Sample i N) : ℝ :=
  rowPayoff i (environment i eps x.1) (focalRow kind) x.1.2.1
    (focalBids i kind (noisyBid i (eps,(x.1.2,x.2.2))) x.2.1) 0

theorem rowFunction_input (i : Row) {N : ℕ} (eps : unitInterval) (kind : Fin N → Fin 3)
    (x : Sample i N) :
    rowFunction i eps kind x =
      rowPayoff i (input i eps kind x).2.1 (focalRow kind) (input i eps kind x).1
        (SourceContinuity.bids i (input i eps kind x).2) 0 := by
  change rowPayoff i (environment i eps x.1) (focalRow kind) x.1.2.1
    (focalBids i kind (noisyBid i (eps,(x.1.2,x.2.2))) x.2.1) 0 = _
  congr 1
  exact (cappedFocalBids_real i kind _ _).symm

theorem measurable_rowFunction (i : Row) {N : ℕ} (eps : unitInterval) (kind : Fin N → Fin 3) :
    Measurable (rowFunction i eps kind) := by
  have he : rowFunction i eps kind = (fun x : Sample i N =>
      rowPayoff i (input i eps kind x).2.1 (focalRow kind) (input i eps kind x).1
        (SourceContinuity.bids i (input i eps kind x).2) 0) := funext (rowFunction_input i eps kind)
  rw [he]
  exact (SourceContinuity.measurable_rowPayoff i (focalRow kind) 0 (focal_mem_lower kind)).comp
    (continuous_input i eps kind).measurable

theorem rowFunction_value_bound (i : Row) {N : ℕ} (eps : unitInterval)
    (kind : Fin N → Fin 3) (x : Sample i N) : |rowFunction i eps kind x| ≤ 3*(x.1.2.1 : ℝ) :=
  noisyRowPayoff_bound i eps x.1.1 x.1.2.1 x.1.2.2 x.2.2 kind x.2.1

theorem rowFunction_bound (i : Row) {N : ℕ} (eps : unitInterval)
    (kind : Fin N → Fin 3) (x : Sample i N) : |rowFunction i eps kind x| ≤ 3*Uniform05.t i :=
  (rowFunction_value_bound i eps kind x).trans
    (mul_le_mul_of_nonneg_left x.1.2.1.property.2 (by norm_num))

def actualBids (i : Row) {N : ℕ} (eps : unitInterval) (kind : Fin N → Fin 3)
    (x : Sample i N) : Fin (N+1) → ℝ :=
  focalBids i kind (noisyBid i (eps,(x.1.2,x.2.2))) x.2.1

theorem continuous_actualBids (i : Row) {N : ℕ} (eps : unitInterval) (kind : Fin N → Fin 3) :
    Continuous (actualBids i eps kind) :=
  (continuous_focalBids i kind).comp
    ((continuous_subtype_val.comp ((continuous_noisyBid i).comp (by fun_prop))).prodMk
      continuous_snd.fst)

def badSet (i : Row) {N : ℕ} (eps : unitInterval) (kind : Fin N → Fin 3) : Set (Sample i N) :=
  {x | actualBids i eps kind x 0 ≤ 0 ∨
    (∃ a ∈ (focalRow kind).lower, actualBids i eps kind x a = Uniform05.t i/2) ∨
    ∃ P Q : Allocation (N+1), LowBody.focalCopy P 0 ≠ LowBody.focalCopy Q 0 ∧
      LowBody.CompleteInformation.potential (Uniform05.kappa i) (actualBids i eps kind x) P.1 P.2 =
      LowBody.CompleteInformation.potential (Uniform05.kappa i) (actualBids i eps kind x) Q.1 Q.2}

theorem isClosed_badSet (i : Row) {N : ℕ} (eps : unitInterval) (kind : Fin N → Fin 3) :
    IsClosed (badSet i eps kind) := by
  let b := actualBids i eps kind
  have hc := continuous_actualBids i eps kind
  have he : badSet i eps kind =
      {x | b x 0 ≤ 0} ∪ ((⋃ a : Fin (N+1),
        {x | a ∈ (focalRow kind).lower ∧ b x a = Uniform05.t i/2}) ∪
      ⋃ P : Allocation (N+1), ⋃ Q : Allocation (N+1),
        {x | LowBody.focalCopy P 0 ≠ LowBody.focalCopy Q 0 ∧
          LowBody.CompleteInformation.potential (Uniform05.kappa i) (b x) P.1 P.2 =
          LowBody.CompleteInformation.potential (Uniform05.kappa i) (b x) Q.1 Q.2}) := by
    ext x
    simp only [badSet, b, mem_setOf_eq, mem_union, mem_iUnion]
  rw [he]
  apply (isClosed_le ((continuous_apply 0).comp hc) continuous_const).union
  apply IsClosed.union
  · apply isClosed_iUnion_of_finite
    intro a
    by_cases ha : a ∈ (focalRow kind).lower
    · simpa only [ha, true_and, Function.comp_def, b] using isClosed_eq ((continuous_apply a).comp hc) continuous_const
    · simpa only [ha, false_and, Set.setOf_false] using isClosed_empty
  · apply isClosed_iUnion_of_finite
    intro P
    apply isClosed_iUnion_of_finite
    intro Q
    by_cases he : LowBody.focalCopy P 0 = LowBody.focalCopy Q 0
    · simpa only [he, ne_eq, not_true_eq_false, false_and, Set.setOf_false] using isClosed_empty
    · simpa only [he, ne_eq, not_false_eq_true, true_and, Function.comp_def] using
        isClosed_eq ((LowBody.continuous_potential (Uniform05.kappa i) P).comp hc)
          ((LowBody.continuous_potential (Uniform05.kappa i) Q).comp hc)

theorem continuousAt_rowFunction_of_not_bad (i : Row) {N : ℕ} (eps : unitInterval)
    (kind : Fin N → Fin 3) (x : Sample i N) (hx : x ∉ badSet i eps kind) :
    ContinuousAt (rowFunction i eps kind) x := by
  have hp : 0 < actualBids i eps kind x 0 := lt_of_not_ge (fun h => hx (Or.inl h))
  have hcut : ∀ a ∈ (focalRow kind).lower, actualBids i eps kind x a ≠ Uniform05.t i/2 := by
    intro a ha he
    exact hx (Or.inr (Or.inl ⟨a,ha,he⟩))
  have hgeneric : ∀ P Q : (Source.lowerTemplate (focalRow kind)).Candidate,
      LowBody.CompleteInformation.potential (Uniform05.kappa i) (actualBids i eps kind x) P.val.1 P.val.2 =
      LowBody.CompleteInformation.potential (Uniform05.kappa i) (actualBids i eps kind x) Q.val.1 Q.val.2 →
      LowBody.focalCopy P.val 0 = LowBody.focalCopy Q.val 0 := by
    intro P Q he
    by_contra hn
    exact hx (Or.inr (Or.inr ⟨P.val,Q.val,hn,he⟩))
  have he : rowFunction i eps kind = fun z : Sample i N =>
    rowPayoff i (input i eps kind z).2.1 (focalRow kind) (input i eps kind z).1
      (SourceContinuity.bids i (input i eps kind z).2) 0 :=
    funext (rowFunction_input i eps kind)
  rw [he]
  have hbid : SourceContinuity.bids i (input i eps kind x).2 = actualBids i eps kind x :=
    cappedFocalBids_real i kind _ _
  apply (SourceContinuity.continuousAt_rowPayoff i (focalRow kind) 0 (focal_mem_lower kind)
    (input i eps kind x) ?_ ?_ ?_).comp (continuous_input i eps kind).continuousAt
  · rw [hbid]
    exact hp
  · rw [hbid]
    exact hcut
  · rw [hbid, actualBids, lowerBids_focalBids]
    exact hgeneric

def sampleLaw (i : Row) (N : ℕ) (eps : unitInterval) (p : Parameter i) :
    ProbabilityMeasure (Sample i N) :=
  productLaw (diracProba p)
    (productLaw (rowLaw N (environment i eps p).bidLaw)
      (⟨volume,inferInstance⟩ : ProbabilityMeasure unitInterval))

theorem continuous_sampleLaw (i : Row) (N : ℕ) (eps : unitInterval) :
    Continuous (sampleLaw i N eps) := by
  have hG := Uniform05.RestrictedLaw.continuous_bidLaw.comp (continuous_environment i eps)
  exact continuous_productLaw.comp (continuous_diracProba.prodMk
    (continuous_productLaw.comp (((continuous_rowLaw N).comp hG).prodMk continuous_const)))

theorem integral_sampleLaw (i : Row) {N : ℕ} (eps : unitInterval)
    (kind : Fin N → Fin 3) (p : Parameter i) :
    (∫ x, rowFunction i eps kind x ∂(sampleLaw i N eps p : Measure (Sample i N))) =
      ∫ b : Fin N → Bid i, (∫ z : unitInterval,
        rowPayoff i (environment i eps p) (focalRow kind) p.2.1
          (focalBids i kind (noisyBid i (eps,(p.2,z))) b) 0)
        ∂(rowLaw N (environment i eps p).bidLaw : Measure (Fin N → Bid i)) := by
  let C := 3*Uniform05.t i
  have hi : Integrable (rowFunction i eps kind) (sampleLaw i N eps p : Measure (Sample i N)) :=
    (integrable_const C).mono' (measurable_rowFunction i eps kind).aestronglyMeasurable
      (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using rowFunction_bound i eps kind x))
  have his : Integrable (fun y : (Fin N → Bid i) × unitInterval => rowFunction i eps kind (p,y))
      ((rowLaw N (environment i eps p).bidLaw : Measure (Fin N → Bid i)).prod volume) :=
    (integrable_const C).mono'
      ((measurable_rowFunction i eps kind).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (ae_of_all _ (fun y => by simpa only [Real.norm_eq_abs] using rowFunction_bound i eps kind (p,y)))
  change (∫ x, rowFunction i eps kind x ∂(Measure.dirac p).prod
    ((rowLaw N (environment i eps p).bidLaw : Measure (Fin N → Bid i)).prod volume)) = _
  have hi' : Integrable (rowFunction i eps kind)
      ((Measure.dirac p).prod
        ((rowLaw N (environment i eps p).bidLaw : Measure (Fin N → Bid i)).prod volume)) := hi
  rw [integral_prod _ hi', integral_dirac]
  exact integral_prod _ his

theorem ae_affine_ties {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ s : ℝ} (hκ : 0 < κ) (hs : s ≠ 0) (a : ℝ) (b : ι → ℝ) (i : ι) :
    ∀ᵐ z : unitInterval ∂volume, ∀ P Q : Finset ι × Finset ι,
      LowBody.CompleteInformation.potential κ (Literal.affineFocal i a s b z) P.1 P.2 =
      LowBody.CompleteInformation.potential κ (Literal.affineFocal i a s b z) Q.1 Q.2 →
      LowBody.focalCopy P i = LowBody.focalCopy Q i := by
  apply ae_all_iff.mpr
  intro P
  apply ae_all_iff.mpr
  intro Q
  by_cases hpq : LowBody.focalCopy P i = LowBody.focalCopy Q i
  · exact ae_of_all _ (fun _ _ => hpq)
  · have hc : (LowBody.copyCoefficient κ P i-LowBody.copyCoefficient κ Q i)*s ≠ 0 :=
      mul_ne_zero (sub_ne_zero.mpr (LowBody.copyCoefficient_ne_of_focalCopy_ne hκ P Q i hpq)) hs
    let C := LowBody.CompleteInformation.potential κ (Function.update b i a) P.1 P.2 -
      LowBody.CompleteInformation.potential κ (Function.update b i a) Q.1 Q.2
    let f : unitInterval → ℝ := fun z =>
      (LowBody.copyCoefficient κ P i-LowBody.copyCoefficient κ Q i)*s*(z:ℝ)+C
    have hf : Function.Injective f := by
      intro z w he
      apply Subtype.ext
      dsimp only [f] at he
      exact mul_left_cancel₀ hc (add_right_cancel he)
    filter_upwards [LowBody.ae_injective_ne volume f hf 0] with z hz he
    apply False.elim (hz ?_)
    rw [Literal.potential_affineFocal, Literal.potential_affineFocal] at he
    dsimp only [f,C]
    linarith

theorem focalBids_affine (i : Row) {N : ℕ} (eps : unitInterval) (kind : Fin N → Fin 3)
    (v : Value i) (q z : unitInterval) (b : Fin N → Bid i) :
    focalBids i kind (noisyBid i (eps,((v,q),z))) b =
      Literal.affineFocal 0
        (Uniform05.floorBid i v+width i v*((1-(eps:ℝ))*(q:ℝ)))
        (width i v*(eps:ℝ)) (focalBids i kind 0 b) z := by
  funext a
  refine Fin.cases ?_ (fun j => ?_) a
  · simp only [focalBids_zero, Literal.affineFocal, Function.update_self]
    change noisyRealBid i eps v q z = _
    unfold noisyRealBid
    ring
  · rw [Literal.affineFocal, Function.update_of_ne (Fin.succ_ne_zero j)]
    simp only [focalBids_succ]

theorem ae_rival_no_seed_cut (i : Row) (N : ℕ) (eps : unitInterval)
    (heps : 0 < (eps:ℝ)) (p : Parameter i) :
    ∀ᵐ b ∂(rowLaw N (environment i eps p).bidLaw : Measure (Fin N → Bid i)),
      ∀ j, (b j : ℝ) ≠ Uniform05.t i/2 := by
  letI := physical_bid_atomless i eps heps p.1
  apply ae_all_iff.mpr
  intro j
  have hbase : ∀ᵐ (b : Bid i) ∂(bidLaw i (eps,p.1) : Measure (Bid i)), (b:ℝ) ≠ Uniform05.t i/2 :=
    LowBody.ae_injective_ne (bidLaw i (eps,p.1) : Measure (Bid i))
      (fun b : Bid i => (b:ℝ)) Subtype.val_injective (Uniform05.t i/2)
  have hs : MeasurableSet {b : Bid i | (b:ℝ) ≠ Uniform05.t i/2} :=
    (measurableSet_eq_fun measurable_subtype_coe measurable_const).compl
  apply (ae_map_iff (μ := (rowLaw N (environment i eps p).bidLaw : Measure (Fin N → Bid i)))
    (measurable_pi_apply j).aemeasurable hs).mp
  rw [rowLaw_coordinate]
  simpa only [environment, restrictedLaw_bidLaw] using hbase

theorem sample_bad_null (i : Row) {N : ℕ} (eps : unitInterval) (heps : 0 < (eps:ℝ))
    (kind : Fin N → Fin 3) (p : Parameter i) (hv : 0 < (p.2.1:ℝ)) :
    (sampleLaw i N eps p : Measure (Sample i N)) (badSet i eps kind) = 0 := by
  have hm : MeasurableSet {x : Sample i N | x ∉ badSet i eps kind} :=
    (isClosed_badSet i eps kind).measurableSet.compl
  apply measure_eq_zero_iff_ae_notMem.mpr
  change ∀ᵐ x ∂(Measure.dirac p).prod
    ((rowLaw N (environment i eps p).bidLaw : Measure (Fin N → Bid i)).prod volume), _
  apply (Measure.ae_prod_iff_ae_ae hm).mpr
  simp only [ae_dirac_eq, Filter.eventually_pure]
  have hm' : MeasurableSet {y : (Fin N → Bid i) × unitInterval | (p,y) ∉ badSet i eps kind} :=
    hm.preimage (measurable_const.prodMk measurable_id)
  apply (Measure.ae_prod_iff_ae_ae hm').mpr
  filter_upwards [ae_rival_no_seed_cut i N eps heps p] with b hb
  have hown : Function.Injective (fun z : unitInterval => (noisyBid i (eps,(p.2,z)) : ℝ)) :=
    Subtype.val_injective.comp (noisyBid_injective_noise i eps heps p.2 hv)
  have hzero := LowBody.ae_injective_ne volume _ hown 0
  have hcut := LowBody.ae_injective_ne volume _ hown (Uniform05.t i/2)
  have hs : width i p.2.1*(eps:ℝ) ≠ 0 := (mul_pos (width_positive i p.2.1 hv) heps).ne'
  have ht := ae_affine_ties (Uniform05.kappa_range i).1 hs
    (Uniform05.floorBid i p.2.1+width i p.2.1*((1-(eps:ℝ))*(p.2.2:ℝ)))
    (focalBids i kind 0 b) (0 : Fin (N+1))
  filter_upwards [hzero,hcut,ht] with z hz hzc hzt
  have hpositive : 0 < (noisyBid i (eps,(p.2,z)) : ℝ) :=
    lt_of_le_of_ne (noisyBid i (eps,(p.2,z))).property.1 (Ne.symm hz)
  rintro (hn | hc | ⟨P,Q,hPQ,he⟩)
  · exact not_le_of_gt hpositive hn
  · obtain ⟨a,ha,hea⟩ := hc
    revert ha hea
    refine Fin.cases ?_ (fun j => ?_) a
    · intro _ he
      exact hzc he
    · intro hj he
      have hk : kind j=0 := by simpa [focalRow, Source.countRowOfKind] using hj
      exact hb j (by simpa [actualBids, focalBids, hk] using he)
  · apply hPQ
    apply hzt P Q
    change LowBody.CompleteInformation.potential (Uniform05.kappa i)
      (focalBids i kind (noisyBid i (eps,(p.2,z))) b) P.1 P.2 =
      LowBody.CompleteInformation.potential (Uniform05.kappa i)
      (focalBids i kind (noisyBid i (eps,(p.2,z))) b) Q.1 Q.2 at he
    rw [focalBids_affine] at he
    exact he

theorem tendsto_row_integral (i : Row) {N : ℕ} (eps : unitInterval) (heps : 0 < (eps:ℝ))
    (kind : Fin N → Fin 3) (p : ℕ → Parameter i) (p₀ : Parameter i)
    (hp : Tendsto p atTop (𝓝 p₀)) (hv : 0 < (p₀.2.1:ℝ)) :
    Tendsto (fun n => ∫ x, rowFunction i eps kind x ∂(sampleLaw i N eps (p n) : Measure (Sample i N)))
      atTop (𝓝 (∫ x, rowFunction i eps kind x ∂(sampleLaw i N eps p₀ : Measure (Sample i N)))) := by
  letI : MetricSpace (Sample i N) := TopologicalSpace.metrizableSpaceMetric (Sample i N)
  exact LowBody.tendsto_integral_of_closed_null_discontinuities
    (rowFunction i eps kind) (measurable_rowFunction i eps kind) (badSet i eps kind)
    (isClosed_badSet i eps kind) (continuousAt_rowFunction_of_not_bad i eps kind)
    (show 0 ≤ 3*Uniform05.t i by have h := Uniform05.t_pos i; positivity) (rowFunction_bound i eps kind)
    (fun n => sampleLaw i N eps (p n)) (sampleLaw i N eps p₀)
    ((continuous_sampleLaw i N eps).continuousAt.tendsto.comp hp)
    (sample_bad_null i eps heps kind p₀ hv)

end Noisy

theorem continuous_expectedUtility (i : Row) (N : ℕ) (eps : unitInterval)
    (heps : 0 < (eps:ℝ)) :
    Continuous (fun p : Joint i × (Value i × unitInterval) =>
      expectedUtility i N eps p.1 p.2.1 p.2.2) := by
  rw [continuous_iff_seqContinuous]
  intro p p₀ hp
  by_cases hv : (p₀.2.1:ℝ)=0
  · have hzero : expectedUtility i N eps p₀.1 p₀.2.1 p₀.2.2=0 := by
      apply abs_eq_zero.mp
      exact le_antisymm (by simpa only [hv,mul_zero] using
        expectedUtility_bound i N eps p₀.1 p₀.2.1 p₀.2.2) (abs_nonneg _)
    have hvalue : Tendsto (fun n => 3*(p n).2.1.val) atTop (𝓝 0) := by
      have hc : Continuous (fun x : Joint i × (Value i × unitInterval) => 3*x.2.1.val) := by fun_prop
      simpa only [hv,mul_zero, Function.comp_def] using (hc.tendsto p₀).comp hp
    change Tendsto (fun n => expectedUtility i N eps (p n).1 (p n).2.1 (p n).2.2) atTop
      (𝓝 (expectedUtility i N eps p₀.1 p₀.2.1 p₀.2.2))
    rw [hzero]
    apply squeeze_zero_norm' _ hvalue
    exact Eventually.of_forall (fun n => by
      simpa only [Real.norm_eq_abs] using
        (expectedUtility_bound i N eps (p n).1 (p n).2.1 (p n).2.2))
  · have hvpos : 0 < (p₀.2.1:ℝ) := lt_of_le_of_ne p₀.2.1.property.1 (Ne.symm hv)
    have hrow (kind : Fin N → Fin 3) := Noisy.tendsto_row_integral i eps heps kind p p₀ hp hvpos
    simp_rw [Noisy.integral_sampleLaw] at hrow
    unfold expectedUtility FiniteLaw.expect
    apply tendsto_finsetSum
    intro kind _
    exact (hrow kind).const_mul _

theorem exists_noisy_restricted_law (i : Row) (N : ℕ) (eps : unitInterval)
    (heps : 0 < (eps:ℝ)) :
    ∃ (pi : Joint i) (sigma : Kernel (Value i) unitInterval),
      IsMarkovKernel sigma ∧
      lowerMeasure i ⊗ₘ sigma = (pi.1 : Measure (Value i × unitInterval)) ∧
      NoisyIC i N eps pi ∧
      (∀ᵐ v ∂lowerMeasure i, ∀ᵐ q ∂sigma v, ∀ q' : unitInterval,
        expectedUtility i N eps pi v q' ≤ expectedUtility i N eps pi v q) := by
  obtain ⟨pi,sigma,hmark,hdis,hjoint,hconditional⟩ := exists_symmetric_law (lowerMeasure i)
    (fun p : Joint i × (Value i × unitInterval) => expectedUtility i N eps p.1 p.2.1 p.2.2)
    (continuous_expectedUtility i N eps heps)
  exact ⟨pi,sigma,hmark,hdis,hjoint,hconditional⟩

end FCAppendix.Affine.UniformFinite
