import FCAppendix.Affine.UniformFinite.NoisyFixedPoint
import FCAppendix.Affine.UniformFinite.RestrictedICAdapters
import FCAppendix.Affine.UniformFinite.FocalSeedContinuity
import FCAppendix.Affine.UniformFinite.RestrictedCompact
import FCAppendix.Affine.LowBody.NullHyperplanes

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology Classical
open Existence.Distributional
open scoped BigOperators

namespace ExactTests

def kindFour {N : ℕ} (kind : Fin N→ Fin 3) : Fin N→ Fin 4 :=
  fun j=> if kind j=0 then 0 else 1

lemma focalBids_as_pattern {N : ℕ} (i : Row) (kind : Fin N→ Fin 3)
    (own : ℝ) (b : Fin N→ Bid i) :
    focalBids i kind own b=LowBody.actualPatternBids (kindFour kind) (Uniform05.cap i) own b := by
  funext a
  refine Fin.cases ?_ (fun j=>?_) a
  · rfl
  · by_cases h : kind j=0 <;> simp [focalBids,LowBody.actualPatternBids,kindFour,h]

theorem ae_rival_ties {N : ℕ} (i : Row) (G : Uniform05.RestrictedLaw i)
    [NullSingletonClass (G.bidLaw : Measure (Bid i))] (kind : Fin N→ Fin 3)
    (own : ℝ) (hown : own≠0) :
    ∀ᵐb∂(rowLaw N G.bidLaw : Measure (Fin N→ Bid i)),∀P Q : Allocation (N+1),
      LowBody.CompleteInformation.potential (Uniform05.kappa i) (focalBids i kind own b) P.1 P.2=
        LowBody.CompleteInformation.potential (Uniform05.kappa i) (focalBids i kind own b) Q.1 Q.2→
      LowBody.focalCopy P 0=LowBody.focalCopy Q 0 := by
  rw [rowLaw_eq_pi]
  simpa only [← focalBids_as_pattern i kind] using
    LowBody.ae_pattern_ties_same_focalCopy (Uniform05.kappa_range i).1 hown
      (G.bidLaw : Measure (Bid i)) (kindFour kind)

theorem ae_rival_cut {N : ℕ} (i : Row) (G : Uniform05.RestrictedLaw i)
    [NullSingletonClass (G.bidLaw : Measure (Bid i))] :
    ∀ᵐb∂(rowLaw N G.bidLaw : Measure (Fin N→ Bid i)),∀j,(b j:ℝ)≠Uniform05.t i/2 := by
  apply ae_all_iff.mpr
  intro j
  have h:=LowBody.ae_injective_ne (G.bidLaw : Measure (Bid i))
    (fun b : Bid i=>(b:ℝ)) Subtype.val_injective (Uniform05.t i/2)
  have hs : MeasurableSet {b : Bid i | (b:ℝ)≠Uniform05.t i/2} := by measurability
  apply (ae_map_iff (μ := (rowLaw N G.bidLaw : Measure (Fin N→Bid i)))
    (measurable_pi_apply j).aemeasurable hs).mp
  rwa [rowLaw_coordinate]

abbrev Mode := Option unitInterval
def chosen {i : Row} (mode : Mode) (p : Value i×unitInterval) : unitInterval := mode.getD p.2

lemma continuous_chosen (i : Row) (mode : Mode) : Continuous (chosen (i:=i) mode) := by
  cases mode
  · exact continuous_snd
  · exact continuous_const

def Parameter (i : Row) := unitInterval×Joint i

instance parameterTopology (i : Row) : TopologicalSpace (Parameter i) :=
  inferInstanceAs (TopologicalSpace (unitInterval×Joint i))

instance parameterMeasurableSpace (i : Row) : MeasurableSpace (Parameter i) := borel (Parameter i)
instance parameterBorel (i : Row) : BorelSpace (Parameter i) := ⟨rfl⟩
instance parameterCompact (i : Row) : CompactSpace (Parameter i) :=
  inferInstanceAs (CompactSpace (unitInterval×Joint i))
instance parameterMetrizable (i : Row) : TopologicalSpace.MetrizableSpace (Parameter i) :=
  inferInstanceAs (TopologicalSpace.MetrizableSpace (unitInterval×Joint i))

abbrev Sample (i : Row) (N : ℕ) :=
  Parameter i × ((Value i×unitInterval) × ((Fin N→ Bid i)×unitInterval))

def repack (i : Row) {N : ℕ} (mode : Mode) (x : Sample i N) : Noisy.Sample i N :=
  ((x.1.2,(x.2.1.1,chosen mode x.2.1)),x.2.2)

def own (i : Row) {N : ℕ} (mode : Mode) (x : Sample i N) : Bid i :=
  noisyBid i (x.1.1,((x.2.1.1,chosen mode x.2.1),x.2.2.2))

lemma continuous_own (i : Row) {N : ℕ} (mode : Mode) : Continuous (own (N:=N) i mode) := by
  unfold own
  apply (continuous_noisyBid i).comp
  have hc:=continuous_chosen i mode
  fun_prop

def rowInput (i : Row) {N : ℕ} (mode : Mode) (kind : Fin N→ Fin 3)
    (x : Sample i N) : ℝ×SourceContinuity.State i (N+1) :=
  (x.2.1.1,restrictedLaw i x.1,Noisy.cappedFocalBids i kind (own i mode x) x.2.2.1)

lemma continuous_rowInput (i : Row) {N : ℕ} (mode : Mode) (kind : Fin N→ Fin 3) :
    Continuous (rowInput i mode kind) := by
  have hown:=continuous_own (N:=N) i mode
  have hG : Continuous (fun x : Sample i N => restrictedLaw i x.1) :=
    (continuous_restrictedLaw i).comp continuous_fst
  have hb : Continuous (fun x : Sample i N =>
      Noisy.cappedFocalBids i kind (own i mode x) x.2.2.1) :=
    (Noisy.continuous_cappedFocalBids i kind).comp (hown.prodMk (by fun_prop))
  exact (show Continuous (fun x : Sample i N=>(x.2.1.1:ℝ)) from by fun_prop).prodMk
    (hG.prodMk hb)

def rowFunction (i : Row) {N : ℕ} (mode : Mode) (kind : Fin N→ Fin 3) (x : Sample i N) : ℝ :=
  rowPayoff i (restrictedLaw i x.1) (focalRow kind) x.2.1.1
    (focalBids i kind (own i mode x) x.2.2.1) 0

lemma rowFunction_input (i : Row) {N : ℕ} (mode : Mode) (kind : Fin N→ Fin 3) (x : Sample i N) :
    rowFunction i mode kind x=rowPayoff i (rowInput i mode kind x).2.1 (focalRow kind)
      (rowInput i mode kind x).1 (SourceContinuity.bids i (rowInput i mode kind x).2) 0 := by
  change rowPayoff i (restrictedLaw i x.1) (focalRow kind) x.2.1.1
    (focalBids i kind (own i mode x) x.2.2.1) 0 = _
  congr 1
  exact (Noisy.cappedFocalBids_real i kind _ _).symm

lemma measurable_rowFunction (i : Row) {N : ℕ} (mode : Mode) (kind : Fin N→ Fin 3) :
    Measurable (rowFunction i mode kind) := by
  have he : rowFunction i mode kind = fun x : Sample i N =>
      rowPayoff i (rowInput i mode kind x).2.1 (focalRow kind)
        (rowInput i mode kind x).1 (SourceContinuity.bids i (rowInput i mode kind x).2) 0 :=
    funext (rowFunction_input i mode kind)
  rw [he]
  exact (SourceContinuity.measurable_rowPayoff i (focalRow kind) 0 (Noisy.focal_mem_lower kind)).comp
    (continuous_rowInput i mode kind).measurable

lemma rowFunction_bound (i : Row) {N : ℕ} (mode : Mode) (kind : Fin N→ Fin 3) (x : Sample i N) :
    |rowFunction i mode kind x|≤3*Uniform05.t i :=
  (noisyRowPayoff_bound i x.1.1 x.1.2 x.2.1.1 (chosen mode x.2.1) x.2.2.2 kind x.2.2.1).trans
    (mul_le_mul_of_nonneg_left x.2.1.1.property.2 (by norm_num))

def bids (i : Row) {N : ℕ} (mode : Mode) (kind : Fin N→ Fin 3) (x : Sample i N) : Fin (N+1)→ℝ :=
  focalBids i kind (own i mode x) x.2.2.1

lemma continuous_bids (i : Row) {N : ℕ} (mode : Mode) (kind : Fin N→ Fin 3) :
    Continuous (bids i mode kind) :=
  (continuous_focalBids i kind).comp
    (((continuous_subtype_val.comp (continuous_own i mode))).prodMk (by fun_prop))

def bad (i : Row) {N : ℕ} (mode : Mode) (kind : Fin N→ Fin 3) : Set (Sample i N) :=
  {x | bids i mode kind x 0≤0 ∨
    (∃a∈(focalRow kind).lower,a≠0 ∧ bids i mode kind x a=Uniform05.t i/2) ∨
    ∃P Q : Allocation (N+1),LowBody.focalCopy P 0≠LowBody.focalCopy Q 0 ∧
      LowBody.CompleteInformation.potential (Uniform05.kappa i) (bids i mode kind x) P.1 P.2=
        LowBody.CompleteInformation.potential (Uniform05.kappa i) (bids i mode kind x) Q.1 Q.2}

lemma isClosed_bad (i : Row) {N : ℕ} (mode : Mode) (kind : Fin N→ Fin 3) :
    IsClosed (bad i mode kind) := by
  have hb:=continuous_bids i mode kind
  have he : bad i mode kind={x : Sample i N | bids i mode kind x 0≤0} ∪
      ((⋃a : Fin (N+1),{x | a∈(focalRow kind).lower ∧ a≠0 ∧ bids i mode kind x a=Uniform05.t i/2}) ∪
       ⋃P : Allocation (N+1),⋃Q : Allocation (N+1),
        {x | LowBody.focalCopy P 0≠LowBody.focalCopy Q 0 ∧
          LowBody.CompleteInformation.potential (Uniform05.kappa i) (bids i mode kind x) P.1 P.2=
            LowBody.CompleteInformation.potential (Uniform05.kappa i) (bids i mode kind x) Q.1 Q.2}) := by
    ext x; simp [bad]
  rw [he]
  apply (isClosed_le ((continuous_apply 0).comp hb) continuous_const).union
  apply IsClosed.union
  · apply isClosed_iUnion_of_finite
    intro a
    by_cases ha : a∈(focalRow kind).lower ∧ a≠0
    · simpa only [ha.1,ha.2,ne_eq,not_false_eq_true,true_and,Function.comp_def] using
        isClosed_eq ((continuous_apply a).comp hb) continuous_const
    · have he : {x : Sample i N | a∈(focalRow kind).lower ∧ a≠0 ∧
          bids i mode kind x a=Uniform05.t i/2}=∅ := by aesop
      rw [he]; exact isClosed_empty
  · apply isClosed_iUnion_of_finite
    intro P
    apply isClosed_iUnion_of_finite
    intro Q
    by_cases h : LowBody.focalCopy P 0=LowBody.focalCopy Q 0
    · simp only [h,ne_eq,not_true_eq_false,false_and,Set.setOf_false]; exact isClosed_empty
    · simpa only [h,ne_eq,not_false_eq_true,true_and,Function.comp_def] using
        isClosed_eq ((LowBody.continuous_potential (Uniform05.kappa i) P).comp hb)
          ((LowBody.continuous_potential (Uniform05.kappa i) Q).comp hb)

lemma continuousAt_rowFunction (i : Row) {N : ℕ} (mode : Mode) (kind : Fin N→ Fin 3)
    (x : Sample i N) (hx : x∉bad i mode kind) : ContinuousAt (rowFunction i mode kind) x := by
  have hp : 0< bids i mode kind x 0:=lt_of_not_ge (fun h=> hx (Or.inl h))
  have hcut : ∀a∈(focalRow kind).lower,a≠0→ bids i mode kind x a≠Uniform05.t i/2 := by
    intro a ha hne h; exact hx (Or.inr (Or.inl ⟨a,ha,hne,h⟩))
  have ht : ∀P Q : (Source.lowerTemplate (focalRow kind)).Candidate,
      LowBody.CompleteInformation.potential (Uniform05.kappa i) (bids i mode kind x) P.val.1 P.val.2=
        LowBody.CompleteInformation.potential (Uniform05.kappa i) (bids i mode kind x) Q.val.1 Q.val.2→
      LowBody.focalCopy P.val 0=LowBody.focalCopy Q.val 0 := by
    intro P Q h
    by_contra hn
    exact hx (Or.inr (Or.inr ⟨P.val,Q.val,hn,h⟩))
  have he : rowFunction i mode kind = fun z : Sample i N =>
      rowPayoff i (rowInput i mode kind z).2.1 (focalRow kind)
        (rowInput i mode kind z).1 (SourceContinuity.bids i (rowInput i mode kind z).2) 0 :=
    funext (rowFunction_input i mode kind)
  rw [he]
  have hbid : SourceContinuity.bids i (rowInput i mode kind x).2 = bids i mode kind x :=
    Noisy.cappedFocalBids_real i kind _ _
  apply (SourceContinuity.continuousAt_rowPayoff_rival_cut i (focalRow kind) 0 (Noisy.focal_mem_lower kind)
    (rowInput i mode kind x) ?_ ?_ ?_).comp (continuous_rowInput i mode kind).continuousAt
  · rw [hbid]
    exact hp
  · rw [hbid]
    exact hcut
  · rw [hbid,bids,Noisy.lowerBids_focalBids]
    exact ht

def sampleLaw (i : Row) (N : ℕ) (p : Parameter i) : ProbabilityMeasure (Sample i N) :=
  productLaw (diracProba p) (productLaw p.2.1
    (productLaw (rowLaw N (restrictedLaw i p).bidLaw)
      (⟨volume,inferInstance⟩ : ProbabilityMeasure unitInterval)))

lemma continuous_sampleLaw (i : Row) (N : ℕ) : Continuous (sampleLaw i N) := by
  have hG : Continuous (fun p : Parameter i => (restrictedLaw i p).bidLaw) :=
    Uniform05.RestrictedLaw.continuous_bidLaw.comp (continuous_restrictedLaw i)
  have hdir : Continuous (fun p : Parameter i=>diracProba p) := continuous_diracProba
  have hjoint : Continuous (fun p : Parameter i=>p.2.1) :=
    continuous_subtype_val.comp continuous_snd
  exact continuous_productLaw.comp (hdir.prodMk
    (continuous_productLaw.comp (hjoint.prodMk
      (continuous_productLaw.comp (((continuous_rowLaw N).comp hG).prodMk continuous_const)))))

def Good (i : Row) (pi : Joint i) (mode : Mode) : Prop :=
  ∀ᵐp∂(pi.1 : Measure (Value i×unitInterval)),
    0<(baseBid i (p.1,chosen mode p):ℝ)

theorem sample_bad_null (i : Row) {N : ℕ} (pi : Joint i)
    [NullSingletonClass ((restrictedLaw i (0,pi)).bidLaw : Measure (Bid i))]
    (mode : Mode) (kind : Fin N→ Fin 3) (hgood : Good i pi mode) :
    (sampleLaw i N (0,pi) : Measure (Sample i N)) (bad i mode kind)=0 := by
  have hm : MeasurableSet {x : Sample i N | x∉bad i mode kind} :=
    (isClosed_bad i mode kind).measurableSet.compl
  apply measure_eq_zero_iff_ae_notMem.mpr
  change ∀ᵐx∂(Measure.dirac (show Parameter i from (0,pi))).prod
    ((pi.1 : Measure (Value i×unitInterval)).prod
      ((rowLaw N (restrictedLaw i (0,pi)).bidLaw : Measure (Fin N→ Bid i)).prod volume)),_
  apply (Measure.ae_prod_iff_ae_ae hm).mpr
  simp only [ae_dirac_eq,Filter.eventually_pure]
  apply (Measure.ae_prod_iff_ae_ae (hm.preimage (by fun_prop))).mpr
  filter_upwards [hgood] with p hp
  apply (Measure.ae_prod_iff_ae_ae (hm.preimage (by fun_prop))).mpr
  filter_upwards [ae_rival_ties i (restrictedLaw i (0,pi)) kind _ hp.ne',
    ae_rival_cut (N:=N) i (restrictedLaw i (0,pi))] with b hties hcut
  apply ae_of_all
  intro z
  rintro (hzero|hseed|⟨P,Q,hne,heq⟩)
  · have h : (baseBid i (p.1,chosen mode p):ℝ)≤0 := by
      simpa [bids,own,noisyBid_zero] using hzero
    exact not_le_of_gt hp h
  · obtain ⟨a,ha,hne,he⟩:=hseed
    revert ha hne he
    refine Fin.cases ?_ (fun j=>?_) a
    · intro _ hne _; exact hne rfl
    · intro ha _ he
      have hk : kind j=0 := by simpa [focalRow,Source.countRowOfKind] using ha
      exact hcut j (by simpa [bids,focalBids,hk] using he)
  · exact hne (hties P Q (by simpa [bids,own,noisyBid_zero] using heq))

def weightedRow (i : Row) {N : ℕ} (mode : Mode) (kind : Fin N→ Fin 3)
    (a : C(Value i×unitInterval,ℝ)) (x : Sample i N) : ℝ := a x.2.1*rowFunction i mode kind x

lemma measurable_weightedRow (i : Row) {N : ℕ} (mode : Mode) (kind : Fin N→ Fin 3)
    (a : C(Value i×unitInterval,ℝ)) : Measurable (weightedRow i mode kind a) :=
  (a.continuous.measurable.comp (measurable_fst.comp measurable_snd)).mul
    (measurable_rowFunction i mode kind)

lemma weightedRow_bound (i : Row) {N : ℕ} (mode : Mode) (kind : Fin N→ Fin 3)
    (a : C(Value i×unitInterval,ℝ)) (x : Sample i N) :
    |weightedRow i mode kind a x|≤‖a‖*(3*Uniform05.t i) := by
  rw [weightedRow,abs_mul]
  exact mul_le_mul (by simpa only [Real.norm_eq_abs] using a.norm_coe_le_norm x.2.1)
    (rowFunction_bound i mode kind x) (abs_nonneg _) (norm_nonneg _)

theorem weightedRow_tendsto (i : Row) {N : ℕ} (mode : Mode) (kind : Fin N→ Fin 3)
    (a : C(Value i×unitInterval,ℝ)) (eps : ℕ→ unitInterval) (pi : ℕ→ Joint i) (pi0 : Joint i)
    (heps : Tendsto eps atTop (𝓝 0)) (hpi : Tendsto pi atTop (𝓝 pi0))
    [NullSingletonClass ((restrictedLaw i (0,pi0)).bidLaw : Measure (Bid i))]
    (hgood : Good i pi0 mode) :
    Tendsto (fun n=>∫x,weightedRow i mode kind a x
      ∂(sampleLaw i N (eps n,pi n) : Measure (Sample i N))) atTop
      (𝓝 (∫x,weightedRow i mode kind a x ∂(sampleLaw i N (0,pi0) : Measure (Sample i N)))) := by
  letI : MetricSpace (Sample i N):=TopologicalSpace.metrizableSpaceMetric (Sample i N)
  exact LowBody.tendsto_integral_of_closed_null_discontinuities
    (weightedRow i mode kind a) (measurable_weightedRow i mode kind a)
    (bad i mode kind) (isClosed_bad i mode kind)
    (fun x hx=>(a.continuous.continuousAt.comp (by fun_prop)).mul
      (continuousAt_rowFunction i mode kind x hx))
    (by have ht:=Uniform05.t_pos i; positivity : 0≤‖a‖*(3*Uniform05.t i))
    (weightedRow_bound i mode kind a)
    (fun n=> sampleLaw i N (eps n,pi n)) (sampleLaw i N (0,pi0))
    ((continuous_sampleLaw i N).continuousAt.tendsto.comp (heps.prodMk_nhds hpi))
    (sample_bad_null i pi0 mode kind hgood)

def rowAverage (i : Row) (N : ℕ) (par : unitInterval×Joint i) (mode : Mode)
    (kind : Fin N→ Fin 3) (p : Value i×unitInterval) : ℝ :=
  ∫b : Fin N→ Bid i,(∫z : unitInterval,
    rowFunction i mode kind (par,(p,(b,z))))
    ∂(rowLaw N (restrictedLaw i par).bidLaw : Measure (Fin N→ Bid i))

lemma measurable_rowAverage (i : Row) (N : ℕ) (par : unitInterval×Joint i) (mode : Mode)
    (kind : Fin N→ Fin 3) : Measurable (rowAverage i N par mode kind) := by
  have h : Measurable (fun x : ((Value i×unitInterval)×(Fin N→ Bid i))×unitInterval=>
      rowFunction i mode kind (par,(x.1.1,(x.1.2,x.2)))) :=
    (measurable_rowFunction i mode kind).comp (by fun_prop)
  have hinner : StronglyMeasurable (fun x : (Value i×unitInterval)×(Fin N→Bid i) =>
      ∫ z : unitInterval, rowFunction i mode kind (par,(x.1,(x.2,z)))) :=
    h.stronglyMeasurable.integral_prod_right'
  exact hinner.integral_prod_right'.measurable

lemma rowAverage_bound (i : Row) (N : ℕ) (par : unitInterval×Joint i) (mode : Mode)
    (kind : Fin N→ Fin 3) (p : Value i×unitInterval) :
    |rowAverage i N par mode kind p|≤3*Uniform05.t i := by
  have hinner (b : Fin N→ Bid i) :
      |(∫z : unitInterval,rowFunction i mode kind (par,(p,(b,z))))|≤3*Uniform05.t i := by
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const
        (f := fun z : unitInterval=>rowFunction i mode kind (par,(p,(b,z))))
        (C := 3*Uniform05.t i) (ae_of_all (volume : Measure unitInterval)
        (fun z=> by simpa only [Real.norm_eq_abs] using rowFunction_bound i mode kind (par,(p,(b,z)))))
  simpa only [rowAverage,Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const
      (f := fun b : Fin N→Bid i=> ∫ z : unitInterval,
        rowFunction i mode kind (par,(p,(b,z)))) (C := 3*Uniform05.t i)
      (ae_of_all (rowLaw N (restrictedLaw i par).bidLaw : Measure (Fin N→ Bid i))
        (fun b=> by simpa only [Real.norm_eq_abs] using hinner b))

lemma weighted_average_integrable (i : Row) (N : ℕ) (par : unitInterval×Joint i) (mode : Mode)
    (kind : Fin N→ Fin 3) (a : C(Value i×unitInterval,ℝ)) :
    Integrable (fun p=> a p*rowAverage i N par mode kind p)
      (par.2.1 : Measure (Value i×unitInterval)) :=
  Integrable.of_bound
    (a.continuous.measurable.mul (measurable_rowAverage i N par mode kind)).aestronglyMeasurable
    (‖a‖*(3*Uniform05.t i)) (ae_of_all _ (fun p=> by
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul (by simpa only [Real.norm_eq_abs] using a.norm_coe_le_norm p)
        (rowAverage_bound i N par mode kind p) (abs_nonneg _) (norm_nonneg _)))

theorem integral_weightedRow (i : Row) (N : ℕ) (par : unitInterval×Joint i) (mode : Mode)
    (kind : Fin N→ Fin 3) (a : C(Value i×unitInterval,ℝ)) :
    (∫x,weightedRow i mode kind a x ∂(sampleLaw i N par : Measure (Sample i N)))=
      ∫p,a p*rowAverage i N par mode kind p ∂(par.2.1 : Measure (Value i×unitInterval)) := by
  let C:=‖a‖*(3*Uniform05.t i)
  have hi : Integrable (weightedRow i mode kind a) (sampleLaw i N par : Measure (Sample i N)) :=
    Integrable.of_bound (measurable_weightedRow i mode kind a).aestronglyMeasurable C
      (ae_of_all _ (fun x=> by simpa only [Real.norm_eq_abs] using weightedRow_bound i mode kind a x))
  have hp : Integrable (fun x : (Value i×unitInterval)×((Fin N→ Bid i)×unitInterval)=>
      weightedRow i mode kind a (par,x))
      ((par.2.1 : Measure (Value i×unitInterval)).prod
        ((rowLaw N (restrictedLaw i par).bidLaw : Measure (Fin N→ Bid i)).prod volume)) :=
    Integrable.of_bound ((measurable_weightedRow i mode kind a).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable C
      (ae_of_all _ (fun x=> by simpa only [Real.norm_eq_abs] using weightedRow_bound i mode kind a (par,x)))
  have hr (p : Value i×unitInterval) :
      Integrable (fun x : (Fin N→ Bid i)×unitInterval=> weightedRow i mode kind a (par,(p,x)))
        ((rowLaw N (restrictedLaw i par).bidLaw : Measure (Fin N→ Bid i)).prod volume) :=
    Integrable.of_bound ((measurable_weightedRow i mode kind a).comp (by fun_prop)).aestronglyMeasurable C
      (ae_of_all _ (fun x=> by simpa only [Real.norm_eq_abs] using weightedRow_bound i mode kind a (par,(p,x))))
  change (∫x,weightedRow i mode kind a x ∂(Measure.dirac (show Parameter i from par)).prod
    ((par.2.1 : Measure (Value i×unitInterval)).prod
      ((rowLaw N (restrictedLaw i par).bidLaw : Measure (Fin N→ Bid i)).prod volume)))=_
  have hi' : Integrable (weightedRow i mode kind a) ((Measure.dirac (show Parameter i from par)).prod
    ((par.2.1 : Measure (Value i×unitInterval)).prod
      ((rowLaw N (restrictedLaw i par).bidLaw : Measure (Fin N→Bid i)).prod volume))) := hi
  rw [integral_prod _ hi',integral_dirac,integral_prod _ hp]
  apply integral_congr_ae
  exact ae_of_all _ (fun p=> by
    change (∫ y : (Fin N→Bid i)×unitInterval,
      weightedRow i mode kind a ((show Parameter i from par),(p,y))
        ∂(rowLaw N (restrictedLaw i par).bidLaw : Measure (Fin N→Bid i)).prod volume) = _
    rw [integral_prod _ (hr p)]
    simp only [weightedRow]
    simp_rw [integral_const_mul]
    rfl)

def testUtility (i : Row) (N : ℕ) (par : unitInterval×Joint i) (mode : Mode)
    (a : C(Value i×unitInterval,ℝ)) : ℝ :=
  (categoryRowLaw i N).expect (fun kind=>∫x,weightedRow i mode kind a x
    ∂(sampleLaw i N par : Measure (Sample i N)))

lemma average_eq_utility (i : Row) (N : ℕ) (par : unitInterval×Joint i) (mode : Mode)
    (p : Value i×unitInterval) :
    (categoryRowLaw i N).expect (fun kind=> rowAverage i N par mode kind p)=
      expectedUtility i N par.1 par.2 p.1 (chosen mode p) := by rfl

lemma measurable_utility (i : Row) (N : ℕ) (par : unitInterval×Joint i) (mode : Mode) :
    Measurable (fun p : Value i×unitInterval=> expectedUtility i N par.1 par.2 p.1 (chosen mode p)) := by
  simp_rw [← average_eq_utility]
  exact Finset.measurable_sum _ (fun kind _=>
    measurable_const.mul (measurable_rowAverage i N par mode kind))

theorem testUtility_eq (i : Row) (N : ℕ) (par : unitInterval×Joint i) (mode : Mode)
    (a : C(Value i×unitInterval,ℝ)) :
    testUtility i N par mode a=
      ∫p,a p*expectedUtility i N par.1 par.2 p.1 (chosen mode p)
        ∂(par.2.1 : Measure (Value i×unitInterval)) := by
  simp_rw [testUtility,integral_weightedRow,← average_eq_utility,FiniteLaw.expect,Finset.mul_sum]
  rw [integral_finsetSum _ (fun kind _=>
    ((weighted_average_integrable i N par mode kind a).const_mul ((categoryRowLaw i N).mass kind)).congr
      (ae_of_all _ (fun p=> by ring)))]
  apply Finset.sum_congr rfl
  intro kind _
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun p=> by ring)

theorem testUtility_tendsto (i : Row) (N : ℕ) (mode : Mode)
    (a : C(Value i×unitInterval,ℝ)) (eps : ℕ→ unitInterval) (pi : ℕ→ Joint i) (pi0 : Joint i)
    (heps : Tendsto eps atTop (𝓝 0)) (hpi : Tendsto pi atTop (𝓝 pi0))
    [NullSingletonClass ((restrictedLaw i (0,pi0)).bidLaw : Measure (Bid i))]
    (hgood : Good i pi0 mode) :
    Tendsto (fun n=> testUtility i N (eps n,pi n) mode a) atTop
      (𝓝 (testUtility i N (0,pi0) mode a)) := by
  unfold testUtility FiniteLaw.expect
  exact tendsto_finsetSum _ (fun kind _=>
    (weightedRow_tendsto i mode kind a eps pi pi0 heps hpi hgood).const_mul _)

lemma test_integrable (i : Row) (N : ℕ) (par : unitInterval×Joint i) (mode : Mode)
    (a : C(Value i×unitInterval,ℝ)) :
    Integrable (fun p=> a p*expectedUtility i N par.1 par.2 p.1 (chosen mode p))
      (par.2.1 : Measure (Value i×unitInterval)) := by
  apply Integrable.of_bound (a.continuous.measurable.mul (measurable_utility i N par mode)).aestronglyMeasurable
    (‖a‖*(3*Uniform05.t i))
  exact ae_of_all _ (fun p=> by
    change ‖a p*expectedUtility i N par.1 par.2 p.1 (chosen mode p)‖ ≤ _
    rw [Real.norm_eq_abs,abs_mul]
    apply mul_le_mul (by simpa only [Real.norm_eq_abs] using a.norm_coe_le_norm p)
      ((expectedUtility_bound i N par.1 par.2 p.1 (chosen mode p)).trans
        (mul_le_mul_of_nonneg_left p.1.property.2 (by norm_num))) (abs_nonneg _) (norm_nonneg _))

theorem actual_limit_tests (i : Row) (N : ℕ) (q : unitInterval)
    (eps : ℕ→ unitInterval) (pi : ℕ→ Joint i) (pi0 : Joint i)
    (heps : Tendsto eps atTop (𝓝 0)) (hpi : Tendsto pi atTop (𝓝 pi0))
    (hIC : ∀n,NoisyIC i N (eps n) (pi n))
    [NullSingletonClass ((restrictedLaw i (0,pi0)).bidLaw : Measure (Bid i))]
    (hold : Good i pi0 none) (hnew : Good i pi0 (some q))
    (a : C(Value i×unitInterval,ℝ)) (ha : ∀p,0≤ a p) :
    (∫p,a p*(expectedUtility i N 0 pi0 p.1 q-expectedUtility i N 0 pi0 p.1 p.2)
      ∂(pi0.1 : Measure (Value i×unitInterval)))≤0 := by
  have hpre (n : ℕ) : testUtility i N (eps n,pi n) (some q) a-
      testUtility i N (eps n,pi n) none a≤0 := by
    rw [testUtility_eq,testUtility_eq]
    apply sub_nonpos.mpr
    apply integral_mono_ae (test_integrable i N (eps n,pi n) (some q) a)
      (test_integrable i N (eps n,pi n) none a)
    filter_upwards [hIC n] with p hp
    exact mul_le_mul_of_nonneg_left (hp q) (ha p)
  have ht:=(testUtility_tendsto i N (some q) a eps pi pi0 heps hpi hnew).sub
    (testUtility_tendsto i N none a eps pi pi0 heps hpi hold)
  have hlim:=le_of_tendsto ht (Eventually.of_forall hpre)
  rw [testUtility_eq,testUtility_eq,
    ← integral_sub (test_integrable i N (0,pi0) (some q) a)
      (test_integrable i N (0,pi0) none a)] at hlim
  convert! hlim using 1
  apply integral_congr_ae
  exact ae_of_all _ (fun p=> by simp only [chosen,Option.getD_some,Option.getD_none]; ring)

end ExactTests
end FCAppendix.Affine.UniformFinite
