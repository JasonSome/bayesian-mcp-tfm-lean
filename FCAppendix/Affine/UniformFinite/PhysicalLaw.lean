import FCAppendix.Affine.Uniform05RestrictedLaw
import FCAppendix.Affine.LowBody.NoisyBidAtomless
import FCAppendix.Existence.R01Parameterization
import FCAppendix.Existence.R01CompactProduct

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open Existence.Distributional

abbrev Row := Uniform07.Row
abbrev Value (i : Row) := Icc (0 : ℝ) (Uniform05.t i)
abbrev Bid (i : Row) := Uniform05.Bid i

instance valueNonempty (i : Row) : Nonempty (Value i) :=
  ⟨⟨0,le_rfl,(Uniform05.t_pos i).le⟩⟩

def valueMap (i : Row) (u : unitInterval) : Value i :=
  ⟨Uniform05.t i*(u:ℝ),mul_nonneg (Uniform05.t_pos i).le u.property.1,
    by nlinarith [u.property.2,Uniform05.t_pos i]⟩

lemma continuous_valueMap (i : Row) : Continuous (valueMap i) := by
  apply Continuous.subtype_mk
  exact continuous_const.mul continuous_subtype_val

def lowerMeasure (i : Row) : Measure (Value i) := volume.map (valueMap i)

instance lowerMeasure_probability (i : Row) : IsProbabilityMeasure (lowerMeasure i) :=
  Measure.isProbabilityMeasure_map (continuous_valueMap i).measurable.aemeasurable

theorem lowerMeasure_real (i : Row) :
    (lowerMeasure i).map Subtype.val = Uniform05.lowerValueMeasure i := by
  letI := Uniform05.lowerValueMeasure_isProbability i
  have ht := Uniform05.t_pos i
  rw [lowerMeasure,Measure.map_map measurable_subtype_coe
    (continuous_valueMap i).measurable]
  apply Measure.ext_of_Iic
  intro b
  rw [Measure.map_apply
    (measurable_subtype_coe.comp (continuous_valueMap i).measurable) measurableSet_Iic]
  change (volume : Measure unitInterval) {u | Uniform05.t i*(u:ℝ)≤ b} = _
  by_cases hb0 : b<0
  · have he : {u : unitInterval | Uniform05.t i*(u:ℝ)≤ b}=∅ := by
      ext u
      simp only [mem_setOf_eq,mem_empty_iff_false,iff_false]
      nlinarith [mul_nonneg ht.le u.property.1]
    have he' : Iic b ∩ Icc (0:ℝ) (Uniform05.t i)=∅ := by
      ext v
      simp only [mem_inter_iff,mem_Iic,mem_Icc,mem_empty_iff_false,iff_false]
      rintro ⟨hv,hv0,_⟩
      linarith
    simp [he,Uniform05.lowerValueMeasure,Measure.restrict_apply,he']
  · have hb := le_of_not_gt hb0
    by_cases hbt : b≤ Uniform05.t i
    · have hq : b/Uniform05.t i∈Icc (0:ℝ) 1 :=
        ⟨div_nonneg hb ht.le,(div_le_one ht).mpr hbt⟩
      have he : {u : unitInterval | Uniform05.t i*(u:ℝ)≤ b}=
          Iic (⟨b/Uniform05.t i,hq⟩ : unitInterval) := by
        ext u
        change Uniform05.t i*(u:ℝ)≤ b ↔ (u:ℝ)≤ b/Uniform05.t i
        rw [le_div_iff₀ ht,mul_comm]
      have he' : Iic b ∩ Icc (0:ℝ) (Uniform05.t i)=Icc 0 b := by
        ext v
        simp only [mem_inter_iff,mem_Iic,mem_Icc]
        constructor
        · rintro ⟨hvb,hv0,_⟩; exact ⟨hv0,hvb⟩
        · rintro ⟨hv0,hvb⟩; exact ⟨hvb,hv0,hvb.trans hbt⟩
      rw [he,unitInterval.volume_Iic]
      simp only [Uniform05.lowerValueMeasure,Measure.smul_apply,
        Measure.restrict_apply measurableSet_Iic,he',Real.volume_Icc,sub_zero,
        smul_eq_mul]
      rw [← ENNReal.ofReal_mul (by positivity : 0≤1/Uniform05.t i)]
      congr 1
      ring
    · have htb := lt_of_not_ge hbt
      have he : {u : unitInterval | Uniform05.t i*(u:ℝ)≤ b}=univ := by
        ext u
        simp only [mem_setOf_eq,mem_univ,iff_true]
        nlinarith [u.property.2]
      have he' : Iic b ∩ Icc (0:ℝ) (Uniform05.t i)=Icc 0 (Uniform05.t i) :=
        inter_eq_right.mpr (fun _ hv=> hv.2.trans htb.le)
      rw [he,measure_univ]
      simp only [Uniform05.lowerValueMeasure,Measure.smul_apply,
        Measure.restrict_apply measurableSet_Iic,he',Real.volume_Icc,sub_zero,
        smul_eq_mul]
      rw [← ENNReal.ofReal_mul (by positivity : 0≤1/Uniform05.t i)]
      simp [ht.ne']

instance lowerMeasure_atomless (i : Row) : NullSingletonClass (lowerMeasure i) := by
  constructor
  intro v
  rw [lowerMeasure,Measure.map_apply (continuous_valueMap i).measurable
    (measurableSet_singleton v)]
  apply Set.Countable.measure_zero
  apply Set.Subsingleton.countable
  intro u hu w hw
  apply Subtype.ext
  have h := congrArg Subtype.val (hu.trans hw.symm)
  change Uniform05.t i*(u:ℝ)=Uniform05.t i*(w:ℝ) at h
  exact mul_left_cancel₀ (Uniform05.t_pos i).ne' h

lemma lowerValue_positive (i : Row) : ∀ᵐ(v : Value i) ∂lowerMeasure i,0<(v:ℝ) := by
  let z : Value i := ⟨0,le_rfl,(Uniform05.t_pos i).le⟩
  filter_upwards [(lowerMeasure i).ae_ne z] with v hv
  apply lt_of_le_of_ne v.property.1
  intro he
  apply hv
  apply Subtype.ext
  exact he.symm

abbrev Joint (i : Row) := Law (A:=unitInterval) (lowerMeasure i)

def hiBid (i : Row) (v : ℝ) : ℝ := min v (Uniform05.cap i)
def width (i : Row) (v : ℝ) : ℝ := hiBid i v-Uniform05.floorBid i v

lemma width_nonneg (i : Row) (v : Value i) : 0≤ width i v :=
  sub_nonneg.mpr (Uniform05.floor_le_min_value_cap i v.property.1 v.property.2)

lemma width_positive (i : Row) (v : Value i) (hv : 0<(v:ℝ)) : 0< width i v := by
  have hf := Uniform05.floor_le_chi_mul i v.property.1 (Uniform05.t_pos i).le
  have hfc : Uniform05.floorBid i v< Uniform05.cap i := by
    have hct := Uniform05.chi_t_lt_cap i
    have hmono := mul_le_mul_of_nonneg_left v.property.2
      (by norm_num [Uniform05.chi] : 0≤ Uniform05.chi)
    linarith
  have hfv : Uniform05.floorBid i v<(v:ℝ) := by
    norm_num [Uniform05.chi] at hf
    linarith
  exact sub_pos.mpr (lt_min hfv hfc)

def noisyRealBid (i : Row) (eps v q z : ℝ) : ℝ :=
  Uniform05.floorBid i v+width i v*((1-eps)*q+eps*z)

lemma noisyRealBid_bounds (i : Row) (eps : unitInterval)
    (v : Value i) (q z : unitInterval) :
    noisyRealBid i eps v q z∈Icc (Uniform05.floorBid i v) (hiBid i v) := by
  have hw := width_nonneg i v
  have h0 : 0≤(1-(eps:ℝ))*(q:ℝ)+(eps:ℝ)*(z:ℝ) := by
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr eps.property.2) q.property.1)
      (mul_nonneg eps.property.1 z.property.1)
  have h1 : (1-(eps:ℝ))*(q:ℝ)+(eps:ℝ)*(z:ℝ)≤1 := by
    nlinarith [mul_le_mul_of_nonneg_left q.property.2
      (sub_nonneg.mpr eps.property.2),
      mul_le_mul_of_nonneg_left z.property.2 eps.property.1]
  have hlo := mul_nonneg hw h0
  have hhi := mul_le_mul_of_nonneg_left h1 hw
  unfold noisyRealBid width hiBid at *
  constructor <;> linarith

def noisyBid (i : Row) (p : unitInterval×((Value i×unitInterval)×unitInterval)) : Bid i :=
  ⟨noisyRealBid i p.1 p.2.1.1 p.2.1.2 p.2.2,
    (Uniform05.floor_nonneg i p.2.1.1).trans
      (noisyRealBid_bounds i p.1 p.2.1.1 p.2.1.2 p.2.2).1,
    (noisyRealBid_bounds i p.1 p.2.1.1 p.2.1.2 p.2.2).2.trans (min_le_right _ _)⟩

lemma continuous_noisyBid (i : Row) : Continuous (noisyBid i) := by
  apply Continuous.subtype_mk
  have hf := Uniform05.continuous_floor i
  unfold noisyRealBid width hiBid
  fun_prop

def baseBid (i : Row) (p : Value i×unitInterval) : Bid i := noisyBid i (0,(p,0))

lemma baseBid_val (i : Row) (p : Value i×unitInterval) :
    (baseBid i p:ℝ)=Uniform05.floorBid i p.1+width i p.1*(p.2:ℝ) := by
  simp [baseBid,noisyBid,noisyRealBid]

lemma continuous_baseBid (i : Row) : Continuous (baseBid i) :=
  (continuous_noisyBid i).comp
    (continuous_const.prodMk (continuous_id.prodMk continuous_const))

def physicalLaw (i : Row) (p : unitInterval×Joint i) : Law (A:=Bid i) (lowerMeasure i) :=
  noisyLaw (lowerMeasure i) (⟨volume,inferInstance⟩ : ProbabilityMeasure unitInterval)
    (fun x=> noisyBid i (p.1,x))
    ((continuous_noisyBid i).comp (continuous_const.prodMk continuous_id)) p.2

lemma noisyBid_zero (i : Row) (x : (Value i×unitInterval)×unitInterval) :
    noisyBid i (0,x)=baseBid i x.1 := by
  apply Subtype.ext
  simp [noisyBid,noisyRealBid,baseBid]

theorem physicalLaw_zero (i : Row) (pi : Joint i) :
    physicalLaw i (0,pi)=pushLaw (lowerMeasure i) (baseBid i) (continuous_baseBid i) pi := by
  apply Subtype.ext
  apply Subtype.ext
  change (((pi.1 : Measure (Value i×unitInterval)).prod (volume : Measure unitInterval)).map
    (fun x=>(x.1.1,noisyBid i (0,x))))=
    (pi.1 : Measure (Value i×unitInterval)).map (fun x=>(x.1,baseBid i x))
  have he : (fun x : (Value i×unitInterval)×unitInterval=>(x.1.1,noisyBid i (0,x)))=
      (fun x : Value i×unitInterval=>(x.1,baseBid i x))∘Prod.fst := by
    funext x
    rw [noisyBid_zero]
    rfl
  rw [he,← Measure.map_map (measurable_fst.prodMk (continuous_baseBid i).measurable)
    measurable_fst,Measure.map_fst_prod,measure_univ,one_smul]

theorem continuous_physicalLaw (i : Row) : Continuous (physicalLaw i) := by
  apply Continuous.subtype_mk
  apply ProbabilityMeasure.continuous_iff_forall_continuousMap_continuous_integral.mpr
  intro f
  let inner : (unitInterval×(Value i×unitInterval))×unitInterval→ℝ :=
    fun x=> f (x.1.2.1,noisyBid i (x.1.1,(x.1.2,x.2)))
  have hinner : Continuous inner := by
    apply f.continuous.comp
    apply (show Continuous (fun x : (unitInterval×(Value i×unitInterval))×unitInterval=>
      x.1.2.1) from by fun_prop).prodMk
    apply (continuous_noisyBid i).comp
    fun_prop
  let g : unitInterval×(Value i×unitInterval)→ℝ := fun x=>∫z : unitInterval,inner (x,z)
  let θ : ProbabilityMeasure unitInterval := ⟨volume,inferInstance⟩
  have hg : Continuous g := (continuous_law_integral inner hinner).comp
    (continuous_id.prodMk
      (continuous_const : Continuous (fun _ : unitInterval×(Value i×unitInterval)=>
        θ)))
  have hc : Continuous (fun p : unitInterval×Joint i=>
      ∫x,g (p.1,x) ∂(p.2.1 : Measure (Value i×unitInterval))) :=
    (continuous_law_integral g hg).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  convert! hc using 1
  funext p
  exact integral_noisyLaw (lowerMeasure i)
    (⟨volume,inferInstance⟩ : ProbabilityMeasure unitInterval)
    (fun x=> noisyBid i (p.1,x))
    ((continuous_noisyBid i).comp (continuous_const.prodMk continuous_id)) p.2 f f.continuous

lemma original_value_positive (i : Row) (pi : Joint i) :
    ∀ᵐp ∂(pi.1 : Measure (Value i×unitInterval)),0<(p.1:ℝ) := by
  have hs : MeasurableSet {v : Value i | 0<(v:ℝ)} :=
    measurableSet_lt measurable_const measurable_subtype_coe
  apply (ae_map_iff measurable_fst.aemeasurable hs).mp
  rw [pi.property]
  exact lowerValue_positive i

lemma noisyBid_injective_noise (i : Row) (eps : unitInterval) (heps : 0<(eps:ℝ))
    (p : Value i×unitInterval) (hp : 0<(p.1:ℝ)) :
    Function.Injective (fun z : unitInterval=> noisyBid i (eps,(p,z))) := by
  intro z w he
  have hh := congrArg Subtype.val he
  change noisyRealBid i eps p.1 p.2 z=noisyRealBid i eps p.1 p.2 w at hh
  have hc := mul_pos (width_positive i p.1 hp) heps
  apply Subtype.ext
  unfold noisyRealBid at hh
  nlinarith

def bidLaw (i : Row) (p : unitInterval×Joint i) : ProbabilityMeasure (Bid i) :=
  (physicalLaw i p).1.map measurable_snd.aemeasurable

theorem physical_bid_singleton (i : Row) (eps : unitInterval) (heps : 0<(eps:ℝ))
    (pi : Joint i) (b : Bid i) : (bidLaw i (eps,pi) : Measure (Bid i)) {b}=0 := by
  let psi : (Value i×unitInterval)×unitInterval→ Value i×Bid i :=
    fun x=>(x.1.1,noisyBid i (eps,x))
  have hm : Measurable psi := (measurable_fst.comp measurable_fst).prodMk
    ((continuous_noisyBid i).comp (continuous_const.prodMk continuous_id)).measurable
  have hs : MeasurableSet {x : Value i×Bid i | x.2≠b} :=
    (measurableSet_eq_fun measurable_snd measurable_const).compl
  have hraw : ∀ᵐx ∂((pi.1 : Measure (Value i×unitInterval)).prod
      (volume : Measure unitInterval)),noisyBid i (eps,x)≠b := by
    apply (Measure.ae_prod_iff_ae_ae (hs.preimage hm)).mpr
    filter_upwards [original_value_positive i pi] with p hp
    exact LowBody.ae_injective_ne volume _ (noisyBid_injective_noise i eps heps p hp) b
  have hactual : ∀ᵐx ∂((physicalLaw i (eps,pi)).1 : Measure (Value i×Bid i)),x.2≠b :=
    (ae_map_iff hm.aemeasurable hs).mpr hraw
  change (((physicalLaw i (eps,pi)).1 : Measure (Value i×Bid i)).map Prod.snd) {b}=0
  rw [Measure.map_apply measurable_snd (measurableSet_singleton b)]
  exact measure_eq_zero_iff_ae_notMem.mpr hactual

theorem physical_bid_atomless (i : Row) (eps : unitInterval) (heps : 0<(eps:ℝ))
    (pi : Joint i) : NullSingletonClass (bidLaw i (eps,pi) : Measure (Bid i)) :=
  ⟨physical_bid_singleton i eps heps pi⟩

def restrictedLaw (i : Row) (p : unitInterval×Joint i) : Uniform05.RestrictedLaw i := by
  let phi : Value i×Bid i→ℝ×Bid i := fun x=>((x.1:ℝ),x.2)
  have hm : Measurable phi := (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  refine ⟨(physicalLaw i p).1.map hm.aemeasurable,?_,?_⟩
  · change (((physicalLaw i p).1 : Measure (Value i×Bid i)).map phi).map Prod.fst=_
    rw [Measure.map_map measurable_fst hm]
    change (((physicalLaw i p).1 : Measure (Value i×Bid i)).map
      (Subtype.val∘Prod.fst))=_
    rw [← Measure.map_map measurable_subtype_coe measurable_fst,
      (physicalLaw i p).property,lowerMeasure_real]
  · apply (ae_map_iff hm.aemeasurable (Uniform05.restrictedPair_measurable i)).mpr
    let psi : (Value i×unitInterval)×unitInterval→ Value i×Bid i :=
      fun x=>(x.1.1,noisyBid i (p.1,x))
    have hpsi : Measurable psi := (measurable_fst.comp measurable_fst).prodMk
      ((continuous_noisyBid i).comp (continuous_const.prodMk continuous_id)).measurable
    change ∀ᵐx ∂(((p.2.1 : Measure (Value i×unitInterval)).prod
      (volume : Measure unitInterval)).map psi),Uniform05.RestrictedPair i (phi x)
    apply (ae_map_iff hpsi.aemeasurable
      ((Uniform05.restrictedPair_measurable i).preimage hm)).mpr
    exact ae_of_all _ fun x=>⟨x.1.1.property,
      (noisyRealBid_bounds i p.1 x.1.1 x.1.2 x.2).1,
      (noisyRealBid_bounds i p.1 x.1.1 x.1.2 x.2).2.trans (min_le_left _ _)⟩

theorem restrictedLaw_bidLaw (i : Row) (p : unitInterval×Joint i) :
    (restrictedLaw i p).bidLaw=bidLaw i p := by
  apply Subtype.ext
  change (((physicalLaw i p).1 : Measure (Value i×Bid i)).map
    (fun x=>((x.1:ℝ),x.2))).map Prod.snd=_
  have hm : Measurable (fun x : Value i × Bid i => ((x.1 : ℝ), x.2)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  rw [Measure.map_map measurable_snd
    hm]
  rfl

theorem continuous_restrictedLaw (i : Row) : Continuous (restrictedLaw i) := by
  apply Continuous.subtype_mk
  exact (ProbabilityMeasure.continuous_map
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).comp
      (continuous_subtype_val.comp (continuous_physicalLaw i))

end FCAppendix.Affine.UniformFinite
