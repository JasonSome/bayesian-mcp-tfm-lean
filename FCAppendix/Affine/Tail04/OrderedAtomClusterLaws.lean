import FCAppendix.Affine.Tail04.OrderedAtomClusterBound

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedAtomClusterLaws
open MeasureTheory ProbabilityTheory Set Classical Filter Topology
open Existence.Distributional OriginalValues CompactSourceBidLaws
open FiniteTailNoisyGame SourceTailNoisyFixedPoint LatentNoisyPopulation LatentSpeciesCalculus
open OrderedAtomActiveLaw OrderedAtomActiveGeometry
open scoped BigOperators

section NoisyLaw
variable {U : ℝ} (hU : 1≤ U)

def universalBid (p : unitInterval×(Icc (1:ℝ) U×unitInterval)) : Icc (1:ℝ) (2*U) :=
  ⟨Hybrid.activeNoisyRealBid p.1 p.2.1 p.2.2,by
    have hb := Hybrid.activeNoisyRealBid_mem (by norm_num : (0:ℝ)<1) p.1.2.1 p.2.1 p.2.2
    exact ⟨hb.1,hb.2.trans (by nlinarith [p.1.2.2])⟩⟩

lemma continuous_universalBid : Continuous (universalBid hU) := by
  apply Continuous.subtype_mk
  unfold Hybrid.activeNoisyRealBid
  fun_prop

def universalLaw (p : unitInterval×ProbabilityMeasure (Icc (1:ℝ) U)) :
    ProbabilityMeasure (Icc (1:ℝ) (2*U)) :=
  (productLaw p.2 uniformLaw).map (f:=fun z => universalBid hU (p.1,z))
    ((continuous_universalBid hU).comp (continuous_const.prodMk continuous_id)).measurable.aemeasurable

lemma integral_universalLaw (p : unitInterval×ProbabilityMeasure (Icc (1:ℝ) U))
    (f : C(Icc (1:ℝ) (2*U),ℝ)) :
    (∫ z,f z ∂(universalLaw hU p : Measure _))=
      ∫ b,∫ u : unitInterval,f (universalBid hU (p.1,(b,u)))
        ∂(volume : Measure unitInterval) ∂(p.2 : Measure _) := by
  change (∫ z,f z ∂(((p.2 : Measure _).prod (volume : Measure unitInterval)).map
    (fun z => universalBid hU (p.1,z))))=_
  have hc : Continuous (fun z : Icc (1:ℝ) U×unitInterval => universalBid hU (p.1,z)) :=
    (continuous_universalBid hU).comp (continuous_const.prodMk continuous_id)
  rw [integral_map hc.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  exact integral_prod _ ((ContinuousMap.equivBoundedOfCompact _ _
    (⟨_,f.continuous.comp ((continuous_universalBid hU).comp
      (continuous_const.prodMk continuous_id))⟩ : C(Icc (1:ℝ) U×unitInterval,ℝ))).integrable _)

theorem continuous_universalLaw : Continuous (universalLaw hU) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuousMap_continuous_integral.mpr
  intro f
  let g : unitInterval×Icc (1:ℝ) U→ℝ := fun q =>
    ∫ u : unitInterval,f (universalBid hU (q.1,(q.2,u)))
  have hinner : Continuous (fun z : (unitInterval×Icc (1:ℝ) U)×unitInterval =>
      f (universalBid hU (z.1.1,(z.1.2,z.2)))) :=
    f.continuous.comp ((continuous_universalBid hU).comp
      (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd)))
  have hg : Continuous g := (continuous_law_integral _ hinner).comp
    (continuous_id.prodMk (continuous_const : Continuous (fun _ => uniformLaw)))
  have hc := (continuous_law_integral g hg)
  simpa only [integral_universalLaw] using hc

def realUniversalLaw (p : unitInterval×ProbabilityMeasure (Icc (1:ℝ) U)) : ProbabilityMeasure ℝ :=
  (universalLaw hU p).map continuous_subtype_val.measurable.aemeasurable

lemma continuous_realUniversalLaw : Continuous (realUniversalLaw hU) :=
  (ProbabilityMeasure.continuous_map continuous_subtype_val).comp (continuous_universalLaw hU)

lemma realUniversalLaw_zero (μ : ProbabilityMeasure (Icc (1:ℝ) U)) :
    realUniversalLaw hU (0,μ)=μ.map continuous_subtype_val.measurable.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  change (((ProbabilityMeasure.toMeasure μ).prod (volume : Measure unitInterval)).map
      (fun z => universalBid hU (0,z))).map Subtype.val=(ProbabilityMeasure.toMeasure μ).map Subtype.val
  have hc : Continuous (fun z : Icc (1:ℝ) U×unitInterval => universalBid hU (0,z)) :=
    (continuous_universalBid hU).comp (continuous_const.prodMk continuous_id)
  rw [Measure.map_map measurable_subtype_coe hc.measurable]
  have he : (Subtype.val ∘ (fun z => universalBid hU (0,z)))=
      (Subtype.val : Icc (1:ℝ) U→ℝ) ∘ Prod.fst := by
    funext z
    simp [universalBid,Hybrid.activeNoisyRealBid]
  rw [he,←Measure.map_map measurable_subtype_coe measurable_fst,Measure.map_fst_prod,
    measure_univ,one_smul]

lemma realUniversalLaw_eq_noisy (eps : unitInterval) (μ : ProbabilityMeasure (Icc (1:ℝ) U)) :
    realUniversalLaw hU (eps,μ)=
      (noisyBidLaw (by norm_num : (0:ℝ)<1) eps.2.1 μ).map
        continuous_subtype_val.measurable.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  change (((ProbabilityMeasure.toMeasure μ).prod (volume : Measure unitInterval)).map
      (fun z => universalBid hU (eps,z))).map Subtype.val=
    (((ProbabilityMeasure.toMeasure μ).prod (volume : Measure unitInterval)).map
      (noisyBid (by norm_num : (0:ℝ)<1) eps.2.1)).map Subtype.val
  have hc : Continuous (fun z : Icc (1:ℝ) U×unitInterval => universalBid hU (eps,z)) :=
    (continuous_universalBid hU).comp (continuous_const.prodMk continuous_id)
  rw [Measure.map_map measurable_subtype_coe hc.measurable,
    Measure.map_map measurable_subtype_coe (continuous_noisyBid (by norm_num) eps.2.1).measurable]
  rfl

end NoisyLaw

variable (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)

def activeWeight : ℝ := P.bulkWeight+P.truncatedTailWeight t

include ht in
lemma activeWeight_pos : 0< activeWeight P t :=
  add_pos P.bulkWeight_pos (P.truncatedTailWeight_pos t ht)

def baseRealLaw (π : JointProfile D P t ht) : ProbabilityMeasure ℝ :=
  ((installOriginal D P t ht).commonLaw (bidLaws D P t ht π)).map
    continuous_subtype_val.measurable.aemeasurable

def physicalRealLaw (π : JointProfile D P t ht) : ProbabilityMeasure ℝ :=
  (noisyBidLaw (by norm_num : (0:ℝ)<1) D.heps.le
    ((installOriginal D P t ht).commonLaw (bidLaws D P t ht π))).map
      continuous_subtype_val.measurable.aemeasurable

lemma continuous_baseRealLaw : Continuous (baseRealLaw D P t ht) :=
  (ProbabilityMeasure.continuous_map continuous_subtype_val).comp
    (((installOriginal D P t ht).continuous_commonLaw).comp (continuous_bidLaws D P t ht))

lemma real_mixture_apply {X : Type*} [MeasurableSpace X]
    (p : unitInterval) (μ ν : ProbabilityMeasure X) (S : Set X) :
    (mixture p μ ν : Measure X).real S=(p:ℝ)*(μ : Measure X).real S+
      (1-(p:ℝ))*(ν : Measure X).real S := by
  change ((ENNReal.ofReal (p:ℝ) • (μ : Measure X)+
    ENNReal.ofReal (1-(p:ℝ)) • (ν : Measure X)) S).toReal=_
  rw [Measure.add_apply,Measure.smul_apply,Measure.smul_apply,smul_eq_mul,smul_eq_mul,
    ENNReal.toReal_add (by finiteness) (by finiteness),ENNReal.toReal_mul,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal p.2.1,ENNReal.toReal_ofReal (sub_nonneg.mpr p.2.2)]
  rfl

private lemma real_map_apply {X : Type*} [MeasurableSpace X]
    (ρ : ProbabilityMeasure X) {f : X→ℝ} (hf : Measurable f)
    (J : Set ℝ) (hJ : MeasurableSet J) :
    (ρ.map hf.aemeasurable : Measure ℝ).real J=ρ.toMeasure.real (f ⁻¹' J) := by
  rw [ProbabilityMeasure.toMeasure_map,measureReal_def,Measure.map_apply hf hJ]
  rfl

lemma baseRealLaw_formula (π : JointProfile D P t ht) (J : Set ℝ) (hJ : MeasurableSet J) :
    (baseRealLaw D P t ht π : Measure ℝ).real J=
      (originalBulkShare P t ht:ℝ)*(ProbabilityMeasure.toMeasure (π 0).1).real (typedCluster D P t 0 J)+
        (1-(originalBulkShare P t ht:ℝ))*(ProbabilityMeasure.toMeasure (π 1).1).real (typedCluster D P t 1 J) := by
  unfold baseRealLaw
  rw [real_map_apply _ measurable_subtype_coe J hJ]
  change (activeBaseLaw D.huU (originalBulkShare P t ht)
    (bidMarginal (π 0).1) (bidMarginal (π 1).1) : Measure _).real
      ((Subtype.val : Icc (1:ℝ) D.U→ℝ) ⁻¹' J)=_
  rw [activeBaseLaw,real_mixture_apply]
  congr 1
  · congr 1
    have houter := Measure.map_apply (μ:=(ProbabilityMeasure.toMeasure (π 0).1).map Prod.snd)
      (continuous_extendBid D.huU).measurable (hJ.preimage measurable_subtype_coe)
    have hinner := Measure.map_apply (μ:=ProbabilityMeasure.toMeasure (π 0).1) measurable_snd
      ((hJ.preimage measurable_subtype_coe).preimage (continuous_extendBid D.huU).measurable)
    simpa only [measureReal_def] using! congrArg ENNReal.toReal (houter.trans hinner)
  · congr 1
    have hinner := Measure.map_apply (μ:=ProbabilityMeasure.toMeasure (π 1).1) measurable_snd
      (hJ.preimage measurable_subtype_coe)
    simpa only [measureReal_def] using! congrArg ENNReal.toReal hinner

variable (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht) (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
local notation "μ" => drawLaw D P t ht πL π upperBid hupperBid

include πL upperBid hupperBid in
theorem original_open_mass (J : Set ℝ) (hJ : MeasurableSet J) :
    (μ).real (cluster D P t J)=activeWeight P t*(baseRealLaw D P t ht π : Measure ℝ).real J := by
  rw [original_cluster_mass D P t ht πL π upperBid hupperBid J hJ,baseRealLaw_formula D P t ht π J hJ]
  have ha := activeWeight_pos P t ht
  unfold originalBulkShare activeWeight
  change 0<P.bulkWeight+P.truncatedTailWeight t at ha
  dsimp only [Subtype.coe_mk]
  field_simp [ha.ne']
  ring

variable (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H)
  (hfloor : ∀ v,t< v→ H≤ upperBid v) (N : ℕ)
  (hrare : (1-D.ξ)*D.B+D.ξ*D.B*((N+1:ℕ)*
    (tailMass P t/(partialMass+tailMass P t)))≤ D.R)
local notation "tag" => latentTag D P hdR H hBH
local notation "bb" => latentBid D P hdR H hBH

include hfloor hrare in
include πL upperBid hupperBid hfloor N hrare in
theorem original_physical_mass (b r : ℝ) :
    (μ).real (physicalCarrier D P hdR H hBH b r)=
      activeWeight P t*(physicalRealLaw D P t ht π : Measure ℝ).real (Icc (b-3*r) (b+3*r)) := by
  let A : Set Draw := tag ⁻¹' {1}
  let J : Set (Icc (1:ℝ) D.B) := Subtype.val ⁻¹' Icc (b-3*r) (b+3*r)
  have hJ : MeasurableSet J := measurableSet_Icc.preimage measurable_subtype_coe
  have hmap : ((μ).restrict A).map bb=
      ENNReal.ofReal (activeWeight P t) • (ProbabilityMeasure.toMeasure (bidMarginal (NativeNoisySource.activePhysical D P t ht π).1)) := by
    calc
      _ = (μ A • cond μ A).map bb := by rw [Hybrid.measure_smul_cond]
      _ = μ A • (cond μ A).map bb := Measure.map_smul _ _ _
      _ = _ := by
        rw [original_common_projection D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare,
          original_category_mass D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare 1]
        rfl
  have hm := congrArg (fun ν : Measure (Icc (1:ℝ) D.B) => (ν J).toReal) hmap
  rw [Measure.map_apply (measurable_latentBid D P hdR H hBH) hJ,
    Measure.restrict_apply (hJ.preimage (measurable_latentBid D P hdR H hBH)),
    Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (activeWeight_pos P t ht).le,
    NoisyCommonRowLaw.original_common_noisy_law D P t ht π] at hm
  have he : bb ⁻¹' J∩A=physicalCarrier D P hdR H hBH b r := by
    ext z
    simp only [J,A,physicalCarrier,mem_inter_iff,mem_preimage,mem_singleton_iff,
      mem_setOf_eq,and_comm]
  rw [he] at hm
  change (μ).real (physicalCarrier D P hdR H hBH b r)=_ at hm
  unfold physicalRealLaw
  rw [real_map_apply _ measurable_subtype_coe _ measurableSet_Icc]
  simpa using! hm

end FCAppendix.Affine.Tail04.OrderedAtomClusterLaws

namespace FCAppendix.Affine.Tail04.OrderedAtomClusterLaws
open MeasureTheory ProbabilityTheory Set Classical Filter Topology
open Existence.Distributional OriginalValues CompactSourceBidLaws
open FiniteTailNoisyGame SourceTailNoisyFixedPoint

variable (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)

@[simp] lemma baseRealLaw_atNoise (eps : unitInterval) (heps : 0<(eps:ℝ))
    (hsmall : (eps:ℝ)< D.eps) (π : JointProfile D P t ht) :
    baseRealLaw (atNoise D eps heps hsmall) P t ht π=baseRealLaw D P t ht π := rfl

lemma physicalRealLaw_atNoise (eps : unitInterval) (heps : 0<(eps:ℝ))
    (hsmall : (eps:ℝ)< D.eps) (π : JointProfile D P t ht) :
    physicalRealLaw (atNoise D eps heps hsmall) P t ht π=
      realUniversalLaw D.hU (eps,(installOriginal D P t ht).commonLaw (bidLaws D P t ht π)) :=
  (realUniversalLaw_eq_noisy D.hU eps _).symm

theorem original_common_laws_tendsto
    (eps : ℕ→ unitInterval) (heps : ∀ j,0<(eps j:ℝ)) (hsmall : ∀ j,(eps j:ℝ)< D.eps)
    (π : ℕ→ JointProfile D P t ht) (π₀ : JointProfile D P t ht)
    (heps0 : Tendsto eps atTop (𝓝 0)) (hπ : Tendsto π atTop (𝓝 π₀)) :
    Tendsto (fun j => baseRealLaw D P t ht (π j)) atTop (𝓝 (baseRealLaw D P t ht π₀)) ∧
      Tendsto (fun j => physicalRealLaw (atNoise D (eps j) (heps j) (hsmall j)) P t ht (π j))
        atTop (𝓝 (baseRealLaw D P t ht π₀)) := by
  have hbase := (continuous_baseRealLaw D P t ht).continuousAt.tendsto.comp hπ
  refine ⟨hbase,?_⟩
  have hcommon := (((installOriginal D P t ht).continuous_commonLaw).comp
    (continuous_bidLaws D P t ht)).continuousAt.tendsto.comp hπ
  have hphys := (continuous_realUniversalLaw D.hU).continuousAt.tendsto.comp
    (heps0.prodMk_nhds hcommon)
  simpa only [physicalRealLaw_atNoise,realUniversalLaw_zero,baseRealLaw] using! hphys

theorem normalize_cluster_bound {a n A K q h g err : ℝ}
    (ha : 0< a) (hn : 0< n)
    (hfinite : A*n*(a*h)^2≤ K*n*q*(a*h)*(a*g)+err*(a*h)) :
    h^2*A≤ h*(K*q*g+err/(n*a)) := by
  apply (mul_le_mul_iff_left₀ (show 0< n*a^2 by positivity)).mp
  convert! hfinite using 1 <;> field_simp [ha.ne',hn.ne']

theorem separate_vanishing_flag_error {h g A K q z e : ℝ}
    (hh : 0≤ h) (hg : g≤1) (hK : 0≤ K) (hz : 0≤ z)
    (hfinite : h^2*A≤ h*(K*(2*q+z)*g+e)) :
    h^2*A≤ h*(2*K*q*g+(e+K*z)) := by
  have hs := mul_le_mul_of_nonneg_left hg (mul_nonneg hK hz)
  have hs' := mul_le_mul_of_nonneg_left hs hh
  nlinarith only [hfinite,hs']

end FCAppendix.Affine.Tail04.OrderedAtomClusterLaws
