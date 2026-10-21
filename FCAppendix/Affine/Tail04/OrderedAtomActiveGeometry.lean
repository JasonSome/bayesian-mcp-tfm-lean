import FCAppendix.Affine.Tail04.OrderedAtomFiniteGain
import FCAppendix.Affine.Tail04.OrderedAtomActiveIC
import FCAppendix.Affine.Tail04.ActiveNoisyClusterGeometry
import FCAppendix.Affine.Tail04.OrderedAtomSupport

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedAtomActiveGeometry
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation
open SourceTailNoisyFixedPoint LatentNoisyPopulation LatentSpeciesCalculus
open OrderedAtomActiveLaw OrderedAtomActiveIC OrderedAtomSupport
open OriginalActiveCrossingCarrier ActiveNoisyClusterGeometry
open scoped BigOperators

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ)

def activeRecord (z : Draw) : Prop :=
  (label z=bandSpecies 0 ∧ bandRecord D P t 0 z) ∨
    (label z=bandSpecies 1 ∧ bandRecord D P t 1 z)

lemma measurableSet_activeRecord : MeasurableSet {z | activeRecord D P t z} :=
  ((measurableSet_eq_fun measurable_label measurable_const).inter
    (measurableSet_bandRecord D P t 0)).union
      ((measurableSet_eq_fun measurable_label measurable_const).inter
        (measurableSet_bandRecord D P t 1))

def cluster (J : Set ℝ) : Set Draw :=
  {z | activeRecord D P t z ∧ baseBid z∈J}

lemma measurableSet_cluster (J : Set ℝ) (hJ : MeasurableSet J) :
    MeasurableSet (cluster D P t J) :=
  (measurableSet_activeRecord D P t).inter (hJ.preimage measurable_baseBid)

lemma record_base_bounds (z : Draw) (hz : activeRecord D P t z) :
    baseBid z∈Icc (1:ℝ) D.U := by
  rcases hz with hz | hz
  · exact ⟨hz.2.2.1.1,hz.2.2.1.2.trans D.huU⟩
  · exact hz.2.2.1

lemma record_value_bounds (ht : P.M< t) (z : Draw) (hz : activeRecord D P t z) :
    value z∈Icc (P.vA-P.w) t := by
  rcases hz with hz | hz
  · exact ⟨hz.2.1.1,hz.2.1.2.trans (P.active_tail_gap.trans ht).le⟩
  · have hvlo : P.M≤value z := hz.2.1.1
    exact ⟨(by linarith [P.active_tail_gap,P.w_pos,hvlo]),hz.2.1.2⟩

lemma record_realize_bid (z : Draw) (hz : activeRecord D P t z) :
    (realize D z).1.2.bid=baseBid z*(1+D.eps*(z.1.2:ℝ)) := by
  rcases hz with hz | hz
  · have hl : z.1.1.1=bandSpecies 0 := hz.1
    simp [realize,implementJoint,hl,bandSpecies,noisyJoint,noisyAction,baseBid]
  · have hl : z.1.1.1=bandSpecies 1 := hz.1
    simp [realize,implementJoint,hl,bandSpecies,noisyJoint,noisyAction,baseBid]

lemma record_realize_bounds (z : Draw) (hz : activeRecord D P t z) :
    (realize D z).1.2.bid∈Icc (1:ℝ) D.B := by
  rw [record_realize_bid D P t z hz]
  have hb := record_base_bounds D P t z hz
  exact Hybrid.activeNoisyRealBid_mem (by norm_num : (0:ℝ)<1) D.heps.le
    (⟨baseBid z,hb⟩ : Icc (1:ℝ) D.U) z.1.2

variable (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H)
local notation "E" => NativeNoisySource.regions D P hdR H hBH

lemma record_tag (z : Draw) (hz : activeRecord D P t z) :
    latentTag D P hdR H hBH z=1 := by
  have hb := record_realize_bounds D P t z hz
  have hl : ¬(realize D z).1.2.bid≤ (E).d :=
    not_le.mpr ((E).d_lt_one.trans_le hb.1)
  have hp : (realize D z).1.2.bid∉(E).privateBids := by
    rintro (hp | hp)
    · linarith [(E).Rp_lt_one,hp.2,hb.1]
    · have hp' : H≤(realize D z).1.2.bid := hp
      linarith [hBH,hb.2]
  simp only [latentTag,Observable.Regions.coarseTag,Observable.Regions.collapse,
    if_neg hl,if_neg hp]

lemma record_latentBid (z : Draw) (hz : activeRecord D P t z) :
    (latentBid D P hdR H hBH z:ℝ)=baseBid z*(1+D.eps*(z.1.2:ℝ)) := by
  have hb := record_realize_bounds D P t z hz
  change (OriginalValues.clipToBand 1 (E).U (E).one_le_U (realize D z).1.2.bid:ℝ)=_
  rw [OriginalValues.clipToBand_eq 1 (E).U (E).one_le_U hb,
    record_realize_bid D P t z hz]

def physicalCarrier (b r : ℝ) : Set Draw :=
  {z | latentTag D P hdR H hBH z=1 ∧
    (latentBid D P hdR H hBH z:ℝ)∈Icc (b-3*r) (b+3*r)}

lemma measurableSet_physicalCarrier (b r : ℝ) :
    MeasurableSet (physicalCarrier D P hdR H hBH b r) :=
  (measurableSet_eq_fun (measurable_latentTag D P hdR H hBH) measurable_const).inter
    (measurableSet_Icc.preimage ((measurable_latentBid D P hdR H hBH).subtype_val))

theorem cluster_geometry (heps : D.eps≤1) (b r : ℝ) (hr : 0< r)
    (hnoise : D.eps*D.U≤ r) (y : Icc (1:ℝ) D.U) (hy : (y:ℝ)=b+2*r)
    (z : Draw) (hz : z∈cluster D P t (Ioo (b-r) (b+r))) :
    b-r<(latentBid D P hdR H hBH z:ℝ) ∧
      (latentBid D P hdR H hBH z:ℝ)< raisedBid D y z ∧
      b+2*r≤(raisedBid D y z:ℝ) ∧ (raisedBid D y z:ℝ)≤ b+3*r ∧
      (raisedBid D y z:ℝ)-(latentBid D P hdR H hBH z:ℝ)<6*r := by
  have hh := open_cluster_geometry D.heps.le heps hr hnoise
    (show b+2*r≤ D.U by rw [←hy];exact y.2.2)
    {z | activeRecord D P t z} baseBid (fun z : Draw => z.1.2)
    (record_base_bounds D P t) z hz
  simpa only [physical,raised,record_latentBid D P t hdR H hBH z hz.1,
    raisedBid,CompactSourceBidLaws.noisyBid,Hybrid.activeNoisyRealBid,hy] using hh

theorem cluster_ordered (b r : ℝ) (hr : 0< r) (hnoise : D.eps*D.U≤ r)
    (y : Icc (1:ℝ) D.U) (hy : (y:ℝ)=b+2*r)
    (x z : Draw) (hx : x∈cluster D P t (Ioo (b-r) (b+r)))
    (hz : z∈cluster D P t (Ioo (b-r) (b+r))) :
    (latentBid D P hdR H hBH z:ℝ)< raisedBid D y x := by
  have hh := cluster_rival_below_raised D.heps.le hr hnoise
    {z | activeRecord D P t z} baseBid (fun z : Draw => z.1.2)
      (record_base_bounds D P t) x z hx hz
  simpa only [physical,raised,record_latentBid D P t hdR H hBH z hz.1,
    raisedBid,CompactSourceBidLaws.noisyBid,Hybrid.activeNoisyRealBid,hy] using hh

theorem crossing_in_physicalCarrier (heps : D.eps≤1) (b r : ℝ) (hr : 0< r)
    (hnoise : D.eps*D.U≤ r) (y : Icc (1:ℝ) D.U) (hy : (y:ℝ)=b+2*r)
    (x z : Draw) (hx : x∈cluster D P t (Ioo (b-r) (b+r)))
    (hz : crossing {z | latentTag D P hdR H hBH z=1}
      (fun z => (latentBid D P hdR H hBH z:ℝ)) (fun z => (raisedBid D y z:ℝ)) x z) :
    z∈physicalCarrier D P hdR H hBH b r := by
  have hg := cluster_geometry D P t hdR H hBH heps b r hr hnoise y hy x hx
  exact ⟨hz.1,by linarith [hz.2.1],hz.2.2.trans hg.2.2.2.1⟩

section OriginalMeasure
variable (ht : P.M< t)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht) (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
local notation "μ" => drawLaw D P t ht πL π upperBid hupperBid

include ht πL π upperBid hupperBid in
theorem cluster_ae_union (J : Set ℝ) :
    cluster D P t J=ᵐ[μ] Set.union (bandCluster 0 J) (bandCluster 1 J) := by
  filter_upwards [original_band_record D P t ht πL π upperBid hupperBid 0,
    original_band_record D P t ht πL π upperBid hupperBid 1] with z h0 h1
  apply propext
  constructor
  · rintro ⟨(hz | hz),hJ⟩
    · exact Or.inl ⟨hz.1,hJ⟩
    · exact Or.inr ⟨hz.1,hJ⟩
  · rintro (hz | hz)
    · exact ⟨Or.inl ⟨hz.1,h0 hz.1⟩,hz.2⟩
    · exact ⟨Or.inr ⟨hz.1,h1 hz.1⟩,hz.2⟩

lemma bandClusters_disjoint (J : Set ℝ) : Disjoint (bandCluster 0 J) (bandCluster 1 J) := by
  apply Set.disjoint_left.mpr
  intro z h0 h1
  have hh := h0.1.symm.trans h1.1
  exact (by decide : bandSpecies 0≠bandSpecies 1) hh

include ht πL π upperBid hupperBid in
theorem original_cluster_restriction (J : Set ℝ) (hJ : MeasurableSet J) :
    (μ).restrict (cluster D P t J)=(μ).restrict (bandCluster 0 J)+(μ).restrict (bandCluster 1 J) := by
  rw [Measure.restrict_congr_set (cluster_ae_union D P t ht πL π upperBid hupperBid J)]
  exact Measure.restrict_union (bandClusters_disjoint J) (measurableSet_bandCluster 1 J hJ)

include πL upperBid hupperBid in
theorem original_cluster_mass (J : Set ℝ) (hJ : MeasurableSet J) :
    (μ).real (cluster D P t J)=
      P.bulkWeight*((π 0).1 : Measure _).real (typedCluster D P t 0 J)+
        P.truncatedTailWeight t*((π 1).1 : Measure _).real (typedCluster D P t 1 J) := by
  have hh := congrArg (fun ν : Measure Draw => ν.real univ)
    (original_cluster_restriction D P t ht πL π upperBid hupperBid J hJ)
  rw [measureReal_add_apply] at hh
  simp only [measureReal_def,Measure.restrict_apply_univ] at hh
  change (μ).real (cluster D P t J)=(μ).real (bandCluster 0 J)+(μ).real (bandCluster 1 J) at hh
  rw [hh,original_band_cluster_mass D P t ht πL π upperBid hupperBid 0 J hJ,
    original_band_cluster_mass D P t ht πL π upperBid hupperBid 1 J hJ]
  rfl

lemma gain_bound_on_cluster (N : ℕ) (y : Icc (1:ℝ) D.U) (J : Set ℝ)
    (z : Draw×(Fin N→ Draw)) (hz : z.1∈cluster D P t J) :
    ‖gain D P t ht π hdR H hBH N y z‖≤2*(|P.vA-P.w|+|t|+2*D.B) := by
  have hv := record_value_bounds D P t ht z.1 hz.1
  have hav : |value z.1|≤|P.vA-P.w|+|t| := by
    apply abs_le.mpr
    constructor <;> linarith [hv.1,hv.2,neg_abs_le (P.vA-P.w),le_abs_self t,
      abs_nonneg (P.vA-P.w),abs_nonneg t]
  rw [Real.norm_eq_abs]
  unfold gain
  exact (abs_sub _ _).trans (by
    linarith [physicalValue_bound D P t ht π hdR H hBH N (value z.1) (raisedBid D y z.1) z.2,
      physicalValue_bound D P t ht π hdR H hBH N (value z.1)
        (latentBid D P hdR H hBH z.1) z.2])

variable (hfloor : ∀ v,t< v→ H≤ upperBid v) (N : ℕ)
  (hrare : (1-D.ξ)*D.B+D.ξ*D.B*((N+1:ℕ)*
    (tailMass P t/(partialMass+tailMass P t)))≤ D.R)

include hfloor hrare in
include πL upperBid hupperBid hfloor hrare in
theorem original_both_cluster_IC (y : Icc (1:ℝ) (1+D.u))
    (J : Set ℝ) (hJ : MeasurableSet J)
    (hC1 : ∀ k : Fin 3,AllActionOptimal (π k) (fun x => SourceOrderedNoisyFixedPoint.payoff D P t ht N k (π,x))) :
    (∫ z,gain D P t ht π hdR H hBH N (activeBase D 0 (by decide) y) z
      ∂((μ).restrict (cluster D P t J)).prod (Measure.pi (fun _ : Fin N => μ)))≤0 := by
  let yT : Icc (1:ℝ) D.U := activeBase D 0 (by decide) y
  have h0 := original_cluster_IC D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare
    0 (by decide) y J hJ (hC1 0)
  have h1 := original_cluster_IC D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare
    1 (by decide) yT J hJ (hC1 1)
  have hy : activeBase D 1 (by decide) yT=yT := by apply Subtype.ext;rfl
  rw [hy] at h1
  have hi (k : Fin 3) (hk : k≠2) : Integrable
      (gain D P t ht π hdR H hBH N yT)
      (((μ).restrict (bandCluster k J)).prod (Measure.pi (fun _ : Fin N => μ))) := by
    apply Integrable.of_bound (measurable_gain D P t ht π hdR H hBH N yT).aestronglyMeasurable
      (bound D P t k)
    have hp : ∀ᵐ z ∂((μ).restrict (bandCluster k J)).prod (Measure.pi (fun _ : Fin N => μ)),
        bandRecord D P t k z.1 := by
      have hr := original_band_record D P t ht πL π upperBid hupperBid k
      have hs : ∀ᵐ x ∂(μ).restrict (bandCluster k J),bandRecord D P t k x := by
        filter_upwards [ae_restrict_of_ae hr,ae_restrict_mem (measurableSet_bandCluster k J hJ)] with x hr hx
        exact hr hx.1
      exact (measurePreserving_fst («μ»:=(μ).restrict (bandCluster k J))
        («ν»:=Measure.pi (fun _ : Fin N => μ))).quasiMeasurePreserving.ae hs
    filter_upwards [hp] with z hz
    have hv : |value z.1|≤|valueLo P k|+|valueHi P t k| := by
      apply abs_le.mpr
      constructor <;> linarith [hz.1.1,hz.1.2,neg_abs_le (valueLo P k),
        le_abs_self (valueHi P t k),abs_nonneg (valueLo P k),abs_nonneg (valueHi P t k)]
    rw [Real.norm_eq_abs]
    unfold gain bound
    exact (abs_sub _ _).trans (by
      linarith [physicalValue_bound D P t ht π hdR H hBH N (value z.1) (raisedBid D yT z.1) z.2,
        physicalValue_bound D P t ht π hdR H hBH N (value z.1)
          (latentBid D P hdR H hBH z.1) z.2])
  rw [original_cluster_restriction D P t ht πL π upperBid hupperBid J hJ,
    Measure.add_prod,integral_add_measure (hi 0 (by decide)) (hi 1 (by decide))]
  exact add_nonpos h0 h1

include hfloor hrare in
include πL upperBid hupperBid hfloor hrare in
theorem original_tail_cluster_IC (y : Icc (1:ℝ) D.U)
    (J : Set ℝ) (hJ : MeasurableSet J) (hJbulk : ∀ x∈J,1+D.u< x)
    (hC1 : AllActionOptimal (π 1) (fun x => SourceOrderedNoisyFixedPoint.payoff D P t ht N 1 (π,x))) :
    (∫ z,gain D P t ht π hdR H hBH N y z
      ∂((μ).restrict (cluster D P t J)).prod (Measure.pi (fun _ : Fin N => μ)))≤0 := by
  have hb0 : (μ).restrict (bandCluster 0 J)=0 := by
    apply Measure.restrict_eq_zero.mpr
    have ha : ∀ᵐ z ∂μ,z∉bandCluster 0 J := by
      filter_upwards [original_band_record D P t ht πL π upperBid hupperBid 0] with z hz
      intro hc
      have hb := (hz hc.1).2.1.2
      exact (not_lt_of_ge hb) (hJbulk (baseBid z) hc.2)
    simpa only [not_not,Set.setOf_mem_eq] using ae_iff.mp ha
  rw [original_cluster_restriction D P t ht πL π upperBid hupperBid J hJ,hb0,zero_add]
  have hi := original_cluster_IC D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare
    1 (by decide) y J hJ hC1
  have he : activeBase D 1 (by decide) y=y := by apply Subtype.ext;rfl
  rwa [he] at hi

include hfloor hrare in
include πL upperBid hupperBid hfloor hrare in
theorem original_active_cluster_IC (y : Icc (1:ℝ) D.U)
    (J : Set ℝ) (hJ : MeasurableSet J)
    (hlegal : (y:ℝ)≤1+D.u ∨ ∀ x∈J,1+D.u< x)
    (hC1 : ∀ k : Fin 3,AllActionOptimal (π k) (fun x => SourceOrderedNoisyFixedPoint.payoff D P t ht N k (π,x))) :
    (∫ z,gain D P t ht π hdR H hBH N y z
      ∂((μ).restrict (cluster D P t J)).prod (Measure.pi (fun _ : Fin N => μ)))≤0 := by
  rcases hlegal with hbulk | htail
  · let yB : Icc (1:ℝ) (1+D.u) := ⟨y,y.2.1,hbulk⟩
    have hi := original_both_cluster_IC D P t hdR H hBH ht πL π upperBid hupperBid
      hfloor N hrare yB J hJ hC1
    have he : activeBase D 0 (by decide) yB=y := by apply Subtype.ext;rfl
    rwa [he] at hi
  · exact original_tail_cluster_IC D P t hdR H hBH ht πL π upperBid hupperBid
      hfloor N hrare y J hJ htail (hC1 1)

include hfloor hrare in
include πL upperBid hupperBid hfloor hrare in
theorem original_active_cluster_IC_with_bulk_null (y : Icc (1:ℝ) D.U)
    (J : Set ℝ) (hJ : MeasurableSet J)
    (hlegal : (y:ℝ)≤1+D.u ∨ (∀ x∈J,1+D.u< x) ∨
      ((π 0).1 : Measure _) (typedCluster D P t 0 J)=0)
    (hC1 : ∀ k : Fin 3,AllActionOptimal (π k) (fun x => SourceOrderedNoisyFixedPoint.payoff D P t ht N k (π,x))) :
    (∫ z,gain D P t ht π hdR H hBH N y z
      ∂((μ).restrict (cluster D P t J)).prod (Measure.pi (fun _ : Fin N => μ)))≤0 := by
  rcases hlegal with hbulk | habove | hnull
  · exact original_active_cluster_IC D P t hdR H hBH ht πL π upperBid hupperBid
      hfloor N hrare y J hJ (Or.inl hbulk) hC1
  · exact original_active_cluster_IC D P t hdR H hBH ht πL π upperBid hupperBid
      hfloor N hrare y J hJ (Or.inr habove) hC1
  · have hz : (μ).restrict (bandCluster 0 J)=0 := by
      rw [drawLaw_restrict_bandCluster D P t ht πL π upperBid hupperBid 0 J hJ,
        Measure.restrict_eq_zero.mpr hnull]
      simp only [Measure.zero_prod,Measure.map_zero,smul_zero]
    rw [original_cluster_restriction D P t ht πL π upperBid hupperBid J hJ,hz,zero_add]
    have hi := original_cluster_IC D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare
      1 (by decide) y J hJ (hC1 1)
    have he : activeBase D 1 (by decide) y=y := by apply Subtype.ext;rfl
    rwa [he] at hi

end OriginalMeasure
end FCAppendix.Affine.Tail04.OrderedAtomActiveGeometry
