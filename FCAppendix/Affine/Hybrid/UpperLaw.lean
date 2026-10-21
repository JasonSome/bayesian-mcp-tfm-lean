import FCAppendix.Affine.Hybrid.PopulationUpper
import FCAppendix.Existence.UpperEnvelope

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory ProbabilityTheory Game Bayes Set

def upperAction (b : ℝ→ℝ) (v : ℝ) : JointAction 2:=⟨max (b v) 0,le_max_right _ _,1,by norm_num⟩

theorem measurable_upperAction (b : ℝ→ℝ) (hb : Measurable b) : Measurable (upperAction b) := by
  apply Measurable.of_comap_le
  rw [instMeasurableSpaceJointAction,MeasurableSpace.comap_comp]
  exact ((hb.max measurable_const).prodMk measurable_const).comap_le

def upperJoint (FH : ProbabilityMeasure ℝ) (b : ℝ→ℝ) (hb : Measurable b) :
    ProbabilityMeasure (ℝ×JointAction 2):=
  FH.map (measurable_id.prodMk (measurable_upperAction b hb)).aemeasurable

theorem upperJoint_value_marginal (FH : ProbabilityMeasure ℝ) (b : ℝ→ℝ) (hb : Measurable b) :
    (upperJoint FH b hb : Measure (ℝ×JointAction 2)).map Prod.fst=(FH : Measure ℝ) := by
  change ((FH : Measure ℝ).map (fun v=>(v,upperAction b v))).map Prod.fst=_
  have hf : Measurable (fun v : ℝ=>(v,upperAction b v)):=measurable_id.prodMk (measurable_upperAction b hb)
  rw [Measure.map_map measurable_fst hf]
  exact Measure.map_id

theorem upperJoint_bid_marginal (FH : ProbabilityMeasure ℝ) (b : ℝ→ℝ) (hb : Measurable b)
    (hpos : ∀ᵐv ∂(FH : Measure ℝ),0 ≤ b v) :
    (upperJoint FH b hb : Measure (ℝ×JointAction 2)).map (fun x=>x.2.bid)=
      (FH : Measure ℝ).map b := by
  change ((FH : Measure ℝ).map (fun v=>(v,upperAction b v))).map (fun x=>x.2.bid)=_
  have hm : Measurable (fun x : ℝ×JointAction 2=>x.2.bid):=(measurable_bid 2).comp measurable_snd
  have hf : Measurable (fun v : ℝ=>(v,upperAction b v)):=measurable_id.prodMk (measurable_upperAction b hb)
  rw [Measure.map_map hm hf]
  apply Measure.map_congr
  exact hpos.mono (fun _ hv=>max_eq_left hv)

theorem upperJoint_support (FH : ProbabilityMeasure ℝ) (b : ℝ→ℝ) (hb : Measurable b)
    (R : ℝ) (hfloor : ∀ᵐv ∂(FH : Measure ℝ),R ≤ b v) :
    ∀ᵐx ∂(upperJoint FH b hb : Measure (ℝ×JointAction 2)),R ≤ x.2.bid ∧ x.2.routeCount=1 := by
  apply (ae_map_iff (measurable_id.prodMk (measurable_upperAction b hb)).aemeasurable
    ((measurableSet_le measurable_const ((measurable_bid 2).comp measurable_snd)).inter
      (measurableSet_eq_fun ((measurable_routeCount 2).comp measurable_snd) measurable_const))).mpr
  filter_upwards [hfloor] with v hv
  change R ≤ max (b v) 0 ∧ (1:ℕ)=1
  exact ⟨hv.trans (le_max_left _ _),rfl⟩

theorem upperJoint_atomless (FH : ProbabilityMeasure ℝ) (b : ℝ→ℝ) (hb : Measurable b)
    (hpos : ∀ᵐv ∂(FH : Measure ℝ),0 ≤ b v) [NullSingletonClass ((FH : Measure ℝ).map b)] :
    ∀y : ℝ,(upperJoint FH b hb : Measure (ℝ×JointAction 2)) {x | x.2.bid=y}=0 := by
  intro y
  have hm : Measurable (fun x : ℝ×JointAction 2=>x.2.bid):=(measurable_bid 2).comp measurable_snd
  have hz:=measure_singleton (μ:=(FH : Measure ℝ).map b) y
  rw [←upperJoint_bid_marginal FH b hb hpos,
    Measure.map_apply hm (measurableSet_singleton y)] at hz
  exact hz

theorem exists_upper_joint (FH : ProbabilityMeasure ℝ) [NullSingletonClass (FH : Measure ℝ)]
    (h : ℝ) (hh : 0<h) (hh1 : h ≤ 1) (r c : ℕ) (hc : 1 ≤ c) (hcr : c ≤ r+1)
    (t R H : ℝ) (hR : 0<R) (hRt : R<t)
    (hsupport : ∀ᵐv ∂(FH : Measure ℝ),v∈Icc t H) :
    let mu:=ENNReal.ofReal h • (FH : Measure ℝ)
    let q:=Existence.RankEnvelope.rank mu (r+1) c 2
    let b:=Existence.RankEnvelope.bid q t R
    ∃PH : ProbabilityMeasure (ℝ×JointAction 2),
      (PH : Measure (ℝ×JointAction 2)).map Prod.fst=(FH : Measure ℝ) ∧
      (PH : Measure (ℝ×JointAction 2)).map (fun x=>x.2.bid)=(FH : Measure ℝ).map b ∧
      (∀ᵐx ∂(PH : Measure (ℝ×JointAction 2)),R ≤ x.2.bid ∧ x.2.routeCount=1) ∧
      (∀y : ℝ,(PH : Measure (ℝ×JointAction 2)) {x | x.2.bid=y}=0) := by
  dsimp only
  let mu:=ENNReal.ofReal h • (FH : Measure ℝ)
  let q:=Existence.RankEnvelope.rank mu (r+1) c 2
  let b:=Existence.RankEnvelope.bid q t R
  have hmass : mu.real univ ≤ 1:=by
    simp only [mu,Measure.real,Measure.smul_apply,smul_eq_mul,measure_univ,mul_one,
      ENNReal.toReal_ofReal hh.le]
    exact hh1
  letI : IsFiniteMeasure mu:=⟨by simp only [mu,Measure.smul_apply,smul_eq_mul,measure_univ,mul_one];exact ENNReal.ofReal_lt_top⟩
  letI : NullSingletonClass mu:=⟨fun y=>by simp only [mu,Measure.smul_apply,smul_eq_mul,measure_singleton,mul_zero]⟩
  have hs : ∀ᵐv ∂mu,v∈Icc t H:=Measure.ae_smul_measure hsupport _
  have hp:=Existence.RankEnvelope.upper_envelope_bounded mu r c hc hcr hmass t R H hR hRt hs
  have hb : Measurable b:=hp.continuous_bid.measurable
  have hfloor : ∀ᵐv ∂(FH : Measure ℝ),R ≤ b v:=
    hsupport.mono (fun v hv=>(hp.bid_bounds v hv.1).1)
  have hpos : ∀ᵐv ∂(FH : Measure ℝ),0 ≤ b v:=hfloor.mono (fun _ hv=>hR.le.trans hv)
  letI : NullSingletonClass ((FH : Measure ℝ).map b):=by
    constructor
    intro y
    have hz:=hp.atomless.measure_singleton y
    change (mu.map b) {y}=0 at hz
    rw [Measure.map_smul,Measure.smul_apply,smul_eq_mul] at hz
    exact (mul_eq_zero.mp hz).resolve_left (ENNReal.ofReal_ne_zero_iff.mpr hh)
  exact ⟨upperJoint FH b hb,upperJoint_value_marginal FH b hb,upperJoint_bid_marginal FH b hb hpos,
    upperJoint_support FH b hb R hfloor,upperJoint_atomless FH b hb hpos⟩

end FCAppendix.Affine.Hybrid
