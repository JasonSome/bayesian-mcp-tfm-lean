import FCAppendix.Affine.LowBody.ActualLowStrategy
import FCAppendix.Affine.Hybrid.NativeRows

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory ProbabilityTheory Set Game Bayes
open Existence.Distributional

def lowBroadcast {d : ℝ} (b : LowBody.LowValue d) : JointAction 2:=
  ⟨b.1,b.property.1,2,le_rfl⟩

theorem measurable_lowBroadcast (d : ℝ) : Measurable (lowBroadcast (d:=d)) := by
  apply Measurable.of_comap_le
  rw [instMeasurableSpaceJointAction,MeasurableSpace.comap_comp]
  exact (measurable_subtype_coe.prodMk measurable_const).comap_le

def lowJoint {d : ℝ} (mu : Measure (LowBody.LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A:=LowBody.LowValue d) mu) : ProbabilityMeasure (ℝ×JointAction 2):=
  pi.1.map (measurable_fst.subtype_val.prodMk
    ((measurable_lowBroadcast d).comp measurable_snd)).aemeasurable

theorem lowJoint_value_marginal {d : ℝ}
    (mu : Measure (LowBody.LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A:=LowBody.LowValue d) mu) :
    (lowJoint mu pi : Measure (ℝ×JointAction 2)).map Prod.fst=mu.map Subtype.val := by
  change ((pi.1 : Measure (LowBody.LowValue d×LowBody.LowValue d)).map
    (fun x=>(x.1.1,lowBroadcast x.2))).map Prod.fst=_
  have hf : Measurable (fun x : LowBody.LowValue d×LowBody.LowValue d=>
    (x.1.1,lowBroadcast x.2)):=
      measurable_fst.subtype_val.prodMk ((measurable_lowBroadcast d).comp measurable_snd)
  rw [Measure.map_map measurable_fst hf]
  calc
    _=((pi.1 : Measure (LowBody.LowValue d×LowBody.LowValue d)).map Prod.fst).map Subtype.val:=
      (Measure.map_map measurable_subtype_coe measurable_fst).symm
    _=mu.map Subtype.val:=by rw [pi.2]

theorem lowJoint_bid_marginal {d : ℝ}
    (mu : Measure (LowBody.LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A:=LowBody.LowValue d) mu) :
    (lowJoint mu pi : Measure (ℝ×JointAction 2)).map (fun x=>x.2.bid)=
      (LowBody.realLowBidLaw pi.1 : Measure ℝ) := by
  change ((pi.1 : Measure (LowBody.LowValue d×LowBody.LowValue d)).map
    (fun x=>(x.1.1,lowBroadcast x.2))).map (fun x=>x.2.bid)=_
  have hf : Measurable (fun x : LowBody.LowValue d×LowBody.LowValue d=>
    (x.1.1,lowBroadcast x.2)):=
      measurable_fst.subtype_val.prodMk ((measurable_lowBroadcast d).comp measurable_snd)
  have hb : Measurable (fun x : ℝ×JointAction 2=>x.2.bid):=
    (measurable_bid 2).comp measurable_snd
  rw [Measure.map_map hb hf]
  rfl

def populationJoint (s a h : ℝ) (PL PA PH : ProbabilityMeasure (ℝ×JointAction 2)) :
    Measure (ℝ×JointAction 2):=
  ENNReal.ofReal s • (PL : Measure (ℝ×JointAction 2))+
    ENNReal.ofReal a • (PA : Measure (ℝ×JointAction 2))+
    ENNReal.ofReal h • (PH : Measure (ℝ×JointAction 2))

theorem populationJoint_probability (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h)
    (hsum : s+a+h=1) (PL PA PH : ProbabilityMeasure (ℝ×JointAction 2)) :
    IsProbabilityMeasure (populationJoint s a h PL PA PH) := by
  constructor
  simp only [populationJoint,Measure.add_apply,Measure.smul_apply,smul_eq_mul,measure_univ,mul_one]
  rw [←ENNReal.ofReal_add hs ha,←ENNReal.ofReal_add (add_nonneg hs ha) hh,hsum,ENNReal.ofReal_one]

def populationLaw (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h)
    (hsum : s+a+h=1) (PL PA PH : ProbabilityMeasure (ℝ×JointAction 2)) :
    ProbabilityMeasure (ℝ×JointAction 2):=
  ⟨populationJoint s a h PL PA PH,populationJoint_probability s a h hs ha hh hsum PL PA PH⟩

theorem populationJoint_value_marginal {d : ℝ} (s a h : ℝ)
    (mu : Measure (LowBody.LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A:=LowBody.LowValue d) mu) (PA PH : ProbabilityMeasure (ℝ×JointAction 2)) :
    (populationJoint s a h (lowJoint mu pi) PA PH).map Prod.fst=
      ENNReal.ofReal s • mu.map Subtype.val+
      ENNReal.ofReal a • (PA : Measure (ℝ×JointAction 2)).map Prod.fst+
      ENNReal.ofReal h • (PH : Measure (ℝ×JointAction 2)).map Prod.fst := by
  rw [populationJoint,Measure.map_add _ _ measurable_fst,Measure.map_add _ _ measurable_fst]
  simp only [Measure.map_smul,lowJoint_value_marginal]

end FCAppendix.Affine.Hybrid
