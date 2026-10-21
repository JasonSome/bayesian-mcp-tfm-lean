import FCAppendix.Affine.Uniform07Finishing.Native.Concrete05Adapter

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Concrete05
open MeasureTheory ProbabilityTheory Game Bayes Set Classical
open FCAppendix.Affine

def lowerJointEncoding (row : Uniform07.Row)
    (p : UniformFinite.Value row×unitInterval) : ℝ×JointAction 2 :=
  ((p.1:ℝ),if 0<(p.1:ℝ) then UniformFinite.OriginalPopulation.lowerAction row p
    else Hybrid.lowBroadcast (d:=1) p.2)

theorem lowerJointEncoding_measurable (row : Uniform07.Row) :
    Measurable (lowerJointEncoding row) :=
  (measurable_subtype_coe.comp measurable_fst).prodMk
    (Measurable.ite
      (measurableSet_lt measurable_const (measurable_subtype_coe.comp measurable_fst))
      (UniformFinite.OriginalPopulation.measurable_lowerAction row)
      ((Hybrid.measurable_lowBroadcast 1).comp measurable_snd))

theorem lowerJointEncoding_embedding (row : Uniform07.Row) :
    MeasurableEmbedding (lowerJointEncoding row) := by
  apply (lowerJointEncoding_measurable row).measurableEmbedding
  rintro ⟨v,q⟩ ⟨w,r⟩ heq
  have hv : v=w := Subtype.ext (congrArg Prod.fst heq)
  subst w
  have ha:=congrArg Prod.snd heq
  refine Prod.ext (α := UniformFinite.Value row) (β := unitInterval) rfl ?_
  by_cases hp : 0<(v:ℝ)
  · exact (UniformFinite.NativeIC.lowerAction_embedding v hp).injective
      (by simpa only [lowerJointEncoding,if_pos hp] using ha)
  · have hq : (q:ℝ)=(r:ℝ) := by
      have hh:=congrArg JointAction.bid ha
      simpa only [lowerJointEncoding,if_neg hp,Hybrid.lowBroadcast] using hh
    exact Subtype.ext hq

theorem lowerJointEncoding_map {row : Uniform07.Row} {M : ℕ}
    (E : UniformFinite.ExactRestrictedLaw row M) :
    (E.pi.1 : Measure (UniformFinite.Value row×unitInterval)).map (lowerJointEncoding row)=
      (lowerJoint E : Measure (ℝ×JointAction 2)) := by
  rw [lowerJoint,UniformFinite.OriginalPopulation.lowerJoint,ProbabilityMeasure.toMeasure_map]
  apply Measure.map_congr
  filter_upwards [E.common_conull_contract] with p hp
  simp only [lowerJointEncoding,if_pos hp.1]
  rfl

theorem lowerJoint_ae_of_original {row : Uniform07.Row} {M : ℕ}
    (E : UniformFinite.ExactRestrictedLaw row M) (P : (ℝ×JointAction 2)→ Prop)
    (hP : ∀ᵐp∂(E.pi.1 : Measure (UniformFinite.Value row×unitInterval)),
      P ((p.1:ℝ),UniformFinite.OriginalPopulation.lowerAction row p)) :
    ∀ᵐx∂(lowerJoint E : Measure (ℝ×JointAction 2)),P x := by
  rw [←lowerJointEncoding_map E,(lowerJointEncoding_embedding row).ae_map_iff]
  filter_upwards [hP,E.common_conull_contract] with p hp hpos
  simpa only [lowerJointEncoding,if_pos hpos.1] using hp

end FCAppendix.Affine.Uniform07Finishing.Concrete05
