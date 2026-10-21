import FCAppendix.Affine.Uniform07Finishing.Crossover.Received05Family
import FCAppendix.Affine.Uniform07Finishing.Crossover.SameLawProducerAdapter

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover.Received05
open MeasureTheory ProbabilityTheory Game Bayes Set Classical
open FCAppendix.Affine Crossover.Physical

theorem compactBroadcastJoint_real (U : ℝ) (hU : 0≤ U)
    (PL : ProbabilityMeasure (ℝ×JointAction 2))
    (hPL : ∀ᵐx∂(PL : Measure (ℝ×JointAction 2)),x.2.bid≤ U) :
    (compactBroadcastJoint U hU PL : Measure (ℝ×Icc (0:ℝ) U)).map
      (fun z=>(z.1,(z.2:ℝ)))=
        (PL : Measure (ℝ×JointAction 2)).map (fun z=>(z.1,z.2.bid)) := by
  change ((PL : Measure (ℝ×JointAction 2)).map
    (fun z=>(z.1,compactBroadcastBid U hU z.2))).map (fun z=>(z.1,(z.2:ℝ)))=_
  have hout : Measurable (fun z : ℝ×Icc (0:ℝ) U=>(z.1,(z.2:ℝ))) := by
    simpa only [Function.comp_def] using
      (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))
  have hin : Measurable (fun z : ℝ×JointAction 2=>(z.1,compactBroadcastBid U hU z.2)) := by
    simpa only [Function.comp_def] using
      (measurable_fst.prodMk ((compactBroadcastBid_measurable U hU).comp measurable_snd))
  rw [Measure.map_map hout hin]
  apply Measure.map_congr
  filter_upwards [hPL] with z hz
  simp only [Function.comp_apply,compactBroadcastBid,min_eq_left hz]

theorem lowerJoint_real {row : Uniform07.Row} {m : ℕ}
    (E : UniformFinite.ExactRestrictedLaw row m) :
    (Concrete05.lowerJoint E : Measure (ℝ×JointAction 2)).map
      (fun z=>(z.1,z.2.bid))=Concrete05.realJoint E := by
  rw [realJoint_original]
  unfold Concrete05.lowerJoint UniformFinite.OriginalPopulation.lowerJoint
  rw [ProbabilityMeasure.toMeasure_map]
  have hout : Measurable (fun z : ℝ×JointAction 2=>(z.1,z.2.bid)) := by
    simpa only [Function.comp_def] using
      (measurable_fst.prodMk ((measurable_bid 2).comp measurable_snd))
  rw [Measure.map_map hout
    ((measurable_subtype_coe.comp measurable_fst).prodMk
      (UniformFinite.OriginalPopulation.measurable_lowerAction row))]
  rfl

theorem crossoverBroadcastLaw_real (D : UniformAuxiliaryData05)
    (row : Uniform07.Row) (k : ℕ)
    (E : UniformFinite.ExactRestrictedLaw row (D.start+k))
    (hD : (D.market row k).lower=Concrete05.lowerJoint E) :
    ((D.crossoverBroadcastLaw row k).lower :
        Measure (ℝ×Icc (0:ℝ) (Early.bidCap row))).map
      (fun z=>(z.1,(z.2:ℝ)))=Concrete05.realJoint E := by
  change (compactBroadcastJoint (Early.bidCap row) _ (D.market row k).lower :
    Measure (ℝ×Icc (0:ℝ) (Early.bidCap row))).map (fun z=>(z.1,(z.2:ℝ)))=_
  rw [compactBroadcastJoint_real _ _ _
    ((D.market row k).lower_routes.mono (fun _ hz=>hz.1)),hD,lowerJoint_real]

end FCAppendix.Affine.Uniform07Finishing.Crossover.Received05
