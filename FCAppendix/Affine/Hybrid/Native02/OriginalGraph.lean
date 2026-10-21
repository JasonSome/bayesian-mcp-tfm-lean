import FCAppendix.Affine.Hybrid.Native02.SourceCountVersions

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes

theorem activeJoint_supported_graph (p : PrimitiveInput) (A : FrozenActiveFamily p)
    (pi : Existence.Distributional.Law (A:=p.Bid) (p.activeValues : Measure p.Value))
    (eps : ℝ)
    (h : ∀ᵐx ∂(pi.1 : Measure (p.Value×p.Bid)),|x.2.1-p.beta x.1|< eps) :
    ∀ᵐx ∂(activeJoint p.L_pos.le (p.activeValues : Measure p.Value) pi : Measure (ℝ×JointAction 2)),
      |x.2.bid-A.targetReal x.1|< eps := by
  have hm : MeasurableSet {x : ℝ×JointAction 2 | |x.2.bid-A.targetReal x.1|< eps} :=
    measurableSet_lt
      ((((measurable_bid 2).comp measurable_snd).sub
        (A.measurable_targetReal.comp measurable_fst)).abs) measurable_const
  apply (ae_map_iff (measurable_fst.subtype_val.prodMk
    ((measurable_activeBroadcast p.L_pos.le).comp measurable_snd)).aemeasurable hm).mpr
  filter_upwards [h] with x hx
  simpa only [Function.comp_def, activeBroadcast,A.targetReal_at_value] using hx

theorem original_joint_supported_graph (p : PrimitiveInput) (A : FrozenActiveFamily p)
    {m c : ℕ} (G : FiniteGame m 2 c unitInterval)
    (pi : Existence.Distributional.Law (A:=p.Bid) (p.activeValues : Measure p.Value))
    (PL PH : ProbabilityMeasure (ℝ×JointAction 2))
    (hjoint : G.F⊗ₘG.σ=populationJoint p.s p.a p.h PL
      (activeJoint p.L_pos.le (p.activeValues : Measure p.Value) pi) PH)
    (hL : ∀ᵐx ∂(PL : Measure (ℝ×JointAction 2)),x.1≤ p.d)
    (hH : ∀ᵐx ∂(PH : Measure (ℝ×JointAction 2)),p.vhi< x.1)
    (eps : ℝ)
    (h : ∀ᵐx ∂(pi.1 : Measure (p.Value×p.Bid)),|x.2.1-p.beta x.1|< eps) :
    ∀ᵐx ∂G.F⊗ₘG.σ,x.1∈ Icc p.vlo p.vhi→|x.2.bid-A.targetReal x.1|< eps := by
  have hdl : p.d< p.vlo := (p.d_lt_L.trans p.L_lt_U).trans p.value_surplus
  rw [hjoint]
  apply original_population_mixture_ae
  · filter_upwards [hL] with x hx
    intro hv
    exact False.elim ((not_lt.mpr (hv.1.trans hx)) hdl)
  · exact (activeJoint_supported_graph p A pi eps h).mono (fun _ hx _=> hx)
  · filter_upwards [hH] with x hx
    intro hv
    exact False.elim ((not_lt.mpr hv.2) hx)

end FCAppendix.Affine.Hybrid.Native02
