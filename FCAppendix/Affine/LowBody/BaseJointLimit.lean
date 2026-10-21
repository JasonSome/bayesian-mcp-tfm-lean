import FCAppendix.Affine.LowBody.NoiseTestCloseness
import FCAppendix.Affine.LowBody.NoisyBaseLaw

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set Filter Topology
open Existence.Distributional

def baseJointLaw (d ε : ℝ) (hε : 0<ε) (hsmall : ε≤1/2)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A:=unitInterval) mu) : ProbabilityMeasure (LowValue d×LowValue d) :=
  pi.1.map (measurable_fst.prodMk (continuous_baseBid d ε hε hsmall).measurable).aemeasurable

theorem baseJointLaw_tendsto {d : ℝ}
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (eps : ℕ→ℝ) (heps : ∀j,0<eps j) (hsmall : ∀j,eps j≤1/2)
    (pi : ℕ→Law (A:=unitInterval) mu) (pi0 : Law (A:=LowValue d) mu)
    (heps0 : Tendsto eps atTop (𝓝 0))
    (hlim : Tendsto (fun j=>(lowNoisyLaw d (eps j) (heps j) (hsmall j) mu (pi j)).1)
      atTop (𝓝 pi0.1)) :
    Tendsto (fun j=>baseJointLaw d (eps j) (heps j) (hsmall j) mu (pi j)) atTop (𝓝 pi0.1) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  let M (j : ℕ) : Measure ((LowValue d×unitInterval)×unitInterval):=
    ((pi j).1 : Measure (LowValue d×unitInterval)).prod (volume : Measure unitInterval)
  letI (j : ℕ) : IsProbabilityMeasure (M j):=inferInstanceAs
    (IsProbabilityMeasure (((pi j).1 : Measure (LowValue d×unitInterval)).prod (volume : Measure unitInterval)))
  have hbcont (j : ℕ) : Continuous (fun x : (LowValue d×unitInterval)×unitInterval=>
      f (basePhysicalPoint d (eps j) (heps j) (hsmall j) x.1)) := by
    apply f.continuous.comp
    exact (continuous_fst.prodMk (continuous_baseBid d (eps j) (heps j) (hsmall j))).comp continuous_fst
  have hpcont (j : ℕ) : Continuous (fun x : (LowValue d×unitInterval)×unitInterval=>
      f (noisyPhysicalPoint d (eps j) (heps j) (hsmall j) x)) := by
    apply f.continuous.comp
    exact continuous_fst.fst.prodMk (continuous_noisyBid d (eps j) (heps j) (hsmall j))
  have hbi (j : ℕ) : Integrable (fun x=>f (basePhysicalPoint d (eps j) (heps j) (hsmall j) x.1)) (M j) :=
    (ContinuousMap.equivBoundedOfCompact _ _ ⟨_,hbcont j⟩).integrable _
  have hpi (j : ℕ) : Integrable (fun x=>f (noisyPhysicalPoint d (eps j) (heps j) (hsmall j) x)) (M j) :=
    (ContinuousMap.equivBoundedOfCompact _ _ ⟨_,hpcont j⟩).integrable _
  have hbase (j : ℕ) :
      (∫x,f x ∂(baseJointLaw d (eps j) (heps j) (hsmall j) mu (pi j) : Measure _))=
      ∫x,f (basePhysicalPoint d (eps j) (heps j) (hsmall j) x.1) ∂M j := by
    rw [integral_prod _ (hbi j)]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
    exact integral_map (measurable_fst.prodMk (continuous_baseBid d (eps j) (heps j) (hsmall j)).measurable).aemeasurable
      f.continuous.aestronglyMeasurable
  have hphys (j : ℕ) :
      (∫x,f x ∂((lowNoisyLaw d (eps j) (heps j) (hsmall j) mu (pi j)).1 : Measure _))=
      ∫x,f (noisyPhysicalPoint d (eps j) (heps j) (hsmall j) x) ∂M j :=
    integral_map ((measurable_fst.comp measurable_fst).prodMk
      (continuous_noisyBid d (eps j) (heps j) (hsmall j)).measurable).aemeasurable
      f.continuous.aestronglyMeasurable
  have hclose : Tendsto (fun j=>
      (∫x,f x ∂(baseJointLaw d (eps j) (heps j) (hsmall j) mu (pi j) : Measure _))-
      ∫x,f x ∂((lowNoisyLaw d (eps j) (heps j) (hsmall j) mu (pi j)).1 : Measure _)) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro eta heta
    filter_upwards [eventually_noisy_test_close f.toContinuousMap eps heps hsmall heps0 (half_pos heta)] with j hj
    rw [Real.dist_eq,sub_zero,hbase,hphys,←integral_sub (hbi j) (hpi j),←Real.norm_eq_abs]
    have hh:=norm_integral_le_of_norm_le (integrable_const (μ:=M j) (eta/2))
      (ae_of_all (M j) (fun x=>by
        rw [Real.norm_eq_abs,abs_sub_comm]
        exact (hj x).le))
    have hh' : ‖∫x,f (basePhysicalPoint d (eps j) (heps j) (hsmall j) x.1)-
        f (noisyPhysicalPoint d (eps j) (heps j) (hsmall j) x) ∂M j‖≤eta/2 := by
      simpa only [BoundedContinuousFunction.coe_toContinuousMap,integral_const,probReal_univ,smul_eq_mul,one_mul] using hh
    exact hh'.trans_lt (half_lt_self heta)
  have hp := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) f
  simpa only [sub_add_cancel,zero_add] using hclose.add hp

end FCAppendix.Affine.LowBody
