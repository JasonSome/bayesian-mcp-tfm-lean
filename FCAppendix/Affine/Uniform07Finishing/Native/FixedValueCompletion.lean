import FCAppendix.Affine.Uniform07Finishing.Native.GlobalUserIC
import FCAppendix.Affine.Uniform07Finishing.Native.UniformOutcomes

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical

variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma measurableSet_commonBestResponse_at (Γ : FiniteGame m 2 c Seed) (v : ℝ) :
    MeasurableSet {a : JointAction 2 | ∀ u : Fin m, ∀ d : JointAction 2,
      (problem Γ u).payoff v d≤(problem Γ u).payoff v a} := by
  have he : {a : JointAction 2 | ∀ u : Fin m, ∀ d : JointAction 2,
      (problem Γ u).payoff v d≤(problem Γ u).payoff v a} =
      ⋂ u : Fin m, (fun a : JointAction 2=>(v,a)) ⁻¹'
        {z | (problem Γ u).BestResponse z.1 z.2} := by
    ext a
    simp only [mem_setOf_eq,mem_iInter,mem_preimage,Interim.Problem.BestResponse]
  rw [he]
  exact MeasurableSet.iInter (fun u=>(measurableSet_bestResponse Γ u).preimage
    (measurable_const.prodMk measurable_id))

theorem exists_full_positive_uniform_version
    (Γ : FiniteGame m 2 c Seed) (U t : ℝ) (ht : 0< t) (ht1 : t≤ 1)
    (hF : Γ.F=Uniform07.uniformLaw) (hg : Γ.g=0)
    (hΓ : IsBayesianEquilibrium Γ) (hVis : VisibleAtomless Γ)
    (hshape : ∀ᵐ z ∂Γ.F⊗ₘΓ.σ, z.1∈Ioo 0 t → z.2.bid≤ U ∧ z.2.routeCount=2)
    (hpay : ∀ u : Fin m, ∀ z : ℝ×Icc (0:ℝ) U, 0<(z.2:ℝ) →
      ContinuousAt (fun w : ℝ×Icc (0:ℝ) U =>
        (problem Γ u).payoff w.1 (sourceLowerBroadcastAction U w.2)) z)
    (upper : ℝ→ JointAction 2)
    (hupperRoute : ∀ v, (upper v).routeCount=1)
    (hupperKernel : ∀ v, t≤ v → Γ.σ v=Measure.dirac (upper v))
    (hupperIC : ∀ v, t≤ v → ∀ u : Fin m, ∀ a : JointAction 2,
      (problem Γ u).payoff v a≤(problem Γ u).payoff v (upper v)) :
    ∃ κ : Kernel ℝ (JointAction 2), ∃ hκM : IsMarkovKernel κ,
      κ=ᵐ[Γ.F]Γ.σ ∧
      (∀ v, v∉Ioo 0 t → κ v=Γ.σ v) ∧
      IsBayesianEquilibrium (@withStrategy m 2 c Seed _ Γ κ hκM) ∧
      VisibleAtomless (@withStrategy m 2 c Seed _ Γ κ hκM) ∧
      (∀ v, 0< v → v≤ 1 → ∀ᵐ a ∂κ v, ∀ u : Fin m, ∀ d : JointAction 2,
        (problem (@withStrategy m 2 c Seed _ Γ κ hκM) u).payoff v d≤
          (problem (@withStrategy m 2 c Seed _ Γ κ hκM) u).payoff v a) ∧
      (∀ v, 0< v → v< t → ∀ᵐ a ∂κ v, a.bid≤ U ∧ a.routeCount=2) ∧
      (∀ v, t≤ v → κ v=Measure.dirac (upper v)) ∧
      (∀ v, 0< v → v≤ 1 → v≠t → ∀ᵐ a ∂κ v,
        a.routeCount=if v< t then 2 else 1) := by
  have hcommon:=actual_lower_common_good_of_usersOptimal Γ U t hΓ.users hshape
  obtain ⟨κ,hκM,hκ,hjoint,hoff,hlow⟩:=exists_actual_lower_fixed_value_version
    Γ U t ht ht1 hF hg hpay hcommon
  letI : IsMarkovKernel κ:=hκM
  let G:=withStrategy Γ κ
  have huKernel (v : ℝ) (hv:t≤ v) : κ v=Measure.dirac (upper v) := by
    rw [hoff v (fun h=>not_lt_of_ge hv h.2),hupperKernel v hv]
  have hupperBest (v : ℝ) (hv:t≤ v) :
      ∀ᵐ a ∂κ v, ∀ u : Fin m, ∀ d : JointAction 2,
        (problem G u).payoff v d≤(problem G u).payoff v a := by
    rw [huKernel v hv]
    apply (ae_dirac_iff (measurableSet_commonBestResponse_at G v)).mpr
    intro u d
    simpa only [G,withStrategy_payoff Γ κ hκ] using hupperIC v hv u d
  refine ⟨κ,hκM,hκ,hoff,withStrategy_bayesian_equilibrium Γ κ hκ hΓ,
    withStrategy_visible_atomless Γ κ hκ hVis,?_,?_,huKernel,?_⟩
  · intro v hv hv1
    by_cases hvt:v< t
    · filter_upwards [hlow v hv hvt] with a ha
      exact ha.2.2
    · exact hupperBest v (le_of_not_gt hvt)
  · intro v hv hvt
    filter_upwards [hlow v hv hvt] with a ha
    exact ⟨ha.1,ha.2.1⟩
  · intro v hv hv1 hne
    by_cases hvt:v< t
    · filter_upwards [hlow v hv hvt] with a ha
      simpa only [if_pos hvt] using ha.2.1
    · rw [huKernel v (le_of_not_gt hvt)]
      apply (ae_dirac_iff ((measurable_routeCount 2)
        (measurableSet_singleton (if v< t then 2 else 1)))).mpr
      simpa only [if_neg hvt, Set.mem_singleton_iff] using hupperRoute v

theorem withStrategy_lower_moment_errors
    (row : Uniform07.Row) (Γ : FiniteGame m 2 c Seed)
    (κ : Kernel ℝ (JointAction 2)) [IsMarkovKernel κ] (hκ : κ=ᵐ[Γ.F]Γ.σ)
    (ε : ℝ)
    (hmom : ∀ u : Fin m, ∀ b : Icc (0:ℝ) (Early.bidCap row),
      |((problem Γ u).outcome (sourceLowerBroadcastAction (Early.bidCap row) b)).load-
        2*sourceProductProbability row b|≤ε ∧
      |((problem Γ u).outcome (sourceLowerBroadcastAction (Early.bidCap row) b)).duplicates-
        (sourceProductProbability row b)^2|≤ε) :
    ∀ u : Fin m, ∀ b : Icc (0:ℝ) (Early.bidCap row),
      |((problem (withStrategy Γ κ) u).outcome
        (sourceLowerBroadcastAction (Early.bidCap row) b)).load-
          2*sourceProductProbability row b|≤ε ∧
      |((problem (withStrategy Γ κ) u).outcome
        (sourceLowerBroadcastAction (Early.bidCap row) b)).duplicates-
          (sourceProductProbability row b)^2|≤ε := by
  intro u b
  simpa only [withStrategy_outcome Γ κ hκ] using hmom u b

theorem withStrategy_upper_conditional_count
    (Γ : FiniteGame m 2 c Seed) (κ : Kernel ℝ (JointAction 2)) [IsMarkovKernel κ]
    (hκ : κ=ᵐ[Γ.F]Γ.σ) (hm:0< m) (v : ℝ) (hv:κ v=Γ.σ v) :
    conditionalTypeCountLaw (withStrategy Γ κ) hm v=conditionalTypeCountLaw Γ hm v := by
  unfold conditionalTypeCountLaw
  congr 1
  funext u
  exact withStrategy_typeOutcome_of_kernel_eq Γ κ hκ u v hv

end FCAppendix.Affine.Uniform07Finishing
