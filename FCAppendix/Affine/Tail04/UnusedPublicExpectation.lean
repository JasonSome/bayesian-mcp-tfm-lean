import FCAppendix.Affine.Tail04.UnusedStrongGuard

noncomputable section
namespace FCAppendix.Affine.Tail04.UnusedPublicExpectation
open MeasureTheory ProbabilityTheory Set Classical
open PublicScenario EqualPrivateSignal LocalHighCommon JoinedHighPolicy
open OriginalFlagCompression UnusedPublicLaw
open scoped BigOperators

local instance (α : Type*) : TopologicalSpace (Finset α) := ⊥
local instance (α : Type*) : DiscreteTopology (Finset α) := ⟨rfl⟩
local instance (α : Type*) : MeasurableSpace (Finset α) := ⊤
local instance (α : Type*) : BorelSpace (Finset α) := ⟨borel_eq_top_of_discrete.symm⟩

theorem expect_le_full_flags {N : ℕ} (Q : PublicScenario.Data) (A : ℕ) (hA : 0< A)
    (H : ℕ×ℕ) (b : Fin A→ℝ) (active : Fin N→ Bool) (e : Fin A≃Active active)
    (p : Bool→ Fin N→ unitInterval)
    (hp : ∀reg j,sourceFlagProb ((PublicScenario.e0 Q) reg) Q.B0 b j=(p reg (e j).val:ℝ))
    (g : Scenario A→ℝ) (f : Bool→(Fin N→ unitInterval)→ℝ)
    (_hf : ∀reg,Measurable (f reg))
    (hi : ∀reg,Integrable (f reg) (Measure.pi (fun _ : Fin N=>(volume:Measure unitInterval))))
    (hbound : ∀reg u target AB,
      (Hybrid.ownerDivision
        (forcedExclusiveSet target (compressedFlags active e (OriginalFlagMeasure.flags (p reg) u)))
        (PublicScenario.ownerQuota Q A H reg (target,compressedFlags active e
          (OriginalFlagMeasure.flags (p reg) u)))).mass AB≠0 →
      g (outputScenario reg ((target,compressedFlags active e
        (OriginalFlagMeasure.flags (p reg) u)),AB))≤ f reg u) :
    (scenarioLaw Q A H b).expect g≤
      (1-Q.θ)*(∫u,f false u ∂Measure.pi (fun _ : Fin N=>(volume:Measure unitInterval)))+
        Q.θ*(∫u,f true u ∂Measure.pi (fun _ : Fin N=>(volume:Measure unitInterval))) := by
  letI : Nonempty (Fin A):=⟨⟨0,hA⟩⟩
  rw [scenario_expect Q A hA H b]
  have hr (reg : Bool) :
      (Hybrid.rankLaw b).expect (fun target=>
        (independentFlagLaw (sourceFlagProb ((PublicScenario.e0 Q) reg) Q.B0 b)
          (sourceFlagProb_nonneg _ _ b) (sourceFlagProb_le_one _ _ b)).expect (fun flags=>
            (Hybrid.ownerDivision (forcedExclusiveSet target flags)
              (PublicScenario.ownerQuota Q A H reg (target,flags))).expect
                (fun AB=> g (outputScenario reg ((target,flags),AB)))))≤
      ∫u,f reg u ∂Measure.pi (fun _ : Fin N=>(volume:Measure unitInterval)) := by
    apply FiniteLaw.expect_le_const_of_support
    intro target _
    let v : (Fin A→ Bool)→ℝ:=fun flags=>
      (Hybrid.ownerDivision (forcedExclusiveSet target flags)
        (PublicScenario.ownerQuota Q A H reg (target,flags))).expect
          (fun AB=> g (outputScenario reg ((target,flags),AB)))
    have hv (flags : Fin A→ Bool) : ‖v flags‖≤∑s : Scenario A,‖g s‖ := by

      have hg (s : Scenario A) : ‖g s‖≤∑s : Scenario A,‖g s‖ :=
        Finset.single_le_sum (fun s _=> norm_nonneg (g s)) (Finset.mem_univ s)
      have hh:=(Hybrid.ownerDivision (forcedExclusiveSet target flags)
        (PublicScenario.ownerQuota Q A H reg (target,flags))).abs_expect_le
          (fun AB=> g (outputScenario reg ((target,flags),AB)))
      have hk:=(Hybrid.ownerDivision (forcedExclusiveSet target flags)
        (PublicScenario.ownerQuota Q A H reg (target,flags))).expect_le_const
          (fun AB=> by simpa only [Real.norm_eq_abs] using hg (outputScenario reg ((target,flags),AB)))
      simpa only [Real.norm_eq_abs] using hh.trans hk
    have hm : Measurable (fun u=> v (compressedFlags active e (OriginalFlagMeasure.flags (p reg) u))) :=
      (measurable_of_countable (fun flags : Fin N→ Bool=> v (compressedFlags active e flags))).comp
        (OriginalFlagMeasure.measurable_flags (p reg))
    have hvI : Integrable (fun u=> v (compressedFlags active e (OriginalFlagMeasure.flags (p reg) u)))
        (Measure.pi (fun _ : Fin N=>(volume:Measure unitInterval))) :=
      Integrable.of_bound hm.aestronglyMeasurable _ (ae_of_all _ fun u=> hv _)
    have he : sourceFlagProb ((PublicScenario.e0 Q) reg) Q.B0 b=(fun j=>(p reg (e j).val:ℝ)) := funext (hp reg)
    change (independentFlagLaw _ _ _).expect v≤_
    calc
      _=(∫ u : Fin N→unitInterval,
          v (compressedFlags active e (OriginalFlagMeasure.flags (p reg) u))
            ∂Measure.pi (fun _ : Fin N=>(volume:Measure unitInterval))) := by
        simpa only [he] using!
          (@OriginalFlagMeasure.flag_expect_compression (Fin N) (Fin.fintype N)
            (fun a b => Classical.propDecidable (a=b)) active A e (p reg) v).trans
              (OriginalFlagMeasure.flag_expect (p reg) (fun z => v (compressedFlags active e z)))
      _≤_ := by
        apply integral_mono_ae hvI (hi reg)
        exact ae_of_all _ fun u=> by
          dsimp only [v]
          apply FiniteLaw.expect_le_const_of_support
          intro AB hAB
          exact hbound reg u target AB hAB
  have hh:=FiniteLaw.expect_mono (IndependentCounts.bernoulli Q.θ Q.θ_nonneg Q.θ_le_one) hr
  simpa only [IndependentCounts.expect_bernoulli] using hh

end FCAppendix.Affine.Tail04.UnusedPublicExpectation
