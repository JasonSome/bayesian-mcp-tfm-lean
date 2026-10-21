import FCAppendix.Affine.Hybrid.PopulationLaw
import FCAppendix.Affine.Hybrid.NativeProposer

noncomputable section
namespace FCAppendix.Affine.Hybrid.PopulationGame
open MeasureTheory ProbabilityTheory Set Game Bayes

local instance : Nonempty (JointAction 2):=⟨Interim.abstain 2⟩

def game (m c : ℕ) (P : ProbabilityMeasure (ℝ×JointAction 2))
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η<1) (U : ℝ) : FiniteGame m 2 c unitInterval where
  F:=(P : Measure (ℝ×JointAction 2)).fst
  hF:=inferInstance
  σ:=(P : Measure (ℝ×JointAction 2)).condKernel
  hσ:=inferInstance
  seedLaw:=volume
  hseed:=inferInstance
  policy:=(NativeContinuation.contextPolicy (m:=m) ((1-η)/2) (by linarith) (by linarith) c).localPolicy U
  policy_measurable:=(NativeContinuation.contextPolicy (m:=m) ((1-η)/2) (by linarith) (by linarith) c).measurable_selection U
  A:=Schedule.affine 2 η hη0 hη1.le
  G:=Schedule.once 2
  g:=0
  g_nonneg:=le_rfl

theorem joint_law (m c : ℕ) (P : ProbabilityMeasure (ℝ×JointAction 2))
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η<1) (U : ℝ) :
    (game m c P η hη0 hη1 U).F⊗ₘ(game m c P η hη0 hη1 U).σ=
      (P : Measure (ℝ×JointAction 2)) := by
  change (P : Measure (ℝ×JointAction 2)).fst⊗ₘ(P : Measure (ℝ×JointAction 2)).condKernel=_
  exact Measure.disintegrate _ _

def actionShape (U : ℝ) (a : JointAction 2) : Prop:=
  (a.bid≤U ∧ a.routeCount=2) ∨ (U<a.bid ∧ a.routeCount=1)

theorem profile_support (m c : ℕ) (P : ProbabilityMeasure (ℝ×JointAction 2))
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η<1) (U : ℝ)
    (hshape : ∀ᵐx ∂(P : Measure (ℝ×JointAction 2)),actionShape U x.2) :
    ∀ᵐd ∂userProfileLaw (game m c P η hη0 hη1 U),d∈classifiedProfiles m U := by
  let Gamma:=game m c P η hη0 hη1 U
  have hjoint : ∀ᵐx ∂Gamma.F⊗ₘGamma.σ,actionShape U x.2 := by
    simpa only [Gamma,joint_law] using hshape
  have hu : ∀ᵐu ∂userLaw Gamma,actionShape U u.1.2:=
    (measurePreserving_fst (μ:=Gamma.F⊗ₘGamma.σ) (ν:=permLaw 2)).quasiMeasurePreserving.ae hjoint
  exact ae_all_iff.mpr (fun i=>
    (measurePreserving_eval (fun _ : Fin m=>userLaw Gamma) i).quasiMeasurePreserving.ae hu)

theorem proposer_optimal (m c : ℕ) (P : ProbabilityMeasure (ℝ×JointAction 2))
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η<1) (U R : ℝ) (hU : 0 ≤ U) (hR : U<R)
    (hshape : ∀ᵐx ∂(P : Measure (ℝ×JointAction 2)),actionShape U x.2) :
    let Gamma:=game m c P η hη0 hη1 U
    let B:=classifiedPosterior Gamma (R:=R) (profile_support m c P η hη0 hη1 U hshape)
    ∀j L,FeasibleObservedList j L→∀seed,
      Finite.Optimal c (beliefReceipts Gamma.A (posteriorCountBelief Gamma B j L) L)
        (Gamma.policy j L seed).val := by
  exact NativeContinuation.nativeGame_proposer_optimal (game m c P η hη0 hη1 U)
    hU hR hη0 hη1 rfl rfl (profile_support m c P η hη0 hη1 U hshape)

end FCAppendix.Affine.Hybrid.PopulationGame
