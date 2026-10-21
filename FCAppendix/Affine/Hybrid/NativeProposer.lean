import FCAppendix.Affine.Hybrid.NativeActivePriority

noncomputable section
namespace FCAppendix.Affine.Hybrid.NativeContinuation
open MeasureTheory ProbabilityTheory Game Set Bayes
variable {m c : ℕ}

theorem nativeGame_proposer_optimal (Gamma : FiniteGame m 2 c unitInterval)
    {U R η : ℝ} (hU : 0 ≤ U) (hR : U<R) (hη0 : 0 ≤ η) (hη1 : η<1)
    (hA : Gamma.A=Schedule.affine 2 η hη0 hη1.le) (hseed:Gamma.seedLaw=volume)
    (hfull : ∀ᵐd ∂userProfileLaw Gamma,d∈classifiedProfiles m U) :
    let C:=contextPolicy (m:=m) ((1-η)/2) (by linarith) (by linarith) c
    let game:=C.nativeGame Gamma U
    let belief:=classifiedPosterior game (R:=R) hfull
    ∀j L,FeasibleObservedList j L→∀s,
      Finite.Optimal c (beliefReceipts game.A (posteriorCountBelief game belief j L) L)
        (game.policy j L s).val:=by
  let hξ : 0<(1-η)/2:=by linarith
  let hξ1 : (1-η)/2<1:=by linarith
  let C:=contextPolicy (m:=m) ((1-η)/2) hξ hξ1 c
  exact ContextPolicy.nativeGame_proposer_optimal C Gamma hU hR hη0 hη1.le hA hfull
    (fun j L hL s=>contextPolicy_observed_lower_optimal ((1-η)/2) hξ hξ1 c Gamma hseed U j L hL s)

end FCAppendix.Affine.Hybrid.NativeContinuation
