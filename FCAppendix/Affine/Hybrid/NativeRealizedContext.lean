import FCAppendix.Affine.Hybrid.NativePayoffIntegral
import FCAppendix.Affine.Hybrid.NativeAllocationCounts
import FCAppendix.Game.RealizedPlay

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory ProbabilityTheory Game Bayes LowBody Classical

theorem focalCount_eq_inserted_count {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Gamma : FiniteGame m 2 c Seed) (i : Fin m) (v : ℝ) (a : JointAction 2)
    (profile : UserProfile m 2) (s : Fin 2→Seed) (tau : Equiv.Perm (Fin 2)) :
    (focalCount Gamma i a ((profile,s),tau)).val=
      inclusionCount (drawsRealization (Function.update profile i ((v,a),tau))) Gamma.policy s i := by
  exact (congrArg Fin.val (playedCount_insertDraw Gamma i (((v,a),tau),(profile,s)))).symm

theorem native_broadcast_realized_context_payoff {m c : ℕ}
    (Gamma : FiniteGame m 2 c unitInterval) {η U : ℝ} (hη0 : 0 ≤ η) (hη1 : η<1)
    (hA : Gamma.A=Schedule.affine 2 η hη0 hη1.le) (hg : Gamma.g=0)
    (i : Fin m) (v : ℝ) (a : JointAction 2) (ha : a.bid ≤ U)
    (profile : UserProfile m 2) (s : Fin 2→unitInterval) (tau : Equiv.Perm (Fin 2))
    (hz : Function.update profile i ((v,a),tau)∈classifiedProfiles m U) :
    let ξ:=(1-η)/2
    let C:=NativeContinuation.contextPolicy (m:=m) ξ (by dsimp only [ξ];linarith)
      (by dsimp only [ξ];linarith) c
    let z:=Function.update profile i ((v,a),tau)
    nativeRealizedPayoff (C.nativeGame Gamma U) i v a ((profile,s),tau)=
      purePayoff (1-ξ) v (fun k=>entryBid ((actualContext U z).1 k))
        (C.selectionPair (actualContext U z) s) i := by
  dsimp only
  let ξ:=(1-η)/2
  let C:=NativeContinuation.contextPolicy (m:=m) ξ (by dsimp only [ξ];linarith)
    (by dsimp only [ξ];linarith) c
  let z:=Function.update profile i ((v,a),tau)
  have hi : (z i).1.2.bid ≤ U:=by simpa only [z,Function.update_self] using ha
  have hc:=C.native_inclusionCount_eq_focalCopy Gamma U z hz s i hi
  have hb:=NativeContinuation.actualContext_entryBid U z hz i hi
  have hbid : (z i).1.2.bid=a.bid:=by simp only [z,Function.update_self]
  rw [hbid] at hb
  change userPayoff v a.bid Gamma.g Gamma.A.charge Gamma.G.charge
    (focalCount (C.nativeGame Gamma U) i a ((profile,s),tau)).val=_
  rw [focalCount_eq_inserted_count,hc,hA,hg,←hb]
  rw [NativeContinuation.affine_count_payoff_eq_pure η hη0 hη1.le v
    (fun k=>entryBid ((actualContext U z).1 k)) (C.selectionPair (actualContext U z) s) i Gamma.G.charge]
  congr 1
  ring

end FCAppendix.Affine.Hybrid
