import FCAppendix.Affine.Hybrid.ActivePattern

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory Set Filter Topology Classical
open scoped BigOperators
variable {N : ℕ}

def activePatternNoisyPayoff {d vlo vhi L U eps : ℝ} (hL : 0<L) (heps : 0≤eps)
    (xi z : ℝ) (c : ℕ) (kind : Fin N→Fin 4)
    (t : ActivePatternInput N d vlo vhi L U eps) (noise : unitInterval) : ℝ :=
  let T:=activePatternTemplate c kind
  let input:ℝ×(Fin (N+1)→ℝ):=(t.1.1,activePatternBids kind t)
  if activePatternGuarded xi L (U*(1+eps)) c z kind then
    guardedNoisyPayoff xi (1-2*xi) eps (activePatternResidual c z kind)
      (activePatternOwner c z kind 0) (activePatternOwner c z kind 1) (activePatternFocal kind)
      (activePatternGuardedInput hL heps kind t) noise
  else if T.residual₀=T.residual₁ then
    LowBody.equalNoisyPayoff xi eps T.residual₀ 0 input noise
  else T.noisyUserPayoff (1-xi) eps 0 input noise

def activePatternSmoothedPayoff {d vlo vhi L U eps : ℝ} (hL : 0<L) (heps : 0≤eps)
    (xi z : ℝ) (c : ℕ) (kind : Fin N→Fin 4)
    (t : ActivePatternInput N d vlo vhi L U eps) : ℝ :=
  let T:=activePatternTemplate c kind
  let input:ℝ×(Fin (N+1)→ℝ):=(t.1.1,activePatternBids kind t)
  if activePatternGuarded xi L (U*(1+eps)) c z kind then
    guardedSmoothedPayoff xi (1-2*xi) eps (activePatternResidual c z kind)
      (activePatternOwner c z kind 0) (activePatternOwner c z kind 1) (activePatternFocal kind)
      (activePatternGuardedInput hL heps kind t)
  else if T.residual₀=T.residual₁ then
    LowBody.equalSmoothedPayoff xi eps T.residual₀ 0 input
  else ∫noise,T.noisyUserPayoff (1-xi) eps 0 input noise ∂LowBody.uniformNoise

theorem activePatternSmoothedPayoff_eq_integral {d vlo vhi L U eps : ℝ}
    (hL : 0<L) (heps : 0≤eps) (xi z : ℝ) (c : ℕ) (kind : Fin N→Fin 4)
    (t : ActivePatternInput N d vlo vhi L U eps) :
    activePatternSmoothedPayoff hL heps xi z c kind t=
      ∫noise : unitInterval,activePatternNoisyPayoff hL heps xi z c kind t noise := by
  unfold activePatternSmoothedPayoff activePatternNoisyPayoff
  dsimp only
  split_ifs
  · rfl
  · exact (unitInterval.measurePreserving_coe.integral_comp unitInterval.measurableEmbedding_coe
      (LowBody.equalNoisyPayoff xi eps (activePatternTemplate c kind).residual₀ 0
        (t.1.1,activePatternBids kind t))).symm
  · exact (unitInterval.measurePreserving_coe.integral_comp unitInterval.measurableEmbedding_coe
      ((activePatternTemplate c kind).noisyUserPayoff (1-xi) eps 0
        (t.1.1,activePatternBids kind t))).symm

theorem continuous_activePatternSmoothedPayoff {d vlo vhi L U eps xi : ℝ}
    (hL : 0<L) (heps : 0<eps) (hxi : 0<xi) (hxi1 : xi<1)
    (z : ℝ) (c : ℕ) (kind : Fin N→Fin 4) :
    Continuous (activePatternSmoothedPayoff (d:=d) (vlo:=vlo) (vhi:=vhi) (U:=U)
      hL heps.le xi z c kind) := by
  let T:=activePatternTemplate c kind
  let input:ActivePatternInput N d vlo vhi L U eps→ℝ×(Fin (N+1)→ℝ):=
    fun t=>(t.1.1,activePatternBids kind t)
  have hc : Continuous input := (show Continuous (fun t : ActivePatternInput N d vlo vhi L U eps=>
      (t.1.1:ℝ)) from by fun_prop).prodMk (continuous_activePatternBids kind)
  unfold activePatternSmoothedPayoff
  dsimp only
  split_ifs with hg hequal
  · exact (continuous_guardedSmoothedPayoff hL heps xi (1-2*xi) (activePatternResidual c z kind)
      (activePatternOwner c z kind 0) (activePatternOwner c z kind 1) (activePatternFocal kind)
      hg.1 hg.2.2.1 hg.2.2.2.1).comp (continuous_activePatternGuardedInput hL heps.le kind)
  · rw [continuous_iff_continuousAt]
    intro t
    have hb : ∀j,0≤(input t).2 j := activePatternBids_nonneg hL kind t
    have hi : 0<(input t).2 0 := by
      change 0<(t.1.2:ℝ)
      exact hL.trans_le t.1.2.property.1
    exact (LowBody.continuousAt_equalSmoothedPayoff hxi hxi1 heps.le T.residual₀ 0
      (input t) hb hi).comp (f:=input) hc.continuousAt
  · rw [continuous_iff_continuousAt]
    intro t
    have hi : (input t).2 0≠0 := by
      change (t.1.2:ℝ)≠0
      exact (hL.trans_le t.1.2.property.1).ne'
    exact (LowBody.continuousAt_pureSmoothedPayoff (fun P : T.Candidate=>P.val)
      LowBody.uniformNoise LowBody.uniformNoise_support (by linarith : 0<1-xi) heps.ne'
      (0:Fin (N+1)) (input t) hi).comp (f:=input) hc.continuousAt

end FCAppendix.Affine.Hybrid
