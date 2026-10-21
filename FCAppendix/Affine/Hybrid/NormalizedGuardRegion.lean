import FCAppendix.Affine.Hybrid.TypicalGuardedData

noncomputable section
namespace FCAppendix.Affine.Hybrid
open Set Filter Topology Classical

def sourceExposure (a h ρ z : ℝ) : ℝ:=((ρ-h/2)/a-z/2)/(1-z)
def sourceCountPoint (a h ρ z : ℝ) : Fin 4→ℝ:=![a,ρ-h/2,z*a/2,0]
def normalizedMixed (p : Fin 4→ℝ) : ℝ:=p 0-2*p 2-p 3
def normalizedResidual (p : Fin 4→ℝ) : ℝ:=p 1-p 2
def normalizedFactor (ξ : ℝ) (p : Fin 4→ℝ) : ℝ:=
  1-ξ*(normalizedResidual p/normalizedMixed p)

def NormalizedGuardRegion (ξ L U : ℝ) (p : Fin 4→ℝ) : Prop:=
  0<normalizedMixed p ∧ 0<normalizedResidual p ∧ normalizedResidual p<normalizedMixed p ∧
    0<normalizedFactor ξ p ∧ (1-ξ)*U<normalizedFactor ξ p*L ∧ normalizedFactor ξ p*U<L

theorem exists_normalized_guard_neighborhood (a h ρ z ξ L U : ℝ)
    (ha : 0 < a) (hz : z<1) (hξ : 0 < ξ) (hξ1 : ξ<1)
    (hq0 : 0<sourceExposure a h ρ z) (hq1 : sourceExposure a h ρ z<1)
    (hboxlo : (1-ξ)*U<(1-ξ*sourceExposure a h ρ z)*L)
    (hboxhi : (1-ξ*sourceExposure a h ρ z)*U<L) :
    ∃η : ℝ,0 < η ∧ ∀p : Fin 4→ℝ,
      (∀i,|p i-sourceCountPoint a h ρ z i|<η)→NormalizedGuardRegion ξ L U p := by
  let p₀:=sourceCountPoint a h ρ z
  have hdEq : normalizedMixed p₀=a*(1-z):=by dsimp [p₀,sourceCountPoint,normalizedMixed];ring
  have hd : 0<normalizedMixed p₀:=by rw [hdEq];positivity
  have hqEq : normalizedResidual p₀/normalizedMixed p₀=sourceExposure a h ρ z:=by
    rw [hdEq]
    dsimp [p₀,sourceCountPoint,normalizedResidual,sourceExposure]
    field_simp [ha.ne',(sub_pos.mpr hz).ne']
  have hr : 0<normalizedResidual p₀:=
    (div_pos_iff_of_pos_right hd).mp (by rw [hqEq];exact hq0)
  have hrd : normalizedResidual p₀<normalizedMixed p₀:=
    (div_lt_one hd).mp (by rw [hqEq];exact hq1)
  have hfEq : normalizedFactor ξ p₀=1-ξ*sourceExposure a h ρ z:=by rw [normalizedFactor,hqEq]
  have hf : 0<normalizedFactor ξ p₀:=by rw [hfEq];nlinarith
  have hdc : Continuous normalizedMixed:=by unfold normalizedMixed;fun_prop
  have hrc : Continuous normalizedResidual:=by unfold normalizedResidual;fun_prop
  have hfc : ContinuousAt (normalizedFactor ξ) p₀:=by
    exact continuousAt_const.sub (continuousAt_const.mul
      (hrc.continuousAt.div hdc.continuousAt hd.ne'))
  have hlo : (1-ξ)*U<normalizedFactor ξ p₀*L:=by rw [hfEq];exact hboxlo
  have hhi : normalizedFactor ξ p₀*U<L:=by rw [hfEq];exact hboxhi
  have hevent : ∀ᶠp : Fin 4→ℝ in 𝓝 p₀,NormalizedGuardRegion ξ L U p := by
    filter_upwards [hdc.continuousAt.eventually (Ioi_mem_nhds hd),
      hrc.continuousAt.eventually (Ioi_mem_nhds hr),
      (hrc.sub hdc).continuousAt.eventually (Iio_mem_nhds (sub_neg.mpr hrd)),
      hfc.eventually (Ioi_mem_nhds hf),
      (hfc.mul_const L).eventually (Ioi_mem_nhds hlo),
      (hfc.mul_const U).eventually (Iio_mem_nhds hhi)]
      with p hpD hpR hpRD hpF hpLo hpHi
    exact ⟨hpD,hpR,sub_neg.mp hpRD,hpF,hpLo,hpHi⟩
  obtain ⟨η,hη,hηsub⟩:=Metric.mem_nhds_iff.mp hevent
  refine ⟨η,hη,?_⟩
  intro p hp
  apply hηsub
  apply (dist_pi_lt_iff hη).mpr
  intro i
  exact hp i

end FCAppendix.Affine.Hybrid
