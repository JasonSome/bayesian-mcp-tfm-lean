import FCAppendix.Affine.LowBody.FirstCopyZeroGain
import FCAppendix.Affine.LowBody.NoisyClusterIC
import FCAppendix.Affine.LowBody.NoisyClusterSupport
import FCAppendix.Affine.LowBody.CarrierRowTransport

set_option maxHeartbeats 1000000
noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set Classical
open Existence.Distributional
variable {N : ℕ}

theorem noisy_zero_cluster_quadratic {d ε tau δ ξ : ℝ}
    (hε : 0<ε) (hsmall : ε≤1/4) (hδ : 0<δ) (htau : 4*δ≤tau) (hnoise : ε*d≤δ)
    (hξ : 0<ξ) (hξh : ξ≤1/2)
    (c : ℕ) (hc : 0<c) (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A:=unitInterval) mu) (hmu : ∀ᵐw ∂mu,0<w.1)
    (sigma : Kernel (LowValue d) unitInterval) [IsMarkovKernel sigma]
    (hdis : mu⊗ₘsigma=(pi.1 : Measure (LowValue d×unitInterval)))
    (hopt : ∀ᵐw ∂mu,∀ᵐq ∂sigma w,∀q' : unitInterval,
      noisyExpectedUtility (N:=N+1) d ξ ε hε (by linarith) c
        (categoryLaw s a h hs ha hh hsum Gref) mu (pi,(w,q'))≤
      noisyExpectedUtility (N:=N+1) d ξ ε hε (by linarith) c
        (categoryLaw s a h hs ha hh hsum Gref) mu (pi,(w,q))) :
    let E:=zeroBaseClusterSet (d:=d) hε (by linarith) tau δ
    let p:=(pi.1 : Measure (LowValue d×unitInterval)).real E
    let G:=(realLowBidLaw (lowNoisyLaw d ε hε (by linarith) mu pi).1 : Measure ℝ)
    (tau-2*δ)*s*p^2*(Measure.pi (fun _ : Fin N=>rivalLaw s a h G)).real
      (firstCopyBoundary c (2*δ))/2≤8*δ*p := by
  have hsmall₂ : ε≤1/2:=by linarith
  let E:=zeroBaseClusterSet (d:=d) hε hsmall₂ tau δ
  let p:=(pi.1 : Measure (LowValue d×unitInterval)).real E
  let G:=(realLowBidLaw (lowNoisyLaw d ε hε hsmall₂ mu pi).1 : Measure ℝ)
  let Γ:=latentClusterCarrier mu pi E
  let θ:=physicalClusterMeasure hε hsmall₂ mu pi E
  let ρ:=rivalLaw s a h G
  let ν:=Measure.pi (fun _ : Fin N=>ρ)
  letI : IsProbabilityMeasure ρ:=rivalLaw_isProbability s a h hs ha hh hsum G
  letI : NullSingletonClass θ:=physicalClusterMeasure_atomless hε hsmall₂ mu pi hmu E
  change (tau-2*δ)*s*p^2*ν.real (firstCopyBoundary c (2*δ))/2≤8*δ*p
  by_cases hp:p=0
  · simp only [hp,zero_pow (by norm_num : 2≠0),mul_zero,zero_mul,zero_div,le_refl]
  have hθ0 : θ univ≠0:=by
    intro hz
    apply hp
    have hm:=physicalClusterMeasure_mass hε hsmall₂ mu pi E
    change θ.real univ=p at hm
    rw [measureReal_def,hz,ENNReal.toReal_zero] at hm
    exact hm.symm
  let old : NoisyCarrier d→ℝ:=fun t=>(noisyBid d ε hε hsmall₂ t).1
  let raised:=clusterRaisedBid (d:=d) hε hsmall δ δ
  let value : NoisyCarrier d→ℝ:=fun t=>t.1.1.1
  have hold : Measurable old:=(continuous_noisyBid d ε hε hsmall₂).subtype_val.measurable
  have hraised : Measurable raised:=measurable_clusterRaisedBid hε hsmall δ δ
  have hvalue : Measurable value:=measurable_fst.fst.subtype_val
  have hgeo:=zero_cluster_carrier_geometry hε hsmall hδ htau hnoise mu pi
  have hpush : Γ.map old=θ:=rfl
  have hθu : ∀ᵐy ∂θ,y≤2*δ:=by
    change ∀ᵐy ∂Γ.map old,y≤2*δ
    apply (ae_map_iff hold.aemeasurable (measurableSet_le measurable_id measurable_const)).mpr
    exact hgeo.mono (fun t ht=>ht.1.2)
  have hbox : ∀ᵐt ∂Γ,0≤old t ∧ old t≤raised t ∧ raised t≤value t ∧ raised t≤4*δ ∧
      2*δ<raised t ∧ tau-2*δ≤value t-old t ∧ |value t|≤d:=by
    filter_upwards [hgeo] with t ht
    refine ⟨ht.1.1,ht.2.2.1.le,ht.2.2.2.1,ht.2.1.2,?_,ht.2.2.2.2.2,?_⟩
    · linarith [ht.2.1.1]
    · change |t.1.1.1|≤d
      rw [abs_of_nonneg t.1.1.property.1]
      exact t.1.1.property.2
  have hG0 : ∀ᵐb ∂G,0≤b:=by
    change ∀ᵐb ∂(realLowBidLaw (lowNoisyLaw d ε hε hsmall₂ mu pi).1 : Measure ℝ),0≤b
    rw [←realLowLaw_implementedBidLaw hε hsmall₂ mu pi]
    change ∀ᵐb ∂(implementedBidLaw d ε hε hsmall₂ mu pi : Measure (LowValue d)).map Subtype.val,0≤b
    apply (ae_map_iff measurable_subtype_coe.aemeasurable
      (measurableSet_le measurable_const measurable_id)).mpr
    exact ae_of_all _ (fun b=>b.property.1)
  have hρ0:=rivalLaw_ae_bid_nonnegative s a h G hG0
  have hν0:=iid_rows_ae_bid_nonnegative (N:=N) ρ hρ0
  have hrows:=firstCopy_mixed_rows_nonnegative ν Γ ρ
    (hν0.mono (fun _ ht j _=>ht j)) (hρ0.mono (fun _ ht _=>ht))
  have hgain:=firstCopy_zero_integrated_gain_lower hξ hξh s a h hs ha hh hsum G θ
    (physicalClusterMeasure_le hε hsmall₂ mu pi E) hθ0 Γ ν c hc
    (2*δ) (tau-2*δ) d (4*δ) (by linarith) (by linarith)
    value old raised hvalue hold hraised hpush hθu hbox hrows
  let dev : LowValue d×unitInterval→unitInterval:=fun t=>crossingChoice ε hε hsmall δ δ t.1
  have hdev : Measurable dev:=(measurable_crossingChoice ε hε hsmall δ δ d).comp measurable_fst
  let f : NoisyCarrier d×(Fin (N+1)→RowRival)→ℝ:=
    Function.uncurry (literalNoisyDeviationGain d ε hε hsmall₂ ξ c dev)
  have hξ1 : ξ<1:=by linarith
  have hf : Measurable f:=measurable_literalNoisyDeviationGain d hε hsmall₂ hξ hξ1 c dev hdev
  have hfi : Integrable f (Γ.prod (Measure.pi (fun _ : Fin (N+1)=>ρ))):=
    integrable_literalNoisyDeviationGain d hε hsmall₂ hξ hξ1 c dev hdev Γ _
  have htrans:=integral_carrierRow (N:=N) Γ ρ f hf hfi
  have hIC:=latent_cluster_noisy_gain_nonpos (N:=N+1) d hε hsmall₂ hξ hξ1 c s a h hs ha hh hsum
    Gref mu pi sigma hdis hopt dev hdev E
  have hnonpos : (∫q : (Fin N→RowRival)×(NoisyCarrier d×RowRival),
      literalRowPayoff ξ c (value q.2.1) (raised q.2.1,Fin.cons q.2.2 q.1)-
        literalRowPayoff ξ c (value q.2.1) (old q.2.1,Fin.cons q.2.2 q.1) ∂ν.prod (Γ.prod ρ))≤0:=by
    change (∫q : (Fin N→RowRival)×(NoisyCarrier d×RowRival),f (q.2.1,Fin.cons q.2.2 q.1)
      ∂ν.prod (Γ.prod ρ))≤0
    rw [htrans]
    exact hIC
  have hmass : Γ.real univ=p:=latentClusterCarrier_mass mu pi E
  rw [hmass] at hgain
  linarith

end FCAppendix.Affine.LowBody
