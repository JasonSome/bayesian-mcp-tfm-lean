import FCAppendix.Affine.LowBody.FirstCopyNoisyGain
import FCAppendix.Affine.LowBody.CarrierClusterLoss
import FCAppendix.Affine.LowBody.NoisyClusterIC
import FCAppendix.Affine.LowBody.NoisyClusterSupport
import FCAppendix.Affine.LowBody.NoisySupportedLimit

set_option maxHeartbeats 1200000
noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set Classical
open Existence.Distributional
variable {N : ℕ}

theorem noisy_positive_cluster_quadratic_uniform (d : ℝ) (hd : 0 ≤ d) {ξ : ℝ}
    (hξ : 0<ξ) (hξh : ξ ≤ 1/2) (b : ℝ) (hb : 0<b) :
    ∀err>0,∃δmax>0,∀δ : ℝ,0<δ→δ<b→δ<δmax→
    ∀(ε : ℝ)(hε : 0<ε)(hsmall : ε ≤ 1/4),ε*d<δ→
    ∀ell : ℝ,0 ≤ ell→3*δ+ε*d ≤ (b-δ)*ell/4→
    ∀(c : ℕ),0<c→
    ∀(s a h : ℝ)(hs : 0 ≤ s)(ha : 0 ≤ a)(hh : 0 ≤ h)(hsum : s+a+h=1)
      (Gref : Measure ℝ)(_hGref : IsProbabilityMeasure Gref)
      (mu : Measure (LowValue d))(_hmuProb : IsProbabilityMeasure mu)
      (pi : Law (A:=unitInterval) mu),
      (∀ᵐw ∂mu,0<w.1)→
    ∀(sigma : Kernel (LowValue d) unitInterval)(_hSigma : IsMarkovKernel sigma),
      mu⊗ₘsigma=(pi.1 : Measure (LowValue d×unitInterval))→
      (∀ᵐw ∂mu,∀ᵐq ∂sigma w,∀q' : unitInterval,
        noisyExpectedUtility (N:=N+1) d ξ ε hε (by linarith) c
          (categoryLaw s a h hs ha hh hsum Gref) mu (pi,(w,q')) ≤
        noisyExpectedUtility (N:=N+1) d ξ ε hε (by linarith) c
          (categoryLaw s a h hs ha hh hsum Gref) mu (pi,(w,q)))→
      ell=(CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) (N+1)).prob (LocalUnderflow c 0)→
      (CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) (N+1)).prob (BothUnderflow c) ≤ ell/4→
    ∀H : ℝ,
      H ≤ PiBinomial.pmf N (higherBidProbability s a h
        (realLowBidLaw (lowNoisyLaw d ε hε (by linarith) mu pi).1 : Measure ℝ)
        (b+δ+ε*d)) (c-1)→
      let E:=baseClusterSet (d:=d) hε (by linarith) b δ
      let p:=(pi.1 : Measure (LowValue d×unitInterval)).real E
      let G:=(realLowBidLaw (lowNoisyLaw d ε hε (by linarith) mu pi).1 : Measure ℝ)
      let e:=(CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob (BothUnderflow c)
      p^2*((b-δ)*ell/4-ε*d)*s*(H-e)/2 ≤
        p*((b+3*δ)*(1-2*ξ)*(N+1:ℕ)*s*e*
          (G.real (Icc (b-δ) (b+3*δ))+G.real (Icc ((1-ξ)*(b-δ)) ((1-ξ)*(b+3*δ))))+
          (4+8*(1-ξ))*δ+err) := by
  intro err herr
  obtain ⟨R,hR,hgain⟩:=firstCopy_integrated_literalGain_uniform
    (N:=N) (A:=NoisyCarrier d) hξ hξh (a:=b/2) (B:=2*b) (W:=d)
    (by linarith) (by linarith) hd err herr
  refine ⟨min (b/4) (R/4),lt_min (by positivity) (by positivity),?_⟩
  intro δ hδ hδb hδmax ε hε hsmall hnoise ell hell hroom c hc s a h hs ha hh hsum
    Gref hGref mu hmuProb pi hmu sigma hSigma hdis hopt hellDef hjoint H hH
  letI:=hGref
  letI:=hmuProb
  letI:=hSigma
  have hsmall₂ : ε ≤ 1/2:=by linarith
  have hδquarter : δ<b/4:=hδmax.trans_le (min_le_left _ _)
  have hδR : 4*δ<R:=by have hh:=hδmax.trans_le (min_le_right (b/4) (R/4));linarith
  let E:=baseClusterSet (d:=d) hε hsmall₂ b δ
  let p:=(pi.1 : Measure (LowValue d×unitInterval)).real E
  let G:=(realLowBidLaw (lowNoisyLaw d ε hε hsmall₂ mu pi).1 : Measure ℝ)
  let e:=(CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob (BothUnderflow c)
  let Γ:=latentClusterCarrier mu pi E
  let θ:=physicalClusterMeasure hε hsmall₂ mu pi E
  let ρ:=rivalLaw s a h G
  let ν:=Measure.pi (fun _ : Fin N=>ρ)
  let S:=(b-δ)*ell/4-ε*d
  let U:=b+3*δ
  let κ:=1-ξ
  let B:=Icc (b-δ) U
  let C:=Icc (κ*(b-δ)) (κ*U)
  letI : IsProbabilityMeasure ρ:=rivalLaw_isProbability s a h hs ha hh hsum G
  letI : NullSingletonClass θ:=physicalClusterMeasure_atomless hε hsmall₂ mu pi hmu E
  change p^2*S*s*(H-e)/2 ≤ p*(U*(1-2*ξ)*(N+1:ℕ)*s*e*(G.real B+G.real C)+(4+8*κ)*δ+err)
  by_cases hp:p=0
  · simp only [hp,zero_pow (by norm_num : 2≠0),zero_mul,zero_div,le_refl]
  have hθ0 : θ univ≠0:=by
    intro hz
    apply hp
    have hm:=physicalClusterMeasure_mass hε hsmall₂ mu pi E
    change θ.real univ=p at hm
    rw [measureReal_def,hz,ENNReal.toReal_zero] at hm
    exact hm.symm
  have hsupport:=noisy_joint_supported_surplus (N:=N+1) d hξ hξh hε hsmall c
    (categoryLaw s a h hs ha hh hsum Gref) mu pi sigma hdis hopt (by simpa only [←hellDef] using hjoint)
  rw [←hellDef] at hsupport
  have hgeo:=positive_cluster_supported_geometry hε hsmall hell hδ hδb hnoise hroom mu pi hsupport
  let old : NoisyCarrier d→ℝ:=fun t=>(noisyBid d ε hε hsmall₂ t).1
  let raised:=clusterRaisedBid (d:=d) hε hsmall b δ
  let value : NoisyCarrier d→ℝ:=fun t=>t.1.1.1
  have hold : Measurable old:=(continuous_noisyBid d ε hε hsmall₂).subtype_val.measurable
  have hraised : Measurable raised:=measurable_clusterRaisedBid hε hsmall b δ
  have hvalue : Measurable value:=measurable_fst.fst.subtype_val
  have hpush : Γ.map old=θ:=rfl
  have hθu : ∀ᵐy ∂θ,y ≤ b+δ+ε*d:=by
    change ∀ᵐy ∂Γ.map old,y ≤ b+δ+ε*d
    apply (ae_map_iff hold.aemeasurable (measurableSet_le measurable_id measurable_const)).mpr
    exact hgeo.mono (fun t ht=>ht.1.2)
  have hbox : ∀ᵐt ∂Γ,b-δ ≤ old t ∧ b/2 ≤ old t ∧ old t ≤ 2*b ∧ old t ≤ value t ∧
      old t<raised t ∧ raised t-old t<R ∧ raised t-(b-δ) ≤ 4*δ ∧ b+δ+ε*d<raised t ∧
      S ≤ value t-old t ∧ |value t| ≤ d:=by
    filter_upwards [hgeo] with t ht
    have hnoise0 : 0 ≤ ε*d:=mul_nonneg hε.le hd
    refine ⟨ht.1.1,?_,?_,?_,?_,?_,ht.2.2.2.2.2.1,ht.2.1,ht.2.2.2.2.2.2,?_⟩
    · linarith [ht.1.1]
    · linarith [ht.1.2]
    · linarith [ht.1.2,ht.2.1,ht.2.2.1]
    · exact ht.1.2.trans_lt ht.2.1
    · exact ht.2.2.2.2.1.trans hδR
    · change |t.1.1.1| ≤ d
      rw [abs_of_nonneg t.1.1.property.1]
      exact t.1.1.property.2
  have hG0 : ∀ᵐy ∂G,0 ≤ y:=by
    rw [show G=(realLowBidLaw (lowNoisyLaw d ε hε hsmall₂ mu pi).1 : Measure ℝ) from rfl,
      ←realLowLaw_implementedBidLaw hε hsmall₂ mu pi]
    change ∀ᵐy ∂(implementedBidLaw d ε hε hsmall₂ mu pi : Measure (LowValue d)).map Subtype.val,0 ≤ y
    apply (ae_map_iff measurable_subtype_coe.aemeasurable
      (measurableSet_le measurable_const measurable_id)).mpr
    exact ae_of_all _ (fun y=>y.property.1)
  have hρ0:=rivalLaw_ae_bid_nonnegative s a h G hG0
  have hν0:=iid_rows_ae_bid_nonnegative (N:=N) ρ hρ0
  have hrows:=firstCopy_mixed_rows_nonnegative ν Γ ρ
    (hν0.mono (fun _ ht j _=>ht j)) (hρ0.mono (fun _ ht _=>ht))
  have hS : 0 ≤ S:=by dsimp only [S];linarith
  have hgain':=hgain s a h hs ha hh hsum G θ inferInstance inferInstance inferInstance
    (physicalClusterMeasure_le hε hsmall₂ mu pi E) hθ0 Γ inferInstance ν inferInstance c hc
    (b-δ) (b+δ+ε*d) S (4*δ) (by positivity) hS value old raised
    hvalue hold hraised hpush hθu hbox hrows
  let dev : LowValue d×unitInterval→unitInterval:=fun t=>crossingChoice ε hε hsmall b δ t.1
  have hdev : Measurable dev:=(measurable_crossingChoice ε hε hsmall b δ d).comp measurable_fst
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
        literalRowPayoff ξ c (value q.2.1) (old q.2.1,Fin.cons q.2.2 q.1) ∂ν.prod (Γ.prod ρ)) ≤ 0:=by
    change (∫q : (Fin N→RowRival)×(NoisyCarrier d×RowRival),f (q.2.1,Fin.cons q.2.2 q.1)
      ∂ν.prod (Γ.prod ρ)) ≤ 0
    rw [htrans]
    exact hIC
  have hκ : 1/2 ≤ κ:=by dsimp only [κ];linarith
  have hboxLoss : ∀ᵐt ∂Γ,0 ≤ old t ∧ old t ≤ U ∧ Icc (old t) (raised t)⊆B ∧
      Icc (κ*old t) (κ*raised t)⊆C:=by
    filter_upwards [hgeo] with t ht
    have hlow : 0 ≤ old t:=by change 0 ≤ (noisyBid d ε hε hsmall₂ t).1;exact (noisyBid d ε hε hsmall₂ t).property.1
    have hup : raised t ≤ U:=ht.2.2.2.1
    have hox : old t ≤ raised t:=ht.1.2.trans ht.2.1.le
    refine ⟨hlow,hox.trans hup,?_,?_⟩
    · intro y hy
      exact ⟨ht.1.1.trans hy.1,hy.2.trans hup⟩
    · intro y hy
      exact ⟨(mul_le_mul_of_nonneg_left ht.1.1 (by linarith : 0 ≤ κ)).trans hy.1,
        hy.2.trans (mul_le_mul_of_nonneg_left hup (by linarith : 0 ≤ κ))⟩
  have hloss:=carrier_intervalLoss_expectation (N:=N) c hκ (U:=U) (by dsimp only [U];linarith)
    s a h hs ha hh hsum G Γ old raised hold hraised B C measurableSet_Icc measurableSet_Icc hboxLoss
  have hcategory:=categoryLaw_eq_low_law s a h hs ha hh hsum G Gref
  rw [hcategory] at hloss
  have hboundary:=firstCopyBoundary_probability_lower s a h hs ha hh hsum G N c (b+δ+ε*d)
  rw [hcategory] at hboundary
  have hboundary' : H-e ≤ ν.real (firstCopyBoundary c (b+δ+ε*d)):=by exact le_trans (sub_le_sub_right hH e) hboundary
  have hscale : 0 ≤ S*s*p^2/2:=by positivity
  have hscaled:=mul_le_mul_of_nonneg_left hboundary' hscale
  have hmass : Γ.real univ=p:=latentClusterCarrier_mass mu pi E
  rw [hmass] at hgain' hloss
  have hfinite : S*s*p^2*ν.real (firstCopyBoundary c (b+δ+ε*d))/2 ≤
      p*(4*δ+2*(1-ξ)*(4*δ)+err)+p*((2*κ-1)*U*(N+1:ℕ)*s*(G.real B+G.real C)*e):=by
    linarith
  calc
    p^2*S*s*(H-e)/2 ≤ S*s*p^2*ν.real (firstCopyBoundary c (b+δ+ε*d))/2:=by nlinarith only [hscaled]
    _ ≤ p*(4*δ+2*(1-ξ)*(4*δ)+err)+p*((2*κ-1)*U*(N+1:ℕ)*s*(G.real B+G.real C)*e):=hfinite
    _=p*(U*(1-2*ξ)*(N+1:ℕ)*s*e*(G.real B+G.real C)+(4+8*κ)*δ+err):=by dsimp only [κ];ring

end FCAppendix.Affine.LowBody
