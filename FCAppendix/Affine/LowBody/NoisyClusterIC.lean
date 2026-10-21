import FCAppendix.Affine.LowBody.ZeroClusterLoss
import FCAppendix.Affine.LowBody.NoisyClusterMeasures
import FCAppendix.Affine.LowBody.NoisyDeviations

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set
open Existence.Distributional
open scoped BigOperators

lemma literalRowPayoff_affine_value {N : ℕ} (ξ : ℝ) (c : ℕ) (w : ℝ)
    (p : ℝ×(Fin N→RowRival)) :
    literalRowPayoff ξ c w p=w*(literalRowPayoff ξ c 1 p-literalRowPayoff ξ c 0 p)+
      literalRowPayoff ξ c 0 p := by
  unfold literalRowPayoff patternPayoff
  dsimp only
  split_ifs
  · unfold equalPayoff
    ring
  · unfold purePayoff
    split_ifs <;> ring

attribute [local irreducible] literalRowPayoff

lemma measurable_literalRowPayoff_value {N : ℕ} {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) : Measurable (fun p : ℝ×(ℝ×(Fin N→RowRival))=>literalRowPayoff ξ c p.1 p.2) := by
  have h0 : Measurable (fun p : ℝ×(ℝ×(Fin N→RowRival))=>literalRowPayoff ξ c 0 p.2):=
    (measurable_literalRowPayoff (N:=N) hξ hξ1 c 0).comp measurable_snd
  have h1 : Measurable (fun p : ℝ×(ℝ×(Fin N→RowRival))=>literalRowPayoff ξ c 1 p.2):=
    (measurable_literalRowPayoff (N:=N) hξ hξ1 c 1).comp measurable_snd
  have he : (fun p : ℝ×(ℝ×(Fin N→RowRival))=>literalRowPayoff ξ c p.1 p.2)=
      fun p=>p.1*(literalRowPayoff ξ c 1 p.2-literalRowPayoff ξ c 0 p.2)+literalRowPayoff ξ c 0 p.2 :=
    funext (fun p=>literalRowPayoff_affine_value ξ c p.1 p.2)
  rw [he]
  exact (measurable_fst.mul (h1.sub h0)).add h0

lemma measurable_literalRowPayoff_value_comp {X : Type*} [MeasurableSpace X] {N : ℕ}
    {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ)
    (w b : X→ℝ) (row : X→(Fin N→RowRival))
    (hw : Measurable w) (hb : Measurable b) (hr : Measurable row) :
    Measurable (fun x=>literalRowPayoff ξ c (w x) (b x,row x)) :=
  (measurable_literalRowPayoff_value (N:=N) hξ hξ1 c).comp (hw.prodMk (hb.prodMk hr))

lemma realLowLaw_implementedBidLaw {d ε : ℝ} (hε : 0<ε) (hsmall : ε  ≤  1/2)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu] (pi : Law (A:=unitInterval) mu) :
    realLowLaw (implementedBidLaw d ε hε hsmall mu pi : Measure (LowValue d))=
      (realLowBidLaw (lowNoisyLaw d ε hε hsmall mu pi).1 : Measure ℝ) := by
  change (((lowNoisyLaw d ε hε hsmall mu pi).1 : Measure (LowValue d×LowValue d)).map Prod.snd).map Subtype.val=_
  exact Measure.map_map measurable_subtype_coe measurable_snd

def literalNoisyDeviationGain {N : ℕ} (d ε : ℝ) (hε : 0<ε) (hsmall : ε  ≤  1/2)
    (ξ : ℝ) (c : ℕ) (dev : LowValue d×unitInterval→unitInterval)
    (x : NoisyCarrier d) (ω : Fin N→RowRival) : ℝ :=
  literalRowPayoff ξ c x.1.1.1 ((noisyBid d ε hε hsmall ((x.1.1,dev x.1),x.2)).1,ω)-
    literalRowPayoff ξ c x.1.1.1 ((noisyBid d ε hε hsmall x).1,ω)

set_option maxHeartbeats 800000 in
lemma measurable_literalNoisyDeviationGain {N : ℕ} (d : ℝ) {ε ξ : ℝ}
    (hε : 0<ε) (hsmall : ε  ≤  1/2) (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (dev : LowValue d×unitInterval→unitInterval) (hd : Measurable dev) :
    Measurable (Function.uncurry (literalNoisyDeviationGain (N:=N) d ε hε hsmall ξ c dev)) := by
  have hvalue : Measurable (fun p : NoisyCarrier d×(Fin N→RowRival)=>p.1.1.1.1):=
    measurable_fst.fst.fst.subtype_val
  have htrans : Measurable (fun p : NoisyCarrier d×(Fin N→RowRival)=>((p.1.1.1,dev p.1.1),p.1.2)):=
    (measurable_fst.fst.fst.prodMk (hd.comp measurable_fst.fst)).prodMk measurable_fst.snd
  have hnew : Measurable (fun p : NoisyCarrier d×(Fin N→RowRival)=>
      (noisyBid d ε hε hsmall ((p.1.1.1,dev p.1.1),p.1.2)).1):=
    (continuous_noisyBid d ε hε hsmall).subtype_val.measurable.comp htrans
  have hold : Measurable (fun p : NoisyCarrier d×(Fin N→RowRival)=>
      (noisyBid d ε hε hsmall p.1).1):=
    (continuous_noisyBid d ε hε hsmall).subtype_val.measurable.comp measurable_fst
  change Measurable (fun p : NoisyCarrier d×(Fin N→RowRival)=>
    literalRowPayoff ξ c p.1.1.1.1 ((noisyBid d ε hε hsmall ((p.1.1.1,dev p.1.1),p.1.2)).1,p.2)-
      literalRowPayoff ξ c p.1.1.1.1 ((noisyBid d ε hε hsmall p.1).1,p.2))
  exact (measurable_literalRowPayoff_value_comp hξ hξ1 c _ _ _ hvalue hnew measurable_snd).sub
    (measurable_literalRowPayoff_value_comp hξ hξ1 c _ _ _ hvalue hold measurable_snd)

lemma abs_literalNoisyDeviationGain_le {N : ℕ} (d : ℝ) {ε ξ : ℝ}
    (hε : 0<ε) (hsmall : ε  ≤  1/2) (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (dev : LowValue d×unitInterval→unitInterval) (x : NoisyCarrier d)
    (ω : Fin N→RowRival) :
    |literalNoisyDeviationGain d ε hε hsmall ξ c dev x ω|  ≤  2*(d+(3+2*|1-ξ|)*d) := by
  let old:=noisyBid d ε hε hsmall x
  let new:=noisyBid d ε hε hsmall ((x.1.1,dev x.1),x.2)
  have hw : |x.1.1.1|  ≤  d:=by rw [abs_of_nonneg x.1.1.property.1];exact x.1.1.property.2
  have hold : |old.1|  ≤  d:=by rw [abs_of_nonneg old.property.1];exact old.property.2
  have hnew : |new.1|  ≤  d:=by rw [abs_of_nonneg new.property.1];exact new.property.2
  have hconst : 0  ≤  3+2*|1-ξ|:=by positivity
  have huNew:=abs_literalRowPayoff_le hξ hξ1 c x.1.1.1 new.1 ω
  have huOld:=abs_literalRowPayoff_le hξ hξ1 c x.1.1.1 old.1 ω
  have hn : |literalRowPayoff ξ c x.1.1.1 (new.1,ω)| ≤ d+(3+2*|1-ξ|)*d:=
    huNew.trans (by gcongr)
  have ho : |literalRowPayoff ξ c x.1.1.1 (old.1,ω)| ≤ d+(3+2*|1-ξ|)*d:=
    huOld.trans (by gcongr)
  change |literalRowPayoff ξ c x.1.1.1 (new.1,ω)-literalRowPayoff ξ c x.1.1.1 (old.1,ω)| ≤ _
  exact (abs_sub _ _).trans (by linarith)

lemma integrable_literalNoisyDeviationGain {N : ℕ} (d : ℝ) {ε ξ : ℝ}
    (hε : 0<ε) (hsmall : ε  ≤  1/2) (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (dev : LowValue d×unitInterval→unitInterval) (hd : Measurable dev)
    (Gamma : Measure (NoisyCarrier d)) [IsFiniteMeasure Gamma]
    (nu : Measure (Fin N→RowRival)) [IsProbabilityMeasure nu] :
    Integrable (Function.uncurry (literalNoisyDeviationGain (N:=N) d ε hε hsmall ξ c dev))
      (Gamma.prod nu) :=
  Integrable.of_bound (measurable_literalNoisyDeviationGain d hε hsmall hξ hξ1 c dev hd).aestronglyMeasurable
    (2*(d+(3+2*|1-ξ|)*d))
    (ae_of_all _ (fun p=>by
      change |literalNoisyDeviationGain d ε hε hsmall ξ c dev p.1 p.2| ≤ _
      exact abs_literalNoisyDeviationGain_le d hε hsmall hξ hξ1 c dev p.1 p.2))

lemma integrable_literalSmoothed {N : ℕ} {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (ε : ℝ) (c : ℕ) (w x : ℝ) (nu : Measure (Fin N→RowRival)) [IsProbabilityMeasure nu] :
    Integrable (literalSmoothedRowPayoff (N:=N) ξ ε c w x) nu :=
  Integrable.of_bound (measurable_literalSmoothedRowPayoff hξ hξ1 ε c w x).aestronglyMeasurable
    (|w|+(3+2*|1-ξ|)*(|x| *(1+|ε|)))
    (ae_of_all _ (fun ω=>by simpa only [Real.norm_eq_abs] using
      abs_literalSmoothedRowPayoff_le hξ hξ1 ε c w x ω))

theorem noisy_choice_difference_eq_literal {N : ℕ} (d : ℝ) {ε ξ : ℝ}
    (hε : 0<ε) (hsmall : ε ≤ 1/2) (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu] (pi : Law (A:=unitInterval) mu)
    (t : LowValue d×unitInterval) (q' : unitInterval) :
    noisyExpectedUtility (N:=N) d ξ ε hε hsmall c
      (categoryLaw s a h hs ha hh hsum Gref) mu (pi,(t.1,q'))-
    noisyExpectedUtility (N:=N) d ξ ε hε hsmall c
      (categoryLaw s a h hs ha hh hsum Gref) mu (pi,t)=
      ∫u : unitInterval,∫ω : Fin N→RowRival,
        literalNoisyDeviationGain d ε hε hsmall ξ c (fun _=>q') (t,u) ω
        ∂Measure.pi (fun _ : Fin N=>rivalLaw s a h
          (realLowBidLaw (lowNoisyLaw d ε hε hsmall mu pi).1 : Measure ℝ)) := by
  let G:=realLowLaw (implementedBidLaw d ε hε hsmall mu pi : Measure (LowValue d))
  let nu:=Measure.pi (fun _ : Fin N=>rivalLaw s a h G)
  letI : IsProbabilityMeasure (rivalLaw s a h G):=rivalLaw_isProbability s a h hs ha hh hsum G
  have hcat:=categoryLaw_eq_low_law s a h hs ha hh hsum Gref G
  rw [hcat]
  rw [noisyExpectedUtility_eq_literal_row d hξ hξ1 hε hsmall c s a h hs ha hh hsum mu pi t.1 q',
    noisyExpectedUtility_eq_literal_row d hξ hξ1 hε hsmall c s a h hs ha hh hsum mu pi t.1 t.2]
  change (∫ω,literalSmoothedRowPayoff ξ ε c t.1.1 (t.1.1*bidRatio ε q') ω ∂nu)-
    (∫ω,literalSmoothedRowPayoff ξ ε c t.1.1 (t.1.1*bidRatio ε t.2) ω ∂nu)=_
  rw [←integral_sub (integrable_literalSmoothed hξ hξ1 ε c t.1.1 (t.1.1*bidRatio ε q') nu)
    (integrable_literalSmoothed hξ hξ1 ε c t.1.1 (t.1.1*bidRatio ε t.2) nu)]
  rw [integral_literalSmoothed_sub hξ hξ1 ε c t.1.1 (t.1.1*bidRatio ε q') (t.1.1*bidRatio ε t.2) nu]
  have hnoise:=unitInterval.measurePreserving_coe.integral_comp unitInterval.measurableEmbedding_coe
    (fun z : ℝ=>∫ω,literalRowPayoff ξ c t.1.1 ((t.1.1*bidRatio ε q')*(1+ε*z),ω)-
      literalRowPayoff ξ c t.1.1 ((t.1.1*bidRatio ε t.2)*(1+ε*z),ω) ∂nu)
  rw [←hnoise]
  have hG : G=(realLowBidLaw (lowNoisyLaw d ε hε hsmall mu pi).1 : Measure ℝ):=
    realLowLaw_implementedBidLaw hε hsmall mu pi
  dsimp only [nu]
  rw [hG]
  apply integral_congr_ae
  apply ae_of_all
  intro u
  apply integral_congr_ae
  exact ae_of_all _ (fun ω=>rfl)

theorem latent_cluster_noisy_gain_identity {N : ℕ} (d : ℝ) {ε ξ : ℝ}
    (hε : 0<ε) (hsmall : ε ≤ 1/2) (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu] (pi : Law (A:=unitInterval) mu)
    (dev : LowValue d×unitInterval→unitInterval) (hd : Measurable dev)
    (E : Set (LowValue d×unitInterval)) :
    (∫t in E,(noisyExpectedUtility (N:=N) d ξ ε hε hsmall c
        (categoryLaw s a h hs ha hh hsum Gref) mu (pi,(t.1,dev t))-
      noisyExpectedUtility (N:=N) d ξ ε hε hsmall c
        (categoryLaw s a h hs ha hh hsum Gref) mu (pi,t))
      ∂(pi.1 : Measure (LowValue d×unitInterval)))=
    ∫x,∫ω : Fin N→RowRival,literalNoisyDeviationGain d ε hε hsmall ξ c dev x ω
      ∂Measure.pi (fun _ : Fin N=>rivalLaw s a h
        (realLowBidLaw (lowNoisyLaw d ε hε hsmall mu pi).1 : Measure ℝ))
      ∂latentClusterCarrier mu pi E := by
  let G:=(realLowBidLaw (lowNoisyLaw d ε hε hsmall mu pi).1 : Measure ℝ)
  let nu:=Measure.pi (fun _ : Fin N=>rivalLaw s a h G)
  let Gamma:=latentClusterCarrier mu pi E
  letI : IsProbabilityMeasure (rivalLaw s a h G):=rivalLaw_isProbability s a h hs ha hh hsum G
  have hi:=integrable_literalNoisyDeviationGain d hε hsmall hξ hξ1 c dev hd Gamma nu
  have houter:=hi.integral_prod_left
  simp only [Function.uncurry] at houter
  symm
  change (∫x,(∫ω,literalNoisyDeviationGain d ε hε hsmall ξ c dev x ω ∂nu)
    ∂(((pi.1 : Measure (LowValue d×unitInterval)).restrict E).prod (volume : Measure unitInterval)))=_
  rw [integral_prod _ houter]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  exact (noisy_choice_difference_eq_literal d hε hsmall hξ hξ1 c s a h hs ha hh hsum
    Gref mu pi t (dev t)).symm

theorem latent_cluster_noisy_gain_nonpos {N : ℕ} (d : ℝ) {ε ξ : ℝ}
    (hε : 0<ε) (hsmall : ε ≤ 1/2) (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu] (pi : Law (A:=unitInterval) mu)
    (sigma : Kernel (LowValue d) unitInterval) [IsMarkovKernel sigma]
    (hdis : mu⊗ₘsigma=(pi.1 : Measure (LowValue d×unitInterval)))
    (hopt : ∀ᵐw ∂mu,∀ᵐq ∂sigma w,∀q' : unitInterval,
      noisyExpectedUtility (N:=N) d ξ ε hε hsmall c (categoryLaw s a h hs ha hh hsum Gref) mu (pi,(w,q')) ≤
        noisyExpectedUtility (N:=N) d ξ ε hε hsmall c (categoryLaw s a h hs ha hh hsum Gref) mu (pi,(w,q)))
    (dev : LowValue d×unitInterval→unitInterval) (hd : Measurable dev)
    (E : Set (LowValue d×unitInterval)) :
    (∫x,∫ω : Fin N→RowRival,literalNoisyDeviationGain d ε hε hsmall ξ c dev x ω
      ∂Measure.pi (fun _ : Fin N=>rivalLaw s a h
        (realLowBidLaw (lowNoisyLaw d ε hε hsmall mu pi).1 : Measure ℝ))
      ∂latentClusterCarrier mu pi E) ≤ 0 := by
  rw [←latent_cluster_noisy_gain_identity d hε hsmall hξ hξ1 c s a h hs ha hh hsum Gref mu pi dev hd E]
  exact noisy_integrated_deviation_nonpos d hξ hξ1 hε hsmall c
    (categoryLaw s a h hs ha hh hsum Gref) mu pi sigma hdis hopt dev hd E

end FCAppendix.Affine.LowBody
