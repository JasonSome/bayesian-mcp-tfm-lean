import FCAppendix.Affine.LowBody.NoisyClusterMeasures

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set Classical
open Existence.Distributional

def baseClusterSet {d ε : ℝ} (hε : 0<ε) (hsmall : ε≤1/2) (b δ : ℝ) :
    Set (LowValue d×unitInterval):=
  (fun x=>(baseBid d ε hε hsmall x).1) ⁻¹' Ioo (b-δ) (b+δ)

theorem measurableSet_baseClusterSet {d ε : ℝ} (hε : 0<ε) (hsmall : ε≤1/2) (b δ : ℝ) :
    MeasurableSet (baseClusterSet (d:=d) hε hsmall b δ) :=
  (continuous_baseBid d ε hε hsmall).subtype_val.measurable measurableSet_Ioo

def clusterRaisedBid {d ε : ℝ} (hε : 0<ε) (hsmall : ε≤1/4) (b δ : ℝ)
    (x : NoisyCarrier d) : ℝ:=
  (noisyBid d ε hε (by linarith) ((x.1.1,crossingChoice ε hε hsmall b δ x.1.1),x.2)).1

theorem measurable_clusterRaisedBid {d ε : ℝ} (hε : 0<ε) (hsmall : ε≤1/4) (b δ : ℝ) :
    Measurable (clusterRaisedBid (d:=d) hε hsmall b δ) :=
  (continuous_noisyBid d ε hε (by linarith)).subtype_val.measurable.comp
    (((measurable_fst.comp measurable_fst).prodMk
      ((measurable_crossingChoice ε hε hsmall b δ d).comp
        (measurable_fst.comp measurable_fst))).prodMk measurable_snd)

theorem baseClusterSet_mass {d ε : ℝ} (hε : 0<ε) (hsmall : ε≤1/2)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A:=unitInterval) mu) (b δ : ℝ) :
    (pi.1 : Measure (LowValue d×unitInterval)).real (baseClusterSet hε hsmall b δ)=
      (baseBidLaw d ε hε hsmall mu pi : Measure ℝ).real (Ioo (b-δ) (b+δ)) := by
  rw [measureReal_def,measureReal_def]
  congr 1
  exact (Measure.map_apply (continuous_baseBid d ε hε hsmall).subtype_val.measurable
    measurableSet_Ioo).symm

theorem positive_cluster_supported_geometry {d ε ell b δ : ℝ}
    (hε : 0<ε) (hsmall : ε≤1/4) (hell : 0≤ell) (hδ : 0<δ) (hδb : δ<b)
    (hnoise : ε*d<δ) (hroom : 3*δ+ε*d≤(b-δ)*ell/4)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu] (pi : Law (A:=unitInterval) mu)
    (hs : ∀ᵐx ∂(pi.1 : Measure (LowValue d×unitInterval)),
      x.1.1*ell/4≤x.1.1-x.1.1*bidRatio ε x.2) :
    ∀ᵐx ∂latentClusterCarrier mu pi (baseClusterSet hε (by linarith) b δ),
      let old:=(noisyBid d ε hε (by linarith) x).1
      let raised:=clusterRaisedBid hε hsmall b δ x
      old∈Icc (b-δ) (b+δ+ε*d) ∧ b+δ+ε*d<raised ∧ raised≤x.1.1.1 ∧
      raised≤b+3*δ ∧ raised-old<4*δ ∧ raised-(b-δ)≤4*δ ∧
      (b-δ)*ell/4-ε*d≤x.1.1.1-old := by
  have hE:=measurableSet_baseClusterSet (d:=d) hε (by linarith) b δ
  have hP : MeasurableSet {x : NoisyCarrier d |
      let old:=(noisyBid d ε hε (by linarith) x).1
      let raised:=clusterRaisedBid hε hsmall b δ x
      old∈Icc (b-δ) (b+δ+ε*d) ∧ b+δ+ε*d<raised ∧ raised≤x.1.1.1 ∧
      raised≤b+3*δ ∧ raised-old<4*δ ∧ raised-(b-δ)≤4*δ ∧
      (b-δ)*ell/4-ε*d≤x.1.1.1-old} := by
    dsimp only
    have ho:=(continuous_noisyBid d ε hε (by linarith)).subtype_val.measurable
    have hr:=measurable_clusterRaisedBid (d:=d) hε hsmall b δ
    measurability
  change ∀ᵐx ∂(((pi.1 : Measure (LowValue d×unitInterval)).restrict
    (baseClusterSet hε (by linarith) b δ)).prod (volume : Measure unitInterval)),_
  apply (Measure.ae_prod_iff_ae_ae hP).mpr
  filter_upwards [ae_restrict_of_ae hs,ae_restrict_mem hE] with x hx hxE
  exact ae_of_all _ (fun z=>by
    have hc : x.1.1*bidRatio ε x.2∈Ioo (b-δ) (b+δ) := by simpa only [baseClusterSet,mem_preimage,baseBid_coe] using hxE
    have hbase:=noisyBid_bounds hε (by linarith) x.1 x.2 (0:unitInterval)
    have hbw : x.1.1*bidRatio ε x.2≤x.1.1:=by simpa using hbase.2
    have hg:=crossing_implemented_geometry hε.le hell hδ hδb x.1.property hc hbw hx hnoise hroom z.property
    have hex:=crossingChoice_exact hε hsmall hell hδ hδb x.1 x.2 hc hx hnoise hroom
    have hr : clusterRaisedBid hε hsmall b δ (x,z)=(b+2*δ)*(1+ε*z.1) := by
      change x.1.1*bidRatio ε (crossingChoice ε hε hsmall b δ x.1)*(1+ε*z.1)=_
      rw [hex]
    dsimp only at hg ⊢
    rw [hr]
    change x.1.1*bidRatio ε x.2*(1+ε*z.1)∈Icc (b-δ) (b+δ+ε*d) ∧ _
    refine ⟨hg.1,?_,hg.2.2.2.1,hg.2.1.2,hg.2.2.2.2.1,?_,hg.2.2.2.2.2⟩ <;>
      linarith [hg.2.1.1,hg.2.1.2])

def zeroBaseClusterSet {d ε : ℝ} (hε : 0<ε) (hsmall : ε≤1/2) (tau δ : ℝ) :
    Set (LowValue d×unitInterval):=
  {x | tau<x.1.1 ∧ (baseBid d ε hε hsmall x).1<δ}

theorem measurableSet_zeroBaseClusterSet {d ε : ℝ} (hε : 0<ε)
    (hsmall : ε≤1/2) (tau δ : ℝ) :
    MeasurableSet (zeroBaseClusterSet (d:=d) hε hsmall tau δ) := by
  unfold zeroBaseClusterSet
  have hb:=(continuous_baseBid d ε hε hsmall).subtype_val.measurable
  measurability

theorem zero_cluster_carrier_geometry {d ε tau δ : ℝ}
    (hε : 0<ε) (hsmall : ε≤1/4) (hδ : 0<δ) (htau : 4*δ≤tau)
    (hnoise : ε*d≤δ) (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A:=unitInterval) mu) :
    ∀ᵐx ∂latentClusterCarrier mu pi (zeroBaseClusterSet hε (by linarith) tau δ),
      let old:=(noisyBid d ε hε (by linarith) x).1
      let raised:=clusterRaisedBid hε hsmall δ δ x
      old∈Icc (0:ℝ) (2*δ) ∧ raised∈Icc (3*δ) (4*δ) ∧
      old<raised ∧ raised≤x.1.1.1 ∧ raised-old≤4*δ ∧ tau-2*δ≤x.1.1.1-old := by
  have hE:=measurableSet_zeroBaseClusterSet (d:=d) hε (by linarith) tau δ
  have hP : MeasurableSet {x : NoisyCarrier d |
      let old:=(noisyBid d ε hε (by linarith) x).1
      let raised:=clusterRaisedBid hε hsmall δ δ x
      old∈Icc (0:ℝ) (2*δ) ∧ raised∈Icc (3*δ) (4*δ) ∧
      old<raised ∧ raised≤x.1.1.1 ∧ raised-old≤4*δ ∧ tau-2*δ≤x.1.1.1-old} := by
    dsimp only
    have ho:=(continuous_noisyBid d ε hε (by linarith)).subtype_val.measurable
    have hr:=measurable_clusterRaisedBid (d:=d) hε hsmall δ δ
    measurability
  change ∀ᵐx ∂(((pi.1 : Measure (LowValue d×unitInterval)).restrict
    (zeroBaseClusterSet hε (by linarith) tau δ)).prod (volume : Measure unitInterval)),_
  apply (Measure.ae_prod_iff_ae_ae hP).mpr
  filter_upwards [ae_restrict_mem hE] with x hx
  exact ae_of_all _ (fun z=>by
    have hc : tau<x.1.1 ∧ x.1.1*bidRatio ε x.2<δ := by
      simpa only [zeroBaseClusterSet,mem_setOf_eq,baseBid_coe] using hx
    have hb:=noisyBid_bounds hε (by linarith) x.1 x.2 (0:unitInterval)
    have hb0 : 0≤x.1.1*bidRatio ε x.2:=by simpa using hb.1
    have hbw : x.1.1*bidRatio ε x.2≤x.1.1:=by simpa using hb.2
    have hg:=zero_cluster_implemented_geometry hε.le hsmall hδ htau
      ⟨hc.1.le,x.1.property.2⟩ ⟨hb0,hc.2.le⟩ hbw hnoise z.property
    have hex:=zero_cluster_choice_exact hε hsmall hδ htau x.1 hc.1.le hnoise
    have hr : clusterRaisedBid hε hsmall δ δ (x,z)=3*δ*(1+ε*z.1) := by
      change x.1.1*bidRatio ε (crossingChoice ε hε hsmall δ δ x.1)*(1+ε*z.1)=_
      rw [hex]
    dsimp only at hg ⊢
    rw [hr]
    exact hg)

end FCAppendix.Affine.LowBody
