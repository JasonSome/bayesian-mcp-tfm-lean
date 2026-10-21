import FCAppendix.Affine.LowBody.NoisyCrossingGeometry

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set Classical
open Existence.Distributional

abbrev NoisyCarrier (d : ℝ):=(LowValue d×unitInterval)×unitInterval

def latentClusterCarrier {d : ℝ} (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A:=unitInterval) mu) (E : Set (LowValue d×unitInterval)) : Measure (NoisyCarrier d):=
  ((pi.1 : Measure (LowValue d×unitInterval)).restrict E).prod (volume : Measure unitInterval)

def physicalClusterMeasure {d ε : ℝ} (hε : 0<ε) (hsmall : ε≤1/2)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A:=unitInterval) mu) (E : Set (LowValue d×unitInterval)) : Measure ℝ:=
  (latentClusterCarrier mu pi E).map (fun x=>(noisyBid d ε hε hsmall x).1)

instance latentClusterCarrier_finite {d : ℝ} (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A:=unitInterval) mu) (E : Set (LowValue d×unitInterval)) :
    IsFiniteMeasure (latentClusterCarrier mu pi E):=inferInstanceAs
      (IsFiniteMeasure (((pi.1 : Measure (LowValue d×unitInterval)).restrict E).prod (volume : Measure unitInterval)))

instance physicalClusterMeasure_finite {d ε : ℝ} (hε : 0<ε) (hsmall : ε≤1/2)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A:=unitInterval) mu) (E : Set (LowValue d×unitInterval)) :
    IsFiniteMeasure (physicalClusterMeasure hε hsmall mu pi E):=inferInstanceAs
      (IsFiniteMeasure ((latentClusterCarrier mu pi E).map (fun x=>(noisyBid d ε hε hsmall x).1)))

theorem realLowBidLaw_lowNoisyLaw {d ε : ℝ} (hε : 0<ε) (hsmall : ε≤1/2)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu] (pi : Law (A:=unitInterval) mu) :
    (realLowBidLaw (lowNoisyLaw d ε hε hsmall mu pi).1 : Measure ℝ)=
      ((pi.1 : Measure (LowValue d×unitInterval)).prod (volume : Measure unitInterval)).map
        (fun x=>(noisyBid d ε hε hsmall x).1) := by
  let P:=(pi.1 : Measure (LowValue d×unitInterval)).prod (volume : Measure unitInterval)
  have hpsi : Measurable (fun x : NoisyCarrier d=>(x.1.1,noisyBid d ε hε hsmall x)) :=
    (measurable_fst.comp measurable_fst).prodMk (continuous_noisyBid d ε hε hsmall).measurable
  change (P.map (fun x=>(x.1.1,noisyBid d ε hε hsmall x))).map (fun x=>x.2.1)=_
  exact Measure.map_map (measurable_snd.subtype_val) hpsi

theorem physicalClusterMeasure_le {d ε : ℝ} (hε : 0<ε) (hsmall : ε≤1/2)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A:=unitInterval) mu) (E : Set (LowValue d×unitInterval)) :
    physicalClusterMeasure hε hsmall mu pi E≤
      (realLowBidLaw (lowNoisyLaw d ε hε hsmall mu pi).1 : Measure ℝ) := by
  rw [realLowBidLaw_lowNoisyLaw]
  exact Measure.map_mono (Measure.prod_mono Measure.restrict_le_self le_rfl)
    (continuous_noisyBid d ε hε hsmall).subtype_val.measurable

theorem latentClusterCarrier_mass {d : ℝ} (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A:=unitInterval) mu) (E : Set (LowValue d×unitInterval)) :
    (latentClusterCarrier mu pi E).real univ=(pi.1 : Measure (LowValue d×unitInterval)).real E := by
  change (((pi.1 : Measure (LowValue d×unitInterval)).restrict E).prod
    (volume : Measure unitInterval) univ).toReal=_
  rw [←univ_prod_univ,Measure.prod_prod]
  simp only [Measure.restrict_apply_univ,measure_univ,mul_one]
  rfl

theorem physicalClusterMeasure_mass {d ε : ℝ} (hε : 0<ε) (hsmall : ε≤1/2)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A:=unitInterval) mu) (E : Set (LowValue d×unitInterval)) :
    (physicalClusterMeasure hε hsmall mu pi E).real univ=
      (pi.1 : Measure (LowValue d×unitInterval)).real E := by
  rw [measureReal_def,physicalClusterMeasure,Measure.map_apply
    (continuous_noisyBid d ε hε hsmall).subtype_val.measurable MeasurableSet.univ,preimage_univ]
  exact latentClusterCarrier_mass mu pi E

theorem realLowBidLaw_lowNoisyLaw_atomless {d ε : ℝ} (hε : 0<ε) (hsmall : ε≤1/2)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A:=unitInterval) mu) (hmu : ∀ᵐw ∂mu,0<w.1) :
    NullSingletonClass (realLowBidLaw (lowNoisyLaw d ε hε hsmall mu pi).1 : Measure ℝ) := by
  let ν:=implementedBidLaw d ε hε hsmall mu pi
  letI : NullSingletonClass (ν : Measure (LowValue d)):=
    ⟨implementedBidLaw_singleton hε hsmall mu pi hmu⟩
  have hmap : (realLowBidLaw (lowNoisyLaw d ε hε hsmall mu pi).1 : Measure ℝ)=
      (ν : Measure (LowValue d)).map Subtype.val := by
    change ((lowNoisyLaw d ε hε hsmall mu pi).1 : Measure (LowValue d×LowValue d)).map
      (fun x=>x.2.1)=(((lowNoisyLaw d ε hε hsmall mu pi).1 : Measure (LowValue d×LowValue d)).map Prod.snd).map Subtype.val
    exact (Measure.map_map measurable_subtype_coe measurable_snd).symm
  constructor
  intro b
  rw [hmap,Measure.map_apply measurable_subtype_coe (measurableSet_singleton b)]
  exact measure_eq_zero_iff_ae_notMem.mpr
    (ae_injective_ne (ν : Measure (LowValue d)) Subtype.val Subtype.val_injective b)

theorem physicalClusterMeasure_atomless {d ε : ℝ} (hε : 0<ε) (hsmall : ε≤1/2)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A:=unitInterval) mu) (hmu : ∀ᵐw ∂mu,0<w.1)
    (E : Set (LowValue d×unitInterval)) :
    NullSingletonClass (physicalClusterMeasure hε hsmall mu pi E) := by
  letI:=realLowBidLaw_lowNoisyLaw_atomless hε hsmall mu pi hmu
  constructor
  intro b
  have hh:=Measure.le_iff'.mp (physicalClusterMeasure_le hε hsmall mu pi E) {b}
  exact le_antisymm (by simpa only [measure_singleton] using hh) bot_le

end FCAppendix.Affine.LowBody
