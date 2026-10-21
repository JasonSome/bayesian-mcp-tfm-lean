import FCAppendix.Affine.Hybrid.Finishing01Definitions
import FCAppendix.Affine.LowBody.FirstCopyPair
import FCAppendix.Affine.LowBody.ClusterMassLimits

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open scoped BigOperators

theorem finite_iid_weak_order_ge_half (theta : Measure ℝ) [IsFiniteMeasure theta] :
    (theta.real univ)^2/2 ≤ (theta.prod theta).real {p : ℝ×ℝ | p.1≤ p.2} := by
  let A : Set (ℝ×ℝ) := {p | p.1≤ p.2}
  let B : Set (ℝ×ℝ) := {p | p.2≤ p.1}
  have hA : MeasurableSet A := measurableSet_le measurable_fst measurable_snd
  have hB : MeasurableSet B := measurableSet_le measurable_snd measurable_fst
  have hswap := congrArg (fun nu : Measure (ℝ×ℝ) => nu A)
    (Measure.prod_swap (μ:=theta) (ν:=theta))
  rw [Measure.map_apply measurable_swap hA] at hswap
  have hAB : (theta.prod theta).real A=(theta.prod theta).real B := by
    simpa only [Measure.real,A,B,preimage_setOf_eq,Prod.fst_swap,Prod.snd_swap]
      using (congrArg ENNReal.toReal hswap).symm
  have hcover : A∪B=univ := by
    ext p
    simp only [mem_union,A,B,mem_setOf_eq,mem_univ,iff_true]
    exact le_total p.1 p.2
  have hbound := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨measure_ne_top (theta.prod theta) A,
      measure_ne_top (theta.prod theta) B⟩)
    (measure_union_le (μ:=theta.prod theta) A B)
  rw [hcover,ENNReal.toReal_add (measure_ne_top (theta.prod theta) A)
    (measure_ne_top (theta.prod theta) B)] at hbound
  change (theta.prod theta).real univ ≤
    (theta.prod theta).real A+(theta.prod theta).real B at hbound
  have hmass : (theta.prod theta).real univ=(theta.real univ)^2 := by
    rw [←univ_prod_univ,measureReal_prod_prod,pow_two]
  rw [hmass,←hAB] at hbound
  change (theta.real univ)^2/2≤(theta.prod theta).real A
  linarith

theorem retained_weak_order_ge_half (theta G : Measure ℝ)
    [IsFiniteMeasure theta] [IsFiniteMeasure G]
    (hdom : theta≤ G) (u : ℝ) (hu : ∀ᵐx ∂theta,x≤ u) :
    (theta.real univ)^2/2 ≤
      (theta.prod G).real {p : ℝ×ℝ | p.1≤ p.2 ∧ p.2≤ u} := by
  have hupper : ∀ᵐp : ℝ×ℝ ∂theta.prod theta,p.2≤ u := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le measurable_snd measurable_const)).mpr
    exact ae_of_all _ (fun _ => hu)
  have he : (fun p : ℝ×ℝ => p.1≤ p.2)=ᵐ[theta.prod theta]
      (fun p : ℝ×ℝ => p.1≤ p.2 ∧ p.2≤ u) := by
    filter_upwards [hupper] with p hp
    exact propext (by simp [hp])
  have hpair := finite_iid_weak_order_ge_half theta
  have he' : (theta.prod theta).real {p : ℝ×ℝ | p.1≤ p.2} =
      (theta.prod theta).real {p : ℝ×ℝ | p.1≤ p.2 ∧ p.2≤ u} := measureReal_congr he
  rw [he'] at hpair
  apply hpair.trans
  exact ENNReal.toReal_mono (measure_ne_top _ _)
    ((Measure.prod_mono (μ:=theta) le_rfl hdom) _)

theorem prod_crossing_mass_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (Gamma : Measure X) (nu : Measure Y) (G : Measure ℝ)
    [IsFiniteMeasure Gamma] [IsFiniteMeasure nu] [IsFiniteMeasure G]
    (old raised : X→ℝ) (hOld : Measurable old) (hRaised : Measurable raised)
    (rival : Y→ℝ) (hRival : Measurable rival) (hLaw : nu.map rival=G) :
    (Gamma.prod nu).real {p | rival p.2∈ Icc (old p.1) (raised p.1)} =
      (Gamma.prod G).real {p | p.2∈ Icc (old p.1) (raised p.1)} := by
  have hmap := Measure.map_prod_map Gamma nu measurable_id hRival
  rw [Measure.map_id,hLaw] at hmap
  have hE : MeasurableSet {p : X×ℝ | p.2∈ Icc (old p.1) (raised p.1)} :=
    (measurableSet_le (hOld.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd (hRaised.comp measurable_fst))
  change ((Gamma.prod nu) _).toReal=((Gamma.prod G) _).toReal
  rw [hmap,Measure.map_apply (measurable_id.prodMap hRival) hE]
  rfl

theorem retained_crossing_mass_lower {X : Type*} [MeasurableSpace X]
    (Gamma : Measure X) (G : Measure ℝ) [IsFiniteMeasure Gamma] [IsFiniteMeasure G]
    (old raised : X→ℝ) (hOld : Measurable old) (hRaised : Measurable raised)
    (hdom : Gamma.map old≤ G) (u : ℝ)
    (hOldU : ∀ᵐp ∂Gamma,old p≤ u) (hRaisedU : ∀ᵐp ∂Gamma,u≤ raised p) :
    (Gamma.real univ)^2/2 ≤
      (Gamma.prod G).real {p | p.2∈ Icc (old p.1) (raised p.1)} := by
  let theta := Gamma.map old
  have htheta : ∀ᵐx ∂theta,x≤ u := by
    exact (ae_map_iff hOld.aemeasurable
      (measurableSet_le measurable_id measurable_const)).mpr hOldU
  have hgain := retained_weak_order_ge_half theta G hdom u htheta
  have hmass : theta.real univ=Gamma.real univ := by
    simp only [theta,measureReal_def,Measure.map_apply hOld MeasurableSet.univ,preimage_univ]
  rw [hmass] at hgain
  have hmap := Measure.map_prod_map Gamma G hOld measurable_id
  rw [Measure.map_id] at hmap
  have hE : MeasurableSet {p : ℝ×ℝ | p.1≤ p.2 ∧ p.2≤ u} :=
    (measurableSet_le measurable_fst measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)
  have hmapMass : (theta.prod G).real {p : ℝ×ℝ | p.1≤ p.2 ∧ p.2≤ u}=
      (Gamma.prod G).real {p | old p.1≤ p.2 ∧ p.2≤ u} := by
    change ((theta.prod G) _).toReal=((Gamma.prod G) _).toReal
    rw [hmap,Measure.map_apply (hOld.prodMap measurable_id) hE]
    rfl
  rw [hmapMass] at hgain
  have hupper : ∀ᵐp : X×ℝ ∂Gamma.prod G,u≤ raised p.1 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le measurable_const
      (hRaised.comp measurable_fst))).mpr
    filter_upwards [hRaisedU] with x hx
    exact ae_of_all _ (fun _ => hx)
  apply hgain.trans
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [hupper] with p hp
  exact fun h => ⟨h.1,h.2.trans hp⟩

theorem retained_crossing_mass_upper {X : Type*} [MeasurableSpace X]
    (Gamma : Measure X) (G : Measure ℝ) [IsFiniteMeasure Gamma] [IsFiniteMeasure G]
    (old raised : X→ℝ) (hOld : Measurable old) (hRaised : Measurable raised)
    (l u : ℝ) (hOldL : ∀ᵐp ∂Gamma,l≤ old p)
    (hRaisedU : ∀ᵐp ∂Gamma,raised p≤ u) :
    (Gamma.prod G).real {p | p.2∈ Icc (old p.1) (raised p.1)} ≤
      Gamma.real univ*G.real (Icc l u) := by
  rw [←measureReal_prod_prod]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  have hgeo : ∀ᵐp : X×ℝ ∂Gamma.prod G,l≤ old p.1 ∧ raised p.1≤ u := by
    apply (Measure.ae_prod_iff_ae_ae
      ((measurableSet_le measurable_const (hOld.comp measurable_fst)).inter
        (measurableSet_le (hRaised.comp measurable_fst) measurable_const))).mpr
    filter_upwards [hOldL,hRaisedU] with x hx hy
    exact ae_of_all _ (fun _ => ⟨hx,hy⟩)
  filter_upwards [hgeo] with p hp
  exact fun h => ⟨mem_univ _,hp.1.trans h.1,h.2.trans hp.2⟩

namespace Finish01.Primitives
variable (P : Primitives)
abbrev ClusterCarrier := (P.Value×P.Bid)×unitInterval

def activeLatentClusterCarrier (mu : Measure P.Value) [IsProbabilityMeasure mu]
    (pi : Existence.Distributional.Law (A:=P.Bid) mu) (E : Set (P.Value×P.Bid)) :
    Measure P.ClusterCarrier :=
  ((pi.1 : Measure (P.Value×P.Bid)).restrict E).prod (volume : Measure unitInterval)

def realImplementedActiveLaw (mu : Measure P.Value) [IsProbabilityMeasure mu]
    (eps : ℝ) (pi : Existence.Distributional.Law (A:=P.Bid) mu) : Measure ℝ :=
  ((pi.1 : Measure (P.Value×P.Bid)).prod (volume : Measure unitInterval)).map
    (fun t => activeNoisyRealBid eps t.1.2 t.2)

def activePhysicalClusterMeasure (mu : Measure P.Value) [IsProbabilityMeasure mu]
    (eps : ℝ) (pi : Existence.Distributional.Law (A:=P.Bid) mu)
    (E : Set (P.Value×P.Bid)) : Measure ℝ :=
  (P.activeLatentClusterCarrier mu pi E).map (fun t => activeNoisyRealBid eps t.1.2 t.2)

lemma measurable_clusterOld (eps : ℝ) :
    Measurable (fun t : P.ClusterCarrier => activeNoisyRealBid eps t.1.2 t.2) := by
  unfold activeNoisyRealBid
  fun_prop

instance activeLatentClusterCarrier_finite (mu : Measure P.Value) [IsProbabilityMeasure mu]
    (pi : Existence.Distributional.Law (A:=P.Bid) mu) (E : Set (P.Value×P.Bid)) :
    IsFiniteMeasure (P.activeLatentClusterCarrier mu pi E) := by
  unfold activeLatentClusterCarrier
  infer_instance

instance realImplementedActiveLaw_probability (mu : Measure P.Value) [IsProbabilityMeasure mu]
    (eps : ℝ) (pi : Existence.Distributional.Law (A:=P.Bid) mu) :
    IsProbabilityMeasure (P.realImplementedActiveLaw mu eps pi) := by
  unfold realImplementedActiveLaw
  exact Measure.isProbabilityMeasure_map (P.measurable_clusterOld eps).aemeasurable

instance activePhysicalClusterMeasure_finite (mu : Measure P.Value) [IsProbabilityMeasure mu]
    (eps : ℝ) (pi : Existence.Distributional.Law (A:=P.Bid) mu)
    (E : Set (P.Value×P.Bid)) : IsFiniteMeasure (P.activePhysicalClusterMeasure mu eps pi E) := by
  unfold activePhysicalClusterMeasure
  infer_instance

theorem activePhysicalClusterMeasure_le (mu : Measure P.Value) [IsProbabilityMeasure mu]
    (eps : ℝ) (pi : Existence.Distributional.Law (A:=P.Bid) mu)
    (E : Set (P.Value×P.Bid)) :
    P.activePhysicalClusterMeasure mu eps pi E≤ P.realImplementedActiveLaw mu eps pi := by
  exact Measure.map_mono (Measure.prod_mono Measure.restrict_le_self le_rfl)
    (P.measurable_clusterOld eps)

theorem activeLatentClusterCarrier_mass (mu : Measure P.Value) [IsProbabilityMeasure mu]
    (pi : Existence.Distributional.Law (A:=P.Bid) mu) (E : Set (P.Value×P.Bid)) :
    (P.activeLatentClusterCarrier mu pi E).real univ=(pi.1:Measure (P.Value×P.Bid)).real E := by
  change ((((pi.1 : Measure (P.Value×P.Bid)).restrict E).prod
    (volume : Measure unitInterval)) univ).toReal = _
  rw [←univ_prod_univ,Measure.prod_prod]
  simp only [Measure.restrict_apply_univ,measure_univ,mul_one]
  rfl

theorem activePhysicalClusterMeasure_mass (mu : Measure P.Value) [IsProbabilityMeasure mu]
    (eps : ℝ) (pi : Existence.Distributional.Law (A:=P.Bid) mu)
    (E : Set (P.Value×P.Bid)) :
    (P.activePhysicalClusterMeasure mu eps pi E).real univ=
      (pi.1:Measure (P.Value×P.Bid)).real E := by
  rw [measureReal_def,activePhysicalClusterMeasure,
    Measure.map_apply (P.measurable_clusterOld eps) MeasurableSet.univ,preimage_univ]
  exact P.activeLatentClusterCarrier_mass mu pi E

end Finish01.Primitives
end FCAppendix.Affine.Hybrid
