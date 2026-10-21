import FCAppendix.Affine.LowBody.ClusterLimitContraction
import FCAppendix.Affine.LowBody.BaseJointLimit
import FCAppendix.Affine.LowBody.NoisyClusterSupport

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open Existence.Distributional

theorem open_mass_bound_of_finite_quadratic {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (mu : ℕ→ProbabilityMeasure X) (mu₀ : ProbabilityMeasure X)
    (hmu : Tendsto mu atTop (𝓝 mu₀)) (E : Set X) (hE : IsOpen E)
    (A err : ℝ) (hA : 0<A) (herr : 0≤err)
    (Aj ej : ℕ→ℝ) (hAj : Tendsto Aj atTop (𝓝 A))
    (hej : Tendsto ej atTop (𝓝 err))
    (hfinite : ∀ᶠj : ℕ in atTop,
      (mu j : Measure X).real E ^2*Aj j≤(mu j : Measure X).real E*ej j) :
    (mu₀ : Measure X).real E*A≤err := by
  let mass : ℕ→unitInterval:=fun j=>⟨(mu j : Measure X).real E,measureReal_nonneg,measureReal_le_one⟩
  obtain ⟨p,phi,hphi,ht⟩:=CompactSpace.tendsto_subseq mass
  have hp : Tendsto (fun j=>(mu (phi j) : Measure X).real E) atTop (𝓝 p.1):=
    continuous_subtype_val.continuousAt.tendsto.comp ht
  have hpoly : p.1^2*A≤p.1*err :=
    le_of_tendsto_of_tendsto ((hp.pow 2).mul (hAj.comp hphi.tendsto_atTop))
      (hp.mul (hej.comp hphi.tendsto_atTop)) (hphi.tendsto_atTop.eventually hfinite)
  have hmass : (mu₀ : Measure X).real E≤p.1 := by
    have hh:=ProbabilityMeasure.le_liminf_measure_open_of_tendsto
      (hmu.comp hphi.tendsto_atTop) hE
    have ht' : Tendsto (fun j=>(mu (phi j) : Measure X) E) atTop (𝓝 (ENNReal.ofReal p.1)) :=
      (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hp).congr'
        (Eventually.of_forall (fun j=>ENNReal.ofReal_toReal (measure_ne_top (mu (phi j) : Measure X) E)))
    simp only [Function.comp_apply] at hh
    rw [ht'.liminf_eq] at hh
    have hb : (mu₀ : Measure X) E≤ENNReal.ofReal p.1 := by
      simpa only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hh
    exact ENNReal.toReal_le_of_le_ofReal p.property.1 hb
  by_cases hp0 : p.1=0
  · have hz : (mu₀ : Measure X).real E=0:=le_antisymm (by simpa only [hp0] using hmass) measureReal_nonneg
    simpa only [hz,zero_mul] using herr
  · have hppos : 0<p.1:=lt_of_le_of_ne p.property.1 (Ne.symm hp0)
    have hcancel : p.1*A≤err := by nlinarith only [hpoly,hppos]
    exact (mul_le_mul_of_nonneg_right hmass hA.le).trans hcancel

def physicalZeroCluster {d : ℝ} (tau δ : ℝ) : Set (LowValue d×LowValue d):=
  {x | tau<x.1.1 ∧ x.2.1<δ}

theorem isOpen_physicalZeroCluster {d : ℝ} (tau δ : ℝ) :
    IsOpen (physicalZeroCluster (d:=d) tau δ) := by
  exact (isOpen_lt continuous_const (continuous_subtype_val.comp continuous_fst)).inter
    (isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const)

theorem zeroBaseClusterSet_mass {d ε : ℝ} (hε : 0<ε) (hsmall : ε≤1/2)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A:=unitInterval) mu) (tau δ : ℝ) :
    (pi.1 : Measure (LowValue d×unitInterval)).real (zeroBaseClusterSet hε hsmall tau δ)=
      (baseJointLaw d ε hε hsmall mu pi : Measure (LowValue d×LowValue d)).real
        (physicalZeroCluster tau δ) := by
  rw [measureReal_def,measureReal_def]
  congr 1
  exact (Measure.map_apply
    (measurable_fst.prodMk (continuous_baseBid d ε hε hsmall).measurable)
      (isOpen_physicalZeroCluster tau δ).measurableSet).symm

theorem law_value_positive {d : ℝ} (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A:=LowValue d) mu) (hmu : ∀ᵐw ∂mu,0<w.1) :
    ∀ᵐx ∂(pi.1 : Measure (LowValue d×LowValue d)),0<x.1.1 := by
  have hmap : ∀ᵐw ∂((pi.1 : Measure (LowValue d×LowValue d)).map Prod.fst),0<w.1 := by
    rw [pi.2]
    exact hmu
  exact (ae_map_iff measurable_fst.aemeasurable
    (measurableSet_lt measurable_const measurable_subtype_coe)).mp hmap

theorem zero_bid_mass_eq_zero_of_cluster_bounds {d A K : ℝ}
    (mu : Measure (LowValue d×LowValue d)) [IsFiniteMeasure mu]
    (hA : 0<A) (hvalue : ∀ᵐx ∂mu,0<x.1.1)
    (hbound : ∀tau : ℝ,0<tau→∀δ : ℝ,0<δ→4*δ≤tau→
      mu.real (physicalZeroCluster tau δ)*((tau-2*δ)*A)≤K*δ) :
    mu {x | x.2.1=0}=0 := by
  have hcut (tau : ℝ) (htau : 0<tau) : mu {x | tau<x.1.1 ∧ x.2.1=0}=0 := by
    let M:=mu.real {x | tau<x.1.1 ∧ x.2.1=0}
    let δ : ℕ→ℝ:=fun j=>tau/(4*((j:ℝ)+1))
    have hδpos (j : ℕ) : 0<δ j:=by dsimp [δ]; positivity
    have hδroom (j : ℕ) : 4*δ j≤tau := by
      dsimp [δ]
      have hj : (1:ℝ)≤(j:ℝ)+1:=by have hh : (0:ℝ)≤(j:ℝ):=Nat.cast_nonneg j; linarith
      rw [←mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0<4*((j:ℝ)+1))).mpr
      nlinarith
    have hδlim : Tendsto δ atTop (𝓝 0) := by
      have hh:=(tendsto_const_div_atTop_nhds_zero_nat (tau/4)).comp
        (tendsto_add_atTop_nat 1)
      convert hh using 1
      ext j
      simp only [δ,Function.comp_apply,Nat.cast_add,Nat.cast_one,div_div]
    have hcutbound (j : ℕ) : M*((tau-2*δ j)*A)≤K*δ j := by
      have hm : M ≤ mu.real (physicalZeroCluster tau (δ j)):=by
        exact measureReal_mono (fun x hx=>
          ⟨hx.1,by simpa only [hx.2] using hδpos j⟩) (measure_ne_top mu _)
      have hn : 0≤(tau-2*δ j)*A:=mul_nonneg (by linarith [hδroom j]) hA.le
      exact (mul_le_mul_of_nonneg_right hm hn).trans (hbound tau htau (δ j) (hδpos j) (hδroom j))
    have hl : M*(tau*A)≤0:=le_of_tendsto_of_tendsto
      (by simpa using (((tendsto_const_nhds (x:=tau)).sub (hδlim.const_mul 2)).mul_const A).const_mul M)
      (by simpa using hδlim.const_mul K) (Eventually.of_forall hcutbound)
    have hM : M=0:=le_antisymm (by nlinarith [mul_pos htau hA]) measureReal_nonneg
    exact (ENNReal.toReal_eq_zero_iff _).mp hM |>.resolve_right (measure_ne_top mu _)
  have hne : ∀ᵐx ∂mu,∀n : ℕ,¬((1:ℝ)/((n:ℝ)+1)<x.1.1 ∧ x.2.1=0) := by
    apply ae_all_iff.mpr
    intro n
    exact measure_eq_zero_iff_ae_notMem.mp (hcut (1/((n:ℝ)+1)) (by positivity))
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [hvalue,hne] with x hx hn
  intro hz
  obtain ⟨n,hnt⟩:=exists_nat_one_div_lt hx
  exact hn n ⟨by simpa only [Nat.cast_add,Nat.cast_one] using hnt,hz⟩

theorem no_zero_atom_of_actual_cluster_estimates {d A K : ℝ}
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (hmu : ∀ᵐw ∂mu,0<w.1) (hA : 0<A) (hK : 0≤K)
    (eps : ℕ→ℝ) (heps : ∀j,0<eps j) (hsmall : ∀j,eps j≤1/2)
    (pi : ℕ→Law (A:=unitInterval) mu) (pi0 : Law (A:=LowValue d) mu)
    (heps0 : Tendsto eps atTop (𝓝 0))
    (hlim : Tendsto (fun j=>(lowNoisyLaw d (eps j) (heps j) (hsmall j) mu (pi j)).1)
      atTop (𝓝 pi0.1))
    (hfinite : ∀tau : ℝ,0<tau→∀δ : ℝ,0<δ→4*δ≤tau→∀ᶠj : ℕ in atTop,
      ((pi j).1 : Measure (LowValue d×unitInterval)).real
        (zeroBaseClusterSet (heps j) (hsmall j) tau δ)^2*((tau-2*δ)*A)≤
      ((pi j).1 : Measure (LowValue d×unitInterval)).real
        (zeroBaseClusterSet (heps j) (hsmall j) tau δ)*(K*δ)) :
    (realLowBidLaw pi0.1 : Measure ℝ) {0}=0 := by
  have hbase:=baseJointLaw_tendsto mu eps heps hsmall pi pi0 heps0 hlim
  have hbound : ∀tau : ℝ,0<tau→∀δ : ℝ,0<δ→4*δ≤tau→
      (pi0.1 : Measure (LowValue d×LowValue d)).real (physicalZeroCluster tau δ)*
        ((tau-2*δ)*A)≤K*δ := by
    intro tau htau δ hδ hroom
    have hcoef : 0<(tau-2*δ)*A:=mul_pos (by linarith) hA
    apply open_mass_bound_of_finite_quadratic
      (fun j=>baseJointLaw d (eps j) (heps j) (hsmall j) mu (pi j)) pi0.1 hbase
      (physicalZeroCluster tau δ) (isOpen_physicalZeroCluster tau δ)
      ((tau-2*δ)*A) (K*δ) hcoef (mul_nonneg hK hδ.le)
      (fun _=>(tau-2*δ)*A) (fun _=>K*δ) tendsto_const_nhds tendsto_const_nhds
    filter_upwards [hfinite tau htau δ hδ hroom] with j hj
    simpa only [zeroBaseClusterSet_mass] using hj
  have hz:=zero_bid_mass_eq_zero_of_cluster_bounds (pi0.1 : Measure (LowValue d×LowValue d))
    hA (law_value_positive mu pi0 hmu) hbound
  change ((pi0.1 : Measure (LowValue d×LowValue d)).map (fun x=>x.2.1)) {0}=0
  rw [Measure.map_apply measurable_snd.subtype_val (measurableSet_singleton 0)]
  exact hz

end FCAppendix.Affine.LowBody
