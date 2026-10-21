import FCAppendix.Affine.Hybrid.Finishing01ClusterIntegration
import FCAppendix.Affine.Hybrid.Finishing01ClusterLimit
import FCAppendix.Affine.Hybrid.Finishing01ClusterAsymptotics
import FCAppendix.Affine.Hybrid.Finishing01ClusterCoefficients
import FCAppendix.Affine.Hybrid.Finishing01MenusLocalization

noncomputable section
namespace FCAppendix.Affine.Hybrid.Finish01.Primitives
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open Existence.Distributional
open scoped BigOperators
variable (P : Primitives)

def realBaseActiveLaw (mu : Measure P.Value) [IsProbabilityMeasure mu]
    (pi : Law (A:=P.Bid) mu) : ProbabilityMeasure ℝ :=
  pi.1.map measurable_snd.subtype_val.aemeasurable

def realImplementedActiveProbability (mu : Measure P.Value) [IsProbabilityMeasure mu]
    (eps : ℝ) (pi : Law (A:=P.Bid) mu) : ProbabilityMeasure ℝ :=
  ⟨P.realImplementedActiveLaw mu eps pi,inferInstance⟩

theorem realImplementedActiveProbability_eq_universal
    (mu : Measure P.Value) [IsProbabilityMeasure mu] (eps : unitInterval)
    (pi : Law (A:=P.Bid) mu) :
    P.realImplementedActiveProbability mu eps pi=
      (activeUniversalNoisyLaw P.L_pos P.L_lt_U.le mu (eps,pi)).1.map
        measurable_snd.subtype_val.aemeasurable := by
  apply Subtype.ext
  change P.realImplementedActiveLaw mu eps pi=
    (((pi.1 : Measure P.Latent).prod (volume : Measure unitInterval)).map
      (fun x => (x.1.1,activeUniversalNoisyBid P.L_pos P.L_lt_U.le (eps,x)))).map
        (fun t => (t.2:ℝ))
  have hm : Measurable (fun x : P.AgentNoise =>
      (x.1.1,activeUniversalNoisyBid P.L_pos P.L_lt_U.le (eps,x))) :=
    (measurable_fst.comp measurable_fst).prodMk
      (((continuous_activeUniversalNoisyBid P.L_pos P.L_lt_U.le).comp
        (continuous_const.prodMk continuous_id)).measurable)
  rw [Measure.map_map measurable_snd.subtype_val hm]
  rfl

theorem realImplementedActiveProbability_zero
    (mu : Measure P.Value) [IsProbabilityMeasure mu] (pi : Law (A:=P.Bid) mu) :
    P.realImplementedActiveProbability mu 0 pi=P.realBaseActiveLaw mu pi := by
  apply Subtype.ext
  change (((pi.1:Measure P.Latent).prod (volume:Measure unitInterval)).map
    (fun x => activeNoisyRealBid 0 x.1.2 x.2))=
      (pi.1:Measure P.Latent).map (fun t => (t.2:ℝ))
  have he : (fun x : P.AgentNoise => activeNoisyRealBid 0 x.1.2 x.2)=
      (fun t : P.Latent => (t.2:ℝ))∘Prod.fst := by
    funext x
    simp only [activeNoisyRealBid,zero_mul,add_zero,mul_one,Function.comp_apply]
  rw [he,←Measure.map_map measurable_snd.subtype_val measurable_fst,
    Measure.map_fst_prod,measure_univ,one_smul]

theorem noisyWitness_real_base_tendsto {M c : ℕ}
    (low : ProbabilityMeasure P.Low) (mu : Measure P.Value) [IsProbabilityMeasure mu]
    (W : P.NoisyWitness M c low mu) :
    Tendsto (fun j => P.realBaseActiveLaw mu (W.noisy j)) atTop
      (𝓝 (P.realBaseActiveLaw mu W.joint)) := by
  exact (((ProbabilityMeasure.continuous_map continuous_snd.subtype_val).comp
    continuous_subtype_val).tendsto W.joint).comp W.joint_tendsto

theorem noisyWitness_real_implemented_tendsto {M c : ℕ}
    (low : ProbabilityMeasure P.Low) (mu : Measure P.Value) [IsProbabilityMeasure mu]
    (W : P.NoisyWitness M c low mu) :
    Tendsto (fun j => P.realImplementedActiveProbability mu (W.eps j) (W.noisy j))
      atTop (𝓝 (P.realBaseActiveLaw mu W.joint)) := by
  have hphys := (continuous_subtype_val.tendsto
    (activeUniversalNoisyLaw P.L_pos P.L_lt_U.le mu (0,W.joint))).comp W.physical_tendsto
  have hreal := ((ProbabilityMeasure.continuous_map continuous_snd.subtype_val).tendsto
    (activeUniversalNoisyLaw P.L_pos P.L_lt_U.le mu (0,W.joint)).1).comp hphys
  simpa only [Function.comp_def, ←P.realImplementedActiveProbability_eq_universal,
    Set.Icc.coe_zero,P.realImplementedActiveProbability_zero] using hreal

def latentBidCluster (b delta : ℝ) : Set P.Latent :=
  {t | (t.2:ℝ)∈ Ioo (b-delta) (b+delta)}

lemma measurableSet_latentBidCluster (b delta : ℝ) :
    MeasurableSet (P.latentBidCluster b delta) :=
  measurableSet_Ioo.preimage measurable_snd.subtype_val

theorem realBaseActiveLaw_cluster (mu : Measure P.Value) [IsProbabilityMeasure mu]
    (pi : Law (A:=P.Bid) mu) (b delta : ℝ) :
    (P.realBaseActiveLaw mu pi:Measure ℝ).real (Ioo (b-delta) (b+delta))=
      (pi.1:Measure P.Latent).real (P.latentBidCluster b delta) := by
  change (((pi.1:Measure P.Latent).map (fun t => (t.2:ℝ))) _).toReal=_
  rw [Measure.map_apply measurable_snd.subtype_val measurableSet_Ioo]
  rfl

theorem active_noise_increment (eps : unitInterval) (B : P.Bid) (z : unitInterval) :
    0≤ activeNoisyRealBid eps B z-(B:ℝ) ∧
      activeNoisyRealBid eps B z-(B:ℝ)≤(eps:ℝ)*P.U := by
  have hB : 0≤(B:ℝ) := (P.bid_pos B).le
  have he : 0≤(eps:ℝ) := eps.property.1
  have hcost : (B:ℝ)*(eps:ℝ)*(z:ℝ)≤(eps:ℝ)*P.U := by
    calc
      _ ≤ (B:ℝ)*(eps:ℝ)*1 :=
        mul_le_mul_of_nonneg_left z.property.2 (mul_nonneg hB he)
      _ = (eps:ℝ)*(B:ℝ) := by ring
      _ ≤ (eps:ℝ)*P.U := mul_le_mul_of_nonneg_left B.property.2 he
  unfold activeNoisyRealBid
  constructor
  · nlinarith [mul_nonneg (mul_nonneg hB he) z.property.1]
  · nlinarith

theorem implemented_law_inside_box_of_strip (eps : unitInterval)
    (mu : Measure P.Value) [IsProbabilityMeasure mu] (pi : Law (A:=P.Bid) mu)
    {tau : ℝ} (heps : (eps:ℝ)*P.U< tau)
    (hs : ∀ᵐt ∂(pi.1:Measure P.Latent),(t.2:ℝ)∈ Icc (P.L+tau) (P.U-tau)) :
    ∀ᵐb ∂P.realImplementedActiveLaw mu eps pi,b∈ Icc P.L P.U := by
  unfold realImplementedActiveLaw
  apply (ae_map_iff (P.measurable_clusterOld eps).aemeasurable measurableSet_Icc).mpr
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_Icc.preimage (P.measurable_clusterOld eps))).mpr
  filter_upwards [hs] with t ht
  exact ae_of_all _ (fun z => by
    have h := P.active_noise_increment eps t.2 z
    constructor
    · exact t.2.property.1.trans (by linarith [h.1])
    · linarith [h.2,ht.2])

def clusterTarget {tau b delta : ℝ} (_ht : 0< tau)
    (hb : b∈ Icc (P.L+tau) (P.U-tau)) (hd : 0< delta) (hdt : delta< tau/4) : P.Bid :=
  ⟨b+2*delta,by constructor <;> linarith [hb.1,hb.2]⟩

theorem actual_cluster_geometry {tau b delta radius : ℝ} (ht : 0< tau)
    (hb : b∈ Icc (P.L+tau) (P.U-tau)) (hd : 0< delta)
    (hdt : delta< tau/4) (hdr : delta< radius/4)
    (eps : unitInterval) (heps : (eps:ℝ)*P.U< delta)
    (x : P.AgentNoise) (hx : x.1∈ P.latentBidCluster b delta) :
    let target := P.clusterTarget ht hb hd hdt
    P.clusterOld eps x∈ Icc P.L P.U ∧
    P.clusterRaised eps target x∈ Icc P.L P.U ∧
    P.clusterOld eps x< P.clusterRaised eps target x ∧
    P.clusterRaised eps target x-P.clusterOld eps x< radius ∧
    P.clusterRaised eps target x-P.clusterOld eps x≤4*delta ∧
    b-delta≤ P.clusterOld eps x ∧ P.clusterOld eps x≤ b+2*delta ∧
    b+2*delta≤ P.clusterRaised eps target x ∧
    P.clusterRaised eps target x≤ b+3*delta := by
  let target := P.clusterTarget ht hb hd hdt
  have ho := P.active_noise_increment eps x.1.2 x.2
  have hr := P.active_noise_increment eps target x.2
  change b-delta<(x.1.2:ℝ) ∧ (x.1.2:ℝ)< b+delta at hx
  have htarg : (target:ℝ)=b+2*delta := rfl
  change 0≤ P.clusterOld eps x-(x.1.2:ℝ) ∧
    P.clusterOld eps x-(x.1.2:ℝ)≤(eps:ℝ)*P.U at ho
  change 0≤ P.clusterRaised eps target x-(target:ℝ) ∧
    P.clusterRaised eps target x-(target:ℝ)≤(eps:ℝ)*P.U at hr
  rw [htarg] at hr
  change P.clusterOld eps x∈ Icc P.L P.U ∧
    P.clusterRaised eps target x∈ Icc P.L P.U ∧ _
  have hol : b-delta< P.clusterOld eps x := by linarith [ho.1,hx.1]
  have hou : P.clusterOld eps x< b+2*delta := by linarith [ho.2,hx.2]
  have hrl : b+2*delta≤ P.clusterRaised eps target x := by linarith [hr.1]
  have hru : P.clusterRaised eps target x< b+3*delta := by linarith [hr.2]
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,hou.trans_le hrl,?_,?_,hol.le,hou.le,hrl,hru.le⟩
  all_goals linarith [hb.1,hb.2]

theorem retained_actual_cluster_geometry
    (mu : Measure P.Value) [IsProbabilityMeasure mu] (pi : Law (A:=P.Bid) mu)
    {tau b delta radius : ℝ} (ht : 0< tau)
    (hb : b∈ Icc (P.L+tau) (P.U-tau)) (hd : 0< delta)
    (hdt : delta< tau/4) (hdr : delta< radius/4)
    (eps : unitInterval) (heps : (eps:ℝ)*P.U< delta) :
    let target := P.clusterTarget ht hb hd hdt
    ∀ᵐx ∂P.activeLatentClusterCarrier mu pi (P.latentBidCluster b delta),
      P.clusterOld eps x∈ Icc P.L P.U ∧
      P.clusterRaised eps target x∈ Icc P.L P.U ∧
      P.clusterOld eps x< P.clusterRaised eps target x ∧
      P.clusterRaised eps target x-P.clusterOld eps x< radius ∧
      P.clusterRaised eps target x-P.clusterOld eps x≤4*delta ∧
      b-delta≤ P.clusterOld eps x ∧ P.clusterOld eps x≤ b+2*delta ∧
      b+2*delta≤ P.clusterRaised eps target x ∧
      P.clusterRaised eps target x≤ b+3*delta := by
  have hmem : ∀ᵐx ∂P.activeLatentClusterCarrier mu pi (P.latentBidCluster b delta),
      x.1∈ P.latentBidCluster b delta :=
    (measurePreserving_fst
      (μ:=(pi.1:Measure P.Latent).restrict (P.latentBidCluster b delta))
      (ν:=(volume:Measure unitInterval))).quasiMeasurePreserving.ae
        (ae_restrict_mem (P.measurableSet_latentBidCluster b delta))
  exact hmem.mono (fun x hx => P.actual_cluster_geometry ht hb hd hdt hdr eps heps x hx)

theorem fixed_market_atom_zero {M c : ℕ}
    (low : ProbabilityMeasure P.Low) (mu : Measure P.Value) [IsProbabilityMeasure mu]
    (W : P.NoisyWitness M c low mu) {tau deltaCount : ℝ} (ht : 0< tau)
    (hstrip : ∀ᶠj in atTop,∀ᵐt ∂((W.noisy j).1:Measure P.Latent),
      (t.2:ℝ)∈ Icc (P.L+tau) (P.U-tau))
    (hguard : (1:ℝ)/2≤(CommonList.iid P.categories (M-1)).prob
      (activePatternGuarded P.xi P.L P.U c P.z))
    (hpure : (CommonList.iid P.categories (M-1)).prob
      (activePatternPure P.xi P.L P.U c P.z)≤
        8*Real.exp (-((M-1:ℕ):ℝ)*deltaCount^2/2))
    (hdom : P.clusterPureCoefficient deltaCount (M-1)< P.clusterPositiveCoefficient (M-1))
    (b : ℝ) (hb : b∈ Icc (P.L+tau) (P.U-tau)) :
    (P.realBaseActiveLaw mu W.joint:Measure ℝ) {b}=0 := by
  let N := M-1
  let H := fun j => P.realBaseActiveLaw mu (W.noisy j)
  let G := fun j => P.realImplementedActiveProbability mu (W.eps j) (W.noisy j)
  let G0 := P.realBaseActiveLaw mu W.joint
  apply active_atom_zero_of_fixed_market_cluster_estimates H G G0
    (P.noisyWitness_real_base_tendsto low mu W)
    (P.noisyWitness_real_implemented_tendsto low mu W) b
    (P.clusterPositiveCoefficient_pos N)
    (P.clusterPureCoefficient_nonneg deltaCount N) hdom
    (mul_nonneg (by norm_num : (0:ℝ)≤8) P.kappa_pos.le)
  intro err herr
  obtain ⟨radius,hradius,hlower⟩ := P.actual_cluster_lower N c herr
  refine ⟨min (tau/4) (radius/4),lt_min (by positivity) (by positivity),?_⟩
  intro delta hd hdelta
  have hdt : delta< tau/4 := (lt_min_iff.mp hdelta).1
  have hdr : delta< radius/4 := (lt_min_iff.mp hdelta).2
  let target := P.clusterTarget ht hb hd hdt
  let E := P.latentBidCluster b delta
  have hnoise := P.eventually_noise_below W.eps W.eps_zero hd
  have hstable := P.all_pattern_physical_guard_identity (N:=N) c W.eps W.eps_zero
  filter_upwards [hstrip,hnoise,hstable] with j hs heps hst
  have hepsTau : (W.eps j:ℝ)*P.U< tau := heps.trans (by linarith)
  have hbox := P.implemented_law_inside_box_of_strip (W.eps j) mu (W.noisy j) hepsTau hs
  have hgeo := P.retained_actual_cluster_geometry mu (W.noisy j) ht hb hd hdt hdr (W.eps j) heps
  have hlow := hlower (W.eps j) low mu (W.noisy j) E target
    (b-delta) (b+2*delta) (b+3*delta) (4*delta) (by positivity) hst hbox hgeo
  obtain ⟨sigma,hmark,hdis,hIC⟩ := W.noisy_IC j
  letI := hmark
  have hnonpos := P.actual_cluster_integral_nonpos (N:=N) (W.eps j)
    (W.eps_pos j) c low mu (W.noisy j) sigma hdis hIC E target
  have hfinite := hlow.trans hnonpos
  let p := (H j:Measure ℝ).real (Ioo (b-delta) (b+delta))
  let e := (G j:Measure ℝ).real (Icc (b-delta) (b+3*delta))
  have hp : 0≤ p := measureReal_nonneg
  have he : 0≤ e := measureReal_nonneg
  have hmass : (P.activeLatentClusterCarrier mu (W.noisy j) E).real univ=p := by
    rw [P.activeLatentClusterCarrier_mass]
    exact (P.realBaseActiveLaw_cluster mu (W.noisy j) b delta).symm
  change P.clusterRankGain/(16*((N+1:ℕ):ℝ)^3)*
      (CommonList.iid P.categories N).prob (activePatternGuarded P.xi P.L P.U c P.z)*
        (P.activeLatentClusterCarrier mu (W.noisy j) E).real univ^2-
      P.eta*P.U*(N:ℝ)*(CommonList.iid P.categories N).prob
        (activePatternPure P.xi P.L P.U c P.z)*
        (P.activeLatentClusterCarrier mu (W.noisy j) E).real univ*e-
      (P.activeLatentClusterCarrier mu (W.noisy j) E).real univ*
        (err+2*P.kappa*(4*delta))≤0 at hfinite
  rw [hmass] at hfinite
  have hc0 : 0≤ P.clusterRankGain/(16*((N+1:ℕ):ℝ)^3) := by
    exact div_nonneg P.clusterRankGain_pos.le (by positivity)
  have hGain : P.clusterPositiveCoefficient N*p^2≤
      P.clusterRankGain/(16*((N+1:ℕ):ℝ)^3)*
        (CommonList.iid P.categories N).prob (activePatternGuarded P.xi P.L P.U c P.z)*p^2 := by
    calc
      _ = (P.clusterRankGain/(16*((N+1:ℕ):ℝ)^3)*(1/2))*p^2 := by
        unfold clusterPositiveCoefficient
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hguard hc0) (sq_nonneg p)
  have hLoss : P.eta*P.U*(N:ℝ)*(CommonList.iid P.categories N).prob
      (activePatternPure P.xi P.L P.U c P.z)*p*e≤
        P.clusterPureCoefficient deltaCount N*p*e := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpure
        (mul_nonneg (mul_nonneg P.eta_pos.le P.U_pos.le) (Nat.cast_nonneg N))) hp) he
  change P.clusterPositiveCoefficient N*p^2≤
    P.clusterPureCoefficient deltaCount N*p*e+p*(8*P.kappa*delta+err)
  nlinarith

theorem atomless_of_actual_noisyWitness (c : ℕ→ℕ)
    (hc : Tendsto (fun M => (c M:ℝ)/(M:ℝ)) atTop (𝓝 P.rho)) :
    ∀ᶠM in atTop,∀(low : ProbabilityMeasure P.Low)
      (mu : Measure P.Value) [IsProbabilityMeasure mu]
      (W : P.NoisyWitness M (c M) low mu),
      NullSingletonClass ((W.joint.1:Measure P.Latent).map Prod.snd) := by
  obtain ⟨tau,ht,hstrip⟩ := Finishing01Menus.uniform_full_row_menu_and_strip P c hc
  obtain ⟨deltaCount,hd,hpure⟩ := P.eventually_pure_branch_rate_one c hc
  have hguard := P.eventually_guarded_probability_half c hc
  have hdom := P.exponential_dominates_cluster_coefficient hd
  have hshift : Tendsto (fun M : ℕ => M-1) atTop atTop := by
    apply tendsto_atTop.2
    intro k
    filter_upwards [eventually_ge_atTop (k+1)] with M hM
    omega
  filter_upwards [hstrip,hshift.eventually hpure,hshift.eventually hguard,
    hshift.eventually hdom,eventually_ge_atTop (1:ℕ)] with M hs hp hg hcoef hM
  have hMc : (M-1)+1=M := by omega
  simp only [hMc] at hp hg
  intro low mu _ W
  obtain ⟨hpre,hpost⟩ := hs low mu W
  let S : Set P.Bid := {B | (B:ℝ)∈ Icc (P.L+tau) (P.U-tau)}
  apply nullSingleton_map_of_supported_singletons (W.joint.1:Measure P.Latent)
    Prod.snd measurable_snd S (measurableSet_Icc.preimage measurable_subtype_coe) hpost
  intro B hB
  have hcoef' : P.clusterPureCoefficient deltaCount (M-1)< P.clusterPositiveCoefficient (M-1) :=
    hcoef.trans (half_lt_self (P.clusterPositiveCoefficient_pos (M-1)))
  have hz := P.fixed_market_atom_zero low mu W ht hpre hg hp hcoef' (B:ℝ) hB
  change ((W.joint.1:Measure P.Latent).map (fun t => (t.2:ℝ))) {(B:ℝ)}=0 at hz
  rw [Measure.map_apply measurable_snd.subtype_val (measurableSet_singleton _)] at hz
  rw [Measure.map_apply measurable_snd (measurableSet_singleton _)]
  have hset : Prod.snd ⁻¹' ({B}:Set P.Bid)=
      (fun t : P.Latent => (t.2:ℝ)) ⁻¹' ({(B:ℝ)}:Set ℝ) := by
    ext t
    simp only [mem_preimage,mem_singleton_iff]
    exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩
  rwa [hset]

end FCAppendix.Affine.Hybrid.Finish01.Primitives
