import FCAppendix.Exclusive.NativeHighOptimal
import FCAppendix.Exclusive.SourceHomogeneousLow
import FCAppendix.Exclusive.SourceStationaryAtomless
import FCAppendix.Exclusive.SourceStationaryContinuation
import FCAppendix.Exclusive.ScarceExistenceData
import FCAppendix.Exclusive.ScarcePrimitiveSelection
import FCAppendix.Exclusive.ExistenceSourceClassification
import FCAppendix.Exclusive.FiniteMarketSequence

noncomputable section
namespace FCAppendix.Bayes.ExclusiveConstruction
open MeasureTheory ProbabilityTheory Game Exclusive Set Filter Topology
open Exclusive.Narrow.Existence ExclusiveSource Completion.Exclusive
open Exclusive.Construction

theorem exists_scarce_family_at_mass (d : ℕ) (hd : 1 ≤ d) (G : Schedule (d+1))
    (h : unitInterval) (rho g : ℝ) (hh : 0 < (h:ℝ)) (hrho : 0 < rho)
    (hrh : rho < (h:ℝ)) (hhbeta : (h:ℝ) < ((d+1:ℕ):ℝ)*rho)
    (hbeta : ((d+1:ℕ):ℝ)*rho < 1) (hg : 0 ≤ g) :
    Nonempty (ScarceEquilibriumFamily d G g rho (h:ℝ)) := by
  classical
  have hp0 : 0 < rho/(h:ℝ) := div_pos hrho hh
  have hp1 : rho/(h:ℝ) < 1 := (div_lt_one hh).mpr hrh
  have hn0 : (0:ℝ) < ((d+1:ℕ):ℝ) := by positivity
  have hscarce : 1/((d+1:ℕ):ℝ) < rho/(h:ℝ) := by
    apply (div_lt_div_iff₀ hn0 hh).mpr
    simpa only [one_mul,mul_one,mul_comm] using hhbeta
  obtain ⟨scaleLo,cap,hlo,hlocap,hscales⟩ :=
    exists_referenceBidScale_bounds d hd (rho/(h:ℝ)) hp0.le hp1
  have hcap : 0 < cap := hlo.trans_le hlocap
  have hlo1 : scaleLo ≤ 1 := by
    have hs := (hscales .unique trivial).1
    rwa [referenceBidScale_unique_eq_one d _ hp1] at hs
  obtain ⟨K⟩ := exists_scarce_lowMarketConstants d hd scaleLo (rho/(h:ℝ)) hlo hp1 hscarce
  obtain ⟨W,hWcap,_hWe,_hWt⟩ := exists_uniform_finite_constants_bounded d hd G h rho hh
    h.property.2 hrho hrh K.deltaCap 1 1 K.width_pos zero_lt_one zero_lt_one
  obtain ⟨dh,eh,etah,Mh,hdh,_hdhW,heh,_hehW,hetah,hHigh⟩ :=
    exists_bandSource_high_parameters d hd G h rho scaleLo cap hh hrho hrh hlo hscales K W hWcap
  obtain ⟨dl,etal,Ml,hdl,_hdlK,hetal,hLow⟩ :=
    exists_bandSource_homogeneous_low_parameters d hd h rho scaleLo cap hh hrho hrh hlo hcap K
  have ht1 : K.t < 1 := K.marker_floor.trans_lt
    (Real.exp_lt_one_iff.mpr (by linarith [K.width_pos]))
  obtain ⟨eta,epsClass,l,u,priceLo,priceHi,heta,hetaCut,hepsClass,hl,hlu,hu,hpriceLo,
    hpriceHi,hClass⟩ := uniform_source_classification_capped d hd G hh hrho hrh h.property.2
      (show 0 < 1-K.t by linarith)
  obtain ⟨dc,hdc,hlog⟩ := exists_log_band_inside_relative heta.1
  obtain ⟨U,hUd,hUe,hUt⟩ := exists_uniform_finite_constants_bounded d hd G h rho hh
    h.property.2 hrho hrh (min dh (min dl dc)) (min eh (min epsClass (1/4)))
    (min etah etal) (lt_min hdh (lt_min hdl hdc))
      (lt_min heh (lt_min hepsClass.1 (by norm_num))) (lt_min hetah hetal)
  have hUdh : U.delta ≤ dh := hUd.trans (min_le_left _ _)
  have hUdl : U.delta ≤ dl := hUd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hUdc : U.delta ≤ dc := hUd.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hUeh : U.eps ≤ eh := hUe.trans (min_le_left _ _)
  have hUec : U.eps ≤ epsClass := hUe.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hUquarter : U.eps ≤ 1/4 := hUe.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hUth : U.eta ≤ etah := hUt.trans (min_le_left _ _)
  have hUtl : U.eta ≤ etal := hUt.trans (min_le_right _ _)
  obtain ⟨H,hH,_hH1,hbase,hbaseStrict,hgQuarter⟩ := exists_high_center g U.eps hg U.eps_pos
  have hseparate : g+H*K.lowUpper < H*(1-U.eps) :=
    normalized_low_band_separation K hlo1 hH hUquarter hgQuarter
  let nu := normalizedUniformLaw U.eps U.eps_pos.le
  letI : IsProbabilityMeasure nu := normalizedUniformLaw_probability _ _
  letI : NullSingletonClass nu := normalizedUniformLaw_atomless U.eps_pos
  let F := bandPrimitive h H nu g (H*K.lowUpper)
  let E := bandHighSet U.eps H
  letI : IsProbabilityMeasure F := bandPrimitive_probability h H nu g _
  letI : NullSingletonClass F := bandPrimitive_atomless h nu g hH (mul_pos hH K.low_pos)
  have hprimitive := bandPrimitive_properties h nu g hH (mul_pos hH K.low_pos) hseparate
  let threshold := max U.M0 (max Mh (Ml+1))
  have htail : ∀ᶠ t in atTop, threshold ≤ t+1 ∧
      |(marketCapacity rho t:ℝ)/((t:ℝ)+1)-rho| < U.eta ∧
      0 < marketCapacity rho t ∧ (d+1)*marketCapacity rho t+d ≤ t+1 := by
    filter_upwards [eventually_ge_atTop threshold,
      (marketDensity_tendsto hrho.le).eventually (Metric.ball_mem_nhds rho U.eta_pos),
      eventually_marker_room (d+1) hrho hbeta] with t ht hC hroom
    refine ⟨by omega,?_,hroom.1,?_⟩
    · simpa only [Metric.mem_ball,Real.dist_eq,marketPopulation,Nat.cast_add,Nat.cast_one] using hC
    · simpa only [Nat.add_sub_cancel,marketPopulation] using hroom.2
  obtain ⟨T,hT⟩ := eventually_atTop.mp htail
  let M := fun t : ℕ => t+T+1
  let C := fun t : ℕ => marketCapacity rho (t+T)
  have hrow (t : ℕ) := hT (t+T) (by omega)
  have hM : Tendsto M atTop atTop := (tendsto_add_atTop_nat 1).comp (tendsto_add_atTop_nat T)
  have hDensity : Tendsto (fun t => (C t:ℝ)/(M t:ℝ)) atTop (𝓝 rho) :=
    (marketDensity_tendsto hrho.le).comp (tendsto_add_atTop_nat T)
  have hCpositive (t : ℕ) : 0 < C t := (hrow t).2.2.1
  have hCU (t : ℕ) : |(C t:ℝ)/(((t+T:ℕ):ℝ)+1)-rho| < U.eta := (hrow t).2.1
  have hMU (t : ℕ) : U.M0 ≤ t+T+1 := (le_max_left _ _).trans (hrow t).1
  have hMH (t : ℕ) : Mh ≤ t+T+1 :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (hrow t).1
  have hML (t : ℕ) : Ml ≤ t+T := by
    have hh := ((le_max_right Mh (Ml+1)).trans (le_max_right U.M0 (max Mh (Ml+1)))).trans (hrow t).1
    omega
  have hroom (t : ℕ) : (d+1)-1 ≤ M t-(d+1)*C t := by
    have hh := (hrow t).2.2.2
    dsimp [M,C]
    omega
  have hexists (a : UserTariff) (ha : a.Allowed) (t : ℕ) :
      ∃ Γ : FiniteGame (M t) (d+1) (C t) unitInterval, ∃ B : PosteriorSystem Γ,
        Γ.F=F ∧ Γ.G=G ∧ Γ.g=g ∧ ExclusiveTariffUsersOptimal Γ a ∧
        ExclusivePosteriorOptimalAE Γ B ∧ SymmetricProposersOnPath Γ ∧ PolicyLawEquivariant Γ ∧
        ExclusiveBroadcastOn Γ E ∧
        (∀ b, (Measure.map (fun x : ℝ×JointAction (d+1) => x.2.bid) ((F.restrict E) ⊗ₘ Γ.σ)) {b}=0) ∧
        (∀ᵐ v ∂Γ.F, ∀ᵐ x ∂Γ.σ v, v ∈ E →
          x.bid ∈ Ioo (H*sourceBid d a h rho*(1-eta)) (H*sourceBid d a h rho*(1+eta))) ∧
        RawBandContinuation Γ B (H*sourceBid d a h rho*(1-eta))
          (H*sourceBid d a h rho*(1+eta)) := by
    obtain ⟨beta,hmono,hroot⟩ := U.exists_pure_stationary hd h.property hp0.le hp1 (C t)
      (hMU t) (hCU t) nu a ha (g/H) hbase
    let scale := H*referenceBidScale d a (rho/(h:ℝ))
    have hs : 0 < scale := mul_pos hH (referenceBidScale_pos d hd a ha _ hp0.le hp1)
    have hbandh : ∀ v, beta.val v ∈ Icc (-dh) dh := fun v =>
      ⟨(neg_le_neg hUdh).trans (beta.property v).1,(beta.property v).2.trans hUdh⟩
    have hbandl : ∀ v, beta.val v ∈ Icc (-dl) dl := fun v =>
      ⟨(neg_le_neg hUdl).trans (beta.property v).1,(beta.property v).2.trans hUdl⟩
    have hcut : scale*K.t ≤ scale*Real.exp (-U.delta) := by
      apply mul_le_mul_of_nonneg_left _ hs.le
      exact K.marker_floor.trans (Real.exp_le_exp.mpr (neg_le_neg (hUdl.trans _hdlK)))
    let Γ := bandSourceGame (M t) (d+1) (C t) (by dsimp [M]; omega) (by omega)
      (hCpositive t) h U.eps_pos.le H scale beta.val beta.val.continuous nu
      (Schedule.once (d+1)) G g hg (H*K.lowUpper) (scale*K.t)
    let B := bandSourcePosterior (by dsimp [M]; omega) (by omega) (hCpositive t)
      h U.eps_pos.le H scale beta.val beta.val.continuous nu (Schedule.once (d+1)) G g hg
      (H*K.lowUpper) (scale*K.t) hs.le beta.property hcut (hroom t)
    have husers : ExclusiveTariffUsersOptimal Γ a := by
      apply bandSourceGame_users_optimal (by dsimp [M]; omega) (by omega) (hCpositive t)
        h U.eps_pos.le hH scale beta.val beta.val.continuous nu (Schedule.once (d+1)) G g hg
        (mul_pos hH K.low_pos) (scale*K.t) hseparate a
      · exact hHigh (t+T) (C t) (hMH t) (hCpositive t) ((hCU t).trans_le hUth)
          U.eps_pos.le hUeh H hH g hg hbase.2 hseparate nu a ha beta.val beta.val.continuous
          hbandh hmono hroot (Schedule.once (d+1))
      · intro i v hv
        exact hLow (t+T) (C t) (hML t) (hCpositive t) ((hCU t).trans_le hUtl)
          U.eps_pos.le H hH _ (hscales a ha) beta.val beta.val.continuous hbandl hmono
          nu (Schedule.once (d+1)) G g hg hseparate a ha i v (by linarith [hv.2])
    have hscaleSource : scale=H*sourceBid d a h rho := rfl
    have hrelative : ∀ v, Real.exp (beta.val v) ∈ Ioo (1-eta) (1+eta) := fun v =>
      hlog _ ⟨(neg_le_neg hUdc).trans (beta.property v).1,(beta.property v).2.trans hUdc⟩
    have hcanonical := bandSourceGame_rawContinuation (by dsimp [M]; omega) (by omega)
      (hCpositive t) h U.eps_pos.le H scale beta.val beta.val.continuous nu
      (Schedule.once (d+1)) G g hg (H*K.lowUpper) (scale*K.t) hs.le beta.property hcut
      (hroom t) (k := d) rfl (scale*(1-eta)) (scale*(1+eta))
      (mul_le_mul_of_nonneg_left (by linarith : K.t ≤ 1-eta) hs.le)
    refine ⟨Γ,B,rfl,rfl,rfl,husers,?_,?_,?_,?_,?_,?_,?_⟩
    · exact bandSourceGame_proposer_optimal (by dsimp [M]; omega) (by omega) (hCpositive t)
        h U.eps_pos.le H scale beta.val beta.val.continuous nu (Schedule.once (d+1)) G g hg
        (H*K.lowUpper) (scale*K.t) hs.le beta.property hcut (hroom t) (k := d) rfl
    · exact bandSourceGame_symmetric (by dsimp [M]; omega) (by omega) (hCpositive t)
        h U.eps_pos.le H scale beta.val beta.val.continuous nu (Schedule.once (d+1)) G g hg
        (H*K.lowUpper) (scale*K.t)
    · exact bandSourceGame_equivariant (by dsimp [M]; omega) (by omega) (hCpositive t)
        h U.eps_pos.le H scale beta.val beta.val.continuous nu (Schedule.once (d+1)) G g hg
        (H*K.lowUpper) (scale*K.t)
    · exact bandSourceGame_broadcast (by dsimp [M]; omega) (by omega) (hCpositive t)
        h U.eps_pos.le H scale beta.val beta.val.continuous nu (Schedule.once (d+1)) G g hg
        (H*K.lowUpper) (scale*K.t) hs
    · have hat := bandSourceGame_active_bids_atomless (m := M t) (by dsimp [M]; omega) (by omega)
        (hCpositive t) h U.eps_pos.le hH hs beta.val beta.val.continuous hmono nu
        (Schedule.once (d+1)) G g hg (mul_pos hH K.low_pos) (scale*K.t)
      intro b
      exact hat.measure_singleton b
    · simpa only [Γ,E,← hscaleSource] using bandSourceGame_relative_band (by dsimp [M]; omega)
        (by omega) (hCpositive t) h U.eps_pos.le H scale hs beta.val beta.val.continuous nu
        (Schedule.once (d+1)) G g hg (H*K.lowUpper) (scale*K.t) eta hrelative
    · simpa only [hscaleSource] using hcanonical
  choose Γ B hF hG hfee husers hproposers hsym hequiv hbroadcast hatom hband hcanonical using hexists
  have hvalues : ∀ᵐ v ∂F.restrict E, v ∈ Icc (H*(1-epsClass)) (H*(1+epsClass)) := by
    filter_upwards [ae_restrict_mem (μ := F) (show MeasurableSet E from measurableSet_Icc)] with v hv
    have hv' : v ∈ Icc (H*(1-U.eps)) (H*(1+U.eps)) := hv
    constructor <;> nlinarith [hv'.1,hv'.2,mul_nonneg hH.le (sub_nonneg.mpr hUec)]
  have hlimits (a : UserTariff) (ha : a.Allowed) :=
    hClass H g hH hg (hbaseStrict.trans_le hUec) a ha (Γ a ha) (B a ha) F E measurableSet_Icc
      hprimitive.1 (hF a ha) (hG a ha) (hfee a ha) hvalues
      (Eventually.of_forall (husers a ha)) (Eventually.of_forall (hbroadcast a ha))
      (Eventually.of_forall (hband a ha)) (Eventually.of_forall (hcanonical a ha)) hM hDensity
  refine ⟨{
    F := F, probability := inferInstance, atomless := inferInstance,
    E := E, measurable_E := measurableSet_Icc, high_mass := hprimitive.1,
    positive_values := hprimitive.2.1, H := H, eps := U.eps, lowWidth := H*K.lowUpper,
    H_pos := hH, eps_pos := U.eps_pos, eps_lt_one := U.eps_lt_one,
    lowWidth_pos := mul_pos hH K.low_pos, high_set := rfl, separation := hseparate,
    high_values := ae_restrict_mem measurableSet_Icc,
    efficient_cutoff := bandPrimitive_efficient_cutoff h nu hH (mul_pos hH K.low_pos)
      hseparate hhbeta hbeta,
    M := M, C := C, population_positive := fun t => by dsimp [M]; omega,
    capacity_positive := hCpositive, population_grows := hM, density := hDensity,
    game := Γ, posterior := B, common_values := hF, common_base := hG, common_fee := hfee,
    users := husers, proposers := hproposers, symmetric := hsym, equivariant := hequiv,
    broadcast := hbroadcast, finite_atomless := hatom,
    eta := eta, l := l, u := u, priceLo := priceLo, priceHi := priceHi, eta_mem := heta,
    exposure_bounds := ⟨hl,hlu,hu⟩, price_bounds := ⟨hpriceLo,hpriceHi⟩,
    source_limits := hlimits }⟩

theorem prop_exclusive_exists (d : ℕ) (hd : 1 ≤ d) (G : Schedule (d+1))
    (g rho zeta : ℝ) (hg : 0 ≤ g) (hrho : 0 < rho)
    (hbeta : ((d+1:ℕ):ℝ)*rho < 1) (hzeta : 0 < zeta) :
    ∃ h : ℝ, rho < h ∧ h < ((d+1:ℕ):ℝ)*rho ∧ h < 1 ∧
      ∃ D : ScarceEquilibriumFamily d G g rho h,
      ∀ a : UserTariff, ∀ ha : a.Allowed,
        ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ Q mu : ℝ,
          0 < Q ∧ ((d+1:ℕ):ℝ)-zeta < mu ∧ mu ≤ ((d+1:ℕ):ℝ) ∧
          Tendsto (fun t => finiteCoverage (D.game a ha (phi t))) atTop (𝓝 Q) ∧
          Tendsto (fun t => finiteMultiplicity (D.game a ha (phi t))) atTop (𝓝 mu) := by
  obtain ⟨h,hrh,hhbeta,hh1,hmu⟩ := exists_scarce_parameters (d+1) (by omega) hrho hbeta hzeta
  obtain ⟨D⟩ := exists_scarce_family_at_mass d hd G ⟨h,(hrho.trans hrh).le,hh1.le⟩ rho g
    (hrho.trans hrh) hrho hrh hhbeta hbeta hg
  refine ⟨h,hrh,hhbeta,hh1,D,?_⟩
  intro a ha
  obtain ⟨phi,hphi,Q,mu,hQ,hmuTarget,hmuHi,_hQhi,hQlim,_hLlim,hmulim⟩ :=
    (D.actual_limits hd hrho hrh hmu a ha).2.2
  exact ⟨phi,hphi,Q,mu,hQ,hmuTarget,hmuHi,hQlim,hmulim⟩

end FCAppendix.Bayes.ExclusiveConstruction
