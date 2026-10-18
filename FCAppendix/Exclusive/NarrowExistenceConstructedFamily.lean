import FCAppendix.Exclusive.NarrowExistenceCanonicalFamily
import FCAppendix.Exclusive.NarrowExistenceCanonicalStatistics
import FCAppendix.Exclusive.ExistenceSourceClassification
import FCAppendix.Exclusive.FiniteMarketSequence

noncomputable section
namespace FCAppendix.Bayes.ExclusiveConstruction
open MeasureTheory ProbabilityTheory Game Exclusive Set Filter Topology
open Exclusive.Narrow.Existence Completion.Exclusive Exclusive.Construction

structure NarrowEquilibriumFamily (d : ℕ) (G : Schedule (d+1)) (g rho : ℝ)
    (h : unitInterval) (H eps : ℝ) (nu : Measure (ValueBand eps)) [IsProbabilityMeasure nu] where
  H_pos : 0 < H
  eps_pos : 0 < eps
  eps_lt_one : eps < 1
  high_mass : (narrowPrimitive h H nu).real (bandHighSet eps H) = (h:ℝ)
  high_atomless : NullSingletonClass ((narrowPrimitive h H nu).restrict (bandHighSet eps H))
  M : ℕ → ℕ
  C : ℕ → ℕ
  population_positive : ∀ t, 0 < M t
  capacity_positive : ∀ t, 0 < C t
  population_grows : Tendsto M atTop atTop
  density : Tendsto (fun t => (C t:ℝ)/(M t:ℝ)) atTop (𝓝 rho)
  game : ∀ a : UserTariff, a.Allowed → ∀ t, FiniteGame (M t) (d+1) (C t) unitInterval
  posterior : ∀ a ha t, PosteriorSystem (game a ha t)
  bid : ∀ a : UserTariff, a.Allowed → ℕ → ℝ → ℝ
  common_values : ∀ a ha t, (game a ha t).F = narrowPrimitive h H nu
  common_base : ∀ a ha t, (game a ha t).G = G
  common_fee : ∀ a ha t, (game a ha t).g = g
  measurable_bid : ∀ a ha t, Measurable (bid a ha t)
  bid_strictMonoOn : ∀ a ha t, StrictMonoOn (bid a ha t) (bandHighSet eps H)
  positive_bid : ∀ a ha t v, 0 < bid a ha t v
  pure : ∀ a ha t v, (game a ha t).σ v =
    Measure.dirac (pureAction (d+1) (bandHighSet eps H) (bid a ha t) v)
  users : ∀ a ha t, ExclusiveTariffUsersOptimal (game a ha t) a
  proposers : ∀ a ha t, ExclusivePosteriorOptimalAE (game a ha t) (posterior a ha t)
  symmetric : ∀ a ha t, SymmetricProposersOnPath (game a ha t)
  equivariant : ∀ a ha t, PolicyLawEquivariant (game a ha t)
  broadcast : ∀ a ha t, ExclusiveBroadcastOn (game a ha t) (bandHighSet eps H)
  finite_atomless : ∀ a ha t, NullSingletonClass
    (submittedBidLawOn (game a ha t) (bandHighSet eps H))
  eta : ℝ
  l : ℝ
  u : ℝ
  priceLo : ℝ
  priceHi : ℝ
  eta_mem : eta ∈ Ioo (0:ℝ) 1
  exposure_bounds : 0 < l ∧ l < u ∧ u < 1
  price_bounds : 0 < priceLo ∧ priceLo ≤ priceHi
  source_limits : ∀ a ha, ∃ beta lam p,
    ExistingSourceFamilyConclusion (game a ha) (narrowPrimitive h H nu) (bandHighSet eps H) a G g rho
      (H*sourceBid d a h rho*(1-eta)) (H*sourceBid d a h rho*(1+eta))
      l u (H*priceLo) (H*priceHi) beta lam p

theorem exists_constructed_narrow_family (d : ℕ) (hd : 1 ≤ d) (G : Schedule (d+1))
    (h : unitInterval) (rho g : ℝ) (hh : 0 < (h:ℝ)) (hrho : 0 < rho)
    (hrh : rho < (h:ℝ)) (hg : 0 ≤ g) :
    ∃ Q : NarrowExistenceParameters d G h rho g,
      ∀ (nu : Measure (ValueBand Q.candidate.eps)) [IsProbabilityMeasure nu] [NullSingletonClass nu],
        Nonempty (NarrowEquilibriumFamily d G g rho h Q.H Q.candidate.eps nu) := by
  classical
  obtain ⟨eta,epsClass,l,u,priceLo,priceHi,heta,_hetaOne,hepsClass,hl,hlu,hu,hpriceLo,
    hpriceHi,hClass⟩ := uniform_source_classification_capped d hd G hh hrho hrh h.property.2 zero_lt_one
  obtain ⟨dc,hdc,hlog⟩ := exists_log_band_inside_relative heta.1
  obtain ⟨Q,hQd,hQe,_hQt⟩ := exists_narrow_existence_parameters_bounded d hd G h rho g
    hh hrho hrh hg dc (epsClass/2) 1 hdc (by linarith [hepsClass.1]) zero_lt_one
  refine ⟨Q,?_⟩
  intro nu _ _
  let U := Q.candidate
  let H := Q.H
  let F := narrowPrimitive h H nu
  let E := bandHighSet U.eps H
  have hH : 0 < H := Q.H_pos
  letI : IsProbabilityMeasure F := narrowPrimitive_probability h H nu
  letI : NullSingletonClass (F.restrict E) :=
    narrowPrimitive_restrict_high_atomless h U.eps_lt_one hH nu
  have hmass : F.real E = (h:ℝ) := narrowPrimitive_high_mass h U.eps_lt_one hH nu
  have hUec : U.eps ≤ epsClass := hQe.trans (by linarith [hepsClass.1])
  have hbase : g/H < epsClass := Q.base.2.trans_lt (hQe.trans_lt (by linarith [hepsClass.1]))
  have htail : ∀ᶠ t in atTop, Q.M0 ≤ t+1 ∧
      |(marketCapacity rho t:ℝ)/((t:ℝ)+1)-rho| < U.eta := by
    filter_upwards [eventually_ge_atTop Q.M0,
      (marketDensity_tendsto hrho.le).eventually (Metric.ball_mem_nhds rho U.eta_pos)] with t ht hC
    refine ⟨by omega,?_⟩
    simpa only [Metric.mem_ball,Real.dist_eq,marketPopulation,Nat.cast_add,Nat.cast_one] using hC
  obtain ⟨T,hT⟩ := eventually_atTop.mp htail
  let M := fun t : ℕ => t+T+1
  let C := fun t : ℕ => marketCapacity rho (t+T)
  have hrow (t : ℕ) := hT (t+T) (by omega)
  have hM : Tendsto M atTop atTop := (tendsto_add_atTop_nat 1).comp (tendsto_add_atTop_nat T)
  have hDensity : Tendsto (fun t => (C t:ℝ)/(M t:ℝ)) atTop (𝓝 rho) :=
    (marketDensity_tendsto hrho.le).comp (tendsto_add_atTop_nat T)
  have hMU (t : ℕ) : Q.M0 ≤ t+T+1 := (hrow t).1
  have hCU (t : ℕ) : |(C t:ℝ)/(((t+T:ℕ):ℝ)+1)-rho| < U.eta := (hrow t).2
  have hCpositive (t : ℕ) : 0 < C t := U.capacity_pos (C t) (Q.candidate_threshold.trans (hMU t)) (hCU t)
  have hp0 : 0 < rho/(h:ℝ) := div_pos hrho hh
  have hp1 : rho/(h:ℝ) < 1 := (div_lt_one hh).mpr hrh
  have hexists (a : UserTariff) (ha : a.Allowed) (t : ℕ) :
      ∃ Γ : FiniteGame (M t) (d+1) (C t) unitInterval, ∃ B : PosteriorSystem Γ, ∃ bid : ℝ → ℝ,
        Γ.F=F ∧ Γ.G=G ∧ Γ.g=g ∧ Measurable bid ∧ StrictMonoOn bid E ∧ (∀ v, 0 < bid v) ∧
        (∀ v, Γ.σ v = Measure.dirac (pureAction (d+1) E bid v)) ∧
        ExclusiveTariffUsersOptimal Γ a ∧ ExclusivePosteriorOptimalAE Γ B ∧
        SymmetricProposersOnPath Γ ∧ PolicyLawEquivariant Γ ∧ ExclusiveBroadcastOn Γ E ∧
        NullSingletonClass (submittedBidLawOn Γ E) ∧
        (∀ᵐ v ∂Γ.F, ∀ᵐ x ∂Γ.σ v, v ∈ E →
          x.bid ∈ Ioo (H*sourceBid d a h rho*(1-eta)) (H*sourceBid d a h rho*(1+eta))) ∧
        RawBandContinuation Γ B (H*sourceBid d a h rho*(1-eta))
          (H*sourceBid d a h rho*(1+eta)) := by
    obtain ⟨beta,hmono,_hpos,_hatom,husers,hbroadcast,hsym,hequiv,B,hpost,hraw⟩ :=
      exists_native_narrow_equilibrium hd G h rho g hh hrho hrh hg Q (C t) (hMU t) (hCU t) nu a ha
    let scale := H*referenceBidScale d a (rho/(h:ℝ))
    have hs : 0 < scale := mul_pos hH (referenceBidScale_pos d hd a ha _ hp0.le hp1)
    let bid := extendedSourceBid U.eps U.eps_pos.le H scale beta.val
    let Γ := narrowCanonicalGame (M t) d (C t) hd (hCpositive t) h U.eps_pos.le H scale
      beta.val beta.val.continuous nu (Schedule.once (d+1)) G g hg
    have hrelative : ∀ v, Real.exp (beta.val v) ∈ Ioo (1-eta) (1+eta) := fun v =>
      hlog _ ⟨(neg_le_neg hQd).trans (beta.property v).1,(beta.property v).2.trans hQd⟩
    have hscaleSource : scale = H*sourceBid d a h rho := rfl
    refine ⟨Γ,B,bid,rfl,rfl,rfl,?_,?_,?_,?_,husers,hpost,hsym,hequiv,hbroadcast,?_,?_,?_⟩
    · exact (continuous_extendedSourceBid U.eps U.eps_pos.le H scale beta.val beta.val.continuous).measurable
    · exact extendedSourceBid_strictMonoOn_high U.eps_pos.le hH hs beta.val hmono
    · exact extendedSourceBid_pos U.eps_pos.le H hs beta.val
    · exact fun _ => rfl
    · exact narrowCanonicalGame_active_bids_atomless hd (hCpositive t) h U.eps_pos.le U.eps_lt_one
        hH hs beta.val beta.val.continuous hmono nu (Schedule.once (d+1)) G g hg
    · simpa only [Γ,E,← hscaleSource] using narrowCanonicalGame_relative_band hd (hCpositive t)
        h U.eps_pos.le H scale hs beta.val beta.val.continuous nu (Schedule.once (d+1)) G g hg eta hrelative
    · exact hraw _ _
  choose Γ B bid hF hG hfee hmeas hmono hpos hpure husers hproposers hsym hequiv hbroadcast
    hatom hband hcanonical using hexists
  have hvalues : ∀ᵐ v ∂F.restrict E, v ∈ Icc (H*(1-epsClass)) (H*(1+epsClass)) := by
    filter_upwards [ae_restrict_mem (μ := F) (show MeasurableSet E from measurableSet_Icc)] with v hv
    have hv' : v ∈ Icc (H*(1-U.eps)) (H*(1+U.eps)) := hv
    constructor <;> nlinarith [hv'.1,hv'.2,mul_nonneg hH.le (sub_nonneg.mpr hUec)]
  have hlimits (a : UserTariff) (ha : a.Allowed) :=
    hClass H g hH hg hbase a ha (Γ a ha) (B a ha) F E measurableSet_Icc hmass
      (hF a ha) (hG a ha) (hfee a ha) hvalues
      (Eventually.of_forall (husers a ha)) (Eventually.of_forall (hbroadcast a ha))
      (Eventually.of_forall (hband a ha)) (Eventually.of_forall (hcanonical a ha)) hM hDensity
  exact ⟨{
    H_pos := hH, eps_pos := U.eps_pos, eps_lt_one := U.eps_lt_one,
    high_mass := hmass, high_atomless := inferInstance,
    M := M, C := C, population_positive := fun t => by dsimp [M]; omega,
    capacity_positive := hCpositive, population_grows := hM, density := hDensity,
    game := Γ, posterior := B, bid := bid, common_values := hF, common_base := hG, common_fee := hfee,
    measurable_bid := hmeas, bid_strictMonoOn := hmono, positive_bid := hpos, pure := hpure,
    users := husers, proposers := hproposers, symmetric := hsym, equivariant := hequiv,
    broadcast := hbroadcast, finite_atomless := hatom,
    eta := eta, l := l, u := u, priceLo := priceLo, priceHi := priceHi, eta_mem := heta,
    exposure_bounds := ⟨hl,hlu,hu⟩, price_bounds := ⟨hpriceLo,hpriceHi⟩, source_limits := hlimits }⟩

end FCAppendix.Bayes.ExclusiveConstruction
