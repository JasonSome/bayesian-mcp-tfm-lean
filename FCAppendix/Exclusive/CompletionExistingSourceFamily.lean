import FCAppendix.Exclusive.CompletionSourceFamily

noncomputable section
namespace FCAppendix.Completion.Exclusive
open MeasureTheory ProbabilityTheory Filter Topology Set
open FCAppendix Game Bayes Exclusive Exclusive.Narrow Exclusive.Narrow.Finite
open Bayes.ExclusiveNarrow
open scoped BigOperators ProbabilityTheory

structure RawBandContinuation {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ) (lo hi : ℝ) : Prop where
  common : ∀ j ℓ, FeasibleObservedList j ℓ →
    (∀ i : VisibleUser ℓ, visibleBid ℓ i ∈ Icc lo hi) →
    ∀ᵐ z ∂B.posterior j ℓ, ∀ l, observe (drawsRealization z) l = ℓ
  symmetric : ∀ j ℓ, FeasibleObservedList j ℓ →
    (∀ i : VisibleUser ℓ, visibleBid ℓ i ∈ Icc lo hi) →
    SymmetricAtList Γ ℓ (seedLottery Γ j ℓ)
  optimal : ∀ j ℓ, FeasibleObservedList j ℓ →
    (∀ i : VisibleUser ℓ, visibleBid ℓ i ∈ Icc lo hi) →
    ∀ᵐ s ∂Γ.seedLaw, FCAppendix.Finite.Optimal c
      (exclusiveReceipts (posteriorCountBelief Γ B j ℓ) ℓ) (Γ.policy j ℓ s).val

theorem rawBandContinuation_iff {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ) (P : Corridor n m c) :
    RawBandContinuation Γ B P.lower P.upper ↔ BroadcastCorridorContinuation Γ B P := by
  constructor
  · intro h; exact ⟨h.common,h.symmetric,h.optimal⟩
  · intro h; exact ⟨h.common,h.symmetric,h.optimal⟩

theorem RawBandContinuation.toCorridor {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {Γ : FiniteGame m n c Seed} {B : PosteriorSystem Γ} {lo hi : ℝ}
    (h : RawBandContinuation Γ B lo hi) (P : Corridor n m c)
    (hl : P.lower = lo) (hu : P.upper = hi) : BroadcastCorridorContinuation Γ B P := by
  apply (rawBandContinuation_iff Γ B P).mp
  simpa only [hl,hu] using h

theorem typeOutcome_mass_row_congr {d : ℕ} {M C : ℕ → ℕ}
    {Seed : Type*} [MeasurableSpace Seed]
    (Γ : ∀ t, FiniteGame (M t) (d+1) (C t) Seed)
    {s t : ℕ} (hst : s = t) (i : Fin (M s)) (j : Fin (M t))
    (hij : i.val = j.val) (v : ℝ) (k : Fin (d+1+1)) :
    (typeOutcome (Γ s) i v).mass k = (typeOutcome (Γ t) j v).mass k := by
  subst t
  have he : i = j := Fin.ext hij
  subst j
  rfl

def fillTailIdentity (M : ℕ → ℕ) (T0 T : ℕ)
    (hpop : ∀ t, 0 < M (t+T0)) (I : ∀ t, Fin (M (t+T))) (r : ℕ) : Fin (M (r+T0)) :=
  if hr : T ≤ r then
    Fin.cast (congrArg M (show (r-T+T0)+T = r+T0 by omega)) (I (r-T+T0))
  else ⟨0,hpop r⟩

theorem restore_count_limits_all_tails {d : ℕ} {M C : ℕ → ℕ}
    {Seed : Type*} [MeasurableSpace Seed]
    (Γ : ∀ t, FiniteGame (M t) (d+1) (C t) Seed) (mu : Measure ℝ)
    (T0 : ℕ) (hpop : ∀ t, 0 < M (t+T0)) (pInf : ℝ → ℝ)
    (hc : ∀ᵐ v ∂mu, ∀ I : ∀ t, Fin (M (t+T0)), ∀ j : Fin (d+1+1),
      Tendsto (fun t => (typeOutcome (Γ (t+T0)) (I t) v).mass j) atTop
        (𝓝 (PayOnce.ManyProposers.binomialMass (d+1) (pInf v) j.val))) :
    ∀ᵐ v ∂mu, ∀ T : ℕ, ∀ I : ∀ t, Fin (M (t+T)), ∀ j : Fin (d+1+1),
      Tendsto (fun t => (typeOutcome (Γ (t+T)) (I t) v).mass j) atTop
        (𝓝 (PayOnce.ManyProposers.binomialMass (d+1) (pInf v) j.val)) := by
  filter_upwards [hc] with v hv
  intro T I j
  let J := fillTailIdentity M T0 T hpop I
  have hlim := (hv J j).comp (tendsto_add_atTop_nat T)
  apply full_sequence_from_tail
    (fun t => (typeOutcome (Γ (t+T)) (I t) v).mass j) _ T0
  convert hlim using 1
  funext t
  apply typeOutcome_mass_row_congr Γ (show (t+T0)+T = (t+T)+T0 by omega)
    (I (t+T0)) (J (t+T)) _ v j
  dsimp only [J,fillTailIdentity]
  rw [dif_pos (show T ≤ t+T by omega)]
  change (I (t+T0)).val = (I ((t+T)-T+T0)).val
  rw [Nat.add_sub_cancel]

structure ExistingSourceFamilyConclusion {d : ℕ} {M C : ℕ → ℕ}
    {Seed : Type*} [MeasurableSpace Seed]
    (Γ : ∀ t, FiniteGame (M t) (d+1) (C t) Seed) (F : Measure ℝ) (E : Set ℝ)
    (a : UserTariff) (G : Schedule (d+1))
    (g rho lo hi l u L U : ℝ) (beta : ℕ → ℝ → ℝ) (lam : ℝ) (p : ℝ → ℝ) : Prop where
  representatives : ∀ t, Monotone (beta t) ∧ Measurable (beta t)
  band : ∀ t v, beta t v ∈ Icc lo hi
  pure : ∀ᶠ t in atTop, ∀ᵐ v ∂F.restrict E, ∀ᵐ x ∂(Γ t).σ v, x.bid = beta t v
  strict_order : ∀ᶠ t in atTop, ∃ S : Set ℝ, (F.restrict E) Sᶜ = 0 ∧ StrictMonoOn (beta t) S
  atomless : ∀ᶠ t in atTop, ∀ b : ℝ,
    (Measure.map (fun x : ℝ × JointAction (d+1) => x.2.bid)
      ((F.restrict E) ⊗ₘ (Γ t).σ)) {b} = 0
  conditional_bids : ∀ᶠ t in atTop, ∀ᵐ v ∂F.restrict E,
    Measure.map (fun x : JointAction (d+1) => x.bid) ((Γ t).σ v) = Measure.dirac (beta t v)
  price : lam ∈ Icc L U
  solution : LocalExposureSolution (F.restrict E) (Icc l u)
    (fTariff d a) (baseMarginalCost d G) g rho lam p
  unique : ∀ tau ∈ Icc L U, ∀ q : ℝ → ℝ,
    LocalExposureSolution (F.restrict E) (Icc l u)
      (fTariff d a) (baseMarginalCost d G) g rho tau q → tau = lam ∧ q =ᵐ[F.restrict E] p
  bids : ∀ᵐ v ∂F.restrict E,
    Tendsto (fun t => beta t v) atTop (𝓝 (referenceBid d lam (p v)))
  counts : ∀ᵐ v ∂F.restrict E, ∀ T : ℕ, ∀ I : ∀ t, Fin (M (t+T)), ∀ j : Fin (d+1+1),
    Tendsto (fun t => (typeOutcome (Γ (t+T)) (I t) v).mass j) atTop
      (𝓝 (PayOnce.ManyProposers.binomialMass (d+1) (p v) j.val))
  once_specialization : a = .unique → G = Schedule.once (d+1) →
    ∀ᵐ v ∂F.restrict E,
      Tendsto (fun t => beta t v) atTop (𝓝 (v-g)) ∧ 0 < v-g ∧
        p v = 1-(lam/(v-g))^(rate (d+1))

def ClassifiesSourceBand (d : ℕ) (G : Schedule (d+1))
    (h rho eta eps H g l u L U : ℝ) : Prop :=
  ∀ a : UserTariff, a.Allowed →
  ∀ {Seed : Type*} [MeasurableSpace Seed] {M C : ℕ → ℕ}
    (Γ : ∀ t, FiniteGame (M t) (d+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F]
    (E : Set ℝ), MeasurableSet E → ∀ [NullSingletonClass (F.restrict E)],
    F.real E = h → (∀ t, (Γ t).F = F) → (∀ t, (Γ t).G = G) → (∀ t, (Γ t).g = g) →
    (∀ᵐ v ∂F.restrict E, v ∈ Icc (H*(1-eps)) (H*(1+eps))) →
    (∀ᶠ t in atTop, ExclusiveTariffUsersOptimal (Γ t) a) →
    (∀ᶠ t in atTop, ExclusiveBroadcastOn (Γ t) E) →
    (∀ᶠ t in atTop, ∀ᵐ v ∂(Γ t).F, ∀ᵐ x ∂(Γ t).σ v,
      v ∈ E → x.bid ∈ Ioo (H*sourceBid d a h rho*(1-eta)) (H*sourceBid d a h rho*(1+eta))) →
    (∀ᶠ t in atTop, RawBandContinuation (Γ t) (B t)
      (H*sourceBid d a h rho*(1-eta)) (H*sourceBid d a h rho*(1+eta))) →
    Tendsto M atTop atTop → Tendsto (fun t => (C t:ℝ)/M t) atTop (𝓝 rho) →
    ∃ beta lam p, ExistingSourceFamilyConclusion Γ F E a G g rho
      (H*sourceBid d a h rho*(1-eta)) (H*sourceBid d a h rho*(1+eta))
      l u (H*L) (H*U) beta lam p

theorem once_exposure_of_reference {d : ℕ} (hd : 1 ≤ d) {lam p v g : ℝ}
    (hlam : 0 < lam) (hp : p < 1) (hb : referenceBid d lam p = v-g) :
    0 < v-g ∧ p = 1-(lam/(v-g))^(rate (d+1)) := by
  have hq : 0 < 1-p := sub_pos.mpr hp
  have hqd : 0 < (1-p)^d := pow_pos hq d
  have hbpos : 0 < v-g := by
    rw [← hb]
    exact div_pos hlam hqd
  have hprod : (v-g)*(1-p)^d = lam := by
    have he : lam/(1-p)^d = v-g := hb
    exact ((div_eq_iff hqd.ne').mp he).symm
  have hratio : lam/(v-g) = (1-p)^d := by
    apply (div_eq_iff hbpos.ne').mpr
    nlinarith only [hprod]
  have hr : (d:ℝ)*rate (d+1) = 1 := by
    have hh := rate_mul (d+1) (by omega)
    simpa only [Nat.add_sub_cancel,mul_comm] using hh
  refine ⟨hbpos,?_⟩
  rw [hratio,← Real.rpow_natCast,← Real.rpow_mul hq.le,hr,Real.rpow_one]
  ring

theorem classify_source_band (d : ℕ) (hd : 1 ≤ d) (G : Schedule (d+1))
    {h rho eta eps H g l u L U delta k K : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) (hrho : 0 < rho)
    (heta : eta ∈ Ioo (0:ℝ) 1) (heps : eps ∈ Ioo (0:ℝ) 1)
    (hH : 0 < H) (hl : 0 < l) (hlu : l ≤ u) (hu : u < 1) (hL : 0 < L)
    (hdelta : 0 < delta) (hk : 0 < k) (hK : 0 ≤ K)
    (hcenter : ∀ a : UserTariff, a.Allowed → 0 < sourceBid d a h rho)
    (hlocal : ∀ a : UserTariff, a.Allowed → ∀ cap : ℝ, |cap-rho| < delta →
      ScalarCorridor d (H*sourceBid d a h rho*(1-eta))
        (H*sourceBid d a h rho*(1+eta)) h cap l u (H*L) (H*U) ∧ spreadRatio d eta cap < 1)
    (hslope : ∀ a : UserTariff, a.Allowed → ∀ lam ∈ Icc (H*L) (H*U), ∀ p ∈ Icc l u,
      lam*dfTariff d a p+g*deriv (baseMarginalCost d G) p ∈ Icc k K) :
    ClassifiesSourceBand d G h rho eta eps H g l u L U := by
  classical
  unfold ClassifiesSourceBand
  intro a ha Seed _ M C Γ B F _ E hE _ hmass hF hG hg hvalues husers hclass hband hcanonical hM hcap
  let X := H*sourceBid d a h rho
  let lo := X*(1-eta)
  let hi := X*(1+eta)
  have hX : 0 < X := mul_pos hH (hcenter a ha)
  have hlo : 0 < lo := mul_pos hX (sub_pos.mpr heta.2)
  have hlohi : lo < hi := by dsimp only [lo,hi]; nlinarith [mul_pos hX heta.1]
  have hlocalTail : ∀ᶠ t in atTop,
      ScalarCorridor d lo hi h ((C t:ℝ)/M t) l u (H*L) (H*U) ∧
        spreadRatio d eta ((C t:ℝ)/M t) < 1 := by
    filter_upwards [hcap.eventually (Metric.ball_mem_nhds rho hdelta)] with t ht
    exact hlocal a ha _ (by simpa only [Metric.mem_ball,Real.dist_eq] using ht)
  have hgood : ∀ᶠ t in atTop,
      (0 < M t ∧ 0 < C t ∧ C t < M t) ∧
      (ScalarCorridor d lo hi h ((C t:ℝ)/M t) l u (H*L) (H*U) ∧
        spreadRatio d eta ((C t:ℝ)/M t) < 1) ∧
      ExclusiveTariffUsersOptimal (Γ t) a ∧ ExclusiveBroadcastOn (Γ t) E ∧
      (∀ᵐ v ∂(Γ t).F, ∀ᵐ x ∂(Γ t).σ v, v ∈ E → x.bid ∈ Ioo lo hi) ∧
      RawBandContinuation (Γ t) (B t) lo hi := by
    filter_upwards [hM.eventually_gt_atTop 0,hcap.eventually (eventually_gt_nhds hrho),
      hlocalTail,husers,hclass,hband,hcanonical] with t hm hc hs huser hcl hb hcan
    have hmR : (0:ℝ) < M t := Nat.cast_pos.mpr hm
    have hcR : (0:ℝ) < C t := by
      simpa only [zero_mul] using (lt_div_iff₀ hmR).mp hc
    have hcmR : (C t:ℝ) < M t :=
      (div_lt_one hmR).mp (hs.1.cap_lt_mass.trans_le hh1)
    exact ⟨⟨hm,Nat.cast_pos.mp hcR,by exact_mod_cast hcmR⟩,hs,huser,hcl,hb,hcan⟩
  obtain ⟨T0,hT0⟩ := eventually_atTop.mp hgood
  have ht (t : ℕ) := hT0 (t+T0) (by omega)
  let Γtail := fun t => Γ (t+T0)
  let Btail := fun t => B (t+T0)
  let P : ∀ t, Corridor (d+1) (M (t+T0)) (C (t+T0)) := fun t =>
    sourceCorridor d _ _ hd (ht t).1.1 (ht t).1.2.1 X eta hX heta (ht t).2.1.2
  have hPl (t : ℕ) : (P t).lower = lo := rfl
  have hPu (t : ℕ) : (P t).upper = hi := rfl
  have hplay (t : ℕ) : CorridorPlay (Γtail t) (P t) :=
    corridorPlay_of_class _ _ E hE (ht t).2.2.2.1 (ht t).2.2.2.2.1
  have hcont (t : ℕ) : BroadcastCorridorContinuation (Γtail t) (Btail t) (P t) :=
    ((ht t).2.2.2.2.2).toCorridor (P t) rfl rfl
  have hfullband (t : ℕ) : ∀ᵐ v ∂(Γtail t).F, ∀ᵐ x ∂(Γtail t).σ v,
      v ∈ E → x.routeCount = d+1 ∧ x.bid ∈ Ioo lo hi := by
    have hc := Measure.ae_ae_of_ae_compProd (ht t).2.2.2.1
    filter_upwards [hc,(ht t).2.2.2.2.1] with v hv hb
    filter_upwards [hv,hb] with x hx hxb hvE
    exact ⟨(hx.1 hvE).2,hxb hvE⟩
  have hval : ∀ᵐ v ∂F.restrict E, |v| ≤ H*(1+eps) := by
    filter_upwards [hvalues] with v hv
    have hv0 : 0 < v := (mul_pos hH (sub_pos.mpr heps.2)).trans_le hv.1
    simpa only [abs_of_pos hv0] using hv.2
  obtain ⟨bt,lam,p,hrep,hbb,hstrict,hatoms,hprice,hsolution,hbid,hcount⟩ :=
    canonical_narrow_family_limit_with_price Γtail P hplay Btail hcont a ha
      (fun t => (ht t).2.2.1) hd F E hE (fun t => hF (t+T0)) G
      (fun t => hG (t+T0)) (fun t => hg (t+T0)) hh hh1 hmass hlo hlohi hPl hPu
      (fun t => (ht t).2.2.2.1) hfullband (fun t => (ht t).1.2.2) hval
      hl hlu hu hk hK (fun t => (ht t).2.1.1) (hslope a ha)
      (hM.comp (tendsto_add_atTop_nat T0)) (hcap.comp (tendsto_add_atTop_nat T0))
  let beta := extendPureTail T0 lo bt
  have hbeta (t : ℕ) : Monotone (beta t) ∧ Measurable (beta t) := by
    by_cases htt : T0 ≤ t
    · simpa only [beta,extendPureTail,if_pos htt] using
        (show Monotone (bt (t-T0)) ∧ Measurable (bt (t-T0)) from
          ⟨(hrep (t-T0)).1,(hrep (t-T0)).2.1⟩)
    · simp only [beta,extendPureTail,if_neg htt]
      exact ⟨monotone_const,measurable_const⟩
  have hbetaBand (t : ℕ) (v : ℝ) : beta t v ∈ Icc lo hi := by
    by_cases htt : T0 ≤ t
    · simpa only [beta,extendPureTail,if_pos htt] using hbb (t-T0) v
    · simp only [beta,extendPureTail,if_neg htt]
      exact ⟨le_rfl,hlohi.le⟩
  have hpure : ∀ᶠ t in atTop, ∀ᵐ v ∂F.restrict E, ∀ᵐ x ∂(Γ t).σ v, x.bid = beta t v := by
    filter_upwards [eventually_ge_atTop T0] with t htt
    have hh := (hrep (t-T0)).2.2
    have hidx : t-T0+T0 = t := by omega
    dsimp only [Γtail] at hh
    rw [hidx] at hh
    simpa only [beta,extendPureTail,if_pos htt] using hh
  have horder : ∀ᶠ t in atTop, ∃ S : Set ℝ, (F.restrict E) Sᶜ = 0 ∧ StrictMonoOn (beta t) S := by
    filter_upwards [eventually_ge_atTop T0] with t htt
    simpa only [beta,extendPureTail,if_pos htt] using hstrict (t-T0)
  have hatom : ∀ᶠ t in atTop, ∀ b : ℝ,
      (Measure.map (fun x : ℝ × JointAction (d+1) => x.2.bid)
        ((F.restrict E) ⊗ₘ (Γ t).σ)) {b} = 0 := by
    filter_upwards [eventually_ge_atTop T0] with t htt
    have hh := hatoms (t-T0)
    have hidx : t-T0+T0 = t := by omega
    dsimp only [Γtail] at hh
    rw [hidx] at hh
    exact hh
  have hbids : ∀ᵐ v ∂F.restrict E,
      Tendsto (fun t => beta t v) atTop (𝓝 (referenceBid d lam (p v))) := by
    apply ae_full_sequence_from_tail beta (fun v => referenceBid d lam (p v)) T0
    simpa only [beta,extendPureTail_shift] using hbid
  have hmu : (F.restrict E).real univ = h := by simpa using hmass
  have hmu0 : F.restrict E ≠ 0 := by
    intro he
    rw [he] at hmu
    have hh0 : h = 0 := by simpa using hmu.symm
    exact hh.ne' hh0
  have hmono : ∀ s ∈ Icc (H*L) (H*U),
      StrictMonoOn (fun x => s*fTariff d a x+g*baseMarginalCost d G x) (Icc l u) := by
    intro s hs x hx y hy hxy
    have hbound := slope_bounds_of_derivative_bounds
      (fun z hz => hasDerivAt_exposureEquation d hd a G g s z (hz.2.trans_lt hu))
      (hslope a ha s hs) x hx y hy hxy.le
    have hpos := mul_pos hk (sub_pos.mpr hxy)
    exact sub_pos.mp (hpos.trans_le hbound.1)
  have hunique : ∀ tau ∈ Icc (H*L) (H*U), ∀ q : ℝ → ℝ,
      LocalExposureSolution (F.restrict E) (Icc l u) (fTariff d a)
        (baseMarginalCost d G) g rho tau q → tau = lam ∧ q =ᵐ[F.restrict E] p := by
    intro tau htau q hq
    exact local_capacity_uniqueness hmu0 htau hprice
      (fun x hx => (fTariff_pos_and_derivative_pos d hd a ha (hl.le.trans hx.1) (hx.2.trans_lt hu)).1)
      hmono hq hsolution
  refine ⟨beta,lam,p,⟨hbeta,hbetaBand,hpure,horder,hatom,?_,hprice,hsolution,hunique,hbids,?_,?_⟩⟩
  · filter_upwards [hpure] with t htt
    have hp' : ∀ᵐ v ∂(Γ t).F.restrict E, ∀ᵐ x ∂(Γ t).σ v, x.bid = beta t v := by
      simpa only [hF t] using htt
    have hc := conditional_bidLaw_dirac (Γ t) E (beta t) hp'
    simpa only [hF t] using hc
  · exact restore_count_limits_all_tails Γ (F.restrict E) T0 (fun t => (ht t).1.1) p hcount
  · intro haunique hGonce
    have hs : LocalExposureSolution (F.restrict E) (Icc l u) (fTariff d .unique)
        (baseMarginalCost d (Schedule.once (d+1))) g rho lam p := by
      simpa only [haunique,hGonce] using hsolution
    have he := unique_once_bid_limit hu hs
    have hlam : 0 < lam := (mul_pos hH hL).trans_le hprice.1
    filter_upwards [he,hbids,hs.mem] with v hv hlim hvm
    have hx := once_exposure_of_reference hd hlam (hvm.2.trans_lt hu) hv
    exact ⟨by simpa only [hv] using hlim,hx⟩

theorem uniform_source_classification (d : ℕ) (hd : 1 ≤ d) (G : Schedule (d+1))
    {h rho : ℝ} (hh : 0 < h) (hrho : 0 < rho) (hrhoh : rho < h) (hh1 : h ≤ 1) :
    ∃ eta eps l u L U : ℝ,
      eta ∈ Ioo (0:ℝ) 1 ∧ eps ∈ Ioo (0:ℝ) 1 ∧ 0 < l ∧ l < u ∧ u < 1 ∧
      0 < L ∧ L ≤ U ∧
      ∀ H g : ℝ, 0 < H → 0 ≤ g → g/H < eps →
        ClassifiesSourceBand d G h rho eta eps H g l u L U := by
  obtain ⟨eta,delta,l,u,L,U,eps0,heta,hdelta,hl,hlu,hu,hL,hLU,heps0,hdata⟩ :=
    source_family_scalar_inputs d hd G hh hrho hrhoh hh1
  let eps := min eps0 (1/2)
  have heps : eps ∈ Ioo (0:ℝ) 1 := by
    refine ⟨lt_min heps0 (by norm_num), ?_⟩
    exact (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨eta,eps,l,u,L,U,heta,heps,hl,hlu,hu,hL,hLU,?_⟩
  intro H g hH hg hsmall
  obtain ⟨k,K,hk,hK,hinputs⟩ := hdata H g hH hg (hsmall.trans_le (min_le_left _ _))
  have hcenter (a : UserTariff) (ha : a.Allowed) : 0 < sourceBid d a h rho := by
    have hp0 : 0 ≤ rho/h := (div_pos hrho hh).le
    have hp1 : rho/h < 1 := (div_lt_one hh).mpr hrhoh
    have hf := (fTariff_pos_and_derivative_pos d hd a ha hp0 hp1).1
    have hq : 0 < sourceQ h rho := sub_pos.mpr hp1
    exact div_pos (one_div_pos.mpr hf) (pow_pos hq d)
  exact classify_source_band d hd G hh hh1 hrho heta heps hH hl hlu.le hu hL hdelta hk hK
    hcenter (fun a ha => (hinputs a ha).1) (fun a ha => (hinputs a ha).2)

theorem fixed_base_source_classification (d : ℕ) (hd : 1 ≤ d) (G : Schedule (d+1))
    {h rho g : ℝ} (hh : 0 < h) (hrho : 0 < rho) (hrhoh : rho < h) (hh1 : h ≤ 1) (hg : 0 ≤ g) :
    ∃ eta eps l u L U H : ℝ,
      eta ∈ Ioo (0:ℝ) 1 ∧ eps ∈ Ioo (0:ℝ) 1 ∧ 0 < l ∧ l < u ∧ u < 1 ∧
      0 < L ∧ L ≤ U ∧ 0 < H ∧ g/H < eps ∧
      ClassifiesSourceBand d G h rho eta eps H g l u L U := by
  obtain ⟨eta,eps,l,u,L,U,heta,heps,hl,hlu,hu,hL,hLU,hfamily⟩ :=
    uniform_source_classification d hd G hh hrho hrhoh hh1
  obtain ⟨H,hH,hsmall⟩ := large_scale_for_fixed_base hg heps.1
  exact ⟨eta,eps,l,u,L,U,H,heta,heps,hl,hlu,hu,hL,hLU,hH,hsmall,hfamily H g hH hg hsmall⟩

theorem fixed_once_base_source_classification (d : ℕ) (hd : 1 ≤ d)
    {h rho g : ℝ} (hh : 0 < h) (hrho : 0 < rho) (hrhoh : rho < h) (hh1 : h ≤ 1) (hg : 0 ≤ g) :
    ∃ eta eps l u L U H : ℝ,
      eta ∈ Ioo (0:ℝ) 1 ∧ eps ∈ Ioo (0:ℝ) 1 ∧ 0 < l ∧ l < u ∧ u < 1 ∧
      0 < L ∧ L ≤ U ∧ 0 < H ∧ g/H < eps ∧
      ClassifiesSourceBand d (Schedule.once (d+1)) h rho eta eps H g l u L U := by
  exact fixed_base_source_classification d hd (Schedule.once (d+1)) hh hrho hrhoh hh1 hg

theorem fixed_unique_once_source_family (d : ℕ) (hd : 1 ≤ d)
    {h rho g : ℝ} (hh : 0 < h) (hrho : 0 < rho) (hrhoh : rho < h) (hh1 : h ≤ 1) (hg0 : 0 ≤ g) :
    ∃ eta eps l u L U H : ℝ,
      eta ∈ Ioo (0:ℝ) 1 ∧ eps ∈ Ioo (0:ℝ) 1 ∧ 0 < l ∧ l < u ∧ u < 1 ∧
      0 < L ∧ L ≤ U ∧ 0 < H ∧ g/H < eps ∧
      ∀ {Seed : Type*} [MeasurableSpace Seed] {M C : ℕ → ℕ}
        (Γ : ∀ t, FiniteGame (M t) (d+1) (C t) Seed)
        (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F]
        (E : Set ℝ), MeasurableSet E → ∀ [NullSingletonClass (F.restrict E)],
        F.real E = h → (∀ t, (Γ t).F = F) →
        (∀ t, (Γ t).G = Schedule.once (d+1)) → (∀ t, (Γ t).g = g) →
        (∀ᵐ v ∂F.restrict E, v ∈ Icc (H*(1-eps)) (H*(1+eps))) →
        (∀ᶠ t in atTop, ExclusiveTariffUsersOptimal (Γ t) .unique) →
        (∀ᶠ t in atTop, ExclusiveBroadcastOn (Γ t) E) →
        (∀ᶠ t in atTop, ∀ᵐ v ∂(Γ t).F, ∀ᵐ x ∂(Γ t).σ v,
          v ∈ E → x.bid ∈ Ioo (H*sourceBid d .unique h rho*(1-eta))
            (H*sourceBid d .unique h rho*(1+eta))) →
        (∀ᶠ t in atTop, RawBandContinuation (Γ t) (B t)
          (H*sourceBid d .unique h rho*(1-eta)) (H*sourceBid d .unique h rho*(1+eta))) →
        Tendsto M atTop atTop → Tendsto (fun t => (C t:ℝ)/M t) atTop (𝓝 rho) →
        ∃ beta lam p,
          ExistingSourceFamilyConclusion Γ F E .unique (Schedule.once (d+1)) g rho
            (H*sourceBid d .unique h rho*(1-eta)) (H*sourceBid d .unique h rho*(1+eta))
            l u (H*L) (H*U) beta lam p ∧
          (∀ᵐ v ∂F.restrict E,
            Tendsto (fun t => beta t v) atTop (𝓝 (v-g)) ∧ 0 < v-g ∧
              p v = 1-(lam/(v-g))^(rate (d+1))) := by
  obtain ⟨eta,eps,l,u,L,U,H,heta,heps,hl,hlu,hu,hL,hLU,hH,hsmall,hfamily⟩ :=
    fixed_once_base_source_classification d hd hh hrho hrhoh hh1 hg0
  refine ⟨eta,eps,l,u,L,U,H,heta,heps,hl,hlu,hu,hL,hLU,hH,hsmall,?_⟩
  intro Seed _ M C Γ B F _ E hE _ hmass hF hG hg hvalues husers hclass hband hcanonical hM hcap
  obtain ⟨beta,lam,p,hresult⟩ := hfamily .unique (by trivial) Γ B F E hE
    hmass hF hG hg hvalues husers hclass hband hcanonical hM hcap
  exact ⟨beta,lam,p,hresult,hresult.once_specialization rfl rfl⟩

end FCAppendix.Completion.Exclusive
