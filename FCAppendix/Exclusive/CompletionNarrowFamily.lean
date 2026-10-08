import FCAppendix.Exclusive.CompletionSourceNeighborhood
import FCAppendix.Exclusive.NarrowResidualStability
import FCAppendix.Exclusive.NarrowConditionalCounts

noncomputable section
namespace FCAppendix.Completion.Exclusive
open MeasureTheory ProbabilityTheory Filter Topology Set
open FCAppendix Game Bayes Exclusive Exclusive.Narrow Exclusive.Narrow.Finite
open Bayes.ExclusiveNarrow
open scoped BigOperators ProbabilityTheory

variable {m c d : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem forcedWeight_pos (_Γ : FiniteGame m (d+1) c Seed)
    (P : Corridor (d+1) m c) (i : Fin m) {b : ℝ}
    (hb : b ∈ Icc P.lower P.upper) (z : UserProfile m (d+1)) :
    0 < forcedWeight P.lower P.upper b i z := by
  apply div_pos _ (Nat.cast_pos.mpr P.population)
  have hsum : 0 ≤ ∑ j ∈ Finset.univ.erase i,
      clippedInverseDraw (d+1) P.lower P.upper (z j) :=
    Finset.sum_nonneg fun j _ => (clippedInverseDraw_bounds (d+1) P.proposers P.lower_pos (z j)).1
  exact add_pos_of_pos_of_nonneg (inverseBid_pos (d+1) (P.lower_pos.trans_le hb.1)) hsum

theorem actual_forced_concentration (Γ : FiniteGame m (d+1) c Seed)
    (P : Corridor (d+1) m c) (hplay : CorridorPlay Γ P) (i : Fin m)
    {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (hmass : ∫ u, activeDraw u ∂userLaw Γ = h)
    (hcap : (c:ℝ)/m < h) {b : ℝ} (hb : b ∈ Icc P.lower P.upper)
    (href : 1-((h-(c:ℝ)/m)/inverseMean Γ P.lower P.upper)*inverseBid (d+1) b ∈ Icc (0:ℝ) 1) :
    (∫ z, |boundedP Γ P hplay i b z-
      (1-((h-(c:ℝ)/m)/inverseMean Γ P.lower P.upper)*inverseBid (d+1) b)|
        ∂userProfileLaw Γ) +
      (∫ z, boundedShare Γ P hplay i b z ∂userProfileLaw Γ) ≤
        concentrationRate m (inverseBid (d+1) P.lower) (h*inverseBid (d+1) P.upper) := by
  let U := inverseBid (d+1) P.lower
  let ell := h*inverseBid (d+1) P.upper
  let mean := inverseMean Γ P.lower P.upper
  let delta := h-(c:ℝ)/m
  let w := inverseBid (d+1) b
  let x := fun z : UserProfile m (d+1) => forcedActive i z-(c:ℝ)/m
  let y : UserProfile m (d+1) → ℝ := forcedWeight P.lower P.upper b i
  have hU : 0 < U := inverseBid_pos (d+1) P.lower_pos
  have hell : 0 < ell := mul_pos hh (inverseBid_pos (d+1) P.upper_pos)
  have hmean : ell ≤ mean := inverseMean_lower Γ P.proposers P.lower_pos P.width.le hmass
  have hw : w ∈ Icc (0:ℝ) U :=
    ⟨(inverseBid_pos _ (P.lower_pos.trans_le hb.1)).le,
      inverseBid_antitone _ P.proposers P.lower_pos hb.1⟩
  have hd : delta ∈ Icc (0:ℝ) 1 :=
    ⟨(sub_pos.mpr hcap).le,by dsimp [delta]; linarith [div_nonneg (Nat.cast_nonneg c : (0:ℝ) ≤ c) (Nat.cast_nonneg m : (0:ℝ) ≤ m)]⟩
  have hreference : 1-delta*w/mean ∈ Icc (0:ℝ) 1 := by simpa [delta,w,mean,div_mul_eq_mul_div] using href
  have hx : (∫ z, |x z-delta| ∂userProfileLaw Γ) ≤ 1/Real.sqrt m+1/m := by
    have he := forcedMean_L1 (userLaw Γ) P.population activeDraw activeDraw_measurable
      zero_le_one activeDraw_bounds (by constructor <;> norm_num : (1:ℝ) ∈ Icc (0:ℝ) 1) i
    have he' : (∫ z, |forcedActive i z-h| ∂userProfileLaw Γ) ≤
        1/Real.sqrt m+1/m := by
      simpa only [userProfileLaw,forcedActive,hmass] using he
    calc
      _ = ∫ z, |forcedActive i z-h| ∂userProfileLaw Γ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun z => by
          dsimp only [x,delta]
          ring
      _ ≤ _ := he'
  have hy : (∫ z, |y z-mean| ∂userProfileLaw Γ) ≤ U/Real.sqrt m+U/m := by
    have he := forcedMean_L1 (userLaw Γ) P.population
      (clippedInverseDraw (d+1) P.lower P.upper)
      (measurable_clippedInverseDraw (d+1) P.lower P.upper) hU.le
      (clippedInverseDraw_bounds (d+1) P.proposers P.lower_pos) hw i
    simpa [userProfileLaw,forcedWeight,y,mean,inverseMean,U,w] using he
  have hiX : Integrable (fun z => |x z-delta|) (userProfileLaw Γ) := by
    have hi := integrable_abs_forcedMean_sub (userProfileLaw Γ) P.population
      (activeDraw (n := d+1)) activeDraw_measurable activeDraw_bounds
      (show (1:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num) i h
    have heq : (fun z => |x z-delta|) = (fun z => |forcedMean activeDraw i 1 z-h|) := by
      funext z
      congr 1
      dsimp only [x,delta,forcedActive]
      ring
    rw [heq]
    exact hi
  have hiY : Integrable (fun z => |y z-mean|) (userProfileLaw Γ) :=
    integrable_abs_forcedMean_sub (userProfileLaw Γ) P.population
      (clippedInverseDraw (d+1) P.lower P.upper)
      (measurable_clippedInverseDraw (d+1) P.lower P.upper)
      (clippedInverseDraw_bounds (d+1) P.proposers P.lower_pos) hw i mean
  have hiP := boundedP_distance_integrable Γ P hplay i b (1-delta*w/mean)
  have hiS := boundedShare_integrable Γ P hplay i b
  have hpoint : ∀ᵐ z ∂userProfileLaw Γ,
      |boundedP Γ P hplay i b z-(1-delta*w/mean)|+boundedShare Γ P hplay i b z ≤
        (2*U/ell)*|x z-delta|+(2*U/ell^2+4/ell)*|y z-mean|+2*U/((m:ℝ)*ell) := by
    filter_upwards [forced_statistics_row Γ P hplay i hb] with z hz
    rw [hz.2.2.1,hz.2.2.2]
    have hp := allocation_ratio_error (x := x z) hU.le hw (forcedWeight_pos Γ P i hb z)
      hell hmean hd hreference
    have hs := share_ratio_error P.population hw (forcedWeight_pos Γ P i hb z) hell hmean
    change |allocationOfMeans w (x z) (y z)-(1-delta*w/mean)|+
      shareOfMeans m w (y z) ≤ _
    calc
      _ ≤ ((2*U/ell)*|x z-delta|+(2*U/ell^2+2/ell)*|y z-mean|)+
          (2*U/((m:ℝ)*ell)+(2/ell)*|y z-mean|) := add_le_add hp hs
      _ = _ := by ring
  let A := 2*U/ell
  let B := 2*U/ell^2+4/ell
  let R := 2*U/((m:ℝ)*ell)
  have hiAX : Integrable (fun z => A*|x z-delta|) (userProfileLaw Γ) := hiX.const_mul A
  have hiBY : Integrable (fun z => B*|y z-mean|) (userProfileLaw Γ) := hiY.const_mul B
  have hiR : Integrable (fun _ : UserProfile m (d+1) => R) (userProfileLaw Γ) := integrable_const R
  have hi := integral_mono_ae (hiP.add hiS) ((hiAX.add hiBY).add hiR) hpoint
  simp only [Pi.add_apply] at hi
  have hiAB : Integrable (fun z => A*|x z-delta|+B*|y z-mean|) (userProfileLaw Γ) := hiAX.add hiBY
  rw [integral_add hiP hiS, integral_add hiAB hiR,
    integral_add hiAX hiBY, integral_const_mul, integral_const_mul] at hi
  simp only [integral_const, probReal_univ, one_smul] at hi
  have hA : 0 ≤ A := div_nonneg (mul_nonneg (by norm_num) hU.le) hell.le
  have hB : 0 ≤ B := add_nonneg
    (div_nonneg (mul_nonneg (by norm_num) hU.le) (sq_nonneg ell))
    (div_nonneg (by norm_num) hell.le)
  have hbound := hi.trans (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hx hA) (mul_le_mul_of_nonneg_left hy hB)) le_rfl)
  simpa only [A, B, R, concentrationRate, U, ell, delta, w, mean,
    div_mul_eq_mul_div] using hbound

theorem inverseMean_eq_pure_active (Γ : FiniteGame m (d+1) c Seed)
    (P : Corridor (d+1) m c) (E : Set ℝ) (hE : MeasurableSet E)
    (hclass : ExclusiveBroadcastOn Γ E) (beta : ℝ → ℝ) (hbeta : Measurable beta)
    (hband : ∀ v, beta v ∈ Icc P.lower P.upper)
    (hpure : ∀ᵐ v ∂Γ.F.restrict E, ∀ᵐ a ∂Γ.σ v, a.bid = beta v) :
    inverseMean Γ P.lower P.upper = ∫ v, inverseBid (d+1) (beta v) ∂Γ.F.restrict E := by
  letI : IsMarkovKernel Γ.σ := Γ.hσ
  let f : ℝ → ℝ := E.indicator (fun v => inverseBid (d+1) (beta v))
  have hf : Measurable f := (hbeta.pow_const (-rate (d+1))).indicator hE
  have hfb (v : ℝ) : |f v| ≤ inverseBid (d+1) P.lower := by
    by_cases hv : v ∈ E
    · change |E.indicator (fun v => inverseBid (d+1) (beta v)) v| ≤ _
      rw [Set.indicator_of_mem hv,
        abs_of_pos (inverseBid_pos _ (P.lower_pos.trans_le (hband v).1))]
      exact inverseBid_antitone _ P.proposers P.lower_pos (hband v).1
    · simp only [f, Set.indicator_of_notMem hv, abs_zero]
      exact (inverseBid_pos _ P.lower_pos).le
  have hp : ∀ᵐ v ∂Γ.F, v ∈ E → ∀ᵐ a ∂Γ.σ v, a.bid = beta v :=
    (ae_restrict_iff' hE).mp hpure
  have hc := Measure.ae_ae_of_ae_compProd hclass
  have hleft : Measurable (fun x : ℝ × JointAction (d+1) =>
      if x.2.routeCount = 0 then (0:ℝ)
      else inverseBid (d+1) (max P.lower (min P.upper x.2.bid))) := by
    exact Measurable.ite
      (measurableSet_eq_fun ((measurable_routeCount _).comp measurable_snd) measurable_const)
      measurable_const
      ((measurable_const.max (measurable_const.min ((measurable_bid _).comp measurable_snd))).pow_const _)
  have he : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ),
      (if x.2.routeCount = 0 then (0:ℝ)
        else inverseBid (d+1) (max P.lower (min P.upper x.2.bid))) = f x.1 := by
    apply Measure.ae_compProd_of_ae_ae (measurableSet_eq_fun hleft (hf.comp measurable_fst))
    filter_upwards [hp,hc] with v hv hcv
    by_cases hvE : v ∈ E
    · filter_upwards [hv hvE,hcv] with a ha hca
      have hn : d+1 ≠ 0 := by omega
      simp only [Function.comp_def, (hca.1 hvE).2, if_neg hn, ha, f, Set.indicator_of_mem hvE,
        min_eq_right (hband v).2, max_eq_right (hband v).1]
    · filter_upwards [hcv] with a hca
      simp only [Function.comp_def, hca.2 hvE, if_true, f, Set.indicator_of_notMem hvE]
  have hu : ∀ᵐ u ∂userLaw Γ, clippedInverseDraw (d+1) P.lower P.upper u = f u.1.1 :=
    Measure.quasiMeasurePreserving_fst.ae he
  change (∫ u, clippedInverseDraw (d+1) P.lower P.upper u ∂userLaw Γ) = _
  rw [integral_congr_ae hu, integral_userLaw_value_bounded Γ f hf _ hfb]
  exact integral_indicator hE

structure ScalarCorridor (d : ℕ) (lo hi h cap l u L U : ℝ) : Prop where
  cap_nonneg : 0 ≤ cap
  cap_lt_mass : cap < h
  exposure_lower : 1-u ≤ ((h-cap)/(h*inverseBid (d+1) lo))*inverseBid (d+1) hi
  exposure_upper : ((h-cap)/(h*inverseBid (d+1) hi))*inverseBid (d+1) lo ≤ 1-l
  price_lower : L ≤ ((h-cap)/(h*inverseBid (d+1) lo))^d
  price_upper : ((h-cap)/(h*inverseBid (d+1) hi))^d ≤ U

theorem comparison_mem_of_scalar_corridor {d : ℕ} (hd : 1 ≤ d)
    {lo hi h cap l u L U W b : ℝ} (hlo : 0 < lo) (hh : 0 < h)
    (hb : b ∈ Icc lo hi)
    (hW : W ∈ Icc (h*inverseBid (d+1) hi) (h*inverseBid (d+1) lo))
    (H : ScalarCorridor d lo hi h cap l u L U) :
    1-((h-cap)/W)*inverseBid (d+1) b ∈ Icc l u ∧ ((h-cap)/W)^d ∈ Icc L U := by
  have hc := meanExposure_corridor (n := d+1) (by omega) hh H.cap_lt_mass hlo hb hW
  have hhi : 0 < hi := hlo.trans_le (hb.1.trans hb.2)
  have hW0 : 0 < W := (mul_pos hh (inverseBid_pos (d+1) hhi)).trans_le hW.1
  have hD0 : 0 ≤ (h-cap)/W := div_nonneg (sub_pos.mpr H.cap_lt_mass).le hW0.le
  have hDlo := div_le_div_of_nonneg_left (sub_pos.mpr H.cap_lt_mass).le hW0 hW.2
  have hDhi := div_le_div_of_nonneg_left (sub_pos.mpr H.cap_lt_mass).le
    (mul_pos hh (inverseBid_pos (d+1) hhi)) hW.1
  exact ⟨⟨by linarith [H.exposure_upper, hc.2],by linarith [H.exposure_lower, hc.1]⟩,
    ⟨H.price_lower.trans (pow_le_pow_left₀ (div_nonneg (sub_pos.mpr H.cap_lt_mass).le
      (mul_pos hh (inverseBid_pos (d+1) hlo)).le) hDlo d),
      (pow_le_pow_left₀ hD0 hDhi d).trans H.price_upper⟩⟩

theorem supported_foc_at_representative (Γ : FiniteGame m (d+1) c Seed)
    (P : Corridor (d+1) m c) (hplay : CorridorPlay Γ P) (B : PosteriorSystem Γ)
    (hC : BroadcastCorridorContinuation Γ B P) (a : UserTariff)
    (hu : ExclusiveTariffUsersOptimal Γ a) (i : Fin m)
    (E : Set ℝ) (hE : MeasurableSet E) (beta : ℝ → ℝ)
    (hpure : ∀ᵐ v ∂Γ.F.restrict E, ∀ᵐ x ∂Γ.σ v, x.bid = beta v)
    (hband : ∀ᵐ v ∂Γ.F, ∀ᵐ x ∂Γ.σ v,
      v ∈ E → x.routeCount = d+1 ∧ x.bid ∈ Ioo P.lower P.upper) :
    ∀ᵐ v ∂Γ.F.restrict E, beta v ∈ Ioo P.lower P.upper ∧
      v*(gameRow Γ P hplay i).momentDerivative successIndicator (beta v) =
        (gameRow Γ P hplay i).costDerivative a Γ.G Γ.g (beta v) := by
  letI : IsMarkovKernel Γ.σ := Γ.hσ
  have hf := ae_supported_interior_FOC_of_continuation Γ P hplay B hC a hu i
  filter_upwards [hpure,ae_restrict_of_ae hf,ae_restrict_of_ae hband,ae_restrict_mem hE]
    with v hp hf hb hvE
  obtain ⟨x,hx,hfx,hbx⟩ := (hp.and (hf.and hb)).exists
  have hg := hbx hvE
  exact ⟨hx ▸ hg.2,by simpa only [hx] using hfx hg.1 hg.2⟩

theorem canonical_narrow_family_limit_with_price
    {M C : ℕ → ℕ} (Γ : (t : ℕ) → FiniteGame (M t) (d+1) (C t) Seed)
    (P : (t : ℕ) → Corridor (d+1) (M t) (C t))
    (hplay : ∀ t, CorridorPlay (Γ t) (P t))
    (Bpost : (t : ℕ) → PosteriorSystem (Γ t))
    (hcont : ∀ t, BroadcastCorridorContinuation (Γ t) (Bpost t) (P t))
    (a : UserTariff) (ha : a.Allowed) (hu : ∀ t, ExclusiveTariffUsersOptimal (Γ t) a)
    (hd : 1 ≤ d) (F : Measure ℝ) [IsProbabilityMeasure F]
    (E : Set ℝ) (hE : MeasurableSet E) [NullSingletonClass (F.restrict E)]
    (hF : ∀ t, (Γ t).F = F) (G : Schedule (d+1)) (hG : ∀ t, (Γ t).G = G)
    {g lo hi h rho V l u L U k K : ℝ}
    (hg : ∀ t, (Γ t).g = g) (hh : 0 < h) (hh1 : h ≤ 1)
    (hmass : F.real E = h) (hlo : 0 < lo) (hlohi : lo < hi)
    (hPl : ∀ t, (P t).lower = lo) (hPu : ∀ t, (P t).upper = hi)
    (hclass : ∀ t, ExclusiveBroadcastOn (Γ t) E)
    (hband : ∀ t, ∀ᵐ v ∂(Γ t).F, ∀ᵐ x ∂(Γ t).σ v,
      v ∈ E → x.routeCount = d+1 ∧ x.bid ∈ Ioo lo hi)
    (hcm : ∀ t, C t < M t)
    (hval : ∀ᵐ v ∂F.restrict E, |v| ≤ V)
    (hl : 0 < l) (hlu : l ≤ u) (hu1 : u < 1) (hk : 0 < k) (hK : 0 ≤ K)
    (hscalar : ∀ t, ScalarCorridor d lo hi h ((C t:ℝ)/M t) l u L U)
    (hslope : ∀ lam ∈ Icc L U, ∀ p ∈ Icc l u,
      lam*dfTariff d a p+g*deriv (baseMarginalCost d G) p ∈ Icc k K)
    (hM : Tendsto M atTop atTop)
    (hcap : Tendsto (fun t => (C t:ℝ)/M t) atTop (𝓝 rho)) :
    ∃ beta : ℕ → ℝ → ℝ, ∃ lamInf : ℝ, ∃ pInf : ℝ → ℝ,
      (∀ t, Monotone (beta t) ∧ Measurable (beta t) ∧
        ∀ᵐ v ∂F.restrict E, ∀ᵐ x ∂(Γ t).σ v, x.bid = beta t v) ∧
      (∀ t v, beta t v ∈ Icc lo hi) ∧
      (∀ t, ∃ S : Set ℝ, (F.restrict E) Sᶜ = 0 ∧ StrictMonoOn (beta t) S) ∧
      (∀ t : ℕ, ∀ b : ℝ, (Measure.map (fun x : ℝ × JointAction (d+1) => x.2.bid)
        ((F.restrict E) ⊗ₘ (Γ t).σ)) {b} = 0) ∧
      lamInf ∈ Icc L U ∧
      LocalExposureSolution (F.restrict E) (Icc l u)
        (fTariff d a) (baseMarginalCost d G) g rho lamInf pInf ∧
      (∀ᵐ v ∂F.restrict E,
        Tendsto (fun t => beta t v) atTop (𝓝 (referenceBid d lamInf (pInf v)))) ∧
      (∀ᵐ v ∂F.restrict E, ∀ I : (t : ℕ) → Fin (M t), ∀ j : Fin (d+1+1),
        Tendsto (fun t => (typeOutcome (Γ t) (I t) v).mass j) atTop
          (𝓝 (PayOnce.ManyProposers.binomialMass (d+1) (pInf v) j.val))) := by
  classical
  let mu := F.restrict E
  letI : IsFiniteMeasure mu := by dsimp only [mu]; infer_instance
  have hmu : mu.real univ = h := by simpa [mu] using hmass
  let i0 : (t : ℕ) → Fin (M t) := fun t => ⟨0,(P t).population⟩
  have hactive (t : ℕ) : userLaw (Γ t) {u : UserDraw (d+1) | u.1.2.routeCount ≠ 0} ≠ 0 := by
    have he := activeMean_eq (Γ t) (by omega) E hE (hclass t)
    rw [hF t,hmass] at he
    intro hz
    have hzero : activeDraw =ᵐ[userLaw (Γ t)] (fun _ : UserDraw (d+1) => (0:ℝ)) := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with z hz
      simp only [not_not] at hz
      simp [activeDraw,hz]
    have hi := integral_congr_ae hzero
    simp only [integral_zero] at hi
    linarith
  have hfinite (t : ℕ) : ∃ beta : ℝ → ℝ, Monotone beta ∧ Measurable beta ∧
      (∀ v, beta v ∈ Icc lo hi) ∧
      (∀ᵐ v ∂mu, ∀ᵐ x ∂(Γ t).σ v, x.bid = beta v) ∧
      (∃ S : Set ℝ, mu Sᶜ = 0 ∧ StrictMonoOn beta S) ∧
      (∀ b : ℝ, (Measure.map (fun x : ℝ × JointAction (d+1) => x.2.bid)
        (mu ⊗ₘ (Γ t).σ)) {b} = 0) := by
    letI : NullSingletonClass ((Γ t).F.restrict E) := by rw [hF t]; infer_instance
    have he := canonical_finite_classification (Γ t) (P t) (hplay t) (Bpost t)
      (hcont t) a ha (hu t) (i0 t) E hE (hcm t) (hactive t)
      (by simpa only [hPl t,hPu t] using hband t)
    simpa only [hF t,hPl t,hPu t,mu] using he
  choose beta hbetaMono hbetaMeas hbetaBand hbetaPure hbetaStrict hbetaAtoms using hfinite
  let W := fun t => ∫ v, inverseBid (d+1) (beta t v) ∂mu
  let D := fun t => (h-(C t:ℝ)/M t)/W t
  let lam := fun t => (D t)^d
  let p := fun t v => 1-D t*inverseBid (d+1) (beta t v)
  have hW (t : ℕ) := inverse_mean_bounds (d+1) (by omega) hh hmu hlo hlohi.le
    (beta t) (hbetaMeas t) (Eventually.of_forall (hbetaBand t))
  have hWgame (t : ℕ) : inverseMean (Γ t) lo hi = W t := by
    simpa [hF t,hPl t,hPu t,mu,W] using inverseMean_eq_pure_active
      (Γ t) (P t) E hE (hclass t) (beta t) (hbetaMeas t)
      (by simpa [hPl,hPu] using hbetaBand t)
      (by simpa [hF t,mu] using hbetaPure t)
  have hmem (t : ℕ) (v : ℝ) : p t v ∈ Icc l u ∧ lam t ∈ Icc L U :=
    comparison_mem_of_scalar_corridor hd hlo hh (hbetaBand t v) (hW t).2.1 (hscalar t)
  have hDpos (t : ℕ) : 0 < D t := div_pos (sub_pos.mpr (hscalar t).cap_lt_mass) (hW t).2.2
  have hformula (t : ℕ) (v : ℝ) : beta t v = referenceBid d (lam t) (p t v) :=
    meanExposure_bid_formula d hd (hDpos t) (hlo.trans_le (hbetaBand t v).1)
  have hpi (t : ℕ) : Integrable (p t) mu := (integrable_const 1).sub ((hW t).1.const_mul (D t))
  have hcapacity (t : ℕ) : ∫ v, p t v ∂mu = (C t:ℝ)/M t :=
    meanExposure_capacity hmu (beta t) (hW t).1 (hW t).2.2.ne'
  let e := fun t => concentrationRate (M t) (inverseBid (d+1) lo) (h*inverseBid (d+1) hi)
  have he : Tendsto e atTop (𝓝 0) := concentrationRate_tendsto hM _ _
  have hconcentration (t : ℕ) (i : Fin (M t)) (v : ℝ) :
      (∫ z, |boundedP (Γ t) (P t) (hplay t) i (beta t v) z-p t v| ∂userProfileLaw (Γ t))+
      ∫ z, boundedShare (Γ t) (P t) (hplay t) i (beta t v) z ∂userProfileLaw (Γ t) ≤ e t := by
    have hevent := activeMean_eq (Γ t) (by omega) E hE (hclass t)
    rw [hF t,hmass] at hevent
    have he' := actual_forced_concentration (Γ t) (P t) (hplay t) i hh hh1 hevent
      (hscalar t).cap_lt_mass (by simpa [hPl,hPu] using hbetaBand t v)
      (by simpa [hPl,hPu,hWgame,D,p] using
        show p t v ∈ Icc (0:ℝ) 1 from ⟨hl.le.trans (hmem t v).1.1,(hmem t v).1.2.trans hu1.le⟩)
    simpa [hPl,hPu,hWgame,D,p,e] using he'
  have he0 (t : ℕ) : 0 ≤ e t := by
    have h := hconcentration t (i0 t) 0
    exact (add_nonneg (integral_nonneg fun _ => abs_nonneg _)
      (integral_nonneg fun _ => (unitClamp_mem _).1)).trans h
  obtain ⟨Bt,Lt,hS,hGB,hAB⟩ := source_polynomial_bounds (d+1) G
  let Kt := (Lt+Bt)/(1-u)+(d:ℝ)*hi/(1-u)*Bt+(hi+|g|)*((Lt+Bt)/(1-u))
  have hKt : 0 ≤ Kt := by
    have hBt := hS.B_nonneg
    have hLt := hS.L_nonneg
    have hhi := hlo.trans hlohi
    have hden : 0 < 1-u := sub_pos.mpr hu1
    dsimp only [Kt]
    positivity
  have hcorrect (t : ℕ) (i : Fin (M t)) := derivativeCorrection_with_bounds
    (Γ t) (P t) (hplay t) hd i hl.le hu1 Bt Lt hS
      (by simpa [hG] using hGB) hAB a ha
  let Smin := ((d+1:ℕ):ℝ)*(1-u)^d
  have hSmin : 0 < Smin := mul_pos (Nat.cast_pos.mpr (by omega))
    (pow_pos (sub_pos.mpr hu1) d)
  have hres : ∀ t, ∀ᵐ v ∂mu,
      |v-(lam t*fTariff d a (p t v)+g*baseMarginalCost d G (p t v))| ≤
        (V+1)*Kt*e t/Smin := by
    intro t
    have hf := supported_foc_at_representative (Γ t) (P t) (hplay t) (Bpost t) (hcont t)
      a (hu t) (i0 t) E hE (beta t) (by simpa [hF,mu] using hbetaPure t)
      (by simpa [hPl,hPu] using hband t)
    rw [hF t] at hf
    filter_upwards [hf,hval] with v hv hvalv
    have hA := (hcorrect t (i0 t)).success (beta t v) hv.1 (p t v) (hmem t v).1
    have hC := (hcorrect t (i0 t)).cost (beta t v) hv.1 (p t v) (hmem t v).1
    have hco := hconcentration t (i0 t) v
    simp only [hPu,hg,hG] at hA hC
    have hA' := hA.trans (mul_le_mul_of_nonneg_left hco hKt)
    have hC' := hC.trans (mul_le_mul_of_nonneg_left hco hKt)
    have hsl : Smin ≤ Exclusive.Narrow.successSlope d (p t v) := by
      change ((d+1:ℕ):ℝ)*(1-u)^d ≤ ((d+1:ℕ):ℝ)*(1-p t v)^d
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (sub_nonneg.mpr hu1.le) (by linarith [(hmem t v).1.2]) d)
        (Nat.cast_nonneg _)
    have he' := source_residual_uniform d hd a G
      (hl.trans_le (hmem t v).1.1) ((hmem t v).1.2.trans_lt hu1) (hformula t v)
      (by simpa [hg,hG] using hv.2) hvalv hSmin hsl (mul_nonneg hKt (he0 t)) hA' hC'
    convert he' using 1
    ring
  obtain ⟨Fmin,Fmax,Dmin,Dmax,hFm,hFM,_hDm,_hDM,hbounds⟩ :=
    source_tariff_uniform_bounds d hd hl.le hlu hu1
  have hslopes : ∀ s ∈ Icc L U, ∀ x ∈ Icc l u, ∀ y ∈ Icc l u, x ≤ y →
      k*(y-x) ≤ (s*fTariff d a y+g*baseMarginalCost d G y)-
        (s*fTariff d a x+g*baseMarginalCost d G x) ∧
      (s*fTariff d a y+g*baseMarginalCost d G y)-
        (s*fTariff d a x+g*baseMarginalCost d G x) ≤ K*(y-x) := by
    intro s hs
    exact slope_bounds_of_derivative_bounds
      (fun z hz => hasDerivAt_exposureEquation d hd a G g s z (hz.2.trans_lt hu1)) (hslope s hs)
  have herr : Tendsto (fun t => (V+1)*Kt*e t/Smin) atTop (𝓝 0) := by
    simpa using (he.const_mul ((V+1)*Kt)).div_const Smin
  obtain ⟨lamInf,pInf,hlamInf,hlam,hpInf,hsolution⟩ := full_sequence_of_finite_residuals
    hh hmu hk hK hFm (hFm.le.trans hFM) (fun z hz => (hbounds a ha z hz).1)
    (fun z hz => (hasDerivAt_fTariff d hd a z (hz.2.trans_lt hu1)).continuousAt)
    (fun z hz => (hasDerivAt_baseMarginalCost d G z (hz.2.trans_lt hu1)).continuousAt)
    hslopes lam (fun t => (C t:ℝ)/M t) (fun t => (V+1)*Kt*e t/Smin) p
    (fun t => (hmem t 0).2) hpi (fun t => Eventually.of_forall fun v => (hmem t v).1)
    hcapacity hres hcap herr
  refine ⟨beta,lamInf,pInf,(fun t => ⟨hbetaMono t,hbetaMeas t,hbetaPure t⟩),
    hbetaBand,hbetaStrict,hbetaAtoms,hlamInf,hsolution,?_,?_⟩
  · filter_upwards [hpInf,hsolution.mem] with v hv hvm
    exact bid_tendsto_of_reference d lam (fun t => p t v) (fun t => beta t v) lamInf (pInf v)
      (hvm.2.trans_lt hu1) hlam hv (Eventually.of_forall fun t => hformula t v)
  · have hfiniteCount (t : ℕ) (i : Fin (M t)) : ∀ᵐ v ∂mu, ∀ j : Fin (d+1+1),
        (typeOutcome (Γ t) i v).mass j =
          binomialMixtureMass (userProfileLaw (Γ t)) (d+1)
            (boundedP (Γ t) (P t) (hplay t) i (beta t v)) j.val := by
      have hkernel := supportedKernel_of_continuation (Γ t) (P t) (hplay t) (Bpost t) (hcont t) i E
        (by filter_upwards [hband t] with v hv; filter_upwards [hv] with x hx hvE _;
            simpa [hPl,hPu] using ⟨(hx hvE).2.1.le,(hx hvE).2.2.le⟩)
      have hp : ∀ᵐ v ∂(Γ t).F.restrict E, ∀ᵐ x ∂(Γ t).σ v,
          x.bid = beta t v ∧ x.routeCount = d+1 := by
        rw [hF t]
        have hb' := ae_restrict_of_ae (s := E) (hband t)
        rw [hF t] at hb'
        filter_upwards [hbetaPure t,hb',ae_restrict_mem hE] with v hv hbandv hvE
        filter_upwards [hv,hbandv] with x hx hxb
        exact ⟨hx,(hxb hvE).1⟩
      have h := typeOutcome_mass_eq_binomialMixture_of_purity (Γ t) i E hE _ hkernel (beta t) hp
      simpa only [hF t,mu] using h
    have hcount := ae_typeOutcome_binomial_limit_changing_identities Γ mu 0
      (fun t i => boundedP (Γ t) (P t) (hplay t) i) beta p pInf e
      (fun t i b => boundedP_measurable (Γ t) (P t) (hplay t) i b)
      (fun _ _ _ _ => unitClamp_mem _)
      (fun t _ => ae_all_iff.mpr (hfiniteCount t))
      (fun t _ => Eventually.of_forall fun v =>
        ⟨hl.le.trans (hmem t v).1.1,(hmem t v).1.2.trans hu1.le⟩)
      (fun t _ => Eventually.of_forall fun v i => (le_add_of_nonneg_right
        (integral_nonneg fun _ => (unitClamp_mem _).1)).trans (hconcentration t i v)) he hpInf
    simpa only [Nat.add_zero] using hcount.mono (fun _ h => h.2)

theorem canonical_narrow_family_limit
    {M C : ℕ → ℕ} (Γ : (t : ℕ) → FiniteGame (M t) (d+1) (C t) Seed)
    (P : (t : ℕ) → Corridor (d+1) (M t) (C t))
    (hplay : ∀ t, CorridorPlay (Γ t) (P t))
    (Bpost : (t : ℕ) → PosteriorSystem (Γ t))
    (hcont : ∀ t, BroadcastCorridorContinuation (Γ t) (Bpost t) (P t))
    (a : UserTariff) (ha : a.Allowed) (hu : ∀ t, ExclusiveTariffUsersOptimal (Γ t) a)
    (hd : 1 ≤ d) (F : Measure ℝ) [IsProbabilityMeasure F]
    (E : Set ℝ) (hE : MeasurableSet E) [NullSingletonClass (F.restrict E)]
    (hF : ∀ t, (Γ t).F = F) (G : Schedule (d+1)) (hG : ∀ t, (Γ t).G = G)
    {g lo hi h rho V l u L U k K : ℝ}
    (hg : ∀ t, (Γ t).g = g) (hh : 0 < h) (hh1 : h ≤ 1)
    (hmass : F.real E = h) (hlo : 0 < lo) (hlohi : lo < hi)
    (hPl : ∀ t, (P t).lower = lo) (hPu : ∀ t, (P t).upper = hi)
    (hclass : ∀ t, ExclusiveBroadcastOn (Γ t) E)
    (hband : ∀ t, ∀ᵐ v ∂(Γ t).F, ∀ᵐ x ∂(Γ t).σ v,
      v ∈ E → x.routeCount = d+1 ∧ x.bid ∈ Ioo lo hi)
    (hcm : ∀ t, C t < M t)
    (hval : ∀ᵐ v ∂F.restrict E, |v| ≤ V)
    (hl : 0 < l) (hlu : l ≤ u) (hu1 : u < 1) (hk : 0 < k) (hK : 0 ≤ K)
    (hscalar : ∀ t, ScalarCorridor d lo hi h ((C t:ℝ)/M t) l u L U)
    (hslope : ∀ lam ∈ Icc L U, ∀ p ∈ Icc l u,
      lam*dfTariff d a p+g*deriv (baseMarginalCost d G) p ∈ Icc k K)
    (hM : Tendsto M atTop atTop)
    (hcap : Tendsto (fun t => (C t:ℝ)/M t) atTop (𝓝 rho)) :
    ∃ beta : ℕ → ℝ → ℝ, ∃ lamInf : ℝ, ∃ pInf : ℝ → ℝ,
      (∀ t, Monotone (beta t) ∧ Measurable (beta t) ∧
        ∀ᵐ v ∂F.restrict E, ∀ᵐ x ∂(Γ t).σ v, x.bid = beta t v) ∧
      LocalExposureSolution (F.restrict E) (Icc l u)
        (fTariff d a) (baseMarginalCost d G) g rho lamInf pInf ∧
      (∀ᵐ v ∂F.restrict E,
        Tendsto (fun t => beta t v) atTop (𝓝 (referenceBid d lamInf (pInf v)))) ∧
      (∀ᵐ v ∂F.restrict E, ∀ I : (t : ℕ) → Fin (M t), ∀ j : Fin (d+1+1),
        Tendsto (fun t => (typeOutcome (Γ t) (I t) v).mass j) atTop
          (𝓝 (PayOnce.ManyProposers.binomialMass (d+1) (pInf v) j.val))) := by
  obtain ⟨beta,lamInf,pInf,hfinite,_hband,_hstrict,_hatoms,_hprice,hsol,hbid,hcount⟩ :=
    canonical_narrow_family_limit_with_price Γ P hplay Bpost hcont a ha hu hd F E hE hF G hG
      hg hh hh1 hmass hlo hlohi hPl hPu hclass hband hcm hval hl hlu hu1 hk hK hscalar hslope hM hcap
  exact ⟨beta,lamInf,pInf,hfinite,hsol,hbid,hcount⟩

theorem unique_once_bid_limit {mu : Measure ℝ} {d : ℕ} {l u g rho lam : ℝ}
    {p : ℝ → ℝ} (hu : u < 1)
    (H : LocalExposureSolution mu (Icc l u) (fTariff d .unique)
      (baseMarginalCost d (Schedule.once (d+1))) g rho lam p) :
    ∀ᵐ v ∂mu, referenceBid d lam (p v) = v-g := by
  filter_upwards [H.mem,H.equation] with v hv he
  exact unique_once_source_bid d lam (p v) v g (hv.2.trans_lt hu) he

end FCAppendix.Completion.Exclusive
