import FCAppendix.Affine.UniformFinite.Late.RemoveCap
import FCAppendix.Affine.UniformFinite.RawCounts

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine.UniformFinite.Late.Exceptional
open Set MeasureTheory ProbabilityTheory Filter Topology Classical
open Uniform05 Source ClippedResidual WeightedSampling
open Existence.Distributional
open scoped BigOperators

def routeProduct (i : Row) (v L b : ℝ) : ℝ :=
  (v-b)*exposure (xi i) L b

def rowRoutePayoff {M : ℕ} [NeZero M] (i : Row) (G : RestrictedLaw i)
    (row : CountRow M) (j : Fin 2) (v : ℝ) (b : Fin M → ℝ) (a : Fin M) : ℝ :=
  (continuationLaw i G row b a).expect (fun P => (v-b a)*routeIndicator j a P)

theorem routeIndicator_bounds {M : ℕ} (j : Fin 2) (a : Fin M) (P : Allocation M) :
    routeIndicator j a P ∈ Icc (0:ℝ) 1 := by
  unfold routeIndicator WeightedSampling.indicator
  split_ifs <;> constructor <;> norm_num

theorem rowRoutePayoff_bound {M : ℕ} [NeZero M] (i : Row) (G : RestrictedLaw i)
    (row : CountRow M) (j : Fin 2) (v : ℝ) (b : Fin M → ℝ) (a : Fin M) :
    |rowRoutePayoff i G row j v b a| ≤ |v|+|b a| := by
  unfold rowRoutePayoff
  apply (WeightedSampling.abs_expect_le _ _).trans
  apply FiniteLaw.expect_le_const
  intro P
  rw [abs_mul,abs_of_nonneg (routeIndicator_bounds j a P).1]
  calc
    _ ≤ |v-b a| *1 := mul_le_mul_of_nonneg_left (routeIndicator_bounds j a P).2 (abs_nonneg _)
    _ ≤ _ := by simpa only [mul_one] using abs_sub v (b a)

theorem rowRoutePayoff_overbid {M : ℕ} [NeZero M] (i : Row) (G : RestrictedLaw i)
    (row : CountRow M) (j : Fin 2) (v : ℝ) (b : Fin M → ℝ) (a : Fin M)
    (hv : v < b a) : rowRoutePayoff i G row j v b a ≤ 0 := by
  apply FiniteLaw.expect_le_const
  intro P
  exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hv.le) (routeIndicator_bounds j a P).1

theorem measurable_rowRoutePayoff {M : ℕ} [NeZero M]
    (i : Row) (G : RestrictedLaw i) (row : CountRow M) (j : Fin 2) (v : ℝ) (a : Fin M) :
    Measurable (fun b : Fin M → ℝ => rowRoutePayoff i G row j v b a) := by
  unfold rowRoutePayoff FiniteLaw.expect
  apply Finset.measurable_sum
  intro P _
  exact (measurable_continuationLaw_mass i G row a P).mul
    ((measurable_const.sub (measurable_pi_apply a)).mul_const _)

theorem row_test_error {M : ℕ} [NeZero M] (i : Row) (G : RestrictedLaw i)
    (row : CountRow M) (b : Fin M → ℝ) (a : Fin M) (T : Allocation M → ℝ)
    (u C : ℝ) (halpha : alpha i G row b a=1)
    (h : ∀p : Path (Fin M) (imbalance row),
      0 < (pathLaw (weight i G row b a) (imbalance row) ∅).mass p →
      |(conditionalCompletion (xi i) (small row) (lowerBids row b)
          (finalSet (imbalance row) ∅ p)).expect (fun P => T (orient row P))-u| ≤ C) :
    |(continuationLaw i G row b a).expect T-u| ≤ C := by
  let P := pathLaw (weight i G row b a) (imbalance row) ∅
  let f := fun p : Path (Fin M) (imbalance row) =>
    (conditionalCompletion (xi i) (small row) (lowerBids row b)
      (finalSet (imbalance row) ∅ p)).expect (fun out => T (orient row out))
  have hc : (canonicalLaw i G row b a).expect T=P.expect f := by
    rw [canonicalLaw,FiniteLaw.expect_map,WeightedSampling.expect_pairLaw]
  have he : (continuationLaw i G row b a).expect T=P.expect f := by
    unfold continuationLaw
    by_cases heq : residual row 0=residual row 1
    · rw [if_pos heq,← canonicalLaw_equal i G row b a heq]
      exact hc
    · rw [if_neg heq,FiniteLaw.expect_mixture,halpha]
      simpa only [one_mul,sub_self,zero_mul,add_zero] using hc
  rw [he,← P.expect_const u,← FiniteLaw.expect_sub]
  exact (WeightedSampling.abs_expect_le P _).trans (WeightedSampling.expect_le_const P _ C h)

theorem conditional_route_payoff {M : ℕ} [NeZero M] (i : Row) {z : ℝ}
    (hz : 0 < z) (hreceipt : kappa i*t i ≤ z) (row : CountRow M)
    (b : Fin M → ℝ) (a : Fin M) (ha : a ∈ row.lower) (j : Fin 2)
    (E : Finset (Fin M)) (haE : a ∉ E) (v : ℝ)
    (hb0 : ∀k,0 ≤ lowerBids row b k) (hbT : ∀k,lowerBids row b k ≤ t i)
    (hclear : remainingDemand (xi i) (lowerBids row b) E z=(small row:ℝ)) :
    (conditionalCompletion (xi i) (small row) (lowerBids row b) E).expect
      (fun P => (v-b a)*routeIndicator j a (orient row P))=routeProduct i v z (b a) := by
  rw [conditionalCompletion_eq_literal (xi_range i).1 (xi_range i).2 hz (t_pos i).le
    hreceipt (small row) (lowerBids row b) E hb0 hbT hclear,FiniteLaw.expect_const_mul]
  have hs := (Literal.completion_implements (xi_range i).1 hz
    (lowerBids row b) E (small row) hclear).2 a
  have hl := (Literal.largeCompletion_implements (xi_range i).1 hz
    (lowerBids row b) E (small row) hclear).2 a
  have hs' : (Literal.completion (xi i) z (lowerBids row b) E).expect (indicator a)=
      exposure (xi i) z (b a) := by
    change (Literal.completion (xi i) z (lowerBids row b) E).expect
      (fun S=>if a∈S then 1 else 0)=_
    have h := (FiniteLaw.prob_eq_expect _ _).symm.trans hs
    simpa only [smallMarginal,if_neg haE,lowerBids_of_mem row b ha] using h
  have hl' : (Literal.largeCompletion (xi i) z (lowerBids row b) E).expect (indicator a)=
      exposure (xi i) z (b a) := by
    change (Literal.largeCompletion (xi i) z (lowerBids row b) E).expect
      (fun S=>if a∈S then 1 else 0)=_
    have h := (FiniteLaw.prob_eq_expect _ _).symm.trans hl
    simpa only [largeMarginal,if_neg haE,lowerBids_of_mem row b ha] using h
  have h0 : (Literal.conditionalCompletion (xi i) z (lowerBids row b) E).expect
      (fun P => indicator a P.1)=exposure (xi i) z (b a) := by
    rw [Literal.conditionalCompletion,FiniteLaw.expect_prod]
    simp only [FiniteLaw.expect_const,hl']
  have h1 : (Literal.conditionalCompletion (xi i) z (lowerBids row b) E).expect
      (fun P => indicator a P.2)=exposure (xi i) z (b a) := by
    rw [Literal.conditionalCompletion,FiniteLaw.expect_prod]
    simp only [hs',FiniteLaw.expect_const]
  by_cases hj : j=0 <;> by_cases ho : residual row 0< residual row 1 <;>
    simp only [routeIndicator,orient,hj,ho,if_true,if_false,h0,h1,routeProduct]

theorem route_root_error (i : Row) (G : RestrictedLaw i) {v b z δ : ℝ}
    (hv : v ∈ Icc (0:ℝ) (t i)) (hb : b ∈ Icc (0:ℝ) (t i))
    (hreceipt : kappa i*t i ≤ rootLo i G) (hz : rootLo i G ≤ z) (hδ : 0 ≤ δ)
    (hdist : |z-G.multiplier| ≤ (16*xi i*cap i/meanResidual i)*δ) :
    |routeProduct i v z b-routeProduct i v G.multiplier b| ≤ errorConstant i*δ := by
  have hr := rootBounds i G
  have ht := t_pos i
  have hxi := (xi_range i).1
  have hU := cap_pos i
  have hq := meanResidual_pos i
  have hlo : t i/2 ≤ rootLo i G := by
    have hh := (le_max_right _ _).trans_lt (shifted_multiplier_guards i G)
    dsimp [rootLo]
    linarith
  have hL : rootLo i G ≤ G.multiplier := by dsimp [rootLo]; linarith [guardRadius_pos i]
  have hp := exposure_abs_sub_z (xi_range i).1 (xi_range i).2 hr.1 hreceipt hb.2 hz hL
  have hvb : |v-b| ≤ t i := abs_le.mpr ⟨by linarith [hv.1,hb.2],by linarith [hv.2,hb.1]⟩
  have hp' : |exposure (xi i) z b-exposure (xi i) G.multiplier b| ≤
      ((16*xi i*cap i/meanResidual i)*δ)/(xi i*(t i/2)) := by
    calc
      _ ≤ |z-G.multiplier| /(xi i*rootLo i G) := hp
      _ ≤ ((16*xi i*cap i/meanResidual i)*δ)/(xi i*rootLo i G) :=
        div_le_div_of_nonneg_right hdist (mul_nonneg hxi.le hr.1.le)
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hlo hxi.le)
  have he : routeProduct i v z b-routeProduct i v G.multiplier b=
      (v-b)*(exposure (xi i) z b-exposure (xi i) G.multiplier b) := by unfold routeProduct; ring
  rw [he,abs_mul]
  calc
    _ ≤ t i*(((16*xi i*cap i/meanResidual i)*δ)/(xi i*(t i/2))) :=
      mul_le_mul hvb hp' (abs_nonneg _) ht.le
    _ = (32*cap i/meanResidual i)*δ := by field_simp [ht.ne',hxi.ne',hq.ne']; ring
    _ ≤ _ := by
      unfold errorConstant
      have hC : 32*cap i/meanResidual i ≤ 128*cap i/meanResidual i := by
        apply div_le_div_of_nonneg_right _ hq.le
        nlinarith
      exact mul_le_mul_of_nonneg_right hC hδ

theorem row_route_menu_error {M : ℕ} [NeZero M]
    (i : Row) (G : RestrictedLaw i) (row : CountRow M) (b : Fin M → ℝ)
    (a : Fin M) (ha : a ∈ row.lower) (j : Fin 2)
    (hmask : lowerBids row b=b) (hzero : b a=0)
    (hb : ∀k ∈ row.lower,b k ∈ Icc (0:ℝ) (cap i)) {own v δ : ℝ}
    (hown : own ∈ Icc (0:ℝ) (t i)) (hv : v ∈ Icc (0:ℝ) (t i))
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ commonGuardMargin i) (hinv : 1/(M:ℝ) ≤ δ)
    (hguard : guardAlpha i G row b=1) (hnew : alpha i G row (Function.update b a own) a=1)
    (hd : |(small row:ℝ)/M-meanResidual i| ≤ 2*δ)
    (hD : (imbalance row:ℝ)/M ≤ 4*δ)
    (hcentral : |centralDemand i G row b/M-meanResidual i| ≤ δ) :
    |rowRoutePayoff i G row j v (Function.update b a own) a-
      routeProduct i v G.multiplier own| ≤ errorConstant i*δ := by
  let b' := Function.update b a own
  have hw : weight i G row b' a=sourceWeights i G row b := by
    unfold weight
    rw [ordinary_update row b a ha hmask hzero own]
  have hapos : 0 < alpha i G row b' a := by rw [hnew]; norm_num
  have hb' (k : Fin M) (hk : k ∈ row.lower) (hka : k ≠ a) : b' k ≤ cap i := by
    simpa only [b',Function.update_of_ne hka] using (hb k hk).2
  have hg := guarded_new_state i G row b' a ha hb' hapos
  have hdata := alpha_pos_data i G row b' a hapos
  have hb0' (k : Fin M) : 0 ≤ lowerBids row b' k := by
    rw [lowerBids_update row b a ha own,hmask]
    by_cases hka : k=a
    · simpa [hka] using hown.1
    · by_cases hk : k ∈ row.lower
      · simpa only [Function.update_of_ne hka] using (hb k hk).1
      · have hz : b k=0 := by simpa [lowerBids,hk] using (congrFun hmask k).symm
        simp [Function.update_of_ne hka,hz]
  change |(continuationLaw i G row b' a).expect (fun P => (v-b' a)*routeIndicator j a P)-
    routeProduct i v G.multiplier own| ≤ _
  rw [show b' a=own by simp [b']]
  apply row_test_error i G row b' a (fun P => (v-own)*routeIndicator j a P)
    (routeProduct i v G.multiplier own) (errorConstant i*δ) hnew
  intro p hp
  have hp0 : 0 < (pathLaw (sourceWeights i G row b) (imbalance row) ∅).mass p := by
    simpa only [hw] using hp
  obtain ⟨hc,haE,hz,hclear,hsel⟩ := guarded_path i G row b' a ha hb' hapos p hp
  have he := conditional_route_payoff i ((rootBounds i G).1.trans_le hz.1)
    (hdata.2.1.trans hz.1) row b' a ha j _ haE v hb0' hg.1.1 hclear
  have hd' := path_root_error i G row b a ha hmask hzero hb hδ0 hδ hinv hguard hnew
    hd hD hcentral p hp0
  have herr := route_root_error i G hv hown hdata.2.1 hz.1 hδ0 hd'
  simp only [b',Function.update_self] at he
  rw [he]
  exact herr

theorem observed_route_menu_error {M : ℕ} [NeZero M]
    (i : Row) (G : RestrictedLaw i) (x : Fin M → Observation i)
    (a : Fin M) (ha : a ∈ (observationCountRow i x).lower)
    (hzero : observationBid i (x a)=0) (j : Fin 2) {v own δ : ℝ}
    (hv : v ∈ Icc (0:ℝ) (t i)) (hown : own ∈ Icc (0:ℝ) (t i))
    (hreceipt : kappa i*t i ≤ rootLo i G)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ commonGuardMargin i) (hsize : 4/(M:ℝ) ≤ δ)
    (hc : |(Uniform07.capacity M:ℝ)/M-rho| ≤ δ) (hx : MenuGood i G δ x) :
    |rowRoutePayoff i G (observationCountRow i x) j v
      (Function.update (fun k => observationBid i (x k)) a own) a-
        routeProduct i v G.multiplier own| ≤ errorConstant i*δ := by
  let row := observationCountRow i x
  let b := fun k => observationBid i (x k)
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hMr : 0 < (M:ℝ) := Nat.cast_pos.mpr hM
  have hinv : 1/(M:ℝ) ≤ δ :=
    (div_le_div_of_nonneg_right (by norm_num : (1:ℝ)≤4) hMr.le).trans hsize
  have hMδ : (4:ℝ) ≤ δ*M := (div_le_iff₀ hMr).mp hsize
  have hMeps : 2 < commonGuardMargin i*M := by
    have h := mul_le_mul_of_nonneg_right hδ hMr.le
    linarith
  have hguard := sourceStatistic_control_guardAlpha_one i G x hM (hc.trans hδ)
    (fun k => (hx.1 k).le.trans hδ)
  have hs := sourceStatistic_sum i G x
  have hN := (hx.1 4).le
  have h0 := (hx.1 5).le
  have h1 := (hx.1 6).le
  have h7 := (hx.1 7).le
  rw [congrFun hs 4] at hN
  rw [congrFun hs 5] at h0
  rw [congrFun hs 6] at h1
  rw [congrFun hs 7] at h7
  have hseed : 1 < seedCount i row b := by
    have hm := (sourceMean_guard_bounds i G).2.2.2.2
    have hl := (abs_le.mp h7).1
    change -δ ≤ (seedCount i row b:ℝ)/M-sourceMean i G 7 at hl
    have hδt : δ < t i/200 := hδ.trans_lt (count_margin i)
    have hrate : 1/(M:ℝ) < (seedCount i row b:ℝ)/M := by linarith [t_pos i]
    have hh : (1:ℝ) < (seedCount i row b:ℝ) := (div_lt_div_iff_of_pos_right hMr).mp hrate
    exact_mod_cast hh
  have hmask := lowerBids_observation i x
  have halpha := alpha_one_of_control i G row b a ha hmask hzero hown.2
    hreceipt hMeps hseed hguard
  have hcounts := count_tolerance i row hM hδ0 hδ hc hN h0 h1
  have hcentral : |centralDemand i G row b/M-meanResidual i| ≤ δ := by
    simpa only [centralStatistic_sum] using hx.2.le
  apply row_route_menu_error i G row b a ha j hmask hzero _ hown hv hδ0 hδ hinv
    hguard halpha hcounts.1 hcounts.2 hcentral
  intro k _
  change observationBid i (x k)∈Icc (0:ℝ) (cap i)
  rcases h : x k with p | r
  · exact p.2.property
  · exact ⟨le_rfl,(cap_pos i).le⟩

def rawRouteUtility (i : Row) (N : ℕ) (G : RestrictedLaw i) (j : Fin 2)
    (v own : ℝ) : ℝ :=
  (categoryRowLaw i N).expect (fun kind =>
    ∫b : Fin N → Bid i,rowRoutePayoff i G (focalRow kind) j v (focalBids i kind own b) 0
      ∂(rowLaw N G.bidLaw : Measure (Fin N → Bid i)))

def oneRouteRawUtility (i : Row) (N : ℕ) (G : RestrictedLaw i) (v own : ℝ) : ℝ :=
  (rawRouteUtility i N G 0 v own+rawRouteUtility i N G 1 v own)/2

def numericFocalRoutePayoff (i : Row) (N : ℕ) (G : RestrictedLaw i) (j : Fin 2)
    (v own : ℝ) (x : Fin N → NumericObservation i) : ℝ :=
  rowRoutePayoff i G (countRowOfKind (Fin.cons 0 (fun k => numericKind i (x k)))) j
    v (Fin.cons own (fun k => numericBid i (x k))) 0

theorem measurable_numericFocalRoutePayoff (i : Row) (N : ℕ) (G : RestrictedLaw i)
    (j : Fin 2) (v own : ℝ) : Measurable (numericFocalRoutePayoff i N G j v own) := by
  let F : (Fin N → Fin 3) × (Fin N → ℝ) → ℝ := fun p =>
    rowRoutePayoff i G (focalRow p.1) j v (Fin.cons own p.2) 0
  have hF : Measurable F := by
    apply measurable_from_prod_countable_right
    intro kind
    have hb : Measurable (fun b : Fin N → ℝ => (Fin.cons own b : Fin (N+1)→ℝ)) := by
      apply measurable_pi_lambda
      intro k
      refine Fin.cases ?_ (fun k => ?_) k
      · exact measurable_const
      · exact measurable_pi_apply k
    exact (measurable_rowRoutePayoff i G (focalRow kind) j v 0).comp hb
  have hk : Measurable (fun x : Fin N → NumericObservation i =>
      fun k => numericKind i (x k)) :=
    measurable_pi_lambda _ (fun k =>
      (UniformFinite.measurable_numericKind i).comp (measurable_pi_apply k))
  have hb : Measurable (fun x : Fin N → NumericObservation i =>
      fun k => numericBid i (x k)) :=
    measurable_pi_lambda _ (fun k =>
      (UniformFinite.measurable_numericBid i).comp (measurable_pi_apply k))
  convert! hF.comp (hk.prodMk hb) using 1

theorem numericFocalRoutePayoff_bound (i : Row) (N : ℕ) (G : RestrictedLaw i)
    (j : Fin 2) (v own : ℝ) (x : Fin N → NumericObservation i) :
    |numericFocalRoutePayoff i N G j v own x| ≤ |v|+|own| := by
  simpa only [numericFocalRoutePayoff,Fin.cons_zero] using rowRoutePayoff_bound i G
    (countRowOfKind (Fin.cons 0 (fun k => numericKind i (x k)))) j
    v (Fin.cons own (fun k => numericBid i (x k))) 0

@[simp] theorem numericFocalRoutePayoff_encode (i : Row) (N : ℕ) (G : RestrictedLaw i)
    (j : Fin 2) (v own : ℝ) (kind : Fin N → Fin 3) (b : Fin N → Bid i) :
    numericFocalRoutePayoff i N G j v own (encodeCategoryRow i N (kind,b))=
      rowRoutePayoff i G (focalRow kind) j v (focalBids i kind own b) 0 := by
  simp [numericFocalRoutePayoff,encodeCategoryRow,focalRow,focalBids]

theorem rawRouteUtility_eq_original_observation_integral (i : Row) (N : ℕ)
    (G : RestrictedLaw i) (j : Fin 2) (v own : ℝ) :
    rawRouteUtility i N G j v own=
      ∫x,numericFocalRoutePayoff i N G j v own (fun k => dropValue i (x k))
        ∂Measure.pi (fun _ : Fin N => observationLaw i G) := by
  rw [integral_original_observation_row i G N (numericFocalRoutePayoff i N G j v own)
    (measurable_numericFocalRoutePayoff i N G j v own) _
    (numericFocalRoutePayoff_bound i N G j v own)]
  simp only [numericFocalRoutePayoff_encode,rawRouteUtility]

theorem rawRouteUtility_overbid (i : Row) (N : ℕ) (G : RestrictedLaw i)
    (j : Fin 2) {v own : ℝ} (hv : v < own) : rawRouteUtility i N G j v own ≤ 0 := by
  unfold rawRouteUtility
  apply FiniteLaw.expect_le_const
  intro kind
  apply integral_nonpos
  intro b
  exact rowRoutePayoff_overbid i G (focalRow kind) j v (focalBids i kind own b) 0
    (by simpa only [focalBids_zero] using hv)

theorem original_focalRoutePayoff_eq (i : Row) (N : ℕ) (G : RestrictedLaw i)
    (j : Fin 2) (v own : ℝ) (x : Fin N → Observation i) :
    numericFocalRoutePayoff i N G j v own (fun k => dropValue i (x k))=
      rowRoutePayoff i G
        (observationCountRow i (prepend (fun _ : Fin 1 => Sum.inl (v,zeroBid i)) x)) j
        v (Function.update
          (fun a => observationBid i (prepend (fun _ : Fin 1 => Sum.inl (v,zeroBid i)) x a))
          0 own) 0 := by
  have hk (y : Observation i) : numericKind i (dropValue i y)=observationKind i y := by
    cases y <;> rfl
  have hb (y : Observation i) : numericBid i (dropValue i y)=observationBid i y := by
    cases y <;> rfl
  simp only [numericFocalRoutePayoff,observationCountRow,prepend]
  have hkind : Fin.cons (0:Fin 3) (fun k => numericKind i (dropValue i (x k)))=
      fun k => observationKind i ((Fin.cons (Sum.inl (v,zeroBid i)) x : Fin (N+1)→Observation i) k) := by
    funext k
    refine Fin.cases ?_ (fun k => ?_) k
    · rfl
    · exact hk (x k)
  have hbids : Fin.cons own (fun k => numericBid i (dropValue i (x k)))=
      Function.update (fun k => observationBid i ((Fin.cons (Sum.inl (v,zeroBid i)) x : Fin (N+1)→Observation i) k)) 0 own := by
    funext k
    refine Fin.cases ?_ (fun k => ?_) k
    · simp
    · simp only [Fin.cons_succ,Function.update_of_ne (Fin.succ_ne_zero k)]
      exact hb (x k)
  rw [hkind,hbids]

theorem routeProduct_bound (i : Row) {L v b : ℝ} (hL : 0 < L)
    (hv : v ∈ Icc (0:ℝ) (t i)) (hb : b ∈ Icc (0:ℝ) (t i)) :
    |routeProduct i v L b| ≤ t i := by
  have hp0 := exposure_nonneg (xi_range i).1 hL (b:=b)
  have hp1 := exposure_le_one (xi i) L b
  have hvb : |v-b| ≤ t i := abs_le.mpr ⟨by linarith [hv.1,hb.2],by linarith [hv.2,hb.1]⟩
  rw [routeProduct,abs_mul,abs_of_nonneg hp0]
  simpa only [mul_one] using mul_le_mul hvb hp1 hp0 (t_pos i).le

theorem rawRouteUtility_product_error (i : Row) (N : ℕ) (G : RestrictedLaw i)
    (j : Fin 2) {v own δ : ℝ} (hv : v ∈ Icc (0:ℝ) (t i)) (hown : own ∈ Icc (0:ℝ) (t i))
    (hreceipt : kappa i*t i ≤ rootLo i G) (hN : 0 < N)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ commonGuardMargin i)
    (hsize : 4/((N+1:ℕ):ℝ) ≤ δ) (hroom : (1:ℝ) ≤ N*δ/2) :
    |rawRouteUtility i N G j v own-routeProduct i v G.multiplier own| ≤
      errorConstant i*δ+108*t i*Real.exp (-(N:ℝ)*δ^2/2) := by
  let μ := Measure.pi (fun _ : Fin N => observationLaw i G)
  let p : Fin 1 → Observation i := fun _ => Sum.inl (v,zeroBid i)
  let f : (Fin N → Observation i) → ℝ := fun x =>
    numericFocalRoutePayoff i N G j v own (fun a => dropValue i (x a))
  let u := routeProduct i v G.multiplier own
  let E : Set (Fin N → Observation i) := {x | ¬MenuGood i G δ (prepend p x)}
  let Q := E.indicator (fun _ => (1:ℝ))
  have hE : MeasurableSet E :=
    ((measurableSet_menuGood i G δ).preimage (measurable_prepend p)).compl
  have hQ : Integrable Q μ := (integrable_const (1:ℝ)).indicator hE
  have hQmean : (∫x,Q x ∂μ)=μ.real E := integral_indicator_one hE
  have hf : Measurable f := (measurable_numericFocalRoutePayoff i N G j v own).comp
    (measurable_pi_lambda _ (fun a => (measurable_dropValue i).comp (measurable_pi_apply a)))
  have ht := t_pos i
  have hfun (x : Fin N → Observation i) : |f x| ≤ 3*t i := by
    have h := numericFocalRoutePayoff_bound i N G j v own (fun a => dropValue i (x a))
    rw [abs_of_nonneg hv.1,abs_of_nonneg hown.1] at h
    change |f x| ≤ _ at h
    linarith [hv.2,hown.2]
  have hu : |u| ≤ 3*t i := (routeProduct_bound i
    ((demandLo_pos i).trans G.multiplier_guards.1) hv hown).trans (by linarith)
  have hD : 0 ≤ errorConstant i*δ := mul_nonneg (errorConstant_pos i).le hδ0
  have hinv : 1/((N+1:ℕ):ℝ) ≤ δ :=
    (div_le_div_of_nonneg_right (by norm_num : (1:ℝ)≤4)
      (Nat.cast_nonneg (N+1))).trans hsize
  have hpoint : ∀x, |f x-u| ≤ 6*t i*Q x+errorConstant i*δ := by
    intro x
    by_cases hx : MenuGood i G δ (prepend p x)
    · have hmem : (0:Fin (N+1)) ∈ (observationCountRow i (prepend p x)).lower := by
        simp [observationCountRow,countRowOfKind,prepend,p,observationKind]
      have herr := observed_route_menu_error i G (prepend p x) 0 hmem (by rfl) j hv hown
        hreceipt hδ0 hδ hsize ((capacity_error_le (N+1) (by omega)).trans hinv) hx
      have hfe := original_focalRoutePayoff_eq i N G j v own x
      change f x=_ at hfe
      rw [← hfe] at herr
      have hnot : x ∉ E := fun hn => hn hx
      simpa only [Q,Set.indicator_of_notMem hnot,mul_zero,zero_add,u] using herr
    · have hfull := (abs_sub (f x) u).trans (add_le_add (hfun x) hu)
      have hmem : x ∈ E := hx
      change |f x-u| ≤ 6*t i*E.indicator (fun _=>(1:ℝ)) x+errorConstant i*δ
      rw [Set.indicator_of_mem hmem]
      simp only [mul_one]
      linarith
  have hb := integral_menu_error μ f Q u (6*t i) (errorConstant i*δ)
    hf.aestronglyMeasurable hQ (Eventually.of_forall hpoint)
  rw [hQmean] at hb
  have hfail := fixed_menu_bad_le i G p N hN hδ0 (by simpa using hroom)
  have hmul := mul_le_mul_of_nonneg_left hfail (by positivity : 0 ≤ 6*t i)
  rw [rawRouteUtility_eq_original_observation_integral]
  change |(∫x,f x ∂μ)-u| ≤ _
  apply hb.trans
  calc
    _ ≤ 6*t i*(18*Real.exp (-(N:ℝ)*δ^2/2))+errorConstant i*δ := add_le_add_left hmul _
    _ = _ := by ring

theorem uniform_route_product_menu (i : Row) {tol : ℝ} (htol : 0 < tol) :
    ∀ᶠ N : ℕ in atTop, ∀ (G : RestrictedLaw i),
      kappa i*t i ≤ rootLo i G → ∀j : Fin 2, ∀v own : ℝ,
      v ∈ Icc (0:ℝ) (t i) → own ∈ Icc (0:ℝ) (t i) →
        |rawRouteUtility i N G j v own-routeProduct i v G.multiplier own| < tol := by
  let δ := min (commonGuardMargin i) (tol/(2*errorConstant i))
  have hC := errorConstant_pos i
  have hδ : 0 < δ := lt_min (common_guard_margin i) (div_pos htol (by positivity))
  have hδle : δ ≤ commonGuardMargin i := min_le_left _ _
  have hsmall : errorConstant i*δ ≤ tol/2 := by
    have h := (le_div_iff₀ (show 0 < 2*errorConstant i by positivity)).mp
      (min_le_right (commonGuardMargin i) (tol/(2*errorConstant i)))
    dsimp [δ]
    nlinarith
  have hNat : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hroom : ∀ᶠ N : ℕ in atTop, (1:ℝ) ≤ N*δ/2 := by
    have h := (hNat.const_mul_atTop (half_pos hδ)).eventually_ge_atTop (1:ℝ)
    simpa only [mul_comm (δ/2),mul_div_assoc] using h
  have hsize : ∀ᶠ N : ℕ in atTop, 4/((N+1:ℕ):ℝ) ≤ δ := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (4:ℝ)).eventually (Iio_mem_nhds hδ)
    filter_upwards [h,eventually_gt_atTop (0:ℕ)] with N hN hN0
    exact (div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤4)
      (by exact_mod_cast hN0) (by exact_mod_cast (show N≤ N+1 by omega))).trans hN.le
  have hexp : Tendsto (fun N : ℕ => Real.exp (-(N:ℝ)*δ^2/2)) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (hNat.const_mul_atTop (show 0 < δ^2/2 by positivity))
    convert! h using 1
    funext N
    congr 1
    ring
  have htail : ∀ᶠ N : ℕ in atTop, 108*t i*Real.exp (-(N:ℝ)*δ^2/2) < tol/2 := by
    have h := hexp.const_mul (108*t i)
    simp only [mul_zero] at h
    exact h.eventually (Iio_mem_nhds (half_pos htol))
  filter_upwards [hroom,hsize,htail,eventually_gt_atTop (0:ℕ)] with N hR hS hT hN
  intro G hreceipt j v own hv hown
  have herr := rawRouteUtility_product_error i N G j hv hown hreceipt hN hδ.le hδle hS hR
  linarith

def fullRouteProduct (i : Row) (p : FullProductBox i) : ℝ :=
  routeProduct i p.1 p.2.1 p.2.2

theorem continuous_fullRouteProduct (i : Row) : Continuous (fullRouteProduct i) := by
  have hV : Continuous (fun p : FullProductBox i => (p.1:ℝ)) := by fun_prop
  have hL : Continuous (fun p : FullProductBox i => (p.2.1:ℝ)) := by fun_prop
  have hB : Continuous (fun p : FullProductBox i => (p.2.2:ℝ)) := by fun_prop
  have hp : Continuous (fun p : FullProductBox i => exposure (xi i) p.2.1 p.2.2) := by
    unfold exposure
    apply continuous_const.min
    apply (continuous_const.max (hB.sub hL)).div (continuous_const.mul (hB.max hL))
    intro p
    have hpos := (demandLo_pos i).trans_le p.2.1.property.1
    exact (mul_pos (xi_range i).1
      (hpos.trans_le (le_max_right (p.2.2:ℝ) p.2.1))).ne'
  exact (hV.sub hB).mul hp

theorem full_route_modulus (i : Row) {tol : ℝ} (htol : 0 < tol) :
    ∃ radius : ℝ, 0 < radius ∧ ∀v b : Value i, ∀L K : ProductRoot i,
      |(L:ℝ)-K| < radius → |routeProduct i v L b-routeProduct i v K b| < tol := by
  obtain ⟨radius,hr,hmod⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous (continuous_fullRouteProduct i)) tol htol
  refine ⟨radius,hr,?_⟩
  intro v b L K hL
  have hd : dist (v,(L,b)) (v,(K,b)) < radius := by
    simp only [Prod.dist_eq,dist_self,Subtype.dist_eq,Real.dist_eq]
    exact max_lt hr (max_lt hL hr)
  simpa only [Real.dist_eq,fullRouteProduct] using hmod hd

theorem uniform_source_route_menu (i : Row) {tol : ℝ} (htol : 0 < tol) :
    ∀ᶠ N : ℕ in atTop, ∀ pi : Joint i, NoisyIC i N 0 pi →
      ∀j : Fin 2, ∀v own : ℝ, v ∈ Icc (0:ℝ) (t i) → own ∈ Icc (0:ℝ) (t i) →
        |rawRouteUtility i N (restrictedLaw i (0,pi)) j v own-
          routeProduct i v (lambda i) own| < tol := by
  have ht2 := half_pos htol
  obtain ⟨radius,hr,hmod⟩ := full_route_modulus i ht2
  obtain ⟨N0,eps0,he0,hroot⟩ := noisy_multiplier_localization i hr
  filter_upwards [eventually_ge_atTop N0,eventual_receipt i,uniform_route_product_menu i ht2]
    with N hN hreceipt hmenu
  intro pi hIC j v own hv hown
  have hL := hroot N hN 0 he0.le pi hIC
  have hP := hmod (⟨v,hv⟩ : Value i) (⟨own,hown⟩ : Value i)
    (actualProductRoot i (restrictedLaw i (0,pi))) (sourceProductRoot i) hL
  have hA := hmenu (restrictedLaw i (0,pi)) (hreceipt pi hIC) j v own hv hown
  calc
    _ ≤ |rawRouteUtility i N (restrictedLaw i (0,pi)) j v own-
        routeProduct i v (restrictedLaw i (0,pi)).multiplier own|+
      |routeProduct i v (restrictedLaw i (0,pi)).multiplier own-
        routeProduct i v (lambda i) own| := abs_sub_le _ _ _
    _ < tol/2+tol/2 := add_lt_add hA hP
    _ = tol := by ring

theorem source_route_scalar_margin (i : Row) : t i < 4*xi i*lambda i := by
  have ht := t_pos i
  cases i <;> norm_num [xi,eta,lambda,x] <;> nlinarith

theorem source_route_gap_pos (i : Row) {p : Value i × Value i}
    (hp : p ∈ aboveCapBox i) :
    0 < sourceProfit i p.1-routeProduct i p.1 (lambda i) p.2 := by
  have hxi := xi_range i
  have hL := lambda_pos i
  have hv := (source_entry_lt_cap i).trans_le hp.1
  have hv0 := hL.trans hv
  have hb := (source_entry_lt_cap i).trans_le hp.2
  have hb0 := hL.trans hb
  have hsrc : sourceProfit i p.1=((p.1:ℝ)-lambda i)^2/(p.1:ℝ) :=
    activeBidAt_product hxi.1 hxi.2 hL hv
  have hS : 0 < ((p.1:ℝ)-lambda i)^2 := sq_pos_of_pos (sub_pos.mpr hv)
  by_cases hOver : (p.1:ℝ) < (p.2:ℝ)
  · have hn : routeProduct i p.1 (lambda i) p.2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hOver.le) (exposure_nonneg hxi.1 hL)
    rw [hsrc]
    linarith [div_pos hS hv0]
  · have hbv : (p.2:ℝ) ≤ (p.1:ℝ) := le_of_not_gt hOver
    have hclip : (1-xi i)*(p.2:ℝ) ≤ lambda i :=
      (mul_le_mul_of_nonneg_left p.2.property.2 (sub_pos.mpr hxi.2).le).trans
        (source_full_receipt i).le
    have hnum : ((p.1:ℝ)-p.2)*((p.2:ℝ)-lambda i) ≤ ((p.1:ℝ)-lambda i)^2/4 := by
      nlinarith [sq_nonneg (2*(p.2:ℝ)-(p.1:ℝ)-lambda i)]
    have hdenB : 0 < xi i*(p.2:ℝ) := mul_pos hxi.1 hb0
    have hdenL : 0 < 4*xi i*lambda i :=
      mul_pos (mul_pos (by norm_num) hxi.1) hL
    have hformula : routeProduct i p.1 (lambda i) p.2=
        (((p.1:ℝ)-p.2)*((p.2:ℝ)-lambda i))/(xi i*(p.2:ℝ)) := by
      rw [routeProduct,exposure_of_between hxi.1 hL hb hclip]
      field_simp [hb0.ne']
    have hquarter : routeProduct i p.1 (lambda i) p.2 ≤
        ((p.1:ℝ)-lambda i)^2/(4*xi i*lambda i) := by
      rw [hformula]
      calc
        _ ≤ (((p.1:ℝ)-lambda i)^2/4)/(xi i*(p.2:ℝ)) :=
          div_le_div_of_nonneg_right hnum hdenB.le
        _ = ((p.1:ℝ)-lambda i)^2/(4*xi i*(p.2:ℝ)) := by
          field_simp [hxi.1.ne',hb0.ne']
        _ ≤ _ := div_le_div_of_nonneg_left hS.le hdenL
          (mul_le_mul_of_nonneg_left hb.le (mul_nonneg (by norm_num) hxi.1.le))
    have hvD : (p.1:ℝ) < 4*xi i*lambda i := p.1.property.2.trans_lt (source_route_scalar_margin i)
    have hstrict : ((p.1:ℝ)-lambda i)^2/(4*xi i*lambda i) <
        ((p.1:ℝ)-lambda i)^2/(p.1:ℝ) :=
      (div_lt_div_iff₀ hdenL hv0).mpr (mul_lt_mul_of_pos_left hvD hS)
    rw [hsrc]
    exact sub_pos.mpr (hquarter.trans_lt hstrict)

theorem source_route_gap (i : Row) :
    ∃ gap : ℝ, 0 < gap ∧ ∀v b : Value i,
      cap i ≤ (v:ℝ) → cap i ≤ (b:ℝ) →
        gap ≤ sourceProfit i v-routeProduct i v (lambda i) b := by
  let f : Value i × Value i → ℝ := fun p =>
    sourceProfit i p.1-routeProduct i p.1 (lambda i) p.2
  have harg : Continuous (fun p : Value i × Value i => (p.1,(sourceProductRoot i,p.2))) :=
    continuous_fst.prodMk (continuous_const.prodMk continuous_snd)
  have hf : Continuous f := ((continuous_sourceProfit i).comp continuous_fst).sub
    ((continuous_fullRouteProduct i).comp harg)
  obtain ⟨p,hp,hmin⟩ := (isClosed_aboveCapBox i).isCompact.exists_isMinOn
    (aboveCapBox_nonempty i) hf.continuousOn
  refine ⟨f p,source_route_gap_pos i hp,?_⟩
  intro v b hv hb
  change f p≤f (v,b)
  exact hmin (show (v,b)∈aboveCapBox i from ⟨hv,hb⟩)

end FCAppendix.Affine.UniformFinite.Late.Exceptional

namespace FCAppendix.Affine.UniformFinite.Late
open Set MeasureTheory ProbabilityTheory Filter Topology
open Uniform05
open Existence.Distributional

theorem remove_cap_routes (i : Row) :
    ∀ᶠ N : ℕ in atTop, ∀ pi : Joint i, NoisyIC i N 0 pi →
      ∀ᵐp ∂(pi.1 : Measure (Value i × unitInterval)), ∀b : ℝ, cap i < b →
        ∀j : Fin 2, Exceptional.rawRouteUtility i N (restrictedLaw i (0,pi)) j p.1 b ≤
          UniformFinite.rawUtility i N (restrictedLaw i (0,pi)) p.1 (baseBid i p) := by
  obtain ⟨gap,hgap,hgapall⟩ := Exceptional.source_route_gap i
  have herr : 0 < gap/4 := by positivity
  filter_upwards [UniformFinite.uniform_source_raw_menu i herr,
    Exceptional.uniform_source_route_menu i herr] with N hmenu hexception
  intro pi hIC
  have hraw := (noisy_zero_iff_restricted_IC i N pi).mp hIC
  filter_upwards [hraw,restricted_incumbent_nonnegative i N pi hraw] with p hp hnonneg
  intro b hb j
  by_cases hbt : b ≤ t i
  · by_cases hvc : cap i ≤ (p.1:ℝ)
    · have hval := (Exceptional.source_entry_lt_cap i).trans_le hvc
      have ha := source_activeBid_feasible i hval p.1.property.2
      have hplay := hp (activeBid i p.1) ha
      have happrox := hmenu pi hIC p.1 (sourceActiveBid i p.1) p.1.property
      have hexc := hexception pi hIC j p.1 b p.1.property
        ⟨(cap_pos i).le.trans hb.le,hbt⟩
      have hgap' := hgapall p.1 (⟨b,(cap_pos i).le.trans hb.le,hbt⟩ : Value i) hvc hb.le
      have hlow := (abs_lt.mp happrox).1
      have hupp := (abs_lt.mp hexc).2
      change -(gap/4) < UniformFinite.rawUtility i N (restrictedLaw i (0,pi))
        p.1 (activeBid i p.1)-sourceProfit i p.1 at hlow
      change Exceptional.rawRouteUtility i N (restrictedLaw i (0,pi)) j p.1 b-
        Exceptional.routeProduct i p.1 (lambda i) b < gap/4 at hupp
      change gap ≤ sourceProfit i p.1-Exceptional.routeProduct i p.1 (lambda i) b at hgap'
      linarith
    · exact (Exceptional.rawRouteUtility_overbid i N (restrictedLaw i (0,pi)) j
        ((lt_of_not_ge hvc).trans hb)).trans hnonneg
  · exact (Exceptional.rawRouteUtility_overbid i N (restrictedLaw i (0,pi)) j
      (p.1.property.2.trans_lt (lt_of_not_ge hbt))).trans hnonneg

theorem remove_cap (i : Row) :
    ∀ᶠ N : ℕ in atTop, ∀ pi : Joint i, NoisyIC i N 0 pi →
      ∀ᵐp ∂(pi.1 : Measure (Value i × unitInterval)), ∀b : ℝ, cap i < b →
        (Exceptional.rawUtility i N (restrictedLaw i (0,pi)) p.1 b ≤
          UniformFinite.rawUtility i N (restrictedLaw i (0,pi)) p.1 (baseBid i p)) ∧
        (∀j : Fin 2, Exceptional.rawRouteUtility i N (restrictedLaw i (0,pi)) j p.1 b ≤
          UniformFinite.rawUtility i N (restrictedLaw i (0,pi)) p.1 (baseBid i p)) ∧
        (Exceptional.oneRouteRawUtility i N (restrictedLaw i (0,pi)) p.1 b ≤
          UniformFinite.rawUtility i N (restrictedLaw i (0,pi)) p.1 (baseBid i p)) := by
  filter_upwards [remove_cap_broadcast i,remove_cap_routes i] with N hB hR
  intro pi hIC
  filter_upwards [hB pi hIC,hR pi hIC] with p hpB hpR
  intro b hb
  refine ⟨hpB b hb,hpR b hb,?_⟩
  have h0 := hpR b hb 0
  have h1 := hpR b hb 1
  unfold Exceptional.oneRouteRawUtility
  linarith

end FCAppendix.Affine.UniformFinite.Late
