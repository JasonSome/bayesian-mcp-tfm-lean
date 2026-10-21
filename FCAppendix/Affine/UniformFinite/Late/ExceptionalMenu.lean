import FCAppendix.Affine.UniformFinite.Late.ExceptionalContinuation

set_option maxHeartbeats 600000

noncomputable section
namespace FCAppendix.Affine.UniformFinite.Late.Exceptional
open Set MeasureTheory ProbabilityTheory Filter Topology Classical
open Uniform05 Source ClippedResidual WeightedSampling
open Existence.Distributional
open scoped BigOperators

section Pointwise
variable {M : ℕ} [NeZero M]

omit [NeZero M] in
theorem lowerBids_update (row : CountRow M) (b : Fin M → ℝ)
    (a : Fin M) (ha : a ∈ row.lower) (own : ℝ) :
    lowerBids row (Function.update b a own)=Function.update (lowerBids row b) a own := by
  funext j
  by_cases hj : j=a
  · subst j
    simp [lowerBids,ha]
  · by_cases hl : j ∈ row.lower <;> simp [lowerBids,hj,hl]

omit [NeZero M] in
theorem ordinary_update (row : CountRow M) (b : Fin M → ℝ) (a : Fin M)
    (ha : a ∈ row.lower) (hmask : lowerBids row b=b) (hzero : b a=0) (own : ℝ) :
    ordinary row (Function.update b a own) a=b := by
  rw [ordinary,lowerBids_update row b a ha own,hmask]
  funext j
  by_cases hj : j=a
  · subst j
    simp [hzero]
  · simp [Function.update_of_ne hj]

omit [NeZero M] in
theorem alpha_one_of_control (i : Row) (G : RestrictedLaw i) (row : CountRow M)
    (b : Fin M → ℝ) (a : Fin M) (ha : a ∈ row.lower)
    (hmask : lowerBids row b=b) (hzero : b a=0) {own : ℝ} (hown : own ≤ t i)
    (hreceipt : kappa i*t i ≤ rootLo i G) (hsize : 2 < commonGuardMargin i*M)
    (hseed : 1 < seedCount i row b) (hguard : guardAlpha i G row b=1) :
    alpha i G row (Function.update b a own) a=1 := by
  have hs : seedCount i row b ≠ 0 := by omega
  have hraw : rawAlpha i G row b=1 := by simpa only [guardAlpha,if_neg hs] using hguard
  simp only [alpha,Function.update_self,ordinary_update row b a ha hmask hzero own]
  rw [if_pos ⟨hown,hreceipt,hsize,hseed⟩,hraw]

theorem path_root_error (i : Row) (G : RestrictedLaw i) (row : CountRow M)
    (b : Fin M → ℝ) (a : Fin M) (ha : a ∈ row.lower)
    (hmask : lowerBids row b=b) (hzero : b a=0)
    (hb : ∀j ∈ row.lower,b j ∈ Icc (0:ℝ) (cap i)) {own δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ commonGuardMargin i)
    (hinv : 1/(M:ℝ) ≤ δ) (hguard : guardAlpha i G row b=1)
    (hnew : alpha i G row (Function.update b a own) a=1)
    (hd : |(small row:ℝ)/M-meanResidual i| ≤ 2*δ)
    (hD : (imbalance row:ℝ)/M ≤ 4*δ)
    (hcentral : |centralDemand i G row b/M-meanResidual i| ≤ δ)
    (p : Path (Fin M) (imbalance row))
    (hp : 0 < (pathLaw (sourceWeights i G row b) (imbalance row) ∅).mass p) :
    let E := finalSet (imbalance row) ∅ p
    let z := Literal.root (xi i) (rootLo i G) (rootHi i G)
      (lowerBids row (Function.update b a own)) E (small row)
    |z-G.multiplier| ≤ (16*xi i*cap i/meanResidual i)*δ := by
  let b' := Function.update b a own
  let E := finalSet (imbalance row) ∅ p
  let z0 := Literal.root (xi i) (rootLo i G) (rootHi i G) b E (small row)
  let z := Literal.root (xi i) (rootLo i G) (rootHi i G) (lowerBids row b') E (small row)
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hMr : 0 < (M:ℝ) := Nat.cast_pos.mpr hM
  have hq := meanResidual_pos i
  have hxi := (xi_range i).1
  have hU := cap_pos i
  have hsmall : δ ≤ meanResidual i/100 := by
    have h := (commonGuardMargin_bounds i).2.2
    linarith
  have hden : meanResidual i*(M:ℝ)/2 ≤ (small row:ℝ)-1 := by
    have hl := (abs_le.mp hd).1
    have hhalf : meanResidual i/2 ≤ ((small row:ℝ)-1)/M := by
      rw [sub_div]
      linarith
    have h := (le_div_iff₀ hMr).mp hhalf
    nlinarith
  have hd1 : 1 < (small row:ℝ) := by nlinarith [mul_pos hq hMr]
  have heq := ordinary_update row b a ha hmask hzero own
  have hw : weight i G row b' a=sourceWeights i G row b := by
    dsimp [weight,b']
    rw [heq]
  have hapos : 0 < alpha i G row b' a := by rw [hnew]; norm_num
  have hb' (j : Fin M) (hj : j ∈ row.lower) (hja : j ≠ a) : b' j ≤ cap i := by
    simpa only [b',Function.update_of_ne hja] using (hb j hj).2
  have hp' : 0 < (pathLaw (weight i G row b' a) (imbalance row) ∅).mass p := by rw [hw]; exact hp
  obtain ⟨hc,haE,hz,hclear,hsel⟩ := guarded_path i G row b' a ha hb' hapos p hp'
  have hbasepos : 0 < guardAlpha i G row b := by rw [hguard]; norm_num
  obtain ⟨hc0,hz0,hclear0,hsel0⟩ := guarded_weighted_path_root i G row b
    (fun j hj => (hb j hj).2) hbasepos p hp
  rw [hmask] at hz0 hclear0
  have hbaseU (j : Fin M) : b j ≤ cap i := by
    by_cases hj : j ∈ row.lower
    · exact (hb j hj).2
    · have hj0 : b j=0 := by
        have h := congrFun hmask j
        simpa [lowerBids,hj] using h.symm
      simp [hj0,(cap_pos i).le]
  have hupdate : Function.update (lowerBids row b') a 0=b := heq
  have hroot := rootBounds i G
  have hshift := exceptional_focal_multiplier_shift (xi_range i).1 (xi_range i).2
    hU hroot.1 hroot.2.2 (lowerBids row b') a E haE
    (fun j => by simpa only [hupdate] using hbaseU j) (small row) hd1 hz0 hz
    (by simpa only [hupdate] using hclear0) hclear
  have hshift' : z-z0 ≤ (2*xi i*cap i/meanResidual i)*δ := by
    have hden0 : 0 < meanResidual i*(M:ℝ)/2 := by positivity
    calc
      _ ≤ xi i*cap i/((small row:ℝ)-1) := hshift.2
      _ ≤ xi i*cap i/(meanResidual i*(M:ℝ)/2) :=
        div_le_div_of_nonneg_left (mul_nonneg hxi.le hU.le) hden0 hden
      _ = (2*xi i*cap i/meanResidual i)*(1/(M:ℝ)) := by
        field_simp [hq.ne',hMr.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left hinv (by positivity)
  have hbaseerr := guarded_path_root_distance i G row b (fun j hj => (hb j hj).2)
    hbasepos hδ0 hδ hd hD hcentral p hp
  rw [hmask] at hbaseerr
  change |z0-G.multiplier| ≤ _ at hbaseerr
  change |z-G.multiplier| ≤ _
  calc
    _ ≤ |z-z0|+|z0-G.multiplier| := abs_sub_le _ _ _
    _ ≤ (2*xi i*cap i/meanResidual i)*δ+(14*xi i*cap i/meanResidual i)*δ := by
      rw [abs_of_nonneg hshift.1]
      exact add_le_add hshift' hbaseerr
    _ = _ := by ring

theorem marginal_lipschitz (i : Row) {v b p q : ℝ}
    (hv : v ∈ Icc (0:ℝ) (t i)) (hb : b ∈ Icc (0:ℝ) (t i))
    (hp : p ∈ Icc (0:ℝ) 1) (hq : q ∈ Icc (0:ℝ) 1) :
    |Source.marginalPayoff (eta i) v b p-Source.marginalPayoff (eta i) v b q| ≤
      4*t i*|p-q| := by
  have he : Source.marginalPayoff (eta i) v b p-Source.marginalPayoff (eta i) v b q=
      (v-b)*(p-q)*(2-p-q)-eta i*b*(p-q)*(p+q) := by
    unfold Source.marginalPayoff
    ring
  have hvb : |v-b| ≤ t i := abs_le.mpr ⟨by linarith [hv.1,hb.2],by linarith [hv.2,hb.1]⟩
  have hsum : |p+q| ≤ 2 := by rw [abs_of_nonneg (by linarith [hp.1,hq.1])]; linarith [hp.2,hq.2]
  have hcomp : |2-p-q| ≤ 2 := by rw [abs_of_nonneg (by linarith [hp.2,hq.2])]; linarith [hp.1,hq.1]
  have hηb : eta i*b ≤ t i := (mul_le_of_le_one_left hb.1 (eta_range i).2.le).trans hb.2
  rw [he]
  calc
    _ ≤ |(v-b)*(p-q)*(2-p-q)|+|eta i*b*(p-q)*(p+q)| := abs_sub _ _
    _ = |v-b| *|p-q| *|2-p-q|+eta i*b*|p-q| *|p+q| := by
      simp only [abs_mul,abs_of_nonneg (eta_range i).1.le,abs_of_nonneg hb.1]
    _ ≤ t i*|p-q| *2+t i*|p-q| *2 := by
      apply add_le_add
      · exact mul_le_mul (mul_le_mul_of_nonneg_right hvb (abs_nonneg _)) hcomp
          (abs_nonneg _) (mul_nonneg (t_pos i).le (abs_nonneg _))
      · exact mul_le_mul (mul_le_mul_of_nonneg_right hηb (abs_nonneg _)) hsum
          (abs_nonneg _) (mul_nonneg (t_pos i).le (abs_nonneg _))
    _ = _ := by ring

def errorConstant (i : Row) : ℝ := 128*cap i/meanResidual i

theorem errorConstant_pos (i : Row) : 0 < errorConstant i := by
  have hU := cap_pos i
  have hq := meanResidual_pos i
  unfold errorConstant
  positivity

theorem product_root_error (i : Row) (G : RestrictedLaw i) {v b z δ : ℝ}
    (hv : v ∈ Icc (0:ℝ) (t i)) (hb : b ∈ Icc (0:ℝ) (t i))
    (hreceipt : kappa i*t i ≤ rootLo i G) (hz : rootLo i G ≤ z) (hδ : 0 ≤ δ)
    (hdist : |z-G.multiplier| ≤ (16*xi i*cap i/meanResidual i)*δ) :
    |productPayoff (xi i) v z b-productPayoff (xi i) v G.multiplier b| ≤ errorConstant i*δ := by
  have hr := rootBounds i G
  have hlo : t i/2 ≤ rootLo i G := by
    have hh := (le_max_right _ _).trans_lt (shifted_multiplier_guards i G)
    dsimp [rootLo]
    linarith [t_pos i]
  have ht := t_pos i
  have hxi := (xi_range i).1
  have hU := cap_pos i
  have hq := meanResidual_pos i
  have hL : rootLo i G ≤ G.multiplier := by dsimp [rootLo]; linarith [guardRadius_pos i]
  have hp := exposure_abs_sub_z (xi_range i).1 (xi_range i).2 hr.1 hreceipt hb.2 hz hL
  have hden : 0 < xi i*(t i/2) := by positivity
  have hp' : |exposure (xi i) z b-exposure (xi i) G.multiplier b| ≤
      ((16*xi i*cap i/meanResidual i)*δ)/(xi i*(t i/2)) := by
    calc
      _ ≤ |z-G.multiplier| /(xi i*rootLo i G) := hp
      _ ≤ ((16*xi i*cap i/meanResidual i)*δ)/(xi i*rootLo i G) :=
        div_le_div_of_nonneg_right hdist (mul_nonneg hxi.le hr.1.le)
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hden
        (mul_le_mul_of_nonneg_left hlo hxi.le)
  rw [Source.productPayoff_eq_marginal,Source.productPayoff_eq_marginal]
  have hu := marginal_lipschitz i (p := exposure (xi i) z b)
    (q := exposure (xi i) G.multiplier b) hv hb
    ⟨exposure_nonneg hxi (hr.1.trans_le hz),exposure_le_one _ _ _⟩
    ⟨exposure_nonneg hxi (hr.1.trans_le hL),exposure_le_one _ _ _⟩
  apply hu.trans
  have h := mul_le_mul_of_nonneg_left hp' (by positivity : 0 ≤ 4*t i)
  convert! h using 1
  unfold errorConstant
  field_simp [hxi.ne',ht.ne',hq.ne']
  ring

omit [NeZero M] in
theorem conditional_payoff (i : Row) {z : ℝ} (hz : 0 < z)
    (hreceipt : kappa i*t i ≤ z) (row : CountRow M) (b : Fin M → ℝ)
    (a : Fin M) (ha : a ∈ row.lower) (E : Finset (Fin M)) (haE : a ∉ E)
    (v : ℝ) (hb0 : ∀j,0 ≤ lowerBids row b j) (hbU : ∀j,lowerBids row b j ≤ t i)
    (hclear : remainingDemand (xi i) (lowerBids row b) E z=(small row:ℝ)) :
    (conditionalCompletion (xi i) (small row) (lowerBids row b) E).expect
      (fun P => pairPayoff (eta i) v (b a) a (orient row P))=
        productPayoff (xi i) v z (b a) := by
  rw [conditionalCompletion_eq_literal (xi_range i).1 (xi_range i).2 hz (t_pos i).le
    hreceipt (small row) (lowerBids row b) E hb0 hbU hclear]
  have he (P : Allocation M) : pairPayoff (eta i) v (b a) a (orient row P)=
      (v-b a)*Literal.firstCopy a P-eta i*b a*Literal.duplicateCopy a P := by
    unfold pairPayoff
    rw [orient_success,orient_duplicate]
  simp_rw [he]
  rw [FiniteLaw.expect_sub,FiniteLaw.expect_const_mul,FiniteLaw.expect_const_mul,
    Literal.conditional_first_copy (xi_range i).1 hz (lowerBids row b) E (small row) hclear a,
    Literal.conditional_duplicate_copy (xi_range i).1 hz (lowerBids row b) E (small row) hclear a,
    if_neg haE,if_neg haE,lowerBids_of_mem row b ha]
  unfold productPayoff Uniform05.xi
  ring

theorem row_menu_error (i : Row) (G : RestrictedLaw i) (row : CountRow M)
    (b : Fin M → ℝ) (a : Fin M) (ha : a ∈ row.lower)
    (hmask : lowerBids row b=b) (hzero : b a=0)
    (hb : ∀j ∈ row.lower,b j ∈ Icc (0:ℝ) (cap i)) {own v δ : ℝ}
    (hown : own ∈ Icc (0:ℝ) (t i)) (hv : v ∈ Icc (0:ℝ) (t i))
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ commonGuardMargin i) (hinv : 1/(M:ℝ) ≤ δ)
    (hguard : guardAlpha i G row b=1) (hnew : alpha i G row (Function.update b a own) a=1)
    (hd : |(small row:ℝ)/M-meanResidual i| ≤ 2*δ)
    (hD : (imbalance row:ℝ)/M ≤ 4*δ)
    (hcentral : |centralDemand i G row b/M-meanResidual i| ≤ δ) :
    |rowPayoff i G row v (Function.update b a own) a-
      productPayoff (xi i) v G.multiplier own| ≤ errorConstant i*δ := by
  let b' := Function.update b a own
  let P := pathLaw (sourceWeights i G row b) (imbalance row) ∅
  let f := fun p : Path (Fin M) (imbalance row) =>
    (conditionalCompletion (xi i) (small row) (lowerBids row b')
      (finalSet (imbalance row) ∅ p)).expect (fun out => pairPayoff (eta i) v own a (orient row out))
  let u := productPayoff (xi i) v G.multiplier own
  have hw : weight i G row b' a=sourceWeights i G row b := by
    unfold weight
    rw [ordinary_update row b a ha hmask hzero own]
  have hapos : 0 < alpha i G row b' a := by rw [hnew]; norm_num
  have hb' (j : Fin M) (hj : j ∈ row.lower) (hja : j ≠ a) : b' j ≤ cap i := by
    simpa only [b',Function.update_of_ne hja] using (hb j hj).2
  have hg := guarded_new_state i G row b' a ha hb' hapos
  have hdata := alpha_pos_data i G row b' a hapos
  have hb0' (j : Fin M) : 0 ≤ lowerBids row b' j := by
    rw [lowerBids_update row b a ha own,hmask]
    by_cases hja : j=a
    · simpa [hja] using hown.1
    · by_cases hj : j ∈ row.lower
      · simpa only [Function.update_of_ne hja] using (hb j hj).1
      · have hz : b j=0 := by simpa [lowerBids,hj] using (congrFun hmask j).symm
        simp [Function.update_of_ne hja,hz]
  have hpoint : ∀p,0 < P.mass p → |f p-u| ≤ errorConstant i*δ := by
    intro p hp
    have hp' : 0 < (pathLaw (weight i G row b' a) (imbalance row) ∅).mass p := by rw [hw]; exact hp
    obtain ⟨hc,haE,hz,hclear,hsel⟩ := guarded_path i G row b' a ha hb' hapos p hp'
    let z := Literal.root (xi i) (rootLo i G) (rootHi i G) (lowerBids row b')
      (finalSet (imbalance row) ∅ p) (small row)
    have he := conditional_payoff i ((rootBounds i G).1.trans_le hz.1)
      (hdata.2.1.trans hz.1) row b' a ha _ haE v hb0' hg.1.1 hclear
    have herr := path_root_error i G row b a ha hmask hzero hb hδ0 hδ hinv hguard hnew
      hd hD hcentral p hp
    have hu := product_root_error i G hv hown hdata.2.1 hz.1 hδ0 herr
    dsimp only [f,u,b',Function.update_self]
    dsimp only [b'] at he
    simp only [Function.update_self] at he
    rw [he]
    exact hu
  have hc : (canonicalLaw i G row b' a).expect (pairPayoff (eta i) v own a)=P.expect f := by
    rw [canonicalLaw,FiniteLaw.expect_map,WeightedSampling.expect_pairLaw,hw]
  have hr : rowPayoff i G row v b' a=P.expect f := by
    unfold rowPayoff continuationLaw
    by_cases heq : residual row 0=residual row 1
    · rw [if_pos heq,← canonicalLaw_equal i G row b' a heq]
      simpa only [b',Function.update_self] using hc
    · rw [if_neg heq,FiniteLaw.expect_mixture,hnew]
      simpa only [one_mul,sub_self,zero_mul,add_zero,b',Function.update_self] using hc
  rw [hr]
  change |P.expect f-u| ≤ _
  rw [← P.expect_const u,← FiniteLaw.expect_sub]
  apply (WeightedSampling.abs_expect_le P _).trans
  exact WeightedSampling.expect_le_const P _ _ hpoint

end Pointwise

theorem observed_menu_error {M : ℕ} [NeZero M]
    (i : Row) (G : RestrictedLaw i) (x : Fin M → Observation i)
    (a : Fin M) (ha : a ∈ (observationCountRow i x).lower)
    (hzero : observationBid i (x a)=0) {v own δ : ℝ}
    (hv : v ∈ Icc (0:ℝ) (t i)) (hown : own ∈ Icc (0:ℝ) (t i))
    (hreceipt : kappa i*t i ≤ rootLo i G)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ commonGuardMargin i) (hsize : 4/(M:ℝ) ≤ δ)
    (hc : |(Uniform07.capacity M:ℝ)/M-rho| ≤ δ) (hx : MenuGood i G δ x) :
    |rowPayoff i G (observationCountRow i x) v
      (Function.update (fun j => observationBid i (x j)) a own) a-
        productPayoff (xi i) v G.multiplier own| ≤ errorConstant i*δ := by
  let row := observationCountRow i x
  let b := fun j => observationBid i (x j)
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
    have he := count_margin i
    have hl := (abs_le.mp h7).1
    change -δ ≤ (seedCount i row b:ℝ)/M-sourceMean i G 7 at hl
    have hδt : δ < t i/200 := hδ.trans_lt he
    have hrate : 1/(M:ℝ) < (seedCount i row b:ℝ)/M := by
      have ht := t_pos i
      linarith
    have hh : (1:ℝ) < (seedCount i row b:ℝ) := (div_lt_div_iff_of_pos_right hMr).mp hrate
    exact_mod_cast hh
  have hmask := lowerBids_observation i x
  have halpha := alpha_one_of_control i G row b a ha hmask hzero hown.2
    hreceipt hMeps hseed hguard
  have hcounts := count_tolerance i row hM hδ0 hδ hc hN h0 h1
  have hcentral : |centralDemand i G row b/M-meanResidual i| ≤ δ := by
    simpa only [centralStatistic_sum] using hx.2.le
  apply row_menu_error i G row b a ha hmask hzero _ hown hv hδ0 hδ hinv
    hguard halpha hcounts.1 hcounts.2 hcentral
  intro j _
  rcases h : x j with p | k
  · simp [b,observationBid,h]
  · simp [b,observationBid,h,(cap_pos i).le]

def rawUtility (i : Row) (N : ℕ) (G : RestrictedLaw i) (v own : ℝ) : ℝ :=
  (categoryRowLaw i N).expect (fun kind =>
    ∫b : Fin N → Bid i, rowPayoff i G (focalRow kind) v (focalBids i kind own b) 0
      ∂(rowLaw N G.bidLaw : Measure (Fin N → Bid i)))

def numericFocalPayoff (i : Row) (N : ℕ) (G : RestrictedLaw i)
    (v own : ℝ) (x : Fin N → NumericObservation i) : ℝ :=
  rowPayoff i G (countRowOfKind (Fin.cons 0 (fun j => numericKind i (x j))))
    v (Fin.cons own (fun j => numericBid i (x j))) 0

theorem measurable_numericFocalPayoff (i : Row) (N : ℕ) (G : RestrictedLaw i)
    (v own : ℝ) : Measurable (numericFocalPayoff i N G v own) := by
  let F : (Fin N → Fin 3) × (Fin N → ℝ) → ℝ := fun p =>
    rowPayoff i G (focalRow p.1) v (Fin.cons own p.2) 0
  have hF : Measurable F := by
    apply measurable_from_prod_countable_right
    intro kind
    have hb : Measurable (fun b : Fin N → ℝ => (Fin.cons own b : Fin (N+1) → ℝ)) := by
      apply measurable_pi_lambda
      intro a
      refine Fin.cases ?_ (fun j => ?_) a
      · exact measurable_const
      · exact measurable_pi_apply j
    convert! (measurable_rowPayoff i G (focalRow kind) v 0).comp hb using 1
  have hk : Measurable (fun x : Fin N → NumericObservation i =>
      fun j => numericKind i (x j)) :=
    measurable_pi_lambda _ (fun j =>
      (UniformFinite.measurable_numericKind i).comp (measurable_pi_apply j))
  have hb : Measurable (fun x : Fin N → NumericObservation i =>
      fun j => numericBid i (x j)) :=
    measurable_pi_lambda _ (fun j =>
      (UniformFinite.measurable_numericBid i).comp (measurable_pi_apply j))
  convert! hF.comp (hk.prodMk hb) using 1

theorem numericFocalPayoff_bound (i : Row) (N : ℕ) (G : RestrictedLaw i)
    (v own : ℝ) (x : Fin N → NumericObservation i) :
    |numericFocalPayoff i N G v own x| ≤ |v|+(1+|eta i|)*|own| := by
  simpa only [numericFocalPayoff,Fin.cons_zero] using rowPayoff_bound i G
    (countRowOfKind (Fin.cons 0 (fun j => numericKind i (x j))))
    v (Fin.cons own (fun j => numericBid i (x j))) 0

@[simp] theorem numericFocalPayoff_encode (i : Row) (N : ℕ) (G : RestrictedLaw i)
    (v own : ℝ) (kind : Fin N → Fin 3) (b : Fin N → Bid i) :
    numericFocalPayoff i N G v own (encodeCategoryRow i N (kind,b))=
      rowPayoff i G (focalRow kind) v (focalBids i kind own b) 0 := by
  simp [numericFocalPayoff,encodeCategoryRow,focalRow,focalBids]

theorem rawUtility_eq_original_observation_integral (i : Row) (N : ℕ)
    (G : RestrictedLaw i) (v own : ℝ) :
    rawUtility i N G v own=
      ∫x,numericFocalPayoff i N G v own (fun j => dropValue i (x j))
        ∂Measure.pi (fun _ : Fin N => observationLaw i G) := by
  rw [integral_original_observation_row i G N (numericFocalPayoff i N G v own)
    (measurable_numericFocalPayoff i N G v own) _
    (numericFocalPayoff_bound i N G v own)]
  simp only [numericFocalPayoff_encode,rawUtility]

theorem rawUtility_bound (i : Row) (N : ℕ) (G : RestrictedLaw i) (v own : ℝ) :
    |rawUtility i N G v own| ≤ |v|+(1+|eta i|)*|own| := by
  rw [rawUtility_eq_original_observation_integral]
  have hb : ∀ᵐ x : Fin N → Observation i
      ∂Measure.pi (fun _ : Fin N => observationLaw i G),
      ‖numericFocalPayoff i N G v own (fun j => dropValue i (x j))‖ ≤
        |v|+(1+|eta i|)*|own| := by
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs] using
      numericFocalPayoff_bound i N G v own (fun j => dropValue i (x j))
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const hb

theorem rawUtility_overbid (i : Row) (N : ℕ) (G : RestrictedLaw i)
    {v own : ℝ} (hv0 : 0 ≤ v) (hv : v < own) : rawUtility i N G v own ≤ 0 := by
  unfold rawUtility
  apply FiniteLaw.expect_le_const
  intro kind
  apply integral_nonpos
  intro b
  exact rowPayoff_overbid i G (focalRow kind) v (focalBids i kind own b) 0 hv0
    (by simpa only [focalBids_zero] using hv)

def zeroBid (i : Row) : Bid i := ⟨0,le_rfl,(cap_pos i).le⟩

theorem original_focalPayoff_eq (i : Row) (N : ℕ) (G : RestrictedLaw i)
    (v own : ℝ) (x : Fin N → Observation i) :
    numericFocalPayoff i N G v own (fun j => dropValue i (x j))=
      rowPayoff i G
        (observationCountRow i (prepend (fun _ : Fin 1 => Sum.inl (v,zeroBid i)) x))
        v (Function.update
          (fun a => observationBid i (prepend (fun _ : Fin 1 => Sum.inl (v,zeroBid i)) x a))
          0 own) 0 := by
  have hk (y : Observation i) : numericKind i (dropValue i y)=observationKind i y := by
    cases y <;> rfl
  have hb (y : Observation i) : numericBid i (dropValue i y)=observationBid i y := by
    cases y <;> rfl
  simp only [numericFocalPayoff,observationCountRow,prepend]
  have hkind : Fin.cons (0:Fin 3) (fun j => numericKind i (dropValue i (x j)))=
      fun j => observationKind i ((Fin.cons (Sum.inl (v,zeroBid i)) x : Fin (N+1) → Observation i) j) := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · exact hk (x j)
  have hbids : Fin.cons own (fun j => numericBid i (dropValue i (x j)))=
      Function.update (fun j => observationBid i ((Fin.cons (Sum.inl (v,zeroBid i)) x : Fin (N+1) → Observation i) j)) 0 own := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · simp only [Fin.cons_succ,Function.update_of_ne (Fin.succ_ne_zero j)]
      exact hb (x j)
  rw [hkind,hbids]

theorem productPayoff_bound (i : Row) {L v b : ℝ} (hL : 0 < L)
    (hv : v ∈ Icc (0:ℝ) (t i)) (hb : b ∈ Icc (0:ℝ) (t i)) :
    |productPayoff (xi i) v L b| ≤ 3*t i := by
  let p := exposure (xi i) L b
  have hp0 : 0 ≤ p := exposure_nonneg (xi_range i).1 hL
  have hp1 : p ≤ 1 := exposure_le_one _ _ _
  have hs0 : 0 ≤ 2*p-p^2 := by nlinarith
  have hs1 : 2*p-p^2 ≤ 1 := by nlinarith [sq_nonneg (1-p)]
  have hp2 : p^2 ≤ 1 := by nlinarith
  have hvb : |v-b| ≤ t i :=
    abs_le.mpr ⟨by linarith [hv.1,hb.2],by linarith [hv.2,hb.1]⟩
  have heta : 0 ≤ eta i*b := mul_nonneg (eta_range i).1.le hb.1
  have heta' : eta i*b ≤ t i :=
    (mul_le_of_le_one_left hb.1 (eta_range i).2.le).trans hb.2
  rw [Source.productPayoff_eq_marginal]
  change |(v-b)*(2*p-p^2)-eta i*b*p^2| ≤ _
  calc
    _ ≤ |(v-b)*(2*p-p^2)|+|eta i*b*p^2| := abs_sub _ _
    _ = |v-b| *(2*p-p^2)+eta i*b*p^2 := by
      rw [abs_mul,abs_of_nonneg hs0,abs_of_nonneg (mul_nonneg heta (sq_nonneg p))]
    _ ≤ t i*1+t i*1 := by
      exact add_le_add (mul_le_mul hvb hs1 hs0 (t_pos i).le)
        (mul_le_mul heta' hp2 (sq_nonneg p) (t_pos i).le)
    _ ≤ _ := by linarith [t_pos i]

theorem integral_menu_error {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f Q : α → ℝ) (u C D : ℝ)
    (hf : AEStronglyMeasurable f μ) (hQ : Integrable Q μ)
    (h : ∀ᵐ x ∂μ, |f x-u| ≤ C*Q x+D) :
    |(∫x,f x ∂μ)-u| ≤ C*(∫x,Q x ∂μ)+D := by
  have hdom : Integrable (fun x => C*Q x+D) μ := (hQ.const_mul C).add (integrable_const D)
  have hdiff : Integrable (fun x => f x-u) μ := hdom.mono'
    (hf.sub aestronglyMeasurable_const) (by simpa only [Real.norm_eq_abs] using h)
  have hfi : Integrable f μ := by
    have he : (fun x => f x-u+u)=f := by funext x; ring
    exact he ▸ hdiff.add (integrable_const u)
  have he : (∫x,f x-u ∂μ)=(∫x,f x ∂μ)-u := by
    rw [integral_sub hfi (integrable_const u),integral_const,probReal_univ,one_smul]
  rw [← he]
  apply abs_integral_le_integral_abs.trans
  have hh := integral_mono_ae hdiff.abs hdom h
  rwa [integral_add (hQ.const_mul C) (integrable_const D),integral_const_mul,
    integral_const,probReal_univ,one_smul] at hh

theorem rawUtility_product_error (i : Row) (N : ℕ) (G : RestrictedLaw i)
    {v own δ : ℝ} (hv : v ∈ Icc (0:ℝ) (t i)) (hown : own ∈ Icc (0:ℝ) (t i))
    (hreceipt : kappa i*t i ≤ rootLo i G) (hN : 0 < N)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ commonGuardMargin i)
    (hsize : 4/((N+1:ℕ):ℝ) ≤ δ) (hroom : (1:ℝ) ≤ N*δ/2) :
    |rawUtility i N G v own-productPayoff (xi i) v G.multiplier own| ≤
      errorConstant i*δ+108*t i*Real.exp (-(N:ℝ)*δ^2/2) := by
  let μ := Measure.pi (fun _ : Fin N => observationLaw i G)
  let p : Fin 1 → Observation i := fun _ => Sum.inl (v,zeroBid i)
  let f : (Fin N → Observation i) → ℝ := fun x =>
    numericFocalPayoff i N G v own (fun a => dropValue i (x a))
  let u := productPayoff (xi i) v G.multiplier own
  let E : Set (Fin N → Observation i) := {x | ¬MenuGood i G δ (prepend p x)}
  let Q := E.indicator (fun _ => (1:ℝ))
  have hE : MeasurableSet E :=
    ((measurableSet_menuGood i G δ).preimage (measurable_prepend p)).compl
  have hQ : Integrable Q μ := (integrable_const (1:ℝ)).indicator hE
  have hQmean : (∫x,Q x ∂μ)=μ.real E := integral_indicator_one hE
  have hf : Measurable f := (measurable_numericFocalPayoff i N G v own).comp
    (measurable_pi_lambda _ (fun a => (measurable_dropValue i).comp (measurable_pi_apply a)))
  have hη := eta_range i
  have ht := t_pos i
  have hfun (x : Fin N → Observation i) : |f x| ≤ 3*t i := by
    have h := numericFocalPayoff_bound i N G v own (fun a => dropValue i (x a))
    rw [abs_of_nonneg hv.1,abs_of_nonneg hown.1,abs_of_nonneg hη.1.le] at h
    have hh := mul_le_mul_of_nonneg_right (show 1+eta i ≤ 2 by linarith [hη.2]) hown.1
    change |f x| ≤ _ at h
    nlinarith [hv.2,hown.2]
  have hu : |u| ≤ 3*t i := productPayoff_bound i
    ((demandLo_pos i).trans G.multiplier_guards.1) hv hown
  have hD : 0 ≤ errorConstant i*δ := mul_nonneg (errorConstant_pos i).le hδ0
  have hinv : 1/((N+1:ℕ):ℝ) ≤ δ :=
    (div_le_div_of_nonneg_right (by norm_num : (1:ℝ)≤4)
      (Nat.cast_nonneg (N+1))).trans hsize
  have hpoint : ∀x, |f x-u| ≤ 6*t i*Q x+errorConstant i*δ := by
    intro x
    by_cases hx : MenuGood i G δ (prepend p x)
    · have hmem : (0:Fin (N+1)) ∈ (observationCountRow i (prepend p x)).lower := by
        simp [observationCountRow,countRowOfKind,prepend,p,observationKind]
      have herr := observed_menu_error i G (prepend p x) 0 hmem (by rfl) hv hown
        hreceipt hδ0 hδ hsize ((capacity_error_le (N+1) (by omega)).trans hinv) hx
      have hfe := original_focalPayoff_eq i N G v own x
      change f x=_ at hfe
      rw [← hfe] at herr
      have hnot : x ∉ E := fun hn => hn hx
      simpa only [Q,Set.indicator_of_notMem hnot,mul_zero,zero_add,u] using herr
    · have hfull := (abs_sub (f x) u).trans (add_le_add (hfun x) hu)
      have hmem : x ∈ E := hx
      dsimp only [Q]
      rw [Set.indicator_of_mem hmem]
      simp only [mul_one]
      linarith
  have hb := integral_menu_error μ f Q u (6*t i) (errorConstant i*δ)
    hf.aestronglyMeasurable hQ (Eventually.of_forall hpoint)
  rw [hQmean] at hb
  have hfail := fixed_menu_bad_le i G p N hN hδ0 (by simpa using hroom)
  have hmul := mul_le_mul_of_nonneg_left hfail (by positivity : 0 ≤ 6*t i)
  rw [rawUtility_eq_original_observation_integral]
  change |(∫x,f x ∂μ)-u| ≤ _
  apply hb.trans
  calc
    _ ≤ 6*t i*(18*Real.exp (-(N:ℝ)*δ^2/2))+errorConstant i*δ := by
      linarith [hmul]
    _ = _ := by ring

theorem uniform_product_menu (i : Row) {tol : ℝ} (htol : 0 < tol) :
    ∀ᶠ N : ℕ in atTop, ∀ (G : RestrictedLaw i),
      kappa i*t i ≤ rootLo i G → ∀v own : ℝ,
      v ∈ Icc (0:ℝ) (t i) → own ∈ Icc (0:ℝ) (t i) →
        |rawUtility i N G v own-productPayoff (xi i) v G.multiplier own| < tol := by
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
  intro G hreceipt v own hv hown
  have herr := rawUtility_product_error i N G hv hown hreceipt hN hδ.le hδle hS hR
  linarith

end FCAppendix.Affine.UniformFinite.Late.Exceptional
