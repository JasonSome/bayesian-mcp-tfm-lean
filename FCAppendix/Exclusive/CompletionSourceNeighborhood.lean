import FCAppendix.Exclusive.NarrowMeanParameters
import FCAppendix.Exclusive.NarrowLocalIdentification
import FCAppendix.Exclusive.CompletionDerivativeCorrection

noncomputable section
namespace FCAppendix.Completion.Exclusive
open MeasureTheory Filter Topology Set
open FCAppendix Game Bayes Exclusive Exclusive.Narrow Exclusive.Narrow.Finite
open scoped BigOperators

def sourceP (h rho : ℝ) : ℝ := rho/h
def sourceQ (h rho : ℝ) : ℝ := 1-rho/h
def sourcePrice (d : ℕ) (a : UserTariff) (h rho : ℝ) : ℝ := 1/fTariff d a (rho/h)
def sourceBid (d : ℕ) (a : UserTariff) (h rho : ℝ) : ℝ :=
  sourcePrice d a h rho/(sourceQ h rho)^d

def qLower (d : ℕ) (h eta cap : ℝ) : ℝ :=
  (1-cap/h)*((1-eta)/(1+eta))^(rate (d+1))
def qUpper (d : ℕ) (h eta cap : ℝ) : ℝ :=
  (1-cap/h)*((1+eta)/(1-eta))^(rate (d+1))
def priceLower (d : ℕ) (h rho eta cap : ℝ) : ℝ :=
  (1-eta)*((1-cap/h)/sourceQ h rho)^d
def priceUpper (d : ℕ) (h rho eta cap : ℝ) : ℝ :=
  (1+eta)*((1-cap/h)/sourceQ h rho)^d
def spreadRatio (d : ℕ) (eta cap : ℝ) : ℝ :=
  ((1+eta)/(1-eta))^(rate (d+1))*(1-cap)

theorem scalar_source_neighborhood (d : ℕ) (hd : 1 ≤ d) {h rho : ℝ}
    (hh : 0 < h) (hrho : 0 < rho) (hrhoh : rho < h) (hh1 : h ≤ 1) :
    ∃ eta delta : ℝ, 0 < eta ∧ eta < 1 ∧ 0 < delta ∧
      ∀ e r : ℝ, |e| < eta → |r-rho| < delta →
        0 < r ∧ r < h ∧
        sourceQ h rho/2 < qLower d h e r ∧
        qUpper d h e r < (1+sourceQ h rho)/2 ∧
        (1/2:ℝ) < priceLower d h rho e r ∧ priceUpper d h rho e r < 2 ∧
        spreadRatio d e r < 1 := by
  have hq : 0 < sourceQ h rho := by dsimp [sourceQ]; exact sub_pos.mpr ((div_lt_one hh).mpr hrhoh)
  have hq1 : sourceQ h rho < 1 := by dsimp [sourceQ]; linarith [div_pos hrho hh]
  let x0 : ℝ×ℝ := (0,rho)
  have hr : 0 ≤ rate (d+1) := (rate_pos (d+1) (by omega)).le
  have htail : ContinuousAt (fun x : ℝ×ℝ => 1-x.2/h) x0 :=
    continuousAt_const.sub (continuousAt_snd.div_const h)
  have hratioL : ContinuousAt (fun x : ℝ×ℝ => (1-x.1)/(1+x.1)) x0 :=
    (continuousAt_const.sub continuousAt_fst).div
      (continuousAt_const.add continuousAt_fst) (by norm_num [x0])
  have hratioU : ContinuousAt (fun x : ℝ×ℝ => (1+x.1)/(1-x.1)) x0 :=
    (continuousAt_const.add continuousAt_fst).div
      (continuousAt_const.sub continuousAt_fst) (by norm_num [x0])
  have hcqL : ContinuousAt (fun x : ℝ×ℝ => qLower d h x.1 x.2) x0 :=
    htail.mul (hratioL.rpow_const (Or.inr hr))
  have hcqU : ContinuousAt (fun x : ℝ×ℝ => qUpper d h x.1 x.2) x0 :=
    htail.mul (hratioU.rpow_const (Or.inr hr))
  have hcpL : ContinuousAt (fun x : ℝ×ℝ => priceLower d h rho x.1 x.2) x0 :=
    (continuousAt_const.sub continuousAt_fst).mul ((htail.div_const (sourceQ h rho)).pow d)
  have hcpU : ContinuousAt (fun x : ℝ×ℝ => priceUpper d h rho x.1 x.2) x0 :=
    (continuousAt_const.add continuousAt_fst).mul ((htail.div_const (sourceQ h rho)).pow d)
  have hcs : ContinuousAt (fun x : ℝ×ℝ => spreadRatio d x.1 x.2) x0 :=
    (hratioU.rpow_const (Or.inr hr)).mul (continuousAt_const.sub continuousAt_snd)
  have hqL0 : qLower d h 0 rho = sourceQ h rho := by simp [qLower,sourceQ]
  have hqU0 : qUpper d h 0 rho = sourceQ h rho := by simp [qUpper,sourceQ]
  have hpL0 : priceLower d h rho 0 rho = 1 := by
    change (1-0)*((sourceQ h rho)/(sourceQ h rho))^d = 1
    simp [hq.ne']
  have hpU0 : priceUpper d h rho 0 rho = 1 := by
    change (1+0)*((sourceQ h rho)/(sourceQ h rho))^d = 1
    simp [hq.ne']
  have hs0 : spreadRatio d 0 rho = 1-rho := by simp [spreadRatio]
  have hneigh : ∀ᶠ x : ℝ×ℝ in 𝓝 x0,
      0 < x.2 ∧ x.2 < h ∧ sourceQ h rho/2 < qLower d h x.1 x.2 ∧
      qUpper d h x.1 x.2 < (1+sourceQ h rho)/2 ∧
      (1/2:ℝ) < priceLower d h rho x.1 x.2 ∧ priceUpper d h rho x.1 x.2 < 2 ∧
      spreadRatio d x.1 x.2 < 1 := by
    have h1 := (continuousAt_snd : ContinuousAt (fun x : ℝ×ℝ => x.2) x0).eventually
      (eventually_gt_nhds hrho)
    have h2 := (continuousAt_snd : ContinuousAt (fun x : ℝ×ℝ => x.2) x0).eventually
      (eventually_lt_nhds hrhoh)
    have h3 := hcqL.eventually (eventually_gt_nhds (show sourceQ h rho/2 < qLower d h 0 rho by
      rw [hqL0]; linarith))
    have h4 := hcqU.eventually (eventually_lt_nhds (show qUpper d h 0 rho < (1+sourceQ h rho)/2 by
      rw [hqU0]; linarith))
    have h5 := hcpL.eventually (eventually_gt_nhds (show (1/2:ℝ) < priceLower d h rho 0 rho by
      rw [hpL0]; norm_num))
    have h6 := hcpU.eventually (eventually_lt_nhds (show priceUpper d h rho 0 rho < 2 by
      rw [hpU0]; norm_num))
    have h7 := hcs.eventually (eventually_lt_nhds (show spreadRatio d 0 rho < 1 by
      rw [hs0]; linarith))
    exact h1.and (h2.and (h3.and (h4.and (h5.and (h6.and h7)))))
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hneigh
  refine ⟨min (r/2) (1/2),r/2,by positivity,by nlinarith [min_le_right (r/2) (1/2)],
    by positivity,?_⟩
  intro e s he hs
  apply hball (a := (e,s))
  rw [Metric.mem_ball,Prod.dist_eq,Real.dist_eq,Real.dist_eq]
  dsimp [x0]
  rw [sub_zero]
  exact max_lt (he.trans_le (min_le_left _ _) |>.trans (by linarith)) (hs.trans (by linarith))

theorem inverseBid_ratio_scale (d : ℕ) {X s t : ℝ}
    (hX : 0 < X) (hs : 0 < s) (ht : 0 < t) :
    inverseBid (d+1) (X*s)/inverseBid (d+1) (X*t) = (t/s)^(rate (d+1)) := by
  unfold inverseBid
  rw [Real.mul_rpow hX.le hs.le,Real.mul_rpow hX.le ht.le]
  have hXp : X^(-rate (d+1)) ≠ 0 := (Real.rpow_pos_of_pos hX _).ne'
  rw [mul_div_mul_left _ _ hXp,Real.rpow_neg hs.le,Real.rpow_neg ht.le,
    inv_div_inv,← Real.div_rpow ht.le hs.le]

theorem relative_exposure_corridor (d : ℕ) (hd : 1 ≤ d)
    {h cap X eta W b : ℝ} (hh : 0 < h) (hcap : cap < h)
    (hX : 0 < X) (heta : eta ∈ Ioo (0:ℝ) 1)
    (hb : b ∈ Icc (X*(1-eta)) (X*(1+eta)))
    (hW : W ∈ Icc (h*inverseBid (d+1) (X*(1+eta)))
      (h*inverseBid (d+1) (X*(1-eta)))) :
    qLower d h eta cap ≤ ((h-cap)/W)*inverseBid (d+1) b ∧
      ((h-cap)/W)*inverseBid (d+1) b ≤ qUpper d h eta cap := by
  have ha : 0 < X*(1-eta) := mul_pos hX (sub_pos.mpr heta.2)
  have hh0 := hh.ne'
  have hs0 : 0 < 1-eta := sub_pos.mpr heta.2
  have ht0 : 0 < 1+eta := by linarith [heta.1]
  have hexposure := meanExposure_corridor (n := d+1) (by omega) hh hcap ha hb hW
  have hlow : ((h-cap)/(h*inverseBid (d+1) (X*(1-eta))))*inverseBid (d+1) (X*(1+eta)) =
      qLower d h eta cap := by
    unfold qLower
    rw [← inverseBid_ratio_scale d hX ht0 hs0]
    field_simp [hh0,(inverseBid_pos (d+1) ha).ne']
  have hupp : ((h-cap)/(h*inverseBid (d+1) (X*(1+eta))))*inverseBid (d+1) (X*(1-eta)) =
      qUpper d h eta cap := by
    unfold qUpper
    rw [← inverseBid_ratio_scale d hX hs0 ht0]
    field_simp [hh0,(inverseBid_pos (d+1) (mul_pos hX ht0)).ne']
  simpa only [hlow,hupp] using hexposure

theorem relative_price_corridor (d : ℕ) (hd : 1 ≤ d)
    {h rho cap H lam0 eta W : ℝ} (hh : 0 < h) (hrho : rho < h) (hcap : cap < h)
    (hH : 0 < H) (hlam0 : 0 < lam0) (heta : eta ∈ Ioo (0:ℝ) 1)
    (hW : W ∈ Icc
      (h*inverseBid (d+1) ((H*lam0/(sourceQ h rho)^d)*(1+eta)))
      (h*inverseBid (d+1) ((H*lam0/(sourceQ h rho)^d)*(1-eta)))) :
    priceLower d h rho eta cap ≤ (((h-cap)/W)^d)/(H*lam0) ∧
      (((h-cap)/W)^d)/(H*lam0) ≤ priceUpper d h rho eta cap := by
  have hq : 0 < sourceQ h rho := by dsimp [sourceQ]; exact sub_pos.mpr ((div_lt_one hh).mpr hrho)
  let X := H*lam0/(sourceQ h rho)^d
  have hX : 0 < X := by dsimp [X]; positivity
  have ha : 0 < X*(1-eta) := mul_pos hX (sub_pos.mpr heta.2)
  have hB : 0 < X*(1+eta) := mul_pos hX (by linarith [heta.1])
  have hWpos : 0 < W := (mul_pos hh (inverseBid_pos (d+1) hB)).trans_le hW.1
  have hlo : (h-cap)/(h*inverseBid (d+1) (X*(1-eta))) ≤ (h-cap)/W :=
    div_le_div_of_nonneg_left (sub_pos.mpr hcap).le hWpos hW.2
  have hhi : (h-cap)/W ≤ (h-cap)/(h*inverseBid (d+1) (X*(1+eta))) :=
    div_le_div_of_nonneg_left (sub_pos.mpr hcap).le
      (mul_pos hh (inverseBid_pos (d+1) hB)) hW.1
  have hdiff : 0 < h-cap := sub_pos.mpr hcap
  have hloPow := pow_le_pow_left₀
    (div_nonneg hdiff.le (mul_pos hh (inverseBid_pos _ ha)).le) hlo d
  have hhiPow := pow_le_pow_left₀ (div_nonneg hdiff.le hWpos.le) hhi d
  have hscalar (s : ℝ) (hs : 0 < s) :
      ((h-cap)/(h*inverseBid (d+1) (X*s)))^d/(H*lam0) =
        s*((1-cap/h)/sourceQ h rho)^d := by
    have hdiff : 1-cap/h = (h-cap)/h := by
      field_simp [hh.ne']
    rw [hdiff]
    simp only [div_pow,mul_pow]
    rw [inverseBid_natPower d hd (mul_pos hX hs)]
    dsimp only [X]
    field_simp [hh.ne',hH.ne',hlam0.ne',hq.ne',hs.ne']
  constructor
  · rw [priceLower,← hscalar (1-eta) (sub_pos.mpr heta.2)]
    exact div_le_div_of_nonneg_right hloPow (mul_pos hH hlam0).le
  · rw [priceUpper,← hscalar (1+eta) (by linarith [heta.1])]
    exact div_le_div_of_nonneg_right hhiPow (mul_pos hH hlam0).le

theorem select_source_rectangle (d : ℕ) (hd : 1 ≤ d) (G : Schedule (d+1))
    {h rho : ℝ} (hh : 0 < h) (hrho : 0 < rho) (hrhoh : rho < h) (hh1 : h ≤ 1) :
    ∃ eta delta l u L U eps : ℝ,
      eta ∈ Ioo (0:ℝ) 1 ∧ 0 < delta ∧ 0 < l ∧ l < u ∧ u < 1 ∧
      0 < L ∧ L ≤ U ∧ 0 < eps ∧
      (∀ a : UserTariff, a.Allowed → sourcePrice d a h rho ∈ Icc (2*L) (U/2)) ∧
      (∀ e r : ℝ, |e| < eta → |r-rho| < delta →
        0 < r ∧ r < h ∧ 1-u < qLower d h e r ∧ qUpper d h e r < 1-l ∧
        (1/2:ℝ) < priceLower d h rho e r ∧ priceUpper d h rho e r < 2 ∧
        spreadRatio d e r < 1) ∧
      ∀ H g lam : ℝ, 0 < H → 0 ≤ g → g/H < eps → lam ∈ Icc (H*L) (H*U) →
        ∀ a : UserTariff, a.Allowed → StrictMonoOn (exposureEquation d a G g lam) (Icc l u) := by
  have hp0 : 0 < rho/h := div_pos hrho hh
  have hp1 : rho/h < 1 := (div_lt_one hh).mpr hrhoh
  obtain ⟨eta,delta,he0,he1,hd0,hscalar⟩ := scalar_source_neighborhood d hd hh hrho hrhoh hh1
  obtain ⟨Fmin,Fmax,Dmin,Dmax,hFm,hFM,hDm,hDM,hf⟩ :=
    source_tariff_uniform_bounds d hd hp0.le le_rfl hp1
  let l := (rho/h)/2
  let u := (1+rho/h)/2
  let L := 1/(2*Fmax)
  let U := 2/Fmin
  have hl : 0 < l := by dsimp [l]; positivity
  have hlu : l < u := by dsimp [l,u]; linarith
  have hu : u < 1 := by dsimp [u]; linarith
  have hFmax : 0 < Fmax := hFm.trans_le hFM
  have hL : 0 < L := by dsimp only [L]; exact one_div_pos.mpr (mul_pos (by norm_num) hFmax)
  have hLU : L ≤ U := by
    dsimp [L,U]
    apply (div_le_div_iff₀ (by positivity) hFm).mpr
    nlinarith
  obtain ⟨eps,A,B,C,D,K,heps,_hA,_hAB,_hC,_hCD,_hK,_hb,hguard⟩ :=
    exists_uniform_small_base_guard d hd G hl.le hlu.le hu hL hLU
  refine ⟨eta,delta,l,u,L,U,eps,⟨he0,he1⟩,hd0,hl,hlu,hu,hL,hLU,heps,?_,?_,?_⟩
  · intro a ha
    have hfa := (hf a ha (rho/h) ⟨le_rfl,le_rfl⟩).1
    have hfpos : 0 < fTariff d a (rho/h) := hFm.trans_le hfa.1
    constructor
    · dsimp [sourcePrice,L]
      have hr := one_div_le_one_div_of_le hfpos hfa.2
      convert hr using 1
      field_simp [hFmax.ne',hfpos.ne',hFm.ne']
    · dsimp [sourcePrice,U]
      have hr := one_div_le_one_div_of_le hFm hfa.1
      convert hr using 1
      field_simp [hFmax.ne',hfpos.ne',hFm.ne']
  · intro e r he hr
    have heqU : 1-u = sourceQ h rho/2 := by dsimp only [u,sourceQ]; ring
    have heqL : 1-l = (1+sourceQ h rho)/2 := by dsimp only [l,sourceQ]; ring
    rw [heqU,heqL]
    exact hscalar e r he hr
  · intro H g lam hH hg hsmall hlam a ha
    exact (hguard H g lam hH hg hsmall hlam a ha).2

theorem large_scale_for_fixed_base {g eps : ℝ} (hg : 0 ≤ g) (heps : 0 < eps) :
    ∃ H : ℝ, 0 < H ∧ g/H < eps := by
  refine ⟨(g+1)/eps,by positivity,?_⟩
  apply (div_lt_iff₀ (by positivity)).mpr
  field_simp [heps.ne']
  nlinarith

theorem source_guards_eventually {M C : ℕ → ℕ} {rho eta delta : ℝ}
    (hrho : Tendsto (fun t => (C t:ℝ)/M t) atTop (𝓝 rho))
    (heta : 0 < eta) (hdelta : 0 < delta) :
    ∀ᶠ t in atTop, |(eta/2:ℝ)| < eta ∧ |(C t:ℝ)/M t-rho| < delta := by
  filter_upwards [hrho.eventually (Metric.ball_mem_nhds rho hdelta)] with t ht
  exact ⟨by rw [abs_of_pos (by positivity)]; linarith,
    by simpa [Metric.mem_ball,Real.dist_eq] using ht⟩

end FCAppendix.Completion.Exclusive
