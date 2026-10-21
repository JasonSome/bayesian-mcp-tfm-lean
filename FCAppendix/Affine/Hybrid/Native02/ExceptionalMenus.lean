import FCAppendix.Affine.EqualCapacity
import FCAppendix.Affine.Hybrid.Menu
import FCAppendix.Affine.Hybrid.MenuLipschitz

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open Set

def outsideOneAt (xi v lam q : ℝ) : ℝ := q * (v-lam/(1-xi*q))

lemma threshold_receipt_lower {xi b lam q : ℝ}
    (ht : EqualCapacity.ScalarThreshold xi b lam q) (hq : 0 < q) :
    lam ≤ b*(1-xi*q) := by
  by_cases hq1 : q = 1
  · exact ht.2.2.2.1 hq1
  · exact (ht.2.2.2.2 hq (lt_of_le_of_ne ht.2.1 hq1)).ge

lemma threshold_weighted_receipt_lower {xi b lam q : ℝ}
    (ht : EqualCapacity.ScalarThreshold xi b lam q) :
    q*lam ≤ q*(b*(1-xi*q)) := by
  by_cases hq : q = 0
  · simp [hq]
  · exact mul_le_mul_of_nonneg_left
      (threshold_receipt_lower ht (lt_of_le_of_ne ht.1 (Ne.symm hq))) ht.1

theorem clipped_singleton_le_M1_integrand {xi v b lam q : ℝ}
    (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (ht : EqualCapacity.ScalarThreshold xi b lam q) :
    q*(v-b) ≤ outsideOneAt xi v lam q := by
  have hden : 0 < 1-xi*q := by nlinarith [ht.2.1]
  by_cases hq : q = 0
  · simp [hq, outsideOneAt]
  · have hr := threshold_receipt_lower ht (lt_of_le_of_ne ht.1 (Ne.symm hq))
    have hcost : lam/(1-xi*q) ≤ b := (div_le_iff₀ hden).2 hr
    exact mul_le_mul_of_nonneg_left (sub_le_sub_left hcost v) ht.1

theorem clipped_broadcast_le_zero_menu {xi eta v b lam q : ℝ}
    (heta : eta = 1-2*xi)
    (ht : EqualCapacity.ScalarThreshold xi b lam q) :
    independentTwo eta v b q ≤ two xi 0 v lam q := by
  have hw := threshold_weighted_receipt_lower ht
  rw [heta]
  unfold independentTwo two
  simp only [zero_mul, sub_zero, one_mul, zero_add]
  nlinarith

theorem clipped_broadcast_le_M2 {xi eta v b lam q : ℝ}
    (hv : 0 < v) (heta : eta = 1-2*xi)
    (ht : EqualCapacity.ScalarThreshold xi b lam q) :
    independentTwo eta v b q ≤ outsideTwo v lam := by
  apply (clipped_broadcast_le_zero_menu heta ht).trans
  rw [two_zero_square _ _ _ _ hv.ne']
  exact sub_le_self _ (mul_nonneg hv.le (sq_nonneg _))

theorem clipped_broadcast_le_M2_sub_gap {xi eta v b lam q gap : ℝ}
    (hv : 0 < v) (heta : eta = 1-2*xi)
    (ht : EqualCapacity.ScalarThreshold xi b lam q)
    (hgap : 0 ≤ gap) (hsep : gap ≤ |q-(1-lam/v)|) :
    independentTwo eta v b q ≤ outsideTwo v lam-v*gap^2 := by
  have hsq : gap^2 ≤ (q-(1-lam/v))^2 := by
    have hh := (sq_le_sq₀ hgap (abs_nonneg _)).2 hsep
    simpa only [sq_abs] using hh
  have hmul := mul_le_mul_of_nonneg_left hsq hv.le
  have h := clipped_broadcast_le_zero_menu (v:=v) heta ht
  rw [two_zero_square _ _ _ _ hv.ne'] at h
  linarith

theorem outsideOneAt_multiplier_lipschitz {xi v lam lam' q : ℝ}
    (hxi0 : 0 < xi) (hxi1 : xi < 1) (hq : q ∈ Icc (0:ℝ) 1) :
    |outsideOneAt xi v lam q-outsideOneAt xi v lam' q| ≤
      |lam-lam'|/(1-xi) := by
  have hk : 0 < 1-xi := sub_pos.mpr hxi1
  have hd : 0 < 1-xi*q := by nlinarith [hq.2]
  have hdk : 1-xi ≤ 1-xi*q := by nlinarith [hq.2]
  have he : outsideOneAt xi v lam q-outsideOneAt xi v lam' q =
      -(q*((lam-lam')/(1-xi*q))) := by unfold outsideOneAt; ring
  rw [he, abs_neg, abs_mul, abs_of_nonneg hq.1, abs_div, abs_of_pos hd]
  calc
    q*(|lam-lam'|/(1-xi*q)) ≤ |lam-lam'|/(1-xi*q) :=
      mul_le_of_le_one_left (div_nonneg (abs_nonneg _) hd.le) hq.2
    _ ≤ |lam-lam'|/(1-xi) := div_le_div_of_nonneg_left (abs_nonneg _) hk hdk

theorem zero_menu_multiplier_lipschitz {xi v lam lam' q : ℝ}
    (hq : q ∈ Icc (0:ℝ) 1) :
    |two xi 0 v lam q-two xi 0 v lam' q| ≤ 2*|lam-lam'| := by
  have he : two xi 0 v lam q-two xi 0 v lam' q = -2*(lam-lam')*q := by
    unfold two
    ring
  rw [he, abs_mul, abs_mul, abs_of_nonneg hq.1]
  norm_num
  exact mul_le_of_le_one_right (by positivity) hq.2

theorem clipped_singleton_le_reference {xi v b price lam q M1 : ℝ}
    (hxi : 0<xi) (hxi1 : xi<1)
    (ht : EqualCapacity.ScalarThreshold xi b price q)
    (hM1 : ∀ p∈ Icc (0:ℝ) 1,outsideOneAt xi v lam p≤ M1) :
    q*(v-b) ≤ M1+|price-lam|/(1-xi) := by
  have hq : q∈ Icc (0:ℝ) 1 := ⟨ht.1,ht.2.1⟩
  have hu := clipped_singleton_le_M1_integrand (v:=v) hxi hxi1 ht
  have he := outsideOneAt_multiplier_lipschitz (v:=v) (lam:=price) (lam':=lam) hxi hxi1 hq
  have hs := le_abs_self (outsideOneAt xi v price q-outsideOneAt xi v lam q)
  have hm := hM1 q hq
  linarith

theorem clipped_broadcast_le_reference {xi eta v b price lam q : ℝ}
    (hv : 0<v) (heta : eta=1-2*xi)
    (ht : EqualCapacity.ScalarThreshold xi b price q) :
    independentTwo eta v b q ≤ outsideTwo v lam+2*|price-lam| := by
  have hq : q∈ Icc (0:ℝ) 1 := ⟨ht.1,ht.2.1⟩
  have hu := clipped_broadcast_le_zero_menu (v:=v) heta ht
  have he := zero_menu_multiplier_lipschitz (xi:=xi) (v:=v) (lam:=price) (lam':=lam) hq
  have hs := le_abs_self (two xi 0 v price q-two xi 0 v lam q)
  have hm : two xi 0 v lam q ≤ outsideTwo v lam := by
    rw [two_zero_square _ _ _ _ hv.ne']
    exact sub_le_self _ (mul_nonneg hv.le (sq_nonneg _))
  linarith

theorem exists_M1_maximizer {xi v lam : ℝ}
    (hxi0 : 0 < xi) (hxi1 : xi < 1) :
    ∃ q ∈ Icc (0:ℝ) 1, ∀ r ∈ Icc (0:ℝ) 1,
      outsideOneAt xi v lam r ≤ outsideOneAt xi v lam q := by
  have hc : ContinuousOn (outsideOneAt xi v lam) (Icc (0:ℝ) 1) := by
    unfold outsideOneAt
    apply continuousOn_id.mul
    apply continuousOn_const.sub
    apply continuousOn_const.div
      (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
    intro q hq
    have : 0 < 1-xi*q := by nlinarith [hq.2]
    exact this.ne'
  obtain ⟨q,hq,hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr zero_le_one) hc
  exact ⟨q,hq,fun r hr => hmax hr⟩

def lowerEndpointGap (xi lo L vmin : ℝ) : ℝ :=
  lo/(xi*L)-lo/vmin-(1-xi)/xi

def upperEndpointGap (xi hi U vmax : ℝ) : ℝ :=
  (1-xi)/xi-hi/(xi*U)+hi/vmax

lemma demand_monotone_bid {xi lam : ℝ} (hxi : 0 < xi) (hlam : 0 ≤ lam)
    {b b' : ℝ} (hb : 0 < b) (hbb : b ≤ b') :
    EqualCapacity.demand xi b lam ≤ EqualCapacity.demand xi b' lam := by
  have hbr : 0 < b' := hb.trans_le hbb
  have hr : lam/b' ≤ lam/b := div_le_div_of_nonneg_left hlam hb hbb
  unfold EqualCapacity.demand
  apply max_le_max le_rfl
  apply min_le_min le_rfl
  exact (div_le_div_iff_of_pos_right hxi).2 (by linarith)

lemma demand_eq_exposure {xi lam b : ℝ}
    (hxi : 0 < xi) (hb : 0 < b)
    (hlow : (1-xi)*b < lam) (hhigh : lam < b) :
    EqualCapacity.demand xi b lam = exposure xi lam b := by
  have h := exposure_mem_Ioo hxi hb hlow hhigh
  change max 0 (min 1 (exposure xi lam b)) = exposure xi lam b
  rw [min_eq_right h.2.le, max_eq_right h.1.le]

lemma scalarThreshold_eq_demand {xi lam b q : ℝ}
    (hxi : 0 < xi) (hxi1 : xi < 1) (hb : 0 < b)
    (ht : EqualCapacity.ScalarThreshold xi b lam q) :
    q = EqualCapacity.demand xi b lam := by
  let p := EqualCapacity.demand xi b lam
  have hp := EqualCapacity.demand_spec hxi hxi1 hb lam
  have hscalar {x y : ℝ}
      (hx : EqualCapacity.ScalarThreshold xi b lam x)
      (hy : EqualCapacity.ScalarThreshold xi b lam y) (hxy : x < y) : False := by
    have hx1 : x < 1 := hxy.trans_le hy.2.1
    have hy0 : 0 < y := hx.1.trans_lt hxy
    have hl : b*(1-xi*x) ≤ lam := by
      by_cases hx0 : x=0
      · exact hx.2.2.1 hx0
      · exact (hx.2.2.2.2 (lt_of_le_of_ne hx.1 (Ne.symm hx0)) hx1).le
    have hu := threshold_receipt_lower hy hy0
    have hdiff := mul_pos hb (mul_pos hxi (sub_pos.mpr hxy))
    nlinarith
  exact le_antisymm (le_of_not_gt (fun h => hscalar hp ht h))
    (le_of_not_gt (fun h => hscalar ht hp h))

lemma lower_endpoint_separation {xi L vmin v lo lam : ℝ}
    (hxi : 0 < xi) (hxi1 : xi < 1) (hL : 0 < L)
    (hLv : L < vmin) (hvv : vmin ≤ v) (hlo : 0 ≤ lo) (hll : lo ≤ lam) :
    lowerEndpointGap xi lo L vmin ≤
      (1-lam/v)-exposure xi lam L := by
  have hvmin : 0 < vmin := hL.trans hLv
  have hv : 0 < v := hvmin.trans_le hvv
  have hcoef : 0 ≤ 1/(xi*L)-1/vmin := by
    have hprod : xi*L < vmin := by nlinarith
    exact sub_nonneg.mpr
      (one_div_le_one_div_of_le (mul_pos hxi hL) hprod.le)
  have hi : 1/v ≤ 1/vmin := one_div_le_one_div_of_le hvmin hvv
  have h1 := mul_le_mul_of_nonneg_left hi (hlo.trans hll)
  have h2 := mul_le_mul_of_nonneg_right hll hcoef
  have he : (1-lam/v)-exposure xi lam L =
      lam*(1/(xi*L)-1/v)-(1-xi)/xi := by
    unfold exposure
    field_simp [hxi.ne',hL.ne',hv.ne']
    ring
  have he' : lowerEndpointGap xi lo L vmin =
      lo*(1/(xi*L)-1/vmin)-(1-xi)/xi := by
    unfold lowerEndpointGap
    ring
  rw [he,he']
  nlinarith

lemma upper_endpoint_separation {xi U vmax v hi lam : ℝ}
    (hxi : 0 < xi) (hxi1 : xi < 1) (hU : 0 < U)
    (hUv : U < v) (hvv : v ≤ vmax) (hlam : 0 ≤ lam) (hlh : lam ≤ hi) :
    upperEndpointGap xi hi U vmax ≤
      exposure xi lam U-(1-lam/v) := by
  have hv : 0 < v := hU.trans hUv
  have hvmax : 0 < vmax := hv.trans_le hvv
  have hcoef : 0 ≤ 1/(xi*U)-1/v := by
    have hprod : xi*U < v := by nlinarith
    exact sub_nonneg.mpr
      (one_div_le_one_div_of_le (mul_pos hxi hU) hprod.le)
  have hi' : 1/vmax ≤ 1/v := one_div_le_one_div_of_le hv hvv
  have h1 := mul_le_mul_of_nonneg_left hi' (hlam.trans hlh)
  have h2 := mul_le_mul_of_nonneg_right hlh hcoef
  have he : exposure xi lam U-(1-lam/v) =
      (1-xi)/xi-lam*(1/(xi*U)-1/v) := by
    unfold exposure
    field_simp [hxi.ne',hU.ne',hv.ne']
    ring
  have he' : upperEndpointGap xi hi U vmax =
      (1-xi)/xi-hi*(1/(xi*U)-1/vmax) := by
    unfold upperEndpointGap
    ring
  rw [he,he']
  nlinarith

theorem zero_outside_box_uniform_gap {xi eta L U vmin vmax v lo hi lam b q : ℝ}
    (hxi : 0 < xi) (hxi1 : xi < 1) (heta : eta=1-2*xi)
    (hL : 0 < L) (hLU : L ≤ U) (hUv : U < vmin)
    (hvmin : vmin ≤ v) (hvmax : v ≤ vmax)
    (hlo : 0 < lo) (hllo : lo ≤ lam) (hlhi : lam ≤ hi)
    (hboxlo : (1-xi)*U < lo) (hboxhi : hi < L)
    (hb : 0 < b) (hout : b ≤ L ∨ U ≤ b)
    (ht : EqualCapacity.ScalarThreshold xi b lam q)
    (hgapL : 0 < lowerEndpointGap xi lo L vmin)
    (hgapU : 0 < upperEndpointGap xi hi U vmax) :
    let gap := min (lowerEndpointGap xi lo L vmin)
      (upperEndpointGap xi hi U vmax)
    0 < gap ∧ independentTwo eta v b q ≤ outsideTwo v lam-vmin*gap^2 := by
  let gap := min (lowerEndpointGap xi lo L vmin) (upperEndpointGap xi hi U vmax)
  have hg : 0 < gap := lt_min hgapL hgapU
  have hU : 0 < U := hL.trans_le hLU
  have hv0 : 0 < v := (hU.trans hUv).trans_le hvmin
  have hlam : 0 < lam := hlo.trans_le hllo
  have hk : 0 ≤ 1-xi := by linarith
  have hLlow : (1-xi)*L < lam :=
    (mul_le_mul_of_nonneg_left hLU hk).trans_lt (hboxlo.trans_le hllo)
  have hUlow : (1-xi)*U < lam := hboxlo.trans_le hllo
  have hLhigh : lam < L := hlhi.trans_lt hboxhi
  have hUhigh : lam < U := hLhigh.trans_le hLU
  have hqeq := scalarThreshold_eq_demand hxi hxi1 hb ht
  have hsep : gap ≤ |q-(1-lam/v)| := by
    rcases hout with hout | hout
    · have hqL := demand_monotone_bid hxi hlam.le hb hout
      rw [←hqeq, demand_eq_exposure hxi hL hLlow hLhigh] at hqL
      have he := lower_endpoint_separation hxi hxi1 hL (hLU.trans_lt hUv)
        hvmin hlo.le hllo
      have hs : gap ≤ (1-lam/v)-q := by
        have := min_le_left (lowerEndpointGap xi lo L vmin)
          (upperEndpointGap xi hi U vmax)
        dsimp only [gap]
        linarith
      have hn : q-(1-lam/v) ≤ 0 := by linarith
      rw [abs_of_nonpos hn]
      linarith
    · have hqU := demand_monotone_bid hxi hlam.le hU hout
      rw [←hqeq, demand_eq_exposure hxi hU hUlow hUhigh] at hqU
      have he := upper_endpoint_separation hxi hxi1 hU (hUv.trans_le hvmin)
        hvmax hlam.le hlhi
      have hs : gap ≤ q-(1-lam/v) := by
        have := min_le_right (lowerEndpointGap xi lo L vmin)
          (upperEndpointGap xi hi U vmax)
        dsimp only [gap]
        linarith
      rw [abs_of_nonneg (by linarith : 0 ≤ q-(1-lam/v))]
      exact hs
  refine ⟨hg,?_⟩
  have hpay := clipped_broadcast_le_M2_sub_gap hv0 heta ht hg.le hsep
  have hmul := mul_le_mul_of_nonneg_right hvmin (sq_nonneg gap)
  linarith

lemma source_zero_endpoint_gaps {xi qbar L U vmin vmax : ℝ}
    (hxi : 0 < xi) (hxi1 : xi < 1) (_hq0 : 0 < qbar) (hq1 : qbar < 1)
    (hL : 0 < L) (hU : 0 < U) (hvmin : 0 < vmin) (hvmax : 0 < vmax)
    (hleft : L < (1-qbar)/(1-xi*qbar)*vmin)
    (hright : (1-qbar)/(1-xi*qbar)*vmax < U) :
    0 < lowerEndpointGap xi ((1-xi*qbar)*L) L vmin ∧
    0 < upperEndpointGap xi ((1-xi*qbar)*U) U vmax := by
  have hh0 : 0 < 1-xi*qbar := by nlinarith
  have heL : lowerEndpointGap xi ((1-xi*qbar)*L) L vmin =
      (1-qbar)-(1-xi*qbar)*L/vmin := by
    unfold lowerEndpointGap
    field_simp [hxi.ne',hL.ne',hvmin.ne']
    ring
  have heU : upperEndpointGap xi ((1-xi*qbar)*U) U vmax =
      (1-xi*qbar)*U/vmax-(1-qbar) := by
    unfold upperEndpointGap
    field_simp [hxi.ne',hU.ne',hvmax.ne']
    ring
  have hl : (1-xi*qbar)*L < (1-qbar)*vmin := by
    have hh := mul_lt_mul_of_pos_left hleft hh0
    field_simp [hh0.ne'] at hh
    nlinarith
  have hr : (1-qbar)*vmax < (1-xi*qbar)*U := by
    have hh := mul_lt_mul_of_pos_left hright hh0
    field_simp [hh0.ne'] at hh
    nlinarith
  rw [heL,heU]
  constructor
  · exact sub_pos.mpr ((div_lt_iff₀ hvmin).2 hl)
  · exact sub_pos.mpr ((lt_div_iff₀ hvmax).2 hr)

lemma clipped_unit_nonexpansive (a b : ℝ) :
    |max 0 (min 1 a)-max 0 (min 1 b)|≤|a-b| := by
  have h0 := abs_nonneg (a-b)
  have h1 := le_abs_self (a-b)
  have h2 := neg_le_abs (a-b)
  rw [abs_le]
  simp only [max_def,min_def]
  split_ifs <;> constructor <;> linarith

lemma demand_price_lipschitz {xi b : ℝ} (hxi : 0<xi) (hb : 0<b)
    (price lam : ℝ) :
    |EqualCapacity.demand xi b price-EqualCapacity.demand xi b lam|≤
      |price-lam|/(xi*b) := by
  have h := clipped_unit_nonexpansive ((1-price/b)/xi) ((1-lam/b)/xi)
  have he : (1-price/b)/xi-(1-lam/b)/xi=-(price-lam)/(xi*b) := by
    field_simp [hxi.ne',hb.ne']
    ring
  rw [he,abs_div,abs_neg,abs_of_pos (mul_pos hxi hb)] at h
  exact h

theorem clipped_broadcast_le_reference_zero_gap
    {xi eta d L U R W vmin vmax v lo hi lam price b q : ℝ}
    (hxi : 0<xi) (hxi1 : xi<1) (heta : eta=1-2*xi)
    (hd : 0<d) (hdb : d≤ b) (hbR : b≤ R) (hvW : |v|≤ W)
    (hL : 0<L) (hLU : L≤ U) (hUv : U<vmin) (hvmin : vmin≤ v) (hvmax : v≤ vmax)
    (hlo : 0<lo) (hllo : lo≤ lam) (hlhi : lam≤ hi)
    (hboxlo : (1-xi)*U<lo) (hboxhi : hi<L)
    (hout : b≤ L ∨ U≤ b) (ht : EqualCapacity.ScalarThreshold xi b price q)
    (hgapL : 0<lowerEndpointGap xi lo L vmin)
    (hgapU : 0<upperEndpointGap xi hi U vmax) :
    let gap := min (lowerEndpointGap xi lo L vmin) (upperEndpointGap xi hi U vmax)
    independentTwo eta v b q≤ outsideTwo v lam-vmin*gap^2+
      (broadcastExposureModulus eta W R/(xi*d))*|price-lam| := by
  let p := EqualCapacity.demand xi b lam
  have hb : 0<b := hd.trans_le hdb
  have hp : p∈ Icc (0:ℝ) 1 := EqualCapacity.demand_bounds xi b lam
  have hq : q∈ Icc (0:ℝ) 1 := ⟨ht.1,ht.2.1⟩
  have hs := zero_outside_box_uniform_gap hxi hxi1 heta hL hLU hUv hvmin hvmax
    hlo hllo hlhi hboxlo hboxhi hb hout (EqualCapacity.demand_spec hxi hxi1 hb lam) hgapL hgapU
  have hdiff : |q-p|≤|price-lam|/(xi*d) := by
    rw [scalarThreshold_eq_demand hxi hxi1 hb ht]
    exact (demand_price_lipschitz hxi hb price lam).trans
      (div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos hxi hd)
        (mul_le_mul_of_nonneg_left hdb hxi.le))
  have hmod := broadcastExposureModulus_nonneg (eta:=eta)
    ((abs_nonneg v).trans hvW) ((hd.trans_le hdb).le.trans hbR)
  have hpay := independentTwo_lipschitz (eta:=eta) (U:=R) hvW
    (by rw [abs_of_pos hb]; exact hbR) hq hp
  have hdif := mul_le_mul_of_nonneg_left hdiff hmod
  have hr := le_abs_self (independentTwo eta v b q-independentTwo eta v b p)
  dsimp only [p] at hr hpay
  have he : broadcastExposureModulus eta W R*(|price-lam|/(xi*d))=
      (broadcastExposureModulus eta W R/(xi*d))*|price-lam| := by ring
  rw [he] at hdif
  linarith [hs.2]

end FCAppendix.Affine.Hybrid.Native02
