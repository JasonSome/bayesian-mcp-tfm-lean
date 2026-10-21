import FCAppendix.Affine.Uniform05LawGuards
import FCAppendix.Affine.Uniform07.OutcomeIntegrals

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open Set

def productPayoff (xi v L b : ℝ) : ℝ :=
  let p := ClippedResidual.exposure xi L b
  v*(2*p-p^2)-2*b*p*(1-xi*p)

def optimalExposure (L v : ℝ) : ℝ := if L< v then 1-L/v else 0
def activeBidAt (xi L v : ℝ) : ℝ := L*v/((1-xi)*v+xi*L)

lemma continuous_product_fixed_root {xi L : ℝ} (hxi : 0< xi) (hL : 0< L) :
    Continuous (fun p : ℝ×ℝ=> productPayoff xi p.1 L p.2) := by
  have hp : Continuous (fun p : ℝ×ℝ=> ClippedResidual.exposure xi L p.2) := by
    unfold ClippedResidual.exposure
    apply continuous_const.min
    apply (continuous_const.max (continuous_snd.sub continuous_const)).div
      (continuous_const.mul (continuous_snd.max continuous_const))
    intro p
    exact (mul_pos hxi (hL.trans_le (le_max_right p.2 L))).ne'
  exact (continuous_fst.mul ((continuous_const.mul hp).sub (hp.pow 2))).sub
    (((continuous_const.mul continuous_snd).mul hp).mul
      (continuous_const.sub (continuous_const.mul hp)))

lemma activeBidAt_den_pos {xi L v : ℝ} (hxi : 0< xi) (hxi1 : xi<1)
    (hL : 0< L) (hv : 0≤ v) : 0<(1-xi)*v+xi*L := by
  have h := mul_pos hxi hL
  have h' := mul_nonneg (sub_pos.mpr hxi1).le hv
  linarith

lemma product_zero {xi v L b : ℝ} (hb : b≤ L) : productPayoff xi v L b=0 := by
  simp [productPayoff,ClippedResidual.exposure_zero hb]

lemma product_active_quadratic {xi v L b : ℝ}
    (hxi : 0< xi) (hL : 0< L) (hb : L< b) (hclip : (1-xi)*b≤ L) :
    productPayoff xi v L b=
      v*(2*ClippedResidual.exposure xi L b-ClippedResidual.exposure xi L b^2)-
        2*L*ClippedResidual.exposure xi L b := by
  rw [productPayoff,ClippedResidual.exposure_of_between hxi hL hb hclip]
  field_simp [hxi.ne',(hL.trans hb).ne']
  ring

lemma product_active_square {xi v L b : ℝ}
    (hxi : 0< xi) (hL : 0< L) (hb : L< b)
    (hclip : (1-xi)*b≤ L) (hv : v≠0) :
    productPayoff xi v L b=(v-L)^2/v-
      v*(ClippedResidual.exposure xi L b-(1-L/v))^2 := by
  rw [product_active_quadratic hxi hL hb hclip]
  exact Uniform05.product_payoff_complete_square hv

lemma activeBidAt_bounds {xi L v : ℝ} (hxi : 0< xi) (hxi1 : xi<1)
    (hL : 0< L) (hv : L< v) :
    L< activeBidAt xi L v ∧ activeBidAt xi L v< v ∧
      (1-xi)*activeBidAt xi L v< L := by
  have hv0 := hL.trans hv
  have hd := activeBidAt_den_pos hxi hxi1 hL hv0.le
  unfold activeBidAt
  refine ⟨(lt_div_iff₀ hd).mpr ?_,(div_lt_iff₀ hd).mpr ?_,?_⟩
  · nlinarith [mul_pos (mul_pos hxi hL) (sub_pos.mpr hv)]
  · nlinarith [mul_pos (mul_pos (sub_pos.mpr hxi1) hv0) (sub_pos.mpr hv)]
  · rw [← mul_div_assoc]
    apply (div_lt_iff₀ hd).mpr
    nlinarith [mul_pos hxi (sq_pos_of_pos hL)]

lemma activeBidAt_exposure {xi L v : ℝ} (hxi : 0< xi) (hxi1 : xi<1)
    (hL : 0< L) (hv : L< v) :
    ClippedResidual.exposure xi L (activeBidAt xi L v)=1-L/v := by
  obtain ⟨hLB,hBv,hkB⟩ := activeBidAt_bounds hxi hxi1 hL hv
  rw [ClippedResidual.exposure_of_between hxi hL hLB hkB.le]
  have hd := activeBidAt_den_pos hxi hxi1 hL (hL.trans hv).le
  unfold activeBidAt
  field_simp [hxi.ne',hL.ne',(hL.trans hv).ne',hd.ne']
  ring

lemma activeBidAt_product {xi L v : ℝ} (hxi : 0< xi) (hxi1 : xi<1)
    (hL : 0< L) (hv : L< v) :
    productPayoff xi v L (activeBidAt xi L v)=(v-L)^2/v := by
  obtain ⟨hLB,hBv,hkB⟩ := activeBidAt_bounds hxi hxi1 hL hv
  rw [product_active_square hxi hL hLB hkB.le (hL.trans hv).ne',
    activeBidAt_exposure hxi hxi1 hL hv]
  simp

lemma activeBidAt_mono_value {xi L v w : ℝ} (hxi : 0< xi) (hxi1 : xi<1)
    (hL : 0< L) (hv : 0≤ v) (hvw : v≤ w) :
    activeBidAt xi L v≤ activeBidAt xi L w := by
  have hdv := activeBidAt_den_pos hxi hxi1 hL hv
  have hdw := activeBidAt_den_pos hxi hxi1 hL (hv.trans hvw)
  unfold activeBidAt
  apply (div_le_div_iff₀ hdv hdw).mpr
  nlinarith [mul_nonneg (mul_nonneg hxi.le (sq_nonneg L)) (sub_nonneg.mpr hvw)]

lemma activeBidAt_mono_root {xi L K v : ℝ} (hxi : 0< xi) (hxi1 : xi<1)
    (hL : 0< L) (hLK : L≤ K) (hv : 0≤ v) :
    activeBidAt xi L v≤ activeBidAt xi K v := by
  have hdL := activeBidAt_den_pos hxi hxi1 hL hv
  have hdK := activeBidAt_den_pos hxi hxi1 (hL.trans_le hLK) hv
  unfold activeBidAt
  apply (div_le_div_iff₀ hdL hdK).mpr
  nlinarith [mul_nonneg (mul_nonneg (sub_pos.mpr hxi1).le (sq_nonneg v))
    (sub_nonneg.mpr hLK)]

lemma product_upper_bound {xi L U v b : ℝ}
    (hxi : 0< xi) (hxi1 : xi<1) (hL : 0< L)
    (hclip : (1-xi)*U≤ L) (hbU : b≤ U) (hv : L< v) :
    productPayoff xi v L b≤(v-L)^2/v := by
  by_cases hb : b≤ L
  · rw [product_zero hb]
    exact div_nonneg (sq_nonneg _) (hL.trans hv).le
  · have hkb := (mul_le_mul_of_nonneg_left hbU (sub_pos.mpr hxi1).le).trans hclip
    rw [product_active_square hxi hL (lt_of_not_ge hb) hkb (hL.trans hv).ne']
    have hn := mul_nonneg (hL.trans hv).le
      (sq_nonneg (ClippedResidual.exposure xi L b-(1-L/v)))
    linarith

lemma product_maximum_unique {xi L U v b : ℝ}
    (hxi : 0< xi) (hxi1 : xi<1) (hL : 0< L)
    (hclip : (1-xi)*U≤ L) (hbU : b≤ U) (hv : L< v)
    (heq : productPayoff xi v L b=(v-L)^2/v) : b=activeBidAt xi L v := by
  have hv0 := hL.trans hv
  have hb : L< b := by
    by_contra hn
    rw [product_zero (le_of_not_gt hn)] at heq
    have hp := div_pos (sq_pos_of_pos (sub_pos.mpr hv)) hv0
    linarith
  have hkb := (mul_le_mul_of_nonneg_left hbU (sub_pos.mpr hxi1).le).trans hclip
  have hs := product_active_square hxi hL hb hkb hv0.ne'
  have hp : ClippedResidual.exposure xi L b=1-L/v := by
    have hz : (ClippedResidual.exposure xi L b-(1-L/v))^2=0 := by nlinarith
    have := sq_eq_zero_iff.mp hz
    linarith
  rw [ClippedResidual.exposure_of_between hxi hL hb hkb] at hp
  have hb0 := hL.trans hb
  have hd := activeBidAt_den_pos hxi hxi1 hL hv0.le
  unfold activeBidAt
  apply (eq_div_iff hd.ne').mpr
  field_simp [hxi.ne',hb0.ne',hv0.ne'] at hp
  nlinarith

lemma source_activeBid_eq (i : Uniform07.Row) (v : ℝ) :
    activeBidAt (Uniform05.xi i) (Uniform05.lambda i) v=Uniform05.activeBid i v := by
  rfl

theorem source_activeBid_feasible (i : Uniform07.Row) {v : ℝ}
    (hv : Uniform05.lambda i< v) (hvt : v≤ Uniform05.t i) :
    Uniform05.activeBid i v∈Icc (Uniform05.floorBid i v) (min v (Uniform05.cap i)) := by
  have hxi := Uniform05.xi_range i
  have hL := Uniform05.lambda_pos i
  have hb := activeBidAt_bounds hxi.1 hxi.2 hL hv
  have hmax := activeBidAt_mono_value hxi.1 hxi.2 hL (hL.trans hv).le hvt
  simp only [source_activeBid_eq] at hb hmax
  have hf := Uniform05.floor_le_chi_positivePart i v
  have hp : max 0 (v-Uniform05.v0 i)≤ Uniform05.t i-Uniform05.v0 i := by
    apply max_le
    · dsimp [Uniform05.v0]
      linarith [Uniform05.t_pos i]
    · linarith
  have hfm := mul_le_mul_of_nonneg_left hp
    (by norm_num [Uniform05.chi] : 0≤ Uniform05.chi)
  have hft := Uniform05.full_floor_max_below_lambda i
  constructor
  · linarith [hb.1]
  · apply le_min hb.2.1.le
    have ht := Uniform05.t_pos i
    unfold Uniform05.cap
    linarith

theorem source_active_maximizer (i : Uniform07.Row) {v b : ℝ}
    (hv : Uniform05.lambda i< v) (hvt : v≤ Uniform05.t i)
    (hb : b∈Icc (Uniform05.floorBid i v) (min v (Uniform05.cap i)))
    (hmax : ∀a∈Icc (Uniform05.floorBid i v) (min v (Uniform05.cap i)),
      productPayoff (Uniform05.xi i) v (Uniform05.lambda i) a≤
        productPayoff (Uniform05.xi i) v (Uniform05.lambda i) b) :
    b=Uniform05.activeBid i v := by
  have hxi := Uniform05.xi_range i
  have hL := Uniform05.lambda_pos i
  have hclip : (1-Uniform05.xi i)*Uniform05.cap i≤ Uniform05.lambda i := by
    have hr := Uniform05.numerical_root_receipt_gap i
    have hx := Uniform05.x_range i
    have ht := Uniform05.t_pos i
    change Uniform05.kappa i*Uniform05.cap i≤ Uniform05.lambda i
    cases i <;> dsimp [Uniform05.lambda,Uniform05.x] at * <;> linarith
  have hopt := hmax _ (source_activeBid_feasible i hv hvt)
  rw [← source_activeBid_eq,
    activeBidAt_product hxi.1 hxi.2 hL hv] at hopt
  have hup := product_upper_bound hxi.1 hxi.2 hL hclip
    (hb.2.trans (min_le_right _ _)) hv
  exact (product_maximum_unique hxi.1 hxi.2 hL hclip
    (hb.2.trans (min_le_right _ _)) hv (le_antisymm hup hopt)).trans
      (source_activeBid_eq i v)

theorem source_inactive_payoff (i : Uniform07.Row) {v b : ℝ}
    (hv : v≤ Uniform05.lambda i) (hb : b≤ v) :
    productPayoff (Uniform05.xi i) v (Uniform05.lambda i) b=0 :=
  product_zero (hb.trans hv)

lemma active_utility_mono {L s v : ℝ} (hL : 0< L) (hLs : L< s) (hsv : s≤ v) :
    (s-L)^2/s≤(v-L)^2/v := by
  have hs := hL.trans hLs
  have hv := hs.trans_le hsv
  apply (div_le_div_iff₀ hs hv).mpr
  have hp : 0≤(v-s)*(s*v-L^2) := by
    apply mul_nonneg (sub_nonneg.mpr hsv)
    have hs2 : L^2< s^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsv hs.le]
  nlinarith

theorem floored_type_product_gap (i : Uniform07.Row) {v : ℝ}
    (_hv0 : 0≤ v) (hvt : v≤ Uniform05.t i) (hf : 0< Uniform05.floorBid i v) :
    0<(Uniform05.s i-Uniform05.lambda i)^2/Uniform05.s i ∧
    ∃ b∈Icc (Uniform05.floorBid i v) (min v (Uniform05.cap i)),
      (Uniform05.s i-Uniform05.lambda i)^2/Uniform05.s i≤
        productPayoff (Uniform05.xi i) v (Uniform05.lambda i) b := by
  have ht := Uniform05.t_pos i
  have hL := Uniform05.lambda_pos i
  have hs : Uniform05.lambda i< Uniform05.s i := by
    unfold Uniform05.s
    linarith
  have hvs : Uniform05.s i< v := by
    by_contra hn
    rw [Uniform05.floor_zero_below_s i ht (le_of_not_gt hn)] at hf
    exact (lt_irrefl 0) hf
  have hval := hs.trans hvs
  refine ⟨div_pos (sq_pos_of_pos (sub_pos.mpr hs)) (hL.trans hs),
    Uniform05.activeBid i v,source_activeBid_feasible i hval hvt,?_⟩
  rw [← source_activeBid_eq,activeBidAt_product (Uniform05.xi_range i).1
    (Uniform05.xi_range i).2 hL hval]
  exact active_utility_mono hL hs hvs.le

end FCAppendix.Affine.UniformFinite
