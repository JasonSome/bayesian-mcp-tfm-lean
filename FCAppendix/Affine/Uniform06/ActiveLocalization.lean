import FCAppendix.Affine.ClippedResidualRoots
import FCAppendix.Affine.Uniform07.Parameters
import Mathlib

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.ActiveLocalization

open FCAppendix.Affine.ClippedResidual Set Filter MeasureTheory

def product (ξ v L b : ℝ) : ℝ :=
  let p := exposure ξ L b
  v*(2*p-p^2)-2*b*p*(1-ξ*p)

def bestBid (ξ v L : ℝ) : ℝ := L*v/((1-ξ)*v+ξ*L)
def bestExposure (v L : ℝ) : ℝ := 1-L/v
def bestValue (v L : ℝ) : ℝ := (v-L)^2/v

theorem exposure_zero_of_bid_le {ξ L b : ℝ}
    (_hξ : 0 < ξ) (_hL : 0 < L) (hb : b ≤ L) : exposure ξ L b=0 := by
  unfold exposure
  rw [max_eq_right hb, max_eq_left (sub_nonpos.mpr hb)]
  simp

theorem interior_exposure_identity {ξ L b : ℝ}
    (hξ : 0 < ξ) (hL : 0 < L)
    (hp0 : 0 < exposure ξ L b) (hp1 : exposure ξ L b < 1) :
    L < b ∧ exposure ξ L b=(1-L/b)/ξ ∧
      b=L/(1-ξ*exposure ξ L b) := by
  have hb : L < b := by
    by_contra h
    rw [exposure_zero_of_bid_le hξ hL (le_of_not_gt h)] at hp0
    exact (lt_irrefl _ hp0).elim
  have hb0 := hL.trans hb
  have hp : exposure ξ L b=(b-L)/(ξ*b) := by
    unfold exposure at hp1 ⊢
    rw [max_eq_left hb.le,max_eq_right (sub_nonneg.mpr hb.le)] at hp1 ⊢
    rcases min_lt_iff.mp hp1 with hbad | hratio
    · exact (lt_irrefl (1:ℝ) hbad).elim
    · exact min_eq_right hratio.le
  have hrel : (1-L/b)/ξ=(b-L)/(ξ*b) := by
    field_simp [hξ.ne',hb0.ne']
  have he : 1-ξ*exposure ξ L b=L/b := by
    rw [hp]
    field_simp [hξ.ne',hb0.ne']
    ring
  refine ⟨hb,hp.trans hrel.symm,?_⟩
  rw [he]
  field_simp [hL.ne',hb0.ne']

theorem effective_payment_lower {ξ L b : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hL : 0 < L) :
    L*exposure ξ L b ≤ b*exposure ξ L b*(1-ξ*exposure ξ L b) := by
  let p := exposure ξ L b
  change L*p ≤ b*p*(1-ξ*p)
  have hp0 : 0 ≤ p := exposure_nonneg hξ hL
  have hp1 : p ≤ 1 := exposure_le_one _ _ _
  by_cases hpz : p=0
  · simp [hpz]
  by_cases hpo : p=1
  · have hb : L < b := by
      by_contra h
      have hz := exposure_zero_of_bid_le hξ hL (le_of_not_gt h)
      change p=0 at hz
      linarith
    have hb0 := hL.trans hb
    have hratio : 1 ≤ (b-L)/(ξ*b) := by
      have h : min 1 ((b-L)/(ξ*b))=1 := by
        simpa [p,exposure,max_eq_left hb.le,max_eq_right (sub_nonneg.mpr hb.le)] using hpo
      exact (min_eq_left_iff.mp h)
    have hcost := (le_div_iff₀ (mul_pos hξ hb0)).mp hratio
    rw [hpo]
    nlinarith
  · obtain ⟨hb,hp,hbid⟩ := interior_exposure_identity hξ hL
      (lt_of_le_of_ne hp0 (Ne.symm hpz)) (lt_of_le_of_ne hp1 hpo)
    have hb0 := hL.trans hb
    have he : b*(1-ξ*p)=L := by
      dsimp [p]
      rw [hp]
      field_simp [hξ.ne',hb0.ne']
      ring
    nlinarith

theorem quadratic_identity {v L p : ℝ} (hv : v ≠ 0) :
    v*(2*p-p^2)-2*L*p=bestValue v L-v*(p-bestExposure v L)^2 := by
  unfold bestValue bestExposure
  field_simp [hv]
  ring

theorem product_square_upper {ξ v L b : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hL : 0 < L) (hv : 0 < v) :
    product ξ v L b ≤ bestValue v L-
      v*(exposure ξ L b-bestExposure v L)^2 := by
  have hcost := effective_payment_lower hξ hξ1 hL (b := b)
  rw [← quadratic_identity hv.ne']
  unfold product
  dsimp only
  nlinarith

theorem bestBid_bounds {ξ v L : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hL : 0 < L) (hLv : L < v) :
    L < bestBid ξ v L ∧ bestBid ξ v L < v := by
  have hv := hL.trans hLv
  have hκ : 0 < 1-ξ := sub_pos.mpr hξ1
  have hd : 0 < (1-ξ)*v+ξ*L := add_pos (mul_pos hκ hv) (mul_pos hξ hL)
  constructor
  · apply (lt_div_iff₀ hd).mpr
    have h := mul_pos (mul_pos hξ hL) (sub_pos.mpr hLv)
    nlinarith
  · apply (div_lt_iff₀ hd).mpr
    have h := mul_pos (mul_pos hκ hv) (sub_pos.mpr hLv)
    nlinarith

theorem bestBid_exposure {ξ v L : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hL : 0 < L) (hLv : L < v) :
    exposure ξ L (bestBid ξ v L)=bestExposure v L := by
  have hv := hL.trans hLv
  have hb := bestBid_bounds hξ hξ1 hL hLv
  have hb0 := hL.trans hb.1
  have hp0 : 0 < bestExposure v L := by
    unfold bestExposure
    have h := (div_lt_one hv).mpr hLv
    linarith
  have hp1 : bestExposure v L < 1 := by
    unfold bestExposure
    linarith [div_pos hL hv]
  have hd : 0 < (1-ξ)*v+ξ*L :=
    add_pos (mul_pos (sub_pos.mpr hξ1) hv) (mul_pos hξ hL)
  have hform : (bestBid ξ v L-L)/(ξ*bestBid ξ v L)=bestExposure v L := by
    apply (div_eq_iff (mul_ne_zero hξ.ne' hb0.ne')).2
    unfold bestBid bestExposure
    have hd' : v-v*ξ+ξ*L ≠ 0 := by nlinarith [hd]
    have hd'' : v*(1-ξ)+L*ξ ≠ 0 := by nlinarith [hd]
    field_simp [hv.ne',hd.ne',hd',hd'']
    ring
  unfold exposure
  rw [max_eq_left hb.1.le,max_eq_right (sub_nonneg.mpr hb.1.le),hform,
    min_eq_right hp1.le]

theorem bestBid_product {ξ v L : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hL : 0 < L) (hLv : L < v) :
    product ξ v L (bestBid ξ v L)=bestValue v L := by
  have hv := hL.trans hLv
  have hd : 0 < (1-ξ)*v+ξ*L :=
    add_pos (mul_pos (sub_pos.mpr hξ1) hv) (mul_pos hξ hL)
  have hexp := bestBid_exposure hξ hξ1 hL hLv
  have hp0 : 0 < exposure ξ L (bestBid ξ v L) := by
    rw [hexp]
    dsimp [bestExposure]
    exact sub_pos.mpr ((div_lt_one hv).mpr hLv)
  have hp1 : exposure ξ L (bestBid ξ v L) < 1 := by
    rw [hexp]
    dsimp [bestExposure]
    linarith [div_pos hL hv]
  have hden : 0 < 1-ξ*exposure ξ L (bestBid ξ v L) := by
    nlinarith [exposure_le_one ξ L (bestBid ξ v L)]
  have hc := (eq_div_iff hden.ne').mp
    (interior_exposure_identity hξ hL hp0 hp1).2.2
  unfold product
  change v*(2*exposure ξ L (bestBid ξ v L)-exposure ξ L (bestBid ξ v L)^2)-
    2*bestBid ξ v L*exposure ξ L (bestBid ξ v L)*
      (1-ξ*exposure ξ L (bestBid ξ v L))=bestValue v L
  have hcost : 2*bestBid ξ v L*exposure ξ L (bestBid ξ v L)*
      (1-ξ*exposure ξ L (bestBid ξ v L))=2*L*exposure ξ L (bestBid ξ v L) := by
    calc
      _ = 2*(bestBid ξ v L*(1-ξ*exposure ξ L (bestBid ξ v L)))*
        exposure ξ L (bestBid ξ v L) := by ring
      _ = _ := by rw [hc]
  rw [hcost, quadratic_identity hv.ne', hexp]
  simp

theorem finite_IC_exposure_error {ξ v L b e : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hL : 0 < L) (hLv : L < v)
    (U : ℝ → ℝ)
    (hused : |U b-product ξ v L b| ≤ e)
    (htest : |U (bestBid ξ v L)-product ξ v L (bestBid ξ v L)| ≤ e)
    (hIC : U (bestBid ξ v L) ≤ U b) :
    v*(exposure ξ L b-bestExposure v L)^2 ≤ 2*e := by

  have ht := bestBid_product hξ hξ1 hL hLv
  have hu := product_square_upper hξ hξ1 hL (hL.trans hLv) (b := b)
  rw [ht] at htest
  have hused' := abs_le.mp hused
  have htest' := abs_le.mp htest
  linarith

theorem finite_IC_bid_error {ξ v L b e d : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hL : 0 < L) (hLv : L < v)
    (hd : 0 < d) (hd0 : d ≤ bestExposure v L)
    (hd1 : d ≤ 1-bestExposure v L) (herr : 2*e < v*d^2)
    (U : ℝ → ℝ)
    (hused : |U b-product ξ v L b| ≤ e)
    (htest : |U (bestBid ξ v L)-product ξ v L (bestBid ξ v L)| ≤ e)
    (hIC : U (bestBid ξ v L) ≤ U b) :
    |b-bestBid ξ v L| ≤ L*ξ*d/(1-ξ)^2 := by
  let p := exposure ξ L b
  let q := bestExposure v L
  have hv := hL.trans hLv
  have hκ : 0 < 1-ξ := sub_pos.mpr hξ1
  have hs := finite_IC_exposure_error hξ hξ1 hL hLv U hused htest hIC
  have hpq : |p-q| < d := by
    by_contra h
    have hge : d ≤ |p-q| := le_of_not_gt h
    have hsq : d^2 ≤ (p-q)^2 := by nlinarith [sq_abs (p-q)]
    have hm := mul_le_mul_of_nonneg_left hsq hv.le
    exact (not_le_of_gt herr) (hs.trans' hm)
  have hpb : 0 < p ∧ p < 1 := by
    have ha := abs_lt.mp hpq
    constructor <;> dsimp [q] at * <;> linarith
  obtain ⟨hb,hp,hbid⟩ := interior_exposure_identity hξ hL hpb.1 hpb.2
  change b=L/(1-ξ*p) at hbid
  have hqb : 0 < q ∧ q < 1 := by
    constructor
    · exact hd.trans_le hd0
    · linarith
  have hdp : 1-ξ ≤ 1-ξ*p := by nlinarith [hpb.2]
  have hdq : 1-ξ ≤ 1-ξ*q := by nlinarith [hqb.2]
  have hdp0 := hκ.trans_le hdp
  have hdq0 := hκ.trans_le hdq
  have hprod : (1-ξ)^2 ≤ (1-ξ*p)*(1-ξ*q) := by
    simpa only [pow_two] using mul_le_mul hdp hdq hκ.le hdp0.le
  have hbest : bestBid ξ v L=L/(1-ξ*q) := by
    have he : exposure ξ L (bestBid ξ v L)=q := bestBid_exposure hξ hξ1 hL hLv
    have h0 : 0 < exposure ξ L (bestBid ξ v L) := by rw [he]; exact hqb.1
    have h1 : exposure ξ L (bestBid ξ v L) < 1 := by rw [he]; exact hqb.2
    simpa only [he] using (interior_exposure_identity hξ hL h0 h1).2.2
  have hdiff : b-bestBid ξ v L=
      L*ξ*(p-q)/((1-ξ*p)*(1-ξ*q)) := by
    rw [hbid,hbest]
    field_simp [hdp0.ne',hdq0.ne']
    ring
  rw [hdiff,abs_div,abs_mul,abs_mul,abs_of_pos hL,abs_of_pos hξ,
    abs_of_pos (mul_pos hdp0 hdq0)]
  calc
    _ ≤ L*ξ*|p-q| /(1-ξ)^2 :=
      div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hκ) hprod
    _ ≤ L*ξ*d/(1-ξ)^2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpq.le (mul_pos hL hξ).le)
        (sq_nonneg _)

theorem bestBid_multiplier_lipschitz {ξ v L L' : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hv : 0 < v)
    (hL : 0 ≤ L) (hL' : 0 ≤ L') :
    |bestBid ξ v L-bestBid ξ v L'| ≤ |L-L'| /(1-ξ) := by
  have hκ : 0 < 1-ξ := sub_pos.mpr hξ1
  have hd : 0 < (1-ξ)*v+ξ*L :=
    add_pos_of_pos_of_nonneg (mul_pos hκ hv) (mul_nonneg hξ.le hL)
  have hd' : 0 < (1-ξ)*v+ξ*L' :=
    add_pos_of_pos_of_nonneg (mul_pos hκ hv) (mul_nonneg hξ.le hL')
  have hdlo : (1-ξ)*v ≤ (1-ξ)*v+ξ*L :=
    le_add_of_nonneg_right (mul_nonneg hξ.le hL)
  have hdlo' : (1-ξ)*v ≤ (1-ξ)*v+ξ*L' :=
    le_add_of_nonneg_right (mul_nonneg hξ.le hL')
  have hden : ((1-ξ)*v)^2 ≤
      ((1-ξ)*v+ξ*L)*((1-ξ)*v+ξ*L') := by
    simpa only [pow_two] using mul_le_mul hdlo hdlo'
      (mul_pos hκ hv).le hd.le
  have he : bestBid ξ v L-bestBid ξ v L' =
      (L-L')*(1-ξ)*v^2/(((1-ξ)*v+ξ*L)*((1-ξ)*v+ξ*L')) := by
    unfold bestBid
    field_simp [hd.ne',hd'.ne']
    ring
  rw [he,abs_div,abs_mul,abs_mul,abs_of_pos hκ,abs_of_nonneg (sq_nonneg v),
    abs_of_pos (mul_pos hd hd')]
  calc
    _ ≤ |L-L'| *(1-ξ)*v^2/((1-ξ)*v)^2 :=
      div_le_div_of_nonneg_left (by positivity)
        (sq_pos_of_pos (mul_pos hκ hv)) hden
    _ = _ := by field_simp [hκ.ne',hv.ne']

section UniformAdapter

variable (C : ℕ → Type*)
    (G : (m : ℕ) → C m → Measure (ℝ × ℝ))
    (L : (m : ℕ) → C m → ℝ)
    (U : (m : ℕ) → C m → ℝ → ℝ → ℝ)
    (A : (m : ℕ) → C m → ℝ → Set ℝ)

theorem uniform_active_graph_from_early_menu
    {ξ t lam : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hlam : 0 < lam) (hlamt : lam < t)
    (hIC : ∀ m (E : C m), ∀ᵐ p ∂G m E,
      p.1 ∈ Icc (0:ℝ) t ∧ p.2 ∈ A m E p.1 ∧
        ∀ b ∈ A m E p.1, U m E p.1 b ≤ U m E p.1 p.2)
    (hcomparison : ∀ m (E : C m) v, lam < v → v ≤ t →
      0 < L m E → L m E < v → bestBid ξ v (L m E) ∈ A m E v)
    (hmenu : ∀ e > (0:ℝ), ∀ᶠ m in atTop, ∀ E : C m,
      ∀ v ∈ Icc (0:ℝ) t, ∀ b ∈ A m E v,
        |U m E v b-product ξ v (L m E) b| ≤ e)
    (hroot : ∀ d > (0:ℝ), ∀ᶠ m in atTop, ∀ E : C m, |L m E-lam| < d) :
    ∀ a > (0:ℝ), ∀ ε > (0:ℝ), ∀ᶠ m in atTop, ∀ E : C m,
      ∀ᵐ p ∂G m E, p.1 ∈ Icc (lam+a) t →
        |p.2-bestBid ξ p.1 lam| < ε := by
  intro a ha ε hε
  have ht := hlam.trans hlamt
  have hκ : 0 < 1-ξ := sub_pos.mpr hξ1
  let d : ℝ := min (ε*(1-ξ)^2/(4*t*ξ)) (min (a/(2*t)) (lam/(2*t)))
  have hd : 0 < d := by dsimp [d]; positivity
  have hdε : d ≤ ε*(1-ξ)^2/(4*t*ξ) := min_le_left _ _
  have hda : d ≤ a/(2*t) := (min_le_right _ _).trans (min_le_left _ _)
  have hdlam : d ≤ lam/(2*t) := (min_le_right _ _).trans (min_le_right _ _)
  let r : ℝ := min (lam/2) (min (a/2) (ε*(1-ξ)/4))
  have hr : 0 < r := by dsimp [r]; positivity
  have hrlam : r ≤ lam/2 := min_le_left _ _
  have hra : r ≤ a/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hrε : r ≤ ε*(1-ξ)/4 := (min_le_right _ _).trans (min_le_right _ _)
  let e : ℝ := lam*d^2/8
  have he : 0 < e := by dsimp [e]; positivity
  filter_upwards [hmenu e he,hroot r hr] with m hm hLm
  intro E
  filter_upwards [hIC m E] with p hp hpv
  have hroot' := abs_lt.mp (hLm E)
  have hL0 : 0 < L m E := by linarith
  have hLv : L m E < p.1 := by linarith [hpv.1]
  have hv : 0 < p.1 := hL0.trans hLv
  have hLt : L m E ≤ t := hLv.le.trans hpv.2
  have hLhalf : lam/2 ≤ L m E := by linarith
  have hgap : a/2 ≤ p.1-L m E := by linarith [hpv.1]
  have hq0 : d ≤ bestExposure p.1 (L m E) := by
    have h1 : d*p.1 ≤ d*t := mul_le_mul_of_nonneg_left hpv.2 hd.le
    have h2 : d*t ≤ a/2 := by
      have hh := (le_div_iff₀ (show 0 < 2*t by positivity)).mp hda
      nlinarith
    unfold bestExposure
    have h3 : d ≤ (p.1-L m E)/p.1 := (le_div_iff₀ hv).mpr (by linarith)
    have hid : (p.1-L m E)/p.1=1-L m E/p.1 := by field_simp [hv.ne']
    rwa [hid] at h3
  have hq1 : d ≤ 1-bestExposure p.1 (L m E) := by
    have h1 : d*p.1 ≤ d*t := mul_le_mul_of_nonneg_left hpv.2 hd.le
    have h2 : d*t ≤ lam/2 := by
      have hh := (le_div_iff₀ (show 0 < 2*t by positivity)).mp hdlam
      nlinarith
    unfold bestExposure
    have h3 : d ≤ L m E/p.1 := (le_div_iff₀ hv).mpr (by linarith)
    linarith
  have hsmall : 2*e < p.1*d^2 := by
    dsimp [e]
    have hd2 : 0 < d^2 := sq_pos_of_pos hd
    have hvlam : lam ≤ p.1 := by linarith [hpv.1]
    nlinarith
  have hlegal := hcomparison m E p.1 (by linarith [hpv.1]) hpv.2 hL0 hLv
  have hb := finite_IC_bid_error hξ hξ1 hL0 hLv hd hq0 hq1 hsmall
    (U m E p.1) (hm E p.1 hp.1 p.2 hp.2.1)
    (hm E p.1 hp.1 _ hlegal) (hp.2.2 _ hlegal)
  have hb' : |p.2-bestBid ξ p.1 (L m E)| ≤ ε/4 := by
    have hstep : L m E*ξ*d/(1-ξ)^2 ≤ t*ξ*d/(1-ξ)^2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLt hξ.le) hd.le)
        (sq_nonneg _)
    have hfin : t*ξ*d/(1-ξ)^2 ≤ ε/4 := by
      have hh := (le_div_iff₀ (show 0 < 4*t*ξ by positivity)).mp hdε
      apply (div_le_iff₀ (sq_pos_of_pos hκ)).mpr
      nlinarith
    exact hb.trans (hstep.trans hfin)
  have hrootbid := bestBid_multiplier_lipschitz hξ hξ1 hv hL0.le hlam.le
  have hrootbid' : |bestBid ξ p.1 (L m E)-bestBid ξ p.1 lam| ≤ ε/4 := by
    have hsmall' : |L m E-lam| /(1-ξ) ≤ ε/4 :=
      (div_le_iff₀ hκ).mpr (by linarith [(hLm E).le])
    exact hrootbid.trans hsmall'
  calc
    _ ≤ |p.2-bestBid ξ p.1 (L m E)|+
        |bestBid ξ p.1 (L m E)-bestBid ξ p.1 lam| := abs_sub_le _ _ _
    _ ≤ ε/4+ε/4 := add_le_add hb' hrootbid'
    _ < ε := by linarith

end UniformAdapter

end FCAppendix.Affine.Uniform06.ActiveLocalization
