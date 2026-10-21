import FCAppendix.Affine.Hybrid.Menu

noncomputable section
namespace FCAppendix.Affine.Hybrid.Tail03
open Set Filter Topology MeasureTheory
open scoped BigOperators

structure Center where
  eta1 : ℝ
  eta2 : ℝ
  theta : ℝ
  eta1_pos : 0 < eta1
  eta12 : eta1 < eta2
  eta2_lt_one : eta2 < 1
  theta_pos : 0 < theta
  theta_small : theta < 1/10

def xi (p : Center) : ℝ := (1-p.eta2)/2
def kappa (p : Center) : ℝ := 1-xi p
def delta (p : Center) : ℝ := p.theta^2
def lowMass (p : Center) : ℝ := 1/100+delta p
def activeMass (p : Center) : ℝ := 67/100-delta p
def partialMass (_p : Center) : ℝ := 8/25
def bulkValue (p : Center) : ℝ := 11*xi p/(10*p.theta)
def B (p : Center) : ℝ := 1+xi p/50
def R (p : Center) : ℝ := 1-37*xi p/40
def width (p : Center) : ℝ := B p-1
def q0 : Fin 2 → ℝ := ![19/20,9/10]
def lambda0 (p : Center) (r : Fin 2) : ℝ := 1-xi p*q0 r
def regimeWeight (p : Center) : Fin 2 → ℝ := ![1-p.theta,p.theta]
def e0 (p : Center) : Fin 2 → ℝ :=
  ![10*delta p/(9*activeMass p),5*(partialMass p+delta p)/(4*activeMass p)]
def deficit (p : Center) : Fin 2 → ℝ :=
  ![delta p/activeMass p,(partialMass p+delta p)/activeMass p]

def exposure (p : Center) (lam : Fin 2 → ℝ) (r : Fin 2) (b : ℝ) : ℝ :=
  (1-lam r/b)/xi p
def mixedProb (p : Center) (r : Fin 2) (b : ℝ) : ℝ :=
  e0 p r*((B p-b)/width p)^2
def served (p : Center) (lam : Fin 2 → ℝ) (b : ℝ) : ℝ :=
  1-∑ r, regimeWeight p r*mixedProb p r b*(1-exposure p lam r b)^2
def duplicates (p : Center) (lam : Fin 2 → ℝ) (b : ℝ) : ℝ :=
  ∑ r, regimeWeight p r*mixedProb p r b*(exposure p lam r b)^2
def load (p : Center) (lam : Fin 2 → ℝ) (b : ℝ) : ℝ :=
  served p lam b+duplicates p lam b
def payment (p : Center) (lam : Fin 2 → ℝ) (b : ℝ) : ℝ :=
  b*(served p lam b+p.eta2*duplicates p lam b)
def utility (p : Center) (lam : Fin 2 → ℝ) (v b : ℝ) : ℝ :=
  v*served p lam b-payment p lam b

lemma xi_pos (p : Center) : 0 < xi p := by
  unfold xi
  linarith [p.eta2_lt_one]

lemma xi_lt_half (p : Center) : xi p < 1/2 := by
  unfold xi
  linarith [p.eta1_pos,p.eta12]

lemma eta2_pos (p : Center) : 0 < p.eta2 := p.eta1_pos.trans p.eta12
lemma kappa_pos (p : Center) : 0 < kappa p := by
  unfold kappa
  linarith [xi_lt_half p]
lemma B_gt_one (p : Center) : 1 < B p := by
  unfold B
  linarith [xi_pos p]
lemma B_le_101 (p : Center) : B p ≤ 101/100 := by
  unfold B
  linarith [xi_lt_half p]
lemma width_pos (p : Center) : 0 < width p := sub_pos.mpr (B_gt_one p)
lemma width_eq (p : Center) : width p = xi p/50 := by simp [width,B]
lemma R_pos (p : Center) : 0 < R p := by
  unfold R
  linarith [xi_lt_half p]
lemma activeMass_pos (p : Center) : 0 < activeMass p := by
  unfold activeMass delta
  nlinarith [p.theta_pos,p.theta_small]
lemma activeMass_gt (p : Center) : 33/50 < activeMass p := by
  unfold activeMass delta
  nlinarith [p.theta_pos,p.theta_small]
lemma delta_pos (p : Center) : 0 < delta p := sq_pos_of_pos p.theta_pos
lemma e0_pos (p : Center) (r : Fin 2) : 0 < e0 p r := by
  have hd : 0 < delta p := delta_pos p
  fin_cases r <;> simp [e0,partialMass]
  · exact div_pos (by positivity) (by have := activeMass_pos p; positivity)
  · exact div_pos (by have := delta_pos p; positivity)
      (by have := activeMass_pos p; positivity)
lemma e0_lt_one (p : Center) (r : Fin 2) : e0 p r < 1 := by
  have ha := activeMass_pos p
  have hd : delta p < 1/100 := by
    unfold delta
    nlinarith [p.theta_small,p.theta_pos]
  fin_cases r
  · simp only [e0]
    apply (div_lt_one (by positivity : 0 < 9*activeMass p)).2
    unfold activeMass
    linarith
  · simp only [e0]
    apply (div_lt_one (by positivity : 0 < 4*activeMass p)).2
    unfold activeMass partialMass
    linarith
lemma regime_weights_positive (p : Center) (r : Fin 2) : 0 < regimeWeight p r := by
  fin_cases r <;> simp [regimeWeight] <;> linarith [p.theta_pos,p.theta_small]
lemma regime_weights_sum (p : Center) : ∑ r, regimeWeight p r = 1 := by
  simp [Fin.sum_univ_two,regimeWeight]
lemma masses_sum (p : Center) : lowMass p+partialMass p+activeMass p=1 := by
  unfold lowMass partialMass activeMass
  ring

lemma central_receipt_order (p : Center) :
    kappa p*B p< lambda0 p 0 ∧ lambda0 p 0< R p ∧ R p< lambda0 p 1 ∧
    kappa p*B p< R p ∧ R p<1 := by
  have hx := xi_pos p
  have hx1 := xi_lt_half p
  norm_num [kappa,B,R,lambda0,q0]
  constructor
  · nlinarith [sq_nonneg (xi p)]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · nlinarith [sq_nonneg (xi p)]
  · linarith

lemma central_active_partial_gap (p : Center) :
    p.theta*bulkValue p+(1-p.theta)*R p-B p=
      31*xi p/200-p.theta*R p := by
  unfold bulkValue R B
  field_simp [p.theta_pos.ne']
  ring

lemma canonical_two_cost_gap (p : Center) :
    2*lambda0 p 0-B p=1-48*xi p/25 := by
  norm_num [lambda0,q0,B]
  ring

lemma canonical_two_cost_gap_lower (p : Center) :
    1/25 < 2*lambda0 p 0-B p := by
  rw [canonical_two_cost_gap]
  linarith [xi_lt_half p]

lemma central_partial_two_gap (p : Center) :
    2*lambda0 p 0-(lambda0 p 0)^2/2-R p=
      1/2-xi p/40-361*(xi p)^2/800 := by
  norm_num [lambda0,q0,R]
  ring

lemma central_partial_two_gap_lower (p : Center) :
    1199/3200 < 2*lambda0 p 0-(lambda0 p 0)^2/2-R p := by
  rw [central_partial_two_gap]
  have hx := xi_pos p
  have hh := xi_lt_half p
  have hs : (xi p)^2 < 1/4 := by nlinarith
  nlinarith

lemma deficit_div_e0 (p : Center) (r : Fin 2) :
    deficit p r/e0 p r=2*q0 r-1 := by
  have ha := (activeMass_pos p).ne'
  have hd := (delta_pos p).ne'
  have hhd : partialMass p+delta p≠0 := by
    have := delta_pos p
    unfold partialMass
    positivity
  fin_cases r <;> norm_num [deficit,e0,q0] <;> field_simp [ha,hd,hhd]

lemma exposure_center_floor (p : Center) (r : Fin 2) :
    exposure p (lambda0 p) r 1 = q0 r := by
  unfold exposure lambda0
  field_simp [(xi_pos p).ne']
  ring

lemma central_exposure_range (p : Center) (r : Fin 2) {b : ℝ}
    (hb : b∈Icc (1:ℝ) (B p)) :
    89/100 < exposure p (lambda0 p) r b ∧
      exposure p (lambda0 p) r b < 98/100 := by
  have hb0 : 0 < b := by linarith [hb.1]
  have hx := xi_pos p
  have hh := xi_lt_half p
  have hbu : b ≤ 1+xi p/50 := hb.2
  have hq : 9/10 ≤ q0 r ∧ q0 r ≤ 19/20 := by
    fin_cases r <;> norm_num [q0]
  constructor
  · rw [exposure,lt_div_iff₀ hx]
    have hl : lambda0 p r/b < 1-89/100*xi p := by
      apply (div_lt_iff₀ hb0).2
      unfold lambda0
      nlinarith [mul_nonneg (sub_nonneg.mpr hb.1) (show 0≤1-89/100*xi p by linarith)]
    linarith
  · rw [exposure,div_lt_iff₀ hx]
    have hl : 1-98/100*xi p < lambda0 p r/b := by
      apply (lt_div_iff₀ hb0).2
      unfold lambda0
      nlinarith [mul_nonneg (sub_nonneg.mpr hbu) (show 0≤1-98/100*xi p by linarith)]
    linarith

lemma failure_factor (p : Center) (lam : Fin 2 → ℝ) (r : Fin 2) {b : ℝ}
    (hb : b≠0) :
    mixedProb p r b*(1-exposure p lam r b)^2=
      e0 p r/(width p^2*xi p^2)*((B p-b)*(lam r/b-kappa p))^2 := by
  unfold mixedProb exposure kappa
  field_simp [hb,(xi_pos p).ne',(width_pos p).ne']
  ring

lemma load_identity (p : Center) (lam : Fin 2 → ℝ) (b : ℝ) :
    load p lam b=1+∑ r,regimeWeight p r*mixedProb p r b*(2*exposure p lam r b-1) := by
  simp only [load,served,duplicates,Fin.sum_univ_two]
  ring

lemma menu_at_B (p : Center) (lam : Fin 2 → ℝ) :
    served p lam (B p)=1 ∧ duplicates p lam (B p)=0 ∧
      payment p lam (B p)=B p := by
  simp [served,duplicates,payment,mixedProb]

lemma utility_at_B (p : Center) (lam : Fin 2 → ℝ) (v : ℝ) :
    utility p lam v (B p)=v-B p := by
  simp [utility,(menu_at_B p lam).1,(menu_at_B p lam).2.2]

lemma mixed_prob_positive_before_B (p : Center) (r : Fin 2) {b : ℝ}
    (hb : b< B p) : 0 < mixedProb p r b := by
  unfold mixedProb
  exact mul_pos (e0_pos p r)
    (sq_pos_of_pos (div_pos (sub_pos.mpr hb) (width_pos p)))

lemma mixed_prob_le_e0 (p : Center) (r : Fin 2) {b : ℝ}
    (hb : b∈Icc (1:ℝ) (B p)) : mixedProb p r b ≤ e0 p r := by
  have hd := width_pos p
  have hy0 : 0 ≤ (B p-b)/width p := div_nonneg (sub_nonneg.mpr hb.2) hd.le
  have hy1 : (B p-b)/width p ≤ 1 := by
    apply (div_le_one hd).2
    unfold width
    linarith [hb.1]
  unfold mixedProb
  have hs : ((B p-b)/width p)^2 ≤ 1 := by nlinarith
  simpa using mul_le_mul_of_nonneg_left hs (e0_pos p r).le

structure Rectangle (p : Center) where
  lo : Fin 2 → ℝ
  hi : Fin 2 → ℝ
  center_interior : ∀ r, lo r< lambda0 p r ∧ lambda0 p r< hi r
  positive : ∀ r, 0< lo r

def Rectangle.box {p : Center} (rect : Rectangle p) : Set (Fin 2 → ℝ) :=
  Icc rect.lo rect.hi

lemma Rectangle.center_mem {p : Center} (rect : Rectangle p) : lambda0 p∈rect.box := by
  constructor <;> intro r
  · exact (rect.center_interior r).1.le
  · exact (rect.center_interior r).2.le

lemma Rectangle.isCompact_box {p : Center} (rect : Rectangle p) : IsCompact rect.box :=
  isCompact_Icc

structure ExplicitReceiptInequalities (p : Center) (rect : Rectangle p) : Prop where
  receipt : ∀ lam∈rect.box, kappa p*B p< lam 0 ∧ lam 0< R p ∧ R p< lam 1
  probabilities : ∀ lam∈rect.box, ∀ r, ∀ b∈Icc (1:ℝ) (B p),
    89/100< exposure p lam r b ∧ exposure p lam r b<98/100

structure UniformActiveAndPartialMenuInequalities
    (p : Center) (rect : Rectangle p) (w : ℝ) : Prop where
  w_pos : 0< w
  high_values : 2+w< bulkValue p-w
  active_partial : ∀ v, bulkValue p-w≤ v →
    (1-p.theta)*(v-R p)< v-B p
  active_canonical_one : ∀ lam∈rect.box, B p< lam 0/kappa p
  active_canonical_one_allq : ∀ lam∈rect.box, ∀ v,bulkValue p-w≤ v →
    ∀ q∈Icc (0:ℝ) 1,q*(v-lam 0/(1-xi p*q))< v-B p
  active_canonical_two : ∀ lam∈rect.box, ∀ v, bulkValue p-w≤ v →
    B p<2*lam 0-(lam 0)^2/v
  active_one_success : ∀ v, bulkValue p-w≤ v →
    (1/2+(∑ r,regimeWeight p r*e0 p r)/2)*v< v-B p
  partial_bids_ge_one : ∀ v∈Icc (2-w) (2+w),
    v-1<(1-p.theta)*(v-R p)
  partial_canonical_one : ∀ lam∈rect.box, ∀ v∈Icc (2-w) (2+w),
    ∀ q∈Icc (0:ℝ) 1,
      q*(v-lam 0/(1-xi p*q))<(1-p.theta)*(v-R p)
  partial_canonical_two : ∀ lam∈rect.box, ∀ v∈Icc (2-w) (2+w),
    R p+p.theta*(v-R p)<2*lam 0-(lam 0)^2/v
  partial_broadcast_charge : 0< p.eta2*R p*(1-p.theta)

lemma canonical_one_partial_bound {x lam q : ℝ}
    (hx : 0< x) (hxhalf : x<1/2) (hlam : 1-x≤ lam)
    (hq : q∈Icc (0:ℝ) 1) :
    q*(2-lam/(1-x*q))≤1 := by
  have hxq : x*q≤ x := by simpa using mul_le_mul_of_nonneg_left hq.2 hx.le
  have hh : 0<1-x*q := by linarith
  have hi : (q*(2-lam/(1-x*q))-1)*(1-x*q)=
      (q-1)*(1-2*x*q)+q*(1-x-lam) := by
    calc
      _ = q*(2*(1-x*q)-lam)-(1-x*q) := by
        rw [sub_mul, mul_assoc, sub_mul, div_mul_cancel₀ _ hh.ne', one_mul]
      _ = _ := by ring
  have h1 : (q-1)*(1-2*x*q)≤0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith [hq.2]) (by nlinarith [hq.2])
  have h2 : q*(1-x-lam)≤0 := mul_nonpos_of_nonneg_of_nonpos hq.1 (by linarith)
  nlinarith

lemma canonical_one_large_bound {x v lam q : ℝ}
    (hx : 0≤ x) (hx1 : x<1) (hlam : 0≤ lam) (hq : q∈Icc (0:ℝ) 1)
    (hv : lam/(1-x)^2≤ v) :
    q*(v-lam/(1-x*q))≤ v-lam/(1-x) := by
  have hk : 0<1-x := by linarith
  have hxq : x*q≤ x := by simpa using mul_le_mul_of_nonneg_left hq.2 hx
  have hH : 0<1-x*q := by linarith
  have hHk : 1-x≤1-x*q := by linarith
  have hquot : lam/((1-x)*(1-x*q))≤ lam/(1-x)^2 := by
    apply div_le_div_of_nonneg_left hlam (sq_pos_of_pos hk)
    nlinarith
  have hid : v-lam/(1-x)-q*(v-lam/(1-x*q))=
      (1-q)*(v-lam/((1-x)*(1-x*q))) := by
    field_simp [hk.ne',hH.ne']
    ring
  have hp : 0≤(1-q)*(v-lam/((1-x)*(1-x*q))) :=
    mul_nonneg (by linarith [hq.2]) (by linarith)
  linarith

end FCAppendix.Affine.Hybrid.Tail03
