import FCAppendix.Affine.Hybrid.Tail03.Analytic
import FCAppendix.Affine.Hybrid.ActiveMenuEndpointSigns

noncomputable section
namespace FCAppendix.Affine.Hybrid.Tail03
open Set Filter Topology

def xiOne (p : Center) : ℝ := (1-p.eta1)/2
def oneMixedMass (p : Center) : ℝ := 5*delta p/partialMass p
def oneOwnerMass (p : Center) : ℝ := 1-oneMixedMass p
def lowerH (x : ℝ) : ℝ := 1-x*(3/5)
def lowerC (x : ℝ) : ℝ := 1/lowerH x+x*(1-3/5)/(2*(lowerH x)^2)
def oneH (p : Center) : ℝ := lowerH (xiOne p)
def oneCostFactor (p : Center) : ℝ := lowerC (xiOne p)
def lowerScale (x e : ℝ) : ℝ :=
  (8/5)*(lowerH x)^2/(2*e*(lowerH x)^2+(1-e)*x)
def lowerLambda (x e : ℝ) : ℝ := e*lowerScale x e
def lowerCe (x e : ℝ) : ℝ := (1-e)*lowerC x+e*(8/5)
def lowerJ (x : ℝ) : ℝ := min (1/(1-x)) 2
def lowerGap (x : ℝ) : ℝ := lowerJ x-lowerC x
def lowerFloorFactor (x : ℝ) : ℝ := (lowerC x+lowerJ x)/2
def lowerA (x e : ℝ) : ℝ := 2*e+(1-e)*x/(1-x)^2

lemma xiOne_pos (p : Center) : 0 < xiOne p := by
  unfold xiOne
  linarith [p.eta12,p.eta2_lt_one]
lemma xiOne_lt_half (p : Center) : xiOne p < 1/2 := by
  unfold xiOne
  linarith [p.eta1_pos]
lemma lowerH_bounds {x : ℝ} (hx : 0 < x) (hx1 : x < 1/2) :
    7/10 < lowerH x ∧ lowerH x < 1 := by
  unfold lowerH
  constructor <;> linarith

lemma coefficient_one_total_load (p : Center) :
    partialMass p*(oneOwnerMass p+2*oneMixedMass p*(3/5))+activeMass p=99/100 := by
  norm_num [partialMass,oneOwnerMass,oneMixedMass,activeMass]
  ring

lemma lowerC_singleton_gap (x : ℝ) (hH : lowerH x ≠ 0) (hk : 1-x ≠ 0) :
    1/(1-x)-lowerC x=x*(5-x)/(25*(1-x)*(lowerH x)^2) := by
  unfold lowerC
  field_simp [hH,hk]
  unfold lowerH
  ring

lemma lowerC_two_gap (x : ℝ) (hH : lowerH x ≠ 0) :
    (2-lowerC x-9/(50*(lowerH x)^2))*(lowerH x)^2=
      (1/2-x)*(41/25-18*x/25) := by
  unfold lowerC
  field_simp [hH]
  unfold lowerH
  ring

theorem coefficient_one_cost_strict_scalar {x : ℝ} (hx : 0 < x) (hx1 : x < 1/2) :
    0 < lowerC x ∧ 1/lowerH x < lowerC x ∧
    lowerC x < 1/(1-x) ∧ 9/(50*(lowerH x)^2) ≤ 2-lowerC x := by
  have hH : 0 < lowerH x := by linarith [(lowerH_bounds hx hx1).1]
  have hk : 0 < 1-x := by linarith
  have hdiff := lowerC_singleton_gap x hH.ne' hk.ne'
  have htwo := lowerC_two_gap x hH.ne'
  have hx5 : 0 < 5-x := by linarith
  have hpos : 0 < x*(5-x)/(25*(1-x)*(lowerH x)^2) := by positivity
  have hterm : 0 < x*(1-3/5)/(2*(lowerH x)^2) := by positivity
  have hprod : 0 ≤ (1/2-x)*(41/25-18*x/25) := by
    apply mul_nonneg <;> linarith
  have hs : 0 < (lowerH x)^2 := sq_pos_of_pos hH
  refine ⟨by unfold lowerC; positivity,by unfold lowerC; linarith,by linarith,?_⟩
  nlinarith

theorem coefficient_one_cost_strict (p : Center) :
    oneCostFactor p < 1/(1-xiOne p) ∧ oneCostFactor p < 2 := by
  have h := coefficient_one_cost_strict_scalar (xiOne_pos p) (xiOne_lt_half p)
  have hp : 0 < 9/(50*(lowerH (xiOne p))^2) := by
    have hH := (lowerH_bounds (xiOne_pos p) (xiOne_lt_half p)).1
    positivity
  exact ⟨h.2.2.1,by dsimp [oneCostFactor]; linarith [h.2.2.2]⟩

lemma lowerGap_pos {x : ℝ} (hx : 0 < x) (hx1 : x < 1/2) : 0 < lowerGap x := by
  have h := coefficient_one_cost_strict_scalar hx hx1
  have hp : 0 < 9/(50*(lowerH x)^2) := by
    have hH := (lowerH_bounds hx hx1).1
    positivity
  unfold lowerGap lowerJ
  exact sub_pos.mpr (lt_min h.2.2.1 (by linarith [h.2.2.2]))

lemma lower_floor_between {x : ℝ} (hx : 0 < x) (hx1 : x < 1/2) :
    0 < lowerFloorFactor x ∧ lowerC x < lowerFloorFactor x ∧
    lowerFloorFactor x < 1/(1-x) ∧ lowerFloorFactor x < 2 := by
  have h := coefficient_one_cost_strict_scalar hx hx1
  have hg := lowerGap_pos hx hx1
  have hj1 : lowerJ x ≤ 1/(1-x) := min_le_left _ _
  have hj2 : lowerJ x ≤ 2 := min_le_right _ _
  unfold lowerGap at hg
  unfold lowerFloorFactor
  constructor
  · linarith [h.1]
  constructor
  · linarith
  constructor <;> linarith

lemma lowerLambda_eq_source {x e : ℝ} (he : e ≠ 0) (hH : lowerH x ≠ 0)
    (_hden : 2*e*(lowerH x)^2+(1-e)*x ≠ 0) :
    lowerLambda x e=2*(1-3/5)/(1+(1-e)*x/(2*e*(lowerH x)^2)) := by
  unfold lowerLambda lowerScale
  field_simp [he,hH]
  ring

lemma lowerLambda_pos {x e : ℝ} (hx : 0 < x) (hx1 : x < 1/2)
    (he : 0 < e) (he1 : e < 1) : 0 < lowerLambda x e := by
  have hH : 0 < lowerH x := by linarith [(lowerH_bounds hx hx1).1]
  have hE : 0 < 1-e := sub_pos.mpr he1
  unfold lowerLambda lowerScale
  positivity

lemma lowerScale_bound {x e : ℝ} (hx : 0 < x) (hx1 : x < 1/2)
    (he : 0 ≤ e) (hehalf : e ≤ 1/2) : lowerScale x e ≤ 4/x := by
  have hH := lowerH_bounds hx hx1
  have hE : 0 < 1-e := by linarith
  have hHsq : (lowerH x)^2 ≤ 1 := by nlinarith [sq_nonneg (lowerH x)]
  have hden : 0 < 2*e*(lowerH x)^2+(1-e)*x := by positivity
  unfold lowerScale
  apply (div_le_div_iff₀ hden hx).2
  have heH : 0 ≤ 2*e*(lowerH x)^2 := by positivity
  have hsqbound := mul_le_mul_of_nonneg_right hHsq hx.le
  have hEbound := mul_le_mul_of_nonneg_right
    (show (1/2:ℝ) ≤ 1-e by linarith) hx.le
  nlinarith

lemma lower_center_cost {x e : ℝ} (hx : 0 < x) (hx1 : x < 1/2)
    (he : 0 < e) (he1 : e < 1) :
    2-Hybrid.two x (1-e) 2 (lowerLambda x e) (3/5)=
      lowerLambda x e*lowerCe x e := by
  have hH : lowerH x ≠ 0 := ne_of_gt (by linarith [(lowerH_bounds hx hx1).1])
  have hE : 0 < 1-e := sub_pos.mpr he1
  have hd : 2*e*(lowerH x)^2+(1-e)*x ≠ 0 := ne_of_gt (by positivity)
  unfold Hybrid.two lowerLambda lowerScale lowerCe lowerC lowerH at *
  field_simp (disch := first | assumption | positivity | nlinarith)
  ring

lemma canonical_singleton_cost_ge {x v lam q : ℝ}
    (hx : 0 ≤ x) (hx1 : x < 1) (hlam : 0 ≤ lam)
    (hq : q ∈ Icc (0:ℝ) 1) (hv : lam/(1-x)^2 ≤ v) :
    lam/(1-x) ≤ v-q*(v-lam/(1-x*q)) := by
  have hk : 0 < 1-x := by linarith
  have hH : 0 < 1-x*q := by nlinarith [hq.2]
  have hHk : 1-x ≤ 1-x*q := by nlinarith [hq.2]
  have hquot : lam/((1-x)*(1-x*q)) ≤ lam/(1-x)^2 := by
    apply div_le_div_of_nonneg_left hlam (sq_pos_of_pos hk)
    nlinarith
  have hid : v-q*(v-lam/(1-x*q)) =
      lam/(1-x)+(1-q)*(v-lam/((1-x)*(1-x*q))) := by
    field_simp (disch := first | assumption | positivity | nlinarith)
    ring
  rw [hid]
  have hp : 0 ≤ (1-q)*(v-lam/((1-x)*(1-x*q))) := by
    apply mul_nonneg (by linarith [hq.2])
    linarith
  linarith

lemma hybrid_one_cost_ge_quarter {x e v lam q : ℝ}
    (hx : 0 ≤ x) (hx1 : x < 1) (he : 0 ≤ e) (hehalf : e ≤ 1/2)
    (hv : 0 ≤ v) (hlam : 0 ≤ lam) (hq : q ∈ Icc (0:ℝ) 1) :
    v/4 ≤ v-Hybrid.one x (1-e) v lam q := by
  have hH : 0 < 1-x*q := by nlinarith [hq.2]
  have hE : 0 ≤ 1-e := by linarith
  have hq0 : 0 ≤ q := hq.1
  have hc0 : 0 ≤ (1-e)/2+e*q := by positivity
  have hc1 : (1-e)/2+e*q ≤ 3/4 := by nlinarith [hq.2]
  have hp : 0 ≤ ((1-e)/2+e*q)*(lam/(1-x*q)) := by positivity
  have hvv := mul_le_mul_of_nonneg_right hc1 hv
  unfold Hybrid.one
  nlinarith

lemma hybrid_two_cost_identity {x e v lam q : ℝ}
    (hk : 1-x ≠ 0) (hH : 1-x*q ≠ 0) :
    v-Hybrid.two x (1-e) v lam q =
      lam*((1-e)/(1-x)+2*e)+e*v*(1-q)^2-
        lam*(2*e+(1-e)*x/((1-x)*(1-x*q)))*(1-q) := by
  unfold Hybrid.two
  field_simp [hk,hH]
  ring

theorem hybrid_two_cost_ge {x e v lam q : ℝ}
    (hx : 0 ≤ x) (hxhalf : x < 1/2) (he : 0 < e) (he1 : e ≤ 1)
    (hv : 0 < v) (hlam : 0 ≤ lam) (hq : q ∈ Icc (0:ℝ) 1) :
    lam/(1-x)-lam^2*(lowerA x e)^2/(4*e*v) ≤
      v-Hybrid.two x (1-e) v lam q := by
  have hk : 0 < 1-x := by linarith
  have hH : 0 < 1-x*q := by nlinarith [hq.2]
  have hHk : 1-x ≤ 1-x*q := by nlinarith [hq.2]
  have hE : 0 ≤ 1-e := sub_nonneg.mpr he1
  have hA : 0 ≤ lowerA x e := by unfold lowerA; positivity
  have hco : 2*e+(1-e)*x/((1-x)*(1-x*q)) ≤ lowerA x e := by
    unfold lowerA
    apply add_le_add_right
    apply div_le_div_of_nonneg_left (mul_nonneg hE hx) (sq_pos_of_pos hk)
    nlinarith
  have hbaseline : 1/(1-x) ≤ (1-e)/(1-x)+2*e := by
    have hh : 1/(1-x) ≤ 2 := (div_le_iff₀ hk).2 (by linarith)
    have hp := mul_nonneg he.le (sub_nonneg.mpr hh)
    have hid : (1-e)/(1-x)+2*e-1/(1-x)=e*(2-1/(1-x)) := by ring
    linarith
  have hloss := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hco hlam) (by linarith [hq.2] : 0 ≤ 1-q)
  have hsquare := sq_nonneg (2*e*v*(1-q)-lam*lowerA x e)
  have hcomplete : -lam^2*(lowerA x e)^2/(4*e*v) ≤
      e*v*(1-q)^2-lam*lowerA x e*(1-q) := by
    apply (div_le_iff₀ (by positivity : 0 < 4*e*v)).2
    nlinarith
  rw [hybrid_two_cost_identity hk.ne' hH.ne']
  have hbase := mul_le_mul_of_nonneg_left hbaseline hlam
  have htotal := add_le_add hbase hcomplete
  have hfinal := sub_le_sub_left hloss (lam*((1-e)/(1-x)+2*e)+e*v*(1-q)^2)
  calc
    lam/(1-x)-lam^2*(lowerA x e)^2/(4*e*v) =
        lam*(1/(1-x))+(-lam^2*(lowerA x e)^2/(4*e*v)) := by ring
    _ ≤ lam*((1-e)/(1-x)+2*e)+(e*v*(1-q)^2-lam*lowerA x e*(1-q)) := htotal
    _ = lam*((1-e)/(1-x)+2*e)+e*v*(1-q)^2-lam*lowerA x e*(1-q) := by ring
    _ ≤ _ := hfinal

lemma outsideTwo_cost {v lam : ℝ} (hv : v ≠ 0) :
    v-Hybrid.outsideTwo v lam=2*lam-lam^2/v := by
  unfold Hybrid.outsideTwo
  field_simp [hv]
  ring

def activeCost (x e v lam : ℝ) : ℝ :=
  v-Hybrid.two x (1-e) v lam (3/5)

structure ActiveScalarGuards (x e floor v lam : ℝ) : Prop where
  xi_pos : 0 < x
  xi_half : x < 1/2
  mixed_pos : 0 < e
  mixed_half : e < 1/2
  value_pos : 0 < v
  multiplier_pos : 0 < lam
  singleton_threshold : lam/(1-x)^2 < v
  upper_gap : activeCost x e v lam < floor
  canonical_one_gap : activeCost x e v lam < lam/(1-x)
  canonical_two_gap : activeCost x e v lam < 2*lam-lam^2/v
  private_one_gap : activeCost x e v lam < v/4

theorem active_all_menu_guards {x e floor v lam : ℝ}
    (H : ActiveScalarGuards x e floor v lam) :
    v-floor < Hybrid.two x (1-e) v lam (3/5) ∧
    Hybrid.outsideTwo v lam < Hybrid.two x (1-e) v lam (3/5) ∧
    (∀ q∈Icc (0:ℝ) 1,
      Hybrid.one x (1-e) v lam q < Hybrid.two x (1-e) v lam (3/5) ∧
      q*(v-lam/(1-x*q)) < Hybrid.two x (1-e) v lam (3/5)) := by
  have hout := outsideTwo_cost (lam:=lam) H.value_pos.ne'
  refine ⟨by have := H.upper_gap; unfold activeCost at this; linarith,
    by have := H.canonical_two_gap; unfold activeCost at this; linarith,?_⟩
  intro q hq
  have h1 := hybrid_one_cost_ge_quarter H.xi_pos.le (by linarith [H.xi_half])
    H.mixed_pos.le H.mixed_half.le H.value_pos.le H.multiplier_pos.le hq
  have h2 := canonical_singleton_cost_ge H.xi_pos.le (by linarith [H.xi_half])
    H.multiplier_pos.le hq H.singleton_threshold.le
  have hc1 := H.private_one_gap
  have hc2 := H.canonical_one_gap
  unfold activeCost at hc1 hc2
  exact ⟨by linarith,by linarith⟩

structure UpperScalarGuards (x e floor V lam : ℝ) : Prop where
  xi_pos : 0 < x
  xi_half : x < 1/2
  mixed_pos : 0 < e
  mixed_half : e < 1/2
  threshold_pos : 0 < V
  multiplier_pos : 0 < lam
  singleton_threshold : lam/(1-x)^2 < V
  hybrid_two_gap : floor < lam/(1-x)-lam^2*(lowerA x e)^2/(4*e*V)
  canonical_one_gap : floor < lam/(1-x)
  canonical_two_gap : floor < 2*lam-lam^2/V
  private_one_gap : floor < V/4

theorem upper_all_menu_guards {x e floor V lam : ℝ}
    (H : UpperScalarGuards x e floor V lam) :
    ∀v, V ≤ v →
      Hybrid.outsideTwo v lam < v-floor ∧
      ∀q∈Icc (0:ℝ) 1,
        Hybrid.two x (1-e) v lam q < v-floor ∧
        Hybrid.one x (1-e) v lam q < v-floor ∧
        q*(v-lam/(1-x*q)) < v-floor := by
  intro v hv
  have hv0 := H.threshold_pos.trans_le hv
  have he0 : 0< e := H.mixed_pos
  have hV0 : 0< V := H.threshold_pos
  have hp : lam^2/v ≤ lam^2/V :=
    div_le_div_of_nonneg_left (sq_nonneg lam) H.threshold_pos hv
  have hcor : lam^2*(lowerA x e)^2/(4*e*v) ≤
      lam^2*(lowerA x e)^2/(4*e*V) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    gcongr
  have hout := outsideTwo_cost (lam:=lam) hv0.ne'
  refine ⟨by linarith [H.canonical_two_gap],?_⟩
  intro q hq
  have h2 := hybrid_two_cost_ge H.xi_pos.le H.xi_half H.mixed_pos
    (by linarith [H.mixed_half]) hv0 H.multiplier_pos.le hq
  have h1 := hybrid_one_cost_ge_quarter H.xi_pos.le (by linarith [H.xi_half])
    H.mixed_pos.le H.mixed_half.le hv0.le H.multiplier_pos.le hq
  have hs := canonical_singleton_cost_ge H.xi_pos.le (by linarith [H.xi_half])
    H.multiplier_pos.le hq (H.singleton_threshold.le.trans hv)
  exact ⟨by linarith [H.hybrid_two_gap],by linarith [H.private_one_gap],
    by linarith [H.canonical_one_gap]⟩

end FCAppendix.Affine.Hybrid.Tail03
