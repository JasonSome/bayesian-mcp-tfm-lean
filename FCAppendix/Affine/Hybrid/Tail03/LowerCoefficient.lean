import FCAppendix.Affine.Hybrid.Tail03.LowerRelativeFloor

noncomputable section
namespace FCAppendix.Affine.Hybrid.Tail03
open Set Filter Topology
open scoped BigOperators

def lowerEpsilon (x : ℝ) : ℝ :=
  min (1/4) (min (lowerGap x/16)
    (x*min (lowerGap x) (min ((1-x)^2) (1/16))/8))

def lowerUpperThreshold (x : ℝ) : ℝ := 100/(x*lowerGap x)

lemma lowerEpsilon_pos {x : ℝ} (hx : 0 < x) (hx1 : x < 1/2) :
    0 < lowerEpsilon x := by
  have hg := lowerGap_pos hx hx1
  have hk : 0 < 1-x := by linarith
  unfold lowerEpsilon
  positivity

lemma lowerEpsilon_bounds {x e : ℝ} (he : e < lowerEpsilon x) :
    e < 1/4 ∧ e < lowerGap x/16 ∧
      e < x*min (lowerGap x) (min ((1-x)^2) (1/16))/8 := by
  simpa only [lowerEpsilon,lt_min_iff] using he

lemma lowerLambda_lt_small {x e : ℝ} (hx : 0 < x) (hx1 : x < 1/2)
    (he : 0 < e) (hes : e < lowerEpsilon x) :
    lowerLambda x e < lowerGap x/2 ∧
    lowerLambda x e < (1-x)^2/2 ∧ lowerLambda x e < 1/32 := by
  have hb := lowerEpsilon_bounds hes
  have hS := lowerScale_bound hx hx1 he.le (by linarith [hb.1])
  have hh : lowerLambda x e ≤ 4*e/x := by
    dsimp [lowerLambda]
    have hm := mul_le_mul_of_nonneg_left hS he.le
    calc
      e*lowerScale x e ≤ e*(4/x) := hm
      _ = 4*e/x := by ring
  have hmin : 4*e/x < min (lowerGap x) (min ((1-x)^2) (1/16))/2 := by
    apply (div_lt_iff₀ hx).2
    linarith [hb.2.2]
  have h0 := min_le_left (lowerGap x) (min ((1-x)^2) (1/16))
  have h1 := (min_le_right (lowerGap x) (min ((1-x)^2) (1/16))).trans
    (min_le_left ((1-x)^2) (1/16))
  have h2 := (min_le_right (lowerGap x) (min ((1-x)^2) (1/16))).trans
    (min_le_right ((1-x)^2) (1/16))
  exact ⟨by linarith,by linarith,by linarith⟩

lemma lowerCe_bound {x e : ℝ} (hx : 0 < x) (hx1 : x < 1/2)
    (he : 0 < e) (hes : e < lowerEpsilon x) :
    lowerCe x e < lowerC x+lowerGap x/8 := by
  have hc := (coefficient_one_cost_strict_scalar hx hx1).1
  have hh := (lowerEpsilon_bounds hes).2.1
  have hp := mul_pos he hc
  unfold lowerCe
  nlinarith

theorem lower_center_active_guards {x e : ℝ} (hx : 0 < x) (hx1 : x < 1/2)
    (he : 0 < e) (hes : e < lowerEpsilon x) :
    ActiveScalarGuards x e (lowerLambda x e*lowerFloorFactor x) 2 (lowerLambda x e) := by
  have hb := lowerEpsilon_bounds hes
  have hsmall := lowerLambda_lt_small hx hx1 he hes
  have hlam := lowerLambda_pos hx hx1 he (by linarith [hb.1])
  have hc := lowerCe_bound hx hx1 he hes
  have hg := lowerGap_pos hx hx1
  have hf := lower_floor_between hx hx1
  have hj1 : lowerJ x ≤ 1/(1-x) := min_le_left _ _
  have hj2 : lowerJ x ≤ 2 := min_le_right _ _
  have hcost : activeCost x e 2 (lowerLambda x e)=lowerLambda x e*lowerCe x e :=
    lower_center_cost hx hx1 he (by linarith [hb.1])
  have hcf : lowerCe x e < lowerFloorFactor x := by
    dsimp [lowerGap,lowerFloorFactor] at *
    linarith
  have hc2 : lowerCe x e < 2-lowerLambda x e/2 := by
    dsimp [lowerGap] at *
    linarith [hsmall.1]
  refine ⟨hx,hx1,he,by linarith [hb.1],by norm_num,hlam,?_,?_,?_,?_,?_⟩
  · apply (div_lt_iff₀ (sq_pos_of_pos (by linarith : 0 < 1-x))).2
    linarith [hsmall.2.1]
  · rw [hcost]
    exact mul_lt_mul_of_pos_left hcf hlam
  · rw [hcost]
    have hh := mul_lt_mul_of_pos_left (hcf.trans hf.2.2.1) hlam
    simpa only [div_eq_mul_inv, one_mul] using hh
  · rw [hcost]
    have hh := mul_lt_mul_of_pos_left hc2 hlam
    nlinarith
  · rw [hcost]
    have hh := mul_lt_mul_of_pos_left (hcf.trans hf.2.2.2) hlam
    nlinarith [hsmall.2.2]

lemma lowerGap_lt_two {x : ℝ} (hx : 0 < x) (hx1 : x < 1/2) : lowerGap x < 2 := by
  have hc := (coefficient_one_cost_strict_scalar hx hx1).1
  have hj : lowerJ x ≤ 2 := min_le_right _ _
  unfold lowerGap
  linarith

lemma lowerA_bound {x e : ℝ} (hx : 0 < x) (hx1 : x < 1/2)
    (he : 0 ≤ e) (heh : e ≤ 1/2) : 0 ≤ lowerA x e ∧ lowerA x e ≤ 3 := by
  have hk : 0 < 1-x := by linarith
  have hE : 0 ≤ 1-e := by linarith
  have hxk : x/(1-x)^2 ≤ 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hk)).2
    nlinarith [sq_nonneg (x-1/2)]
  have hnum : (1-e)*x/(1-x)^2 ≤ x/(1-x)^2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    nlinarith [mul_nonneg he hx.le]
  unfold lowerA
  exact ⟨by positivity,by linarith⟩

theorem lower_center_upper_guards {x e V : ℝ} (hx : 0 < x) (hx1 : x < 1/2)
    (he : 0 < e) (hes : e < lowerEpsilon x) (hV : lowerUpperThreshold x ≤ V) :
    UpperScalarGuards x e (lowerLambda x e*lowerFloorFactor x) V (lowerLambda x e) := by
  have hg := lowerGap_pos hx hx1
  have hg2 := lowerGap_lt_two hx hx1
  have hb := lowerEpsilon_bounds hes
  have hE : 0 < 1-e := by linarith [hb.1]
  have hl := lowerLambda_pos hx hx1 he (by linarith [hb.1])
  have hs := lowerLambda_lt_small hx hx1 he hes
  have hf := lower_floor_between hx hx1
  have hA := lowerA_bound hx hx1 he.le (by linarith [hb.1])
  have hS := lowerScale_bound hx hx1 he.le (by linarith [hb.1])
  have hV0 : 0 < V := (by unfold lowerUpperThreshold; positivity :
    0 < lowerUpperThreshold x).trans_le hV
  have hxg : 0 < x*lowerGap x := mul_pos hx hg
  have hVlarge : 100 ≤ V*x*lowerGap x := by
    have hh := (div_le_iff₀ hxg).mp hV
    nlinarith
  have hVgt : 100 < V := by
    have hp := mul_pos hx hg
    have hp1 : x*lowerGap x < 1 := by
      calc
        x*lowerGap x < (1/2)*lowerGap x := mul_lt_mul_of_pos_right hx1 hg
        _ < (1/2)*2 := mul_lt_mul_of_pos_left hg2 (by norm_num)
        _ = 1 := by norm_num
    nlinarith
  have hco : lowerLambda x e*(lowerA x e)^2/(4*e*V) < lowerGap x/4 := by
    have hSpos : 0 ≤ lowerScale x e := by
      unfold lowerScale
      have hH := (lowerH_bounds hx hx1).1
      positivity
    have hA2 : (lowerA x e)^2 ≤ 9 := by nlinarith
    have hmult := mul_le_mul_of_nonneg_left hA2 hSpos
    have hbound : lowerScale x e*(lowerA x e)^2 ≤ 36/x := by
      have hh := mul_le_mul_of_nonneg_right hS (by norm_num : (0:ℝ) ≤ 9)
      calc
        lowerScale x e * lowerA x e ^ 2 ≤ lowerScale x e * 9 := hmult
        _ ≤ (4/x)*9 := hh
        _ = 36/x := by ring
    have hcancel : lowerLambda x e*(lowerA x e)^2/(4*e*V)=
        lowerScale x e*(lowerA x e)^2/(4*V) := by
      unfold lowerLambda
      field_simp [he.ne',hV0.ne']
    rw [hcancel]
    apply (div_lt_iff₀ (by positivity : 0 < 4*V)).2
    have hh : 36/x < V*lowerGap x := by
      apply (div_lt_iff₀ hx).2
      nlinarith
    linarith
  have hbase1 : lowerFloorFactor x+lowerGap x/2 ≤ 1/(1-x) := by
    have hj : lowerJ x ≤ 1/(1-x) := min_le_left _ _
    dsimp [lowerFloorFactor,lowerGap]
    linarith
  have hbase2 : lowerFloorFactor x+lowerGap x/2 ≤ 2 := by
    have hj : lowerJ x ≤ 2 := min_le_right _ _
    dsimp [lowerFloorFactor,lowerGap]
    linarith
  refine ⟨hx,hx1,he,by linarith [hb.1],hV0,hl,?_,?_,?_,?_,?_⟩
  · apply (div_lt_iff₀ (sq_pos_of_pos (by linarith : 0 < 1-x))).2
    have hp := mul_lt_mul_of_pos_right hVgt (sq_pos_of_pos (by linarith : 0 < 1-x))
    linarith [hs.2.1]
  · have hh := mul_lt_mul_of_pos_left hco hl
    have hb1 := mul_le_mul_of_nonneg_left hbase1 hl.le
    have hident : lowerLambda x e*(lowerLambda x e*(lowerA x e)^2/(4*e*V))=
        (lowerLambda x e)^2*(lowerA x e)^2/(4*e*V) := by ring
    rw [hident] at hh
    have hp := mul_pos hl hg
    have hratio : lowerLambda x e / (1-x) = lowerLambda x e * (1/(1-x)) := by ring
    rw [hratio]
    nlinarith only [hh,hb1,hp]
  · simpa only [div_eq_mul_inv, one_mul] using mul_lt_mul_of_pos_left hf.2.2.1 hl
  · have hrat : lowerLambda x e/V < lowerGap x/2 := by
      apply (div_lt_iff₀ hV0).2
      have hp := mul_lt_mul_of_pos_right hVgt hg
      linarith [hs.1]
    have hm := mul_lt_mul_of_pos_left hrat hl
    have hb2 := mul_le_mul_of_nonneg_left hbase2 hl.le
    have hid : lowerLambda x e * (lowerLambda x e / V) =
        lowerLambda x e ^ 2 / V := by ring
    rw [hid] at hm
    nlinarith
  · have hh := mul_lt_mul_of_pos_left hf.2.2.2 hl
    nlinarith [hs.2.2]

def lowerMargins (x e floor V v lam : ℝ) : Fin 11 → ℝ := ![
  v,lam,v-lam/(1-x)^2,
  floor-activeCost x e v lam,
  lam/(1-x)-activeCost x e v lam,
  2*lam-lam^2/v-activeCost x e v lam,
  v/4-activeCost x e v lam,
  V-lam/(1-x)^2,
  lam/(1-x)-lam^2*(lowerA x e)^2/(4*e*V)-floor,
  2*lam-lam^2/V-floor,
  V/4-floor]

lemma lowerMargins_pos {x e floor V v lam : ℝ}
    (hA : ActiveScalarGuards x e floor v lam)
    (hH : UpperScalarGuards x e floor V lam) :
    ∀i,0 < lowerMargins x e floor V v lam i := by
  intro i
  fin_cases i <;> norm_num [lowerMargins] <;>
    linarith [hA.value_pos,hA.multiplier_pos,hA.singleton_threshold,hA.upper_gap,
      hA.canonical_one_gap,hA.canonical_two_gap,hA.private_one_gap,
      hH.singleton_threshold,hH.hybrid_two_gap,hH.canonical_two_gap,hH.private_one_gap]

lemma guards_of_lowerMargins {x e floor V v lam : ℝ}
    (hx : 0 < x) (hx1 : x < 1/2) (he : 0 < e) (heh : e < 1/2)
    (hV : 0 < V) (hm : ∀i,0 < lowerMargins x e floor V v lam i) :
    ActiveScalarGuards x e floor v lam ∧ UpperScalarGuards x e floor V lam := by
  have hh (i : Fin 11) := hm i
  have h0 := hh 0
  have h1 := hh 1
  have h2 := hh 2
  have h3 := hh 3
  have h4 := hh 4
  have h5 := hh 5
  have h6 := hh 6
  have h7 := hh 7
  have h8 := hh 8
  have h9 := hh 9
  have h10 := hh 10
  change 0 < v at h0
  change 0 < lam at h1
  change 0 < v-lam/(1-x)^2 at h2
  change 0 < floor-activeCost x e v lam at h3
  change 0 < lam/(1-x)-activeCost x e v lam at h4
  change 0 < 2*lam-lam^2/v-activeCost x e v lam at h5
  change 0 < v/4-activeCost x e v lam at h6
  change 0 < V-lam/(1-x)^2 at h7
  change 0 < lam/(1-x)-lam^2*(lowerA x e)^2/(4*e*V)-floor at h8
  change 0 < 2*lam-lam^2/V-floor at h9
  change 0 < V/4-floor at h10
  have hnonneg : 0 ≤ lam^2*(lowerA x e)^2/(4*e*V) := by positivity
  exact ⟨⟨hx,hx1,he,heh,h0,h1,by linarith,by linarith,by linarith,
    by linarith,by linarith⟩,
    ⟨hx,hx1,he,heh,hV,h1,by linarith,by linarith,by linarith,
    by linarith,by linarith⟩⟩

lemma finite_strict_neighborhood {ι : Type*} [Fintype ι]
    (f : ℝ×ℝ → ι → ℝ) (v0 l0 : ℝ)
    (hc : ∀i,ContinuousAt (fun y=> f y i) (v0,l0))
    (hp : ∀i,0 < f (v0,l0) i) :
    ∃d : ℝ,0 < d ∧ ∀v l,|v-v0| < d → |l-l0| < d → ∀i,0 < f (v,l) i := by
  have he : ∀ᶠ y in 𝓝 (v0,l0),∀i,0 < f y i := by
    rw [Filter.eventually_all]
    intro i
    exact (hc i).eventually (eventually_gt_nhds (hp i))
  obtain ⟨d,hd,hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨d,hd,?_⟩
  intro v l hv hl
  apply hball
  simpa only [Prod.dist_eq,Real.dist_eq,max_lt_iff] using And.intro hv hl

structure ExplicitCoefficientOneGuards (p : Center) (w : ℝ) where
  L : ℝ
  U : ℝ
  floor : ℝ
  width_pos : 0 < w
  width_small : w < 1
  mixed_pos : 0 < oneMixedMass p
  mixed_half : oneMixedMass p < 1/2
  floor_eq : floor=lowerLambda (xiOne p) (oneMixedMass p)*lowerFloorFactor (xiOne p)
  relative_floor : ((1-xiOne p)+lowerRelativeMargin (xiOne p))*floor ≤ lowerH (xiOne p)*L
  floor_twice : floor < 2*lowerLambda (xiOne p) (oneMixedMass p)
  L_pos : 0 < L
  box_strict : L < U
  upper_value : U < 2-w
  floor_order : U < floor
  receipt_lo : (1-xiOne p)*U < lowerH (xiOne p)*L
  receipt_hi : lowerH (xiOne p)*U < L
  inward_lo : L < Hybrid.inwardScale (xiOne p) (oneOwnerMass p) (3/5)*(2-w)
  inward_hi : Hybrid.inwardScale (xiOne p) (oneOwnerMass p) (3/5)*(2+w) < U

  active : ∀v∈Icc (2-w) (2+w),
    ∀lam∈Icc (lowerH (xiOne p)*L) (lowerH (xiOne p)*U),
      ActiveScalarGuards (xiOne p) (oneMixedMass p) floor v lam
  upper : ∀lam∈Icc (lowerH (xiOne p)*L) (lowerH (xiOne p)*U),
      UpperScalarGuards (xiOne p) (oneMixedMass p) floor (bulkValue p-w) lam

lemma lower_phi_identity {x e : ℝ} (hx : 0 < x) (hx1 : x < 1/2)
    (he : 0 < e) (he1 : e < 1) :
    2*Hybrid.phi x (1-e) (3/5)=lowerLambda x e := by
  have hH : lowerH x ≠ 0 := ne_of_gt (by linarith [(lowerH_bounds hx hx1).1])
  have hE : 0 < 1-e := sub_pos.mpr he1
  have hden : 2*e*(lowerH x)^2+(1-e)*x ≠ 0 := ne_of_gt (by positivity)
  rw [lowerLambda_eq_source he.ne' hH hden]
  change 2*((1-(3/5:ℝ))/(1+(1-e)*x/(2*(1-(1-e))*(lowerH x)^2))) = _
  rw [show 1-(1-e)=e by ring]
  ring

lemma lower_inward_identity {x e : ℝ} (hx : 0 < x) (hx1 : x < 1/2)
    (he : 0 < e) (he1 : e < 1) :
    2*Hybrid.inwardScale x (1-e) (3/5)=lowerLambda x e/lowerH x := by
  have hH : lowerH x ≠ 0 := ne_of_gt (by linarith [(lowerH_bounds hx hx1).1])
  have hE : 0 < 1-e := sub_pos.mpr he1
  have hden : 2*e*(lowerH x)^2+(1-e)*x ≠ 0 := ne_of_gt (by positivity)
  rw [lowerLambda_eq_source he.ne' hH hden]
  change 2*((1-(3/5:ℝ))*lowerH x/((lowerH x)^2+(1-e)*x/(2*(1-(1-e))))) = _
  rw [show 1-(1-e)=e by ring]
  field_simp [he.ne',hH]

lemma upperScalar_mono_threshold {x e floor V W lam : ℝ}
    (H : UpperScalarGuards x e floor V lam) (hVW : V ≤ W) :
    UpperScalarGuards x e floor W lam := by
  have hW : 0 < W := H.threshold_pos.trans_le hVW
  have he0 : 0< e := H.mixed_pos
  have hV0 : 0< V := H.threshold_pos
  have h1 : lam^2/W ≤ lam^2/V :=
    div_le_div_of_nonneg_left (sq_nonneg lam) H.threshold_pos hVW
  have h2 : lam^2*(lowerA x e)^2/(4*e*W) ≤
      lam^2*(lowerA x e)^2/(4*e*V) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    gcongr
  refine ⟨H.xi_pos,H.xi_half,H.mixed_pos,H.mixed_half,hW,H.multiplier_pos,
    H.singleton_threshold.trans_le hVW,?_,H.canonical_one_gap,?_,?_⟩
  · linarith only [H.hybrid_two_gap,h2]
  · linarith only [H.canonical_two_gap,h1]
  · linarith only [H.private_one_gap,hVW]

set_option maxHeartbeats 800000 in
theorem exists_lower_coefficient_guards (p : Center)
    (he : oneMixedMass p < lowerEpsilon (xiOne p))
    (hbulk : lowerUpperThreshold (xiOne p)+1 ≤ bulkValue p) :
    ∃w0 : ℝ,0 < w0 ∧ ∀w,0 < w → w ≤ w0 →
      Nonempty (ExplicitCoefficientOneGuards p w) := by
  let x := xiOne p
  let e := oneMixedMass p
  let lam := lowerLambda x e
  let f := lam*lowerFloorFactor x
  let b0 := lam/lowerH x
  let qphi := Hybrid.phi x (1-e) (3/5)
  let T := Hybrid.inwardScale x (1-e) (3/5)
  let V := bulkValue p-1
  have hx : 0 < x := xiOne_pos p
  have hx1 : x < 1/2 := xiOne_lt_half p
  have he0 : 0 < e := by
    have ht := p.theta_pos
    dsimp [e,oneMixedMass,partialMass,delta]
    positivity
  have heb := lowerEpsilon_bounds he
  have he1 : e < 1 := by linarith [heb.1]
  have hl : 0 < lam := lowerLambda_pos hx hx1 he0 he1
  have hH := lowerH_bounds hx hx1
  have hH0 : 0 < lowerH x := by linarith [hH.1]
  have hk : 0 < 1-x := by linarith
  have hg : 0 < lowerGap x := lowerGap_pos hx hx1
  have hf := lower_floor_between hx hx1
  have hc := coefficient_one_cost_strict_scalar hx hx1
  have hsmall := lowerLambda_lt_small hx hx1 he0 he
  have hb0 : 0 < b0 := div_pos hl hH0
  have hb02 : b0 < 2 := by
    apply (div_lt_iff₀ hH0).2
    linarith [hsmall.2.2,hH.1]
  have hb0f : b0 < f := by
    have hh := mul_lt_mul_of_pos_left (hc.2.1.trans hf.2.1) hl
    simpa [b0,f,div_eq_mul_inv] using hh
  have hT : 0 < T := Hybrid.inwardScale_pos hx (by linarith) (by linarith [he1])
    (by linarith) (by norm_num)
  have hphieq : 2*qphi=lam := lower_phi_identity hx hx1 he0 he1
  have hphi : 0 < qphi := by linarith
  have hTeq : 2*T=b0 := lower_inward_identity hx hx1 he0 he1
  have hV : 0 < V := by
    have hp : 0 < lowerUpperThreshold x := by unfold lowerUpperThreshold; positivity
    dsimp [V]
    linarith
  have hact : ActiveScalarGuards x e f 2 lam := lower_center_active_guards hx hx1 he0 he
  have hupp : UpperScalarGuards x e f V lam :=
    lower_center_upper_guards hx hx1 he0 he (by dsimp [V]; linarith)
  have hcont : ∀i,ContinuousAt (fun y : ℝ×ℝ=> lowerMargins x e f V y.1 y.2 i) (2,lam) := by
    intro i
    fin_cases i <;> norm_num [lowerMargins,activeCost,Hybrid.two] <;>
      fun_prop (disch := norm_num)
  obtain ⟨d,hd,hdall⟩ := finite_strict_neighborhood
    (fun y i=> lowerMargins x e f V y.1 y.2 i) 2 lam hcont (lowerMargins_pos hact hupp)
  have hrec1 : 0 < (lowerH x-(1-x))*b0 := by
    have hh : 0 < lowerH x-(1-x) := by unfold lowerH; linarith
    positivity
  have hrec2 : 0 < (1-lowerH x)*b0 :=
    mul_pos (sub_pos.mpr hH.2) hb0
  let baseRad := min b0 (min (f-b0) (min (2-b0)
    (min (((lowerH x-(1-x))*b0)/(lowerH x+(1-x)))
      (((1-lowerH x)*b0)/(1+lowerH x)))))

  let relativeGap := 1-(1-x)*lowerFloorFactor x
  have hrelativeGap : 0 < relativeGap := by
    have hh := (lt_div_iff₀ hk).mp hf.2.2.1
    dsimp only [relativeGap]
    nlinarith only [hh]
  let relativeRad := lam*relativeGap/lowerH x
  have hrelativeRad : 0 < relativeRad := by dsimp only [relativeRad];positivity
  let eps := min baseRad (min (d/lowerH x) relativeRad)/4
  have hbaseRad : 0 < baseRad := by
    dsimp [baseRad]
    exact lt_min hb0 (lt_min (sub_pos.mpr hb0f) (lt_min (sub_pos.mpr hb02)
      (lt_min (div_pos hrec1 (add_pos hH0 hk))
        (div_pos hrec2 (add_pos (by norm_num) hH0)))))
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hepsBase : 4*eps ≤ baseRad := by
    dsimp [eps]
    linarith [min_le_left baseRad (min (d/lowerH x) relativeRad)]
  have hepsD : 4*eps ≤ d/lowerH x := by
    dsimp [eps]
    have hh := (min_le_right baseRad (min (d/lowerH x) relativeRad)).trans
      (min_le_left (d/lowerH x) relativeRad)
    linarith only [hh]
  have hepsRelative : 4*eps ≤ relativeRad := by
    have hh := (min_le_right baseRad (min (d/lowerH x) relativeRad)).trans
      (min_le_right (d/lowerH x) relativeRad)
    dsimp only [eps]
    linarith only [hh]
  have hmin0 : 4*eps ≤ b0 :=
    hepsBase.trans (min_le_left _ _)
  have hmin1 : 4*eps ≤ f-b0 :=
    (hepsBase.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hmine : 4*eps ≤ min (2-b0)
      (min (((lowerH x-(1-x))*b0)/(lowerH x+(1-x)))
        (((1-lowerH x)*b0)/(1+lowerH x))) :=
    (hepsBase.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hmin2 := hmine.trans (min_le_left _ _)
  have hmin3 := (hmine.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hmin4 := (hmine.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hlamRadius : lowerH x*eps < d := by
    have hbound := (le_div_iff₀ hH0).mp hepsD
    have hp := mul_pos hH0 heps
    nlinarith
  have hcenter : lowerH x*b0=lam := by
    dsimp [b0]
    field_simp [hH0.ne']
  let L := b0-eps
  let U := b0+eps
  have hL : 0 < L := by dsimp [L]; linarith only [hmin0,heps]
  have hLU : L < U := by dsimp [L,U]; linarith only [heps]
  have hU2 : U < 2 := by dsimp [U]; linarith only [hmin2,heps]
  have hUf : U < f := by dsimp [U]; linarith only [hmin1,heps]
  have hlo : (1-x)*U < lowerH x*L := by
    have hh := (le_div_iff₀ (by positivity : 0 < lowerH x+(1-x))).mp hmin3
    dsimp [L,U]
    have hp := mul_pos heps (show 0 < lowerH x+(1-x) by positivity)
    nlinarith only [hh,hp]
  have hhi : lowerH x*U < L := by
    have hh := (le_div_iff₀ (by positivity : 0 < 1+lowerH x)).mp hmin4
    dsimp [L,U]
    have hp := mul_pos heps (show 0 < 1+lowerH x by positivity)
    nlinarith only [hh,hp]
  let w0 := min (1/2) (min (d/(4*(1+qphi)))
    (min ((2-U)/2) (eps/(4*(T+1)))))
  have hw0 : 0 < w0 := by
    have hroom : 0<2-U := sub_pos.mpr hU2
    dsimp [w0]
    positivity
  refine ⟨w0,hw0,?_⟩
  intro w hw hww
  have hwsmall : w ≤ 1/2 := hww.trans (min_le_left _ _)
  have hwd : w ≤ d/(4*(1+qphi)) :=
    (hww.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hwu : w ≤ (2-U)/2 :=
    ((hww.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hwt : w ≤ eps/(4*(T+1)) :=
    ((hww.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hwdd : w < d ∧ qphi*w < d := by
    have hbound := (le_div_iff₀ (by positivity : 0 < 4*(1+qphi))).mp hwd
    have hp := mul_pos hphi hw
    exact ⟨by nlinarith only [hbound,hphi,hw],by nlinarith only [hbound,hw,hphi]⟩
  have hTw : T*w < eps := by
    have hbound := (le_div_iff₀ (by positivity : 0 < 4*(T+1))).mp hwt
    have hp := mul_pos hT hw
    nlinarith only [hbound,hw,hT,heps]
  have hnear : ∀v∈Icc (2-w) (2+w),∀l∈Icc (lowerH x*L) (lowerH x*U),
      ActiveScalarGuards x e f v l ∧ UpperScalarGuards x e f V l := by
    intro v hv l hlv
    apply guards_of_lowerMargins hx hx1 he0 (by linarith [heb.1]) hV
    apply hdall
    · exact abs_lt.mpr ⟨by linarith only [hv.1,hwdd.1],by linarith only [hv.2,hwdd.1]⟩
    · rcases hlv with ⟨hlv,hvu⟩
      dsimp [L,U] at hlv hvu
      exact abs_lt.mpr ⟨by nlinarith only [hlv,hcenter,hlamRadius],by nlinarith only [hvu,hcenter,hlamRadius]⟩
  refine ⟨{
    L := L, U := U, floor := f
    width_pos := hw
    width_small := by linarith only [hwsmall]
    mixed_pos := he0
    mixed_half := by linarith [heb.1]
    floor_eq := rfl
    relative_floor := by
      change ((1-x)+lowerRelativeMargin x)*(lam*lowerFloorFactor x) ≤ lowerH x*(b0-eps)
      have hh : 4*eps*lowerH x ≤ lam*relativeGap :=
        (le_div_iff₀ hH0).mp hepsRelative
      have hid := lowerRelativeMargin_identity hx hx1
      have hm := congrArg (fun t : ℝ => lam*t) hid
      have hp := mul_pos hl hrelativeGap
      dsimp only [relativeGap] at hh hp
      nlinarith only [hh,hcenter,hm,hp]
    floor_twice := by
      change lam*lowerFloorFactor x < 2*lam
      nlinarith only [mul_lt_mul_of_pos_left hf.2.2.2 hl]
    L_pos := hL
    box_strict := hLU
    upper_value := by linarith only [hwu,hU2]
    floor_order := hUf
    receipt_lo := hlo
    receipt_hi := hhi
    inward_lo := by change L < T*(2-w); dsimp [L]; nlinarith only [hTw,hTeq]
    inward_hi := by change T*(2+w) < U; dsimp [U]; nlinarith only [hTw,hTeq]
    active := ?_
    upper := ?_ }⟩
  · intro v hv l hlv
    exact (hnear v hv l hlv).1
  · intro l hlv
    have hh := (hnear 2 (by constructor <;> linarith) l hlv).2
    apply upperScalar_mono_threshold hh
    dsimp [V]
    linarith

def lowerThetaBudget (eta1 eta2 : ℝ) : ℝ :=
  min (1/20) (min (8*lowerEpsilon ((1-eta1)/2)/125)
    (11*((1-eta2)/2)/(10*(lowerUpperThreshold ((1-eta1)/2)+2))))

lemma lowerThetaBudget_pos {eta1 eta2 : ℝ} (h1 : 0 < eta1)
    (h12 : eta1 < eta2) (h2 : eta2 < 1) : 0 < lowerThetaBudget eta1 eta2 := by
  have hx1 : 0 < (1-eta1)/2 := by linarith
  have hx1h : (1-eta1)/2 < 1/2 := by linarith
  have hx2 : 0 < (1-eta2)/2 := by linarith
  have he := lowerEpsilon_pos hx1 hx1h
  have hV : 0 < lowerUpperThreshold ((1-eta1)/2) := by
    unfold lowerUpperThreshold
    have hg := lowerGap_pos hx1 hx1h
    positivity
  unfold lowerThetaBudget
  positivity

theorem lower_guards_of_theta_budget (p : Center)
    (ht : p.theta < lowerThetaBudget p.eta1 p.eta2) :
    ∃w0 : ℝ,0 < w0 ∧ ∀w,0 < w → w ≤ w0 →
      Nonempty (ExplicitCoefficientOneGuards p w) := by
  have hparts : p.theta < 1/20 ∧
      p.theta < 8*lowerEpsilon (xiOne p)/125 ∧
      p.theta < 11*xi p/(10*(lowerUpperThreshold (xiOne p)+2)) := by
    simpa only [lowerThetaBudget,xiOne,xi,lt_min_iff] using ht
  have he : oneMixedMass p < lowerEpsilon (xiOne p) := by
    have hsq : p.theta^2 < p.theta := by nlinarith [p.theta_pos,hparts.1]
    norm_num [oneMixedMass,partialMass,delta]
    nlinarith [hparts.2.1]
  have hV0 : 0 < lowerUpperThreshold (xiOne p) := by
    unfold lowerUpperThreshold
    have hg := lowerGap_pos (xiOne_pos p) (xiOne_lt_half p)
    have hx := xiOne_pos p
    positivity
  have htheta := p.theta_pos
  have hbound := (lt_div_iff₀ (by positivity : 0 < 10*(lowerUpperThreshold (xiOne p)+2))).mp
    hparts.2.2
  have hv : lowerUpperThreshold (xiOne p)+1 ≤ bulkValue p := by
    unfold bulkValue
    apply (le_div_iff₀ (by positivity : 0 < 10*p.theta)).2
    nlinarith [p.theta_pos]
  exact exists_lower_coefficient_guards p he hv

theorem small_theta_lower_guards (eta1 eta2 : ℝ) (h1 : 0 < eta1)
    (h12 : eta1 < eta2) (h2 : eta2 < 1) :
    ∀ᶠ theta in 𝓝[>] (0:ℝ),∀p : Center,p.eta1=eta1 → p.eta2=eta2 → p.theta=theta →
      ∃w0 : ℝ,0 < w0 ∧ ∀w,0 < w → w ≤ w0 →
        Nonempty (ExplicitCoefficientOneGuards p w) := by
  have hb := lowerThetaBudget_pos h1 h12 h2
  have ht : ∀ᶠtheta in 𝓝[>] (0:ℝ),theta < lowerThetaBudget eta1 eta2 :=
    (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds
  filter_upwards [ht] with theta htheta
  intro p hp1 hp2 hpt
  apply lower_guards_of_theta_budget
  simpa only [hp1,hp2,hpt] using htheta

end FCAppendix.Affine.Hybrid.Tail03
