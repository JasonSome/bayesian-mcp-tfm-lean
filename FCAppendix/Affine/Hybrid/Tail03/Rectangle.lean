import FCAppendix.Affine.Hybrid.Tail03.Selection

noncomputable section
namespace FCAppendix.Affine.Hybrid.Tail03
open Set Filter Topology
open scoped BigOperators

def leadingA (p : Center) (lam : Fin 2 → ℝ) : ℝ :=
  ∑ r,regimeWeight p r*e0 p r*(1-exposure p lam r (B p))^2/width p^2

lemma leadingA_continuous (p : Center) : Continuous (leadingA p) := by
  unfold leadingA exposure
  fun_prop

lemma leadingA_center_pos (p : Center) : 0< leadingA p (lambda0 p) := by
  unfold leadingA
  apply Finset.sum_pos
  · intro r _
    have hq := central_exposure_range p r ⟨(B_gt_one p).le,le_rfl⟩
    exact div_pos
      (mul_pos (mul_pos (regime_weights_positive p r) (e0_pos p r))
        (sq_pos_of_ne_zero (by linarith [hq.2])))
      (sq_pos_of_pos (width_pos p))
  · exact Finset.univ_nonempty

set_option maxHeartbeats 800000 in
lemma derivative_continuity (p : Center) (lam : Fin 2 → ℝ) (b : ℝ) (hb : b≠0) :
    ContinuousAt (fun z : (Fin 2 → ℝ)×ℝ => served1 p z.1 z.2) (lam,b) ∧
    ContinuousAt (fun z : (Fin 2 → ℝ)×ℝ => served2 p z.1 z.2) (lam,b) ∧
    ContinuousAt (fun z : (Fin 2 → ℝ)×ℝ => payment1 p z.1 z.2) (lam,b) ∧
    ContinuousAt (fun z : (Fin 2 → ℝ)×ℝ => payment2 p z.1 z.2) (lam,b) := by
  have hx : xi p≠0 := (xi_pos p).ne'
  have ha : Raw.mass p.theta≠0 := (activeMass_pos p).ne'
  have hg : Raw.gap (xi p)≠0 := by unfold Raw.gap;exact div_ne_zero hx (by norm_num)
  simp only [served1,served2,payment1,payment2,Raw.F1,Raw.F2,Raw.H1,Raw.H2,
    Raw.F,Raw.D,Raw.D1,Raw.D2,Raw.coeff,Raw.fail,Raw.fail1,Raw.fail2,
    Raw.dup,Raw.dup1,Raw.dup2,Raw.mass,Fin.sum_univ_two,
    Matrix.cons_val_zero,Matrix.cons_val_one] at *
  constructor
  · fun_prop (disch := first | assumption | positivity)
  constructor
  · fun_prop (disch := first | assumption | positivity)
  constructor <;> fun_prop (disch := first | assumption | positivity)

structure RectangleAnalyticCertificate (p : Center) (rect : Rectangle p) : Prop where
  central : CentralAnalyticCertificate p
  receipt : ExplicitReceiptInequalities p rect
  derivative : ExplicitDerivativeInequalities p rect
  active_two : ∀ lam∈rect.box,
    B p<2*lam 0-(lam 0)^2/bulkValue p
  partial_two : ∀ lam∈rect.box,
    R p+p.theta*(2-R p)<2*lam 0-(lam 0)^2/2
  leading : ∀ lam∈rect.box,
    9/10*leadingA p (lambda0 p)< leadingA p lam ∧
      leadingA p lam<11/10*leadingA p (lambda0 p)

theorem closed_rectangle_by_strict_continuity (p : Center)
    (h : CentralAnalyticCertificate p) :
    ∃ rect : Rectangle p, RectangleAnalyticCertificate p rect := by
  have hF : ∀ᶠ lam in 𝓝 (lambda0 p), ∀ b∈Icc (1:ℝ) (B p),
      0< Raw.F2 (xi p) p.theta lam b := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro b hb
    have hb0 : b≠0 := ne_of_gt (by linarith [hb.1])
    have hc := (Raw.rational_continuity (xi p) p.theta (lambda0 p) b
      (xi_pos p).ne' (activeMass_pos p).ne' hb0).2.1
    have hm : ContinuousAt (fun z : (Fin 2 → ℝ)×ℝ => ((p.theta,z.1),z.2)) (lambda0 p,b) := by fun_prop
    exact (tendsto_order.1 (hc.comp_of_eq hm rfl)).1 0 (h.F2_pos b hb)
  have hD : ∀ᶠ lam in 𝓝 (lambda0 p), ∀ b∈Icc (1:ℝ) (B p),
      0< payment2 p lam b*served1 p lam b-payment1 p lam b*served2 p lam b := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro b hb
    have hb0 : b≠0 := ne_of_gt (by linarith [hb.1])
    have hc := derivative_continuity p (lambda0 p) b hb0
    have hd := (hc.2.2.2.mul hc.1).sub (hc.2.2.1.mul hc.2.1)
    apply (tendsto_order.1 hd).1 0
    change 0 < payment2 p (lambda0 p) b*served1 p (lambda0 p) b-
      payment1 p (lambda0 p) b*served2 p (lambda0 p) b
    rw [determinant_identity]
    exact mul_pos p.theta_pos (h.determinant_pos b hb)
  have hP : ∀ᶠ lam in 𝓝 (lambda0 p), ∀ b∈Icc (1:ℝ) (B p),
      9/10< payment1 p lam b := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro b hb
    exact (tendsto_order.1 (derivative_continuity p (lambda0 p) b
      (ne_of_gt (by linarith [hb.1]))).2.2.1).1 (9/10) (h.payment_pos b hb)
  have hE (r : Fin 2) : ∀ᶠ lam in 𝓝 (lambda0 p), ∀ b∈Icc (1:ℝ) (B p),
      89/100< exposure p lam r b ∧ exposure p lam r b<98/100 := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro b hb
    have hb0 : b≠0 := ne_of_gt (by linarith [hb.1])
    have hc : ContinuousAt (fun z : (Fin 2 → ℝ)×ℝ => exposure p z.1 r z.2) (lambda0 p,b) := by
      unfold exposure
      fun_prop (disch := exact hb0)
    have he := central_exposure_range p r hb
    exact ((tendsto_order.1 hc).1 (89/100) he.1).and
      ((tendsto_order.1 hc).2 (98/100) he.2)
  have hB : ∀ᶠ lam in 𝓝 (lambda0 p), bulkValue p*served1 p lam 1<4/5 := by
    have hc := (derivative_continuity p (lambda0 p) 1 (by norm_num)).1
    have hm : ContinuousAt (fun lam : Fin 2 → ℝ => (lam,(1:ℝ))) (lambda0 p) := by fun_prop
    exact (tendsto_order.1 (continuousAt_const.mul (hc.comp_of_eq hm rfl))).2 (4/5) h.bulk
  have hR : ∀ᶠ lam in 𝓝 (lambda0 p),
      kappa p*B p< lam 0 ∧ lam 0< R p ∧ R p< lam 1 := by
    have ho := central_receipt_order p
    have h0 : ContinuousAt (fun lam : Fin 2 → ℝ => lam 0) (lambda0 p) :=
      (continuous_apply (0:Fin 2)).continuousAt
    have h1 : ContinuousAt (fun lam : Fin 2 → ℝ => lam 1) (lambda0 p) :=
      (continuous_apply (1:Fin 2)).continuousAt
    exact ((tendsto_order.1 h0).1 _ ho.1).and
      (((tendsto_order.1 h0).2 _ ho.2.1).and ((tendsto_order.1 h1).1 _ ho.2.2.1))
  have hT : ∀ᶠ lam in 𝓝 (lambda0 p),
      B p<2*lam 0-(lam 0)^2/bulkValue p ∧
      R p+p.theta*(2-R p)<2*lam 0-(lam 0)^2/2 := by
    have hc0 : ContinuousAt (fun lam : Fin 2 → ℝ => 2*lam 0-(lam 0)^2/bulkValue p) (lambda0 p) := by fun_prop
    have hc1 : ContinuousAt (fun lam : Fin 2 → ℝ => 2*lam 0-(lam 0)^2/2) (lambda0 p) := by fun_prop
    exact ((tendsto_order.1 hc0).1 _ h.active_two).and
      ((tendsto_order.1 hc1).1 _ h.partial_two)
  have hA : ∀ᶠ lam in 𝓝 (lambda0 p),
      9/10*leadingA p (lambda0 p)< leadingA p lam ∧
      leadingA p lam<11/10*leadingA p (lambda0 p) := by
    have hc : ContinuousAt (leadingA p) (lambda0 p) := (leadingA_continuous p).continuousAt
    have hp := leadingA_center_pos p
    exact ((tendsto_order.1 hc).1 _ (by linarith)).and
      ((tendsto_order.1 hc).2 _ (by linarith))
  have hall : {lam : Fin 2 → ℝ |
      (∀ b∈Icc (1:ℝ) (B p),0< Raw.F2 (xi p) p.theta lam b) ∧
      (∀ b∈Icc (1:ℝ) (B p),0< payment2 p lam b*served1 p lam b-payment1 p lam b*served2 p lam b) ∧
      (∀ b∈Icc (1:ℝ) (B p),9/10< payment1 p lam b) ∧
      (∀ r,∀ b∈Icc (1:ℝ) (B p),89/100< exposure p lam r b ∧ exposure p lam r b<98/100) ∧
      bulkValue p*served1 p lam 1<4/5 ∧
      (kappa p*B p< lam 0 ∧ lam 0< R p ∧ R p< lam 1) ∧
      (B p<2*lam 0-(lam 0)^2/bulkValue p ∧
        R p+p.theta*(2-R p)<2*lam 0-(lam 0)^2/2) ∧
      (9/10*leadingA p (lambda0 p)< leadingA p lam ∧
        leadingA p lam<11/10*leadingA p (lambda0 p))}∈𝓝 (lambda0 p) := by
    filter_upwards [hF,hD,hP,hE 0,hE 1,hB,hR,hT,hA]
      with lam hF hD hP hE0 hE1 hB hR hT hA
    refine ⟨hF,hD,hP,?_,hB,hR,hT,hA⟩
    intro r
    fin_cases r
    · exact hE0
    · exact hE1
  obtain ⟨rect,hr⟩ := closed_rectangle_in_nhds p hall
  have hrec : ExplicitReceiptInequalities p rect := {
    receipt := fun lam hlam => (hr hlam).2.2.2.2.2.1
    probabilities := fun lam hlam => (hr hlam).2.2.2.1 }
  have hcurv := normalized_curvature_uniform p rect (fun lam hlam => (hr hlam).1)
  refine ⟨rect,{
    central := h
    receipt := hrec
    derivative := {
      served_pos := ?_
      curvature := hcurv
      payment_pos := fun lam hlam => (hr hlam).2.2.1
      determinant_pos := fun lam hlam => (hr hlam).2.1
      bulk := fun lam hlam => (hr hlam).2.2.2.2.1 }
    active_two := fun lam hlam => (hr hlam).2.2.2.2.2.2.1.1
    partial_two := fun lam hlam => (hr hlam).2.2.2.2.2.2.1.2
    leading := fun lam hlam => (hr hlam).2.2.2.2.2.2.2 }⟩
  intro lam hlam b hb
  apply served1_positive p lam _ hb
  intro r
  fin_cases r
  · exact (hrec.receipt lam hlam).1
  · exact (hrec.receipt lam hlam).1.trans
      ((hrec.receipt lam hlam).2.1.trans (hrec.receipt lam hlam).2.2)

lemma active_success_coefficient_lt_one (p : Center) :
    1/2+(∑ r,regimeWeight p r*e0 p r)/2<1 := by
  have hs : ∑ r,regimeWeight p r*e0 p r<∑ r,regimeWeight p r := by
    apply Finset.sum_lt_sum
    · intro r _
      exact le_of_lt (by simpa only [mul_one] using
        (mul_lt_mul_of_pos_left (e0_lt_one p r) (regime_weights_positive p r)))
    · refine ⟨0,Finset.mem_univ _,?_⟩
      simpa using mul_lt_mul_of_pos_left (e0_lt_one p 0) (regime_weights_positive p 0)
  rw [regime_weights_sum] at hs
  linarith

theorem narrow_value_widths (p : Center) (rect : Rectangle p)
    (h : RectangleAnalyticCertificate p rect) :
    ∃ w0>0, w0<1 ∧ ∀ w,0< w → w≤ w0 →
      UniformActiveAndPartialMenuInequalities p rect w := by
  let va := bulkValue p
  let C := 1/2+(∑ r,regimeWeight p r*e0 p r)/2
  have hva : 100< va := h.central.bulk_large
  have hglobal : ∀ᶠ w in 𝓝 (0:ℝ),
      0<2-w ∧ 2+w< va-w ∧
      (1-p.theta)*(va-w-R p)< va-w-B p ∧
      C*(va-w)< va-w-B p ∧ R p+p.theta*(2+w-R p)<1 ∧
      1+w<(1-p.theta)*(2-w-R p) := by
    have hc1 : ContinuousAt (fun w : ℝ => 2-w) 0 := by fun_prop
    have hc2 : ContinuousAt (fun w : ℝ => va-w-(2+w)) 0 := by fun_prop
    have hc3 : ContinuousAt (fun w : ℝ => va-w-B p-(1-p.theta)*(va-w-R p)) 0 := by fun_prop
    have hc4 : ContinuousAt (fun w : ℝ => va-w-B p-C*(va-w)) 0 := by fun_prop
    have hc5 : ContinuousAt (fun w : ℝ => 1-R p-p.theta*(2+w-R p)) 0 := by fun_prop
    have hc6 : ContinuousAt (fun w : ℝ => (1-p.theta)*(2-w-R p)-(1+w)) 0 := by fun_prop
    have hp3 : 0< va-0-B p-(1-p.theta)*(va-0-R p) := by
      have hc := central_active_partial_gap p
      dsimp [va]
      nlinarith [h.central.active_partial]
    filter_upwards [(tendsto_order.1 hc1).1 0 (by norm_num),
      (tendsto_order.1 hc2).1 0 (by linarith),
      (tendsto_order.1 hc3).1 0 hp3,
      (tendsto_order.1 hc4).1 0 (by simpa [C,va] using sub_pos.mpr h.central.active_one),
      (tendsto_order.1 hc5).1 0 (by nlinarith [h.central.partial_cost]),
      (tendsto_order.1 hc6).1 0 (by nlinarith [h.central.partial_cost])]
      with w h1 h2 h3 h4 h5 h6
    exact ⟨h1,by linarith,by linarith,by linarith,by linarith,by linarith⟩
  have hlam : ∀ᶠ w in 𝓝 (0:ℝ), ∀ lam∈rect.box,
      B p<2*lam 0-(lam 0)^2/(va-w) ∧
      R p+p.theta*(2+w-R p)<2*lam 0-(lam 0)^2/(2-w) := by
    apply rect.isCompact_box.eventually_forall_of_forall_eventually
    intro lam hmem
    have hc1 : ContinuousAt (fun z : ℝ×(Fin 2 → ℝ) =>
        2*z.2 0-(z.2 0)^2/(va-z.1)) (0,lam) := by
      fun_prop (disch := dsimp [va]; linarith [h.central.bulk_large])
    have hc2 : ContinuousAt (fun z : ℝ×(Fin 2 → ℝ) =>
        2*z.2 0-(z.2 0)^2/(2-z.1)-R p-p.theta*(2+z.1-R p)) (0,lam) := by
      fun_prop (disch := norm_num)
    have h1 := (tendsto_order.1 hc1).1 (B p) (by simpa [va] using h.active_two lam hmem)
    have h2 := (tendsto_order.1 hc2).1 0 (by nlinarith [h.partial_two lam hmem])
    filter_upwards [h1,h2] with z hz1 hz2
    exact ⟨hz1,by linarith⟩
  obtain ⟨eps,heps,hball⟩ := Metric.mem_nhds_iff.mp (hglobal.and hlam)
  let w0 : ℝ := min (eps/2) (1/2)
  have hw0 : 0< w0 := lt_min (by positivity) (by norm_num)
  refine ⟨w0,hw0,(min_le_right _ _).trans_lt (by norm_num),?_⟩
  intro w hw hww
  have hwE : w< eps := hww.trans_lt ((min_le_left _ _).trans_lt (by linarith))
  have hsmall := hball (show w∈Metric.ball (0:ℝ) eps from by
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hw] using hwE)
  rcases hsmall.1 with ⟨hpositive,hhigh,hactivepartial,hactiveone,hpartialcost,hpartialone⟩
  have hV : 0< va-w := by linarith
  refine {
    w_pos := hw
    high_values := hhigh
    active_partial := ?_
    active_canonical_one := ?_
    active_canonical_one_allq := ?_
    active_canonical_two := ?_
    active_one_success := ?_
    partial_bids_ge_one := ?_
    partial_canonical_one := ?_
    partial_canonical_two := ?_
    partial_broadcast_charge := by
      exact mul_pos (mul_pos (eta2_pos p) (R_pos p)) (by linarith [p.theta_small]) }
  · intro v hv
    have ht := p.theta_pos
    have hd := mul_nonneg ht.le (sub_nonneg.mpr hv)
    dsimp [va] at hactivepartial hV
    nlinarith
  · intro lam hmem
    exact (lt_div_iff₀ (kappa_pos p)).2 (by nlinarith [(h.receipt.receipt lam hmem).1])
  · intro lam hmem v hv q hq
    have hk : (1/2:ℝ)< kappa p := by unfold kappa; linarith [xi_lt_half p]
    have hksq : (1/4:ℝ)<(kappa p)^2 := by nlinarith [sq_nonneg (kappa p-1/2)]
    have hr : R p<1 := by unfold R; linarith [xi_pos p]
    have hlam0 : 0< lam 0 := (rect.positive 0).trans_le (hmem.1 0)
    have hlam1 : lam 0<1 := (h.receipt.receipt lam hmem).2.1.trans hr
    have hthreshold : lam 0/(kappa p)^2<4 :=
      (div_lt_iff₀ (sq_pos_of_pos (kappa_pos p))).2 (by linarith)
    have hw1 : w<1 := hww.trans_lt ((min_le_right _ _).trans_lt (by norm_num))
    have hvlarge : lam 0/(1-xi p)^2≤ v := by
      change lam 0/(kappa p)^2≤ v
      dsimp [va] at hva
      linarith
    have hb := canonical_one_large_bound (xi_pos p).le (by linarith [xi_lt_half p])
      hlam0.le hq hvlarge
    have hgap : B p< lam 0/kappa p :=
      (lt_div_iff₀ (kappa_pos p)).2 (by nlinarith [(h.receipt.receipt lam hmem).1])
    unfold kappa at hgap
    linarith
  · intro lam hmem v hv
    have hv0 : 0< v := hV.trans_le hv
    have hi : (lam 0)^2/v≤(lam 0)^2/(va-w) :=
      div_le_div_of_nonneg_left (sq_nonneg _) hV hv
    exact (hsmall.2 lam hmem).1.trans_le (by linarith)
  · intro v hv
    have hc := active_success_coefficient_lt_one p
    have hd := mul_nonneg (show 0≤1-C by dsimp [C]; linarith) (sub_nonneg.mpr hv)
    change C*v < v-B p
    dsimp [va] at hactiveone
    nlinarith only [hactiveone,hd]
  · intro v hv
    have hi : R p+p.theta*(v-R p)<1 := by
      nlinarith [mul_nonneg p.theta_pos.le (sub_nonneg.mpr hv.2)]
    nlinarith
  · intro lam hmem v hv q hq
    have hlam : 1-xi p≤ lam 0 := by
      have hk := kappa_pos p
      have hmul := mul_le_mul_of_nonneg_left (B_gt_one p).le hk.le
      have hr := (h.receipt.receipt lam hmem).1
      unfold kappa at *
      nlinarith
    have htwo := canonical_one_partial_bound (xi_pos p) (xi_lt_half p) hlam hq
    have hshift : q*(v-2)≤ w := by
      have h1 := mul_nonneg hq.1 (show 0≤ w-(v-2) by linarith [hv.2])
      have h2 := mul_nonneg hw.le (sub_nonneg.mpr hq.2)
      nlinarith
    have hupper : q*(v-lam 0/(1-xi p*q))≤1+w := by nlinarith
    have hsucc : 0≤1-p.theta := by linarith [p.theta_small]
    have hlower := mul_le_mul_of_nonneg_left hv.1 hsucc
    nlinarith
  · intro lam hmem v hv
    have hv0 : 0< v := hpositive.trans_le hv.1
    have hi : (lam 0)^2/v≤(lam 0)^2/(2-w) :=
      div_le_div_of_nonneg_left (sq_nonneg _) hpositive hv.1
    have hu := mul_nonneg p.theta_pos.le (sub_nonneg.mpr hv.2)
    nlinarith [(hsmall.2 lam hmem).2]

structure LeadingWindow (p : Center) (rect : Rectangle p) where
  Amin : ℝ
  Amax : ℝ
  capK : ℝ
  Amin_pos : 0< Amin
  Amax_lt : Amax<2*Amin
  leading_bounds : ∀ lam∈rect.box,Amin≤ leadingA p lam ∧ leadingA p lam≤ Amax
  capK_lower : 1/(4*Amin)< capK
  capK_upper : capK<1/(2*Amax)

theorem shrink_rectangle_choose_cap_constant (p : Center) (rect : Rectangle p)
    (h : RectangleAnalyticCertificate p rect) : Nonempty (LeadingWindow p rect) := by
  let A0 := leadingA p (lambda0 p)
  let a := 9/10*A0
  let b := 11/10*A0
  have hA : 0< A0 := leadingA_center_pos p
  have ha : 0< a := by dsimp [a]; positivity
  have hb : 0< b := by dsimp [b]; positivity
  have hab : b<2*a := by dsimp [a,b]; nlinarith
  have hi : 1/(4*a)<1/(2*b) := by
    apply one_div_lt_one_div_of_lt (by positivity : 0<2*b)
    nlinarith
  exact ⟨{
    Amin := a
    Amax := b
    capK := (1/(4*a)+1/(2*b))/2
    Amin_pos := ha
    Amax_lt := hab
    leading_bounds := fun lam hlam => ⟨(h.leading lam hlam).1.le,(h.leading lam hlam).2.le⟩
    capK_lower := by linarith
    capK_upper := by linarith }⟩

end FCAppendix.Affine.Hybrid.Tail03
