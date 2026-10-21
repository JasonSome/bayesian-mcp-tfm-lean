import FCAppendix.Affine.Hybrid.Tail03.Curvature

noncomputable section
namespace FCAppendix.Affine.Hybrid.Tail03
open Set Filter Topology
open scoped BigOperators

theorem bulk_derivative_limit {x : ℝ} (hx : 0< x) :
    Tendsto (fun t : ℝ => -(11*x/10)*Raw.F1 x t (fun r => 1-x*q0 r) 1)
      (𝓝 (0:ℝ)) (𝓝 ((11/10:ℝ)*(40/67)*(1+(1-9*x/10)/5))) := by
  have hc : ContinuousAt
      (fun t : ℝ => -(11*x/10)*Raw.F1 x t (fun r => 1-x*q0 r) 1) 0 := by
    unfold Raw.F1 Raw.coeff Raw.mass Raw.fail Raw.fail1
    simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one]
    fun_prop (disch := norm_num)
  simpa [Raw.central_bulk_zero_formula hx.ne'] using hc.tendsto

lemma bulk_derivative_limit_upper {x : ℝ} (hx : 0< x) :
    (11/10:ℝ)*(40/67)*(1+(1-9*x/10)/5)<264/335 := by nlinarith

structure CentralAnalyticCertificate (p : Center) : Prop where
  F2_pos : ∀ b∈Icc (1:ℝ) (B p), 0< Raw.F2 (xi p) p.theta (lambda0 p) b
  determinant_pos : ∀ b∈Icc (1:ℝ) (B p),
    0< Raw.determinant (xi p) p.theta (lambda0 p) b
  payment_pos : ∀ b∈Icc (1:ℝ) (B p), 9/10< payment1 p (lambda0 p) b
  bulk : bulkValue p*served1 p (lambda0 p) 1<4/5
  bulk_large : 100< bulkValue p
  active_partial : 0<31*xi p/200-p.theta*R p
  active_two : B p<2*lambda0 p 0-(lambda0 p 0)^2/bulkValue p
  active_one :
    (1/2+(∑ r,regimeWeight p r*e0 p r)/2)*bulkValue p< bulkValue p-B p
  partial_cost : R p+p.theta*(2-R p)<1
  partial_two : R p+p.theta*(2-R p)<2*lambda0 p 0-(lambda0 p 0)^2/2

theorem small_theta_analytic (eta1 eta2 : ℝ)
    (h1 : 0< eta1) (h12 : eta1< eta2) (h2 : eta2<1) :
    ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ p : Center,
      p.eta1=eta1 → p.eta2=eta2 → p.theta=t →
        Nonempty (CentralAnalyticCertificate p) := by
  let x : ℝ := (1-eta2)/2
  let lam : Fin 2 → ℝ := fun r => 1-x*q0 r
  let cap : ℝ := Raw.cap x
  let floor : ℝ := 1-37*x/40
  have hx : 0< x := by dsimp [x]; linarith
  have hh : x<1/2 := by dsimp [x]; linarith
  have hcap : 1< cap := by dsimp [cap,Raw.cap]; linarith
  have hlam : (1-x)*Raw.cap x< lam 1 := by
    norm_num [lam,q0,Raw.cap]
    nlinarith [sq_nonneg x]
  have hF : ∀ᶠ t in 𝓝 (0:ℝ), ∀ b∈Icc (1:ℝ) cap, 0< Raw.F2 x t lam b := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro b hb
    have hb0 : b≠0 := ne_of_gt (by linarith [hb.1])
    have hc : ContinuousAt (fun z : ℝ×ℝ => Raw.F2 x z.1 lam z.2) (0,b) := by
      unfold Raw.F2 Raw.coeff Raw.mass Raw.fail Raw.fail1 Raw.fail2
      simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one]
      fun_prop (disch := first | exact hb0 | exact hx.ne' | positivity | norm_num)
    exact (tendsto_order.1 hc).1 0 (Raw.zero_F2_pos hx hh lam hlam hb)
  have hdet : ∀ᶠ t in 𝓝 (0:ℝ), ∀ b∈Icc (1:ℝ) cap,
      0< Raw.determinant x t lam b := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro b hb
    have hb0 : b≠0 := ne_of_gt (by linarith [hb.1])
    have hc : ContinuousAt (fun z : ℝ×ℝ => Raw.determinant x z.1 lam z.2) (0,b) := by
      unfold Raw.determinant Raw.H1 Raw.H2 Raw.F Raw.F1 Raw.F2 Raw.D Raw.D1 Raw.D2
        Raw.coeff Raw.mass Raw.fail Raw.fail1 Raw.fail2 Raw.dup Raw.dup1 Raw.dup2
      simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one]
      fun_prop (disch := first | exact hb0 | exact hx.ne' | positivity | norm_num)
    apply (tendsto_order.1 hc).1 0
    simpa [Raw.determinant] using Raw.zero_F2_pos hx hh lam hlam hb
  have hpay : ∀ᶠ t in 𝓝 (0:ℝ), ∀ b∈Icc (1:ℝ) cap,
      9/10<1+t*Raw.H1 x t lam b := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro b hb
    have hb0 : b≠0 := ne_of_gt (by linarith [hb.1])
    have hc : ContinuousAt (fun z : ℝ×ℝ => 1+z.1*Raw.H1 x z.1 lam z.2) (0,b) := by
      unfold Raw.H1 Raw.F Raw.F1 Raw.D Raw.D1 Raw.coeff Raw.mass Raw.fail Raw.fail1
        Raw.dup Raw.dup1
      simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one]
      fun_prop (disch := first | exact hb0 | exact hx.ne' | positivity | norm_num)
    exact (tendsto_order.1 hc).1 (9/10) (by norm_num)
  have hbulk : ∀ᶠ t in 𝓝 (0:ℝ), -(11*x/10)*Raw.F1 x t lam 1<4/5 := by
    have hc : ContinuousAt (fun t : ℝ => -(11*x/10)*Raw.F1 x t lam 1) 0 := by
      unfold Raw.F1 Raw.coeff Raw.mass Raw.fail Raw.fail1
      simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one]
      fun_prop (disch := norm_num)
    apply (tendsto_order.1 hc).2 (4/5)
    exact (Raw.central_bulk_zero_bound hx).trans (by norm_num)
  have hscalars : ∀ᶠ t in 𝓝 (0:ℝ),
      100*t<11*x/10 ∧
      0<31*x/200-t*floor ∧
      cap<2*lam 0-(lam 0)^2*(10*t/(11*x)) ∧
      0<(11*x/10)*(1/2-t*(∑ r,Raw.coeff t r)/2)-t*cap ∧
      floor+t*(2-floor)<1 ∧
      floor+t*(2-floor)<2*lam 0-(lam 0)^2/2 := by
    have hc1 : ContinuousAt (fun t : ℝ => 11*x/10-100*t) 0 := by fun_prop
    have hc2 : ContinuousAt (fun t : ℝ => 31*x/200-t*floor) 0 := by fun_prop
    have hc3 : ContinuousAt (fun t : ℝ => 2*lam 0-(lam 0)^2*(10*t/(11*x))-cap) 0 := by fun_prop
    have hc4 : ContinuousAt (fun t : ℝ =>
        (11*x/10)*(1/2-t*(∑ r,Raw.coeff t r)/2)-t*cap) 0 := by
      unfold Raw.coeff Raw.mass
      simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one]
      fun_prop (disch := norm_num)
    have hc5 : ContinuousAt (fun t : ℝ => 1-floor-t*(2-floor)) 0 := by fun_prop
    have hc6 : ContinuousAt (fun t : ℝ => 2*lam 0-(lam 0)^2/2-floor-t*(2-floor)) 0 := by fun_prop
    have hp1 : 0<11*x/10-100*0 := by simp only [mul_zero,sub_zero];positivity
    have hp2 : 0<31*x/200-0*floor := by simp only [zero_mul,sub_zero];positivity
    have hp3 : 0<2*lam 0-(lam 0)^2*(10*0/(11*x))-cap := by
      norm_num [lam,q0,cap,Raw.cap]
      linarith
    have hp4 : 0<(11*x/10)*(1/2-0*(∑ r,Raw.coeff 0 r)/2)-0*cap := by
      simp only [zero_mul,sub_zero,zero_div]
      positivity
    have hp5 : 0<1-floor-0*(2-floor) := by dsimp [floor]; linarith
    have hp6 : 0<2*lam 0-(lam 0)^2/2-floor-0*(2-floor) := by
      norm_num [lam,q0,floor]
      have hs : x^2<1/4 := by nlinarith
      nlinarith
    filter_upwards [(tendsto_order.1 hc1).1 0 hp1,(tendsto_order.1 hc2).1 0 hp2,
      (tendsto_order.1 hc3).1 0 hp3,(tendsto_order.1 hc4).1 0 hp4,
      (tendsto_order.1 hc5).1 0 hp5,(tendsto_order.1 hc6).1 0 hp6]
      with t ht1 ht2 ht3 ht4 ht5 ht6
    exact ⟨by linarith,ht2,by linarith,ht4,by linarith,by linarith⟩
  filter_upwards [hF.filter_mono nhdsWithin_le_nhds,hdet.filter_mono nhdsWithin_le_nhds,
    hpay.filter_mono nhdsWithin_le_nhds,hbulk.filter_mono nhdsWithin_le_nhds,
    hscalars.filter_mono nhdsWithin_le_nhds] with t htF htD htP htB htS
  intro p hp1 hp2 hpt
  have hxp : xi p=x := by simp [xi,x,hp2]
  have hlp : lambda0 p=lam := by ext r; simp [lambda0,hxp,lam]
  have hBp : B p=cap := by simp [B,cap,Raw.cap,hxp]
  have hRp : R p=floor := by simp [R,floor,hxp]
  have ht0 : 0< t := hpt ▸ p.theta_pos
  have hv : bulkValue p=11*x/(10*t) := by simp [bulkValue,hxp,hpt]
  have hvp : 0< bulkValue p := by rw [hv]; positivity
  have hsum : ∑ r,regimeWeight p r*e0 p r=t*(∑ r,Raw.coeff t r) := by
    simp_rw [normalized_coeff_identity,hpt]
    rw [Finset.mul_sum]
  refine ⟨{
    F2_pos := by simpa [hxp,hpt,hlp,hBp] using htF
    determinant_pos := by simpa [hxp,hpt,hlp,hBp] using htD
    payment_pos := by simpa [payment1,hxp,hpt,hlp,hBp] using htP
    bulk := ?_
    bulk_large := ?_
    active_partial := by simpa [hxp,hpt,hRp] using htS.2.1
    active_two := ?_
    active_one := ?_
    partial_cost := by simpa [hpt,hRp] using htS.2.2.2.2.1
    partial_two := by simpa [hpt,hRp,hlp] using htS.2.2.2.2.2 }⟩
  · rw [hv,served1,hxp,hpt,hlp]
    convert! htB using 1 ; field_simp [ht0.ne']
  · rw [hv]
    exact (lt_div_iff₀ (by positivity : 0<10*t)).2 (by nlinarith [htS.1])
  · rw [hBp,hlp,hv]
    convert! htS.2.2.1 using 1 ; field_simp [hx.ne',ht0.ne']
  · rw [hsum,hv,hBp]
    apply (mul_lt_mul_iff_left₀ (show 0< t from ht0)).mp
    have hvT : (11*x/(10*t))*t=11*x/10 := by
      field_simp [ht0.ne']
    calc
      (1/2+t*(∑ r,Raw.coeff t r)/2)*(11*x/(10*t))*t
          = (1/2+t*(∑ r,Raw.coeff t r)/2)*(11*x/10) := by rw [mul_assoc,hvT]
      _ < 11*x/10-t*cap := by nlinarith [htS.2.2.2.1]
      _ = (11*x/(10*t)-cap)*t := by rw [sub_mul,hvT]; ring

theorem closed_rectangle_in_nhds (p : Center) {s : Set (Fin 2 → ℝ)}
    (hs : s∈𝓝 (lambda0 p)) :
    ∃ rect : Rectangle p, rect.box⊆s := by
  obtain ⟨eps,heps,hsub⟩ := Metric.mem_nhds_iff.mp hs
  let r : ℝ := min (eps/2) (1/8)
  have hr : 0< r := lt_min (by positivity) (by norm_num)
  have hre : r< eps := (min_le_left _ _).trans_lt (by linarith)
  have hrsmall : r≤1/8 := min_le_right _ _
  let rect : Rectangle p := {
    lo := fun i => lambda0 p i-r
    hi := fun i => lambda0 p i+r
    center_interior := by intro i; constructor <;> linarith
    positive := by
      intro i
      have hq : q0 i≤19/20 := by fin_cases i <;> norm_num [q0]
      have hx := xi_pos p
      have hh := xi_lt_half p
      unfold lambda0
      nlinarith }
  refine ⟨rect,?_⟩
  intro lam hlam
  apply hsub
  rw [Metric.mem_ball,dist_pi_lt_iff heps]
  intro i
  rw [Real.dist_eq,abs_lt]
  have hlo := hlam.1 i
  have hhi := hlam.2 i
  dsimp [rect] at hlo hhi
  constructor <;> linarith

lemma normalized_curvature_uniform (p : Center) (rect : Rectangle p)
    (h : ∀ lam∈rect.box, ∀ b∈Icc (1:ℝ) (B p),
      0< Raw.F2 (xi p) p.theta lam b) :
    ∃ c>0, ∀ lam∈rect.box, ∀ b∈Icc (1:ℝ) (B p),
      c*p.theta≤-served2 p lam b := by
  have hc : ContinuousOn (fun z : (Fin 2 → ℝ)×ℝ =>
      Raw.F2 (xi p) p.theta z.1 z.2) (rect.box×ˢIcc (1:ℝ) (B p)) := by
    intro z hz
    have hb : z.2≠0 := ne_of_gt (by linarith [hz.2.1])
    have ha : Raw.mass p.theta≠0 := (activeMass_pos p).ne'
    unfold Raw.F2 Raw.coeff Raw.mass Raw.fail Raw.fail1 Raw.fail2
    simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one]
    fun_prop (disch := first | exact hb | exact ha | exact (xi_pos p).ne' | positivity)
  obtain ⟨c,hc0,hc⟩ := (rect.isCompact_box.prod isCompact_Icc).exists_forall_le'
    hc (fun z hz => h z.1 hz.1 z.2 hz.2)
  refine ⟨c,hc0,?_⟩
  intro lam hlam b hb
  have hh := mul_le_mul_of_nonneg_right (hc (lam,b) ⟨hlam,hb⟩) p.theta_pos.le
  simpa [served2,mul_comm] using hh

lemma served1_positive (p : Center) (lam : Fin 2 → ℝ)
    (hl : ∀ r,kappa p*B p< lam r) {b : ℝ} (hb : b∈Ico (1:ℝ) (B p)) :
    0< served1 p lam b := by
  have hb0 : 0< b := by linarith [hb.1]
  have he : ∀ r,0< Raw.coeff p.theta r := by
    intro r
    have hp := mul_pos (regime_weights_positive p r) (e0_pos p r)
    rw [normalized_coeff_identity] at hp
    by_contra hn
    have hh := mul_nonpos_of_nonneg_of_nonpos p.theta_pos.le (le_of_not_gt hn)
    exact not_lt_of_ge hh hp
  have hF : Raw.F1 (xi p) p.theta lam b<0 := by
    unfold Raw.F1
    apply Finset.sum_neg
    · intro r _
      have hs := Raw.failure_square_curvature (xi_pos p) (xi_lt_half p)
        (show (1-xi p)*Raw.cap (xi p)< lam r from hl r) ⟨hb.1,hb.2.le⟩
      have hf : 0< Raw.fail (xi p) (lam r) b := by
        unfold Raw.fail
        have hden : 0< lam r/b-(1-xi p) := by
          have hk := kappa_pos p
          apply sub_pos.mpr
          apply (lt_div_iff₀ hb0).2
          calc
            (1-xi p)*b ≤ (1-xi p)*B p := mul_le_mul_of_nonneg_left hb.2.le hk.le
            _ < lam r := hl r
        exact mul_pos (sub_pos.mpr hb.2) hden
      have hd : 0< Raw.gap (xi p)^2*xi p^2 := by
        unfold Raw.gap
        have := xi_pos p
        positivity
      exact mul_neg_of_pos_of_neg (div_pos (he r) hd)
        (mul_neg_of_pos_of_neg (by positivity) hs.2.1)
    · exact Finset.univ_nonempty
  unfold served1
  exact mul_pos_of_neg_of_neg (neg_neg_of_pos p.theta_pos) hF

end FCAppendix.Affine.Hybrid.Tail03
