import FCAppendix.Affine.Hybrid.Tail03.Parameters
import FCAppendix.Affine.Hybrid.Tail03.Response
import FCAppendix.Affine.Tail04.SourceAnalyticContract

noncomputable section
namespace FCAppendix.Affine.Hybrid.Tail03.EarlySourceAdapter
open MeasureTheory Set Filter Topology

variable {eta1 eta2 : ℝ}

def values (p : Parameters eta1 eta2) : FCAppendix.Affine.Tail04.ValueParameters where
  theta:=p.center.theta
  d0:=p.d0
  w:=p.valueWidth
  zeta:=p.tailMass
  M:=p.tailFloor
  vA:=bulkValue p.center
  theta_pos:=p.center.theta_pos
  theta_small:=by linarith [p.theta_small]
  d0_pos:=p.d0_pos
  w_pos:=p.valueWidth_pos
  zeta_pos:=p.moments.zeta_pos
  zeta_lt_one:=p.moments.zeta_small.trans (by norm_num)
  low_partial_gap:=p.low_separation
  partial_active_gap:=p.bulk_separation
  active_tail_gap:=p.tail_separation

def finPair (lam : ℝ×ℝ) : Fin 2→ℝ := ![lam.1,lam.2]
def rectangle (p : Parameters eta1 eta2) : Set (ℝ×ℝ) :=
  Icc (p.rect.lo 0,p.rect.lo 1) (p.rect.hi 0,p.rect.hi 1)

lemma finPair_mem (p : Parameters eta1 eta2) {lam : ℝ×ℝ}
    (h : lam∈rectangle p) : finPair lam∈p.rect.box := by
  constructor <;> intro r <;> fin_cases r
  · exact h.1.1
  · exact h.1.2
  · exact h.2.1
  · exact h.2.2

lemma success_eq (p : Parameters eta1 eta2) (lam : ℝ×ℝ) :
    FCAppendix.Affine.Tail04.SourceAnalyticContract.success (values p) (xi p.center) lam=served p.center (finPair lam) := by
  funext b
  simp [FCAppendix.Affine.Tail04.SourceAnalyticContract.success,FCAppendix.Affine.Tail04.SourceAnalyticContract.flag,FCAppendix.Affine.Tail04.SourceAnalyticContract.flagBase,FCAppendix.Affine.Tail04.SourceAnalyticContract.endpoint,FCAppendix.Affine.Tail04.SourceAnalyticContract.exposure,values,
    FCAppendix.Affine.Tail04.activeMass,FCAppendix.Affine.Tail04.delta,FCAppendix.Affine.Tail04.partialMass,served,mixedProb,e0,delta,activeMass,partialMass,
    B,width,exposure,regimeWeight,finPair,Fin.sum_univ_two]

lemma duplicates_eq (p : Parameters eta1 eta2) (lam : ℝ×ℝ) :
    FCAppendix.Affine.Tail04.SourceAnalyticContract.duplicates (values p) (xi p.center) lam=duplicates p.center (finPair lam) := by
  funext b
  simp [FCAppendix.Affine.Tail04.SourceAnalyticContract.duplicates,FCAppendix.Affine.Tail04.SourceAnalyticContract.flag,FCAppendix.Affine.Tail04.SourceAnalyticContract.flagBase,FCAppendix.Affine.Tail04.SourceAnalyticContract.endpoint,FCAppendix.Affine.Tail04.SourceAnalyticContract.exposure,values,
    FCAppendix.Affine.Tail04.activeMass,FCAppendix.Affine.Tail04.delta,FCAppendix.Affine.Tail04.partialMass,duplicates,mixedProb,e0,delta,activeMass,partialMass,
    B,width,exposure,regimeWeight,finPair,Fin.sum_univ_two]

lemma payment_eq (p : Parameters eta1 eta2) (lam : ℝ×ℝ) :
    FCAppendix.Affine.Tail04.SourceAnalyticContract.payment (values p) (xi p.center) lam=payment p.center (finPair lam) := by
  have he : 1-2*xi p.center=p.center.eta2:=by unfold xi;ring
  funext b
  simp only [FCAppendix.Affine.Tail04.SourceAnalyticContract.payment,success_eq,duplicates_eq,payment,he]

lemma utility_eq (p : Parameters eta1 eta2) (lam : ℝ×ℝ) (v : ℝ) :
    FCAppendix.Affine.Tail04.SourceAnalyticContract.utility (values p) (xi p.center) lam v=utility p.center (finPair lam) v := by
  funext b
  simp only [FCAppendix.Affine.Tail04.SourceAnalyticContract.utility,success_eq,payment_eq,utility]

lemma leading_eq (p : Parameters eta1 eta2) (lam : ℝ×ℝ) :
    FCAppendix.Affine.Tail04.SourceAnalyticContract.leading (values p) (xi p.center) lam=leadingA p.center (finPair lam) := by
  simp only [FCAppendix.Affine.Tail04.SourceAnalyticContract.leading,FCAppendix.Affine.Tail04.SourceAnalyticContract.flagBase,FCAppendix.Affine.Tail04.SourceAnalyticContract.endpoint,FCAppendix.Affine.Tail04.SourceAnalyticContract.exposure,values,
    FCAppendix.Affine.Tail04.activeMass,FCAppendix.Affine.Tail04.delta,FCAppendix.Affine.Tail04.partialMass,leadingA,e0,delta,activeMass,partialMass,
    B,width,exposure,regimeWeight,finPair,Fin.sum_univ_two,
    Matrix.cons_val_zero,Matrix.cons_val_one,Bool.false_eq_true,ite_false,ite_true]
  ring

lemma center_eq (p : Parameters eta1 eta2) (reg : Bool) :
    FCAppendix.Affine.Tail04.SourceAnalyticContract.centerMoment (values p) reg=sourceCenterMoment p.center (if reg then 1 else 0) := by
  have ha:activeMass p.center≠0:=(activeMass_pos p.center).ne'
  cases reg <;> simp [FCAppendix.Affine.Tail04.SourceAnalyticContract.centerMoment,values,FCAppendix.Affine.Tail04.partialMass,sourceCenterMoment,e0,delta,partialMass]
  all_goals field_simp [ha]

lemma numerator_eq (p : Parameters eta1 eta2) (x : ℝ) (reg : Bool) :
    FCAppendix.Affine.Tail04.SourceAnalyticContract.numerator (values p) (xi p.center) x reg=
      (1-xi p.center/2)*x-(xi p.center/2)*sourceMomentDeficit p.center (if reg then 1 else 0) := by
  have ha:activeMass p.center≠0:=(activeMass_pos p.center).ne'
  cases reg <;> simp only [FCAppendix.Affine.Tail04.SourceAnalyticContract.numerator,values,FCAppendix.Affine.Tail04.partialMass,sourceMomentDeficit,deficit,
    partialMass,delta,Bool.false_eq_true,ite_false,ite_true,Matrix.cons_val_zero,Matrix.cons_val_one]
  all_goals field_simp [ha]

theorem moment_invariant (p : Parameters eta1 eta2) (M W : Bool→ℝ)
    (hM : ∀reg,|M reg-FCAppendix.Affine.Tail04.SourceAnalyticContract.centerMoment (values p) reg|≤
      FCAppendix.Affine.Tail04.SourceAnalyticContract.centerMoment (values p) reg*p.relativeMoments.rho)
    (hW : ∀reg,|W reg-FCAppendix.Affine.Tail04.SourceAnalyticContract.centerMoment (values p) reg|≤
      FCAppendix.Affine.Tail04.SourceAnalyticContract.centerMoment (values p) reg*p.relativeMoments.rho) :
    (FCAppendix.Affine.Tail04.SourceAnalyticContract.numerator (values p) (xi p.center) (M false) false/W false,
      FCAppendix.Affine.Tail04.SourceAnalyticContract.numerator (values p) (xi p.center) (M true) true/W true)∈rectangle p := by
  have hm : ∀r,|(![M false,M true] : Fin 2→ℝ) r-sourceCenterMoment p.center r|≤
      sourceCenterMoment p.center r*p.relativeMoments.rho := by
    intro r
    fin_cases r
    · change |M false-sourceCenterMoment p.center 0|≤ sourceCenterMoment p.center 0*p.relativeMoments.rho
      simpa only [center_eq,Bool.false_eq_true,ite_false] using hM false
    · change |M true-sourceCenterMoment p.center 1|≤ sourceCenterMoment p.center 1*p.relativeMoments.rho
      simpa only [center_eq,ite_true] using hM true
  have hw : ∀r,|(![W false,W true] : Fin 2→ℝ) r-sourceCenterMoment p.center r|≤
      sourceCenterMoment p.center r*p.relativeMoments.rho := by
    intro r
    fin_cases r
    · change |W false-sourceCenterMoment p.center 0|≤ sourceCenterMoment p.center 0*p.relativeMoments.rho
      simpa only [center_eq,Bool.false_eq_true,ite_false] using hW false
    · change |W true-sourceCenterMoment p.center 1|≤ sourceCenterMoment p.center 1*p.relativeMoments.rho
      simpa only [center_eq,ite_true] using hW true
  have hh:=p.relativeMoments.invariant ![M false,M true] ![W false,W true] hm hw
  have h0:=hh 0
  have h1:=hh 1
  rw [numerator_eq,numerator_eq]
  exact ⟨⟨h0.1.le,h1.1.le⟩,⟨h0.2.le,h1.2.le⟩⟩

lemma second_deriv_of_offzero (f f1 f2 : ℝ→ℝ)
    (hd : ∀b,b≠0→ HasDerivAt f (f1 b) b)
    (hd1 : ∀b,b≠0→ HasDerivAt f1 (f2 b) b) {b : ℝ} (hb : b≠0) :
    deriv (deriv f) b=f2 b := by
  have he : deriv f=ᶠ[nhds b] f1:=by
    filter_upwards [eventually_ne_nhds hb] with x hx
    exact (hd x hx).deriv
  exact he.deriv_eq.trans (hd1 b hb).deriv

lemma tail_start (p : Parameters eta1 eta2) (lam : Fin 2→ℝ) (hlam : lam∈p.rect.box) :
    payment1 p.center lam 1< p.tailFloor*served1 p.center lam 1 := by
  let b:=p.boundary.response lam p.tailFloor
  have hb:=p.boundary.response_mem lam hlam p.tailFloor p.tail_above_boundary.le
  have hfo:=p.boundary.response_first_order lam hlam p.tailFloor p.tail_above_boundary.le
  have hs:=p.analytic.derivative.served_pos lam hlam b ⟨hb.1.le,hb.2⟩
  have hs1:=p.analytic.derivative.served_pos lam hlam 1 ⟨le_rfl,B_gt_one p.center⟩
  have he : marginalCost p.center lam b=p.tailFloor:=by
    exact (div_eq_iff hs.ne').mpr (by nlinarith only [hfo])
  have hmono:=marginalCost_strictMonoOn p.center p.rect p.analytic lam hlam
    ⟨le_rfl,B_gt_one p.center⟩ ⟨hb.1.le,hb.2⟩ hb.1
  rw [he] at hmono
  exact (div_lt_iff₀ hs1).mp hmono

def analyticParameters (p : Parameters eta1 eta2) : FCAppendix.Affine.Tail04.SourceAnalyticContract.Parameters where
  P:=values p
  ξ:=xi p.center
  Up:=R p.center+xi p.center/2000
  u:=p.bulkBidWidth
  k:=p.boundary.capK
  width:=xi p.center/2000
  ρ:=p.relativeMoments.rho
  κ:=1/25
  Amin:=p.boundary.Amin
  Amax:=p.boundary.Amax
  ξ_pos:=xi_pos p.center
  ξ_half:=xi_lt_half p.center
  u_pos:=p.moments.u_pos
  partial_floor_lt:=by change R p.center< R p.center+xi p.center/2000;linarith [xi_pos p.center]
  partial_cap_lt_one:=by unfold R;linarith [xi_pos p.center]
  width_pos:=by exact div_pos (xi_pos p.center) (by norm_num)
  low_gap:=by
    have hh:=p.low_receipt_two.trans_le (min_le_right _ _)
    have hk:=kappa_pos p.center
    change p.d0< kappa p.center
    linarith only [hh,hk]
  width_small:=by linarith [xi_pos p.center]
  partial_value_gap:=by
    change R p.center+xi p.center/2000<2-p.valueWidth
    have hu : R p.center+xi p.center/2000<1:=by unfold R;linarith [xi_pos p.center]
    linarith [p.valueWidth_small]
  bulk_box_lt:=by
    have hh:=p.moments.u_lt_width
    change 1+p.bulkBidWidth< B p.center
    unfold width at hh
    linarith only [hh]
  partial_width_small:=by change R p.center+xi p.center/2000< R p.center+xi p.center/1000;linarith [xi_pos p.center]
  moment_small:=by
    have hh:=p.relativeMoments.coefficient_error
    rw [p.relative_u,p.relative_zeta] at hh
    change p.tailMass+p.bulkBidWidth*(1+2/width p.center)< xi p.center/1000
    linarith only [hh,p.moments.zeta_pos]
  κ_pos:=by norm_num
  Amin_pos:=p.boundary.Amin_pos
  cap_lower:=p.boundary.capK_lower
  cap_upper:=p.boundary.capK_upper
  low_entropy_gap:=by
    have hh:=p.rates.upper 0 le_rfl p.rates.tolerance_pos
    simp only [add_zero,sub_zero] at hh
    change 2*FCAppendix.Ample.binaryKL (99/200) (1-partialMass p.center/2)<
      FCAppendix.Affine.LowBody.jointRate (lowMass p.center) (activeMass p.center) (partialMass p.center) (99/200)
    linarith only [hh]
  Λ:=rectangle p
  compact_rectangle:=isCompact_Icc
  moment_tolerance:=by
    have hh:=p.relativeMoments.moment_error
    rw [p.relative_u,p.relative_zeta] at hh
    change p.tailMass+p.bulkBidWidth*(1+2/width p.center)< p.relativeMoments.rho
    linarith only [hh,p.moments.zeta_pos]
  moment_invariant:=moment_invariant p
  bulk_derivative:=by
    intro lam hlam v hv b hb
    rw [utility_eq]
    exact p.bulk_derivative (finPair lam) (finPair_mem p hlam) v hv b hb
  tail_derivatives:=by
    intro lam hlam
    have hmem:=finPair_mem p hlam
    rw [success_eq,payment_eq]
    refine ⟨?_,?_,?_⟩
    · intro b hb
      rw [(served_hasDerivAt p.center (finPair lam) (ne_of_gt (by linarith [hb.1]))).deriv]
      exact p.analytic.derivative.served_pos _ hmem b hb
    · intro b hb
      have hb0 : b≠0:=ne_of_gt (by linarith [hb.1])
      rw [(payment_hasDerivAt p.center (finPair lam) hb0).deriv,
        (served_hasDerivAt p.center (finPair lam) hb0).deriv,
        second_deriv_of_offzero _ _ _ (fun x hx=> payment_hasDerivAt p.center (finPair lam) hx)
          (fun x hx=> payment1_hasDerivAt p.center (finPair lam) hx) hb0,
        second_deriv_of_offzero _ _ _ (fun x hx=> served_hasDerivAt p.center (finPair lam) hx)
          (fun x hx=> served1_hasDerivAt p.center (finPair lam) hx) hb0]
      exact p.analytic.derivative.determinant_pos _ hmem b ⟨hb.1.le,hb.2.le⟩
    · rw [(payment_hasDerivAt p.center (finPair lam) (by norm_num)).deriv,
        (served_hasDerivAt p.center (finPair lam) (by norm_num)).deriv]
      exact tail_start p _ hmem
  leading_bounds:=by
    intro lam hlam
    rw [leading_eq]
    exact p.boundary.leading_bounds _ (finPair_mem p hlam)
  exposure_rectangle:=by
    intro lam hlam
    have hm:=finPair_mem p hlam
    have hr:=p.analytic.receipt.receipt _ hm
    have h0:=p.analytic.receipt.probabilities _ hm 0 1 ⟨le_rfl,(B_gt_one p.center).le⟩
    have h1:=p.analytic.receipt.probabilities _ hm 1 1 ⟨le_rfl,(B_gt_one p.center).le⟩
    simp only [finPair,Matrix.cons_val_zero,Matrix.cons_val_one,exposure,div_one] at hr h0 h1
    have hh0:lam.1<1-xi p.center/2:=by
      have hh:=(lt_div_iff₀ (xi_pos p.center)).mp h0.1
      nlinarith only [hh,xi_pos p.center]
    have hh1:lam.2<1-xi p.center/2:=by
      have hh:=(lt_div_iff₀ (xi_pos p.center)).mp h1.1
      nlinarith only [hh,xi_pos p.center]
    exact ⟨hr.1,hh0,hr.1.trans (hr.2.1.trans hr.2.2),hh1⟩
  theta_small:=p.theta_source_small
  value_width_small:=p.valueWidth_source_small
  bulk_center:=rfl

theorem exists_analyticParameters (eta1 eta2 : ℝ) (h1 : 0<eta1)
    (h12 : eta1<eta2) (h2 : eta2<1) :
    ∃S : FCAppendix.Affine.Tail04.SourceAnalyticContract.Parameters,1-2*S.ξ=eta2 := by
  obtain ⟨p⟩:=exists_parameters eta1 eta2 h1 h12 h2
  refine ⟨analyticParameters p,?_⟩
  change 1-2*xi p.center=eta2
  unfold xi
  nlinarith only [p.eta2_eq]

end FCAppendix.Affine.Hybrid.Tail03.EarlySourceAdapter
