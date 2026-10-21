import FCAppendix.Affine.Hybrid.Native02.PrimitiveInput
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Deriv

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open MeasureTheory Set Filter Topology

def twoQDerivative (xi z v lam q : ℝ) : ℝ :=
  -z*lam*xi/(1-xi*q)^2+(1-z)*(v*(2-2*q)-2*lam)

theorem hasDerivAt_twoQ {xi z v lam q : ℝ} (hd : 1-xi*q≠0) :
    HasDerivAt (two xi z v lam) (twoQDerivative xi z v lam q) q := by
  have hden : HasDerivAt (fun r : ℝ => 1-xi*r) (-xi) q := by
    convert! (hasDerivAt_const q (1:ℝ)).sub ((hasDerivAt_id q).const_mul xi) using 1
    ring
  have hh := (((hasDerivAt_const q v).sub
    ((hasDerivAt_const q lam).div hden hd)).const_mul z).add
      ((((((hasDerivAt_id q).const_mul 2).sub ((hasDerivAt_id q).pow 2)).const_mul v).sub
        ((hasDerivAt_id q).const_mul (2*lam))).const_mul (1-z))
  apply hh.congr_deriv
  unfold twoQDerivative
  simp only [id_eq]
  ring

theorem twoQDerivative_factor {xi z v lam q : ℝ}
    (hv : v≠0) (he : 1-z≠0) (hd : 1-xi*q≠0)
    (hD : 1+z*xi/(2*(1-z)*(1-xi*q)^2)≠0) :
    twoQDerivative xi z v lam q =
      (2*(1-z)*v*(1+z*xi/(2*(1-z)*(1-xi*q)^2)))*
        (phi xi z q-lam/v) := by
  let D := 1+z*xi/(2*(1-z)*(1-xi*q)^2)
  have hcancel : D * phi xi z q = 1-q := mul_div_cancel₀ _ hD
  change -z*lam*xi/(1-xi*q)^2+(1-z)*(v*(2-2*q)-2*lam) =
    (2*(1-z)*v*D)*(phi xi z q-lam/v)
  conv_rhs => rw [mul_sub]
  rw [mul_assoc (2*(1-z)*v) D (phi xi z q), hcancel]
  dsimp only [D]
  field_simp [hv,he,hd]
  ring

theorem twoQDerivative_factor_pos {xi z v q : ℝ}
    (hxi : 0< xi) (hxi1 : xi<1) (hz : 0≤ z) (hz1 : z<1)
    (hv : 0< v) (hq : q∈ Icc (0:ℝ) 1) :
    0<2*(1-z)*v*(1+z*xi/(2*(1-z)*(1-xi*q)^2)) := by
  have hd : 0<1-xi*q := by nlinarith [hq.2]
  have he : 0<1-z := sub_pos.mpr hz1
  have hfrac : 0≤ z*xi/(2*(1-z)*(1-xi*q)^2) := by positivity
  positivity

theorem continuousOn_phi_unit {xi z : ℝ}
    (hxi : 0< xi) (hxi1 : xi<1) (hz : 0≤ z) (hz1 : z<1) :
    ContinuousOn (phi xi z) (Icc (0:ℝ) 1) := by
  have he : 0<1-z := sub_pos.mpr hz1
  have hd (q : ℝ) (hq : q∈ Icc (0:ℝ) 1) : 0<1-xi*q := by nlinarith [hq.2]
  have hbase : ContinuousOn (fun q : ℝ => 2*(1-z)*(1-xi*q)^2) (Icc (0:ℝ) 1) :=
    continuousOn_const.mul ((continuousOn_const.sub
      (continuousOn_const.mul continuousOn_id)).pow 2)
  have hfrac : ContinuousOn (fun q : ℝ => z*xi/(2*(1-z)*(1-xi*q)^2))
      (Icc (0:ℝ) 1) :=
    continuousOn_const.div hbase (fun q hq => by
      have hqd := hd q hq
      exact (by positivity : 0<2*(1-z)*(1-xi*q)^2).ne')
  apply (continuousOn_const.sub continuousOn_id).div (continuousOn_const.add hfrac)
  intro q hq
  have hqden := hd q hq
  exact (by positivity : 0<1+z*xi/(2*(1-z)*(1-xi*q)^2)).ne'

theorem unitArgmax_interior_of_phi_threshold {xi z v lam : ℝ}
    (hxi : 0< xi) (hxi1 : xi<1) (hz : 0≤ z) (hz1 : z<1)
    (hv : 0< v) (hlam : 0< lam) (hthreshold : lam/v< phi xi z 0) :
    unitArgmax (two xi z v lam) (continuousOn_two_unit hxi hxi1 z v lam)
      ∈ Ioo (0:ℝ) 1 := by
  have he : 0<1-z := sub_pos.mpr hz1
  have hratio : 0< lam/v := div_pos hlam hv
  obtain ⟨r,hr,hrphi⟩ := intermediate_value_Icc' (show (0:ℝ)≤1 by norm_num)
    (continuousOn_phi_unit hxi hxi1 hz hz1)
    (show lam/v∈ Icc (phi xi z 1) (phi xi z 0) from
      ⟨by simpa only [phi_one] using hratio.le,hthreshold.le⟩)
  have hr0 : 0< r := by
    by_contra hn
    have hzero : r=0 := le_antisymm (le_of_not_gt hn) hr.1
    rw [hzero] at hrphi
    exact (not_lt_of_ge hrphi.le) hthreshold
  have hr1 : r<1 := by
    by_contra hn
    have hone : r=1 := le_antisymm hr.2 (le_of_not_gt hn)
    rw [hone,phi_one] at hrphi
    exact (not_lt_of_ge hrphi.ge) hratio
  have hanti := phi_strictAntiOn hxi hxi1 hz hz1
  have hsign (q : ℝ) (hq : q∈ Icc (0:ℝ) 1) :
      twoQDerivative xi z v lam q =
        (2*(1-z)*v*(1+z*xi/(2*(1-z)*(1-xi*q)^2)))*(phi xi z q-lam/v) := by
    have hd : 0<1-xi*q := by nlinarith [hq.2]
    have hD : 0<1+z*xi/(2*(1-z)*(1-xi*q)^2) := by positivity
    exact twoQDerivative_factor hv.ne' he.ne' hd.ne' hD.ne'
  have hleft : StrictMonoOn (two xi z v lam) (Icc 0 r) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      ((continuousOn_two_unit hxi hxi1 z v lam).mono
        (fun q hq => ⟨hq.1,hq.2.trans hr.2⟩))
    intro q hq
    rw [interior_Icc] at hq
    have hq' : q∈ Icc (0:ℝ) 1 := ⟨hq.1.le,hq.2.le.trans hr.2⟩
    have hd : 0<1-xi*q := by nlinarith [hq'.2]
    rw [(hasDerivAt_twoQ (z:=z) (v:=v) (lam:=lam) hd.ne').deriv,hsign q hq']
    apply mul_pos (twoQDerivative_factor_pos hxi hxi1 hz hz1 hv hq')
    apply sub_pos.mpr
    rw [←hrphi]
    exact hanti hq' hr hq.2
  have hright : StrictAntiOn (two xi z v lam) (Icc r 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      ((continuousOn_two_unit hxi hxi1 z v lam).mono
        (fun q hq => ⟨hr.1.trans hq.1,hq.2⟩))
    intro q hq
    rw [interior_Icc] at hq
    have hq' : q∈ Icc (0:ℝ) 1 := ⟨hr.1.trans hq.1.le,hq.2.le⟩
    have hd : 0<1-xi*q := by nlinarith [hq'.2]
    rw [(hasDerivAt_twoQ (z:=z) (v:=v) (lam:=lam) hd.ne').deriv,hsign q hq']
    apply mul_neg_of_pos_of_neg (twoQDerivative_factor_pos hxi hxi1 hz hz1 hv hq')
    apply sub_neg.mpr
    rw [←hrphi]
    exact hanti hr hq' hq.1
  let q := unitArgmax (two xi z v lam) (continuousOn_two_unit hxi hxi1 z v lam)
  have hq := unitArgmax_spec (two xi z v lam) (continuousOn_two_unit hxi hxi1 z v lam)
  have hq0 : q≠0 := by
    intro heq
    have hmax := hq.2 r hr
    change two xi z v lam r≤ two xi z v lam q at hmax
    rw [heq] at hmax
    exact (not_lt_of_ge hmax) (hleft ⟨le_rfl,hr.1⟩ ⟨hr.1,le_rfl⟩ hr0)
  have hq1 : q≠1 := by
    intro heq
    have hmax := hq.2 r hr
    change two xi z v lam r≤ two xi z v lam q at hmax
    rw [heq] at hmax
    exact (not_lt_of_ge hmax) (hright ⟨le_rfl,hr.2⟩ ⟨hr.2,le_rfl⟩ hr1)
  exact ⟨lt_of_le_of_ne hq.1.1 hq0.symm,lt_of_le_of_ne hq.1.2 hq1⟩

namespace PrimitiveInput
variable (p : PrimitiveInput)

theorem source_q_monotone_without_interior : Monotone p.q := by
  intro v w hvw
  by_contra hn
  have hq : p.q w< p.q v := lt_of_not_ge hn
  have hvw' : v.1< w.1 := by
    apply lt_of_le_of_ne (show v.1≤ w.1 from hvw)
    intro heq
    have hvwEq : v=w := Subtype.ext heq
    rw [hvwEq] at hq
    exact lt_irrefl _ hq
  have hvq := p.q_mem v
  have hwq := p.q_mem w
  have hlast : 0<2-p.q v-p.q w := by linarith [hvq.2, hwq.2]
  have hp : 0<(w.1-v.1)*(1-p.z)*(p.q v-p.q w)*(2-p.q v-p.q w) := by
    exact mul_pos (mul_pos (mul_pos (sub_pos.mpr hvw')
      (sub_pos.mpr p.z_lt_one)) (sub_pos.mpr hq)) hlast
  have hfirst := p.q_max v (p.q w) hwq
  have hsecond := p.q_max w (p.q v) hvq
  have hid :
      (two p.xi p.z w.1 p.lam (p.q v)-two p.xi p.z w.1 p.lam (p.q w))-
      (two p.xi p.z v.1 p.lam (p.q v)-two p.xi p.z v.1 p.lam (p.q w)) =
      (w.1-v.1)*(1-p.z)*(p.q v-p.q w)*(2-p.q v-p.q w) := by
    unfold two
    ring
  linarith

theorem source_q_measurable_without_interior : Measurable p.q :=
  p.source_q_monotone_without_interior.measurable

theorem source_q_integrable_without_interior :
    Integrable p.q (p.activeValues : Measure p.Value) :=
  Integrable.of_bound p.source_q_measurable_without_interior.aestronglyMeasurable 1
    (ae_of_all _ (fun v => by
      rw [Real.norm_eq_abs,abs_of_nonneg (p.q_mem v).1]
      exact (p.q_mem v).2))

theorem source_q_phi_on_support (v : p.Value) (hvK : v.1∈ p.activeSupport) :
    phi p.xi p.z (p.q v)=p.lam/v.1 := by
  have hxi := p.xi_pos
  have hz := p.z_nonneg
  have hq := p.q_interior_on_support v hvK
  have hv : 0< v.1 := p.vlo_pos.trans_le v.property.1
  have he : 0<1-p.z := sub_pos.mpr p.z_lt_one
  have hd : 0<1-p.xi*p.q v := by nlinarith [p.xi_pos,p.xi_lt_one,hq.2]
  have hD : 0<1+p.z*p.xi/(2*(1-p.z)*(1-p.xi*p.q v)^2) := by positivity
  have hmax : IsLocalMax (two p.xi p.z v.1 p.lam) (p.q v) := by
    change ∀ᶠ r in nhds (p.q v),two p.xi p.z v.1 p.lam r≤ two p.xi p.z v.1 p.lam (p.q v)
    filter_upwards [Ioo_mem_nhds hq.1 hq.2] with r hr
    exact p.q_max v r ⟨hr.1.le,hr.2.le⟩
  have hzero : twoQDerivative p.xi p.z v.1 p.lam (p.q v)=0 :=
    hmax.hasDerivAt_eq_zero (hasDerivAt_twoQ hd.ne')
  have heq := twoQDerivative_factor (xi:=p.xi) (z:=p.z) (v:=v.1)
    (lam:=p.lam) (q:=p.q v) hv.ne' he.ne' hd.ne' hD.ne'
  rw [hzero] at heq
  have hf := twoQDerivative_factor_pos p.xi_pos p.xi_lt_one p.z_nonneg p.z_lt_one hv (p.q_mem v)
  exact sub_eq_zero.mp ((mul_eq_zero.mp heq.symm).resolve_left hf.ne')

theorem source_price_upper_from_supported_clearing :
    p.lam≤ p.vhi*phi p.xi p.z p.qbar := by
  have hxi := p.xi_pos
  have hz := p.z_nonneg
  have he : 0<1-p.z := sub_pos.mpr p.z_lt_one
  have hqbar : p.qbar∈ Icc (0:ℝ) 1 := ⟨p.qbar_pos.le,p.qbar_lt_one.le⟩
  have hh0 : 0<1-p.xi*p.qbar := by nlinarith [p.xi_pos,p.xi_lt_one,(show p.qbar < 1 from p.qbar_lt_one), (show 0 < p.qbar from p.qbar_pos)]
  have hphi : 0< phi p.xi p.z p.qbar := by
    unfold phi
    exact div_pos (sub_pos.mpr p.qbar_lt_one) (by positivity)
  by_contra hn
  have hlamhi : p.vhi*phi p.xi p.z p.qbar< p.lam := lt_of_not_ge hn
  have hpoint : ∀ᵐ v ∂(p.activeValues : Measure p.Value),p.q v< p.qbar := by
    filter_upwards [p.active_supported] with v hvK
    by_contra hbad
    have hbad' : p.qbar≤ p.q v := le_of_not_gt hbad
    have hvpos := p.vlo_pos.trans_le v.property.1
    have hp := (phi_strictAntiOn p.xi_pos p.xi_lt_one p.z_nonneg p.z_lt_one).antitoneOn
      hqbar (p.q_mem v) hbad'
    have hbound : p.lam≤ p.vhi*phi p.xi p.z p.qbar := calc
      p.lam = v.1*phi p.xi p.z (p.q v) := by
        rw [p.source_q_phi_on_support v hvK]
        field_simp [hvpos.ne']
      _ ≤ v.1*phi p.xi p.z p.qbar := mul_le_mul_of_nonneg_left hp hvpos.le
      _ ≤ p.vhi*phi p.xi p.z p.qbar := mul_le_mul_of_nonneg_right v.property.2 hphi.le
    exact (not_lt_of_ge hbound) hlamhi
  have hi := (integrable_const p.qbar).sub p.source_q_integrable_without_interior
  have hnn : 0≤ᵐ[(p.activeValues : Measure p.Value)] (fun v => p.qbar-p.q v) :=
    hpoint.mono (fun _ hv => (sub_pos.mpr hv).le)
  have hs : Function.support (fun v : p.Value => p.qbar-p.q v) =ᵐ[
      (p.activeValues : Measure p.Value)] univ := by
    filter_upwards [hpoint] with v hv
    apply propext
    change (p.qbar-p.q v ≠ 0) ↔ True
    exact iff_true_intro (sub_pos.mpr hv).ne'
  have hpositive : 0<∫v : p.Value,p.qbar-p.q v ∂(p.activeValues : Measure p.Value) := by
    apply (integral_pos_iff_support_of_nonneg_ae hnn hi).mpr
    rw [measure_congr hs,measure_univ]
    exact zero_lt_one
  have hclear : (∫v : p.Value,p.q v ∂(p.activeValues : Measure p.Value))=p.qbar := p.clearing
  rw [integral_sub (integrable_const p.qbar) p.source_q_integrable_without_interior,
    integral_const,probReal_univ,one_smul,hclear,sub_self] at hpositive
  exact lt_irrefl _ hpositive

theorem source_interior_phi_scale :
    phi p.xi p.z p.qbar=p.h0*inwardScale p.xi p.z p.qbar := by
  have hxi := p.xi_pos
  have hz := p.z_nonneg
  have he : 0<1-p.z := sub_pos.mpr p.z_lt_one
  have hh : 0<1-p.xi*p.qbar := by nlinarith [p.xi_pos,p.xi_lt_one,(show p.qbar < 1 from p.qbar_lt_one), (show 0 < p.qbar from p.qbar_pos)]
  let t := 1-p.xi*p.qbar
  let alpha := p.z*p.xi/(2*(1-p.z))
  have ht : t ≠ 0 := hh.ne'
  have hden : 1+p.z*p.xi/(2*(1-p.z)*t^2) = (t^2+alpha)/t^2 := by
    dsimp only [alpha]
    field_simp [he.ne', ht]
  change (1-p.qbar)/(1+p.z*p.xi/(2*(1-p.z)*t^2)) =
    t*((1-p.qbar)*t/(t^2+alpha))
  rw [hden, div_div_eq_mul_div]
  ring

theorem source_inwardScale_lt_phi_zero :
    inwardScale p.xi p.z p.qbar< phi p.xi p.z 0 := by
  have hxi := p.xi_pos
  have hz := p.z_nonneg
  let alpha := p.z*p.xi/(2*(1-p.z))
  let h0 := 1-p.xi*p.qbar
  have he : 0<1-p.z := sub_pos.mpr p.z_lt_one
  have ha : 0≤ alpha := by dsimp only [alpha];positivity
  have hh : 0< h0 := by dsimp only [h0];nlinarith [p.xi_pos,p.xi_lt_one,(show p.qbar < 1 from p.qbar_lt_one), (show 0 < p.qbar from p.qbar_pos)]
  have hh1 : h0≤1 := by dsimp only [h0];nlinarith [p.xi_pos,(show 0 < p.qbar from p.qbar_pos)]
  have hD : 0< h0^2+alpha := by positivity
  have hA : 0<1+alpha := by positivity
  have hleft : 0< h0*p.qbar*(1-p.xi) :=
    mul_pos (mul_pos hh p.qbar_pos) (sub_pos.mpr p.xi_lt_one)
  have hright : 0≤ alpha*(1-(1-p.qbar)*h0) := by
    apply mul_nonneg ha
    have hqh : 0≤ p.qbar*h0 := mul_nonneg p.qbar_pos.le hh.le
    nlinarith
  have hid : h0^2+alpha-((1-p.qbar)*h0)*(1+alpha)=
      h0*p.qbar*(1-p.xi)+alpha*(1-(1-p.qbar)*h0) := by
    dsimp only [h0]
    ring
  rw [phi_zero]
  change ((1-p.qbar)*h0)/(h0^2+alpha)<1/(1+alpha)
  apply (div_lt_div_iff₀ hD hA).mpr
  nlinarith

theorem source_lambda_below_endpoint_threshold : p.lam< p.vlo*phi p.xi p.z 0 := by
  have hh : 0< p.h0 := by dsimp only [h0];nlinarith [p.xi_pos,p.xi_lt_one,(show p.qbar < 1 from p.qbar_lt_one), (show 0 < p.qbar from p.qbar_pos)]
  have hu := p.source_price_upper_from_supported_clearing
  rw [p.source_interior_phi_scale] at hu
  have hmul := mul_lt_mul_of_pos_left p.inward_upper hh
  change p.h0*(inwardScale p.xi p.z p.qbar*p.vhi) < p.h0*p.U at hmul
  have hprice : p.lam< p.L := (show p.lam< p.h0*p.U by nlinarith).trans p.box_upper
  calc
    p.lam < p.L := hprice
    _ < inwardScale p.xi p.z p.qbar*p.vlo := p.inward_lower
    _ < phi p.xi p.z 0*p.vlo :=
      mul_lt_mul_of_pos_right p.source_inwardScale_lt_phi_zero p.vlo_pos
    _ = p.vlo*phi p.xi p.z 0 := mul_comm _ _

theorem q_interior (v : p.Value) : p.q v∈ Ioo (0:ℝ) 1 := by
  have hxi := p.xi_pos
  have hz := p.z_nonneg
  have hv : 0< v.1 := p.vlo_pos.trans_le v.property.1
  have he : 0<1-p.z := sub_pos.mpr p.z_lt_one
  have hphi0 : 0< phi p.xi p.z 0 := by rw [phi_zero];positivity
  have hlam : p.lam< v.1*phi p.xi p.z 0 := p.source_lambda_below_endpoint_threshold.trans_le
    (mul_le_mul_of_nonneg_right v.property.1 hphi0.le)
  exact unitArgmax_interior_of_phi_threshold p.xi_pos p.xi_lt_one p.z_nonneg p.z_lt_one
    hv p.lam_pos ((div_lt_iff₀ hv).mpr (by simpa only [mul_comm] using hlam))

end PrimitiveInput
end FCAppendix.Affine.Hybrid.Native02
