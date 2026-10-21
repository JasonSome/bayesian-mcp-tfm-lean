import FCAppendix.Affine.Hybrid.Native02.SourceInterior
import FCAppendix.Affine.Hybrid.ActiveMenuEndpointSigns

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open MeasureTheory Set Filter Topology

theorem bidDerivative_eq_twoQDerivative {xi z v lam b : ℝ}
    (hxi : xi≠0) (hlam : lam≠0) (hb : b≠0) :
    bidDerivative xi z v lam b =
      twoQDerivative xi z v lam (exposure xi lam b)*(lam/(xi*b^2)) := by
  have hd : 1-xi*exposure xi lam b=lam/b := by
    unfold exposure
    field_simp [hxi,hb]
    ring
  unfold twoQDerivative bidDerivative
  rw [hd]
  unfold exposure
  field_simp [hxi,hlam,hb]

namespace PrimitiveInput
variable (p : PrimitiveInput)

theorem source_q_first_order (v : p.Value) :
    twoQDerivative p.xi p.z v.1 p.lam (p.q v)=0 := by
  have hq := p.q_interior v
  have hd : 0<1-p.xi*p.q v := by nlinarith [p.xi_pos,p.xi_lt_one,hq.2]
  have hmax : IsLocalMax (two p.xi p.z v.1 p.lam) (p.q v) := by
    change ∀ᶠ r in nhds (p.q v),
      two p.xi p.z v.1 p.lam r≤ two p.xi p.z v.1 p.lam (p.q v)
    filter_upwards [Ioo_mem_nhds hq.1 hq.2] with r hr
    exact p.q_max v r ⟨hr.1.le,hr.2.le⟩
  exact hmax.hasDerivAt_eq_zero (hasDerivAt_twoQ hd.ne')

theorem source_q_phi (v : p.Value) : phi p.xi p.z (p.q v)=p.lam/v.1 := by
  have hxi := p.xi_pos
  have hzn := p.z_nonneg
  have hv : 0< v.1 := p.vlo_pos.trans_le v.property.1
  have hq := p.q_mem v
  have hd : 0<1-p.xi*p.q v := by nlinarith [p.xi_pos,p.xi_lt_one,hq.2]
  have he : 0<1-p.z := sub_pos.mpr p.z_lt_one
  have hD : 0<1+p.z*p.xi/(2*(1-p.z)*(1-p.xi*p.q v)^2) := by positivity
  have heq := twoQDerivative_factor (xi:=p.xi) (z:=p.z) (v:=v.1)
    (lam:=p.lam) (q:=p.q v) hv.ne' he.ne' hd.ne' hD.ne'
  rw [p.source_q_first_order] at heq
  have hf := twoQDerivative_factor_pos p.xi_pos p.xi_lt_one p.z_nonneg p.z_lt_one hv hq
  have hz := (mul_eq_zero.mp heq.symm).resolve_left hf.ne'
  exact sub_eq_zero.mp hz

theorem source_q_eq_of_phi (v : p.Value) (r : ℝ) (hr : r∈ Icc (0:ℝ) 1)
    (hphi : phi p.xi p.z r=p.lam/v.1) : r=p.q v :=
  phi_injectiveOn p.xi_pos p.xi_lt_one p.z_nonneg p.z_lt_one hr (p.q_mem v)
    (hphi.trans (p.source_q_phi v).symm)

theorem source_q_monotone : Monotone p.q := by
  intro v w hvw
  by_contra hn
  have hqwqv : p.q w< p.q v := lt_of_not_ge hn
  have hh := phi_strictAntiOn p.xi_pos p.xi_lt_one p.z_nonneg p.z_lt_one
    (p.q_mem w) (p.q_mem v) hqwqv
  rw [p.source_q_phi,p.source_q_phi] at hh
  have hd := div_le_div_of_nonneg_left p.lam_pos.le
    (p.vlo_pos.trans_le v.property.1) (show v.1≤ w.1 from hvw)
  exact (not_lt_of_ge hd) hh

theorem source_response_measurable : Measurable p.q := p.source_q_monotone.measurable

theorem source_response_integrable : Integrable p.q (p.activeValues : Measure p.Value) :=
  Integrable.of_bound p.source_response_measurable.aestronglyMeasurable 1
    (ae_of_all _ (fun v => by
      rw [Real.norm_eq_abs,abs_of_nonneg (p.q_mem v).1]
      exact (p.q_mem v).2))

theorem source_h0_pos : 0< p.h0 := by
  change 0 < 1-p.xi*p.qbar
  nlinarith [p.xi_pos, p.xi_lt_one, (show p.qbar < 1 from p.qbar_lt_one),
    (show 0 < p.qbar from p.qbar_pos)]

theorem source_phi_scale : phi p.xi p.z p.qbar=p.h0*inwardScale p.xi p.z p.qbar :=
  p.source_interior_phi_scale

theorem source_price_clearing_bounds :
    p.lam∈ Icc (p.vlo*phi p.xi p.z p.qbar) (p.vhi*phi p.xi p.z p.qbar) := by
  have hclear : (∫ v : p.Value, p.q v ∂(p.activeValues : Measure p.Value)) = p.qbar := p.clearing
  let vlo : p.Value := ⟨p.vlo,⟨le_rfl,p.value_order⟩⟩
  let vhi : p.Value := ⟨p.vhi,⟨p.value_order,le_rfl⟩⟩
  have hl : p.q vlo≤ p.qbar := by
    have h := integral_mono_ae (integrable_const (p.q vlo)) p.source_response_integrable
      (ae_of_all (p.activeValues : Measure p.Value)
        (fun v => p.source_q_monotone (show vlo≤ v from v.property.1)))
    simpa only [integral_const,probReal_univ,one_smul,hclear] using h
  have hu : p.qbar≤ p.q vhi := by
    have h := integral_mono_ae p.source_response_integrable (integrable_const (p.q vhi))
      (ae_of_all (p.activeValues : Measure p.Value)
        (fun v => p.source_q_monotone (show v≤ vhi from v.property.2)))
    simpa only [integral_const,probReal_univ,one_smul,hclear] using h
  have hqb : p.qbar∈ Icc (0:ℝ) 1 := ⟨p.qbar_pos.le,p.qbar_lt_one.le⟩
  have ha := (phi_strictAntiOn p.xi_pos p.xi_lt_one p.z_nonneg p.z_lt_one).antitoneOn
  have hpl := ha (p.q_mem vlo) hqb hl
  have hpu := ha hqb (p.q_mem vhi) hu
  rw [p.source_q_phi] at hpl hpu
  constructor
  · have h := (le_div_iff₀ p.vlo_pos).mp hpl
    simpa only [vlo,mul_comm] using h
  · have h := (div_le_iff₀ (p.vlo_pos.trans_le p.value_order)).mp hpu
    simpa only [vhi,mul_comm] using h

theorem source_price_box : p.lam∈ Ioo (p.h0*p.L) (p.h0*p.U) := by
  have hh := p.source_h0_pos
  have hb := p.source_price_clearing_bounds
  rw [p.source_phi_scale] at hb
  have hl := mul_lt_mul_of_pos_left p.inward_lower hh
  have hu := mul_lt_mul_of_pos_left p.inward_upper hh
  change p.h0*p.L < p.h0*(inwardScale p.xi p.z p.qbar*p.vlo) at hl
  change p.h0*(inwardScale p.xi p.z p.qbar*p.vhi) < p.h0*p.U at hu
  constructor <;> nlinarith [hb.1, hb.2]

theorem source_box_exposure_interior (b : ℝ) (hb : b∈ Icc p.L p.U) :
    exposure p.xi p.lam b∈ Ioo (0:ℝ) 1 := by
  apply exposure_mem_Ioo p.xi_pos (p.L_pos.trans_le hb.1)
  · have hk : 0≤1-p.xi := (sub_pos.mpr p.xi_lt_one).le
    exact (mul_le_mul_of_nonneg_left hb.2 hk).trans_lt
      (p.box_lower.trans p.source_price_box.1)
  · exact p.source_price_box.2.trans (p.box_upper.trans_le hb.1)

theorem source_response_interior (v : p.Value) : p.beta v∈ Ioo p.L p.U := by
  have hxi := p.xi_pos
  have hzn := p.z_nonneg
  have hlambda := p.lam_pos
  have hv : 0< v.1 := p.vlo_pos.trans_le v.property.1
  have hl := p.source_box_exposure_interior p.L ⟨le_rfl,p.L_lt_U.le⟩
  have hu := p.source_box_exposure_interior p.U ⟨p.L_lt_U.le,le_rfl⟩
  have hend := active_menu_endpoint_signs p.xi_pos p.xi_lt_one p.z_nonneg p.z_lt_one
    ⟨p.qbar_pos,p.qbar_lt_one⟩ p.L_pos p.L_lt_U.le p.value_surplus
    p.inward_lower p.inward_upper v.property
    ⟨p.source_price_box.1.le,p.source_price_box.2.le⟩
  have hdiffL : 0< twoQDerivative p.xi p.z v.1 p.lam (exposure p.xi p.lam p.L) := by
    rw [bidDerivative_eq_twoQDerivative p.xi_pos.ne' p.lam_pos.ne' p.L_pos.ne'] at hend
    exact pos_of_mul_pos_left hend.1 (by positivity)
  have hdiffU : twoQDerivative p.xi p.z v.1 p.lam (exposure p.xi p.lam p.U)<0 := by
    rw [bidDerivative_eq_twoQDerivative p.xi_pos.ne' p.lam_pos.ne' p.U_pos.ne'] at hend
    exact neg_of_mul_neg_left hend.2 (by positivity)
  have he : 0<1-p.z := sub_pos.mpr p.z_lt_one
  have hsign (r : ℝ) (hr : r∈ Icc (0:ℝ) 1) :
      twoQDerivative p.xi p.z v.1 p.lam r =
        (2*(1-p.z)*v.1*(1+p.z*p.xi/(2*(1-p.z)*(1-p.xi*r)^2)))*
          (phi p.xi p.z r-p.lam/v.1) := by
    have hd : 0<1-p.xi*r := by nlinarith [p.xi_pos,p.xi_lt_one,hr.2]
    exact twoQDerivative_factor hv.ne' he.ne' hd.ne' (by positivity)
  rw [hsign _ ⟨hl.1.le,hl.2.le⟩] at hdiffL
  rw [hsign _ ⟨hu.1.le,hu.2.le⟩] at hdiffU
  have hphiL : p.lam/v.1< phi p.xi p.z (exposure p.xi p.lam p.L) :=
    sub_pos.mp (pos_of_mul_pos_right hdiffL
      (twoQDerivative_factor_pos p.xi_pos p.xi_lt_one p.z_nonneg p.z_lt_one
        hv ⟨hl.1.le,hl.2.le⟩).le)
  have hphiU : phi p.xi p.z (exposure p.xi p.lam p.U)< p.lam/v.1 :=
    sub_neg.mp (neg_of_mul_neg_right hdiffU
      (twoQDerivative_factor_pos p.xi_pos p.xi_lt_one p.z_nonneg p.z_lt_one
        hv ⟨hu.1.le,hu.2.le⟩).le)
  have ha := (phi_strictAntiOn p.xi_pos p.xi_lt_one p.z_nonneg p.z_lt_one).antitoneOn
  have hql : exposure p.xi p.lam p.L< p.q v := by
    by_contra hn
    have hh := ha (p.q_mem v) ⟨hl.1.le,hl.2.le⟩ (le_of_not_gt hn)
    rw [p.source_q_phi] at hh
    exact not_lt_of_ge hh hphiL
  have hqu : p.q v< exposure p.xi p.lam p.U := by
    by_contra hn
    have hh := ha ⟨hu.1.le,hu.2.le⟩ (p.q_mem v) (le_of_not_gt hn)
    rw [p.source_q_phi] at hh
    exact not_lt_of_ge hh hphiU
  have hd : 0<1-p.xi*p.q v := by nlinarith [p.xi_pos,p.xi_lt_one,(p.q_mem v).2]
  unfold exposure at hql hqu
  have hxl := (div_lt_iff₀ p.xi_pos).mp hql
  have hxu := (lt_div_iff₀ p.xi_pos).mp hqu
  have hlm := mul_lt_mul_of_pos_right hxl p.L_pos
  have hum := mul_lt_mul_of_pos_right hxu p.U_pos
  have hLc : p.lam/p.L*p.L=p.lam := div_mul_cancel₀ _ p.L_pos.ne'
  have hUc : p.lam/p.U*p.U=p.lam := div_mul_cancel₀ _ p.U_pos.ne'
  constructor
  · exact (lt_div_iff₀ hd).mpr (by nlinarith)
  · exact (div_lt_iff₀ hd).mpr (by nlinarith)

theorem source_response_boxed : ∀ v : p.Value,p.beta v∈ Icc p.L p.U :=
  fun v => ⟨(p.source_response_interior v).1.le,(p.source_response_interior v).2.le⟩

end PrimitiveInput
end FCAppendix.Affine.Hybrid.Native02
