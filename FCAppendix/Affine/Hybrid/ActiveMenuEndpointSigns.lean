import FCAppendix.Affine.Hybrid.Menu

noncomputable section
namespace FCAppendix.Affine.Hybrid
open Set

lemma bidDerivative_polynomial {xi z v lam b : ℝ} (hxi : xi≠0) (he : 1-z≠0) (hb : b≠0) :
    bidDerivative xi z v lam b=
      (2*(1-z)/(xi^2*b^3))*((v-xi*b)*lam^2-v*(1-xi)*b*lam-
        z*xi^2*b^3/(2*(1-z))) := by
  unfold bidDerivative exposure
  field_simp
  ring

lemma inwardScale_pos {xi z qbar : ℝ} (hxi : 0<xi) (hxi1 : xi<1)
    (hz : 0≤z) (hz1 : z<1) (hq : qbar∈Ioo (0:ℝ) 1) :
    0< inwardScale xi z qbar := by
  have hh : 0<1-xi*qbar := by nlinarith [hq.2]
  unfold inwardScale
  have hd : 0<(1-xi*qbar)^2+z*xi/(2*(1-z)) := by positivity
  exact div_pos (mul_pos (sub_pos.mpr hq.2) hh) hd

theorem active_menu_endpoint_signs {xi z qbar L U vlo vhi v lam : ℝ}
    (hxi : 0<xi) (hxi1 : xi<1) (hz : 0≤z) (hz1 : z<1)
    (hq : qbar∈Ioo (0:ℝ) 1) (hL : 0<L) (hLU : L≤U) (hUv : U<vlo)
    (hboxlo : L< inwardScale xi z qbar*vlo) (hboxhi : inwardScale xi z qbar*vhi<U)
    (hv : v∈Icc vlo vhi)
    (hlam : lam∈Icc ((1-xi*qbar)*L) ((1-xi*qbar)*U)) :
    0<bidDerivative xi z v lam L ∧ bidDerivative xi z v lam U<0 := by
  have he : 0<1-z:=sub_pos.mpr hz1
  have h0 : 0<1-xi*qbar := by nlinarith [hq.2]
  have hU : 0<U:=hL.trans_le hLU
  have hv0 : 0<v:=hU.trans (hUv.trans_le hv.1)
  have hT:=inwardScale_pos hxi hxi1 hz hz1 hq
  have hD : 0<(1-xi*qbar)^2+z*xi/(2*(1-z)) := by positivity
  have hbaseL : 0<bidDerivative xi z v ((1-xi*qbar)*L) L := by
    rw [reference_derivative_identity hxi.ne' he.ne' hL.ne' hD.ne']
    exact mul_pos (by positivity) (by nlinarith [mul_le_mul_of_nonneg_left hv.1 hT.le])
  have hbaseU : bidDerivative xi z v ((1-xi*qbar)*U) U<0 := by
    rw [reference_derivative_identity hxi.ne' he.ne' hU.ne' hD.ne']
    exact mul_neg_of_pos_of_neg (by positivity) (by nlinarith [mul_le_mul_of_nonneg_left hv.2 hT.le])
  have hlamp : 0<lam:= (mul_pos h0 hL).trans_le hlam.1
  constructor
  · have hA : 0<v-xi*L := by nlinarith [hv.1]
    have hC : 0≤z*xi^2*L^3/(2*(1-z)) := by positivity
    have hf : 0<2*(1-z)/(xi^2*L^3) := by positivity
    rw [bidDerivative_polynomial hxi.ne' he.ne' hL.ne'] at hbaseL ⊢
    have hQ : 0<(v-xi*L)*((1-xi*qbar)*L)^2-v*(1-xi)*L*((1-xi*qbar)*L)-
        z*xi^2*L^3/(2*(1-z)) := by
      by_contra hn
      have hh:=mul_nonpos_of_nonneg_of_nonpos hf.le (le_of_not_gt hn)
      linarith
    exact mul_pos hf (quadratic_positive_above hA hC (mul_pos h0 hL) hlam.1 hQ)
  · have hA : 0≤v-xi*U := by nlinarith [hv.1]
    have hC : 0≤z*xi^2*U^3/(2*(1-z)) := by positivity
    have hf : 0<2*(1-z)/(xi^2*U^3) := by positivity
    rw [bidDerivative_polynomial hxi.ne' he.ne' hU.ne'] at hbaseU ⊢
    have hQ : (v-xi*U)*((1-xi*qbar)*U)^2-v*(1-xi)*U*((1-xi*qbar)*U)-
        z*xi^2*U^3/(2*(1-z))<0 := by
      by_contra hn
      have hh:=mul_nonneg hf.le (le_of_not_gt hn)
      linarith
    exact mul_neg_of_pos_of_neg hf (quadratic_negative_below hA hC hlamp hlam.2 hQ)

end FCAppendix.Affine.Hybrid
