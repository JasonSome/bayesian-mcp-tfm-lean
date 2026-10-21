import FCAppendix.Existence.NarrowPayOnceSmoothReply

noncomputable section
namespace FCAppendix.Existence.NarrowPayOnce
open Set Filter Topology MeasureTheory
open PayOnce PayOnce.OwnImpact CommonList
open scoped BigOperators
namespace FiniteScoreControl
variable {n R c : ℕ} {w0 kappa eps delta : ℝ}
  (U : FiniteScoreControl n R c w0 kappa eps delta)

theorem row_open_bid_bound (beta : U.valueBand→ℝ)
    (hb : ∀v,beta v∈Icc (U.B-eps) (U.B+eps)) (w : U.openValueBand)
    (x y : ℝ) (hx : x∈Icc (U.B-eps) (U.B+eps))
    (hy : y∈Icc (U.B-eps) (U.B+eps)) (omega : Fin R→U.valueBand) :
    |finiteRowScore n c beta w y omega-finiteRowScore n c beta w x omega|≤
      (U.A+kappa/3)*|y-x| := by
  have ha := U.row_box beta hb x hx omega
  have hc := U.row_box beta hb y hy omega
  have hrem := profileScore_increment_error U.n_ge (by have:=U.c_le; omega) U.lower_pos
    U.interior (U.derivative_open_types w) (rowBids beta x omega) (rowBids beta y omega) ha hc
  have hlin := (source_reference_linearization U.n_ge U.c_pos U.c_le U.w_pos
    (rowBids beta y omega-rowBids beta x omega)).2
  have he : fderiv ℝ (profileScore n c w0) (fun _ : Fin (R+1)=>U.B)
      (rowBids beta y omega-rowBids beta x omega)= -U.A*(y-x) := by
    simpa only [rowBids,Pi.sub_apply,Fin.cons_zero,Fin.cons_succ,sub_self,
      Finset.sum_const_zero,mul_zero,add_zero] using hlin
  rw [he,norm_rowBids_sub_same] at hrem
  have hpos := fun v=>U.lower_pos.trans_le (hb v).1
  rw [finiteRowScore_eq_profileScore U.n_ge (by have:=U.c_le; omega) beta w y omega
      (U.lower_pos.trans_le hy.1) hpos (U.interior _ hc),
    finiteRowScore_eq_profileScore U.n_ge (by have:=U.c_le; omega) beta w x omega
      (U.lower_pos.trans_le hx.1) hpos (U.interior _ ha)]
  have hA : 0≤U.A := U.kappa_pos.le.trans U.curvature_floor
  calc
    _=|(profileScore n c w (rowBids beta y omega)-profileScore n c w (rowBids beta x omega)-(-U.A*(y-x)))+
      (-U.A*(y-x))| := by congr 1; ring
    _≤|profileScore n c w (rowBids beta y omega)-profileScore n c w (rowBids beta x omega)-(-U.A*(y-x))|+
      |-U.A*(y-x)| := abs_add_le _ _
    _≤kappa/3*|y-x|+U.A*|y-x| := add_le_add hrem (by rw [abs_mul,abs_neg,abs_of_nonneg hA])
    _=_ := by ring

variable (nu : Measure U.valueBand) [IsProbabilityMeasure nu]

theorem expected_open_bid_bound (beta : U.valueBand→ℝ) (hbeta : Continuous beta)
    (hb : ∀v,beta v∈Icc (U.B-eps) (U.B+eps)) (w : U.openValueBand)
    (x y : ℝ) (hx : x∈Icc (U.B-eps) (U.B+eps))
    (hy : y∈Icc (U.B-eps) (U.B+eps)) :
    |finiteExpectedScore (R:=R) n c nu beta w y-finiteExpectedScore (R:=R) n c nu beta w x|≤
      (U.A+kappa/3)*|y-x| := by
  rw [finiteExpectedScore,finiteExpectedScore,← integral_sub
    (U.row_integrable nu beta hbeta hb w y hy) (U.row_integrable nu beta hbeta hb w x hx)]
  have hh := norm_integral_le_of_norm_le_const (μ:=Measure.pi (fun _ : Fin R=>nu))
    (f:=fun omega=>finiteRowScore n c beta w y omega-finiteRowScore n c beta w x omega)
    (C:=(U.A+kappa/3)*|y-x|)
    (ae_of_all _ (fun omega=>by simpa only [Real.norm_eq_abs] using U.row_open_bid_bound beta hb w x y hx hy omega))
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hh

theorem own_partial_abs_le (beta : U.valueBand→ℝ) (hbeta : Continuous beta)
    (hb : ∀v,beta v∈Icc (U.B-eps) (U.B+eps)) (w z : ℝ)
    (hw : w∈U.openValueBand) (hz : z∈Ioo (U.B-eps) (U.B+eps)) :
    |fderiv ℝ (U.expectedJointScore nu beta) (w,z) (0,1)|≤U.A+kappa/3 := by
  have hdF := (U.contDiffAt_expectedJointScore nu beta hbeta hb (w,z) hz).differentiableAt (by norm_num)
  have hcurve : HasDerivAt (fun x : ℝ=>(w,x)) ((0,1):ℝ×ℝ) z :=
    (hasDerivAt_const z w).prodMk (hasDerivAt_id z)
  have hd := hdF.hasFDerivAt.comp_hasDerivAt z hcurve
  have hC : 0≤U.A+kappa/3 := by linarith [U.curvature_floor,U.kappa_pos]
  have hh := hd.le_of_lip' hC (by
    filter_upwards [Ioo_mem_nhds hz.1 hz.2] with x hx
    simpa only [Function.comp_def,Real.norm_eq_abs,expectedJointScore] using
      U.expected_open_bid_bound nu beta hbeta hb ⟨w,hw⟩ z x ⟨hz.1.le,hz.2.le⟩ ⟨hx.1.le,hx.2.le⟩)
  simpa only [Real.norm_eq_abs] using hh

end FiniteScoreControl
end FCAppendix.Existence.NarrowPayOnce
