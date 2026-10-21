import FCAppendix.Existence.NarrowPayOnceGlobalOptimal

noncomputable section
namespace FCAppendix.Existence.NarrowPayOnce
open Set Filter Topology MeasureTheory CommonList PayOnce

namespace FiniteScoreControl
variable {n R c : ℕ} {w0 kappa eps delta : ℝ}
  (U : FiniteScoreControl n R c w0 kappa eps delta)
  (nu : Measure U.valueBand) [IsProbabilityMeasure nu]

theorem stationary_bid_lt_value (beta : U.strategyBand)
    (hroot : ∀v : U.valueBand,finiteExpectedScore (R:=R) n c nu beta.val v (beta.val v)=0)
    (v : U.valueBand) : beta.val v<(v:ℝ) := by
  by_contra hh
  have hle : (v:ℝ)≤beta.val v := le_of_not_gt hh
  have hR : 0<R := by have:=U.c_pos; have:=U.c_le; omega
  have hneg (omega : Fin R→U.valueBand) : finiteRowScore n c beta.val v (beta.val v) omega<0 := by
    have hp:=U.interior _ (U.row_box beta.val beta.property (beta.val v) (beta.property v) omega)
    have hv:=finiteRowVelocity_pos U.n_ge hR beta.val (beta.val v) omega
      (U.lower_pos.trans_le (beta.property v).1)
      (fun v=>U.lower_pos.trans_le (beta.property v).1) hp
    have hs:=success_pos n (by have:=U.n_ge; omega) _ (hp 0).1 (hp 0).2.le
    have hp0 : finiteRowMarginal n c beta.val (beta.val v) omega∈Ioo (0:ℝ) 1 := hp 0
    change 0<success n (finiteRowMarginal n c beta.val (beta.val v) omega) at hs
    have hprod : ((v:ℝ)-beta.val v)*(n:ℝ)*(1-finiteRowMarginal n c beta.val (beta.val v) omega)^(n-1)*
        finiteRowVelocity n c beta.val (beta.val v) omega≤0 := by
      apply mul_nonpos_of_nonpos_of_nonneg _ hv.le
      apply mul_nonpos_of_nonpos_of_nonneg _ (pow_nonneg (by linarith [hp0.2]) _)
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hle) (Nat.cast_nonneg n)
    dsimp [finiteRowScore]
    linarith
  have hi:Integrable (fun omega : Fin R→U.valueBand=>-finiteRowScore n c beta.val v (beta.val v) omega)
      (Measure.pi (fun _=>nu)) :=
    (U.row_integrable nu beta.val beta.val.continuous beta.property v (beta.val v) (beta.property v)).neg
  have hpos : 0<∫omega : Fin R→U.valueBand,-finiteRowScore n c beta.val v (beta.val v) omega
      ∂Measure.pi (fun _=>nu) := by
    apply (integral_pos_iff_support_of_nonneg (fun omega=>(neg_pos.mpr (hneg omega)).le) hi).mpr
    have hs:Function.support (fun omega : Fin R→U.valueBand=>-finiteRowScore n c beta.val v (beta.val v) omega)=univ := by
      ext omega
      simp only [Function.mem_support,mem_univ,iff_true]
      exact (neg_pos.mpr (hneg omega)).ne'
    rw [hs,measure_univ]
    norm_num
  rw [integral_neg] at hpos
  change 0< -finiteExpectedScore (R:=R) n c nu beta.val v (beta.val v) at hpos
  rw [hroot v] at hpos
  linarith

theorem stationary_utility_pos (beta : U.strategyBand)
    (hroot : ∀v : U.valueBand,finiteExpectedScore (R:=R) n c nu beta.val v (beta.val v)=0)
    (v : U.valueBand) :
    0<finiteExpectedUtility (R:=R) n c nu beta.val v (beta.val v) := by
  have hsurplus:=sub_pos.mpr (U.stationary_bid_lt_value nu beta hroot v)
  have hrow (omega : Fin R→U.valueBand) : 0<finiteRowUtility n c beta.val v (beta.val v) omega := by
    have hp:=U.interior _ (U.row_box beta.val beta.property (beta.val v) (beta.property v) omega)
    exact mul_pos hsurplus (success_pos n (by have:=U.n_ge; omega) _ (hp 0).1 (hp 0).2.le)
  apply (integral_pos_iff_support_of_nonneg (fun omega=>(hrow omega).le)
    (U.integrable_row_utility_positive nu beta v (beta.val v)
      (U.lower_pos.trans_le (beta.property v).1))).mpr
  have hs:Function.support (finiteRowUtility (R:=R) n c beta.val v (beta.val v))=univ := by
    ext omega
    simp only [Function.mem_support,mem_univ,iff_true]
    exact (hrow omega).ne'
  rw [hs,measure_univ]
  norm_num

end FiniteScoreControl
end FCAppendix.Existence.NarrowPayOnce
