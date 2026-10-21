import FCAppendix.Existence.NarrowPayOnceStationary

noncomputable section
namespace FCAppendix.Existence.NarrowPayOnce
open Set Filter Topology MeasureTheory
open PayOnce PayOnce.OwnImpact CommonList
open scoped BigOperators

theorem finiteRowVelocity_pos {R n c : ℕ} (hn : 2≤n) (hR : 0<R)
    {V : Type*} (beta : V→ℝ) (z : ℝ) (omega : Fin R→V)
    (hz : 0<z) (hbeta : ∀v,0<beta v)
    (hp : ∀i,kernelMarginal n c (rowBids beta z omega) i∈Ioo (0:ℝ) 1) :
    0<finiteRowVelocity n c beta z omega := by
  let b:=rowBids beta z omega
  let p:=kernelMarginal n c b
  let s:=fun i=>sensitivity n (b i) (p i)
  have hb : ∀i,0<b i := fun i=>Fin.cases hz (fun j=>hbeta (omega j)) i
  have hs : ∀i,0<s i := fun i=>sensitivity_pos hn (hb i) ⟨(hp i).1.le,(hp i).2.le⟩
  letI : NeZero R := ⟨by omega⟩
  have hrest : 0<∑j : Fin R,s j.succ := Finset.sum_pos (fun j _=>hs j.succ) Finset.univ_nonempty
  have hsum : s 0<∑i,s i := by rw [Fin.sum_univ_succ]; linarith
  have hsum0 : 0<∑i,s i := (hs 0).trans hsum
  have hdiv : 1-s 0/(∑i,s i)>0 := sub_pos.mpr ((div_lt_one hsum0).mpr hsum)
  exact mul_pos (mul_pos (hs 0) (H_pos n (by omega) (p 0) (hp 0).1.le (hp 0).2.le)) hdiv

namespace FiniteScoreControl
variable {n R c : ℕ} {w0 kappa eps delta : ℝ}
  (U : FiniteScoreControl n R c w0 kappa eps delta)
  (nu : Measure U.valueBand) [IsProbabilityMeasure nu]

theorem expected_strict_type (beta : U.valueBand→ℝ) (hbeta : Continuous beta)
    (hb : ∀v,beta v∈Icc (U.B-eps) (U.B+eps))
    (v w z : ℝ) (hvw : v<w) (hz : z∈Icc (U.B-eps) (U.B+eps)) :
    finiteExpectedScore (R:=R) n c nu beta v z<finiteExpectedScore (R:=R) n c nu beta w z := by
  let f : (Fin R→U.valueBand)→ℝ := fun omega=>finiteRowScore n c beta w z omega-finiteRowScore n c beta v z omega
  have hf (omega : Fin R→U.valueBand) : 0<f omega := by
    have hp := U.interior _ (U.row_box beta hb z hz omega)
    have hu := finiteRowVelocity_pos U.n_ge (by have:=U.c_pos; have:=U.c_le; omega)
      beta z omega (U.lower_pos.trans_le hz.1) (fun v=>U.lower_pos.trans_le (hb v).1) hp
    have hn : (0:ℝ)<n := by exact_mod_cast (show 0<n by have:=U.n_ge; omega)
    have he : f omega=(w-v)*(n:ℝ)*(1-finiteRowMarginal n c beta z omega)^(n-1)*
        finiteRowVelocity n c beta z omega := by dsimp [f,finiteRowScore]; ring
    rw [he]
    have hp0 : 0<1-finiteRowMarginal n c beta z omega := sub_pos.mpr (hp 0).2
    positivity
  have hfi : Integrable f (Measure.pi (fun _ : Fin R=>nu)) :=
    (U.row_integrable nu beta hbeta hb w z hz).sub (U.row_integrable nu beta hbeta hb v z hz)
  have hpos : 0<∫omega,f omega ∂Measure.pi (fun _ : Fin R=>nu) := by
    apply (integral_pos_iff_support_of_nonneg (fun omega=>(hf omega).le) hfi).mpr
    have he : Function.support f=Set.univ := by ext omega; simp only [Function.mem_support,Set.mem_univ,iff_true]; exact (hf omega).ne'
    rw [he]
    simp
  dsimp [f] at hpos
  rw [integral_sub (U.row_integrable nu beta hbeta hb w z hz) (U.row_integrable nu beta hbeta hb v z hz)] at hpos
  exact sub_pos.mp hpos

theorem stationary_strictMono (beta : U.strategyBand)
    (hroot : ∀v : U.valueBand,finiteExpectedScore (R:=R) n c nu beta.val v (beta.val v)=0) :
    StrictMono beta.val := by
  let D := U.finiteScoreData nu
  have hreply (v : U.valueBand) : D.reply beta v=beta.val v :=
    (D.root_unique beta v (beta.property v) (hroot v)).symm
  have hm := D.reply_strictMono beta (fun v w hvw z hz=>
    U.expected_strict_type nu beta.val beta.val.continuous beta.property v w z hvw hz)
  intro v w hvw
  simpa only [hreply] using hm hvw

theorem stationary_displacement (beta : U.strategyBand)
    (hroot : ∀v : U.valueBand,finiteExpectedScore (R:=R) n c nu beta.val v (beta.val v)=0) :
    ∀v : U.valueBand,|beta.val v-U.B|≤(2*U.typeRate/kappa)*delta := by
  let b0 := BoundedContinuousFunction.const U.valueBand U.B
  let D := dist beta.val b0
  have hD : 0≤D := dist_nonneg
  have hz : U.B∈Icc (U.B-eps) (U.B+eps) := ⟨by linarith [U.eps_pos],by linarith [U.eps_pos]⟩
  have hd (v : U.valueBand) : |beta.val v-U.B|≤D := by
    simpa only [D,b0,Real.dist_eq,BoundedContinuousFunction.const_apply] using
      BoundedContinuousFunction.dist_coe_le_dist (f:=beta.val) (g:=b0) v
  have hrootbound (v : U.valueBand) : U.own*|beta.val v-U.B|≤U.rival*D+U.typeRate*delta := by
    have hpar := U.expected_rival_bound nu beta.val (fun _=>U.B) beta.val.continuous continuous_const
      beta.property (fun _=>hz) D hD hd v U.B hz
    have htype := (U.expected_type_bound nu (fun _=>U.B) continuous_const (fun _=>hz) v w0 U.B hz).trans
      (mul_le_mul_of_nonneg_left (U.value_mem v) U.typeRate_nonneg)
    rw [U.expected_constant_zero nu,sub_zero] at htype
    have hcenter : |finiteExpectedScore (R:=R) n c nu beta.val v U.B|≤U.rival*D+U.typeRate*delta := by
      calc
        _=|(finiteExpectedScore (R:=R) n c nu beta.val v U.B-
          finiteExpectedScore (R:=R) n c nu (fun _=>U.B) v U.B)+
          finiteExpectedScore (R:=R) n c nu (fun _=>U.B) v U.B| := by congr 1; ring
        _≤|finiteExpectedScore (R:=R) n c nu beta.val v U.B-
          finiteExpectedScore (R:=R) n c nu (fun _=>U.B) v U.B|+
          |finiteExpectedScore (R:=R) n c nu (fun _=>U.B) v U.B| := abs_add_le _ _
        _≤_ := add_le_add hpar htype
    have hinv := Exclusive.Existence.strongDecrease_inverse_bound U.own_pos
      (fun a ha b hb hab=>U.expected_decrease nu beta.val beta.val.continuous beta.property v a b ha hb hab)
      (beta.property v) hz
    rw [hroot v,zero_sub,abs_neg] at hinv
    exact hinv.trans hcenter
  have hC : 0≤U.rival*D+U.typeRate*delta :=
    add_nonneg (mul_nonneg U.rival_nonneg hD) (mul_nonneg U.typeRate_nonneg U.delta_nonneg)
  have hnorm : D≤(U.rival*D+U.typeRate*delta)/U.own := by
    apply (BoundedContinuousFunction.dist_le (div_nonneg hC U.own_pos.le)).mpr
    intro v
    rw [Real.dist_eq]
    apply (le_div_iff₀ U.own_pos).mpr
    change |beta.val v-U.B| *U.own≤_
    nlinarith [hrootbound v]
  have hnorm' := (le_div_iff₀ U.own_pos).mp hnorm
  have hgap := mul_le_mul_of_nonneg_right U.contraction_gap hD
  have hbound : D≤(2*U.typeRate/kappa)*delta := by
    apply (le_of_mul_le_mul_left ?_ U.kappa_pos)
    calc
      kappa*D≤2*(U.typeRate*delta) := by nlinarith
      _=kappa*((2*U.typeRate/kappa)*delta) := by field_simp [U.kappa_pos.ne']
  exact fun v=>(hd v).trans hbound

end FiniteScoreControl
end FCAppendix.Existence.NarrowPayOnce
