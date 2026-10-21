import FCAppendix.Existence.NarrowPayOnceValueSlope
import FCAppendix.Existence.NarrowPayOnceOwnScoreBound
import FCAppendix.Existence.NarrowPayOnceRegularConstants

noncomputable section
namespace FCAppendix.Existence.NarrowPayOnce
open Set Filter Topology MeasureTheory
open PayOnce PayOnce.OwnImpact CommonList

def valueSlopeFloor (n : ℕ) (kappa w0 hi : ℝ) : ℝ :=
  (n:ℝ)*(1-(1+hi)/2)^(n-1)*velocityFloor n (kappa/2) (2*w0)

theorem valueSlopeFloor_pos {n : ℕ} (hn : 2≤n) {kappa w0 hi : ℝ}
    (hk : 0<kappa) (hw : 0<w0) (hhi : hi<1) : 0<valueSlopeFloor n kappa w0 hi := by
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hp : 0<1-(1+hi)/2 := by linarith
  unfold valueSlopeFloor velocityFloor
  positivity

namespace FiniteScoreControl
variable {n R c : ℕ} {w0 kappa eps delta : ℝ}
  (U : FiniteScoreControl n R c w0 kappa eps delta)
  (nu : Measure U.valueBand) [IsProbabilityMeasure nu]
  (beta : U.valueBand→ℝ) (hbeta : Continuous beta)
  (hb : ∀v,beta v∈Icc (U.B-eps) (U.B+eps))

include hbeta hb in
theorem expectedValueSlope_lower {hi : ℝ} (hhi : hi<1) (hrho : density R c≤hi)
    (heps : eps≤(1-hi)*kappa/(16*(n:ℝ)))
    (z : ℝ) (hz : z∈Icc (U.B-eps) (U.B+eps)) :
    valueSlopeFloor n kappa w0 hi≤U.expectedValueSlope nu beta z := by
  have hR : 0<R := by have:=U.c_pos; have:=U.c_le; omega
  have hRreal : (0:ℝ)<R := by exact_mod_cast hR
  have hcreal : (1:ℝ)≤c := by exact_mod_cast U.c_pos
  have hcRreal : (c:ℝ)≤R := by exact_mod_cast U.c_le
  have hBw : U.B<w0 := (referenceBid_pos_lt U.n_ge hRreal hcreal hcRreal U.w_pos).2
  have hupper : U.B+eps≤2*w0 := by linarith [U.eps_small,U.bid_floor,U.w_pos]
  have hrow (omega : Fin R→U.valueBand) : valueSlopeFloor n kappa w0 hi≤
      finiteRowScore n c beta 1 z omega-finiteRowScore n c beta 0 z omega := by
    have hbox:=U.row_box beta hb z hz omega
    have hbox' : rowBids beta z omega∈bidBox (kappa/2) (2*w0) := fun i=>
      ⟨U.lower_floor.trans (hbox i).1,(hbox i).2.trans hupper⟩
    have hp:=U.interior _ hbox
    have hvel:=finiteRowVelocity_lower U.n_ge hR (half_pos U.kappa_pos) (by linarith [U.w_pos]) beta z omega hbox' hp
    have hpupper:=U.marginal_upper hhi hrho heps _ hbox 0
    have hpow : (1-(1+hi)/2)^(n-1)≤(1-finiteRowMarginal n c beta z omega)^(n-1) := by
      apply pow_le_pow_left₀ (by linarith : 0≤1-(1+hi)/2)
      exact sub_le_sub_left hpupper 1
    have he : finiteRowScore n c beta 1 z omega-finiteRowScore n c beta 0 z omega=
        (n:ℝ)*(1-finiteRowMarginal n c beta z omega)^(n-1)*finiteRowVelocity n c beta z omega := by
      dsimp [finiteRowScore]
      ring
    rw [he]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg n)) hvel
      (by unfold velocityFloor; have hk:=U.kappa_pos; have hw:=U.w_pos; positivity)
      (mul_nonneg (Nat.cast_nonneg n) (pow_nonneg (sub_nonneg.mpr (hp 0).2.le) _))
  have hh:=integral_mono (μ:=Measure.pi (fun _ : Fin R=>nu))
    (integrable_const (valueSlopeFloor n kappa w0 hi))
    ((U.row_integrable nu beta hbeta hb 1 z hz).sub (U.row_integrable nu beta hbeta hb 0 z hz)) hrow
  simp only [Pi.sub_apply] at hh
  rw [integral_sub (U.row_integrable nu beta hbeta hb 1 z hz) (U.row_integrable nu beta hbeta hb 0 z hz)] at hh
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul,expectedValueSlope,finiteExpectedScore] using hh

theorem deriv_smoothReply_bounds {hi M : ℝ} (hhi : hi<1) (hM : 0<M)
    (hrho : density R c≤hi) (heps : eps≤(1-hi)*kappa/(16*(n:ℝ))) (hA : U.A≤M)
    (w : ℝ) (hw : w∈U.openValueBand) :
    valueSlopeFloor n kappa w0 hi/(M+kappa/3)≤deriv (U.smoothReply nu beta hbeta hb) w ∧
      deriv (U.smoothReply nu beta hbeta hb) w≤U.typeRate/(2*kappa/3) := by
  let z:=U.smoothReply nu beta hbeta hb w
  let D := -fderiv ℝ (U.expectedJointScore nu beta) (w,z) (0,1)
  have hz:=U.smoothReply_mem nu beta hbeta hb w hw
  have hVlo:=U.expectedValueSlope_lower nu beta hbeta hb hhi hrho heps z ⟨hz.1.le,hz.2.le⟩
  have hVhi:=U.expectedValueSlope_le nu beta hbeta hb z ⟨hz.1.le,hz.2.le⟩
  have hDlo : 2*kappa/3≤D := by
    have hh:=U.own_partial_negative nu beta hbeta hb w z hw hz
    dsimp [D]
    linarith [U.curvature_floor]
  have hDpos : 0<D := lt_of_lt_of_le (by linarith [U.kappa_pos]) hDlo
  have hDhi : D≤M+kappa/3 := by
    have hh:=U.own_partial_abs_le nu beta hbeta hb w z hw hz
    exact (neg_le_abs _).trans (hh.trans (by linarith))
  have hmax : 0<M+kappa/3 := add_pos hM (div_pos U.kappa_pos (by norm_num))
  have hmin : 0<2*kappa/3 := by linarith [U.kappa_pos]
  rw [U.deriv_smoothReply_eq nu beta hbeta hb w hw]
  change valueSlopeFloor n kappa w0 hi/(M+kappa/3)≤U.expectedValueSlope nu beta z/D ∧
    U.expectedValueSlope nu beta z/D≤U.typeRate/(2*kappa/3)
  constructor
  · apply (div_le_div_iff₀ hmax hDpos).mpr
    exact (mul_le_mul_of_nonneg_left hDhi
      (valueSlopeFloor_pos U.n_ge U.kappa_pos U.w_pos hhi).le).trans
      (mul_le_mul_of_nonneg_right hVlo hmax.le)
  · apply (div_le_div_iff₀ hDpos hmin).mpr
    exact (mul_le_mul_of_nonneg_right hVhi hmin.le).trans
      (mul_le_mul_of_nonneg_left hDlo U.typeRate_nonneg)

end FiniteScoreControl
end FCAppendix.Existence.NarrowPayOnce
