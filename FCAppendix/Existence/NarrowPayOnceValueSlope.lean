import FCAppendix.Existence.NarrowPayOnceSmoothReply

noncomputable section
namespace FCAppendix.Existence.NarrowPayOnce
open Set Filter Topology MeasureTheory
open PayOnce PayOnce.OwnImpact CommonList
open scoped BigOperators

def velocityFloor (n : ℕ) (lower upper : ℝ) : ℝ :=
  let smin := 1/(upper*(n:ℝ))
  let smax := (n:ℝ)/lower
  smin/(n:ℝ)*(smin/(smax+smin))

theorem finiteRowVelocity_lower {R n c : ℕ} (hn : 2≤n) (hR : 0<R)
    {lower upper : ℝ} (hlower : 0<lower) (hupper : 0<upper)
    {V : Type*} (beta : V→ℝ) (z : ℝ) (omega : Fin R→V)
    (hb : rowBids beta z omega∈bidBox lower upper)
    (hp : ∀i,kernelMarginal n c (rowBids beta z omega) i∈Ioo (0:ℝ) 1) :
    velocityFloor n lower upper≤finiteRowVelocity n c beta z omega := by
  let b:=rowBids beta z omega
  let p:=kernelMarginal n c b
  let s:=fun i=>sensitivity n (b i) (p i)
  let smin:=1/(upper*(n:ℝ))
  let smax:=(n:ℝ)/lower
  let T:=∑i,s i
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hsmin : 0<smin := by dsimp [smin]; positivity
  have hsmax : 0<smax := by dsimp [smax]; positivity
  have hs (i : Fin (R+1)) : smin ≤ s i ∧ s i ≤ smax := by
    have hbp : 0<b i := hlower.trans_le (hb i).1
    have hsp := Hslope_pos hn ⟨(hp i).1.le,(hp i).2.le⟩
    have hbd := Hslope_bounds hn ⟨(hp i).1.le,(hp i).2.le⟩
    have hden : 0<b i*Hslope n (p i) := mul_pos hbp hsp
    constructor
    · apply one_div_le_one_div_of_le hden
      exact mul_le_mul (hb i).2 hbd.2 hsp.le hupper.le
    · change 1/(b i*Hslope n (p i))≤(n:ℝ)/lower
      apply (div_le_div_iff₀ hden hlower).mpr
      have hh := mul_le_mul_of_nonneg_left hbd.1 hbp.le
      change b i*(1/(n:ℝ))≤b i*Hslope n (p i) at hh
      have hhm := mul_le_mul_of_nonneg_right hh hnR.le
      have he : b i*(1/(n:ℝ))*(n:ℝ)=b i := by field_simp
      rw [he] at hhm
      rw [one_mul]
      nlinarith [(hb i).1]
  have hspos (i : Fin (R+1)) : 0<s i := hsmin.trans_le (hs i).1
  let j : Fin R:=⟨0,hR⟩
  have hsum : s 0+s j.succ≤T := by
    dsimp [T]
    rw [Fin.sum_univ_succ]
    gcongr
    exact Finset.single_le_sum (fun i _=>(hspos i.succ).le) (Finset.mem_univ j)
  have hT : 0<T := lt_of_lt_of_le (add_pos (hspos 0) (hspos j.succ)) hsum
  have hrest : smin≤T-s 0 := by linarith [(hs j.succ).1]
  have hcross : smin*T≤(smax+smin)*(T-s 0) := by
    have h1 := mul_le_mul_of_nonneg_left hrest hsmax.le
    have h2 := mul_le_mul_of_nonneg_left (hs 0).2 hsmin.le
    nlinarith
  have hfrac : smin/(smax+smin)≤1-s 0/T := by
    apply (div_le_iff₀ (add_pos hsmax hsmin)).mpr
    apply (le_of_mul_le_mul_right ?_ hT)
    have he : ((1-s 0/T)*(smax+smin))*T=(smax+smin)*(T-s 0) := by field_simp
    rw [he]
    nlinarith
  have hH := (H_bounds n (by omega) (p 0) (hp 0).1.le (hp 0).2.le).1
  change smin/(n:ℝ)*(smin/(smax+smin))≤ s 0*H n (p 0)*(1-s 0/T)
  have hfirst : smin/(n:ℝ)≤ s 0*H n (p 0) := by
    simpa only [div_eq_mul_inv,one_mul] using mul_le_mul (hs 0).1 hH (by positivity : 0≤1/(n:ℝ)) (hspos 0).le
  exact mul_le_mul hfirst hfrac (by positivity) (mul_nonneg (hspos 0).le (H_pos n (by omega) (p 0) (hp 0).1.le (hp 0).2.le).le)

namespace FiniteScoreControl
variable {n R c : ℕ} {w0 kappa eps delta : ℝ}
  (U : FiniteScoreControl n R c w0 kappa eps delta)
  (nu : Measure U.valueBand) [IsProbabilityMeasure nu]
  (beta : U.valueBand→ℝ) (hbeta : Continuous beta)
  (hb : ∀v,beta v∈Icc (U.B-eps) (U.B+eps))

def expectedValueSlope (z : ℝ) : ℝ :=
  finiteExpectedScore (R:=R) n c nu beta 1 z-finiteExpectedScore (R:=R) n c nu beta 0 z

include hbeta hb

theorem expected_score_affine_value (w z : ℝ) (hz : z∈Icc (U.B-eps) (U.B+eps)) :
    finiteExpectedScore (R:=R) n c nu beta w z=
      w*U.expectedValueSlope nu beta z+finiteExpectedScore (R:=R) n c nu beta 0 z := by
  have hrow (omega : Fin R→U.valueBand) : finiteRowScore n c beta w z omega=
      w*(finiteRowScore n c beta 1 z omega-finiteRowScore n c beta 0 z omega)+finiteRowScore n c beta 0 z omega := by
    dsimp [finiteRowScore]
    ring
  dsimp [finiteExpectedScore,expectedValueSlope]
  simp_rw [hrow]
  have hfg : Integrable (fun omega=>w*(finiteRowScore n c beta 1 z omega-finiteRowScore n c beta 0 z omega))
      (Measure.pi (fun _ : Fin R=>nu)) := by
    simpa only [Pi.sub_apply] using
      ((U.row_integrable nu beta hbeta hb 1 z hz).sub (U.row_integrable nu beta hbeta hb 0 z hz)).const_mul w
  rw [integral_add hfg (U.row_integrable nu beta hbeta hb 0 z hz),integral_const_mul,
    integral_sub (U.row_integrable nu beta hbeta hb 1 z hz) (U.row_integrable nu beta hbeta hb 0 z hz)]

theorem expectedValueSlope_pos (z : ℝ) (hz : z∈Icc (U.B-eps) (U.B+eps)) :
    0<U.expectedValueSlope nu beta z :=
  sub_pos.mpr (U.expected_strict_type nu beta hbeta hb 0 1 z zero_lt_one hz)

theorem expectedValueSlope_le (z : ℝ) (hz : z∈Icc (U.B-eps) (U.B+eps)) :
    U.expectedValueSlope nu beta z≤U.typeRate := by
  have hh:=U.expected_type_bound nu beta hbeta hb 1 0 z hz
  change |U.expectedValueSlope nu beta z|≤U.typeRate*|1-0| at hh
  simpa only [sub_zero,abs_one,mul_one,abs_of_pos (U.expectedValueSlope_pos nu beta hbeta hb z hz)] using hh

theorem value_partial_eq (w z : ℝ) (hz : z∈Ioo (U.B-eps) (U.B+eps)) :
    fderiv ℝ (U.expectedJointScore nu beta) (w,z) (1,0)=U.expectedValueSlope nu beta z := by
  have hdF := (U.contDiffAt_expectedJointScore nu beta hbeta hb (w,z) hz).differentiableAt (by norm_num)
  have hcurve : HasDerivAt (fun x : ℝ=>(x,z)) ((1,0):ℝ×ℝ) w :=
    (hasDerivAt_id w).prodMk (hasDerivAt_const w z)
  have hh := hdF.hasFDerivAt.comp_hasDerivAt w hcurve
  have he : (fun x=>U.expectedJointScore nu beta (x,z))=
      (fun x=>x*U.expectedValueSlope nu beta z+finiteExpectedScore (R:=R) n c nu beta 0 z) := by
    funext x
    exact U.expected_score_affine_value nu beta hbeta hb x z ⟨hz.1.le,hz.2.le⟩
  have hd : HasDerivAt (fun x=>U.expectedJointScore nu beta (x,z)) (U.expectedValueSlope nu beta z) w := by
    rw [he]
    convert (((hasDerivAt_id w).mul_const (U.expectedValueSlope nu beta z)).add_const
      (finiteExpectedScore (R:=R) n c nu beta 0 z)) using 1 <;> first | rfl | simp only [one_mul]
  exact hh.unique hd

theorem deriv_smoothReply_eq (w : ℝ) (hw : w∈U.openValueBand) :
    deriv (U.smoothReply nu beta hbeta hb) w=
      U.expectedValueSlope nu beta (U.smoothReply nu beta hbeta hb w)/
        (-fderiv ℝ (U.expectedJointScore nu beta)
          (w,U.smoothReply nu beta hbeta hb w) (0,1)) := by
  let f:=U.smoothReply nu beta hbeta hb
  let F:=U.expectedJointScore nu beta
  have hf := (U.contDiffAt_smoothReply nu beta hbeta hb w hw).differentiableAt (by norm_num)
  have hz := U.smoothReply_mem nu beta hbeta hb w hw
  have hF := (U.contDiffAt_expectedJointScore nu beta hbeta hb (w,f w) hz).differentiableAt (by norm_num)
  have hd:=hF.hasFDerivAt.comp_hasDerivAt w ((hasDerivAt_id w).prodMk hf.hasDerivAt)
  have hzero : (fun x=>F (x,f x))=ᶠ[𝓝 w] fun _=>0 := by
    filter_upwards [isOpen_Ioo.mem_nhds hw] with x hx
    exact U.score_smoothReply nu beta hbeta hb x hx
  have hconst := (hasDerivAt_const w (0:ℝ)).congr_of_eventuallyEq hzero
  have heq := hd.unique hconst
  have hlin : fderiv ℝ F (w,f w) (1,deriv f w)=
      fderiv ℝ F (w,f w) (1,0)+deriv f w*fderiv ℝ F (w,f w) (0,1) := by
    have hp : ((1,deriv f w):ℝ×ℝ)=(1,0)+deriv f w • (0,1) := by ext <;> simp
    rw [hp,map_add,map_smul]
    rfl
  rw [hlin,U.value_partial_eq nu beta hbeta hb w (f w) hz] at heq
  have hM : 0<U.A-kappa/3 := (U.openScoreData nu beta hbeta hb).curvature_pos
  have hneg := U.own_partial_negative nu beta hbeta hb w (f w) hw hz
  apply (eq_div_iff (by linarith : -fderiv ℝ F (w,f w) (0,1)≠0)).mpr
  change deriv f w * (-fderiv ℝ F (w,f w) (0,1))=_
  linarith

theorem deriv_smoothReply_pos (w : ℝ) (hw : w∈U.openValueBand) :
    0<deriv (U.smoothReply nu beta hbeta hb) w := by
  rw [U.deriv_smoothReply_eq nu beta hbeta hb w hw]
  have hz:=U.smoothReply_mem nu beta hbeta hb w hw
  have hp:=U.expectedValueSlope_pos nu beta hbeta hb _ ⟨hz.1.le,hz.2.le⟩
  have hm : 0<U.A-kappa/3 := (U.openScoreData nu beta hbeta hb).curvature_pos
  have hn:=U.own_partial_negative nu beta hbeta hb w _ hw hz
  exact div_pos hp (by linarith)

end FiniteScoreControl

end FCAppendix.Existence.NarrowPayOnce
