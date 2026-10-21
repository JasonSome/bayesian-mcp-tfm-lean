import FCAppendix.Existence.NarrowPayOnceOpenReply

noncomputable section
namespace FCAppendix.Existence.NarrowPayOnce
open Set Filter Topology MeasureTheory
open scoped ContDiff NNReal

private theorem realLinear_isInvertible (L : ℝ→L[ℝ] ℝ) (hL : L 1≠0) : L.IsInvertible := by
  have he (x : ℝ) : L x=x*L 1 := by
    calc
      _=L (x • (1:ℝ)) := by rw [smul_eq_mul,mul_one]
      _=x • L 1 := L.map_smul x 1
      _=_ := rfl
  have hi : Function.Injective L := by
    intro x y hxy
    rw [he x,he y] at hxy
    exact mul_right_cancel₀ hL hxy
  have hs := LinearMap.surjective_of_injective (f:=L.toLinearMap) hi
  let e := ContinuousLinearEquiv.ofBijective L (LinearMap.ker_eq_bot.mpr hi) (LinearMap.range_eq_top.mpr hs)
  refine ⟨e,?_⟩
  exact rfl

namespace FiniteScoreControl
variable {n R c : ℕ} {w0 kappa eps delta : ℝ}
  (U : FiniteScoreControl n R c w0 kappa eps delta)
  (nu : Measure U.valueBand) [IsProbabilityMeasure nu]
  (beta : U.valueBand→ℝ) (hbeta : Continuous beta)
  (hb : ∀v,beta v∈Icc (U.B-eps) (U.B+eps))

def smoothReply (w : ℝ) : ℝ :=
  if hw : w∈U.openValueBand then (U.openScoreData nu beta hbeta hb).reply Unit.unit ⟨w,hw⟩ else 0

theorem smoothReply_mem (w : ℝ) (hw : w∈U.openValueBand) :
    U.smoothReply nu beta hbeta hb w∈Ioo (U.B-eps) (U.B+eps) := by
  simp only [smoothReply,dif_pos hw]
  exact (U.openScoreData nu beta hbeta hb).reply_mem _ _

theorem score_smoothReply (w : ℝ) (hw : w∈U.openValueBand) :
    U.expectedJointScore nu beta (w,U.smoothReply nu beta hbeta hb w)=0 := by
  simp only [smoothReply,dif_pos hw]
  change finiteExpectedScore (R:=R) n c nu beta w ((U.openScoreData nu beta hbeta hb).reply Unit.unit ⟨w,hw⟩)=0
  exact (U.openScoreData nu beta hbeta hb).score_reply Unit.unit ⟨w,hw⟩

theorem continuousOn_smoothReply : ContinuousOn (U.smoothReply nu beta hbeta hb) U.openValueBand := by
  let D := U.openScoreData nu beta hbeta hb
  let M := U.A-kappa/3
  have hM : 0<M := D.curvature_pos
  let L : ℝ≥0 := ⟨U.typeRate/M,div_nonneg U.typeRate_nonneg hM.le⟩
  have hL : ∀v w z,z∈Icc (U.B-eps) (U.B+eps) →
      |D.score Unit.unit v z-D.score Unit.unit w z|≤M*(L:ℝ)*dist v w := by
    intro v w z hz
    have he : M*(L:ℝ)=U.typeRate := by
      change M*(U.typeRate/M)=U.typeRate
      rw [mul_comm]
      exact div_mul_cancel₀ _ hM.ne'
    rw [he,Subtype.dist_eq,Real.dist_eq]
    exact U.expected_type_bound nu beta hbeta hb v w z hz
  have hc := (D.reply_lipschitz_type Unit.unit L hL).continuous
  rw [continuousOn_iff_continuous_restrict]
  have he : U.openValueBand.restrict (U.smoothReply nu beta hbeta hb)=D.reply Unit.unit := by
    funext w
    exact dif_pos w.property
  rw [he]
  exact hc

include hbeta hb

theorem own_partial_negative (w z : ℝ) (hw : w∈U.openValueBand)
    (hz : z∈Ioo (U.B-eps) (U.B+eps)) :
    fderiv ℝ (U.expectedJointScore nu beta) (w,z) (0,1)≤ -(U.A-kappa/3) := by
  let F := U.expectedJointScore nu beta
  let M := U.A-kappa/3
  have hdF := (U.contDiffAt_expectedJointScore nu beta hbeta hb (w,z) hz).differentiableAt (by norm_num)
  have hcurve : HasDerivAt (fun x : ℝ=>(w,x)) ((0,1):ℝ×ℝ) z :=
    (hasDerivAt_const z w).prodMk (hasDerivAt_id z)
  have hd := hdF.hasFDerivAt.comp_hasDerivAt z hcurve
  have ha : AntitoneOn (fun x=>F (w,x)+M*x) (Icc (U.B-eps) (U.B+eps)) := by
    intro x hx y hy hxy
    have hh := U.expected_open_decrease nu beta hbeta hb ⟨w,hw⟩ x y hx hy hxy
    change M*(y-x)≤F (w,x)-F (w,y) at hh
    linarith
  have hsum' : HasDerivAt (fun x=>F (w,x)+M*x)
      (fderiv ℝ F (w,z) (0,1)+M) z := by
    convert hd.add ((hasDerivAt_id z).const_mul M) using 1 <;> first | rfl | simp only [mul_one,F]
  have hh := ha.derivWithin_nonpos (x:=z)
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds hz.1 hz.2),hsum'.deriv] at hh
  change fderiv ℝ F (w,z) (0,1)≤ -M
  linarith

theorem contDiffAt_smoothReply (w : ℝ) (hw : w∈U.openValueBand) :
    ContDiffAt ℝ 1 (U.smoothReply nu beta hbeta hb) w := by
  let f := U.smoothReply nu beta hbeta hb
  let F := U.expectedJointScore nu beta
  let z := f w
  have hz := U.smoothReply_mem nu beta hbeta hb w hw
  have hF : ContDiffAt ℝ 1 F (w,z) := U.contDiffAt_expectedJointScore nu beta hbeta hb (w,z) hz
  have hM : 0<U.A-kappa/3 := (U.openScoreData nu beta hbeta hb).curvature_pos
  have hpartial : (fderiv ℝ F (w,z) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ) (1:ℝ)≠0 := by
    have hh := U.own_partial_negative nu beta hbeta hb w z hw hz
    change fderiv ℝ F (w,z) (0,1)≠0
    linarith
  have hinv : (fderiv ℝ F (w,z) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible :=
    realLinear_isInvertible _ hpartial
  let psi := hF.implicitFunction (by norm_num) hinv
  have hpsi : ContDiffAt ℝ 1 psi w := hF.contDiffAt_implicitFunction (by norm_num) hinv
  have heq : ∀ᶠ t in 𝓝 (w,z),F t=F (w,z) ↔ psi t.1=t.2 :=
    hF.eventually_apply_eq_iff_implicitFunction (by norm_num) hinv
  have hopen : IsOpen U.openValueBand := isOpen_Ioo
  have hf : ContinuousAt f w := (U.continuousOn_smoothReply nu beta hbeta hb).continuousAt (hopen.mem_nhds hw)
  have hpair : Tendsto (fun x : ℝ=>(x,f x)) (𝓝 w) (𝓝 (w,z)) := continuousAt_id.prodMk hf
  apply hpsi.congr_of_eventuallyEq
  filter_upwards [hpair.eventually heq,hopen.mem_nhds hw] with x hx hxs
  apply (hx.mp ?_).symm
  change U.expectedJointScore nu beta (x,U.smoothReply nu beta hbeta hb x)=
    U.expectedJointScore nu beta (w,U.smoothReply nu beta hbeta hb w)
  rw [U.score_smoothReply nu beta hbeta hb x hxs,U.score_smoothReply nu beta hbeta hb w hw]

theorem smoothReply_eq_stationary
    (hroot : ∀v : U.valueBand,finiteExpectedScore (R:=R) n c nu beta v (beta v)=0)
    (v : U.valueBand) : U.smoothReply nu beta hbeta hb v=beta v := by
  have hv : (v:ℝ)∈U.openValueBand := ⟨by linarith [v.property.1,U.extensionWidth_pos],
    by linarith [v.property.2,U.extensionWidth_pos]⟩
  simp only [smoothReply,dif_pos hv]
  exact ((U.openScoreData nu beta hbeta hb).root_unique Unit.unit ⟨v,hv⟩ (hb v) (hroot v)).symm

end FiniteScoreControl
end FCAppendix.Existence.NarrowPayOnce
