import FCAppendix.Affine.Tail04.SourceMenuPopulation
import FCAppendix.Affine.Tail04.SourceMenuError

noncomputable section
namespace FCAppendix.Affine.Tail04.UnusedMomentGeometry
open Set
open OriginalValues SourceMenuPopulation SourceMenuError SourceMomentRectangle

lemma centerMoment_le_half (P : ValueParameters) (reg : Bool) : centerMoment P reg≤1/2 := by
  have hθ : P.theta^2<1/100 := by nlinarith [P.theta_pos,P.theta_small]
  cases reg <;>
    norm_num [centerMoment,Central.mixedA,Central.mixedR,Central.h] <;> nlinarith

theorem exclusive_room (P : ValueParameters) {ξ hm M : ℝ}
    (hξ : 0< ξ) (hξh : ξ<1/2) (reg : Bool)
    (hhm : hm≤ Central.mixedR (P.theta^2)/1000)
    (hM : |M-centerMoment P reg|≤ ξ*centerMoment P reg/1000) :
    4*radius ξ (centerMoment P reg)≤ activeMass P.theta-hm-M := by
  have hθ : P.theta^2<1/100 := by nlinarith [P.theta_pos,P.theta_small]
  have ha : 66/100≤ activeMass P.theta := by unfold activeMass delta;nlinarith
  have hc0:=centerMoment_pos P reg
  have hc1:=centerMoment_le_half P reg
  have hR : Central.mixedR (P.theta^2)≤1/2 := centerMoment_le_half P true
  have hprod : ξ*centerMoment P reg≤1/4 := by nlinarith [mul_nonneg hξ.le hc0.le]
  have hMhi:=(abs_le.mp hM).2
  unfold radius γ
  nlinarith

theorem multiplier_ceiling (P : ValueParameters) {ξ M W : ℝ}
    (hξ : 0< ξ) (hξh : ξ<1/2) (reg : Bool)
    (hM : |M-centerMoment P reg|≤ ξ*centerMoment P reg/1000)
    (hW : |W-centerMoment P reg|≤ ξ*centerMoment P reg/1000) :
    meanNumerator P ξ M reg/W+γ ξ≤1-ξ/2-ξ/4 := by
  have hc:=centerMoment_pos P reg
  cases reg
  · have he:=accept_center P ξ
    change 0<Central.mixedA (P.theta^2) at hc
    have hn:=central_ratio_bounds ⟨hξ.le,hξh.le⟩
      (by norm_num : (19/20:ℝ)∈Icc (0:ℝ) 1) hc
      (he.trans (by unfold Central.lamA;ring))
    have hr:=moment_ratio ⟨hξ.le,hξh.le⟩ hc hM hW hn
    rw [he] at hr
    simp only [meanNumerator,Bool.false_eq_true,if_false]
    unfold Central.lamA γ at *
    linarith [(abs_le.mp hr).2]
  · have he:=reject_center P ξ
    change 0<Central.mixedR (P.theta^2) at hc
    have hn:=central_ratio_bounds ⟨hξ.le,hξh.le⟩
      (by norm_num : (9/10:ℝ)∈Icc (0:ℝ) 1) hc
      (he.trans (by unfold Central.lamR;ring))
    have hr:=moment_ratio ⟨hξ.le,hξh.le⟩ hc hM hW hn
    rw [he] at hr
    simp only [meanNumerator,if_true]
    unfold Central.lamR γ at *
    linarith [(abs_le.mp hr).2]

end FCAppendix.Affine.Tail04.UnusedMomentGeometry
