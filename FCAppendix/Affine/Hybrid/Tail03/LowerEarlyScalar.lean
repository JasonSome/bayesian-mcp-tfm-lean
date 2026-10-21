import FCAppendix.Affine.Hybrid.Tail03.EarlySourceAdapter
import FCAppendix.Affine.Tail04.CoefficientOneFloorSource

noncomputable section
namespace FCAppendix.Affine.Hybrid.Tail03.LowerEarlyScalar
open Set
open EarlySourceAdapter
open FCAppendix.Affine.Tail04

variable {eta1 eta2 : ℝ} (p : Parameters eta1 eta2)

lemma source_multiplier :
    CoefficientOne.SourceFloor.multiplier (values p) p.center.eta1 =
      lowerLambda (xiOne p.center) (oneMixedMass p.center) := by
  have hx := xiOne_pos p.center
  have hx1 := xiOne_lt_half p.center
  have he := p.lowerGuards.mixed_pos
  have he1 := p.lowerGuards.mixed_half.trans (by norm_num : (1/2:ℝ) < 1)
  rw [←lower_phi_identity hx hx1 he he1]
  change 2*(1-(3/5:ℝ))/(1+(1-oneMixedMass p.center)*xiOne p.center/
    (2*oneMixedMass p.center*(lowerH (xiOne p.center))^2)) = _
  unfold phi
  rw [show 1-(1-oneMixedMass p.center)=oneMixedMass p.center by ring]
  dsimp only [lowerH]
  ring

lemma harmonic_pos : 0 < lowerH (xiOne p.center)*p.lowerGuards.L :=
  mul_pos (by linarith [(lowerH_bounds (xiOne_pos p.center) (xiOne_lt_half p.center)).1])
    p.lowerGuards.L_pos

lemma harmonic_below_floor : lowerH (xiOne p.center)*p.lowerGuards.L < p.lowerGuards.floor := by
  have hH := lowerH_bounds (xiOne_pos p.center) (xiOne_lt_half p.center)
  have hL := p.lowerGuards.L_pos
  have hbox := p.lowerGuards.box_strict
  have hfloor := p.lowerGuards.floor_order
  have hHL : lowerH (xiOne p.center)*p.lowerGuards.L < p.lowerGuards.L := by nlinarith
  exact hHL.trans (hbox.trans hfloor)

lemma floor_below_upper : p.lowerGuards.floor < bulkValue p.center-p.valueWidth := by
  have hH0 : 0 < lowerH (xiOne p.center) := by
    linarith [(lowerH_bounds (xiOne_pos p.center) (xiOne_lt_half p.center)).1]
  have hlo := p.lowerGuards.upper (lowerH (xiOne p.center)*p.lowerGuards.L)
    ⟨le_rfl,mul_le_mul_of_nonneg_left p.lowerGuards.box_strict.le hH0.le⟩
  linarith [hlo.private_one_gap,hlo.threshold_pos]

def scalar : CoefficientOne.ScalarInput (values p) :=
  CoefficientOne.SourceFloor.scalarInput (values p) p.center.eta1 (xi p.center)
    p.lowerGuards.U p.lowerGuards.floor (lowerH (xiOne p.center)*p.lowerGuards.L)
    (lowerRelativeMargin (xiOne p.center))
    p.center.eta1_pos (by linarith [p.center.eta12,p.center.eta2_lt_one])
    (xi_pos p.center) (p.lowerGuards.L_pos.trans p.lowerGuards.box_strict)
    p.lowerGuards.floor_order (floor_below_upper p) (harmonic_pos p)
    (harmonic_below_floor p)
    (lowerRelativeMargin_pos (xiOne_pos p.center) (xiOne_lt_half p.center))
    (by rw [source_multiplier p];exact p.lowerGuards.floor_twice)
    p.lowerGuards.relative_floor rfl p.theta_lower_floor

lemma scalar_xi : (scalar p).xi = xiOne p.center := rfl
lemma scalar_owner : (scalar p).ownerMass = oneOwnerMass p.center := rfl
lemma scalar_mixed : (scalar p).mixedMass = oneMixedMass p.center := rfl

end FCAppendix.Affine.Hybrid.Tail03.LowerEarlyScalar
