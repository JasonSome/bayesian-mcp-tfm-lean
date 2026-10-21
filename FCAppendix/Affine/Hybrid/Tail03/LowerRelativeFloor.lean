import FCAppendix.Affine.Hybrid.Tail03.LowerAlgebra

noncomputable section
namespace FCAppendix.Affine.Hybrid.Tail03
open Set

def lowerRelativeMargin (x : ℝ) : ℝ :=
  (1-(1-x)*lowerFloorFactor x)/(4*lowerFloorFactor x)

lemma lowerRelativeMargin_pos {x : ℝ} (hx : 0 < x) (hx1 : x < 1/2) :
    0 < lowerRelativeMargin x := by
  have hf := lower_floor_between hx hx1
  have hk : 0 < 1-x := by linarith
  have hbound : lowerFloorFactor x < 1/(1-x) :=
    hf.2.2.1
  have hprod : (1-x)*lowerFloorFactor x < 1 := by
    have hh := (lt_div_iff₀ hk).mp hbound
    simpa only [mul_comm] using hh
  have hfpos : 0 < lowerFloorFactor x := hf.1
  exact div_pos (sub_pos.mpr hprod) (mul_pos (by norm_num) hfpos)

lemma lowerRelativeMargin_identity {x : ℝ} (hx : 0 < x) (hx1 : x < 1/2) :
    ((1-x)+lowerRelativeMargin x)*lowerFloorFactor x =
      1-(3/4)*(1-(1-x)*lowerFloorFactor x) := by
  have hfpos := (lower_floor_between hx hx1).1
  unfold lowerRelativeMargin
  field_simp [hfpos.ne']
  ring

end FCAppendix.Affine.Hybrid.Tail03
