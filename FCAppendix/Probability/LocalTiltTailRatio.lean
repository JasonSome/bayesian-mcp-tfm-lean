import FCAppendix.Probability.BoundedTiltTailRatio

namespace FCAppendix.ExponentialTilt
open PayOnce.GaussianTilt

theorem one_add_mul_ratio_le_max {A B t : ℝ} (hB : 0 < B) (ht : 0 ≤ t) :
    (1+A*t)/(1+B*t) ≤ max 1 (A/B) := by
  have hAB : A ≤ max 1 (A/B)*B := (div_le_iff₀ hB).mp (le_max_right _ _)
  apply (div_le_iff₀ (show 0 < 1+B*t by positivity)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hAB ht, le_max_left (1:ℝ) (A/B)]

theorem local_tilt_prefactor_ratio_le {u w d z Cu cw SX sYmin sX sY : ℝ} {N : ℕ}
    (hd : 0 < d) (hz : 0 ≤ z) (hCu : 0 < Cu) (hcw : 0 < cw)
    (hSX : 0 < SX) (hsYmin : 0 < sYmin) (hsX : 0 ≤ sX)
    (hu : |u| ≤ Cu*d) (hw : cw*(d+z) ≤ |w|)
    (hsXupper : sX ≤ SX*Real.sqrt N) (hsYlower : sYmin*Real.sqrt N ≤ sY) :
    (1+|u| *sX)/(1+|w| *sY) ≤ max 1 ((Cu*SX)/(cw*sYmin)) := by
  have hroot := Real.sqrt_nonneg (N:ℝ)
  have hsY : 0 ≤ sY := (mul_nonneg hsYmin.le hroot).trans hsYlower
  have hU : |u| *sX ≤ (Cu*SX)*(d*Real.sqrt N) := by
    calc
      _ ≤ (Cu*d)*(SX*Real.sqrt N) := mul_le_mul hu hsXupper hsX (by positivity)
      _ = _ := by ring
  have hW : (cw*sYmin)*(d*Real.sqrt N) ≤ |w| *sY := by
    have hwd : cw*d ≤ |w| := (mul_le_mul_of_nonneg_left (by linarith : d ≤ d+z) hcw.le).trans hw
    calc
      _ = (cw*d)*(sYmin*Real.sqrt N) := by ring
      _ ≤ |w| *sY := mul_le_mul hwd hsYlower (by positivity) (abs_nonneg _)
  calc
    _ ≤ (1+(Cu*SX)*(d*Real.sqrt N))/(1+(cw*sYmin)*(d*Real.sqrt N)) :=
      div_le_div₀ (by positivity) (by linarith) (by positivity) (by linarith)
    _ ≤ max 1 ((Cu*SX)/(cw*sYmin)) :=
      one_add_mul_ratio_le_max (by positivity) (by positivity)

theorem local_tilt_rate_exp_le {a u d z cu cg G r q : ℝ} {N : ℕ}
    (hz : 0 ≤ z) (hcg : 0 < cg)
    (hu : cu*d ≤ |u|) (hG : cg*z ≤ G) (hrq : 0 ≤ r-q) :
    Real.exp (-(N:ℝ)*(Real.exp (-a)*|u| *G+|u| *(r-q))) ≤
      Real.exp (-(N:ℝ)*Real.exp (-a)*cu*cg*d*z) := by
  have hp := mul_le_mul hu hG (mul_nonneg hcg.le hz) (abs_nonneg u)
  have hp' := mul_le_mul_of_nonneg_left hp (Real.exp_pos (-a)).le
  have hrate : Real.exp (-a)*cu*cg*d*z ≤ Real.exp (-a)*|u| *G+|u| *(r-q) := by
    nlinarith [mul_nonneg (abs_nonneg u) hrq]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hrate (Nat.cast_nonneg N : (0:ℝ) ≤ N)
  nlinarith

theorem tail_ratio_le_local_exponential
    {F₀ Fs a u w d z cu Cu cw cg SX sYmin sX sY G r q : ℝ} {N : ℕ}
    (hd : 0 < d) (hz : 0 ≤ z) (_hcu : 0 < cu) (hCu : 0 < Cu)
    (hcw : 0 < cw) (hcg : 0 < cg) (hSX : 0 < SX) (hsYmin : 0 < sYmin)
    (hsX : 0 ≤ sX) (hulower : cu*d ≤ |u|) (huupper : |u| ≤ Cu*d)
    (hwlower : cw*(d+z) ≤ |w|)
    (hsXupper : sX ≤ SX*Real.sqrt N) (hsYlower : sYmin*Real.sqrt N ≤ sY)
    (hG : cg*z ≤ G) (hrq : 0 ≤ r-q)
    (hratio : Fs/F₀ ≤ (3*upperConstant/lowerConstant)*((1+|u| *sX)/(1+|w| *sY))*
      Real.exp (-(N:ℝ)*(Real.exp (-a)*|u| *G+|u| *(r-q)))) :
    Fs/F₀ ≤ (3*upperConstant/lowerConstant)*max 1 ((Cu*SX)/(cw*sYmin))*
      Real.exp (-(N:ℝ)*Real.exp (-a)*cu*cg*d*z) := by
  have hp := local_tilt_prefactor_ratio_le hd hz hCu hcw hSX hsYmin hsX huupper
    hwlower hsXupper hsYlower
  have he := local_tilt_rate_exp_le (a := a) (N := N) hz hcg hulower hG hrq
  have hK : 0 ≤ 3*upperConstant/lowerConstant := by
    exact div_nonneg (mul_nonneg (by norm_num) upperConstant_pos.le) lowerConstant_pos.le
  apply hratio.trans
  exact mul_le_mul (mul_le_mul_of_nonneg_left hp hK) he (Real.exp_pos _).le
    (mul_nonneg hK (le_trans (by norm_num) (le_max_left _ _)))

end FCAppendix.ExponentialTilt
