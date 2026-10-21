import FCAppendix.Affine.Uniform07.ExactIntegral
namespace FCAppendix.Affine.Uniform07
open MeasureTheory Set
noncomputable def normalizedBid (i : Row) (y : ℝ) : ℝ :=
  if y ≤ x i then y else x i*y/(kappa i*y+xi i*x i)

noncomputable def normalizedAcceptance (i : Row) (z y : ℝ) : ℝ :=
  if y ≤ z then 0 else if y ≤ x i then pieceP (1/xi i) (z/xi i) y
  else pieceP ((1-z*kappa i/x i)/xi i) z y
noncomputable def laplace (i : Row) (theta z : ℝ) : ℝ :=
  (1-cutoff i)*Real.exp (-theta/2)+cutoff i*
    (z+pieceZ (1/xi i) (z/xi i) theta z (x i)+
      pieceZ ((1-z*kappa i/x i)/xi i) z theta (x i) 1)
noncomputable def tiltScore (i : Row) (theta z : ℝ) : ℝ :=
  (1-cutoff i)*(1/2-rho)*Real.exp (-theta/2)+cutoff i*
    (-rho*z+pieceF (1/xi i) (z/xi i) theta z (x i)+
      pieceF ((1-z*kappa i/x i)/xi i) z theta (x i) 1)
noncomputable def objective (i : Row) (theta z : ℝ) : ℝ :=
  -theta*rho-Real.log (laplace i theta z)
noncomputable def canonicalRate (i : Row) (z : ℝ) : ℝ :=
  sSup ((fun theta => objective i theta z) '' Ici 0)
noncomputable def pureParameter (i : Row) (z : ℝ) : ℝ := (1+cutoff i)/2-z*cutoff i
noncomputable def pureRate (i : Row) (z : ℝ) : ℝ :=
  rho*Real.log (rho/pureParameter i z)+(1-rho)*Real.log ((1-rho)/(1-pureParameter i z))
noncomputable def laplacePoly (n : ℕ) (i : Row) (theta z : ℝ) : ℝ :=
  (1-cutoff i)*expPoly n (-theta/2)+cutoff i*
    (z+pieceZPoly n (1/xi i) (z/xi i) theta z (x i)+
      pieceZPoly n ((1-z*kappa i/x i)/xi i) z theta (x i) 1)
noncomputable def tiltScorePoly (n : ℕ) (i : Row) (theta z : ℝ) : ℝ :=
  (1-cutoff i)*(1/2-rho)*expPoly n (-theta/2)+cutoff i*
    (-rho*z+pieceFPoly n (1/xi i) (z/xi i) theta z (x i)+
      pieceFPoly n ((1-z*kappa i/x i)/xi i) z theta (x i) 1)

theorem low_piece_bounds (i : Row) {z y : ℝ} (hz : 1/2 ≤ z)
    (hzy : z ≤ y) (hy : y ≤ x i) : pieceP (1/xi i) (z/xi i) y ∈ Icc 0 1 := by
  have hyp : 0 < y := by linarith
  have hxi := xi_pos i
  have hid : pieceP (1/xi i) (z/xi i) y = (y-z)/(xi i*y) := by
    unfold pieceP; field_simp
  rw [hid]
  constructor
  · exact div_nonneg (sub_nonneg.mpr hzy) (mul_nonneg hxi.le hyp.le)
  · rw [div_le_iff₀ (mul_pos hxi hyp)]
    cases i <;> norm_num [xi,xiQ,etaQ,x,xQ] at * <;> nlinarith

theorem high_piece_bounds (i : Row) {z y : ℝ} (hz : 1/2 ≤ z)
    (hzx : z ≤ x i) (hxy : x i ≤ y) (hy : y ≤ 1) :
    pieceP ((1-z*kappa i/x i)/xi i) z y ∈ Icc 0 1 := by
  have hxp : 0 < x i := by cases i <;> norm_num [x,xQ]
  have hyp : 0 < y := hxp.trans_le hxy
  have hxi := xi_pos i
  have hz0 : 0 ≤ z := by linarith
  have h1 : z/y ≤ z/x i := div_le_div_of_nonneg_left hz0 hxp hxy
  have h2 : z ≤ z/y := (le_div_iff₀ hyp).2 (by nlinarith)
  have hid : (1-z*kappa i/x i)/xi i-z/x i = (x i-z)/(xi i*x i) := by
    have hk : kappa i+xi i=1 := by cases i <;> norm_num [kappa,kappaQ,xi,xiQ,etaQ]
    field_simp; nlinarith
  have hn : 0 ≤ (1-z*kappa i/x i)/xi i-z/x i := by
    rw [hid]; exact div_nonneg (sub_nonneg.mpr hzx) (mul_nonneg hxi.le hxp.le)
  constructor
  · dsimp [pieceP]; linarith
  · dsimp [pieceP]
    cases i <;> norm_num [x,xQ,xi,xiQ,kappa,kappaQ,etaQ] at * <;> nlinarith

private theorem combine_error {t z x e u0 u1 u2 : ℝ}
    (ht : t ∈ Icc 0 1) (hz : 0 ≤ z) (_hzx : z ≤ x) (_hx : x ≤ 1)
    (he : 0 ≤ e) (h0 : |u0| ≤ e) (h1 : |u1| ≤ (x-z)*e) (h2 : |u2| ≤ (1-x)*e) :
    |(1-t)*u0+t*(u1+u2)| ≤ e := by
  calc
    _ ≤ |(1-t)*u0|+|t*(u1+u2)| := abs_add_le _ _
    _ ≤ (1-t)*e+t*((x-z)*e+(1-x)*e) := by
      rw [abs_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr ht.2),abs_of_nonneg ht.1]
      exact add_le_add (mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr ht.2))
        (mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add h1 h2)) ht.1)
    _ ≤ e := by nlinarith [mul_nonneg (mul_nonneg ht.1 hz) he]

theorem rate_integral_errors (n : ℕ) (i : Row) {theta z : ℝ}
    (ht : cutoff i ∈ Icc 0 1) (hz : 1/2 ≤ z) (hzx : z ≤ x i)
    (htheta : 0 ≤ theta) (hsmall : theta/(n+1:ℝ) ≤ 1/2) :
    |laplace i theta z-laplacePoly n i theta z| ≤ 2*theta^n/(n.factorial:ℝ) ∧
    |tiltScore i theta z-tiltScorePoly n i theta z| ≤ 2*theta^n/(n.factorial:ℝ) := by
  have hz0 : 0 < z := by linarith
  have hx0 : 0 < x i := hz0.trans_le hzx
  have hx1 : x i ≤ 1 := by cases i <;> norm_num [x,xQ]
  have h0 := expPoly_error n htheta (x := -theta/2)
    (by rw [abs_div,abs_neg,abs_of_nonneg htheta]; norm_num; linarith) hsmall
  have h1 := piece_errors n hz0 hzx htheta hsmall (fun y hy => low_piece_bounds i hz hy.1 hy.2)
  have h2 := piece_errors n hx0 hx1 htheta hsmall (fun y hy => high_piece_bounds i hz hzx hy.1 hy.2)
  have he : 0 ≤ 2*theta^n/(n.factorial:ℝ) := by positivity
  constructor
  · convert combine_error ht hz0.le hzx hx1 he h0 h1.1 h2.1 using 1
    dsimp [laplace,laplacePoly]
    congr 1
    ring
  · have h0' : |(1/2-rho)*(Real.exp (-theta/2)-expPoly n (-theta/2))| ≤
        2*theta^n/(n.factorial:ℝ) := by
      rw [abs_mul]
      have hw : |(1/2:ℝ)-rho| ≤ 1 := by norm_num [rho]
      simpa using mul_le_mul hw h0 (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    convert combine_error ht hz0.le hzx hx1 he h0' h1.2 h2.2 using 1
    dsimp [tiltScore,tiltScorePoly]
    congr 1
    ring

def laplacePolyBox (n : ℕ) (i : Row) (theta z : ℚ) (tb logz logx : Box) : Box :=
  Box.add (Box.scale (expPolyQ n (-theta/2)) (Box.sub (Box.point 1) tb))
    (Box.mul tb (Box.add (Box.add (Box.point z)
      (pieceZBox n (1/xiQ i) (z/xiQ i) theta z (xQ i) logz logx))
      (pieceZBox n ((1-z*kappaQ i/xQ i)/xiQ i) z theta (xQ i) 1 logx (Box.point 0))))
def tiltScorePolyBox (n : ℕ) (i : Row) (theta z : ℚ) (tb logz logx : Box) : Box :=
  Box.add (Box.scale ((1/2-999/2000)*expPolyQ n (-theta/2)) (Box.sub (Box.point 1) tb))
    (Box.mul tb (Box.add (Box.add (Box.point (-(999/2000)*z))
      (pieceFBox n (1/xiQ i) (z/xiQ i) theta z (xQ i) logz logx))
      (pieceFBox n ((1-z*kappaQ i/xQ i)/xiQ i) z theta (xQ i) 1 logx (Box.point 0))))

theorem laplacePolyBox_ok (n : ℕ) (i : Row) (theta z : ℚ) {tb logz logx : Box}
    (ht : tb.Holds (cutoff i)) (hlz : logz.Holds (Real.log (z:ℝ)))
    (hlx : logx.Holds (Real.log (x i))) :
    (laplacePolyBox n i theta z tb logz logx).Holds (laplacePoly n i theta z) := by
  have hlog1 : (Box.point 0).Holds (Real.log ((1:ℚ):ℝ)) := by norm_num [Box.Holds, Box.point]
  have h := Box.add_ok
    (Box.scale_ok (expPolyQ n (-theta/2)) (Box.sub_ok (Box.point_ok 1) ht))
    (Box.mul_ok ht (Box.add_ok (Box.add_ok (Box.point_ok z)
      (pieceZBox_ok n (1/xiQ i) (z/xiQ i) theta z (xQ i) hlz hlx))
      (pieceZBox_ok n ((1-z*kappaQ i/xQ i)/xiQ i) z theta (xQ i) 1 hlx hlog1)))
  simpa [laplacePoly,laplacePolyBox,xi,kappa,x,mul_comm] using h

theorem tiltScorePolyBox_ok (n : ℕ) (i : Row) (theta z : ℚ) {tb logz logx : Box}
    (ht : tb.Holds (cutoff i)) (hlz : logz.Holds (Real.log (z:ℝ)))
    (hlx : logx.Holds (Real.log (x i))) :
    (tiltScorePolyBox n i theta z tb logz logx).Holds (tiltScorePoly n i theta z) := by
  have hlog1 : (Box.point 0).Holds (Real.log ((1:ℚ):ℝ)) := by norm_num [Box.Holds, Box.point]
  have h := Box.add_ok
    (Box.scale_ok ((1/2-999/2000)*expPolyQ n (-theta/2)) (Box.sub_ok (Box.point_ok 1) ht))
    (Box.mul_ok ht (Box.add_ok (Box.add_ok (Box.point_ok (-(999/2000)*z))
      (pieceFBox_ok n (1/xiQ i) (z/xiQ i) theta z (xQ i) hlz hlx))
      (pieceFBox_ok n ((1-z*kappaQ i/xQ i)/xiQ i) z theta (xQ i) 1 hlx hlog1)))
  simpa [tiltScorePoly,tiltScorePolyBox,xi,kappa,x,rho,mul_assoc,mul_comm,mul_left_comm] using h
end FCAppendix.Affine.Uniform07
