import FCAppendix.Affine.Uniform06.EntryMomentAlgebra
set_option autoImplicit false

noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryOptimizer
open FCAppendix.Affine.Uniform06.EntryMomentAlgebra

def oneRoutePayoff (v b q : ℝ) : ℝ := (v - b) * q

def twoRoutePayoff (η v b q r : ℝ) : ℝ :=
  2 * (v - b) * q - ((v - b) + η * b) * r

theorem twoRoute_minus_oneRoute (η v b q r : ℝ) :
    twoRoutePayoff η v b q r - oneRoutePayoff v b q =
      oneRoutePayoff v b q - ((v - b) + η * b) * r := by
  unfold twoRoutePayoff oneRoutePayoff
  ring

theorem optimizer_routeGap_identity
    (η v b q dq r c : ℝ)
    (hstation : q = (v - b) * dq) :
    q * (twoRoutePayoff η v b q r -
           (1 + c) * oneRoutePayoff v b q) =
      (v - b) * (routeGap η b q dq r - c * q ^ 2) := by
  unfold twoRoutePayoff oneRoutePayoff routeGap
  calc
    q * (2 * (v - b) * q - ((v - b) + η * b) * r -
        (1 + c) * ((v - b) * q)) =
      (v - b) * (q ^ 2 - (q + η * b * dq) * r - c * q ^ 2) +
       η * b * r * ((v - b) * dq - q) := by ring
    _ = _ := by rw [← hstation]; ring

theorem optimizer_twoRoute_margin
    {η v b q dq r c : ℝ}
    (hv : b ≤ v) (hq : 0 < q)
    (hstation : q = (v - b) * dq)
    (hgap : c * q ^ 2 ≤ routeGap η b q dq r) :
    (1 + c) * oneRoutePayoff v b q ≤
      twoRoutePayoff η v b q r := by
  have hident := optimizer_routeGap_identity η v b q dq r c hstation
  have hnon : 0 ≤ q * (twoRoutePayoff η v b q r -
      (1 + c) * oneRoutePayoff v b q) := by
    rw [hident]
    exact mul_nonneg (sub_nonneg.mpr hv) (sub_nonneg.mpr hgap)
  by_contra hnot
  have hneg : twoRoutePayoff η v b q r -
        (1 + c) * oneRoutePayoff v b q < 0 := by linarith
  have hprod : q * (twoRoutePayoff η v b q r -
      (1 + c) * oneRoutePayoff v b q) < 0 := mul_neg_of_pos_of_neg hq hneg
  linarith

theorem restore_exceptional_states
    {Bid : Type*} (u1G u1 u2G u2 : Bid → ℝ) (bStar : Bid)
    {c ε : ℝ}
    (hopt : ∀ b, u1G b ≤ u1G bStar)
    (hmargin : (1 + c) * u1G bStar ≤ u2G bStar)
    (hone : ∀ b, |u1 b - u1G b| ≤ ε)
    (htwo : |u2 bStar - u2G bStar| ≤ ε) :
    ∀ b, c * u1G bStar - 2 * ε ≤ u2 bStar - u1 b := by
  intro b
  have h1 := (abs_le.mp (hone b)).2
  have h2 := (abs_le.mp htwo).1
  have hoptb := hopt b
  linarith

theorem restore_strict_twoRoute
    {Bid : Type*} (u1G u1 u2G u2 : Bid → ℝ) (bStar : Bid)
    {c ε : ℝ}
    (hopt : ∀ b, u1G b ≤ u1G bStar)
    (hmargin : (1 + c) * u1G bStar ≤ u2G bStar)
    (hone : ∀ b, |u1 b - u1G b| ≤ ε)
    (htwo : |u2 bStar - u2G bStar| ≤ ε)
    (hstrict : 2 * ε < c * u1G bStar) :
    ∀ b, u1 b < u2 bStar := by
  intro b
  have h := restore_exceptional_states u1G u1 u2G u2 bStar
    hopt hmargin hone htwo b
  linarith

theorem singleton_FOC_of_localMax (q : ℝ → ℝ) (v b dq : ℝ)
    (hd : HasDerivAt q dq b)
    (hmax : IsLocalMax (fun t => (v-t)*q t) b) : q b=(v-b)*dq := by
  have hlin : HasDerivAt (fun t : ℝ => v-t) (-1) b := by
    convert! (hasDerivAt_id b).const_sub v using 1
  have hp := hlin.mul hd
  have hz := hmax.hasDerivAt_eq_zero hp
  nlinarith

end FCAppendix.Affine.Uniform06.EntryOptimizer
