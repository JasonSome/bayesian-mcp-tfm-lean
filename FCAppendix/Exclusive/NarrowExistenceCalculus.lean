import FCAppendix.Exclusive.NarrowCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section
namespace FCAppendix.Exclusive.Narrow.Existence
open Finset
open scoped BigOperators

def logShare (r W z : ℝ) : ℝ := Real.exp (-r*z) / (W + Real.exp (-r*z))
def logAllocation (r a W z : ℝ) : ℝ := 1 - a * logShare r W z
def logVelocity (r a W z : ℝ) : ℝ :=
  r * (1-logAllocation r a W z) * (1-logShare r W z)

theorem hasDerivAt_logShare (r W z : ℝ) (hW : 0 ≤ W) :
    HasDerivAt (logShare r W)
      (-r * logShare r W z * (1-logShare r W z)) z := by
  have he : HasDerivAt (fun t : ℝ => Real.exp (-r*t))
      (-r * Real.exp (-r*z)) z := by
    apply ((hasDerivAt_id z).const_mul (-r)).exp.congr_deriv
    simp only [id_eq]
    ring
  have hd : W + Real.exp (-r*z) ≠ 0 :=
    (add_pos_of_nonneg_of_pos hW (Real.exp_pos _)).ne'
  apply (he.div (he.const_add W) hd).congr_deriv
  dsimp [logShare]
  field_simp
  ring

theorem hasDerivAt_logAllocation (r a W z : ℝ) (hW : 0 ≤ W) :
    HasDerivAt (logAllocation r a W) (logVelocity r a W z) z := by
  apply (((hasDerivAt_logShare r W z hW).const_mul a).const_sub 1).congr_deriv
  dsimp [logAllocation, logVelocity]
  ring

theorem hasDerivAt_logVelocity (r a W z : ℝ) (hW : 0 ≤ W) :
    HasDerivAt (logVelocity r a W)
      (-r * logVelocity r a W z * (1-2*logShare r W z)) z := by
  have hp := hasDerivAt_logAllocation r a W z hW
  have hs := hasDerivAt_logShare r W z hW
  apply ((((hp.const_sub 1).const_mul r).mul (hs.const_sub 1))).congr_deriv
  dsimp [logVelocity, logAllocation]
  ring

def utility (r a W v g : ℝ) (S T H : ℝ → ℝ) (z : ℝ) : ℝ :=
  v*S (logAllocation r a W z) - Real.exp z*T (logAllocation r a W z) -
    g*H (logAllocation r a W z)

def score (r a W v g : ℝ) (S' T T' H' : ℝ → ℝ) (z : ℝ) : ℝ :=
  logVelocity r a W z *
      (v*S' (logAllocation r a W z) - Real.exp z*T' (logAllocation r a W z) -
        g*H' (logAllocation r a W z)) -
    Real.exp z*T (logAllocation r a W z)

theorem hasDerivAt_utility (r a W v g z : ℝ) (hW : 0 ≤ W)
    (S S' T T' H H' : ℝ → ℝ)
    (hS : HasDerivAt S (S' (logAllocation r a W z)) (logAllocation r a W z))
    (hT : HasDerivAt T (T' (logAllocation r a W z)) (logAllocation r a W z))
    (hH : HasDerivAt H (H' (logAllocation r a W z)) (logAllocation r a W z)) :
    HasDerivAt (utility r a W v g S T H) (score r a W v g S' T T' H' z) z := by
  have hp := hasDerivAt_logAllocation r a W z hW
  apply ((((hS.comp z hp).const_mul v).sub
    ((Real.hasDerivAt_exp z).mul (hT.comp z hp))).sub
    ((hH.comp z hp).const_mul g)).congr_deriv
  dsimp [score]
  ring

def ownHessian (r q omega b R Rp T Tp : ℝ) : ℝ :=
  let A := r*q*(1-omega);
  -r*A*(1-2*omega)*R + A^2*Rp - 2*b*A*Tp - b*T

def crossCoefficient (r q omega b R Rp Tp : ℝ) : ℝ :=
  let A := r*q*(1-omega)
  r*A*(1-2*omega)*R - A^2*Rp + b*A*Tp

theorem hasDerivAt_score (r a W v g z : ℝ) (hW : 0 ≤ W)
    (S' S'' T T' T'' H' H'' : ℝ → ℝ)
    (hS : HasDerivAt S' (S'' (logAllocation r a W z)) (logAllocation r a W z))
    (hT : HasDerivAt T (T' (logAllocation r a W z)) (logAllocation r a W z))
    (hT' : HasDerivAt T' (T'' (logAllocation r a W z)) (logAllocation r a W z))
    (hH : HasDerivAt H' (H'' (logAllocation r a W z)) (logAllocation r a W z)) :
    HasDerivAt (score r a W v g S' T T' H')
      (ownHessian r (1-logAllocation r a W z) (logShare r W z) (Real.exp z)
        (v*S' (logAllocation r a W z) - Real.exp z*T' (logAllocation r a W z) -
          g*H' (logAllocation r a W z))
        (v*S'' (logAllocation r a W z) - Real.exp z*T'' (logAllocation r a W z) -
          g*H'' (logAllocation r a W z))
        (T (logAllocation r a W z)) (T' (logAllocation r a W z))) z := by
  have hp := hasDerivAt_logAllocation r a W z hW
  have hR := (((hS.comp z hp).const_mul v).sub
    ((Real.hasDerivAt_exp z).mul (hT'.comp z hp))).sub
    ((hH.comp z hp).const_mul g)
  apply (((hasDerivAt_logVelocity r a W z hW).mul hR).sub
    ((Real.hasDerivAt_exp z).mul (hT.comp z hp))).congr_deriv
  dsimp [ownHessian, logVelocity]
  ring

theorem hessian_cross_identity (r q omega b R Rp T Tp : ℝ) :
    ownHessian r q omega b R Rp T Tp +
        crossCoefficient r q omega b R Rp Tp =
      -b * (r*q*(1-omega)*Tp+T) := by
  dsimp [ownHessian, crossCoefficient]
  ring

theorem hasDerivAt_logShare_rivalSum (r W z : ℝ) (hW : 0 ≤ W) :
    HasDerivAt (fun w : ℝ => logShare r w z)
      (-logShare r W z / (W+Real.exp (-r*z))) W := by
  have hd : W+Real.exp (-r*z) ≠ 0 :=
    (add_pos_of_nonneg_of_pos hW (Real.exp_pos _)).ne'
  apply ((hasDerivAt_const W (Real.exp (-r*z))).div
    ((hasDerivAt_id W).add_const (Real.exp (-r*z))) hd).congr_deriv
  dsimp [logShare]
  field_simp
  ring

theorem hasDerivAt_logAllocation_rivalSum (r a W z : ℝ) (hW : 0 ≤ W) :
    HasDerivAt (fun w : ℝ => logAllocation r a w z)
      ((1-logAllocation r a W z)/(W+Real.exp (-r*z))) W := by
  apply (((hasDerivAt_logShare_rivalSum r W z hW).const_mul a).const_sub 1).congr_deriv
  dsimp [logAllocation]
  ring

theorem hasDerivAt_logVelocity_rivalSum (r a W z : ℝ) (hW : 0 ≤ W) :
    HasDerivAt (fun w : ℝ => logVelocity r a w z)
      (-r*(1-logAllocation r a W z)*(1-2*logShare r W z)/
        (W+Real.exp (-r*z))) W := by
  have hp := hasDerivAt_logAllocation_rivalSum r a W z hW
  have hs := hasDerivAt_logShare_rivalSum r W z hW
  apply (((hp.const_sub 1).const_mul r).mul (hs.const_sub 1)).congr_deriv
  dsimp [logAllocation, logVelocity]
  ring

def rivalSumScoreDerivative (r q omega b R Rp Tp denom : ℝ) : ℝ :=
  q/denom * (-r*(1-2*omega)*R + r*q*(1-omega)*Rp - b*Tp)

theorem hasDerivAt_score_rivalSum (r a W v g z : ℝ) (hW : 0 ≤ W)
    (S' S'' T T' T'' H' H'' : ℝ → ℝ)
    (hS : HasDerivAt S' (S'' (logAllocation r a W z)) (logAllocation r a W z))
    (hT : HasDerivAt T (T' (logAllocation r a W z)) (logAllocation r a W z))
    (hT' : HasDerivAt T' (T'' (logAllocation r a W z)) (logAllocation r a W z))
    (hH : HasDerivAt H' (H'' (logAllocation r a W z)) (logAllocation r a W z)) :
    HasDerivAt (fun w : ℝ => score r a w v g S' T T' H' z)
      (rivalSumScoreDerivative r (1-logAllocation r a W z) (logShare r W z)
        (Real.exp z)
        (v*S' (logAllocation r a W z) - Real.exp z*T' (logAllocation r a W z) -
          g*H' (logAllocation r a W z))
        (v*S'' (logAllocation r a W z) - Real.exp z*T'' (logAllocation r a W z) -
          g*H'' (logAllocation r a W z)) (T' (logAllocation r a W z))
        (W+Real.exp (-r*z))) W := by
  have hp := hasDerivAt_logAllocation_rivalSum r a W z hW
  have hR := (((hS.comp W hp).const_mul v).sub
    ((hT'.comp W hp).const_mul (Real.exp z))).sub
    ((hH.comp W hp).const_mul g)
  apply (((hasDerivAt_logVelocity_rivalSum r a W z hW).mul hR).sub
    ((hT.comp W hp).const_mul (Real.exp z))).congr_deriv
  dsimp [rivalSumScoreDerivative, logVelocity]
  ring

theorem cross_eq_rivalSumDerivative (r a W z b R Rp Tp : ℝ) (hW : 0 ≤ W) :
    crossCoefficient r (1-logAllocation r a W z) (logShare r W z) b R Rp Tp =
      -r*W*rivalSumScoreDerivative r (1-logAllocation r a W z)
        (logShare r W z) b R Rp Tp (W+Real.exp (-r*z)) := by
  have hd : W+Real.exp (-r*z) ≠ 0 :=
    (add_pos_of_nonneg_of_pos hW (Real.exp_pos _)).ne'
  dsimp [crossCoefficient, rivalSumScoreDerivative, logShare, logAllocation]
  field_simp
  ring

theorem sum_abs_rival_cross {ι : Type*} [Fintype ι]
    (weights : ι → ℝ) (hw : ∀ i, 0 ≤ weights i)
    (r q omega b R Rp Tp : ℝ) (hr : 0 ≤ r) (homega : omega < 1)
    (hsum : ∑ i, weights i = 1-omega) :
    (∑ i, |r * weights i *
      (r*q*(1-2*omega)*R - q*(r*q*(1-omega))*Rp + b*q*Tp)|) =
      |crossCoefficient r q omega b R Rp Tp| := by
  have hs : 0 ≤ 1-omega := (sub_pos.mpr homega).le
  simp_rw [abs_mul, abs_of_nonneg hr, abs_of_nonneg (hw _)]
  rw [← Finset.sum_mul, ← Finset.mul_sum, hsum, ← abs_of_nonneg (mul_nonneg hr hs),
    ← abs_mul]
  congr 1
  dsimp [crossCoefficient]
  ring

end FCAppendix.Exclusive.Narrow.Existence
