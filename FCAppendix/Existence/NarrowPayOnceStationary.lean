import FCAppendix.Existence.NarrowPayOnceExpectedBounds

noncomputable section
namespace FCAppendix.Existence.NarrowPayOnce
open Set Filter Topology MeasureTheory
open scoped NNReal BoundedContinuousFunction

namespace FiniteScoreControl
variable {n R c : ℕ} {w0 kappa eps delta : ℝ}
  (U : FiniteScoreControl n R c w0 kappa eps delta)
  (nu : Measure U.valueBand) [IsProbabilityMeasure nu]

theorem expected_bid_continuous (beta : U.valueBand→ℝ) (hbeta : Continuous beta)
    (hb : ∀v,beta v∈Icc (U.B-eps) (U.B+eps)) (w : ℝ) :
    ContinuousOn (finiteExpectedScore (R:=R) n c nu beta w) (Icc (U.B-eps) (U.B+eps)) := by
  have hc : ContinuousOn (finiteExpectedScore (R:=R) n c nu beta w) (Ioi (0:ℝ)) := by
    rw [continuousOn_iff_continuous_restrict]
    exact continuous_finiteExpectedScore_positive U.n_ge nu beta hbeta
      (fun v=>U.lower_pos.trans_le (hb v).1) w
  exact hc.mono (fun z hz=>U.lower_pos.trans_le hz.1)

def finiteScoreData : Exclusive.Existence.ScoreData U.strategyBand U.valueBand
    (U.B-eps) (U.B+eps) U.own where
  score beta v z := finiteExpectedScore (R:=R) n c nu beta.val v z
  band_nonempty := by linarith [U.eps_pos]
  curvature_pos := U.own_pos
  continuous_bid beta v := U.expected_bid_continuous nu beta.val beta.val.continuous beta.property v
  inward_left beta v := (U.expected_inward nu beta.val beta.val.continuous beta.property v).1
  inward_right beta v := (U.expected_inward nu beta.val beta.val.continuous beta.property v).2
  decrease beta v x hx y hy hxy := U.expected_decrease nu beta.val beta.val.continuous beta.property v x y hx hy hxy

theorem exists_unique_stationary :
    ∃! beta : U.strategyBand, ∀v : U.valueBand,
      finiteExpectedScore (R:=R) n c nu beta.val v (beta.val v)=0 := by
  let D := U.finiteScoreData nu
  let L : ℝ≥0 := ⟨U.typeRate/U.own,div_nonneg U.typeRate_nonneg U.own_pos.le⟩
  let q : ℝ≥0 := ⟨U.rival/U.own,div_nonneg U.rival_nonneg U.own_pos.le⟩
  have hq : q<1 := by
    change U.rival/U.own<1
    apply (div_lt_one U.own_pos).mpr
    linarith [U.contraction_gap,U.kappa_pos]
  have hL : ∀theta v w z,z∈Icc (U.B-eps) (U.B+eps) →
      |D.score theta v z-D.score theta w z|≤U.own*(L:ℝ)*dist v w := by
    intro theta v w z hz
    have hh := U.expected_type_bound nu theta.val theta.val.continuous theta.property v w z hz
    change |finiteExpectedScore (R:=R) n c nu theta.val v z-
      finiteExpectedScore (R:=R) n c nu theta.val w z|≤_
    have he : U.own*(L:ℝ)=U.typeRate := by
      change U.own*(U.typeRate/U.own)=U.typeRate
      rw [mul_comm]
      exact div_mul_cancel₀ _ U.own_pos.ne'
    rw [he,Subtype.dist_eq,Real.dist_eq]
    exact hh
  apply Exclusive.Existence.exists_unique_pure_stationary D L hL q hq
  intro beta gamma v z hz
  have hh := U.expected_rival_bound nu beta.val gamma.val beta.val.continuous gamma.val.continuous
    beta.property gamma.property (dist beta gamma) dist_nonneg
    (fun v=>by simpa only [Real.dist_eq,Subtype.dist_eq] using
      BoundedContinuousFunction.dist_coe_le_dist (f:=beta.val) (g:=gamma.val) v) v z hz
  change |finiteExpectedScore (R:=R) n c nu beta.val v z-
    finiteExpectedScore (R:=R) n c nu gamma.val v z|≤_
  have he : U.own*(q:ℝ)=U.rival := by
    change U.own*(U.rival/U.own)=U.rival
    rw [mul_comm]
    exact div_mul_cancel₀ _ U.own_pos.ne'
  rw [he]
  exact hh

end FiniteScoreControl
end FCAppendix.Existence.NarrowPayOnce
