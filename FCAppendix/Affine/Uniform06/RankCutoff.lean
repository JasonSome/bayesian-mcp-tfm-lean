import FCAppendix.Affine.Uniform06.LowChernoffCertificate
import FCAppendix.Ample.RateSystem

set_option autoImplicit false
noncomputable section

namespace FCAppendix.Affine.Uniform06.RankCutoff

open FCAppendix.Affine.Uniform07

def Mstar (i : Row) : ℝ := (x i+1/200)*cutoff i

theorem Mstar_above_entry (i : Row) : entry i < Mstar i := by
  have ht := cutoff_pos i
  unfold Mstar entry
  nlinarith

theorem Mstar_bounds (i : Row) :
    0 < Mstar i ∧ Mstar i < (17/20000:ℝ) := by
  have ht := cutoff_pos i
  have hT := (LowChernoff.sourceTBox_ok i).2
  constructor
  · unfold Mstar
    have hx : 0 < x i := by cases i <;> norm_num [x, xQ]
    positivity
  · cases i <;> norm_num [Mstar, x, xQ, LowChernoff.sourceTBox] at hT ⊢ <;> linarith

theorem Mstar_below_source_guards (i : Row) :
    Mstar i < min delta (delta*(1-cutoff i)/(1-delta)) := by
  have hM := (Mstar_bounds i).2
  have hT := (LowChernoff.sourceTBox_ok i).2
  apply lt_min
  · norm_num [delta] at *
    linarith
  · apply (lt_div_iff₀ (by norm_num [delta] : 0 < 1-delta)).mpr
    cases i <;> norm_num [delta, LowChernoff.sourceTBox] at hT ⊢ <;> nlinarith

theorem exp_tenth_upper : Real.exp (1/10:ℝ) ≤ (553/500:ℝ) := by
  apply le_of_lt
  have hb := Box.upper_real (expBox_ok 4 (1/10) (by norm_num))
    (show ((expBox 4 (1/10)).hi : ℝ) < (553/500:ℝ) from by
      norm_num [expBox, expPolyQ, expErrorQ, Box.inflate, Box.point, Finset.sum_range_succ, Nat.factorial])
  norm_num at hb
  exact hb

theorem entropy_lower_of_small_rank {w : ℝ}
    (hw : 0 < w) (hwHi : w ≤ (17/20000:ℝ)) :
    (9/1000000:ℝ) < Ample.binaryKL delta w := by
  have hw1 : w < 1 := by linarith
  have hδ : 0 < delta := by norm_num [delta]
  have hδ1 : delta < 1 := by norm_num [delta]
  have hobj := Ample.binary_objective_le hw hw1 hδ hδ1 (1/10)
  have hOne : 0 < 1-w := sub_pos.mpr hw1
  have harg : 0 < 1-w+w*Real.exp (1/10:ℝ) := by positivity
  have hlog := Real.log_le_sub_one_of_pos harg
  have he0 : 0 ≤ Real.exp (1/10:ℝ)-1 := by
    have hh := Real.one_le_exp_iff.mpr (show (0:ℝ) ≤ 1/10 by norm_num)
    linarith
  have heHi : Real.exp (1/10:ℝ)-1 ≤ (53/500:ℝ) := by
    linarith [exp_tenth_upper]
  have hprod := mul_le_mul hwHi heHi he0 (by norm_num : (0:ℝ) ≤ 17/20000)
  norm_num [delta] at hobj
  dsimp only [delta]
  nlinarith

theorem rankI0_lt_three_micro (i : Row) :
    LowChernoff.rankI0 i < (3/1000000:ℝ) := by
  have h := (LowChernoff.rankI0Box_ok i).2
  have hbound : ((LowChernoff.rankI0Box i).hi : ℝ) < (3/1000000:ℝ) := by
    cases i <;> norm_num [LowChernoff.rankI0Box, logBox,
      LowChernoff.logRankOneLo, LowChernoff.logRankOneHi,
      LowChernoff.logRankTwoLo, LowChernoff.logRankTwoHi,
      Box.add, Box.scale, Box.mul, Box.point, LogCertificate.box]
  exact h.trans_lt hbound

theorem source_entropy_margin (i : Row) :
    LowChernoff.rankI0 i < Ample.binaryKL delta (Mstar i) ∧
      2*LowChernoff.rankI0 i < Ample.binaryKL delta (Mstar i) := by
  have hJ := entropy_lower_of_small_rank (Mstar_bounds i).1 (Mstar_bounds i).2.le
  have hI := rankI0_lt_three_micro i
  constructor <;> linarith

theorem choose_rank_cutoff (i : Row) :
    ∃ w : ℝ, entry i < w ∧
      w < min delta (delta*(1-cutoff i)/(1-delta)) ∧
      LowChernoff.rankI0 i < Ample.binaryKL delta w ∧
      2*LowChernoff.rankI0 i < Ample.binaryKL delta w :=
  ⟨Mstar i, Mstar_above_entry i, Mstar_below_source_guards i,
    source_entropy_margin i⟩

end FCAppendix.Affine.Uniform06.RankCutoff
