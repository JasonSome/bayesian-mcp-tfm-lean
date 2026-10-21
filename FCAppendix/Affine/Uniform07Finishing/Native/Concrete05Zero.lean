import FCAppendix.Affine.Uniform07Finishing.Native.Concrete05Rows
import FCAppendix.Affine.Uniform07Finishing.Native.ZeroCountMonotonicity

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Concrete05
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open FCAppendix.Affine Crossover.Physical

variable {row : Uniform07.Row} {m : ℕ} [Nonempty (Fin m)]

omit [Nonempty (Fin m)] in
theorem auxiliary_receipt_gap (E : UniformFinite.ExactRestrictedLaw row m) :
    Uniform07.kappa row*sourceLowerPriceCeiling row<
      E.law.multiplier-Early.nativeRadius row := by
  have h := (source_auxiliary_floor_guards row).2.2.2
  have hL := multiplier_lower E
  norm_num only at h hL
  linarith

theorem native_zero_duplicate_le_half
    (E : UniformFinite.ExactRestrictedLaw row m)
    (hc : 1≤ Uniform07.capacity m) (i : Fin m) :
    duplicate (nativeGame E hc (sourceLowerPriceCeiling row)) i 0≤
      duplicate (nativeGame E hc (sourceLowerPriceCeiling row)) i
        (Uniform07.cutoff row/2) := by
  let test : Fin 3→ℝ:=fun r=>(r.val:ℝ)-successIndicator r.val
  have ht : Monotone test := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> norm_num [test,successIndicator,Fin.le_def] at *
  have h0 : test 0=0 := by norm_num [test,successIndicator]
  have hhalf : 0< Uniform07.cutoff row/2:=half_pos (Uniform07.cutoff_pos row)
  have hz : Uniform07.cutoff row/2≤ E.law.rejectionRoot := by
    have hh := (rejection_root_bounds E).1
    have hh' := Uniform07.cutoff_pos row
    linarith
  have h := sourceNativeGame_zero_broadcast_moment_le
    (width:=10*UniformFinite.Source.commonGuardMargin row) row E.cluster.market_two_le hc
    (source_auxiliary_floor_guards row).1
    (source_auxiliary_floor_guards row).2.1
    (source_auxiliary_floor_guards row).2.2.1
    (multiplier_lower E) (auxiliary_receipt_gap E) hz
    (UniformFinite.Source.common_guard_margin row)
    (lowerJoint E) (lowerJoint_value E) (lowerJoint_routes E)
    i (two 0) (two (Uniform07.cutoff row/2)) (two_bid le_rfl) (two_routes 0)
    (by simpa only [two_bid hhalf.le] using hhalf)
    (by simpa only [two_bid hhalf.le] using (le_rfl : Uniform07.cutoff row/2≤Uniform07.cutoff row/2)) (two_routes _)
    test ht h0
  simpa only [duplicate,CountLaw.duplicates_eq_expect,nativeGame,test] using h

theorem LowerFamily.native_zero_duplicate (F : LowerFamily)
    (row : Uniform07.Row) (k : ℕ) (i : Fin (F.start+k)) :
    duplicate (F.marketData row k).native i 0≤
      duplicate (F.marketData row k).native i (Uniform07.cutoff row/2) := by
  letI : Nonempty (Fin (F.start+k)) := (F.marketData row k).fin_nonempty
  exact native_zero_duplicate_le_half (F.construction row k).finite.restricted
    (F.marketData row k).capacity_positive i

end FCAppendix.Affine.Uniform07Finishing.Concrete05
