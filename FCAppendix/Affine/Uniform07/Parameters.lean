import FCAppendix.Affine.Uniform07.RationalBounds
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
namespace FCAppendix.Affine.Uniform07
inductive Row where | first | second deriving DecidableEq, Fintype
 def etaQ : Row → ℚ | .first => 1/10 | .second => 9/50
 def xQ : Row → ℚ | .first => 3/4 | .second => 7/10
 def xiQ (i : Row) : ℚ := (1-etaQ i)/2
 def kappaQ (i : Row) : ℚ := 1-xiQ i
 def zloQ : Row → ℚ | .first => 739/1000 | .second => 691/1000
 def zhiQ : Row → ℚ | .first => 371/500 | .second => 347/500
 noncomputable def eta (i : Row) : ℝ := etaQ i
 noncomputable def x (i : Row) : ℝ := xQ i
 noncomputable def xi (i : Row) : ℝ := xiQ i
 noncomputable def kappa (i : Row) : ℝ := kappaQ i
 noncomputable def delta : ℝ := 1/1000
 noncomputable def rho : ℝ := 999/2000
 noncomputable def cutoff (i : Row) : ℝ := delta/(2*x i*(1-Real.log (x i))-1)
 noncomputable def entry (i : Row) : ℝ := x i*cutoff i
 noncomputable def limitingFloor (i : Row) : ℝ := 2*entry i-entry i^2/cutoff i
 noncomputable def limitDup (i : Row) : ℝ := cutoff i*(1-x i^2+2*x i*Real.log (x i))
 noncomputable def limitCoverage (i : Row) : ℝ := 1-delta-limitDup i
 noncomputable def testValue : ℝ := 109/100000

 def capacity (m : ℕ) : ℕ := (999*m)/2000
 noncomputable def uniformLaw : MeasureTheory.Measure ℝ :=
  MeasureTheory.volume.restrict (Set.Icc 0 1)
 theorem xi_identity (i : Row) : 2*xi i = 1-eta i := by
  cases i <;> norm_num [xi,xiQ,eta,etaQ]
 theorem xi_pos (i : Row) : 0 < xi i := by cases i <;> norm_num [xi,xiQ,etaQ]
 theorem eta_pos (i : Row) : 0 < eta i := by cases i <;> norm_num [eta,etaQ]
 theorem route_coefficient (i : Row) :
    1-2*eta i/xi i = (match i with | .first => 5/9 | .second => 5/41) := by
  cases i <;> norm_num [eta,etaQ,xi,xiQ]
 theorem route_coefficient_pos (i : Row) : 0 < 1-2*eta i/xi i := by
  rw [route_coefficient]; cases i <;> norm_num
 theorem cutoff_equation (i : Row)
    (h : 2*x i*(1-Real.log (x i))-1 ≠ 0) :
    cutoff i*(2*x i*(1-Real.log (x i))-1) = delta := by simp [cutoff,h]
 theorem floor_simplify (i : Row) (ht : cutoff i ≠ 0) :
    limitingFloor i = cutoff i*(2*x i-x i^2) := by
  unfold limitingFloor entry; field_simp [ht]
 theorem duplicate_floor_identity (i : Row)
    (ht : cutoff i ≠ 0) (hd : 2*x i*(1-Real.log (x i))-1 ≠ 0) :
    limitDup i = limitingFloor i-delta ∧ limitCoverage i = 1-limitingFloor i := by
  have h := cutoff_equation i hd
  rw [floor_simplify i ht]
  constructor
  · dsimp [limitDup]; nlinarith
  · dsimp [limitCoverage,limitDup]; nlinarith
end FCAppendix.Affine.Uniform07
