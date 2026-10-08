import FCAppendix.Finite.EnvelopeIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

namespace FCAppendix.Interim.Problem
open MeasureTheory

variable {n : ℕ}

theorem envelope_deriv_intervalIntegrable (P : FCAppendix.Interim.Problem n)
    (x y : ℝ) : IntervalIntegrable (deriv P.envelope) volume x y :=
  P.envelope_lipschitzWith.lipschitzOnWith.absolutelyContinuousOnInterval.intervalIntegrable_deriv

theorem envelope_sub_eq_integral_deriv (P : FCAppendix.Interim.Problem n)
    (x y : ℝ) : P.envelope y - P.envelope x = ∫ v in x..y, deriv P.envelope v :=
  P.envelope_lipschitzWith.lipschitzOnWith.absolutelyContinuousOnInterval.integral_deriv_eq_sub.symm

end FCAppendix.Interim.Problem
