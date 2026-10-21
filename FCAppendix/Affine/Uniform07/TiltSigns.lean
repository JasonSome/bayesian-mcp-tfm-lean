import FCAppendix.Affine.Uniform07.RateDefinitions
import FCAppendix.Affine.Uniform07.ParameterCertificate

namespace FCAppendix.Affine.Uniform07
open Set

def certifiedTiltBox (n : ℕ) (i : Row) (theta z : ℚ) (lz : LogCertificate z) : Box :=
  Box.inflate (tiltScorePolyBox n i theta z (cutoffBox i) lz.box (logX i).box)
    (expErrorQ n theta)

theorem certifiedTiltBox_ok (n : ℕ) (i : Row) (theta z : ℚ) (lz : LogCertificate z)
    (hz : (z:ℝ) ∈ Icc (1/2) (x i)) (htheta : 0 ≤ (theta:ℝ))
    (hsmall : (theta:ℝ)/((n:ℝ)+1) ≤ 1/2) :
    (certifiedTiltBox n i theta z lz).Holds (tiltScore i (theta:ℝ) (z:ℝ)) := by
  apply Box.inflate_ok (tiltScorePolyBox_ok n i theta z
    (cutoffBox_ok i) lz.correct (logX i).correct)
  have h := (rate_integral_errors n i (theta := (theta:ℝ)) (z := (z:ℝ))
    (cutoff_mem i) hz.1 hz.2 htheta hsmall).2
  simpa only [expErrorQ, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow,
    Rat.cast_natCast] using h

set_option maxHeartbeats 12000000 in
theorem first_tilt_low : (13661/10^10:ℝ) < tiltScore .first (1/50) (371/500) := by
  have h := certifiedTiltBox_ok 12 .first (1/50) (371/500) log_first_hi
    (by norm_num [x,xQ]) (by norm_num) (by norm_num)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] at h
  apply Box.lower_real h
  norm_num (config := { maxSteps := 1000000 }) [certifiedTiltBox, tiltScorePolyBox, pieceFBox, momentBox,
    invMomentBox, Box.inflate, Box.add, Box.sub, Box.neg, Box.mul, Box.scale,
    Box.sum, Box.point, Box.div, Box.inv, expErrorQ, expPolyQ,
    Finset.sum_range_succ, Nat.factorial, cutoffBox, cutoffDenBox,
    log_first_hi, logX, log_first_x, LogCertificate.box, xQ, xiQ, kappaQ, etaQ]

set_option maxHeartbeats 12000000 in
theorem first_tilt_high : tiltScore .first (7/5) (1/2) < (-3703/250000000:ℝ) := by
  have h := certifiedTiltBox_ok 16 .first (7/5) (1/2) log_half
    (by norm_num [x,xQ]) (by norm_num) (by norm_num)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] at h
  apply Box.upper_real h
  norm_num (config := { maxSteps := 1000000 }) [certifiedTiltBox, tiltScorePolyBox, pieceFBox, momentBox,
    invMomentBox, Box.inflate, Box.add, Box.sub, Box.neg, Box.mul, Box.scale,
    Box.sum, Box.point, Box.div, Box.inv, expErrorQ, expPolyQ,
    Finset.sum_range_succ, Nat.factorial, cutoffBox, cutoffDenBox,
    log_first_hi, log_second_hi, log_half, logX, log_first_x, log_second_x,
    LogCertificate.box, xQ, xiQ, kappaQ, etaQ]

set_option maxHeartbeats 12000000 in
theorem first_bracket_low : (0:ℝ) < tiltScore .first (323/12500) (371/500) := by
  have h := certifiedTiltBox_ok 12 .first (323/12500) (371/500) log_first_hi
    (by norm_num [x,xQ]) (by norm_num) (by norm_num)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] at h
  apply Box.lower_real h
  norm_num (config := { maxSteps := 1000000 }) [certifiedTiltBox, tiltScorePolyBox, pieceFBox, momentBox,
    invMomentBox, Box.inflate, Box.add, Box.sub, Box.neg, Box.mul, Box.scale,
    Box.sum, Box.point, Box.div, Box.inv, expErrorQ, expPolyQ,
    Finset.sum_range_succ, Nat.factorial, cutoffBox, cutoffDenBox,
    log_first_hi, log_second_hi, log_half, logX, log_first_x, log_second_x,
    LogCertificate.box, xQ, xiQ, kappaQ, etaQ]

set_option maxHeartbeats 12000000 in
theorem first_bracket_high : tiltScore .first (517/20000) (371/500) < (0:ℝ) := by
  have h := certifiedTiltBox_ok 12 .first (517/20000) (371/500) log_first_hi
    (by norm_num [x,xQ]) (by norm_num) (by norm_num)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] at h
  apply Box.upper_real h
  norm_num (config := { maxSteps := 1000000 }) [certifiedTiltBox, tiltScorePolyBox, pieceFBox, momentBox,
    invMomentBox, Box.inflate, Box.add, Box.sub, Box.neg, Box.mul, Box.scale,
    Box.sum, Box.point, Box.div, Box.inv, expErrorQ, expPolyQ,
    Finset.sum_range_succ, Nat.factorial, cutoffBox, cutoffDenBox,
    log_first_hi, log_second_hi, log_half, logX, log_first_x, log_second_x,
    LogCertificate.box, xQ, xiQ, kappaQ, etaQ]

set_option maxHeartbeats 12000000 in
theorem second_tilt_low : (19361/10^10:ℝ) < tiltScore .second (1/50) (347/500) := by
  have h := certifiedTiltBox_ok 12 .second (1/50) (347/500) log_second_hi
    (by norm_num [x,xQ]) (by norm_num) (by norm_num)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] at h
  apply Box.lower_real h
  norm_num (config := { maxSteps := 1000000 }) [certifiedTiltBox, tiltScorePolyBox, pieceFBox, momentBox,
    invMomentBox, Box.inflate, Box.add, Box.sub, Box.neg, Box.mul, Box.scale,
    Box.sum, Box.point, Box.div, Box.inv, expErrorQ, expPolyQ,
    Finset.sum_range_succ, Nat.factorial, cutoffBox, cutoffDenBox,
    log_first_hi, log_second_hi, log_half, logX, log_first_x, log_second_x,
    LogCertificate.box, xQ, xiQ, kappaQ, etaQ]

set_option maxHeartbeats 12000000 in
theorem second_tilt_high : tiltScore .second (7/5) (1/2) < (-19121/10^9:ℝ) := by
  have h := certifiedTiltBox_ok 16 .second (7/5) (1/2) log_half
    (by norm_num [x,xQ]) (by norm_num) (by norm_num)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] at h
  apply Box.upper_real h
  norm_num (config := { maxSteps := 1000000 }) [certifiedTiltBox, tiltScorePolyBox, pieceFBox, momentBox,
    invMomentBox, Box.inflate, Box.add, Box.sub, Box.neg, Box.mul, Box.scale,
    Box.sum, Box.point, Box.div, Box.inv, expErrorQ, expPolyQ,
    Finset.sum_range_succ, Nat.factorial, cutoffBox, cutoffDenBox,
    log_first_hi, log_second_hi, log_half, logX, log_first_x, log_second_x,
    LogCertificate.box, xQ, xiQ, kappaQ, etaQ]

set_option maxHeartbeats 12000000 in
theorem second_bracket_low : (0:ℝ) < tiltScore .second (1421/50000) (347/500) := by
  have h := certifiedTiltBox_ok 12 .second (1421/50000) (347/500) log_second_hi
    (by norm_num [x,xQ]) (by norm_num) (by norm_num)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] at h
  apply Box.lower_real h
  norm_num (config := { maxSteps := 1000000 }) [certifiedTiltBox, tiltScorePolyBox, pieceFBox, momentBox,
    invMomentBox, Box.inflate, Box.add, Box.sub, Box.neg, Box.mul, Box.scale,
    Box.sum, Box.point, Box.div, Box.inv, expErrorQ, expPolyQ,
    Finset.sum_range_succ, Nat.factorial, cutoffBox, cutoffDenBox,
    log_first_hi, log_second_hi, log_half, logX, log_first_x, log_second_x,
    LogCertificate.box, xQ, xiQ, kappaQ, etaQ]

set_option maxHeartbeats 12000000 in
theorem second_bracket_high : tiltScore .second (711/25000) (347/500) < (0:ℝ) := by
  have h := certifiedTiltBox_ok 12 .second (711/25000) (347/500) log_second_hi
    (by norm_num [x,xQ]) (by norm_num) (by norm_num)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] at h
  apply Box.upper_real h
  norm_num (config := { maxSteps := 1000000 }) [certifiedTiltBox, tiltScorePolyBox, pieceFBox, momentBox,
    invMomentBox, Box.inflate, Box.add, Box.sub, Box.neg, Box.mul, Box.scale,
    Box.sum, Box.point, Box.div, Box.inv, expErrorQ, expPolyQ,
    Finset.sum_range_succ, Nat.factorial, cutoffBox, cutoffDenBox,
    log_first_hi, log_second_hi, log_half, logX, log_first_x, log_second_x,
    LogCertificate.box, xQ, xiQ, kappaQ, etaQ]

end FCAppendix.Affine.Uniform07
