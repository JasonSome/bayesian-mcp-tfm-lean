import FCAppendix.Affine.Uniform07.TiltCertificate

namespace FCAppendix.Affine.Uniform07
open Set

def certifiedLaplaceBox (n : ℕ) (i : Row) (theta z : ℚ) (lz : LogCertificate z) : Box :=
  Box.inflate (laplacePolyBox n i theta z (cutoffBox i) lz.box (logX i).box)
    (expErrorQ n theta)

theorem certifiedLaplaceBox_ok (n : ℕ) (i : Row) (theta z : ℚ) (lz : LogCertificate z)
    (hz : (z:ℝ) ∈ Icc (1/2) (x i)) (htheta : 0 ≤ (theta:ℝ))
    (hsmall : (theta:ℝ)/((n:ℝ)+1) ≤ 1/2) :
    (certifiedLaplaceBox n i theta z lz).Holds (laplace i (theta:ℝ) (z:ℝ)) := by
  apply Box.inflate_ok (laplacePolyBox_ok n i theta z
    (cutoffBox_ok i) lz.correct (logX i).correct)
  have h := (rate_integral_errors n i (theta := (theta:ℝ)) (z := (z:ℝ))
    (cutoff_mem i) hz.1 hz.2 htheta hsmall).1
  simpa only [expErrorQ, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow,
    Rat.cast_natCast] using h

def first_test_objectiveZBox : Box := ⟨(613892264887355831767257/625000000000000000000000),(9822276238197693308276113/10000000000000000000000000)⟩
set_option maxHeartbeats 12000000 in
theorem first_test_objectiveZBox_ok : first_test_objectiveZBox.Holds (laplace .first (359/10000) (739/1000)) := by
  have h := certifiedLaplaceBox_ok 16 .first (359/10000) (739/1000) log_first_lo
    (by norm_num [x,xQ]) (by norm_num) (by norm_num)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] at h
  apply Box.widen h <;>
    norm_num (config := { maxSteps := 1000000 }) [first_test_objectiveZBox, certifiedLaplaceBox, laplacePolyBox, pieceZBox, momentBox, invMomentBox,
    Box.inflate, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.sum,
    Box.point, Box.div, Box.inv, expErrorQ, expPolyQ, Finset.sum_range_succ,
    Nat.factorial, cutoffBox, cutoffDenBox, log_first_lo, log_first_hi,
    log_second_lo, log_second_hi, logX, log_first_x, log_second_x,
    LogCertificate.box, xQ, xiQ, kappaQ, etaQ]

set_option maxHeartbeats 12000000 in
def first_test_objectiveZlo : LogCertificate first_test_objectiveZBox.lo where
  lo := (-4483050334442553267313116679/250000000000000000000000000000)
  hi := (-17932201337770213069252466713/1000000000000000000000000000000)
  n := 32
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [first_test_objectiveZBox,expBox,expPolyQ,expErrorQ,Box.inflate,Box.point,Finset.sum_range_succ,Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [first_test_objectiveZBox,expBox,expPolyQ,expErrorQ,Box.inflate,Box.point,Finset.sum_range_succ,Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [first_test_objectiveZBox,expBox,expPolyQ,expErrorQ,Box.inflate,Box.point,Finset.sum_range_succ,Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [first_test_objectiveZBox,expBox,expPolyQ,expErrorQ,Box.inflate,Box.point,Finset.sum_range_succ,Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [first_test_objectiveZBox,expBox,expPolyQ,expErrorQ,Box.inflate,Box.point,Finset.sum_range_succ,Nat.factorial]

set_option maxHeartbeats 12000000 in
def first_test_objectiveZhi : LogCertificate first_test_objectiveZBox.hi where
  lo := (-17932201337770213069252364907/1000000000000000000000000000000)
  hi := (-2241525167221276633656545613/125000000000000000000000000000)
  n := 32
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [first_test_objectiveZBox,expBox,expPolyQ,expErrorQ,Box.inflate,Box.point,Finset.sum_range_succ,Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [first_test_objectiveZBox,expBox,expPolyQ,expErrorQ,Box.inflate,Box.point,Finset.sum_range_succ,Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [first_test_objectiveZBox,expBox,expPolyQ,expErrorQ,Box.inflate,Box.point,Finset.sum_range_succ,Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [first_test_objectiveZBox,expBox,expPolyQ,expErrorQ,Box.inflate,Box.point,Finset.sum_range_succ,Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [first_test_objectiveZBox,expBox,expPolyQ,expErrorQ,Box.inflate,Box.point,Finset.sum_range_succ,Nat.factorial]

def first_test_objectiveBox : Box := Box.sub (Box.point (-358641/20000000))
  (logBox first_test_objectiveZBox first_test_objectiveZlo first_test_objectiveZhi)
theorem first_test_objectiveBox_ok : first_test_objectiveBox.Holds (objective .first (359/10000) (739/1000)) := by
  have h := Box.sub_ok (Box.point_ok (-358641/20000000))
    (logBox_ok first_test_objectiveZlo first_test_objectiveZhi first_test_objectiveZBox_ok)
  norm_num only [Rat.cast_div,Rat.cast_neg,Rat.cast_ofNat] at h
  convert h using 1 <;> norm_num [objective,rho,first_test_objectiveBox]
theorem first_test_objective : ((945861/6250000000000):ℝ) < objective .first (359/10000) (739/1000) := by
  apply Box.lower_real first_test_objectiveBox_ok
  norm_num [first_test_objectiveBox,Box.sub,Box.add,Box.neg,Box.point,
    logBox,first_test_objectiveZlo,first_test_objectiveZhi]

def first_mid_objectiveZBox : Box := ⟨(4935866580272203238709987/5000000000000000000000000),(394869326421776259096799/400000000000000000000000)⟩
set_option maxHeartbeats 12000000 in
theorem first_mid_objectiveZBox_ok : first_mid_objectiveZBox.Holds (laplace .first (5169/200000) (371/500)) := by
  have h := certifiedLaplaceBox_ok 16 .first (5169/200000) (371/500) log_first_hi
    (by norm_num [x,xQ]) (by norm_num) (by norm_num)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] at h
  apply Box.widen h <;>
    norm_num (config := { maxSteps := 1000000 }) [first_mid_objectiveZBox, certifiedLaplaceBox, laplacePolyBox, pieceZBox, momentBox, invMomentBox,
    Box.inflate, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.sum,
    Box.point, Box.div, Box.inv, expErrorQ, expPolyQ, Finset.sum_range_succ,
    Nat.factorial, cutoffBox, cutoffDenBox, log_first_lo, log_first_hi,
    log_second_lo, log_second_hi, logX, log_first_x, log_second_x,
    LogCertificate.box, xQ, xiQ, kappaQ, etaQ]

set_option maxHeartbeats 12000000 in
def first_mid_objectiveZlo : LogCertificate first_mid_objectiveZBox.lo where
  lo := (-12909656124974810016637469331/1000000000000000000000000000000)
  hi := (-806853507810925626039841833/62500000000000000000000000000)
  n := 32
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [first_mid_objectiveZBox,expBox,expPolyQ,expErrorQ,Box.inflate,Box.point,Finset.sum_range_succ,Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [first_mid_objectiveZBox,expBox,expPolyQ,expErrorQ,Box.inflate,Box.point,Finset.sum_range_succ,Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [first_mid_objectiveZBox,expBox,expPolyQ,expErrorQ,Box.inflate,Box.point,Finset.sum_range_succ,Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [first_mid_objectiveZBox,expBox,expPolyQ,expErrorQ,Box.inflate,Box.point,Finset.sum_range_succ,Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [first_mid_objectiveZBox,expBox,expPolyQ,expErrorQ,Box.inflate,Box.point,Finset.sum_range_succ,Nat.factorial]

set_option maxHeartbeats 12000000 in
def first_mid_objectiveZhi : LogCertificate first_mid_objectiveZBox.hi where
  lo := (-403426753905462813019917751/31250000000000000000000000000)
  hi := (-12909656124974810016637368029/1000000000000000000000000000000)
  n := 32
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [first_mid_objectiveZBox,expBox,expPolyQ,expErrorQ,Box.inflate,Box.point,Finset.sum_range_succ,Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [first_mid_objectiveZBox,expBox,expPolyQ,expErrorQ,Box.inflate,Box.point,Finset.sum_range_succ,Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [first_mid_objectiveZBox,expBox,expPolyQ,expErrorQ,Box.inflate,Box.point,Finset.sum_range_succ,Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [first_mid_objectiveZBox,expBox,expPolyQ,expErrorQ,Box.inflate,Box.point,Finset.sum_range_succ,Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [first_mid_objectiveZBox,expBox,expPolyQ,expErrorQ,Box.inflate,Box.point,Finset.sum_range_succ,Nat.factorial]

def first_mid_objectiveBox : Box := Box.sub (Box.point (-5163831/400000000))
  (logBox first_mid_objectiveZBox first_mid_objectiveZlo first_mid_objectiveZhi)
theorem first_mid_objectiveBox_ok : first_mid_objectiveBox.Holds (objective .first (5169/200000) (371/500)) := by
  have h := Box.sub_ok (Box.point_ok (-5163831/400000000))
    (logBox_ok first_mid_objectiveZlo first_mid_objectiveZhi first_mid_objectiveZBox_ok)
  norm_num only [Rat.cast_div,Rat.cast_neg,Rat.cast_ofNat] at h
  convert h using 1 <;> norm_num [objective,rho,first_mid_objectiveBox]
theorem first_mid_objective : objective .first (5169/200000) (371/500) < ((3145003/40000000000000):ℝ) := by
  apply Box.upper_real first_mid_objectiveBox_ok
  norm_num [first_mid_objectiveBox,Box.sub,Box.add,Box.neg,Box.point,
    logBox,first_mid_objectiveZlo,first_mid_objectiveZhi]

def second_test_objectiveZBox : Box := ⟨(9787014234378145359739669/10000000000000000000000000),(978701423437814535973967/1000000000000000000000000)⟩
set_option maxHeartbeats 12000000 in
theorem second_test_objectiveZBox_ok : second_test_objectiveZBox.Holds (laplace .second (431/10000) (691/1000)) := by
  have h := certifiedLaplaceBox_ok 16 .second (431/10000) (691/1000) log_second_lo
    (by norm_num [x,xQ]) (by norm_num) (by norm_num)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] at h
  apply Box.widen h <;>
    norm_num (config := { maxSteps := 1000000 }) [second_test_objectiveZBox, certifiedLaplaceBox, laplacePolyBox, pieceZBox, momentBox, invMomentBox,
    Box.inflate, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.sum,
    Box.point, Box.div, Box.inv, expErrorQ, expPolyQ, Finset.sum_range_succ,
    Nat.factorial, cutoffBox, cutoffDenBox, log_first_lo, log_first_hi,
    log_second_lo, log_second_hi, logX, log_first_x, log_second_x,
    LogCertificate.box, xQ, xiQ, kappaQ, etaQ]

set_option maxHeartbeats 12000000 in
def second_test_objectiveZlo : LogCertificate second_test_objectiveZBox.lo where
  lo := (-10764332067263253330306557309/500000000000000000000000000000)
  hi := (-4305732826905301332122622923/200000000000000000000000000000)
  n := 32
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [second_test_objectiveZBox,expBox,expPolyQ,expErrorQ,Box.inflate,Box.point,Finset.sum_range_succ,Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [second_test_objectiveZBox,expBox,expPolyQ,expErrorQ,Box.inflate,Box.point,Finset.sum_range_succ,Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [second_test_objectiveZBox,expBox,expPolyQ,expErrorQ,Box.inflate,Box.point,Finset.sum_range_succ,Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [second_test_objectiveZBox,expBox,expPolyQ,expErrorQ,Box.inflate,Box.point,Finset.sum_range_succ,Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [second_test_objectiveZBox,expBox,expPolyQ,expErrorQ,Box.inflate,Box.point,Finset.sum_range_succ,Nat.factorial]

set_option maxHeartbeats 12000000 in
def second_test_objectiveZhi : LogCertificate second_test_objectiveZBox.hi where
  lo := (-10764332067263253330306506221/500000000000000000000000000000)
  hi := (-21528664134526506660613012439/1000000000000000000000000000000)
  n := 32
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [second_test_objectiveZBox,expBox,expPolyQ,expErrorQ,Box.inflate,Box.point,Finset.sum_range_succ,Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [second_test_objectiveZBox,expBox,expPolyQ,expErrorQ,Box.inflate,Box.point,Finset.sum_range_succ,Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [second_test_objectiveZBox,expBox,expPolyQ,expErrorQ,Box.inflate,Box.point,Finset.sum_range_succ,Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [second_test_objectiveZBox,expBox,expPolyQ,expErrorQ,Box.inflate,Box.point,Finset.sum_range_succ,Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [second_test_objectiveZBox,expBox,expPolyQ,expErrorQ,Box.inflate,Box.point,Finset.sum_range_succ,Nat.factorial]

def second_test_objectiveBox : Box := Box.sub (Box.point (-430569/20000000))
  (logBox second_test_objectiveZBox second_test_objectiveZlo second_test_objectiveZhi)
theorem second_test_objectiveBox_ok : second_test_objectiveBox.Holds (objective .second (431/10000) (691/1000)) := by
  have h := Box.sub_ok (Box.point_ok (-430569/20000000))
    (logBox_ok second_test_objectiveZlo second_test_objectiveZhi second_test_objectiveZBox_ok)
  norm_num only [Rat.cast_div,Rat.cast_neg,Rat.cast_ofNat] at h
  convert h using 1 <;> norm_num [objective,rho,second_test_objectiveBox]
theorem second_test_objective : ((5353363/25000000000000):ℝ) < objective .second (431/10000) (691/1000) := by
  apply Box.lower_real second_test_objectiveBox_ok
  norm_num [second_test_objectiveBox,Box.sub,Box.add,Box.neg,Box.point,
    logBox,second_test_objectiveZlo,second_test_objectiveZhi]

def second_mid_objectiveZBox : Box := ⟨(4929497391726740650830473/5000000000000000000000000),(9858994783453481301660947/10000000000000000000000000)⟩
set_option maxHeartbeats 12000000 in
theorem second_mid_objectiveZBox_ok : second_mid_objectiveZBox.Holds (laplace .second (2843/100000) (347/500)) := by
  have h := certifiedLaplaceBox_ok 16 .second (2843/100000) (347/500) log_second_hi
    (by norm_num [x,xQ]) (by norm_num) (by norm_num)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] at h
  apply Box.widen h <;>
    norm_num (config := { maxSteps := 1000000 }) [second_mid_objectiveZBox, certifiedLaplaceBox, laplacePolyBox, pieceZBox, momentBox, invMomentBox,
    Box.inflate, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.sum,
    Box.point, Box.div, Box.inv, expErrorQ, expPolyQ, Finset.sum_range_succ,
    Nat.factorial, cutoffBox, cutoffDenBox, log_first_lo, log_first_hi,
    log_second_lo, log_second_hi, logX, log_first_x, log_second_x,
    LogCertificate.box, xQ, xiQ, kappaQ, etaQ]

set_option maxHeartbeats 12000000 in
def second_mid_objectiveZlo : LogCertificate second_mid_objectiveZBox.lo where
  lo := (-1420087851645722997276626963/100000000000000000000000000000)
  hi := (-14200878516457229972766269627/1000000000000000000000000000000)
  n := 32
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [second_mid_objectiveZBox,expBox,expPolyQ,expErrorQ,Box.inflate,Box.point,Finset.sum_range_succ,Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [second_mid_objectiveZBox,expBox,expPolyQ,expErrorQ,Box.inflate,Box.point,Finset.sum_range_succ,Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [second_mid_objectiveZBox,expBox,expPolyQ,expErrorQ,Box.inflate,Box.point,Finset.sum_range_succ,Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [second_mid_objectiveZBox,expBox,expPolyQ,expErrorQ,Box.inflate,Box.point,Finset.sum_range_succ,Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [second_mid_objectiveZBox,expBox,expPolyQ,expErrorQ,Box.inflate,Box.point,Finset.sum_range_succ,Nat.factorial]

set_option maxHeartbeats 12000000 in
def second_mid_objectiveZhi : LogCertificate second_mid_objectiveZBox.hi where
  lo := (-71004392582286149863830841/5000000000000000000000000000)
  hi := (-14200878516457229972766168197/1000000000000000000000000000000)
  n := 32
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [second_mid_objectiveZBox,expBox,expPolyQ,expErrorQ,Box.inflate,Box.point,Finset.sum_range_succ,Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [second_mid_objectiveZBox,expBox,expPolyQ,expErrorQ,Box.inflate,Box.point,Finset.sum_range_succ,Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [second_mid_objectiveZBox,expBox,expPolyQ,expErrorQ,Box.inflate,Box.point,Finset.sum_range_succ,Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [second_mid_objectiveZBox,expBox,expPolyQ,expErrorQ,Box.inflate,Box.point,Finset.sum_range_succ,Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [second_mid_objectiveZBox,expBox,expPolyQ,expErrorQ,Box.inflate,Box.point,Finset.sum_range_succ,Nat.factorial]

def second_mid_objectiveBox : Box := Box.sub (Box.point (-2840157/200000000))
  (logBox second_mid_objectiveZBox second_mid_objectiveZlo second_mid_objectiveZhi)
theorem second_mid_objectiveBox_ok : second_mid_objectiveBox.Holds (objective .second (2843/100000) (347/500)) := by
  have h := Box.sub_ok (Box.point_ok (-2840157/200000000))
    (logBox_ok second_mid_objectiveZlo second_mid_objectiveZhi second_mid_objectiveZBox_ok)
  norm_num only [Rat.cast_div,Rat.cast_neg,Rat.cast_ofNat] at h
  convert h using 1 <;> norm_num [objective,rho,second_mid_objectiveBox]
theorem second_mid_objective : objective .second (2843/100000) (347/500) < ((187033/2000000000000):ℝ) := by
  apply Box.upper_real second_mid_objectiveBox_ok
  norm_num [second_mid_objectiveBox,Box.sub,Box.add,Box.neg,Box.point,
    logBox,second_mid_objectiveZlo,second_mid_objectiveZhi]

theorem first_rate_high : canonicalRate .first (371/500) < (786282/10^13:ℝ) := by
  obtain ⟨theta,_htheta,_hroot,_hrate,hbound⟩ := first_optimized_bracket
  linarith [first_mid_objective]

theorem second_rate_high : canonicalRate .second (347/500) < (935290/10^13:ℝ) := by
  obtain ⟨theta,_htheta,_hroot,_hrate,hbound⟩ := second_optimized_bracket
  linarith [second_mid_objective]
end FCAppendix.Affine.Uniform07
