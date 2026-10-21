import FCAppendix.Affine.Uniform07.Parameters

namespace FCAppendix.Affine.Uniform07
open Set
def log_half : LogCertificate (1/2) where
  lo := (-34657359027997265470861606073/50000000000000000000000000000)
  hi := (-693147180559945309417232121457/1000000000000000000000000000000)
  n := 32
  q_pos := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ]
  lo_small := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ]
  hi_small := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ]
  lower_check := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ]
  upper_check := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ]

def log_first_x : LogCertificate (3/4) where
  lo := (-57536414490356185487843801199/200000000000000000000000000000)
  hi := (-35960259056472615929902375749/125000000000000000000000000000)
  n := 32
  q_pos := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ]
  lo_small := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ]
  hi_small := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ]
  lower_check := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ]
  upper_check := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ]

def log_first_lo : LogCertificate (739/1000) where
  lo := (-151228679016967638918407744487/500000000000000000000000000000)
  hi := (-302457358033935277836815488971/1000000000000000000000000000000)
  n := 32
  q_pos := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ]
  lo_small := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ]
  hi_small := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ]
  lower_check := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ]
  upper_check := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ]

def log_first_hi : LogCertificate (371/500) where
  lo := (-74601508953689150846730090031/250000000000000000000000000000)
  hi := (-298406035814756603386920360121/1000000000000000000000000000000)
  n := 32
  q_pos := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ]
  lo_small := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ]
  hi_small := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ]
  lower_check := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ]
  upper_check := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ]

def log_second_x : LogCertificate (7/10) where
  lo := (-356674943938732378912638711243/1000000000000000000000000000000)
  hi := (-8916873598468309472815967781/25000000000000000000000000000)
  n := 32
  q_pos := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ]
  lo_small := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ]
  hi_small := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ]
  lower_check := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ]
  upper_check := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ]

def log_second_lo : LogCertificate (691/1000) where
  lo := (-46201931901808394430777036779/125000000000000000000000000000)
  hi := (-369615455214467155446216294229/1000000000000000000000000000000)
  n := 32
  q_pos := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ]
  lo_small := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ]
  hi_small := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ]
  lower_check := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ]
  upper_check := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ]

def log_second_hi : LogCertificate (347/500) where
  lo := (-365283318475332550283065396211/1000000000000000000000000000000)
  hi := (-22830207404708284392691587263/62500000000000000000000000000)
  n := 32
  q_pos := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ]
  lo_small := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ]
  hi_small := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ]
  lower_check := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ]
  upper_check := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ]

def logX : (i : Row) → LogCertificate (xQ i)
 | .first => log_first_x
 | .second => log_second_x

def cutoffDenBox (i : Row) : Box := Box.sub
  (Box.scale (2*xQ i) (Box.sub (Box.point 1) (logX i).box)) (Box.point 1)
def cutoffBox (i : Row) : Box := Box.div (Box.point (1/1000)) (cutoffDenBox i)
def entryBox (i : Row) : Box := Box.scale (xQ i) (cutoffBox i)
def floorBox (i : Row) : Box := Box.scale (2*xQ i-(xQ i)^2) (cutoffBox i)
def dupBox (i : Row) : Box := Box.sub (floorBox i) (Box.point (1/1000))

theorem cutoffDenBox_ok (i : Row) :
    (cutoffDenBox i).Holds (2*x i*(1-Real.log (x i))-1) := by
  simpa [cutoffDenBox,x] using Box.sub_ok
    (Box.scale_ok (2*xQ i) (Box.sub_ok (Box.point_ok 1) (logX i).correct)) (Box.point_ok 1)
theorem cutoffBox_ok (i : Row) : (cutoffBox i).Holds (cutoff i) := by
  have hp : 0 < (cutoffDenBox i).lo := by cases i <;> norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, testValue, cutoffBox, cutoffDenBox, entryBox, floorBox, dupBox, logX, log_first_x, log_second_x, LogCertificate.box, xQ, xiQ, etaQ, kappaQ]
  simpa [cutoffBox,cutoff,delta] using Box.div_ok hp (Box.point_ok (1/1000)) (cutoffDenBox_ok i)
theorem cutoff_pos (i : Row) : 0 < cutoff i :=
  Box.lower_real (cutoffBox_ok i) (by cases i <;> norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, testValue, cutoffBox, cutoffDenBox, entryBox, floorBox, dupBox, logX, log_first_x, log_second_x, LogCertificate.box, xQ, xiQ, etaQ, kappaQ])
theorem cutoff_lt_one (i : Row) : cutoff i < 1 :=
  Box.upper_real (cutoffBox_ok i) (by cases i <;> norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, testValue, cutoffBox, cutoffDenBox, entryBox, floorBox, dupBox, logX, log_first_x, log_second_x, LogCertificate.box, xQ, xiQ, etaQ, kappaQ])
theorem cutoff_mem (i : Row) : cutoff i ∈ Icc 0 1 := ⟨(cutoff_pos i).le,(cutoff_lt_one i).le⟩
theorem cutoff_den_ne (i : Row) : 2*x i*(1-Real.log (x i))-1 ≠ 0 :=
  (Box.lower_real (cutoffDenBox_ok i) (by cases i <;> norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, testValue, cutoffBox, cutoffDenBox, entryBox, floorBox, dupBox, logX, log_first_x, log_second_x, LogCertificate.box, xQ, xiQ, etaQ, kappaQ]) : (0:ℝ) < _).ne'
theorem entryBox_ok (i : Row) : (entryBox i).Holds (entry i) := by
  simpa [entryBox,entry,x] using Box.scale_ok (xQ i) (cutoffBox_ok i)
theorem floorBox_ok (i : Row) : (floorBox i).Holds (limitingFloor i) := by
  rw [floor_simplify i (cutoff_pos i).ne']
  have h := Box.scale_ok (2*xQ i-(xQ i)^2) (cutoffBox_ok i)
  convert h using 1
  · rfl
  · dsimp [x]
    push_cast
    ring
theorem dupBox_ok (i : Row) : (dupBox i).Holds (limitDup i) := by
  rw [(duplicate_floor_identity i (cutoff_pos i).ne' (cutoff_den_ne i)).1]
  simpa [dupBox,delta] using Box.sub_ok (floorBox_ok i) (Box.point_ok (1/1000))

theorem cutoff_first_enclosure :
    ((107351067373897/100000000000000000):ℝ) < cutoff .first ∧ cutoff .first < (1073510673739/1000000000000000) := by
  exact ⟨Box.lower_real (cutoffBox_ok .first) (by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, testValue, cutoffBox, cutoffDenBox, entryBox, floorBox, dupBox, logX, log_first_x, log_second_x, LogCertificate.box, xQ, xiQ, etaQ, kappaQ]), Box.upper_real (cutoffBox_ok .first) (by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, testValue, cutoffBox, cutoffDenBox, entryBox, floorBox, dupBox, logX, log_first_x, log_second_x, LogCertificate.box, xQ, xiQ, etaQ, kappaQ])⟩

theorem floor_first_enclosure :
    ((25160406415757/25000000000000000):ℝ) < limitingFloor .first ∧ limitingFloor .first < (100641625663031/100000000000000000) := by
  exact ⟨Box.lower_real (floorBox_ok .first) (by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, testValue, cutoffBox, cutoffDenBox, entryBox, floorBox, dupBox, logX, log_first_x, log_second_x, LogCertificate.box, xQ, xiQ, etaQ, kappaQ]), Box.upper_real (floorBox_ok .first) (by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, testValue, cutoffBox, cutoffDenBox, entryBox, floorBox, dupBox, logX, log_first_x, log_second_x, LogCertificate.box, xQ, xiQ, etaQ, kappaQ])⟩

theorem dup_first_enclosure :
    ((160406415757/25000000000000000):ℝ) < limitDup .first ∧ limitDup .first < (641625663031/100000000000000000) := by
  exact ⟨Box.lower_real (dupBox_ok .first) (by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, testValue, cutoffBox, cutoffDenBox, entryBox, floorBox, dupBox, logX, log_first_x, log_second_x, LogCertificate.box, xQ, xiQ, etaQ, kappaQ]), Box.upper_real (dupBox_ok .first) (by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, testValue, cutoffBox, cutoffDenBox, entryBox, floorBox, dupBox, logX, log_first_x, log_second_x, LogCertificate.box, xQ, xiQ, etaQ, kappaQ])⟩

theorem cutoff_second_enclosure :
    ((11119204390639/10000000000000000):ℝ) < cutoff .second ∧ cutoff .second < (111192043906393/100000000000000000) := by
  exact ⟨Box.lower_real (cutoffBox_ok .second) (by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, testValue, cutoffBox, cutoffDenBox, entryBox, floorBox, dupBox, logX, log_first_x, log_second_x, LogCertificate.box, xQ, xiQ, etaQ, kappaQ]), Box.upper_real (cutoffBox_ok .second) (by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, testValue, cutoffBox, cutoffDenBox, entryBox, floorBox, dupBox, logX, log_first_x, log_second_x, LogCertificate.box, xQ, xiQ, etaQ, kappaQ])⟩

theorem floor_second_enclosure :
    ((20236951990963/20000000000000000):ℝ) < limitingFloor .second ∧ limitingFloor .second < (50592379977409/50000000000000000) := by
  exact ⟨Box.lower_real (floorBox_ok .second) (by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, testValue, cutoffBox, cutoffDenBox, entryBox, floorBox, dupBox, logX, log_first_x, log_second_x, LogCertificate.box, xQ, xiQ, etaQ, kappaQ]), Box.upper_real (floorBox_ok .second) (by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, testValue, cutoffBox, cutoffDenBox, entryBox, floorBox, dupBox, logX, log_first_x, log_second_x, LogCertificate.box, xQ, xiQ, etaQ, kappaQ])⟩

theorem dup_second_enclosure :
    ((236951990963/20000000000000000):ℝ) < limitDup .second ∧ limitDup .second < (592379977409/50000000000000000) := by
  exact ⟨Box.lower_real (dupBox_ok .second) (by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, testValue, cutoffBox, cutoffDenBox, entryBox, floorBox, dupBox, logX, log_first_x, log_second_x, LogCertificate.box, xQ, xiQ, etaQ, kappaQ]), Box.upper_real (dupBox_ok .second) (by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, testValue, cutoffBox, cutoffDenBox, entryBox, floorBox, dupBox, logX, log_first_x, log_second_x, LogCertificate.box, xQ, xiQ, etaQ, kappaQ])⟩

theorem cutoff_test_order : cutoff .first < testValue ∧ testValue < cutoff .second := by
  exact ⟨Box.upper_real (cutoffBox_ok .first) (by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, testValue, cutoffBox, cutoffDenBox, entryBox, floorBox, dupBox, logX, log_first_x, log_second_x, LogCertificate.box, xQ, xiQ, etaQ, kappaQ]), Box.lower_real (cutoffBox_ok .second) (by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, testValue, cutoffBox, cutoffDenBox, entryBox, floorBox, dupBox, logX, log_first_x, log_second_x, LogCertificate.box, xQ, xiQ, etaQ, kappaQ])⟩
theorem entry_test_order : entry .second < testValue :=
  Box.upper_real (entryBox_ok .second) (by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, testValue, cutoffBox, cutoffDenBox, entryBox, floorBox, dupBox, logX, log_first_x, log_second_x, LogCertificate.box, xQ, xiQ, etaQ, kappaQ])
theorem floors_order : limitingFloor .first < limitingFloor .second := by
  have h1 := Box.upper_real (floorBox_ok .first) (show ((floorBox .first).hi:ℝ) < (1009/1000000:ℝ) by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, testValue, cutoffBox, cutoffDenBox, entryBox, floorBox, dupBox, logX, log_first_x, log_second_x, LogCertificate.box, xQ, xiQ, etaQ, kappaQ])
  have h2 := Box.lower_real (floorBox_ok .second) (show (1009/1000000:ℝ) < ((floorBox .second).lo:ℝ) by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, testValue, cutoffBox, cutoffDenBox, entryBox, floorBox, dupBox, logX, log_first_x, log_second_x, LogCertificate.box, xQ, xiQ, etaQ, kappaQ])
  exact h1.trans h2
theorem strict_aggregates : limitDup .first < limitDup .second ∧
    limitCoverage .second < limitCoverage .first := by
  have h1 := duplicate_floor_identity .first (cutoff_pos .first).ne' (cutoff_den_ne .first)
  have h2 := duplicate_floor_identity .second (cutoff_pos .second).ne' (cutoff_den_ne .second)
  rw [h1.1,h2.1,h1.2,h2.2]
  constructor <;> linarith [floors_order]

noncomputable def testSuccess : ℝ := 1-(entry .second/testValue)^2
noncomputable def testMultiplicity : ℝ := 2/(1+entry .second/testValue)
def testRatioBox : Box := Box.scale (100000/109) (entryBox .second)
def testSuccessBox : Box := Box.sub (Box.point 1) (Box.mul testRatioBox testRatioBox)
def testMultiplicityBox : Box := Box.div (Box.point 2) (Box.add (Box.point 1) testRatioBox)
theorem testRatioBox_ok : testRatioBox.Holds (entry .second/testValue) := by
  simpa [testRatioBox,testValue,div_eq_mul_inv,mul_comm] using
    Box.scale_ok (100000/109) (entryBox_ok .second)
theorem testSuccessBox_ok : testSuccessBox.Holds testSuccess := by
  simpa [testSuccessBox,testSuccess,pow_two] using
    Box.sub_ok (Box.point_ok 1) (Box.mul_ok testRatioBox_ok testRatioBox_ok)
theorem testMultiplicityBox_ok : testMultiplicityBox.Holds testMultiplicity := by
  simpa only [testMultiplicity, testMultiplicityBox, Rat.cast_ofNat, Rat.cast_one] using Box.div_ok (by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, testValue, cutoffBox, cutoffDenBox, entryBox, floorBox, dupBox, logX, log_first_x, log_second_x, LogCertificate.box, xQ, xiQ, etaQ, kappaQ, testRatioBox, testSuccessBox, testMultiplicityBox]) (Box.point_ok 2) (Box.add_ok (Box.point_ok 1) testRatioBox_ok)
theorem pointwise_numbers :
    (49009354366/10^11:ℝ) < testSuccess ∧ testSuccess < 49009354367/10^11 ∧
    (116680848997/10^11:ℝ) < testMultiplicity ∧ testMultiplicity < 116680848998/10^11 := by
  exact ⟨Box.lower_real testSuccessBox_ok (by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, testValue, cutoffBox, cutoffDenBox, entryBox, floorBox, dupBox, logX, log_first_x, log_second_x, LogCertificate.box, xQ, xiQ, etaQ, kappaQ, testRatioBox, testSuccessBox, testMultiplicityBox]),Box.upper_real testSuccessBox_ok (by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, testValue, cutoffBox, cutoffDenBox, entryBox, floorBox, dupBox, logX, log_first_x, log_second_x, LogCertificate.box, xQ, xiQ, etaQ, kappaQ, testRatioBox, testSuccessBox, testMultiplicityBox]),
    Box.lower_real testMultiplicityBox_ok (by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, testValue, cutoffBox, cutoffDenBox, entryBox, floorBox, dupBox, logX, log_first_x, log_second_x, LogCertificate.box, xQ, xiQ, etaQ, kappaQ, testRatioBox, testSuccessBox, testMultiplicityBox]),Box.upper_real testMultiplicityBox_ok (by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, testValue, cutoffBox, cutoffDenBox, entryBox, floorBox, dupBox, logX, log_first_x, log_second_x, LogCertificate.box, xQ, xiQ, etaQ, kappaQ, testRatioBox, testSuccessBox, testMultiplicityBox])⟩

noncomputable def slopeRatioLower (i : Row) : ℝ :=
  ((1/50)*(1-x i)*Real.exp (-(7/5:ℝ))/(xi i*(x i/(kappa i+xi i*x i))))/(1/500)
def slopeRatioBox (i : Row) : Box := Box.scale
  (((1/50)*(1-xQ i)/(xiQ i*(xQ i/(kappaQ i+xiQ i*xQ i))))/(1/500))
  (expBox 32 (-7/5))
theorem slopeRatioBox_ok (i : Row) : (slopeRatioBox i).Holds (slopeRatioLower i) := by
  have h := Box.scale_ok
    (((1/50)*(1-xQ i)/(xiQ i*(xQ i/(kappaQ i+xiQ i*xQ i))))/(1/500))
    (expBox_ok 32 (-7/5) (by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, testValue, cutoffBox, cutoffDenBox, entryBox, floorBox, dupBox, logX, log_first_x, log_second_x, LogCertificate.box, xQ, xiQ, etaQ, kappaQ, testRatioBox, testSuccessBox, testMultiplicityBox, slopeRatioBox]))
  convert h using 1
  · rfl
  · dsimp [slopeRatioLower,x,xi,kappa]
    push_cast
    ring
 theorem physical_slope_numerics :
    (16211/10000:ℝ) < slopeRatioLower .first ∧
    (11303/5000:ℝ) < slopeRatioLower .second := by
  exact ⟨Box.lower_real (slopeRatioBox_ok .first) (by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, testValue, cutoffBox, cutoffDenBox, entryBox, floorBox, dupBox, logX, log_first_x, log_second_x, LogCertificate.box, xQ, xiQ, etaQ, kappaQ, testRatioBox, testSuccessBox, testMultiplicityBox, slopeRatioBox]),
    Box.lower_real (slopeRatioBox_ok .second) (by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point, Finset.sum_range_succ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, testValue, cutoffBox, cutoffDenBox, entryBox, floorBox, dupBox, logX, log_first_x, log_second_x, LogCertificate.box, xQ, xiQ, etaQ, kappaQ, testRatioBox, testSuccessBox, testMultiplicityBox, slopeRatioBox])⟩
end FCAppendix.Affine.Uniform07
