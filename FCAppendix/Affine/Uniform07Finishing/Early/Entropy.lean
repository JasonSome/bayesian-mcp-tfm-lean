import FCAppendix.Affine.Uniform07Finishing.Early.Definitions

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Early
open FCAppendix.Affine.Uniform07 MeasureTheory Set

set_option maxHeartbeats 12000000
set_option maxRecDepth 100000

def entropyBox (a : ℚ) (b : Box)
    (l₁ : LogCertificate (Box.div (Box.point a) b).lo)
    (h₁ : LogCertificate (Box.div (Box.point a) b).hi)
    (l₂ : LogCertificate (Box.div (Box.point (1-a)) (Box.sub (Box.point 1) b)).lo)
    (h₂ : LogCertificate (Box.div (Box.point (1-a)) (Box.sub (Box.point 1) b)).hi) : Box :=
  Box.add (Box.scale a (logBox (Box.div (Box.point a) b) l₁ h₁))
    (Box.scale (1-a) (logBox (Box.div (Box.point (1-a))
      (Box.sub (Box.point 1) b)) l₂ h₂))

theorem entropyBox_ok (a : ℚ) (b : Box)
    (l₁ : LogCertificate (Box.div (Box.point a) b).lo)
    (h₁ : LogCertificate (Box.div (Box.point a) b).hi)
    (l₂ : LogCertificate (Box.div (Box.point (1-a)) (Box.sub (Box.point 1) b)).lo)
    (h₂ : LogCertificate (Box.div (Box.point (1-a)) (Box.sub (Box.point 1) b)).hi)
    (hb0 : 0 < b.lo) (hb1 : b.hi < 1) {y : ℝ} (hy : b.Holds y) :
    (entropyBox a b l₁ h₁ l₂ h₂).Holds (binaryEntropy (a : ℝ) y) := by
  have hc : 0 < (Box.sub (Box.point 1) b).lo := by
    dsimp [Box.sub, Box.add, Box.neg, Box.point]
    linarith
  have hq₁ := Box.div_ok hb0 (Box.point_ok a) hy
  have hq₂ := Box.div_ok hc (Box.point_ok (1-a)) (Box.sub_ok (Box.point_ok 1) hy)
  have h := Box.add_ok (Box.scale_ok a (logBox_ok l₁ h₁ hq₁))
    (Box.scale_ok (1-a) (logBox_ok l₂ h₂ hq₂))
  simpa only [entropyBox, binaryEntropy, Rat.cast_sub, Rat.cast_one] using h

def firstI0ParameterBox : Box := Box.scale (1/2) (Box.add (Box.point 1) (earlyCutoffBox .first))
theorem firstI0ParameterBox_ok : firstI0ParameterBox.Holds ((1 + cutoff .first) / 2) := by
  simpa [firstI0ParameterBox,div_eq_mul_inv,mul_comm] using
    Box.scale_ok (1/2) (Box.add_ok (Box.point_ok 1) (earlyCutoffBox_ok .first))

def firstI0Log1lo : LogCertificate ((Box.div (Box.point (999 / 2000)) firstI0ParameterBox).lo) where
  lo := (-414687041357544137433 / 200000000000000000000000)
  hi := (-51835880169693017179 / 25000000000000000000000)
  n := 24
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [firstI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [firstI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [firstI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [firstI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [firstI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]

def firstI0Log1hi : LogCertificate ((Box.div (Box.point (999 / 2000)) firstI0ParameterBox).hi) where
  lo := (-259179400848461339917 / 125000000000000000000000)
  hi := (-2073435206787690719331 / 1000000000000000000000000)
  n := 24
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [firstI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [firstI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [firstI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [firstI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [firstI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]

def firstI0Log2lo : LogCertificate ((Box.div (Box.point (1-(999 / 2000))) (Box.sub (Box.point 1) firstI0ParameterBox)).lo) where
  lo := (2073587632118364275807 / 1000000000000000000000000)
  hi := (518396908029591068953 / 250000000000000000000000)
  n := 24
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [firstI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [firstI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [firstI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [firstI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [firstI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]

def firstI0Log2hi : LogCertificate ((Box.div (Box.point (1-(999 / 2000))) (Box.sub (Box.point 1) firstI0ParameterBox)).hi) where
  lo := (2073587632118394308047 / 1000000000000000000000000)
  hi := (518396908029598577013 / 250000000000000000000000)
  n := 24
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [firstI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [firstI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [firstI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [firstI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [firstI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]

def firstI0Box : Box := entropyBox (999 / 2000) firstI0ParameterBox firstI0Log1lo firstI0Log1hi firstI0Log2lo firstI0Log2hi
theorem firstI0Box_ok : firstI0Box.Holds (binaryEntropy ((999 / 2000) : ℝ) ((1 + cutoff .first) / 2)) := by
  convert! entropyBox_ok (999 / 2000) firstI0ParameterBox firstI0Log1lo firstI0Log1hi firstI0Log2lo firstI0Log2hi
    (by norm_num [firstI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum])
    (by norm_num [firstI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum]) firstI0ParameterBox_ok using 1; norm_num

def firstI0RoundedBox : Box := ⟨(107486204238741 / 50000000000000000000), (42994481696097 / 20000000000000000000)⟩
theorem firstI0RoundedBox_ok : firstI0RoundedBox.Holds
    (binaryEntropy ((999 / 2000) : ℝ) ((1 + cutoff .first) / 2)) := by
  apply Box.widen firstI0Box_ok <;>
    norm_num [firstI0RoundedBox, firstI0Box, entropyBox, logBox,
      firstI0Log1lo, firstI0Log1hi, firstI0Log2lo, firstI0Log2hi, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum]

def firstLowerParameterBox : Box := earlyCutoffBox .first
theorem firstLowerParameterBox_ok : firstLowerParameterBox.Holds (cutoff .first) := by
  exact earlyCutoffBox_ok .first

def firstLowerLog1lo : LogCertificate ((Box.div (Box.point (1 / 1000)) firstLowerParameterBox).lo) where
  lo := (-70934281220663468015039 / 1000000000000000000000000)
  hi := (-35467140610331734007517 / 500000000000000000000000)
  n := 24
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [firstLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [firstLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [firstLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [firstLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [firstLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]

def firstLowerLog1hi : LogCertificate ((Box.div (Box.point (1 / 1000)) firstLowerParameterBox).hi) where
  lo := (-35467140610317761160889 / 500000000000000000000000)
  hi := (-70934281220635522321773 / 1000000000000000000000000)
  n := 24
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [firstLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [firstLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [firstLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [firstLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [firstLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]

def firstLowerLog2lo : LogCertificate ((Box.div (Box.point (1-(1 / 1000))) (Box.sub (Box.point 1) firstLowerParameterBox)).lo) where
  lo := (36793482725648804427 / 500000000000000000000000)
  hi := (73586965451297608859 / 1000000000000000000000000)
  n := 24
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [firstLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [firstLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [firstLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [firstLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [firstLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]

def firstLowerLog2hi : LogCertificate ((Box.div (Box.point (1-(1 / 1000))) (Box.sub (Box.point 1) firstLowerParameterBox)).hi) where
  lo := (36793482725663820547 / 500000000000000000000000)
  hi := (73586965451327641099 / 1000000000000000000000000)
  n := 24
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [firstLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [firstLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [firstLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [firstLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [firstLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]

def firstLowerBox : Box := entropyBox (1 / 1000) firstLowerParameterBox firstLowerLog1lo firstLowerLog1hi firstLowerLog2lo firstLowerLog2hi
theorem firstLowerBox_ok : firstLowerBox.Holds (binaryEntropy ((1 / 1000) : ℝ) (cutoff .first)) := by
  convert! entropyBox_ok (1 / 1000) firstLowerParameterBox firstLowerLog1lo firstLowerLog1hi firstLowerLog2lo firstLowerLog2hi
    (by norm_num [firstLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum])
    (by norm_num [firstLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum]) firstLowerParameterBox_ok using 1; norm_num

def firstLowerRoundedBox : Box := ⟨(257909726518283 / 100000000000000000000), (257909726524081 / 100000000000000000000)⟩
theorem firstLowerRoundedBox_ok : firstLowerRoundedBox.Holds
    (binaryEntropy ((1 / 1000) : ℝ) (cutoff .first)) := by
  apply Box.widen firstLowerBox_ok <;>
    norm_num [firstLowerRoundedBox, firstLowerBox, entropyBox, logBox,
      firstLowerLog1lo, firstLowerLog1hi, firstLowerLog2lo, firstLowerLog2hi, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum]

def firstJParameterBox : Box := Box.scale (xQ .first + 1/200) (earlyCutoffBox .first)
theorem firstJParameterBox_ok : firstJParameterBox.Holds (categoryCutoff .first) := by
  have h := Box.scale_ok (xQ .first + 1/200) (earlyCutoffBox_ok .first)
  convert! h using 1; norm_num [categoryCutoff, entry, x, firstJParameterBox]; ring

def firstJLog1lo : LogCertificate ((Box.div (Box.point (1 / 1000)) firstJParameterBox).lo) where
  lo := (10505162425622444032097 / 50000000000000000000000)
  hi := (42020649702489776128389 / 200000000000000000000000)
  n := 24
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [firstJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [firstJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [firstJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [firstJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [firstJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]

def firstJLog1hi : LogCertificate ((Box.div (Box.point (1 / 1000)) firstJParameterBox).hi) where
  lo := (262629060640596032919 / 1250000000000000000000)
  hi := (42020649702495365267041 / 200000000000000000000000)
  n := 24
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [firstJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [firstJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [firstJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [firstJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [firstJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]

def firstJLog2lo : LogCertificate ((Box.div (Box.point (1-(1 / 1000))) (Box.sub (Box.point 1) firstJParameterBox)).lo) where
  lo := (-23708892718654248167 / 125000000000000000000000)
  hi := (-189671141749233985331 / 1000000000000000000000000)
  n := 24
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [firstJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [firstJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [firstJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [firstJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [firstJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]

def firstJLog2hi : LogCertificate ((Box.div (Box.point (1-(1 / 1000))) (Box.sub (Box.point 1) firstJParameterBox)).hi) where
  lo := (-189671141749211316963 / 1000000000000000000000000)
  hi := (-94835570874605658479 / 500000000000000000000000)
  n := 24
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [firstJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [firstJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [firstJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [firstJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [firstJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]

def firstJBox : Box := entropyBox (1 / 1000) firstJParameterBox firstJLog1lo firstJLog1hi firstJLog2lo firstJLog2hi
theorem firstJBox_ok : firstJBox.Holds (binaryEntropy ((1 / 1000) : ℝ) (categoryCutoff .first)) := by
  convert! entropyBox_ok (1 / 1000) firstJParameterBox firstJLog1lo firstJLog1hi firstJLog2lo firstJLog2hi
    (by norm_num [firstJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum])
    (by norm_num [firstJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum]) firstJParameterBox_ok using 1; norm_num

def firstJRoundedBox : Box := ⟨(2062177790496411 / 100000000000000000000), (1031088895250737 / 50000000000000000000)⟩
theorem firstJRoundedBox_ok : firstJRoundedBox.Holds
    (binaryEntropy ((1 / 1000) : ℝ) (categoryCutoff .first)) := by
  apply Box.widen firstJBox_ok <;>
    norm_num [firstJRoundedBox, firstJBox, entropyBox, logBox,
      firstJLog1lo, firstJLog1hi, firstJLog2lo, firstJLog2hi, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum]

def secondI0ParameterBox : Box := Box.scale (1/2) (Box.add (Box.point 1) (earlyCutoffBox .second))
theorem secondI0ParameterBox_ok : secondI0ParameterBox.Holds ((1 + cutoff .second) / 2) := by
  simpa [secondI0ParameterBox,div_eq_mul_inv,mul_comm] using
    Box.scale_ok (1/2) (Box.add_ok (Box.point_ok 1) (earlyCutoffBox_ok .second))

def secondI0Log1lo : LogCertificate ((Box.div (Box.point (999 / 2000)) secondI0ParameterBox).lo) where
  lo := (-2111803046981517289887 / 1000000000000000000000000)
  hi := (-1055901523490758644941 / 500000000000000000000000)
  n := 24
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [secondI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [secondI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [secondI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [secondI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [secondI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]

def secondI0Log1hi : LogCertificate ((Box.div (Box.point (999 / 2000)) secondI0ParameterBox).hi) where
  lo := (-263975380872685915401 / 125000000000000000000000)
  hi := (-2111803046981487323203 / 1000000000000000000000000)
  n := 24
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [secondI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [secondI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [secondI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [secondI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [secondI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]

def secondI0Log2lo : LogCertificate ((Box.div (Box.point (1-(999 / 2000))) (Box.sub (Box.point 1) secondI0ParameterBox)).lo) where
  lo := (2112039414308597432993 / 1000000000000000000000000)
  hi := (1056019707154298716499 / 500000000000000000000000)
  n := 24
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [secondI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [secondI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [secondI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [secondI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [secondI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]

def secondI0Log2hi : LogCertificate ((Box.div (Box.point (1-(999 / 2000))) (Box.sub (Box.point 1) secondI0ParameterBox)).hi) where
  lo := (528009853577156866597 / 250000000000000000000000)
  hi := (2112039414308627466393 / 1000000000000000000000000)
  n := 24
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [secondI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [secondI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [secondI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [secondI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [secondI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]

def secondI0Box : Box := entropyBox (999 / 2000) secondI0ParameterBox secondI0Log1lo secondI0Log1hi secondI0Log2lo secondI0Log2hi
theorem secondI0Box_ok : secondI0Box.Holds (binaryEntropy ((999 / 2000) : ℝ) ((1 + cutoff .second) / 2)) := by
  convert! entropyBox_ok (999 / 2000) secondI0ParameterBox secondI0Log1lo secondI0Log1hi secondI0Log2lo secondI0Log2hi
    (by norm_num [secondI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum])
    (by norm_num [secondI0ParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum]) secondI0ParameterBox_ok using 1; norm_num

def secondI0RoundedBox : Box := ⟨(223010489418511 / 100000000000000000000), (111505244710757 / 50000000000000000000)⟩
theorem secondI0RoundedBox_ok : secondI0RoundedBox.Holds
    (binaryEntropy ((999 / 2000) : ℝ) ((1 + cutoff .second) / 2)) := by
  apply Box.widen secondI0Box_ok <;>
    norm_num [secondI0RoundedBox, secondI0Box, entropyBox, logBox,
      secondI0Log1lo, secondI0Log1hi, secondI0Log2lo, secondI0Log2hi, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum]

def secondLowerParameterBox : Box := earlyCutoffBox .second
theorem secondLowerParameterBox_ok : secondLowerParameterBox.Holds (cutoff .second) := by
  exact earlyCutoffBox_ok .second

def secondLowerLog1lo : LogCertificate ((Box.div (Box.point (1 / 1000)) secondLowerParameterBox).lo) where
  lo := (-106088645664359198723707 / 1000000000000000000000000)
  hi := (-53044322832179599361851 / 500000000000000000000000)
  n := 24
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [secondLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [secondLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [secondLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [secondLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [secondLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]

def secondLowerLog1hi : LogCertificate ((Box.div (Box.point (1 / 1000)) secondLowerParameterBox).hi) where
  lo := (-53044322832166109188031 / 500000000000000000000000)
  hi := (-106088645664332218376057 / 1000000000000000000000000)
  n := 24
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [secondLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [secondLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [secondLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [secondLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [secondLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]

def secondLowerLog2lo : LogCertificate ((Box.div (Box.point (1-(1 / 1000))) (Box.sub (Box.point 1) secondLowerParameterBox)).lo) where
  lo := (112038747641530766041 / 1000000000000000000000000)
  hi := (56019373820765383023 / 500000000000000000000000)
  n := 24
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [secondLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [secondLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [secondLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [secondLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [secondLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]

def secondLowerLog2hi : LogCertificate ((Box.div (Box.point (1-(1 / 1000))) (Box.sub (Box.point 1) secondLowerParameterBox)).hi) where
  lo := (22407749528312159887 / 200000000000000000000000)
  hi := (1400484345519509993 / 12500000000000000000000)
  n := 24
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [secondLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [secondLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [secondLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [secondLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [secondLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]

def secondLowerBox : Box := entropyBox (1 / 1000) secondLowerParameterBox secondLowerLog1lo secondLowerLog1hi secondLowerLog2lo secondLowerLog2hi
theorem secondLowerBox_ok : secondLowerBox.Holds (binaryEntropy ((1 / 1000) : ℝ) (cutoff .second)) := by
  convert! entropyBox_ok (1 / 1000) secondLowerParameterBox secondLowerLog1lo secondLowerLog1hi secondLowerLog2lo secondLowerLog2hi
    (by norm_num [secondLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum])
    (by norm_num [secondLowerParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum]) secondLowerParameterBox_ok using 1; norm_num

def secondLowerRoundedBox : Box := ⟨(291903161476501 / 50000000000000000000), (36487895184919 / 6250000000000000000)⟩
theorem secondLowerRoundedBox_ok : secondLowerRoundedBox.Holds
    (binaryEntropy ((1 / 1000) : ℝ) (cutoff .second)) := by
  apply Box.widen secondLowerBox_ok <;>
    norm_num [secondLowerRoundedBox, secondLowerBox, entropyBox, logBox,
      secondLowerLog1lo, secondLowerLog1hi, secondLowerLog2lo, secondLowerLog2hi, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum]

def secondJParameterBox : Box := Box.scale (xQ .second + 1/200) (earlyCutoffBox .second)
theorem secondJParameterBox_ok : secondJParameterBox.Holds (categoryCutoff .second) := by
  have h := Box.scale_ok (xQ .second + 1/200) (earlyCutoffBox_ok .second)
  convert! h using 1; norm_num [categoryCutoff, entry, x, firstJParameterBox, secondJParameterBox]; ring

def secondJLog1lo : LogCertificate ((Box.div (Box.point (1 / 1000)) secondJParameterBox).lo) where
  lo := (7608400953297162516041 / 31250000000000000000000)
  hi := (243468830505509200513317 / 1000000000000000000000000)
  n := 24
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [secondJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [secondJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [secondJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [secondJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [secondJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]

def secondJLog1hi : LogCertificate ((Box.div (Box.point (1 / 1000)) secondJParameterBox).hi) where
  lo := (243468830505536180860957 / 1000000000000000000000000)
  hi := (121734415252768090430481 / 500000000000000000000000)
  n := 24
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [secondJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [secondJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [secondJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [secondJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [secondJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]

def secondJLog2lo : LogCertificate ((Box.div (Box.point (1-(1 / 1000))) (Box.sub (Box.point 1) secondJParameterBox)).lo) where
  lo := (-108144505354139237021 / 500000000000000000000000)
  hi := (-216289010708278474037 / 1000000000000000000000000)
  n := 24
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [secondJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [secondJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [secondJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [secondJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [secondJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]

def secondJLog2hi : LogCertificate ((Box.div (Box.point (1-(1 / 1000))) (Box.sub (Box.point 1) secondJParameterBox)).hi) where
  lo := (-4325780214165146149 / 20000000000000000000000)
  hi := (-43257802141651461489 / 200000000000000000000000)
  n := 24
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [secondJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [secondJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [secondJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [secondJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [secondJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]

def secondJBox : Box := entropyBox (1 / 1000) secondJParameterBox secondJLog1lo secondJLog1hi secondJLog2lo secondJLog2hi
theorem secondJBox_ok : secondJBox.Holds (binaryEntropy ((1 / 1000) : ℝ) (categoryCutoff .second)) := by
  convert! entropyBox_ok (1 / 1000) secondJParameterBox secondJLog1lo secondJLog1hi secondJLog2lo secondJLog2hi
    (by norm_num [secondJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum])
    (by norm_num [secondJParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum]) secondJParameterBox_ok using 1; norm_num

def secondJRoundedBox : Box := ⟨(2739610880793899 / 100000000000000000000), (547922176159743 / 20000000000000000000)⟩
theorem secondJRoundedBox_ok : secondJRoundedBox.Holds
    (binaryEntropy ((1 / 1000) : ℝ) (categoryCutoff .second)) := by
  apply Box.widen secondJBox_ok <;>
    norm_num [secondJRoundedBox, secondJBox, entropyBox, logBox,
      secondJLog1lo, secondJLog1hi, secondJLog2lo, secondJLog2hi, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum]

def imbalanceParameterBox : Box := Box.point (1/2)
theorem imbalanceParameterBox_ok : imbalanceParameterBox.Holds (1/2 : ℝ) := by
  norm_num [imbalanceParameterBox, Box.Holds, Box.point]

def imbalanceLog1lo : LogCertificate ((Box.div (Box.point (997 / 1998)) imbalanceParameterBox).lo) where
  lo := (-200400868671518831311 / 100000000000000000000000)
  hi := (-400801737343037662621 / 200000000000000000000000)
  n := 24
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [imbalanceParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [imbalanceParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [imbalanceParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [imbalanceParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [imbalanceParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]

def imbalanceLog1hi : LogCertificate ((Box.div (Box.point (997 / 1998)) imbalanceParameterBox).hi) where
  lo := (-200400868671518831311 / 100000000000000000000000)
  hi := (-400801737343037662621 / 200000000000000000000000)
  n := 24
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [imbalanceParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [imbalanceParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [imbalanceParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [imbalanceParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [imbalanceParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]

def imbalanceLog2lo : LogCertificate ((Box.div (Box.point (1-(997 / 1998))) (Box.sub (Box.point 1) imbalanceParameterBox)).lo) where
  lo := (40000013333341333339 / 20000000000000000000000)
  hi := (400000133333413333391 / 200000000000000000000000)
  n := 24
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [imbalanceParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [imbalanceParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [imbalanceParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [imbalanceParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [imbalanceParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]

def imbalanceLog2hi : LogCertificate ((Box.div (Box.point (1-(997 / 1998))) (Box.sub (Box.point 1) imbalanceParameterBox)).hi) where
  lo := (40000013333341333339 / 20000000000000000000000)
  hi := (400000133333413333391 / 200000000000000000000000)
  n := 24
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [imbalanceParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [imbalanceParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [imbalanceParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [imbalanceParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [imbalanceParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]

def imbalanceBox : Box := entropyBox (997 / 1998) imbalanceParameterBox imbalanceLog1lo imbalanceLog1hi imbalanceLog2lo imbalanceLog2hi
theorem imbalanceBox_ok : imbalanceBox.Holds (binaryEntropy ((997 / 1998) : ℝ) (1/2 : ℝ)) := by
  convert! entropyBox_ok (997 / 1998) imbalanceParameterBox imbalanceLog1lo imbalanceLog1hi imbalanceLog2lo imbalanceLog2hi
    (by norm_num [imbalanceParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum])
    (by norm_num [imbalanceParameterBox, earlyCutoffBox, xQ, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum]) imbalanceParameterBox_ok using 1; norm_num

def imbalanceRoundedBox : Box := ⟨(200400734669217 / 100000000000000000000), (10020036733461 / 5000000000000000000)⟩
theorem imbalanceRoundedBox_ok : imbalanceRoundedBox.Holds
    (binaryEntropy ((997 / 1998) : ℝ) (1/2 : ℝ)) := by
  apply Box.widen imbalanceBox_ok <;>
    norm_num [imbalanceRoundedBox, imbalanceBox, entropyBox, logBox,
      imbalanceLog1lo, imbalanceLog1hi, imbalanceLog2lo, imbalanceLog2hi, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum]

def sourceI0Box : Row → Box
  | .first => firstI0RoundedBox
  | .second => secondI0RoundedBox
def sourceI1Box : Row → Box
  | .first => Box.add firstLowerRoundedBox (Box.scale (999/1000) imbalanceRoundedBox)
  | .second => Box.add secondLowerRoundedBox (Box.scale (999/1000) imbalanceRoundedBox)
def sourceJBox : Row → Box
  | .first => firstJRoundedBox
  | .second => secondJRoundedBox

theorem sourceI0Box_ok (i : Row) : (sourceI0Box i).Holds (atomRateI0 i) := by
  cases i
  · simpa [sourceI0Box, atomRateI0, rho] using firstI0RoundedBox_ok
  · simpa [sourceI0Box, atomRateI0, rho] using secondI0RoundedBox_ok

theorem sourceI1Box_ok (i : Row) : (sourceI1Box i).Holds (atomRateI1 i) := by
  cases i
  · have h := Box.add_ok firstLowerRoundedBox_ok
      (Box.scale_ok (999/1000) imbalanceRoundedBox_ok)
    norm_num [sourceI1Box, atomRateI1, delta] at h ⊢
    exact h
  · have h := Box.add_ok secondLowerRoundedBox_ok
      (Box.scale_ok (999/1000) imbalanceRoundedBox_ok)
    norm_num [sourceI1Box, atomRateI1, delta] at h ⊢
    exact h

theorem sourceJBox_ok (i : Row) : (sourceJBox i).Holds (atomRateJ i) := by
  cases i
  · simpa [sourceJBox, atomRateJ, delta] using firstJRoundedBox_ok
  · simpa [sourceJBox, atomRateJ, delta] using secondJRoundedBox_ok

theorem atom_entropy_guards (i : Row) :
    (atomMarginQ i : ℝ) < atomRateJ i - atomRateI0 i - atomRateI1 i ∧
    2 * atomRateI0 i < atomRateJ i := by
  constructor
  · apply Box.lower_real (Box.sub_ok (Box.sub_ok (sourceJBox_ok i)
      (sourceI0Box_ok i)) (sourceI1Box_ok i))
    cases i <;> norm_num [atomMarginQ, sourceJBox, sourceI0Box, sourceI1Box,
      firstJRoundedBox, secondJRoundedBox, firstI0RoundedBox, secondI0RoundedBox,
      firstLowerRoundedBox, secondLowerRoundedBox, imbalanceRoundedBox,
      Box.sub, Box.add, Box.neg, Box.mul, Box.scale, Box.point]
  · have h : 0 < atomRateJ i - 2 * atomRateI0 i := by
      apply Box.lower_real (Box.sub_ok (sourceJBox_ok i)
        (Box.scale_ok 2 (sourceI0Box_ok i)))
      cases i <;> norm_num [sourceJBox, sourceI0Box,
        firstJRoundedBox, secondJRoundedBox, firstI0RoundedBox, secondI0RoundedBox,
        Box.sub, Box.add, Box.neg, Box.mul, Box.scale, Box.point]
    linarith

end FCAppendix.Affine.Uniform07Finishing.Early
