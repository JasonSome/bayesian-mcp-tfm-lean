import FCAppendix.Affine.Uniform07.ExactIntegral
import FCAppendix.Affine.Uniform07.ParameterCertificate

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section
namespace FCAppendix.Affine.Uniform06.LowChernoff
open MeasureTheory Set
open FCAppendix.Affine.Uniform07
open scoped BigOperators

def thetaQ : Row → ℚ | .first => 27/100 | .second => 23/100
def leftQ : Row → ℚ | .first => 3/4 | .second => 167/230
def rightQ : ℚ := 199/200
def aQ (i : Row) : ℚ := leftQ i + 1/200
def alphaQ (i : Row) : ℚ := 1/xiQ i
def betaQ (i : Row) : ℚ := (167/230)/xiQ i

def sourceTBox : Row → Box
 | .first => ⟨107351067373897/100000000000000000,
     1073510673739/1000000000000000⟩
 | .second => ⟨11119204390639/10000000000000000,
     111192043906393/100000000000000000⟩

theorem sourceTBox_ok (i : Row) : (sourceTBox i).Holds (cutoff i) := by
  cases i
  · convert! And.intro cutoff_first_enclosure.1.le cutoff_first_enclosure.2.le using 1;
      norm_num [sourceTBox, Box.Holds]
  · convert! And.intro cutoff_second_enclosure.1.le cutoff_second_enclosure.2.le using 1;
      norm_num [sourceTBox, Box.Holds]

theorem source_cutoff_for_surrogate (i : Row) :
    (aQ i : ℝ) = max (x i + 1/200) (1/200 + (501/1000)/(69/100)) := by
  cases i <;> norm_num [aQ, leftQ, x, xQ]

theorem full_floor_piece_bounds (i : Row) {y : ℝ}
    (hy : y ∈ Icc (leftQ i : ℝ) (rightQ : ℝ)) :
    pieceP (alphaQ i : ℝ) (betaQ i : ℝ) y ∈ Icc 0 1 := by
  have hl : (0 : ℝ) < leftQ i := by cases i <;> norm_num [leftQ]
  have hpos : 0 < y := hl.trans_le hy.1
  have ha : (0 : ℝ) ≤ alphaQ i := by
    cases i <;> norm_num [alphaQ, xiQ, etaQ]
  have ha1 : (0 : ℝ) ≤ (alphaQ i : ℝ) - 1 := by
    cases i <;> norm_num [alphaQ, xiQ, etaQ]
  have hlo : (betaQ i : ℝ) ≤ (alphaQ i : ℝ) * (leftQ i : ℝ) := by
    cases i <;> norm_num [betaQ, alphaQ, leftQ, xiQ, etaQ]
  have hhi : ((alphaQ i : ℝ) - 1) * (rightQ : ℝ) ≤ (betaQ i : ℝ) := by
    cases i <;> norm_num [betaQ, alphaQ, rightQ, xiQ, etaQ]
  have hdivLo : (betaQ i : ℝ) / y ≤ (alphaQ i : ℝ) := by
    apply (div_le_iff₀ hpos).2
    nlinarith [mul_le_mul_of_nonneg_left hy.1 ha]
  have hdivHi : (alphaQ i : ℝ) - 1 ≤ (betaQ i : ℝ) / y := by
    apply (le_div_iff₀ hpos).2
    exact (mul_le_mul_of_nonneg_left hy.2 ha1).trans hhi
  constructor <;> dsimp [pieceP] <;> linarith

def logLeft : (i : Row) → LogCertificate (leftQ i)
 | .first =>
    { lo := (-143841036225890463719609503/500000000000000000000000000)
      hi := (-2876820724517809274392190059/10000000000000000000000000000)
      n := 32
      q_pos := by norm_num [thetaQ, leftQ, aQ, alphaQ, betaQ, rightQ, sourceTBox, xiQ, etaQ, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      lo_small := by norm_num [thetaQ, leftQ, aQ, alphaQ, betaQ, rightQ, sourceTBox, xiQ, etaQ, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      hi_small := by norm_num [thetaQ, leftQ, aQ, alphaQ, betaQ, rightQ, sourceTBox, xiQ, etaQ, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      lower_check := by norm_num [thetaQ, leftQ, aQ, alphaQ, betaQ, rightQ, sourceTBox, xiQ, etaQ, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      upper_check := by norm_num [thetaQ, leftQ, aQ, alphaQ, betaQ, rightQ, sourceTBox, xiQ, etaQ, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box] }
 | .second =>
    { lo := (-1600427482532201337824967549/5000000000000000000000000000)
      hi := (-3200854965064402675649935097/10000000000000000000000000000)
      n := 32
      q_pos := by norm_num [thetaQ, leftQ, aQ, alphaQ, betaQ, rightQ, sourceTBox, xiQ, etaQ, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      lo_small := by norm_num [thetaQ, leftQ, aQ, alphaQ, betaQ, rightQ, sourceTBox, xiQ, etaQ, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      hi_small := by norm_num [thetaQ, leftQ, aQ, alphaQ, betaQ, rightQ, sourceTBox, xiQ, etaQ, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      lower_check := by norm_num [thetaQ, leftQ, aQ, alphaQ, betaQ, rightQ, sourceTBox, xiQ, etaQ, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      upper_check := by norm_num [thetaQ, leftQ, aQ, alphaQ, betaQ, rightQ, sourceTBox, xiQ, etaQ, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box] }

def logRight : (i : Row) → LogCertificate (rightQ)
 | .first =>
    { lo := (-5012541823544282043093739/1000000000000000000000000000)
      hi := (-50125418235442820430937389/10000000000000000000000000000)
      n := 32
      q_pos := by norm_num [thetaQ, leftQ, aQ, alphaQ, betaQ, rightQ, sourceTBox, xiQ, etaQ, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      lo_small := by norm_num [thetaQ, leftQ, aQ, alphaQ, betaQ, rightQ, sourceTBox, xiQ, etaQ, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      hi_small := by norm_num [thetaQ, leftQ, aQ, alphaQ, betaQ, rightQ, sourceTBox, xiQ, etaQ, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      lower_check := by norm_num [thetaQ, leftQ, aQ, alphaQ, betaQ, rightQ, sourceTBox, xiQ, etaQ, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      upper_check := by norm_num [thetaQ, leftQ, aQ, alphaQ, betaQ, rightQ, sourceTBox, xiQ, etaQ, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box] }
 | .second =>
    { lo := (-5012541823544282043093739/1000000000000000000000000000)
      hi := (-50125418235442820430937389/10000000000000000000000000000)
      n := 32
      q_pos := by norm_num [thetaQ, leftQ, aQ, alphaQ, betaQ, rightQ, sourceTBox, xiQ, etaQ, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      lo_small := by norm_num [thetaQ, leftQ, aQ, alphaQ, betaQ, rightQ, sourceTBox, xiQ, etaQ, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      hi_small := by norm_num [thetaQ, leftQ, aQ, alphaQ, betaQ, rightQ, sourceTBox, xiQ, etaQ, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      lower_check := by norm_num [thetaQ, leftQ, aQ, alphaQ, betaQ, rightQ, sourceTBox, xiQ, etaQ, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      upper_check := by norm_num [thetaQ, leftQ, aQ, alphaQ, betaQ, rightQ, sourceTBox, xiQ, etaQ, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box] }

def lowPieceBox (i : Row) : Box :=
  Box.inflate
    (pieceZBox 16 (alphaQ i) (betaQ i) (thetaQ i) (leftQ i) rightQ
      (logLeft i).box (logRight i).box)
    ((rightQ-leftQ i)*expErrorQ 16 (thetaQ i))

def rawSurrogateBox (i : Row) : Box :=
  Box.add (Box.mul (Box.sub (Box.point 1) (sourceTBox i))
    (expBox 16 (-thetaQ i/2)))
    (Box.mul (sourceTBox i) (Box.add (Box.point (aQ i)) (lowPieceBox i)))

def lowSurrogate (i : Row) : ℝ :=
  (1-cutoff i)*Real.exp (-(thetaQ i : ℝ)/2)+cutoff i*
    ((aQ i : ℝ)+pieceZ (alphaQ i : ℝ) (betaQ i : ℝ) (thetaQ i : ℝ)
      (leftQ i : ℝ) (rightQ : ℝ))

theorem lowPieceBox_ok (i : Row) :
    (lowPieceBox i).Holds
      (pieceZ (alphaQ i : ℝ) (betaQ i : ℝ) (thetaQ i : ℝ)
        (leftQ i : ℝ) (rightQ : ℝ)) := by
  apply Box.inflate_ok (pieceZBox_ok 16 (alphaQ i) (betaQ i) (thetaQ i)
    (leftQ i) rightQ (logLeft i).correct (logRight i).correct)
  have he := (piece_errors 16
    (by cases i <;> norm_num [leftQ] : (0 : ℝ) < leftQ i)
    (by cases i <;> norm_num [leftQ, rightQ] : (leftQ i : ℝ) ≤ rightQ)
    (by cases i <;> norm_num [thetaQ] : (0 : ℝ) ≤ thetaQ i)
    (by cases i <;> norm_num [thetaQ] : (thetaQ i : ℝ)/(16+1:ℝ) ≤ 1/2)
    (fun y hy => full_floor_piece_bounds i hy)).1
  simpa only [expErrorQ, Rat.cast_mul, Rat.cast_sub, Rat.cast_div,
    Rat.cast_ofNat, Rat.cast_pow, Rat.cast_natCast] using he

theorem rawSurrogateBox_ok (i : Row) :
    (rawSurrogateBox i).Holds (lowSurrogate i) := by
  have hx := expBox_ok 16 (-thetaQ i/2)
    (by cases i <;> norm_num [thetaQ])
  have h := Box.add_ok
    (Box.mul_ok (Box.sub_ok (Box.point_ok 1) (sourceTBox_ok i)) hx)
    (Box.mul_ok (sourceTBox_ok i) (Box.add_ok (Box.point_ok (aQ i))
      (lowPieceBox_ok i)))
  simpa only [rawSurrogateBox, lowSurrogate, Rat.cast_neg, Rat.cast_div,
    Rat.cast_ofNat, Rat.cast_one] using h

def surrogateBox : Row → Box
 | .first => ⟨(10922841000447918037/12500000000000000000), (1747654560071666997/2000000000000000000)⟩
 | .second => ⟨(44573158863441002857/50000000000000000000), (3565852709075280453/4000000000000000000)⟩

theorem surrogateBox_ok (i : Row) :
    (surrogateBox i).Holds (lowSurrogate i) := by
  apply Box.widen (rawSurrogateBox_ok i)
  · cases i <;> norm_num [surrogateBox, rawSurrogateBox, lowPieceBox, pieceZBox, momentBox, invMomentBox, logLeft, logRight, thetaQ, leftQ, aQ, alphaQ, betaQ, rightQ, sourceTBox, xiQ, etaQ, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
  · cases i <;> norm_num [surrogateBox, rawSurrogateBox, lowPieceBox, pieceZBox, momentBox, invMomentBox, logLeft, logRight, thetaQ, leftQ, aQ, alphaQ, betaQ, rightQ, sourceTBox, xiQ, etaQ, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]

def rankPBox (i : Row) : Box :=
  Box.scale (1/2) (Box.add (Box.point 1) (sourceTBox i))
def rankRatioOneBox (i : Row) : Box :=
  Box.div (Box.point (999/2000)) (rankPBox i)
def rankRatioTwoBox (i : Row) : Box :=
  Box.div (Box.point (1001/2000)) (Box.sub (Box.point 1) (rankPBox i))

theorem rankPBox_ok (i : Row) :
    (rankPBox i).Holds ((1+cutoff i)/2) := by
  simpa [rankPBox, div_eq_mul_inv, mul_comm] using
    Box.scale_ok (1/2) (Box.add_ok (Box.point_ok 1) (sourceTBox_ok i))

theorem rankRatioOneBox_ok (i : Row) :
    (rankRatioOneBox i).Holds (rho/((1+cutoff i)/2)) := by
  have hp : 0 < (rankPBox i).lo := by
    cases i <;> norm_num [rankPBox, sourceTBox, Box.scale, Box.mul, Box.point, Box.add]
  simpa [rankRatioOneBox, rho] using
    Box.div_ok hp (Box.point_ok (999/2000)) (rankPBox_ok i)

theorem rankRatioTwoBox_ok (i : Row) :
    (rankRatioTwoBox i).Holds ((1-rho)/(1-(1+cutoff i)/2)) := by
  have hp : 0 < (Box.sub (Box.point 1) (rankPBox i)).lo := by
    cases i <;> norm_num [rankPBox, sourceTBox, Box.sub, Box.neg,
      Box.scale, Box.mul, Box.point, Box.add]
  have h := Box.div_ok hp (Box.point_ok (1001/2000))
    (Box.sub_ok (Box.point_ok 1) (rankPBox_ok i))
  convert! h using 1; norm_num [rankRatioTwoBox, rho]

def logRankOneLo : (i : Row) → LogCertificate ((rankRatioOneBox i).lo)
 | .first =>
    { lo := (-10367176033938603435814197/5000000000000000000000000000)
      hi := (-20734352067877206871628393/10000000000000000000000000000)
      n := 32
      q_pos := by norm_num [rankRatioOneBox, rankPBox, sourceTBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      lo_small := by norm_num [rankRatioOneBox, rankPBox, sourceTBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      hi_small := by norm_num [rankRatioOneBox, rankPBox, sourceTBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      lower_check := by norm_num [rankRatioOneBox, rankPBox, sourceTBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      upper_check := by norm_num [rankRatioOneBox, rankPBox, sourceTBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box] }
 | .second =>
    { lo := (-2639753808726896612356183/1250000000000000000000000000)
      hi := (-21118030469815172898849463/10000000000000000000000000000)
      n := 32
      q_pos := by norm_num [rankRatioOneBox, rankPBox, sourceTBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      lo_small := by norm_num [rankRatioOneBox, rankPBox, sourceTBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      hi_small := by norm_num [rankRatioOneBox, rankPBox, sourceTBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      lower_check := by norm_num [rankRatioOneBox, rankPBox, sourceTBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      upper_check := by norm_num [rankRatioOneBox, rankPBox, sourceTBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box] }

def logRankOneHi : (i : Row) → LogCertificate ((rankRatioOneBox i).hi)
 | .first =>
    { lo := (-259179400848461339916703/125000000000000000000000000)
      hi := (-20734352067876907193336239/10000000000000000000000000000)
      n := 32
      q_pos := by norm_num [rankRatioOneBox, rankPBox, sourceTBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      lo_small := by norm_num [rankRatioOneBox, rankPBox, sourceTBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      hi_small := by norm_num [rankRatioOneBox, rankPBox, sourceTBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      lower_check := by norm_num [rankRatioOneBox, rankPBox, sourceTBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      upper_check := by norm_num [rankRatioOneBox, rankPBox, sourceTBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box] }
 | .second =>
    { lo := (-10559015234907436616027549/5000000000000000000000000000)
      hi := (-21118030469814873232055097/10000000000000000000000000000)
      n := 32
      q_pos := by norm_num [rankRatioOneBox, rankPBox, sourceTBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      lo_small := by norm_num [rankRatioOneBox, rankPBox, sourceTBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      hi_small := by norm_num [rankRatioOneBox, rankPBox, sourceTBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      lower_check := by norm_num [rankRatioOneBox, rankPBox, sourceTBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      upper_check := by norm_num [rankRatioOneBox, rankPBox, sourceTBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box] }

def logRankTwoLo : (i : Row) → LogCertificate ((rankRatioTwoBox i).lo)
 | .first =>
    { lo := (20735876321183642758092829/10000000000000000000000000000)
      hi := (2073587632118364275809283/1000000000000000000000000000)
      n := 32
      q_pos := by norm_num [rankRatioTwoBox, rankPBox, sourceTBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      lo_small := by norm_num [rankRatioTwoBox, rankPBox, sourceTBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      hi_small := by norm_num [rankRatioTwoBox, rankPBox, sourceTBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      lower_check := by norm_num [rankRatioTwoBox, rankPBox, sourceTBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      upper_check := by norm_num [rankRatioTwoBox, rankPBox, sourceTBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box] }
 | .second =>
    { lo := (21120394143085974329956077/10000000000000000000000000000)
      hi := (10560197071542987164978039/5000000000000000000000000000)
      n := 32
      q_pos := by norm_num [rankRatioTwoBox, rankPBox, sourceTBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      lo_small := by norm_num [rankRatioTwoBox, rankPBox, sourceTBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      hi_small := by norm_num [rankRatioTwoBox, rankPBox, sourceTBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      lower_check := by norm_num [rankRatioTwoBox, rankPBox, sourceTBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      upper_check := by norm_num [rankRatioTwoBox, rankPBox, sourceTBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box] }

def logRankTwoHi : (i : Row) → LogCertificate ((rankRatioTwoBox i).hi)
 | .first =>
    { lo := (2073587632118394308049213/1000000000000000000000000000)
      hi := (20735876321183943080492131/10000000000000000000000000000)
      n := 32
      q_pos := by norm_num [rankRatioTwoBox, rankPBox, sourceTBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      lo_small := by norm_num [rankRatioTwoBox, rankPBox, sourceTBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      hi_small := by norm_num [rankRatioTwoBox, rankPBox, sourceTBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      lower_check := by norm_num [rankRatioTwoBox, rankPBox, sourceTBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      upper_check := by norm_num [rankRatioTwoBox, rankPBox, sourceTBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box] }
 | .second =>
    { lo := (21120394143086274663903531/10000000000000000000000000000)
      hi := (5280098535771568665975883/2500000000000000000000000000)
      n := 32
      q_pos := by norm_num [rankRatioTwoBox, rankPBox, sourceTBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      lo_small := by norm_num [rankRatioTwoBox, rankPBox, sourceTBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      hi_small := by norm_num [rankRatioTwoBox, rankPBox, sourceTBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      lower_check := by norm_num [rankRatioTwoBox, rankPBox, sourceTBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      upper_check := by norm_num [rankRatioTwoBox, rankPBox, sourceTBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box] }

def logSurrogateLo : (i : Row) → LogCertificate ((surrogateBox i).lo)
 | .first =>
    { lo := (-1348725429523262113969205621/10000000000000000000000000000)
      hi := (-67436271476163105698460281/500000000000000000000000000)
      n := 32
      q_pos := by norm_num [surrogateBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      lo_small := by norm_num [surrogateBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      hi_small := by norm_num [surrogateBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      lower_check := by norm_num [surrogateBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      upper_check := by norm_num [surrogateBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box] }
 | .second =>
    { lo := (-1148911467733540363735866989/10000000000000000000000000000)
      hi := (-287227866933385090933966747/2500000000000000000000000000)
      n := 32
      q_pos := by norm_num [surrogateBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      lo_small := by norm_num [surrogateBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      hi_small := by norm_num [surrogateBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      lower_check := by norm_num [surrogateBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      upper_check := by norm_num [surrogateBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box] }

def logSurrogateHi : (i : Row) → LogCertificate ((surrogateBox i).hi)
 | .first =>
    { lo := (-1348725429523261478374491781/10000000000000000000000000000)
      hi := (-67436271476163073918724589/500000000000000000000000000)
      n := 32
      q_pos := by norm_num [surrogateBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      lo_small := by norm_num [surrogateBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      hi_small := by norm_num [surrogateBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      lower_check := by norm_num [surrogateBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      upper_check := by norm_num [surrogateBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box] }
 | .second =>
    { lo := (-574455733866769867160599357/5000000000000000000000000000)
      hi := (-1148911467733539734321198713/10000000000000000000000000000)
      n := 32
      q_pos := by norm_num [surrogateBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      lo_small := by norm_num [surrogateBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      hi_small := by norm_num [surrogateBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      lower_check := by norm_num [surrogateBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]
      upper_check := by norm_num [surrogateBox, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box] }

def rankI0 (i : Row) : ℝ :=
  rho*Real.log (rho/((1+cutoff i)/2))+
    (1-rho)*Real.log ((1-rho)/(1-(1+cutoff i)/2))

def rankI0Box (i : Row) : Box :=
  Box.add
    (Box.scale (999/2000) (logBox (rankRatioOneBox i)
      (logRankOneLo i) (logRankOneHi i)))
    (Box.scale (1001/2000) (logBox (rankRatioTwoBox i)
      (logRankTwoLo i) (logRankTwoHi i)))

def lowChernoffRate (i : Row) : ℝ :=
  -(thetaQ i : ℝ)*rho-Real.log (lowSurrogate i)

def lowChernoffRateBox (i : Row) : Box :=
  Box.sub (Box.point (-thetaQ i*(999/2000)))
    (logBox (surrogateBox i) (logSurrogateLo i) (logSurrogateHi i))

def gapBox (i : Row) : Box := Box.sub (lowChernoffRateBox i) (rankI0Box i)

theorem rankI0Box_ok (i : Row) : (rankI0Box i).Holds (rankI0 i) := by
  have h := Box.add_ok
    (Box.scale_ok (999/2000) (logBox_ok (logRankOneLo i) (logRankOneHi i)
      (rankRatioOneBox_ok i)))
    (Box.scale_ok (1001/2000) (logBox_ok (logRankTwoLo i) (logRankTwoHi i)
      (rankRatioTwoBox_ok i)))
  convert! h using 1; norm_num [rankI0Box, rankI0, rho]

theorem lowChernoffRateBox_ok (i : Row) :
    (lowChernoffRateBox i).Holds (lowChernoffRate i) := by
  have h := Box.sub_ok (Box.point_ok (-thetaQ i*(999/2000)))
    (logBox_ok (logSurrogateLo i) (logSurrogateHi i) (surrogateBox_ok i))
  simpa [lowChernoffRateBox, lowChernoffRate, rho] using h

theorem gapBox_ok (i : Row) :
    (gapBox i).Holds (lowChernoffRate i-rankI0 i) :=
  Box.sub_ok (lowChernoffRateBox_ok i) (rankI0Box_ok i)

def sourceGap : Row → ℝ
 | .first => 10747/2000000000
 | .second => 3893/1000000000

theorem certified_source_gaps (i : Row) :
    sourceGap i < lowChernoffRate i-rankI0 i := by
  apply Box.lower_real (gapBox_ok i)
  cases i <;> norm_num [gapBox, lowChernoffRateBox, rankI0Box, sourceGap, thetaQ, logBox, logSurrogateLo, logSurrogateHi, logRankOneLo, logRankOneHi, logRankTwoLo, logRankTwoHi, Box.Holds, Box.point, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.inv, Box.div, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial, LogCertificate.box]

theorem rank_rate_strictly_smaller (i : Row) : rankI0 i < lowChernoffRate i := by
  have hg := certified_source_gaps i
  have hp : 0 < sourceGap i := by cases i <;> norm_num [sourceGap]
  linarith

theorem dominated_mgf_rate_gap (i : Row) {Z : ℝ}
    (hZ : 0 < Z) (hdom : Z ≤ lowSurrogate i) :
    sourceGap i < -(thetaQ i : ℝ)*rho-Real.log Z-rankI0 i := by
  have hl := Real.log_le_log hZ hdom
  have hg := certified_source_gaps i
  unfold lowChernoffRate at hg
  linarith

end FCAppendix.Affine.Uniform06.LowChernoff
