import FCAppendix.Affine.Uniform07Finishing.Early.LogData
import FCAppendix.Affine.Uniform07Finishing.Early.Entropy

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Early
open FCAppendix.Affine.Uniform07 MeasureTheory Set

set_option maxHeartbeats 12000000
set_option maxRecDepth 100000

private def reindexLog {q r : ℚ} (C : LogCertificate q) (h : q=r) : LogCertificate r where
  lo := C.lo
  hi := C.hi
  n := C.n
  q_pos := by rw [←h]; exact C.q_pos
  lo_small := C.lo_small
  hi_small := C.hi_small
  lower_check := by rw [←h]; exact C.lower_check
  upper_check := by rw [←h]; exact C.upper_check

theorem low_piece_bounds (i : Row) {y : ℝ}
    (hy : y ∈ Icc (lowPieceLeftQ i : ℝ) (lowPieceRightQ : ℝ)) :
    pieceP (lowPieceAQ i) (lowPieceCQ i) y ∈ Icc 0 1 := by
  have hy0 : 0 < y := by
    cases i <;> norm_num [lowPieceLeftQ, lowStartQ, lowPieceRightQ, xQ] at hy <;>
      linarith [hy.1]
  have hx0 : 0 < xi i := xi_pos i
  have hid : pieceP (lowPieceAQ i) (lowPieceCQ i) y =
      (y - 501/690) / (xi i * y) := by
    cases i <;> norm_num [pieceP, lowPieceAQ, lowPieceCQ, xi, xiQ, etaQ]
    all_goals (field_simp [hy0.ne']; ring)
  rw [hid]
  constructor
  · apply div_nonneg _ (mul_nonneg hx0.le hy0.le)
    cases i <;> norm_num [lowPieceLeftQ, lowStartQ, xQ] at hy <;> linarith [hy.1]
  · rw [div_le_iff₀ (mul_pos hx0 hy0)]
    cases i <;> norm_num [lowPieceRightQ, xi, xiQ, etaQ] at * <;> nlinarith [hy.2]

theorem low_transform_source_integral (i : Row) :
    lowTransform i = (1-cutoff i) * Real.exp (-(lowThetaQ i : ℝ)/2) + cutoff i *
      ((lowStartQ i : ℝ) + ∫ y in (lowStartQ i : ℝ)..1,
        Real.exp (-(lowThetaQ i : ℝ) *
          ((1 - (501/1000 : ℝ)/((69/100 : ℝ)*(y-1/200))) / xi i))) := by
  have htranslate := intervalIntegral.integral_comp_sub_right
    (fun y : ℝ => Real.exp (-(lowThetaQ i : ℝ) *
      pieceP (lowPieceAQ i) (lowPieceCQ i) y)) (1/200 : ℝ)
    (a := (lowStartQ i : ℝ)) (b := 1)
  have hfun (y : ℝ) :
      pieceP (lowPieceAQ i) (lowPieceCQ i) (y-1/200) =
      (1 - (501/1000 : ℝ)/((69/100 : ℝ)*(y-1/200))) / xi i := by
    cases i <;> norm_num [pieceP, lowPieceAQ, lowPieceCQ, xi, xiQ, etaQ,
      div_eq_mul_inv, mul_inv_rev]
    all_goals ring
  simp_rw [hfun] at htranslate
  have hpiece : pieceZ (lowPieceAQ i) (lowPieceCQ i) (lowThetaQ i)
      (lowPieceLeftQ i) lowPieceRightQ =
      ∫ y in (lowStartQ i : ℝ)..1, Real.exp (-(lowThetaQ i : ℝ)*
        ((1-(501/1000 : ℝ)/((69/100 : ℝ)*(y-1/200)))/xi i)) := by
    simpa only [pieceZ, lowPieceLeftQ, lowPieceRightQ, Rat.cast_sub, Rat.cast_div,
      Rat.cast_one, Rat.cast_ofNat, show (1:ℝ)-1/200 = 199/200 by norm_num]
      using htranslate.symm
  rw [lowTransform, hpiece]

def lowTransformBox (n : ℕ) (i : Row)
    (ll : LogCertificate (lowPieceLeftQ i)) : Box :=
  Box.add (Box.mul (Box.sub (Box.point 1) (earlyCutoffBox i))
    (expBox n (-(lowThetaQ i)/2)))
    (Box.mul (earlyCutoffBox i) (Box.add (Box.point (lowStartQ i))
      (Box.inflate (pieceZBox n (lowPieceAQ i) (lowPieceCQ i) (lowThetaQ i)
        (lowPieceLeftQ i) lowPieceRightQ ll.box lowRightLog.box)
        ((lowPieceRightQ-lowPieceLeftQ i)*expErrorQ n (lowThetaQ i)))))

theorem lowTransformBox_ok (i : Row) (ll : LogCertificate (lowPieceLeftQ i)) :
    (lowTransformBox 12 i ll).Holds (lowTransform i) := by
  have hp := (piece_errors 12
    (a := (lowPieceAQ i : ℝ)) (c := (lowPieceCQ i : ℝ))
    (theta := (lowThetaQ i : ℝ))
    (l := (lowPieceLeftQ i : ℝ)) (h := (lowPieceRightQ : ℝ))
    (by cases i <;> norm_num [lowPieceLeftQ, lowStartQ, xQ])
    (by cases i <;> norm_num [lowPieceLeftQ, lowStartQ, lowPieceRightQ, xQ])
    (by cases i <;> norm_num [lowThetaQ])
    (by cases i <;> norm_num [lowThetaQ]) (fun y hy => low_piece_bounds i hy)).1
  have herror : |pieceZ (lowPieceAQ i) (lowPieceCQ i) (lowThetaQ i)
      (lowPieceLeftQ i) lowPieceRightQ -
      pieceZPoly 12 (lowPieceAQ i) (lowPieceCQ i) (lowThetaQ i)
        (lowPieceLeftQ i) lowPieceRightQ| ≤
      (((lowPieceRightQ-lowPieceLeftQ i)*expErrorQ 12 (lowThetaQ i) : ℚ) : ℝ) := by
    simpa [expErrorQ] using hp
  have hz := Box.inflate_ok (pieceZBox_ok 12 (lowPieceAQ i) (lowPieceCQ i)
    (lowThetaQ i) (lowPieceLeftQ i) lowPieceRightQ ll.correct lowRightLog.correct)
    herror
  have he := expBox_ok 12 (-(lowThetaQ i)/2)
    (by cases i <;> norm_num [lowThetaQ])
  have h := Box.add_ok
    (Box.mul_ok (Box.sub_ok (Box.point_ok 1) (earlyCutoffBox_ok i)) he)
    (Box.mul_ok (earlyCutoffBox_ok i) (Box.add_ok (Box.point_ok (lowStartQ i)) hz))
  simpa [lowTransformBox, lowTransform] using h

def firstLowTransformRounded : Box := ⟨(873827280035833441 / 1000000000000000000), (1747654560071667 / 2000000000000000)⟩
theorem firstLowTransformRounded_ok : firstLowTransformRounded.Holds (lowTransform .first) := by
  let ll : LogCertificate (lowPieceLeftQ .first) := reindexLog lowLeftFirstLog
    (by norm_num [lowPieceLeftQ, lowStartQ, xQ])
  have h := lowTransformBox_ok .first ll
  apply Box.widen h <;>
    norm_num (config := { maxSteps := 1000000 }) [firstLowTransformRounded, lowTransformBox,
      ll, reindexLog, pieceZBox, momentBox, invMomentBox, lowLeftFirstLog, lowRightLog,
      lowThetaQ, lowPieceAQ, lowPieceCQ, lowPieceLeftQ, lowPieceRightQ,
      lowStartQ, xQ, xiQ, etaQ, earlyCutoffBox, LogCertificate.box,
      Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]

def firstLowTransformLoglo : LogCertificate firstLowTransformRounded.lo where
  lo := (-134872542952326213639929 / 1000000000000000000000000)
  hi := (-33718135738081553409981 / 250000000000000000000000)
  n := 24
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [firstLowTransformRounded, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [firstLowTransformRounded, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [firstLowTransformRounded, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [firstLowTransformRounded, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [firstLowTransformRounded, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]

def firstLowTransformLoghi : LogCertificate firstLowTransformRounded.hi where
  lo := (-26974508590465229224173 / 200000000000000000000000)
  hi := (-6743627147616307306043 / 50000000000000000000000)
  n := 24
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [firstLowTransformRounded, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [firstLowTransformRounded, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [firstLowTransformRounded, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [firstLowTransformRounded, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [firstLowTransformRounded, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]

def firstLowRateBox : Box := Box.sub (Box.point (-(27 / 100)*(999/2000)))
  (logBox firstLowTransformRounded firstLowTransformLoglo firstLowTransformLoghi)
theorem firstLowRateBox_ok : firstLowRateBox.Holds (lowCanonicalRate .first) := by
  have h := Box.sub_ok (Box.point_ok (-(27 / 100)*(999/2000)))
    (logBox_ok firstLowTransformLoglo firstLowTransformLoghi firstLowTransformRounded_ok)
  simpa [lowCanonicalRate, lowThetaQ, rho, firstLowRateBox] using h

def secondLowTransformRounded : Box := ⟨(111432897158602507 / 125000000000000000), (178292635453764023 / 200000000000000000)⟩
theorem secondLowTransformRounded_ok : secondLowTransformRounded.Holds (lowTransform .second) := by
  let ll : LogCertificate (lowPieceLeftQ .second) := reindexLog lowLeftSecondLog
    (by norm_num [lowPieceLeftQ, lowStartQ, xQ])
  have h := lowTransformBox_ok .second ll
  apply Box.widen h <;>
    norm_num (config := { maxSteps := 1000000 }) [secondLowTransformRounded, lowTransformBox,
      ll, reindexLog, pieceZBox, momentBox, invMomentBox, lowLeftSecondLog, lowRightLog,
      lowThetaQ, lowPieceAQ, lowPieceCQ, lowPieceLeftQ, lowPieceRightQ,
      lowStartQ, xQ, xiQ, etaQ, earlyCutoffBox, LogCertificate.box,
      Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]

def secondLowTransformLoglo : LogCertificate secondLowTransformRounded.lo where
  lo := (-57445573386677018826193 / 500000000000000000000000)
  hi := (-114891146773354037652381 / 1000000000000000000000000)
  n := 24
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [secondLowTransformRounded, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [secondLowTransformRounded, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [secondLowTransformRounded, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [secondLowTransformRounded, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [secondLowTransformRounded, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]

def secondLowTransformLoghi : LogCertificate secondLowTransformRounded.hi where
  lo := (-57445573386676985734529 / 500000000000000000000000)
  hi := (-114891146773353971469053 / 1000000000000000000000000)
  n := 24
  q_pos := by norm_num (config := { maxSteps := 1000000 }) [secondLowTransformRounded, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lo_small := by norm_num (config := { maxSteps := 1000000 }) [secondLowTransformRounded, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  hi_small := by norm_num (config := { maxSteps := 1000000 }) [secondLowTransformRounded, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  lower_check := by norm_num (config := { maxSteps := 1000000 }) [secondLowTransformRounded, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]
  upper_check := by norm_num (config := { maxSteps := 1000000 }) [secondLowTransformRounded, Box.Holds, Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point, Box.inflate, Box.sum, expBox, expPolyQ, expErrorQ, Finset.sum_range_succ, Nat.factorial]

def secondLowRateBox : Box := Box.sub (Box.point (-(23 / 100)*(999/2000)))
  (logBox secondLowTransformRounded secondLowTransformLoglo secondLowTransformLoghi)
theorem secondLowRateBox_ok : secondLowRateBox.Holds (lowCanonicalRate .second) := by
  have h := Box.sub_ok (Box.point_ok (-(23 / 100)*(999/2000)))
    (logBox_ok secondLowTransformLoglo secondLowTransformLoghi secondLowTransformRounded_ok)
  simpa [lowCanonicalRate, lowThetaQ, rho, secondLowRateBox] using h

theorem low_canonical_transform_guards (i : Row) :
    0 < lowTransform i ∧
    (lowMarginQ i : ℝ) < lowCanonicalRate i - atomRateI0 i := by
  cases i
  · constructor
    · exact Box.lower_real firstLowTransformRounded_ok (by norm_num [firstLowTransformRounded])
    · apply Box.lower_real (Box.sub_ok firstLowRateBox_ok (sourceI0Box_ok .first))
      norm_num [lowMarginQ, firstLowRateBox, sourceI0Box, firstI0RoundedBox,
        logBox, firstLowTransformLoglo, firstLowTransformLoghi,
        Box.sub, Box.add, Box.neg, Box.mul, Box.scale, Box.point]
  · constructor
    · exact Box.lower_real secondLowTransformRounded_ok (by norm_num [secondLowTransformRounded])
    · apply Box.lower_real (Box.sub_ok secondLowRateBox_ok (sourceI0Box_ok .second))
      norm_num [lowMarginQ, secondLowRateBox, sourceI0Box, secondI0RoundedBox,
        logBox, secondLowTransformLoglo, secondLowTransformLoghi,
        Box.sub, Box.add, Box.neg, Box.mul, Box.scale, Box.point]

end FCAppendix.Affine.Uniform07Finishing.Early
