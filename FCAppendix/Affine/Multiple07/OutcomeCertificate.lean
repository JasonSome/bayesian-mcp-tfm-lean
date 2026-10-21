import FCAppendix.Affine.Multiple07.ProfileIntegrals

noncomputable section
namespace FCAppendix.Affine.Multiple07

open Uniform07

def firstBandLog : LogCertificate (1901 / 1899) where
  lo := 105263167614328290 / 10^20
  hi := 105263167614328291 / 10^20
  n := 8
  q_pos := by norm_num
  lo_small := by norm_num
  hi_small := by norm_num
  lower_check := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point,
    Finset.sum_range_succ]
  upper_check := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point,
    Finset.sum_range_succ]

def secondBandLog : LogCertificate (2101 / 2099) where
  lo := 95238102436742871 / 10^20
  hi := 95238102436742872 / 10^20
  n := 8
  q_pos := by norm_num
  lo_small := by norm_num
  hi_small := by norm_num
  lower_check := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point,
    Finset.sum_range_succ]
  upper_check := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point,
    Finset.sum_range_succ]

def firstReciprocalBox : Box := Box.scale 1000 firstBandLog.box
def secondReciprocalBox : Box := Box.scale 1000 secondBandLog.box

theorem firstReciprocalBox_ok : firstReciprocalBox.Holds (bandReciprocal .first) := by
  convert! Box.scale_ok 1000 firstBandLog.correct using 1;
    norm_num [firstReciprocalBox, bandReciprocal, bandLower, bandUpper]; ring

theorem secondReciprocalBox_ok : secondReciprocalBox.Holds (bandReciprocal .second) := by
  convert! Box.scale_ok 1000 secondBandLog.correct using 1;
    norm_num [secondReciprocalBox, bandReciprocal, bandLower, bandUpper]; ring

def reciprocalBox : Partition → Box
  | .row335 => firstReciprocalBox
  | .row665 => Box.add (Box.scale (67 / 133) firstReciprocalBox)
      (Box.scale (66 / 133) secondReciprocalBox)

theorem reciprocalBox_ok (r : Partition) : (reciprocalBox r).Holds (reciprocalMean r) := by
  rw [reciprocalMean_logarithmic]
  cases r
  · exact firstReciprocalBox_ok
  · convert! Box.add_ok (Box.scale_ok (67 / 133) firstReciprocalBox_ok)
      (Box.scale_ok (66 / 133) secondReciprocalBox_ok) using 1; norm_num

def unfilledFractionQ : Partition → ℚ
  | .row335 => 33 / 67
  | .row665 => 66 / 133

def multiplierBox (r : Partition) : Box :=
  Box.div (Box.point (unfilledFractionQ r)) (reciprocalBox r)

theorem multiplierBox_ok (r : Partition) : (multiplierBox r).Holds (multiplier r) := by
  have hpos : 0 < (reciprocalBox r).lo := by
    cases r <;> norm_num [reciprocalBox, firstReciprocalBox, secondReciprocalBox,
      firstBandLog, secondBandLog, LogCertificate.box, Box.scale, Box.mul,
      Box.point, Box.add]
  have he : (unfilledFractionQ r : ℝ) = 1 - activeFraction r := by
    cases r <;> norm_num [unfilledFractionQ, activeFraction, rho, upperMass, activeMass]
  simpa only [multiplierBox, he, multiplier] using
    Box.div_ok hpos (Box.point_ok (unfilledFractionQ r)) (reciprocalBox_ok r)

def firstDuplicateBox (r : Partition) : Box :=
  Box.add
    (Box.sub (Box.point 1) (Box.scale 2 (Box.mul (multiplierBox r) firstReciprocalBox)))
    (Box.scale (4000000 / (1899 * 1901)) (Box.mul (multiplierBox r) (multiplierBox r)))

def secondDuplicateBox (r : Partition) : Box :=
  Box.add
    (Box.sub (Box.point 1) (Box.scale 2 (Box.mul (multiplierBox r) secondReciprocalBox)))
    (Box.scale (4000000 / (2099 * 2101)) (Box.mul (multiplierBox r) (multiplierBox r)))

theorem firstDuplicateBox_ok (r : Partition) :
    (firstDuplicateBox r).Holds (bandDuplicateMoment (multiplier r) .first) := by
  have h := Box.add_ok
    (Box.sub_ok (Box.point_ok 1)
      (Box.scale_ok 2 (Box.mul_ok (multiplierBox_ok r) firstReciprocalBox_ok)))
    (Box.scale_ok (4000000 / (1899 * 1901))
      (Box.mul_ok (multiplierBox_ok r) (multiplierBox_ok r)))
  convert! h using 1;
    norm_num [firstDuplicateBox, bandDuplicateMoment, bandLower, bandUpper, pow_two]; ring

theorem secondDuplicateBox_ok (r : Partition) :
    (secondDuplicateBox r).Holds (bandDuplicateMoment (multiplier r) .second) := by
  have h := Box.add_ok
    (Box.sub_ok (Box.point_ok 1)
      (Box.scale_ok 2 (Box.mul_ok (multiplierBox_ok r) secondReciprocalBox_ok)))
    (Box.scale_ok (4000000 / (2099 * 2101))
      (Box.mul_ok (multiplierBox_ok r) (multiplierBox_ok r)))
  convert! h using 1;
    norm_num [secondDuplicateBox, bandDuplicateMoment, bandLower, bandUpper, pow_two]; ring

def sourceDuplicateBox (r : Partition) : Box :=
  match r with
  | .row335 => Box.scale (67 / 200) (firstDuplicateBox r)
  | .row665 => Box.add (Box.scale (67 / 200) (firstDuplicateBox r))
      (Box.scale (33 / 100) (secondDuplicateBox r))

theorem sourceDuplicateBox_ok (r : Partition) :
    (sourceDuplicateBox r).Holds (limitingDuplicates r) := by
  cases r
  · convert! Box.scale_ok (67 / 200) (firstDuplicateBox_ok .row335) using 1;
      norm_num [sourceDuplicateBox,limitingDuplicates]
  · convert! Box.add_ok (Box.scale_ok (67 / 200) (firstDuplicateBox_ok .row665))
      (Box.scale_ok (33 / 100) (secondDuplicateBox_ok .row665)) using 1;
      norm_num [sourceDuplicateBox,limitingDuplicates]

theorem duplicate_enclosures :
    (86268664220 / 10^12 : ℝ) < limitingDuplicates .row335 ∧
      limitingDuplicates .row335 < 86268664221 / 10^12 ∧
      (169168480288 / 10^12 : ℝ) < limitingDuplicates .row665 ∧
      limitingDuplicates .row665 < 169168480289 / 10^12 := by
  refine ⟨Box.lower_real (sourceDuplicateBox_ok .row335) ?_,
    Box.upper_real (sourceDuplicateBox_ok .row335) ?_,
    Box.lower_real (sourceDuplicateBox_ok .row665) ?_,
    Box.upper_real (sourceDuplicateBox_ok .row665) ?_⟩ <;>
    norm_num [sourceDuplicateBox, firstDuplicateBox, secondDuplicateBox,
      multiplierBox, unfilledFractionQ, reciprocalBox, firstReciprocalBox,
      secondReciprocalBox, firstBandLog, secondBandLog, LogCertificate.box,
      Box.add, Box.sub, Box.neg, Box.mul, Box.scale, Box.div, Box.inv, Box.point]

theorem coverage_enclosures :
    (903731335779 / 10^12 : ℝ) < limitingCoverage .row335 ∧
      limitingCoverage .row335 < 903731335780 / 10^12 ∧
      (820831519711 / 10^12 : ℝ) < limitingCoverage .row665 ∧
      limitingCoverage .row665 < 820831519712 / 10^12 := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := duplicate_enclosures
  dsimp [limitingCoverage]
  norm_num at h₁ h₂ h₃ h₄ ⊢
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem multiplicity_enclosures :
    (10954583080 / 10^10 : ℝ) < limitingMultiplicity .row335 ∧
      limitingMultiplicity .row335 < 10954583081 / 10^10 ∧
      (12060940354 / 10^10 : ℝ) < limitingMultiplicity .row665 ∧
      limitingMultiplicity .row665 < 12060940355 / 10^10 := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := coverage_enclosures
  have hp₁ := limitingCoverage_pos .row335
  have hp₂ := limitingCoverage_pos .row665
  unfold limitingMultiplicity
  rw [lt_div_iff₀ hp₁, div_lt_iff₀ hp₁, lt_div_iff₀ hp₂, div_lt_iff₀ hp₂]
  norm_num at h₁ h₂ h₃ h₄ ⊢
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem strict_source_outcomes :
    limitingDuplicates .row335 < limitingDuplicates .row665 ∧
      limitingCoverage .row665 < limitingCoverage .row335 ∧
      limitingMultiplicity .row335 < limitingMultiplicity .row665 := by
  have hd := duplicate_enclosures
  have hq := coverage_enclosures
  have hm := multiplicity_enclosures
  norm_num at hd hq hm
  exact ⟨by linarith [hd.2.1, hd.2.2.1],
    by linarith [hq.1, hq.2.2.2], by linarith [hm.2.1, hm.2.2.1]⟩

end FCAppendix.Affine.Multiple07
