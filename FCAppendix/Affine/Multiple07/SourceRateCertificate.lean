import FCAppendix.Affine.Multiple07.SourceGuards
import FCAppendix.Affine.LowBody.SourcePrimitiveGuards

noncomputable section
namespace FCAppendix.Affine.Multiple07
open MeasureTheory ProbabilityTheory Set Filter Topology Uniform07

def firstTiltLog : LogCertificate (1 / 5) where
  lo := -1609437912435 / 10^12
  hi := -1609437912434 / 10^12
  n := 32
  q_pos := by norm_num
  lo_small := by norm_num
  hi_small := by norm_num
  lower_check := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point,
    Finset.sum_range_succ]
  upper_check := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point,
    Finset.sum_range_succ]

def firstTransformLog : LogCertificate (99 / 625) where
  lo := -1842631799602 / 10^12
  hi := -1842631799601 / 10^12
  n := 32
  q_pos := by norm_num
  lo_small := by norm_num
  hi_small := by norm_num
  lower_check := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point,
    Finset.sum_range_succ]
  upper_check := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point,
    Finset.sum_range_succ]

def firstKLLeftLog : LogCertificate (11 / 15) where
  lo := -310154928304 / 10^12
  hi := -310154928303 / 10^12
  n := 32
  q_pos := by norm_num
  lo_small := by norm_num
  hi_small := by norm_num
  lower_check := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point,
    Finset.sum_range_succ]
  upper_check := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point,
    Finset.sum_range_succ]

def firstKLRightLog : LogCertificate (101 / 65) where
  lo := 440733246945 / 10^12
  hi := 440733246946 / 10^12
  n := 32
  q_pos := by norm_num
  lo_small := by norm_num
  hi_small := by norm_num
  lower_check := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point,
    Finset.sum_range_succ]
  upper_check := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point,
    Finset.sum_range_succ]

def secondTiltLog : LogCertificate (14633 / 100000) where
  lo := -1921890933878 / 10^12
  hi := -1921890933877 / 10^12
  n := 32
  q_pos := by norm_num
  lo_small := by norm_num
  hi_small := by norm_num
  lower_check := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point,
    Finset.sum_range_succ]
  upper_check := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point,
    Finset.sum_range_succ]

def secondTransformLog : LogCertificate (152129783637 / 2000000000000) where
  lo := -2576168463293 / 10^12
  hi := -2576168463292 / 10^12
  n := 32
  q_pos := by norm_num
  lo_small := by norm_num
  hi_small := by norm_num
  lower_check := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point,
    Finset.sum_range_succ]
  upper_check := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point,
    Finset.sum_range_succ]

def secondKLLeftLog : LogCertificate (33 / 56) where
  lo := -528844129269 / 10^12
  hi := -528844129268 / 10^12
  n := 32
  q_pos := by norm_num
  lo_small := by norm_num
  hi_small := by norm_num
  lower_check := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point,
    Finset.sum_range_succ]
  upper_check := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point,
    Finset.sum_range_succ]

def secondKLRightLog : LogCertificate (101 / 32) where
  lo := 1149384614041 / 10^12
  hi := 1149384614042 / 10^12
  n := 32
  q_pos := by norm_num
  lo_small := by norm_num
  hi_small := by norm_num
  lower_check := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point,
    Finset.sum_range_succ]
  upper_check := by norm_num [expBox, expErrorQ, expPolyQ, Box.inflate, Box.point,
    Finset.sum_range_succ]

def jointTilt : Partition → ℝ
  | .row335 => 1 / 5
  | .row665 => 14633 / 100000

def rateMargin : Partition → ℝ
  | .row335 => 11120 / 100000
  | .row665 => 3617 / 100000

theorem jointTilt_mem (r : Partition) : jointTilt r ∈ Ioo (0 : ℝ) 1 := by
  cases r <;> norm_num [jointTilt]

theorem jointObjective_at_log (r : Partition) {z : ℝ} (hz : 0 < z) :
    LowBody.jointObjective (3 / 200) (activeMass r) (upperMass r) rho (Real.log z) =
      2 * rho * Real.log z -
        Real.log (activeMass r * z ^ 2 + upperMass r * z + 3 / 200) := by
  have he : Real.exp (2 * Real.log z) = z ^ 2 := by
    rw [show 2 * Real.log z = Real.log z + Real.log z by ring,
      Real.exp_add, Real.exp_log hz]
    ring
  simp only [LowBody.jointObjective, he, Real.exp_log hz]

theorem source_negative_tilt_margin (r : Partition) :
    rateMargin r <
      LowBody.jointObjective (3 / 200) (activeMass r) (upperMass r) rho
        (Real.log (jointTilt r)) -
      2 * Ample.binaryKL rho (1 - upperMass r / 2) := by
  rw [jointObjective_at_log r (jointTilt_mem r).1]
  cases r
  · have hz := firstTiltLog.correct
    have hT := firstTransformLog.correct
    have hL := firstKLLeftLog.correct
    have hR := firstKLRightLog.correct
    norm_num [firstTiltLog, firstTransformLog, firstKLLeftLog, firstKLRightLog,
      LogCertificate.box, Box.Holds] at hz hT hL hR
    norm_num [rateMargin, jointTilt, rho, activeMass, upperMass, Ample.binaryKL]
    linarith [hz.1, hT.2, hL.2, hR.2]
  · have hz := secondTiltLog.correct
    have hT := secondTransformLog.correct
    have hL := secondKLLeftLog.correct
    have hR := secondKLRightLog.correct
    norm_num [secondTiltLog, secondTransformLog, secondKLLeftLog, secondKLRightLog,
      LogCertificate.box, Box.Holds] at hz hT hL hR
    norm_num [rateMargin, jointTilt, rho, activeMass, upperMass, Ample.binaryKL]
    linarith [hz.1, hT.2, hL.2, hR.2]

theorem source_joint_objective_bddAbove (r : Partition) :
    BddAbove (LowBody.jointObjective (3 / 200) (activeMass r) (upperMass r) rho '' Iio 0) := by
  refine ⟨-Real.log (3 / 200 : ℝ), ?_⟩
  rintro y ⟨t, ht, rfl⟩
  have ha : 0 ≤ activeMass r := by cases r <;> norm_num [activeMass]
  have hh : 0 ≤ upperMass r := by cases r <;> norm_num [upperMass]
  have hZ : (3 / 200 : ℝ) ≤
      activeMass r * Real.exp (2 * t) + upperMass r * Real.exp t + 3 / 200 := by
    linarith [mul_nonneg ha (Real.exp_pos (2 * t)).le,
      mul_nonneg hh (Real.exp_pos t).le]
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 3 / 200) hZ
  have hrt : 2 * rho * t ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by norm_num [rho]) ht.le
  dsimp [LowBody.jointObjective]
  linarith

theorem source_joint_rate_margin (r : Partition) :
    rateMargin r < LowBody.jointRate (3 / 200) (activeMass r) (upperMass r) rho -
      2 * Ample.binaryKL rho (1 - upperMass r / 2) := by
  have hmem :
      LowBody.jointObjective (3 / 200) (activeMass r) (upperMass r) rho
        (Real.log (jointTilt r)) ∈
      LowBody.jointObjective (3 / 200) (activeMass r) (upperMass r) rho '' Iio 0 :=
    ⟨Real.log (jointTilt r), Real.log_neg (jointTilt_mem r).1 (jointTilt_mem r).2, rfl⟩
  have hle := le_csSup (source_joint_objective_bddAbove r) hmem
  change _ ≤ LowBody.jointRate (3 / 200) (activeMass r) (upperMass r) rho at hle
  linarith [source_negative_tilt_margin r]

theorem source_joint_rate_gap (r : Partition) :
    2 * Ample.binaryKL rho (1 - upperMass r / 2) <
      LowBody.jointRate (3 / 200) (activeMass r) (upperMass r) rho := by
  have hm : 0 < rateMargin r := by cases r <;> norm_num [rateMargin]
  linarith [source_joint_rate_margin r]

def sourceCategoryLaw (r : Partition) : FiniteLaw (Fin 4) :=
  LowBody.categoryLaw (3 / 200) (activeMass r) (upperMass r)
    (by norm_num) (by cases r <;> norm_num [activeMass])
    (by cases r <;> norm_num [upperMass])
    (by cases r <;> norm_num [activeMass, upperMass]) (bandLaw .low)

theorem sourceCategoryLaw_eq_reference (r : Partition) (G : Measure ℝ)
    [IsProbabilityMeasure G] :
    sourceCategoryLaw r = LowBody.categoryLaw (3 / 200) (activeMass r) (upperMass r)
      (by norm_num) (by cases r <;> norm_num [activeMass])
      (by cases r <;> norm_num [upperMass])
      (by cases r <;> norm_num [activeMass, upperMass]) G := by
  apply FiniteLaw.ext
  intro j
  simp only [sourceCategoryLaw, LowBody.categoryLaw_mass]

theorem source_low_finite_guards (r : Partition) :
    ∀ᶠ m : ℕ in atTop,
      let L := (CommonList.iid (sourceCategoryLaw r) (m - 1)).prob
        (LowBody.LocalUnderflow (marketCapacity m) 0)
      let H := LowBody.boundary marketCapacity (1 - upperMass r / 2) m
      let D := (CommonList.iid (sourceCategoryLaw r) (m - 1)).prob
        (LowBody.BothUnderflow (marketCapacity m))
      let E := (CommonList.iid (sourceCategoryLaw r) (m - 2)).prob
        (LowBody.BothUnderflow (marketCapacity m))
      2 < m ∧ 0 < marketCapacity m ∧ 0 < L ∧ E < H ∧ D ≤ L / 4 ∧
        8 * eta * ((m - 1 : ℕ) : ℝ) * E / (L * (H - E)) < 1 / 2 ∧
        ∀ (G : Measure ℝ) (_hG : IsProbabilityMeasure G) (u : ℝ),
          H ≤ PiBinomial.pmf (m - 2)
            (LowBody.higherBidProbability (3 / 200) (activeMass r) (upperMass r) G u)
            (marketCapacity m - 1) ∧
          H - E ≤ (Measure.pi (fun _ : Fin (m - 2) =>
            LowBody.rivalLaw (3 / 200) (activeMass r) (upperMass r) G)).real
              (LowBody.firstCopyBoundary (marketCapacity m) u) := by
  simpa only [sourceCategoryLaw] using LowBody.eventually_primitive_source_guards
    (3 / 200) (activeMass r) (upperMass r)
    (by norm_num) (by cases r <;> norm_num [activeMass])
    (by cases r <;> norm_num [upperMass])
    (by cases r <;> norm_num [activeMass, upperMass]) (bandLaw .low)
    marketCapacity rho eta (by norm_num [rho])
    (by cases r <;> norm_num [rho, activeMass, upperMass]) (by norm_num [eta])
    marketCapacity_density (source_joint_rate_gap r)

end FCAppendix.Affine.Multiple07
