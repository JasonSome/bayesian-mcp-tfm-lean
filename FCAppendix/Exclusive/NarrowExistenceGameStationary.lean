import FCAppendix.Exclusive.NarrowExistenceGameExpected
import FCAppendix.Exclusive.NarrowExistenceGameType
import FCAppendix.Exclusive.CompactBestResponse

noncomputable section
namespace FCAppendix.Exclusive.Narrow.Existence
open MeasureTheory Set Filter Topology
open scoped NNReal BoundedContinuousFunction

namespace UniformFiniteConstants
variable {d : ℕ} {G : Schedule (d+1)} {h rho : ℝ}
    (U : UniformFiniteConstants d G h rho)

theorem expected_bid_continuous (hh : h ∈ Icc (0:ℝ) 1) {m : ℕ} (c : ℕ)
    (hM : U.M0 ≤ m+1) (hC : |(c:ℝ)/((m:ℝ)+1)-rho| < U.eta)
    (nu : Measure (ValueBand U.eps)) [IsProbabilityMeasure nu]
    (a : UserTariff) (ha : a.Allowed) (baseRatio : ℝ) (hbase : baseRatio ∈ Icc (0:ℝ) U.eps)
    (beta : ValueBand U.eps → ℝ) (hbeta : Continuous beta)
    (hband : ∀ v, beta v ∈ Icc (-U.delta) U.delta)
    (v : ℝ) (hv : v ∈ Icc (1-U.eps) (1+U.eps)) :
    ContinuousOn (finiteExpectedScore (m := m) d c a G (rho/h) baseRatio ⟨h,hh⟩ nu beta v)
      (Icc (-U.delta) U.delta) := by
  have hh' : LipschitzOnWith ⟨U.B,U.B_pos.le⟩
      (finiteExpectedScore (m := m) d c a G (rho/h) baseRatio ⟨h,hh⟩ nu beta v)
      (Icc (-U.delta) U.delta) := LipschitzOnWith.of_dist_le_mul (fun x hx y hy => by
    change |finiteExpectedScore (m := m) d c a G (rho/h) baseRatio ⟨h,hh⟩ nu beta v x-
      finiteExpectedScore (m := m) d c a G (rho/h) baseRatio ⟨h,hh⟩ nu beta v y| ≤ U.B*|x-y|
    exact finiteExpectedScore_bid_bound d c a G (rho/h) baseRatio
      ⟨h,hh⟩ nu beta hbeta v (-U.delta) U.delta U.B
      (fun omega z hz => (U.all_rows c hM hC a ha beta hband v z baseRatio hv hz hbase omega).2.1)
      y x hy hx)
  exact hh'.continuousOn

theorem expected_inward (hd : 1 ≤ d) (hh : h ∈ Icc (0:ℝ) 1) {m : ℕ} (c : ℕ)
    (hM : U.M0 ≤ m+1) (hC : |(c:ℝ)/((m:ℝ)+1)-rho| < U.eta)
    (nu : Measure (ValueBand U.eps)) [IsProbabilityMeasure nu]
    (a : UserTariff) (ha : a.Allowed) (baseRatio : ℝ) (hbase : baseRatio ∈ Icc (0:ℝ) U.eps)
    (beta : ValueBand U.eps → ℝ) (hbeta : Continuous beta)
    (hband : ∀ v, beta v ∈ Icc (-U.delta) U.delta)
    (v : ℝ) (hv : v ∈ Icc (1-U.eps) (1+U.eps)) :
    0 < finiteExpectedScore (m := m) d c a G (rho/h) baseRatio ⟨h,hh⟩ nu beta v (-U.delta) ∧
      finiteExpectedScore (m := m) d c a G (rho/h) baseRatio ⟨h,hh⟩ nu beta v U.delta < 0 := by
  have hz : (0:ℝ) ∈ Icc (-U.delta) U.delta := ⟨by linarith [U.delta_pos], U.delta_pos.le⟩
  have hlo : -U.delta ∈ Icc (-U.delta) U.delta := ⟨le_rfl, by linarith [U.delta_pos]⟩
  have hhi : U.delta ∈ Icc (-U.delta) U.delta := ⟨by linarith [U.delta_pos], le_rfl⟩
  have hcentral := U.expected_central_bound hh c hM hC nu a ha baseRatio hbase v hv
  have hparameter := U.expected_parameter_bound hd hh c hM hC nu a ha baseRatio hbase
    (fun _ => 0) beta continuous_const hbeta (fun _ => hz) hband U.delta U.delta_pos.le
    (fun w => by simpa only [sub_zero] using abs_le.mpr (hband w)) v 0 hv hz
  have hleft := U.expected_decrease hh c hM hC nu a ha baseRatio hbase beta hbeta hband
    v (-U.delta) 0 hv hlo hz (by linarith [U.delta_pos])
  have hright := U.expected_decrease hh c hM hC nu a ha baseRatio hbase beta hbeta hband
    v 0 U.delta hv hz hhi U.delta_pos.le
  have hK := U.kappa_pos.trans_le (U.reference a ha).1
  have hKD := mul_pos hK U.delta_pos
  have hkD := mul_le_mul_of_nonneg_right (U.reference a ha).1 U.delta_pos.le
  have hc := abs_le.mp hcentral
  have hp := abs_le.mp hparameter
  constructor <;> nlinarith

def finiteScoreData (hd : 1 ≤ d) (hh : h ∈ Icc (0:ℝ) 1) {m : ℕ} (c : ℕ)
    (hM : U.M0 ≤ m+1) (hC : |(c:ℝ)/((m:ℝ)+1)-rho| < U.eta)
    (nu : Measure (ValueBand U.eps)) [IsProbabilityMeasure nu]
    (a : UserTariff) (ha : a.Allowed) (baseRatio : ℝ) (hbase : baseRatio ∈ Icc (0:ℝ) U.eps) :
    Exclusive.Existence.ScoreData
      (Exclusive.Existence.bidBand (ValueBand U.eps) (-U.delta) U.delta) (ValueBand U.eps)
      (-U.delta) U.delta ((5/6:ℝ)*literalReferenceCurvature d a (rho/h)) where
  score beta v z := finiteExpectedScore (m := m) d c a G (rho/h) baseRatio ⟨h,hh⟩ nu beta.val (v:ℝ) z
  band_nonempty := by linarith [U.delta_pos]
  curvature_pos := mul_pos (by norm_num) (U.kappa_pos.trans_le (U.reference a ha).1)
  continuous_bid beta v := U.expected_bid_continuous hh c hM hC nu a ha baseRatio hbase
    beta.val beta.val.continuous beta.property v.val v.property
  inward_left beta v := (U.expected_inward hd hh c hM hC nu a ha baseRatio hbase
    beta.val beta.val.continuous beta.property v.val v.property).1
  inward_right beta v := (U.expected_inward hd hh c hM hC nu a ha baseRatio hbase
    beta.val beta.val.continuous beta.property v.val v.property).2
  decrease beta v x hx y hy hxy := U.expected_decrease hh c hM hC nu a ha baseRatio hbase
    beta.val beta.val.continuous beta.property v.val x y v.property hx hy hxy

theorem finiteScoreData_parameter_bound (hd : 1 ≤ d) (hh : h ∈ Icc (0:ℝ) 1) {m : ℕ} (c : ℕ)
    (hM : U.M0 ≤ m+1) (hC : |(c:ℝ)/((m:ℝ)+1)-rho| < U.eta)
    (nu : Measure (ValueBand U.eps)) [IsProbabilityMeasure nu]
    (a : UserTariff) (ha : a.Allowed) (baseRatio : ℝ) (hbase : baseRatio ∈ Icc (0:ℝ) U.eps)
    (beta gamma : Exclusive.Existence.bidBand (ValueBand U.eps) (-U.delta) U.delta)
    (v : ValueBand U.eps) (z : ℝ) (hz : z ∈ Icc (-U.delta) U.delta) :
    |(U.finiteScoreData hd hh c hM hC nu a ha baseRatio hbase).score beta v z-
      (U.finiteScoreData hd hh c hM hC nu a ha baseRatio hbase).score gamma v z| ≤
        ((5/6:ℝ)*literalReferenceCurvature d a (rho/h))*(9/10:ℝ)*dist beta gamma := by
  have hh' := U.expected_parameter_bound hd hh c hM hC nu a ha baseRatio hbase
    gamma.val beta.val gamma.val.continuous beta.val.continuous gamma.property beta.property
    (dist beta gamma) dist_nonneg (fun w => by
      simpa only [Real.dist_eq, Subtype.dist_eq] using
        (BoundedContinuousFunction.dist_coe_le_dist (f := beta.val) (g := gamma.val) w))
    v.val z v.property hz
  change |finiteExpectedScore (m := m) d c a G (rho/h) baseRatio ⟨h,hh⟩ nu beta.val v.val z-
    finiteExpectedScore (m := m) d c a G (rho/h) baseRatio ⟨h,hh⟩ nu gamma.val v.val z| ≤ _
  convert hh' using 1; ring

theorem actual_state_bounds {m : ℕ} (c : ℕ)
    (hM : U.M0 ≤ m+1) (hC : |(c:ℝ)/((m:ℝ)+1)-rho| < U.eta)
    (baseRatio : ℝ) (hbase : baseRatio ∈ Icc (0:ℝ) U.eps)
    (beta : ValueBand U.eps → ℝ) (hband : ∀ v, beta v ∈ Icc (-U.delta) U.delta)
    (z : ℝ) (hz : z ∈ Icc (-U.delta) U.delta) (omega : RivalProfile m (ValueBand U.eps)) :
    (finiteRowState d c baseRatio beta 0 z omega) 0 ∈ Icc (0:ℝ) 1 ∧
      (finiteRowState d c baseRatio beta 0 z omega) 1 ∈ Icc (0:ℝ) 1 ∧
        (finiteRowState d c baseRatio beta 0 z omega) 0 < 1 := by
  have hbox := finiteRowState_mem_box d c U.delta baseRatio U.delta_le_one
    ⟨hbase.1, hbase.2.trans U.eps_lt_one.le⟩ beta hband 0 z (by constructor <;> norm_num)
    hz omega (U.safe c hM hC)
  have hq := profileFailure_lt_one_of_full_ratio (1/(d:ℝ)) U.delta (by positivity)
    (activeLogProfile beta z omega) (activeLogProfile_band beta U.delta z hz hband omega)
    (m+1) c (by omega) (by rw [activeIndex_card]; have := activeCount_le omega; omega)
    (by simpa only [Nat.cast_add, Nat.cast_one] using U.safe c hM hC) none
  rw [activeIndex_card, ← logShare_eq_activeProfileShare] at hq
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, hq⟩
  · simpa only [stateBoxLower, Matrix.cons_val_zero] using hbox.1 0
  · simpa only [stateBoxUpper, Matrix.cons_val_zero] using hbox.2 0
  · simpa only [stateBoxLower, Matrix.cons_val_one, Matrix.cons_val_zero] using hbox.1 1
  · simpa only [stateBoxUpper, Matrix.cons_val_one, Matrix.cons_val_zero] using hbox.2 1

theorem goodCount_pos (hh : h ∈ Icc (0:ℝ) 1) {m : ℕ} (hM : U.M0 ≤ m+1)
    (nu : Measure (ValueBand U.eps)) [IsProbabilityMeasure nu]
    (a : UserTariff) (ha : a.Allowed) :
    0 < iidRivalLaw m ⟨h,hh⟩ nu (goodCount m h U.eta) := by
  have hb := (le_div_iff₀ (show 0 < 48*U.B from mul_pos (by norm_num) U.B_pos)).mp
    ((U.count_bad_bound hh hM nu).trans (min_le_left _ _))
  have href := (U.reference a ha).1.trans (U.reference a ha).2
  have he := measureReal_add_measureReal_compl (μ := iidRivalLaw m ⟨h,hh⟩ nu)
    (measurableSet_goodCount m h U.eta)
  rw [probReal_univ] at he
  have hpos : 0 < (iidRivalLaw m ⟨h,hh⟩ nu).real (goodCount m h U.eta) := by
    nlinarith [U.B_pos]
  exact (ENNReal.toReal_pos_iff.mp hpos).1

theorem expected_strict_type (hd : 1 ≤ d) (hh : h ∈ Icc (0:ℝ) 1)
    (hp0 : 0 ≤ rho/h) (hp1 : rho/h < 1) {m : ℕ} (c : ℕ)
    (hM : U.M0 ≤ m+1) (hC : |(c:ℝ)/((m:ℝ)+1)-rho| < U.eta)
    (nu : Measure (ValueBand U.eps)) [IsProbabilityMeasure nu]
    (a : UserTariff) (ha : a.Allowed) (baseRatio : ℝ) (hbase : baseRatio ∈ Icc (0:ℝ) U.eps)
    (beta : ValueBand U.eps → ℝ) (hbeta : Continuous beta)
    (hband : ∀ v, beta v ∈ Icc (-U.delta) U.delta)
    (v w z : ℝ) (hvw : v < w) (hz : z ∈ Icc (-U.delta) U.delta) :
    finiteExpectedScore (m := m) d c a G (rho/h) baseRatio ⟨h,hh⟩ nu beta v z <
      finiteExpectedScore (m := m) d c a G (rho/h) baseRatio ⟨h,hh⟩ nu beta w z := by
  apply finiteExpectedScore_strict_type d c hd a ha G (rho/h) baseRatio hp0 hp1
    ⟨h,hh⟩ nu beta hbeta v w z hvw
    (fun omega => ⟨(U.actual_state_bounds c hM hC baseRatio hbase beta hband z hz omega).1,
      (U.actual_state_bounds c hM hC baseRatio hbase beta hband z hz omega).2.1⟩)
    (fun omega => (U.actual_state_bounds c hM hC baseRatio hbase beta hband z hz omega).2.2)
    (goodCount m h U.eta) (U.goodCount_pos hh hM nu a ha)
  exact U.typical_overload c hM hC

theorem finiteScoreData_type_bound (hd : 1 ≤ d) (hh : h ∈ Icc (0:ℝ) 1)
    (hp0 : 0 ≤ rho/h) (hp1 : rho/h < 1) {m : ℕ} (c : ℕ)
    (hM : U.M0 ≤ m+1) (hC : |(c:ℝ)/((m:ℝ)+1)-rho| < U.eta)
    (nu : Measure (ValueBand U.eps)) [IsProbabilityMeasure nu]
    (a : UserTariff) (ha : a.Allowed) (baseRatio : ℝ) (hbase : baseRatio ∈ Icc (0:ℝ) U.eps)
    (beta : Exclusive.Existence.bidBand (ValueBand U.eps) (-U.delta) U.delta)
    (v w : ValueBand U.eps) (z : ℝ) (hz : z ∈ Icc (-U.delta) U.delta) :
    |(U.finiteScoreData hd hh c hM hC nu a ha baseRatio hbase).score beta v z-
      (U.finiteScoreData hd hh c hM hC nu a ha baseRatio hbase).score beta w z| ≤
        ((1/(d:ℝ))*sourceValueFactor d a (rho/h)*((d+1:ℕ):ℝ))*dist v w := by
  have hh' := finiteExpectedScore_type_bound d c hd a ha G (rho/h) baseRatio hp0 hp1
    ⟨h,hh⟩ nu beta.val beta.val.continuous v.val w.val z
    (fun omega => ⟨(U.actual_state_bounds c hM hC baseRatio hbase beta.val beta.property z hz omega).1,
      (U.actual_state_bounds c hM hC baseRatio hbase beta.val beta.property z hz omega).2.1⟩)
  simpa only [finiteScoreData, Subtype.dist_eq, Real.dist_eq] using hh'

theorem exists_pure_stationary (hd : 1 ≤ d) (hh : h ∈ Icc (0:ℝ) 1)
    (hp0 : 0 ≤ rho/h) (hp1 : rho/h < 1) {m : ℕ} (c : ℕ)
    (hM : U.M0 ≤ m+1) (hC : |(c:ℝ)/((m:ℝ)+1)-rho| < U.eta)
    (nu : Measure (ValueBand U.eps)) [IsProbabilityMeasure nu]
    (a : UserTariff) (ha : a.Allowed) (baseRatio : ℝ) (hbase : baseRatio ∈ Icc (0:ℝ) U.eps) :
    ∃ beta : Exclusive.Existence.bidBand (ValueBand U.eps) (-U.delta) U.delta,
      StrictMono beta.val ∧ ∀ v : ValueBand U.eps,
        finiteExpectedScore (m := m) d c a G (rho/h) baseRatio ⟨h,hh⟩ nu beta.val v.val (beta.val v) = 0 := by
  let D := U.finiteScoreData hd hh c hM hC nu a ha baseRatio hbase
  let K := (5/6:ℝ)*literalReferenceCurvature d a (rho/h)
  let A := (1/(d:ℝ))*sourceValueFactor d a (rho/h)*((d+1:ℕ):ℝ)
  have hK : 0 < K := D.curvature_pos
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (mul_nonneg (by positivity) (sourceValueFactor_pos d hd a ha (rho/h) hp0 hp1).le)
      (Nat.cast_nonneg _)
  let L : ℝ≥0 := ⟨A/K, div_nonneg hA hK.le⟩
  have hL : ∀ theta v w z, z ∈ Icc (-U.delta) U.delta →
      |D.score theta v z-D.score theta w z| ≤ K*(L:ℝ)*dist v w := by
    intro theta v w z hz
    have hb := U.finiteScoreData_type_bound hd hh hp0 hp1 c hM hC nu a ha baseRatio hbase theta v w z hz
    have he : K*(L:ℝ) = A := by change K*(A/K) = A; field_simp [hK.ne']
    rw [he]
    exact hb
  obtain ⟨beta, hbeta, _hunique⟩ := Exclusive.Existence.exists_unique_pure_stationary
    D L hL (⟨9/10, by norm_num⟩ : ℝ≥0) (by change (9/10:ℝ) < 1; norm_num)
    (U.finiteScoreData_parameter_bound hd hh c hM hC nu a ha baseRatio hbase)
  have heq (v : ValueBand U.eps) : D.reply beta v = beta.val v :=
    (D.root_unique beta v (beta.property v) (hbeta v)).symm
  refine ⟨beta, ?_, hbeta⟩
  have hm := D.reply_strictMono beta (fun v w hvw z hz =>
    U.expected_strict_type hd hh hp0 hp1 c hM hC nu a ha baseRatio hbase
      beta.val beta.val.continuous beta.property v.val w.val z hvw hz)
  intro v w hvw
  simpa only [heq] using hm hvw

end UniformFiniteConstants
end FCAppendix.Exclusive.Narrow.Existence
