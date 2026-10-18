import FCAppendix.Exclusive.NarrowExistenceGameRowBounds

noncomputable section
namespace FCAppendix.Exclusive.Narrow.Existence
open MeasureTheory Set Filter Topology

def sourceStateTypeSlope (d : ℕ) (a : UserTariff) (p0 : ℝ) (x : RowState) : ℝ :=
  (1/(d:ℝ))*x 0*(1-x 1)*sourceSFirst d a p0 (1-x 0)

theorem sourceValueFactor_pos (d : ℕ) (hd : 1 ≤ d) (a : UserTariff) (ha : a.Allowed)
    (p0 : ℝ) (hp0 : 0 ≤ p0) (hp1 : p0 < 1) : 0 < sourceValueFactor d a p0 :=
  mul_pos (pow_pos (sub_pos.mpr hp1) d)
    (fTariff_pos_and_derivative_pos d hd a ha hp0 hp1).1

theorem sourceStateTypeSlope_eq (d : ℕ) (a : UserTariff) (p0 : ℝ) (x : RowState) :
    sourceStateTypeSlope d a p0 x =
      (1/(d:ℝ))*x 0*(1-x 1)*sourceValueFactor d a p0*((d+1:ℕ):ℝ)*(x 0)^d := by
  dsimp [sourceStateTypeSlope, sourceSFirst]
  rw [successFirst_eq]
  ring

theorem sourceStateTypeSlope_bounds (d : ℕ) (hd : 1 ≤ d) (a : UserTariff) (ha : a.Allowed)
    (p0 : ℝ) (hp0 : 0 ≤ p0) (hp1 : p0 < 1) (x : RowState)
    (hq : x 0 ∈ Icc (0:ℝ) 1) (hs : x 1 ∈ Icc (0:ℝ) 1) :
    0 ≤ sourceStateTypeSlope d a p0 x ∧
      sourceStateTypeSlope d a p0 x ≤ (1/(d:ℝ))*sourceValueFactor d a p0*((d+1:ℕ):ℝ) := by
  rw [sourceStateTypeSlope_eq]
  have hf := sourceValueFactor_pos d hd a ha p0 hp0 hp1
  have hr : 0 ≤ 1/(d:ℝ) := by positivity
  have hqp := pow_nonneg hq.1 d
  have hq1 := pow_le_one₀ hq.1 hq.2 (n := d)
  have hs0 : 0 ≤ 1-x 1 := sub_nonneg.mpr hs.2
  have hs1 : 1-x 1 ≤ 1 := by linarith [hs.1]
  have hA0 : 0 ≤ x 0*(1-x 1) := mul_nonneg hq.1 hs0
  have hA1 : x 0*(1-x 1) ≤ 1 := by nlinarith [hq.1, hq.2]
  constructor
  · exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hr hq.1) hs0) hf.le)
      (Nat.cast_nonneg _)) hqp
  · calc
      _ = ((1/(d:ℝ))*sourceValueFactor d a p0*((d+1:ℕ):ℝ))*(x 0*(1-x 1)*(x 0)^d) := by ring
      _ ≤ ((1/(d:ℝ))*sourceValueFactor d a p0*((d+1:ℕ):ℝ))*1 :=
        mul_le_mul_of_nonneg_left (mul_le_one₀ hA1 hqp hq1) (by positivity)
      _ = _ := mul_one _

theorem sourceStateTypeSlope_pos (d : ℕ) (hd : 1 ≤ d) (a : UserTariff) (ha : a.Allowed)
    (p0 : ℝ) (hp0 : 0 ≤ p0) (hp1 : p0 < 1) (x : RowState)
    (hq : 0 < x 0) (hs : x 1 < 1) : 0 < sourceStateTypeSlope d a p0 x := by
  have hf := sourceValueFactor_pos d hd a ha p0 hp0 hp1
  have hdpos : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  rw [sourceStateTypeSlope_eq]
  exact mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (one_div_pos.mpr hdpos) hq)
    (sub_pos.mpr hs)) hf) (by positivity)) (pow_pos hq d)

theorem finiteRowScore_type_difference {m : ℕ} {V : Type*} (d c : ℕ)
    (a : UserTariff) (G : Schedule (d+1)) (p0 baseRatio : ℝ)
    (beta : V → ℝ) (v w z : ℝ) (omega : RivalProfile m V) :
    finiteRowScore d c a G p0 baseRatio beta v z omega-
      finiteRowScore d c a G p0 baseRatio beta w z omega =
        (v-w)*sourceStateTypeSlope d a p0 (finiteRowState d c baseRatio beta 0 z omega) := by
  dsimp [finiteRowScore, score, logVelocity, sourceStateTypeSlope, sourceSFirst,
    finiteRowState, logAllocation]
  ring

theorem finiteRowTypeSlope_pos_of_overload {m : ℕ} {V : Type*}
    (d c : ℕ) (hd : 1 ≤ d) (a : UserTariff) (ha : a.Allowed)
    (p0 baseRatio : ℝ) (hp0 : 0 ≤ p0) (hp1 : p0 < 1)
    (beta : V → ℝ) (z : ℝ) (omega : RivalProfile m V)
    (hover : c < 1+activeCount omega)
    (hsafe : (finiteRowState d c baseRatio beta 0 z omega) 0 < 1) :
    0 < sourceStateTypeSlope d a p0 (finiteRowState d c baseRatio beta 0 z omega) := by
  let W := rivalInverseSum (1/(d:ℝ)) beta omega
  have hshare : 0 < logShare (1/(d:ℝ)) W z := div_pos (Real.exp_pos _)
    (add_pos_of_nonneg_of_pos (rivalInverseSum_nonneg _ _ omega) (Real.exp_pos _))
  have hnat : 1 ≤ 1+activeCount omega-c := Nat.sub_pos_of_lt hover
  have hcast : (1:ℝ) ≤ ((1+activeCount omega-c:ℕ):ℝ) := by exact_mod_cast hnat
  have hq : 0 < (finiteRowState d c baseRatio beta 0 z omega) 0 :=
    mul_pos (lt_of_lt_of_le (by norm_num) hcast) hshare
  have hsq : (finiteRowState d c baseRatio beta 0 z omega) 1 ≤
      (finiteRowState d c baseRatio beta 0 z omega) 0 := by
    dsimp [finiteRowState]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hcast hshare.le
  exact sourceStateTypeSlope_pos d hd a ha p0 hp0 hp1 _ hq (hsq.trans_lt hsafe)

section Expected
variable {m : ℕ} {V : Type*} [TopologicalSpace V] [MeasurableSpace V]
  [BorelSpace V] [SecondCountableTopology V] [CompactSpace V]

theorem integrable_finiteRowTypeSlope (d c : ℕ) (a : UserTariff) (G : Schedule (d+1))
    (p0 baseRatio : ℝ) (h : unitInterval) (nu : Measure V) [IsProbabilityMeasure nu]
    (beta : V → ℝ) (hbeta : Continuous beta) (z : ℝ) :
    Integrable (fun omega : RivalProfile m V => sourceStateTypeSlope d a p0
      (finiteRowState d c baseRatio beta 0 z omega)) (iidRivalLaw m h nu) := by
  have he := funext (finiteRowScore_type_difference (m := m) d c a G p0 baseRatio beta 1 0 z)
  simp only [sub_zero, one_mul] at he
  rw [← he]
  exact (integrable_finiteRowScore (m := m) d c a G p0 baseRatio h nu beta hbeta 1 z).sub
    (integrable_finiteRowScore (m := m) d c a G p0 baseRatio h nu beta hbeta 0 z)

theorem finiteExpectedScore_type_difference (d c : ℕ) (a : UserTariff) (G : Schedule (d+1))
    (p0 baseRatio : ℝ) (h : unitInterval) (nu : Measure V) [IsProbabilityMeasure nu]
    (beta : V → ℝ) (hbeta : Continuous beta) (v w z : ℝ) :
    finiteExpectedScore (m := m) d c a G p0 baseRatio h nu beta v z-
      finiteExpectedScore (m := m) d c a G p0 baseRatio h nu beta w z =
        (v-w)*∫ omega, sourceStateTypeSlope d a p0
          (finiteRowState d c baseRatio beta 0 z omega) ∂iidRivalLaw m h nu := by
  unfold finiteExpectedScore
  rw [← integral_sub (integrable_finiteRowScore (m := m) d c a G p0 baseRatio h nu beta hbeta v z)
    (integrable_finiteRowScore (m := m) d c a G p0 baseRatio h nu beta hbeta w z)]
  simp_rw [finiteRowScore_type_difference]
  exact integral_const_mul _ _

theorem finiteExpectedScore_type_bound (d c : ℕ) (hd : 1 ≤ d)
    (a : UserTariff) (ha : a.Allowed) (G : Schedule (d+1))
    (p0 baseRatio : ℝ) (hp0 : 0 ≤ p0) (hp1 : p0 < 1)
    (h : unitInterval) (nu : Measure V) [IsProbabilityMeasure nu]
    (beta : V → ℝ) (hbeta : Continuous beta) (v w z : ℝ)
    (hstate : ∀ omega : RivalProfile m V,
      (finiteRowState d c baseRatio beta 0 z omega) 0 ∈ Icc (0:ℝ) 1 ∧
        (finiteRowState d c baseRatio beta 0 z omega) 1 ∈ Icc (0:ℝ) 1) :
    |finiteExpectedScore (m := m) d c a G p0 baseRatio h nu beta v z-
      finiteExpectedScore (m := m) d c a G p0 baseRatio h nu beta w z| ≤
        ((1/(d:ℝ))*sourceValueFactor d a p0*((d+1:ℕ):ℝ))*|v-w| := by
  have hbounds := fun omega => sourceStateTypeSlope_bounds d hd a ha p0 hp0 hp1
    (finiteRowState d c baseRatio beta 0 z omega) (hstate omega).1 (hstate omega).2
  have hi := integrable_finiteRowTypeSlope (m := m) d c a G p0 baseRatio h nu beta hbeta z
  have hnonneg : (0:ℝ) ≤ ∫ omega, sourceStateTypeSlope d a p0
      (finiteRowState d c baseRatio beta 0 z omega) ∂iidRivalLaw m h nu :=
    integral_nonneg (fun omega => (hbounds omega).1)
  have hle := integral_mono hi (integrable_const ((1/(d:ℝ))*sourceValueFactor d a p0*((d+1:ℕ):ℝ)))
    (fun omega => (hbounds omega).2)
  simp only [integral_const, probReal_univ, one_smul] at hle
  rw [finiteExpectedScore_type_difference d c a G p0 baseRatio h nu beta hbeta,
    abs_mul, abs_of_nonneg hnonneg, mul_comm]
  exact mul_le_mul_of_nonneg_right hle (abs_nonneg _)

theorem finiteExpectedScore_strict_type (d c : ℕ) (hd : 1 ≤ d)
    (a : UserTariff) (ha : a.Allowed) (G : Schedule (d+1))
    (p0 baseRatio : ℝ) (hp0 : 0 ≤ p0) (hp1 : p0 < 1)
    (h : unitInterval) (nu : Measure V) [IsProbabilityMeasure nu]
    (beta : V → ℝ) (hbeta : Continuous beta) (v w z : ℝ) (hvw : v < w)
    (hstate : ∀ omega : RivalProfile m V,
      (finiteRowState d c baseRatio beta 0 z omega) 0 ∈ Icc (0:ℝ) 1 ∧
        (finiteRowState d c baseRatio beta 0 z omega) 1 ∈ Icc (0:ℝ) 1)
    (hsafe : ∀ omega : RivalProfile m V, (finiteRowState d c baseRatio beta 0 z omega) 0 < 1)
    (E : Set (RivalProfile m V)) (hEpos : 0 < iidRivalLaw m h nu E)
    (hover : ∀ omega ∈ E, c < 1+activeCount omega) :
    finiteExpectedScore (m := m) d c a G p0 baseRatio h nu beta v z <
      finiteExpectedScore (m := m) d c a G p0 baseRatio h nu beta w z := by
  have hnonneg := fun omega => (sourceStateTypeSlope_bounds d hd a ha p0 hp0 hp1
    (finiteRowState d c baseRatio beta 0 z omega) (hstate omega).1 (hstate omega).2).1
  have hint := integrable_finiteRowTypeSlope (m := m) d c a G p0 baseRatio h nu beta hbeta z
  have hsupp : E ⊆ Function.support (fun omega : RivalProfile m V => sourceStateTypeSlope d a p0
      (finiteRowState d c baseRatio beta 0 z omega)) := by
    intro omega homega
    exact (finiteRowTypeSlope_pos_of_overload d c hd a ha p0 baseRatio hp0 hp1 beta z omega
      (hover omega homega) (hsafe omega)).ne'
  have hpos := (integral_pos_iff_support_of_nonneg hnonneg hint).mpr
    (hEpos.trans_le (measure_mono hsupp))
  have hdiff := finiteExpectedScore_type_difference (m := m) d c a G p0 baseRatio h nu
    beta hbeta w v z
  have hstrict := mul_pos (sub_pos.mpr hvw) hpos
  linarith

end Expected
end FCAppendix.Exclusive.Narrow.Existence
