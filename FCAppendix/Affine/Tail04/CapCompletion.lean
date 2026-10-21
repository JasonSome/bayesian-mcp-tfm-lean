import FCAppendix.Affine.Tail04.MovingBoundary
import FCAppendix.Affine.Tail04.UpperOriginal

noncomputable section
namespace FCAppendix.Affine.Tail04
open MeasureTheory Filter Topology Set
open Existence.RankEnvelope

theorem cap_gap_transfers_down
    (S T : ℝ → ℝ) (t v b y gap : ℝ)
    (hvt : v ≤ t) (hS : S y ≤ S b)
    (hgap : gap ≤ (t * S y - T y) - (t * S b - T b)) :
    gap ≤ (v * S y - T y) - (v * S b - T b) := by
  have hp := mul_nonneg (sub_nonneg.mpr hvt) (sub_nonneg.mpr hS)
  nlinarith

theorem finite_cap_gap
    (S T : ℝ → ℝ) (t v b y gap eps actualB actualY : ℝ)
    (hvt : v ≤ t) (hS : S y ≤ S b)
    (hgap : gap ≤ (t * S y - T y) - (t * S b - T b))
    (hB : |actualB - (v * S b - T b)| ≤ eps)
    (hY : |actualY - (v * S y - T y)| ≤ eps) :
    gap - 2 * eps ≤ actualY - actualB := by
  have hg := cap_gap_transfers_down S T t v b y gap hvt hS hgap
  have hb := abs_le.mp hB
  have hy := abs_le.mp hY
  linarith

theorem cap_action_not_bestResponse
    (P : Interim.Problem 2) (S T : ℝ → ℝ)
    (t v b y gap eps : ℝ) (act comparison : Game.JointAction 2)
    (hvt : v ≤ t) (hS : S y ≤ S b)
    (hgap : gap ≤ (t * S y - T y) - (t * S b - T b))
    (hB : |P.payoff v act - (v * S b - T b)| ≤ eps)
    (hY : |P.payoff v comparison - (v * S y - T y)| ≤ eps)
    (heps : 2 * eps < gap) :
    ¬ P.BestResponse v act := by
  have hg := finite_cap_gap S T t v b y gap eps
    (P.payoff v act) (P.payoff v comparison) hvt hS hgap hB hY
  intro hbr
  have hh := hbr comparison
  linarith

def matchedUpperFloor (t U q : ℝ) : ℝ := t - U / q

theorem matchedUpperFloor_matching (q : ℝ → ℝ) (t U : ℝ) (hqt : q t ≠ 0) :
    utility q t (matchedUpperFloor t U (q t)) t = U := by
  rw [utility_at_floor]
  unfold matchedUpperFloor
  field_simp
  ring

theorem matchedUpperFloor_exact_shift (t U q : ℝ) :
    matchedUpperFloor t U q = (t - U) - U * (1 / q - 1) := by
  unfold matchedUpperFloor
  ring

theorem matchedUpperFloor_rank_correction
    (t U q D : ℝ) (hD : 0 ≤ D) (hDhalf : D ≤ 1 / 2)
    (hqlower : 1 - D ≤ q) (hqupper : q ≤ 1)
    (hU0 : 0 ≤ U) (hUt : U ≤ t) :
    0 ≤ U * (1 / q - 1) ∧ U * (1 / q - 1) ≤ 2 * t * D := by
  have hqhalf : (1 / 2 : ℝ) ≤ q := by linarith
  have hq : 0 < q := by linarith
  have hn : 0 ≤ 1 / q - 1 := by
    have hh : 1 ≤ 1 / q := (le_div_iff₀ hq).2 (by simpa using hqupper)
    linarith
  have hhdiv : 1 / q ≤ 1 + 2 * D := by
    apply (div_le_iff₀ hq).2
    have hp := mul_le_mul_of_nonneg_left hqhalf hD
    nlinarith
  have hh : 1 / q - 1 ≤ 2 * D := by linarith
  constructor
  · exact mul_nonneg hU0 hn
  · calc
      U * (1 / q - 1) ≤ U * (2 * D) := mul_le_mul_of_nonneg_left hh hU0
      _ ≤ t * (2 * D) := mul_le_mul_of_nonneg_right hUt (by positivity)
      _ = 2 * t * D := by ring

theorem matchedUpperFloor_above_cap
    (B k t U q c0 eps D : ℝ)
    (_ht : 0 < t) (hD : 0 ≤ D) (hDhalf : D ≤ 1 / 2)
    (hqlower : 1 - D ≤ q) (hqupper : q ≤ 1)
    (hU0 : 0 ≤ U) (hUt : U ≤ t)
    (happrox : |(t - U) - (B - c0 / t)| ≤ eps)
    (hbudget : eps + 2 * t * D < (k - c0) / t) :
    B - k / t < matchedUpperFloor t U q := by
  have hc := (matchedUpperFloor_rank_correction t U q D hD hDhalf
    hqlower hqupper hU0 hUt).2
  have hl := (abs_le.mp happrox).1
  rw [matchedUpperFloor_exact_shift]
  rw [sub_div] at hbudget
  linarith

theorem matchedUpperFloor_below_top
    (B t U q c0 eps : ℝ) (hq : 0 < q) (hqupper : q ≤ 1) (hU0 : 0 ≤ U)
    (happrox : |(t - U) - (B - c0 / t)| ≤ eps)
    (heps : eps < c0 / t) :
    matchedUpperFloor t U q < B := by
  have hu := (abs_le.mp happrox).2
  have hn : 0 ≤ 1 / q - 1 := by
    have hh : 1 ≤ 1 / q := (le_div_iff₀ hq).2 (by simpa using hqupper)
    linarith
  have hp := mul_nonneg hU0 hn
  rw [matchedUpperFloor_exact_shift]
  linarith

theorem all_lower_failure_preserved
    {Action : Type*} (A : Set Action) (S actual : Action → ℝ)
    (t c0 eps : ℝ) (hc0 : 0 < c0) (ht : 0 < t)
    (hS : ∀ act ∈ A, S act ≤ 1 - c0 / t ^ 2)
    (herr : ∀ act ∈ A, |actual act - S act| ≤ eps)
    (heps : eps ≤ c0 / (2 * t ^ 2)) :
    ∀ act ∈ A, actual act ≤ 1 - c0 / (2 * t ^ 2) := by
  intro act ha
  have hs := hS act ha
  have hu := (abs_le.mp (herr act ha)).2
  have he : c0 / t ^ 2 = 2 * (c0 / (2 * t ^ 2)) := by field_simp
  rw [he] at hs
  linarith

theorem upper_rank_strictly_above_lower
    (S q D t c0 : ℝ)
    (hS : S ≤ 1 - c0 / (2 * t ^ 2))
    (hD : D < c0 / (2 * t ^ 2)) (hq : 1 - D ≤ q) : S < q := by
  linarith

end FCAppendix.Affine.Tail04
