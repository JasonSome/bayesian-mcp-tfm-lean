import Mathlib
set_option autoImplicit false

noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryMomentAlgebra

def approxSuccess (ξ b A : ℝ) : ℝ := A / (ξ * b)
def approxSuccessDeriv (ξ b A P : ℝ) : ℝ := (b * P - A) / (ξ * b ^ 2)
def approxDup (ξ b B : ℝ) : ℝ := B / (ξ ^ 2 * b ^ 2)

def routeGap (η b q dq r : ℝ) : ℝ :=
  q ^ 2 - (q + η * b * dq) * r

theorem u12_gap_identity {η ξ b A B P : ℝ}
    (hξ : 0 < ξ) (hb : 0 < b) (hB : 0 < B) (hP : 0 < P)
    (hrel : ξ = (1 - η) / 2) :
    routeGap η b (approxSuccess ξ b A)
       (approxSuccessDeriv ξ b A P) (approxDup ξ b B)
      = (P * B) / (ξ ^ 2 * b ^ 2) *
        (A ^ 2 / (P * B) - η / ξ - 2 * A / (b * P)) := by
  have hη : η = 1 - 2 * ξ := by linarith
  have hξ0 : ξ ≠ 0 := ne_of_gt hξ
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hP0 : P ≠ 0 := ne_of_gt hP
  have hB0 : B ≠ 0 := ne_of_gt hB
  unfold routeGap approxSuccess approxSuccessDeriv approxDup
  rw [hη]
  field_simp [hξ0, hb0, hP0, hB0]
  ring

theorem u12_criterion {η ξ b A B P : ℝ}
    (hξ : 0 < ξ) (hb : 0 < b) (hB : 0 < B) (hP : 0 < P)
    (hrel : ξ = (1 - η) / 2) :
    0 < routeGap η b (approxSuccess ξ b A)
         (approxSuccessDeriv ξ b A P) (approxDup ξ b B) ↔
      η / ξ + 2 * A / (b * P) < A ^ 2 / (P * B) := by
  rw [u12_gap_identity hξ hb hB hP hrel]
  have hc : 0 < (P * B) / (ξ ^ 2 * b ^ 2) := by positivity
  constructor
  · intro h
    have hsub : 0 < A ^ 2 / (P * B) - η / ξ - 2 * A / (b * P) := by
      by_contra hn
      have hnon : A ^ 2 / (P * B) - η / ξ - 2 * A / (b * P) ≤ 0 :=
        le_of_not_gt hn
      have hprod := mul_nonpos_of_nonneg_of_nonpos hc.le hnon
      linarith
    linarith
  · intro h
    apply mul_pos hc
    linarith

theorem u12_quantitative {η ξ b A B P γ : ℝ}
    (hξ : 0 < ξ) (hb : 0 < b) (hB : 0 < B) (hP : 0 < P)
    (hrel : ξ = (1 - η) / 2)
    (hmargin : η / ξ + 2 * A / (b * P) + γ ≤ A ^ 2 / (P * B)) :
    (P * B) / (ξ ^ 2 * b ^ 2) * γ ≤
      routeGap η b (approxSuccess ξ b A)
        (approxSuccessDeriv ξ b A P) (approxDup ξ b B) := by
  rw [u12_gap_identity hξ hb hB hP hrel]
  have hc : 0 ≤ (P * B) / (ξ ^ 2 * b ^ 2) := by positivity
  apply mul_le_mul_of_nonneg_left _ hc
  linarith

theorem routeGap_perturbation_identity (η b q dq r q₀ dq₀ r₀ : ℝ) :
    routeGap η b q dq r - routeGap η b q₀ dq₀ r₀ =
       (q - q₀) * (q + q₀ - r)
       - (r - r₀) * (q₀ + η * b * dq₀)
       - (dq - dq₀) * (η * b * r) := by
  unfold routeGap
  ring

theorem routeGap_perturbation_bound (η b q dq r q₀ dq₀ r₀ : ℝ) :
    |routeGap η b q dq r - routeGap η b q₀ dq₀ r₀| ≤
      |q - q₀| * |q + q₀ - r| +
      |r - r₀| * |q₀ + η * b * dq₀| +
      |dq - dq₀| * |η * b * r| := by
  rw [routeGap_perturbation_identity]
  calc
    |(q - q₀) * (q + q₀ - r) -
        (r - r₀) * (q₀ + η * b * dq₀) -
        (dq - dq₀) * (η * b * r)|
      ≤ |(q - q₀) * (q + q₀ - r) -
            (r - r₀) * (q₀ + η * b * dq₀)| +
          |(dq - dq₀) * (η * b * r)| := abs_sub _ _
    _ ≤ (|(q - q₀) * (q + q₀ - r)| +
          |(r - r₀) * (q₀ + η * b * dq₀)|) +
          |(dq - dq₀) * (η * b * r)| := by
          gcongr
          exact abs_sub _ _
    _ = _ := by simp only [abs_mul]

theorem u12_finite_error {η ξ b A B P γ q dq r εq εr εdq Lq Lr Ldq : ℝ}
    (hξ : 0 < ξ) (hb : 0 < b) (hB : 0 < B) (hP : 0 < P)
    (hrel : ξ = (1 - η) / 2)
    (hmargin : η / ξ + 2 * A / (b * P) + γ ≤ A ^ 2 / (P * B))
    (hq : |q - approxSuccess ξ b A| ≤ εq)
    (hr : |r - approxDup ξ b B| ≤ εr)
    (hdq : |dq - approxSuccessDeriv ξ b A P| ≤ εdq)
    (hLq : |q + approxSuccess ξ b A - r| ≤ Lq)
    (hLr : |approxSuccess ξ b A + η * b * approxSuccessDeriv ξ b A P| ≤ Lr)
    (hLdq : |η * b * r| ≤ Ldq)
    (hstrict : εq * Lq + εr * Lr + εdq * Ldq <
        (P * B) / (ξ ^ 2 * b ^ 2) * γ) :
    0 < routeGap η b q dq r := by
  have hbase := u12_quantitative hξ hb hB hP hrel hmargin
  have herr := routeGap_perturbation_bound η b q dq r
      (approxSuccess ξ b A) (approxSuccessDeriv ξ b A P) (approxDup ξ b B)
  have hcoeff : |routeGap η b q dq r -
        routeGap η b (approxSuccess ξ b A)
          (approxSuccessDeriv ξ b A P) (approxDup ξ b B)| ≤
        εq * Lq + εr * Lr + εdq * Ldq := by
    refine herr.trans ?_
    have hprodq : |q - approxSuccess ξ b A| *
       |q + approxSuccess ξ b A - r| ≤ εq * Lq :=
       mul_le_mul hq hLq (abs_nonneg _) (by
         have := abs_nonneg (q - approxSuccess ξ b A)
         linarith)
    have hprodr : |r - approxDup ξ b B| *
       |approxSuccess ξ b A + η * b * approxSuccessDeriv ξ b A P| ≤ εr * Lr :=
       mul_le_mul hr hLr (abs_nonneg _) (by
         have := abs_nonneg (r - approxDup ξ b B)
         linarith)
    have hprodd : |dq - approxSuccessDeriv ξ b A P| *
       |η * b * r| ≤ εdq * Ldq :=
       mul_le_mul hdq hLdq (abs_nonneg _) (by
         have := abs_nonneg (dq - approxSuccessDeriv ξ b A P)
         linarith)
    linarith
  have habs := (abs_le.mp hcoeff).1
  linarith

end FCAppendix.Affine.Uniform06.EntryMomentAlgebra
