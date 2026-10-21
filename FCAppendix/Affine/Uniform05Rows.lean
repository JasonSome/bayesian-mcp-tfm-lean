import FCAppendix.Affine.Uniform05Basic

noncomputable section
namespace FCAppendix.Affine.Uniform05
open Set

lemma x_range (i : Row) : (1 : ℝ)/2 < x i ∧ x i < 1 := by
  cases i <;> norm_num [x]

lemma log_lower_reciprocal {y : ℝ} (hy : 0 < y) :
    1-1/y ≤ Real.log y := by
  simpa only [one_div] using Real.one_sub_inv_le_log_of_pos hy

lemma log_upper_factor {y a : ℝ} (hy : 0 < y) (ha : 0 < a) (N : ℕ) :
    Real.log y ≤ (N : ℝ)*(a-1)+(y/a^N-1) := by
  have hq : 0 < y/a^N := div_pos hy (pow_pos ha _)
  have he : Real.log y = (N : ℝ)*Real.log a+Real.log (y/a^N) := by
    rw [Real.log_div hy.ne' (pow_ne_zero _ ha.ne'), Real.log_pow]
    ring
  rw [he]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos ha) (Nat.cast_nonneg _))
    (Real.log_le_sub_one_of_pos hq)

lemma log_lower_factor {y a : ℝ} (hy : 0 < y) (ha : 0 < a) (N : ℕ) :
    (N : ℝ)*(1-1/a)+(1-a^N/y) ≤ Real.log y := by
  have hq : 0 < y/a^N := div_pos hy (pow_pos ha _)
  have he : Real.log y = (N : ℝ)*Real.log a+Real.log (y/a^N) := by
    rw [Real.log_div hy.ne' (pow_ne_zero _ ha.ne'), Real.log_pow]
    ring
  have hinv : 1/(y/a^N) = a^N/y := by
    field_simp [hy.ne', pow_ne_zero N ha.ne']
  rw [he]
  have hqlog := log_lower_reciprocal hq
  rw [hinv] at hqlog
  exact add_le_add
    (mul_le_mul_of_nonneg_left (log_lower_reciprocal ha) (Nat.cast_nonneg _)) hqlog

lemma row_denominator_pos (i : Row) :
    0 < 2*x i*(1-Real.log (x i))-1 := by
  have hx := x_range i
  have hx0 : 0 < x i := by linarith
  have hl : Real.log (x i) < 0 := Real.log_neg hx0 hx.2
  have hp := mul_neg_of_pos_of_neg hx0 hl
  nlinarith

lemma row_denominator_lt_one (i : Row) :
    2*x i*(1-Real.log (x i))-1 < 1 := by
  have hx0 : 0 < x i := by have hx := x_range i; linarith
  have hl := log_lower_factor (y := x i) (a := (9 : ℝ)/10) hx0 (by norm_num) 1
  cases i <;> norm_num [x] at hl ⊢ <;> nlinarith

lemma t_pos (i : Row) : 0 < t i := by
  rw [t_eq_canonical]
  exact Uniform07.cutoff_pos i

lemma t_lt_one (i : Row) : t i < 1 := by
  rw [t_eq_canonical]
  exact Uniform07.cutoff_lt_one i

lemma delta_lt_t (i : Row) : delta < t i := by
  unfold t
  apply (lt_div_iff₀ (row_denominator_pos i)).2
  have h := mul_pos (by norm_num [delta] : 0 < delta)
    (sub_pos.mpr (row_denominator_lt_one i))
  nlinarith

lemma lambda_pos (i : Row) : 0 < lambda i := by
  unfold lambda
  exact mul_pos (by have hx := x_range i; linarith) (t_pos i)

lemma requiredDemand_range (i : Row) :
    0 < requiredDemand i ∧ requiredDemand i < (1 : ℝ)/2 := by
  have ht := t_pos i
  have hd := delta_lt_t i
  have hδ : 0 < delta := by norm_num [delta]
  unfold requiredDemand
  constructor
  · exact div_pos (sub_pos.mpr hd) (by positivity)
  · apply (div_lt_iff₀ (by positivity : 0 < 2*t i)).2
    linarith

lemma requiredDemand_ge_one_sixtieth (i : Row) :
    (1 : ℝ)/60 ≤ requiredDemand i := by
  rw [requiredDemand_eq i (row_denominator_pos i).ne']
  have hx0 : 0 < x i := by have hx := x_range i; linarith
  have hl := log_lower_factor (y := x i) (a := (9 : ℝ)/10) hx0 (by norm_num) 1
  cases i <;> norm_num [x] at hl ⊢ <;> nlinarith

def demandUpper : Row → ℝ
  | .first => 37/1000
  | .second => 54/1000

lemma requiredDemand_lt_coarse_upper (i : Row) :
    requiredDemand i < demandUpper i := by
  rw [requiredDemand_eq i (row_denominator_pos i).ne']
  have hx0 : 0 < x i := by have hx := x_range i; linarith
  have hl := log_upper_factor (y := x i) (a := (49 : ℝ)/50) hx0 (by norm_num) 15
  cases i <;> norm_num [x, demandUpper] at hl ⊢ <;> nlinarith

lemma three_requiredDemand_lt_one (i : Row) : 3*requiredDemand i < 1 := by
  have h := requiredDemand_lt_coarse_upper i
  cases i <;> norm_num [demandUpper] at h ⊢ <;> linarith

lemma unconditional_requiredDemand (i : Row) :
    t i*requiredDemand i = (t i-delta)/2 := by
  unfold requiredDemand
  field_simp [(t_pos i).ne']

lemma residual_mean_identity (i : Row) :
    rho-(1-t i)/2 = t i*requiredDemand i := by
  rw [unconditional_requiredDemand]
  norm_num [rho, delta]
  ring

lemma full_load_identity (i : Row) :
    1-t i+2*t i*requiredDemand i = 2*rho := by
  have h := unconditional_requiredDemand i
  norm_num [rho, delta] at h ⊢
  nlinarith

def capRatio (i : Row) : ℝ := x i/(kappa i+xi i*x i)+1/200

lemma capRatio_pos (i : Row) : 0 < capRatio i := by
  cases i <;> norm_num [capRatio, x, kappa, xi, eta]

lemma cap_eq_ratio (i : Row) : cap i = capRatio i*t i := by
  have ht : t i ≠ 0 := (t_pos i).ne'
  cases i <;>
    norm_num [cap, activeBid, lambda, capRatio, kappa, xi, eta, x] <;>
    field_simp [ht] <;> ring

lemma cap_lt_t (i : Row) : cap i < t i := by
  rw [cap_eq_ratio]
  have hc : capRatio i < 1 := by
    cases i <;> norm_num [capRatio, x, kappa, xi, eta]
  simpa using mul_lt_mul_of_pos_right hc (t_pos i)

lemma upperFloorLimit_eq_ratio (i : Row) :
    upperFloorLimit i = (2*x i-(x i)^2)*t i := by
  unfold upperFloorLimit lambda
  field_simp [(t_pos i).ne']

lemma upperFloorLimit_gt_cap (i : Row) : cap i < upperFloorLimit i := by
  rw [cap_eq_ratio, upperFloorLimit_eq_ratio]
  apply mul_lt_mul_of_pos_right _ (t_pos i)
  cases i <;> norm_num [capRatio, x, kappa, xi, eta]

lemma upperFloorLimit_receipt_guard (i : Row) :
    upperFloorLimit i < lambda i/kappa i := by
  have hk := (kappa_range i).1
  apply (lt_div_iff₀ hk).2
  rw [upperFloorLimit_eq_ratio]
  unfold lambda
  have ht := t_pos i
  cases i <;> norm_num [x, kappa, xi, eta] <;> nlinarith

lemma product_route_primitive_guard (i : Row) :
    1/(1+Real.sqrt (x i))^2 < xi i := by
  have hx0 : 0 ≤ x i := by have hx := x_range i; linarith
  have hs0 := Real.sqrt_nonneg (x i)
  have hs := Real.sq_sqrt hx0
  have hslo : (4 : ℝ)/5 < Real.sqrt (x i) := by
    have hx : (7 : ℝ)/10 ≤ x i := by cases i <;> norm_num [x]
    nlinarith
  apply (div_lt_iff₀ (sq_pos_of_pos (by linarith : 0 < 1+Real.sqrt (x i)))).2
  cases i <;> norm_num [xi, eta] <;> nlinarith

lemma chi_t_lt_cap (i : Row) : chi*t i < cap i := by
  rw [cap_eq_ratio]
  apply mul_lt_mul_of_pos_right _ (t_pos i)
  cases i <;> norm_num [chi, capRatio, x, kappa, xi, eta]

lemma full_floor_max_below_lambda (i : Row) :
    chi*(t i-v0 i) < lambda i := by
  have ht := t_pos i
  cases i <;> norm_num [chi, v0, lambda, x] <;> nlinarith

lemma zc_receipt_guard (i : Row) :
    kappa i*cap i < chi*(zc i-v0 i) := by
  rw [cap_eq_ratio]
  have ht := t_pos i
  cases i <;>
    norm_num [capRatio, kappa, xi, eta, chi, zc, v0, lambda, x] <;> nlinarith

lemma numerical_root_receipt_gap (i : Row) :
    kappa i*cap i < ((54 : ℝ)/100-1/2000)*t i := by
  rw [cap_eq_ratio, ← mul_assoc]
  apply mul_lt_mul_of_pos_right _ (t_pos i)
  cases i <;> norm_num [capRatio, kappa, xi, eta, x]

lemma floor_le_min_value_cap (i : Row) {v : ℝ} (hv : 0 ≤ v) (hvt : v ≤ t i) :
    floorBid i v ≤ min v (cap i) := by
  apply le_min (floor_le_value i hv (t_pos i).le)
  have h := floor_le_chi_mul i hv (t_pos i).le
  exact h.trans ((mul_le_mul_of_nonneg_left hvt (by norm_num [chi])).trans
    (chi_t_lt_cap i).le)

def fullFloorCut : ℝ := 1/200+(54/100)/(69/100)

def normalizedFloorDemand (i : Row) : ℝ :=
  (1-fullFloorCut-((54/100)/(69/100))*
    Real.log ((1-1/200)/(fullFloorCut-1/200)))/xi i

lemma fullFloorCut_is_max (i : Row) :
    max (x i+1/200) (1/200+(54/100)/(69/100)) = fullFloorCut := by
  cases i <;> norm_num [x, fullFloorCut]

lemma normalizedFloorDemand_lower (i : Row) :
    (match i with | .first => (51 : ℝ)/1000 | .second => 56/1000) <
      normalizedFloorDemand i := by
  have hy : 0 < ((1 : ℝ)-1/200)/(fullFloorCut-1/200) := by
    norm_num [fullFloorCut]
  have hl := log_upper_factor hy (by norm_num : (0 : ℝ) < 203/200) 15
  cases i <;>
    norm_num [normalizedFloorDemand, fullFloorCut, xi, eta] at hl ⊢ <;> nlinarith

theorem numerical_floor_root_guard (i : Row) :
    requiredDemand i < normalizedFloorDemand i := by
  have h₁ := requiredDemand_lt_coarse_upper i
  have h₂ := normalizedFloorDemand_lower i
  cases i <;> norm_num [demandUpper] at h₁ h₂ ⊢ <;> linarith

lemma zc_probability_bounds (i : Row) : 0 ≤ zc i ∧ zc i ≤ 1 := by
  have ht := t_pos i
  have ht1 := t_lt_one i
  have hx0 : 0 < x i+1/200 := by cases i <;> norm_num [x]
  have hx1 : x i+1/200 < 1 := by cases i <;> norm_num [x]
  have he : zc i = (x i+1/200)*t i := by dsimp [zc, lambda]; ring
  rw [he]
  constructor
  · positivity
  · exact (mul_lt_mul_of_pos_right hx1 ht).le.trans (by simpa using ht1.le)

theorem numerical_seed_rejection_guard (i : Row) :
    (21239 : ℝ)/100000 < 1-fullFloorCut ∧
    (20227 : ℝ)/100000 < (1-fullFloorCut)*((2/100)/(1/1000+2/100)) ∧
    3*requiredDemand i < (1-fullFloorCut)*((2/100)/(1/1000+2/100)) := by
  have hr := requiredDemand_lt_coarse_upper i
  refine ⟨by norm_num [fullFloorCut], by norm_num [fullFloorCut], ?_⟩
  cases i <;> norm_num [demandUpper, fullFloorCut] at hr ⊢ <;> linarith

lemma numerical_balanced_h_gap (i : Row) :
    (1-(69/100)/capRatio i)/xi i < (42 : ℝ)/100 := by
  cases i <;> norm_num [capRatio, x, kappa, xi, eta]

end FCAppendix.Affine.Uniform05
