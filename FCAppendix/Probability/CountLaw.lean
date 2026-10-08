import FCAppendix.Model.Schedules

namespace FCAppendix

abbrev CountLaw (n : ℕ) := FiniteLaw (Fin (n + 1))

namespace CountLaw

variable {n : ℕ}

noncomputable def success (μ : CountLaw n) : ℝ := μ.expect (fun r => successIndicator r.val)
noncomputable def load (μ : CountLaw n) : ℝ := μ.expect (fun r => (r.val : ℝ))
noncomputable def duplicates (μ : CountLaw n) : ℝ := μ.load - μ.success
noncomputable def factorialMoment (μ : CountLaw n) : ℝ :=
  μ.expect (fun r => (r.val : ℝ) * ((r.val : ℝ) - 1))
noncomputable def charge (μ : CountLaw n) (A : Schedule n) : ℝ :=
  μ.expect (fun r => A.charge r.val)
noncomputable def utility (μ : CountLaw n) (v b g : ℝ) (A G : Schedule n) : ℝ :=
  μ.expect (fun r => userPayoff v b g A.charge G.charge r.val)

@[simp] theorem utility_eq (μ : CountLaw n) (v b g : ℝ) (A G : Schedule n) :
    μ.utility v b g A G = v * μ.success - b * μ.charge A - g * μ.charge G := by
  unfold utility userPayoff success charge
  rw [μ.expect_sub, μ.expect_sub, μ.expect_const_mul,
    μ.expect_const_mul, μ.expect_const_mul]

theorem success_nonneg (μ : CountLaw n) : 0 ≤ μ.success :=
  μ.expect_nonneg (fun r => successIndicator_nonneg r.val)

theorem success_le_one (μ : CountLaw n) : μ.success ≤ 1 :=
  μ.expect_le_const (fun r => successIndicator_le_one r.val)

theorem success_le_load (μ : CountLaw n) : μ.success ≤ μ.load :=
  μ.expect_mono (fun r => successIndicator_le_count r.val)

theorem load_nonneg (μ : CountLaw n) : 0 ≤ μ.load :=
  le_trans μ.success_nonneg μ.success_le_load

theorem load_le_mul_success (μ : CountLaw n) : μ.load ≤ n * μ.success := by
  calc
    _ ≤ μ.expect (fun r => (n : ℝ) * successIndicator r.val) :=
      μ.expect_mono (fun r => count_le_mul_success n r.val (by omega))
    _ = _ := μ.expect_const_mul n _

theorem load_le_n (μ : CountLaw n) : μ.load ≤ n := by
  have h := μ.load_le_mul_success
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [μ.success_le_one]

theorem duplicates_nonneg (μ : CountLaw n) : 0 ≤ μ.duplicates := by
  exact sub_nonneg.mpr μ.success_le_load

theorem duplicates_eq_expect (μ : CountLaw n) :
    μ.duplicates = μ.expect (fun r => (r.val : ℝ) - successIndicator r.val) := by
  rw [μ.expect_sub]
  rfl

theorem charge_nonneg (μ : CountLaw n) (A : Schedule n) : 0 ≤ μ.charge A :=
  μ.expect_nonneg (fun r => A.nonneg r.val (by omega))

theorem success_le_charge (μ : CountLaw n) (A : Schedule n) : μ.success ≤ μ.charge A := by
  apply μ.expect_mono
  intro r
  by_cases h : r.val = 0
  · simp [h, A.zero, successIndicator]
  · simp only [successIndicator, if_neg h]
    exact A.lower r.val (by omega) (by omega)

theorem charge_le_load (μ : CountLaw n) (A : Schedule n) : μ.charge A ≤ μ.load :=
  μ.expect_mono (fun r => A.upper r.val (by omega))

@[simp] theorem charge_once (μ : CountLaw n) : μ.charge (Schedule.once n) = μ.success := rfl
@[simp] theorem charge_ppi (μ : CountLaw n) : μ.charge (Schedule.ppi n) = μ.load := rfl

theorem charge_affine (μ : CountLaw n) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    μ.charge (Schedule.affine n η hη0 hη1) = μ.success + η * μ.duplicates := by
  unfold charge Schedule.affine
  rw [μ.expect_add, μ.expect_const_mul, μ.expect_sub]
  rfl

theorem receipt_lower (μ : CountLaw n) (A : Schedule n) (a : ℝ)
    (ha : ∀ r, r ≤ n → a * (r : ℝ) ≤ A.charge r) : a * μ.load ≤ μ.charge A := by
  calc
    _ = μ.expect (fun r => a * (r.val : ℝ)) := (μ.expect_const_mul a _).symm
    _ ≤ _ := μ.expect_mono (fun r => ha r.val (by omega))

theorem affine_receipt_lower (μ : CountLaw n) (hn : 0 < n)
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    ((1 + ((n : ℝ) - 1) * η) / n) * μ.load ≤
      μ.charge (Schedule.affine n η hη0 hη1) := by
  apply μ.receipt_lower
  intro r hr
  by_cases h : r = 0
  · simp [h, Schedule.affine, successIndicator]
  · have hrR : (0 : ℝ) < r := by exact_mod_cast (Nat.pos_of_ne_zero h)
    exact (le_div_iff₀ hrR).mp
      (Schedule.affine_ratio_lower n r hn (Nat.pos_of_ne_zero h) hr η hη0 hη1)

theorem ppi_utility (μ : CountLaw n) (v b g : ℝ) (G : Schedule n) :
    μ.utility v b g (Schedule.ppi n) G =
      (v - g - b) * μ.success - b * μ.duplicates - g * (μ.charge G - μ.success) := by
  rw [utility_eq, charge_ppi]
  unfold duplicates
  ring

theorem once_utility (μ : CountLaw n) (v b g : ℝ) :
    μ.utility v b g (Schedule.once n) (Schedule.once n) = (v - b - g) * μ.success := by
  rw [utility_eq, charge_once]
  ring

theorem affine_utility (μ : CountLaw n) (v b g η θ : ℝ)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    μ.utility v b g (Schedule.affine n η hη0 hη1) (Schedule.affine n θ hθ0 hθ1) =
      (v - b - g) * μ.success - (η * b + θ * g) * μ.duplicates := by
  rw [utility_eq, charge_affine, charge_affine]
  ring

theorem service_deficit (μ : CountLaw n) (v b g : ℝ) (A G : Schedule n) :
    (v - g) - μ.utility v b g A G =
      (v - g) * (1 - μ.success) + b * μ.charge A + g * (μ.charge G - μ.success) := by
  rw [utility_eq]
  ring

theorem utility_le_net_success (μ : CountLaw n) (v b g : ℝ) (A G : Schedule n)
    (hb : 0 ≤ b) (hg : 0 ≤ g) :
    μ.utility v b g A G ≤ (v - g) * μ.success := by
  rw [utility_eq]
  have hA := mul_nonneg hb (μ.charge_nonneg A)
  have hG := mul_le_mul_of_nonneg_left (μ.success_le_charge G) hg
  linarith

theorem utility_le_positive_part (μ : CountLaw n) (v b g : ℝ) (A G : Schedule n)
    (hb : 0 ≤ b) (hg : 0 ≤ g) : μ.utility v b g A G ≤ max (v - g) 0 := by
  apply le_trans (μ.utility_le_net_success v b g A G hb hg)
  by_cases hv : 0 ≤ v - g
  · rw [max_eq_left hv]
    nlinarith [μ.success_le_one]
  · rw [max_eq_right (le_of_not_ge hv)]
    exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hv) μ.success_nonneg

theorem factorial_le_n_duplicates (μ : CountLaw n) :
    μ.factorialMoment ≤ n * μ.duplicates := by
  calc
    _ ≤ μ.expect (fun r => (n : ℝ) * ((r.val : ℝ) - successIndicator r.val)) :=
      μ.expect_mono (fun r => factorial_le_duplicate n r.val (by omega))
    _ = _ := by rw [μ.expect_const_mul, ← μ.duplicates_eq_expect]

theorem two_duplicates_le_factorial (μ : CountLaw n) :
    2 * μ.duplicates ≤ μ.factorialMoment := by
  calc
    _ = μ.expect (fun r => 2 * ((r.val : ℝ) - successIndicator r.val)) := by
      rw [μ.expect_const_mul, ← μ.duplicates_eq_expect]
    _ ≤ _ := μ.expect_mono (fun r => duplicate_le_half_factorial r.val)

theorem mean_square_load_bound (μ : CountLaw n) :
    μ.load ^ 2 - μ.load ≤ μ.factorialMoment := by
  have h := μ.mean_sq_le (fun r => (r.val : ℝ))
  have he : μ.factorialMoment = μ.expect (fun r => (r.val : ℝ) ^ 2) - μ.load := by
    calc
      _ = μ.expect (fun r => (r.val : ℝ) ^ 2 - (r.val : ℝ)) := by
        apply μ.expect_congr
        intro r
        ring
      _ = _ := μ.expect_sub _ _
  rw [he]
  exact sub_le_sub_right h μ.load

theorem zero_success_iff_zero_load (μ : CountLaw n) : μ.success = 0 ↔ μ.load = 0 := by
  constructor
  · intro h
    have hu := μ.load_le_mul_success
    rw [h, mul_zero] at hu
    exact le_antisymm hu μ.load_nonneg
  · intro h
    have hu := μ.success_le_load
    rw [h] at hu
    exact le_antisymm hu μ.success_nonneg

theorem conditionalMultiplicity_bounds (μ : CountLaw n) (hS : 0 < μ.success) :
    1 ≤ conditionalMultiplicity μ.success μ.load ∧
      conditionalMultiplicity μ.success μ.load ≤ n := by
  unfold conditionalMultiplicity
  constructor
  · exact (le_div_iff₀ hS).mpr (by simpa using μ.success_le_load)
  · exact (div_le_iff₀ hS).mpr μ.load_le_mul_success

end CountLaw
end FCAppendix
