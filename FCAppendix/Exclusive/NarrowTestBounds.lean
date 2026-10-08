import FCAppendix.Exclusive.NarrowCalculus

namespace FCAppendix.Exclusive.Narrow
open MeasureTheory Filter Topology Set
open scoped BigOperators

def CountTestBound (n : ℕ) (f : ℕ → ℝ) (K : ℝ) : Prop :=
  0 ≤ K ∧ ∀ j, j ≤ n → |f j| ≤ K

lemma countTestBound_exists (n : ℕ) (f : ℕ → ℝ) : ∃ K, CountTestBound n f K := by
  refine ⟨∑ j ∈ Finset.range (n + 1), |f j|, ?_, ?_⟩
  · exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  · intro j hj
    exact Finset.single_le_sum (f := fun j : ℕ => |f j|)
      (s := Finset.range (n + 1)) (a := j) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.mpr (by omega))

lemma continuous_binomialPolynomial (n : ℕ) (f : ℕ → ℝ) :
    Continuous (binomialPolynomial n f) :=
  continuous_iff_continuousAt.mpr fun p =>
    (hasDerivAt_binomialPolynomial n f p).continuousAt

lemma continuous_binomialPolynomialDerivative (n : ℕ) (f : ℕ → ℝ) :
    Continuous (binomialPolynomialDerivative n f) := by
  induction n generalizing f with
  | zero => exact continuous_const
  | succ n ih =>
    exact (((continuous_binomialPolynomial n f).neg.add
      ((continuous_const.sub continuous_id).mul (ih f))).add
      (continuous_binomialPolynomial n (fun j => f (1+j)))).add
      (continuous_id.mul (ih (fun j => f (1+j))))

lemma abs_binomialPolynomial_le (n : ℕ) (f : ℕ → ℝ) {K p : ℝ}
    (hf : CountTestBound n f K) (hp : p ∈ Icc (0 : ℝ) 1) :
    |binomialPolynomial n f p| ≤ K := by
  induction n generalizing f with
  | zero => exact hf.2 0 le_rfl
  | succ n ih =>
    have h0 : CountTestBound n f K := ⟨hf.1, fun j hj => hf.2 j (by omega)⟩
    have h1 : CountTestBound n (fun j => f (1+j)) K :=
      ⟨hf.1, fun j hj => hf.2 (1+j) (by omega)⟩
    calc
      |binomialPolynomial (n+1) f p| ≤
          |(1-p) * binomialPolynomial n f p| +
            |p * binomialPolynomial n (fun j => f (1+j)) p| := abs_add_le _ _
      _ = (1-p) * |binomialPolynomial n f p| +
            p * |binomialPolynomial n (fun j => f (1+j)) p| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hp.2), abs_of_nonneg hp.1]
      _ ≤ (1-p)*K + p*K := add_le_add
        (mul_le_mul_of_nonneg_left (ih f h0) (sub_nonneg.mpr hp.2))
        (mul_le_mul_of_nonneg_left (ih _ h1) hp.1)
      _ = K := by ring

lemma abs_binomialPolynomialDerivative_le (n : ℕ) (f : ℕ → ℝ) {K p : ℝ}
    (hf : CountTestBound n f K) (hp : p ∈ Icc (0 : ℝ) 1) :
    |binomialPolynomialDerivative n f p| ≤ 2 * (n : ℝ) * K := by
  induction n generalizing f with
  | zero => simp [binomialPolynomialDerivative]
  | succ n ih =>
    have h0 : CountTestBound n f K := ⟨hf.1, fun j hj => hf.2 j (by omega)⟩
    have h1 : CountTestBound n (fun j => f (1+j)) K :=
      ⟨hf.1, fun j hj => hf.2 (1+j) (by omega)⟩
    have hval0 := abs_binomialPolynomial_le n f h0 hp
    have hval1 := abs_binomialPolynomial_le n (fun j => f (1+j)) h1 hp
    have hder0 := ih f h0
    have hder1 := ih (fun j => f (1+j)) h1
    calc
      |binomialPolynomialDerivative (n+1) f p| ≤
          |binomialPolynomial n f p| +
          (1-p) * |binomialPolynomialDerivative n f p| +
          |binomialPolynomial n (fun j => f (1+j)) p| +
          p * |binomialPolynomialDerivative n (fun j => f (1+j)) p| := by
        dsimp only [binomialPolynomialDerivative]
        calc
          _ ≤ |-binomialPolynomial n f p +
              (1-p)*binomialPolynomialDerivative n f p +
              binomialPolynomial n (fun j => f (1+j)) p| +
              |p*binomialPolynomialDerivative n (fun j => f (1+j)) p| := abs_add_le _ _
          _ ≤ (|-binomialPolynomial n f p + (1-p)*binomialPolynomialDerivative n f p| +
              |binomialPolynomial n (fun j => f (1+j)) p|) +
              |p*binomialPolynomialDerivative n (fun j => f (1+j)) p| := by
            gcongr; exact abs_add_le _ _
          _ ≤ ((|-binomialPolynomial n f p| +
              |(1-p)*binomialPolynomialDerivative n f p|) +
              |binomialPolynomial n (fun j => f (1+j)) p|) +
              |p*binomialPolynomialDerivative n (fun j => f (1+j)) p| := by
            gcongr; exact abs_add_le _ _
          _ = _ := by
            rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hp.2),
              abs_of_nonneg hp.1]
      _ ≤ K + (1-p)*(2*(n:ℝ)*K) + K + p*(2*(n:ℝ)*K) := by
        have hp0 := hp.1
        have hq0 := sub_nonneg.mpr hp.2
        gcongr
      _ = 2*((n+1:ℕ):ℝ)*K := by push_cast; ring

lemma success_test_bound (n : ℕ) : CountTestBound n successIndicator 1 := by
  refine ⟨zero_le_one, ?_⟩
  intro j _
  by_cases hj : j = 0 <;> simp [successIndicator, hj]

lemma schedule_test_bound {n : ℕ} (G : Schedule n) :
    CountTestBound n G.charge n := by
  refine ⟨Nat.cast_nonneg _, ?_⟩
  intro j hj
  rw [abs_of_nonneg (G.nonneg j hj)]
  exact (G.upper j hj).trans (by exact_mod_cast hj)

lemma tariff_test_bound (n : ℕ) (hn : 1 ≤ n) (a : UserTariff) (ha : a.Allowed) :
    CountTestBound n a.charge n := by
  refine ⟨Nat.cast_nonneg _, ?_⟩
  intro j hj
  rw [abs_of_nonneg (a.charge_nonneg ha j)]
  cases a with
  | unique =>
    simp only [UserTariff.charge]
    split_ifs
    · exact_mod_cast hn
    · exact Nat.cast_nonneg _
  | affine eta =>
    rw [UserTariff.charge_affine_eq_schedule eta ha.1 ha.2 n j]
    exact ((Schedule.affine n eta ha.1 ha.2).upper j hj).trans (by exact_mod_cast hj)

lemma binomialPolynomialDerivative_success (k : ℕ) (p : ℝ) :
    binomialPolynomialDerivative (k+1) successIndicator p =
      ((k+1 : ℕ) : ℝ) * (1-p)^k := by
  have h := hasDerivAt_binomialPolynomial (k+1) successIndicator p
  have he : binomialPolynomial (k+1) successIndicator = PayOnce.success (k+1) :=
    funext (binomialPolynomial_once (k+1))
  rw [he] at h
  exact h.unique (hasDerivAt_success k p)

end FCAppendix.Exclusive.Narrow
