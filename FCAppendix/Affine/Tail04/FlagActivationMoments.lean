import FCAppendix.Affine.Tail04.WeightedFairInterval
import FCAppendix.Probability.Bounds

noncomputable section
namespace FCAppendix.Affine.Tail04.WeightedFlagBound
open Set
open scoped BigOperators
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]

theorem expect_distinct_coordinates (mu : ι → FiniteLaw Ω)
    (i j : ι) (hij : i ≠ j) (f g : Ω → ℝ) :
    (BidDependentFlags.product mu).expect (fun omega => f (omega i) * g (omega j)) =
      (mu i).expect f * (mu j).expect g := by
  classical
  let h : ι → Ω → ℝ := fun k x =>
    (if k=i then f x else 1) * (if k=j then g x else 1)
  have hprod (omega : ι → Ω) :
      (∏ k, h k (omega k)) = f (omega i) * g (omega j) := by
    unfold h
    rw [Finset.prod_mul_distrib]
    simp
  have he (k : ι) : (mu k).expect (h k) =
      (if k=i then (mu i).expect f else 1) *
        (if k=j then (mu j).expect g else 1) := by
    by_cases hi : k=i
    · subst k
      simp [h, hij]
    · by_cases hj : k=j
      · subst k
        simp [h, hi]
      · simp [h, hi, hj]
  calc
    _ = (BidDependentFlags.product mu).expect (fun omega => ∏ k, h k (omega k)) := by
      apply FiniteLaw.expect_congr
      intro omega
      exact (hprod omega).symm
    _ = ∏ k, (mu k).expect (h k) := BidDependentFlags.expect_product mu h
    _ = _ := by simp_rw [he]; rw [Finset.prod_mul_distrib]; simp

def activationCount (flags : ι → Bool) : ℝ := ∑ i, bit (flags i)

def constantFlags (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : FiniteLaw (ι → Bool) :=
  BidDependentFlags.flags (fun _ : ι => p) (fun _ => hp0) (fun _ => hp1)

theorem constantFlags_mean (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (constantFlags (ι:=ι) p hp0 hp1).expect activationCount =
      (Fintype.card ι : ℝ) * p := by
  unfold activationCount
  rw [FiniteLaw.expect_finset_sum]
  have he (i : ι) : (constantFlags (ι:=ι) p hp0 hp1).expect (fun flags=>bit (flags i))=p := by
    change (BidDependentFlags.product (fun _ : ι=>IndependentCounts.bernoulli p hp0 hp1)).expect
      (fun flags=>bit (flags i))=p
    rw [BidDependentFlags.expect_coordinate (fun _ : ι=>IndependentCounts.bernoulli p hp0 hp1) i bit,
      IndependentCounts.expect_bernoulli]
    simp [bit]
  simp_rw [he]
  simp

theorem constantFlags_centered_second (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (constantFlags (ι:=ι) p hp0 hp1).expect
      (fun flags => (activationCount flags - (Fintype.card ι : ℝ)*p)^2) =
      (Fintype.card ι : ℝ) * p * (1-p) := by
  let mu := constantFlags (ι:=ι) p hp0 hp1
  let x : ι → (ι → Bool) → ℝ := fun i flags => bit (flags i)-p
  have hxmean (i : ι) :
      (IndependentCounts.bernoulli p hp0 hp1).expect (fun b => bit b-p) = 0 := by
    rw [IndependentCounts.expect_bernoulli]
    simp only [bit, Bool.false_eq_true, ite_false, ite_true]
    ring
  have hdiag (i : ι) : mu.expect (fun flags => x i flags * x i flags) = p*(1-p) := by
    change (BidDependentFlags.product (fun _ : ι => IndependentCounts.bernoulli p hp0 hp1)).expect
      (fun flags => (bit (flags i)-p)*(bit (flags i)-p)) = _
    rw [BidDependentFlags.expect_coordinate (fun _ : ι => IndependentCounts.bernoulli p hp0 hp1) i
      (fun b => (bit b-p)*(bit b-p)), IndependentCounts.expect_bernoulli]
    simp only [bit, Bool.false_eq_true, ite_false, ite_true]
    ring
  have hoff (i j : ι) (hij : i ≠ j) :
      mu.expect (fun flags => x i flags * x j flags) = 0 := by
    change (BidDependentFlags.product (fun _ : ι => IndependentCounts.bernoulli p hp0 hp1)).expect
      (fun flags => (bit (flags i)-p)*(bit (flags j)-p)) = _
    rw [expect_distinct_coordinates (fun _ : ι => IndependentCounts.bernoulli p hp0 hp1) i j hij
      (fun b => bit b-p) (fun b => bit b-p), hxmean i, zero_mul]
  have hcenter (flags : ι → Bool) :
      activationCount flags - (Fintype.card ι : ℝ)*p = ∑ i, x i flags := by
    simp [activationCount, x, Finset.sum_sub_distrib]
  calc
    _ = mu.expect (fun flags => ∑ i, ∑ j, x i flags * x j flags) := by
      apply FiniteLaw.expect_congr
      intro flags
      rw [hcenter]
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm
    _ = ∑ i, ∑ j, mu.expect (fun flags => x i flags * x j flags) := by
      rw [FiniteLaw.expect_finset_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact FiniteLaw.expect_finset_sum _ _ _
    _ = ∑ i : ι, p*(1-p) := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        _ = mu.expect (fun flags => x i flags * x i flags) := by
          apply Finset.sum_eq_single i
          · intro j _ hji
            exact hoff i j hji.symm
          · simp
        _ = _ := hdiag i
    _ = _ := by simp; ring

theorem constantFlags_variance (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (constantFlags (ι:=ι) p hp0 hp1).variance activationCount =
      (Fintype.card ι : ℝ) * p * (1-p) := by
  rw [FiniteLaw.variance, constantFlags_mean]
  exact constantFlags_centered_second p hp0 hp1

theorem activation_lower_tail {epsilon : ℝ} (heps : 0 < epsilon)
    (heps' : epsilon < 1/2) (hN : 0 < Fintype.card ι) :
    (constantFlags (ι:=ι) (2*epsilon) (by positivity) (by linarith)).prob
      (fun flags => activationCount flags < epsilon*(Fintype.card ι : ℝ)) ≤
        2 / (epsilon*(Fintype.card ι : ℝ)) := by
  let mu := constantFlags (ι:=ι) (2*epsilon) (by positivity) (by linarith)
  have hn : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast hN
  have ht : 0 < epsilon*(Fintype.card ι : ℝ) := mul_pos heps hn
  have hsub : mu.prob (fun flags => activationCount flags < epsilon*(Fintype.card ι : ℝ)) ≤
      mu.prob (fun flags => epsilon*(Fintype.card ι : ℝ) ≤
        |activationCount flags-mu.expect activationCount|) := by
    apply FiniteLaw.prob_mono
    intro flags hflags
    rw [constantFlags_mean]
    have hh := neg_le_abs (activationCount flags-(Fintype.card ι : ℝ)*(2*epsilon))
    linarith
  have hc := mu.chebyshev activationCount (epsilon*(Fintype.card ι : ℝ)) ht
  rw [constantFlags_variance] at hc
  have halgebra :
      (Fintype.card ι : ℝ)*(2*epsilon)*(1-2*epsilon) /
        (epsilon*(Fintype.card ι : ℝ))^2 ≤ 2/(epsilon*(Fintype.card ι : ℝ)) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos ht) ht).mpr
    nlinarith [mul_nonneg heps.le (sq_nonneg (epsilon*(Fintype.card ι : ℝ)))]
  exact hsub.trans (hc.trans halgebra)

end FCAppendix.Affine.Tail04.WeightedFlagBound
