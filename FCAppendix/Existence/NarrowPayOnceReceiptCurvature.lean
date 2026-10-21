import FCAppendix.PayOnce.OwnImpact

noncomputable section
namespace FCAppendix.Existence.NarrowPayOnce
open Set
open PayOnce PayOnce.OwnImpact
open scoped BigOperators

def Hcurvature (n : ℕ) (p : ℝ) : ℝ :=
  (∑ j ∈ Finset.range n, (j:ℝ)*((j-1:ℕ):ℝ)*(1-p)^(j-2))/(n:ℝ)

theorem hasDerivAt_Hslope (n : ℕ) (p : ℝ) :
    HasDerivAt (Hslope n) (-Hcurvature n p) p := by
  have hterm (j : ℕ) : HasDerivAt (fun x : ℝ => (j:ℝ)*(1-x)^(j-1))
      (-((j:ℝ)*((j-1:ℕ):ℝ)*(1-p)^(j-2))) p := by
    have hh := (((hasDerivAt_id p).const_sub 1).pow (j-1)).const_mul (j:ℝ)
    convert hh using 1 <;> first | rfl | (simp only [Nat.sub_sub,id_eq]; ring)
  have hh := (HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.range n) => hterm j)).div_const (n:ℝ)
  convert hh using 1 <;> first | rfl | (simp only [Hcurvature,Finset.sum_neg_distrib,neg_div])

theorem Hcurvature_nonneg (n : ℕ) {p : ℝ} (hp : p ≤ 1) : 0 ≤ Hcurvature n p := by
  unfold Hcurvature
  positivity

theorem Hcurvature_upper {n : ℕ} (hn : 0<n) {p : ℝ} (hp : p ∈ Icc (0:ℝ) 1) :
    Hcurvature n p ≤ (n:ℝ)^2 := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  unfold Hcurvature
  apply (div_le_iff₀ hnR).mpr
  calc
    _ ≤ ∑ _j ∈ Finset.range n, (n:ℝ)^2 := by
      apply Finset.sum_le_sum
      intro j hj
      have hjn : (j:ℝ) ≤ n := by exact_mod_cast (Finset.mem_range.mp hj).le
      have hj1n : ((j-1:ℕ):ℝ) ≤ n := by exact_mod_cast (Nat.sub_le j 1).trans (Finset.mem_range.mp hj).le
      have hpow : (1-p)^(j-2) ≤ 1 := pow_le_one₀ (sub_nonneg.mpr hp.2) (by linarith [hp.1])
      have hprod := mul_le_mul hjn hj1n (Nat.cast_nonneg (j-1)) (Nat.cast_nonneg n)
      have hh := mul_le_of_le_one_right (mul_nonneg (Nat.cast_nonneg j) (Nat.cast_nonneg (j-1))) hpow
      exact hh.trans (by nlinarith [hprod])
    _ = _ := by simp; ring

def Hthird (n : ℕ) (p : ℝ) : ℝ :=
  (∑ j ∈ Finset.range n, (j:ℝ)*((j-1:ℕ):ℝ)*((j-2:ℕ):ℝ)*(1-p)^(j-3))/(n:ℝ)

theorem hasDerivAt_Hcurvature (n : ℕ) (p : ℝ) :
    HasDerivAt (Hcurvature n) (-Hthird n p) p := by
  have hterm (j : ℕ) : HasDerivAt (fun x : ℝ => (j:ℝ)*((j-1:ℕ):ℝ)*(1-x)^(j-2))
      (-((j:ℝ)*((j-1:ℕ):ℝ)*((j-2:ℕ):ℝ)*(1-p)^(j-3))) p := by
    have hh := (((hasDerivAt_id p).const_sub 1).pow (j-2)).const_mul ((j:ℝ)*((j-1:ℕ):ℝ))
    convert hh using 1 <;> first | rfl | (simp only [Nat.sub_sub,id_eq]; ring)
  have hh := (HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.range n) => hterm j)).div_const (n:ℝ)
  convert hh using 1 <;> first | rfl | (simp only [Hthird,Finset.sum_neg_distrib,neg_div])

theorem Hthird_nonneg (n : ℕ) {p : ℝ} (hp : p ≤ 1) : 0 ≤ Hthird n p := by
  unfold Hthird
  positivity

theorem Hthird_upper {n : ℕ} (hn : 0<n) {p : ℝ} (hp : p ∈ Icc (0:ℝ) 1) :
    Hthird n p ≤ (n:ℝ)^3 := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  unfold Hthird
  apply (div_le_iff₀ hnR).mpr
  calc
    _ ≤ ∑ _j ∈ Finset.range n, (n:ℝ)^3 := by
      apply Finset.sum_le_sum
      intro j hj
      have hjn : (j:ℝ) ≤ n := by exact_mod_cast (Finset.mem_range.mp hj).le
      have hj1n : ((j-1:ℕ):ℝ) ≤ n := by exact_mod_cast (Nat.sub_le j 1).trans (Finset.mem_range.mp hj).le
      have hj2n : ((j-2:ℕ):ℝ) ≤ n := by exact_mod_cast (Nat.sub_le j 2).trans (Finset.mem_range.mp hj).le
      have hpow : (1-p)^(j-3) ≤ 1 := pow_le_one₀ (sub_nonneg.mpr hp.2) (by linarith [hp.1])
      calc
        _ ≤ (n:ℝ)*n*n*1 := by gcongr; exact pow_nonneg (sub_nonneg.mpr hp.2) _
        _ = _ := by ring
    _ = _ := by simp; ring

end FCAppendix.Existence.NarrowPayOnce
