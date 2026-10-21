import FCAppendix.Affine.Uniform06.WeightedMoments

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.WeightedReplacement

open FCAppendix.Affine.WeightedSampling
open FCAppendix.Affine.Uniform06.WeightedMoments
open Set MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def iidPathLaw (w : Weights ι) : (n : ℕ) → FiniteLaw (Path ι n)
  | 0 => FiniteLaw.dirac PUnit.unit
  | n+1 => pairLaw (oneDraw w ∅) (fun _ => iidPathLaw w n)

theorem expect_iid_succ (w : Weights ι) (n : ℕ) (f : Path ι (n+1) → ℝ) :
    (iidPathLaw w (n+1)).expect f =
      (oneDraw w ∅).expect (fun a => (iidPathLaw w n).expect (fun p => f (a,p))) :=
  expect_pairLaw _ _ _

theorem abs_expect_le_bound {Ω : Type*} [Fintype Ω]
    (P : FiniteLaw Ω) (f : Ω → ℝ) {A : ℝ} (hf : ∀ a, |f a| ≤ A) :
    |P.expect f| ≤ A :=
  (abs_expect_le P f).trans (expect_le_const P _ A (fun a _ => hf a))

theorem path_expectation_error (w : Weights ι) (K n : ℕ)
    (S : Finset ι) {A : ℝ} (hA : 0 ≤ A)
    (hW : 0 < totalWeight w) (hhalf : 2*(K:ℝ) ≤ totalWeight w)
    (hbudget : S.card+n ≤ K) (f : Path ι n → ℝ)
    (hf : ∀ p, |f p| ≤ A) :
    |(pathLaw w n S).expect f-(iidPathLaw w n).expect f| ≤
      4*A*n*K/totalWeight w := by
  induction n generalizing S with
  | zero => simp [pathLaw, iidPathLaw]
  | succ n ih =>
    rw [expect_path_succ, expect_iid_succ]
    let fS : ι → ℝ := fun a =>
      (pathLaw w n (insert a S)).expect (fun p => f (a,p))
    let fI : ι → ℝ := fun a =>
      (iidPathLaw w n).expect (fun p => f (a,p))
    have hbudget' (a : ι) : (insert a S).card+n ≤ K := by
      have h := Finset.card_insert_le a S
      omega
    have hdiff (a : ι) : |fS a-fI a| ≤ 4*A*n*K/totalWeight w :=
      ih (insert a S) (hbudget' a) (fun p => f (a,p)) (fun p => hf (a,p))
    have hI (a : ι) : |fI a| ≤ A :=
      abs_expect_le_bound _ _ (fun p => hf (a,p))
    have htail : |(oneDraw w S).expect fS-(oneDraw w S).expect fI| ≤
        4*A*n*K/totalWeight w := by
      rw [← expect_sub]
      exact abs_expect_le_bound _ _ hdiff
    have hstep := nextMean_drift_bound w fI hA hI K S hW hhalf
      (by omega : S.card ≤ K)
    rw [← nextMean_empty w fI hW] at hstep
    change |(oneDraw w S).expect fI-(oneDraw w ∅).expect fI| ≤ _ at hstep
    change |(oneDraw w S).expect fS-(oneDraw w ∅).expect fI| ≤ _
    calc
      _ ≤ |(oneDraw w S).expect fS-(oneDraw w S).expect fI|+
          |(oneDraw w S).expect fI-(oneDraw w ∅).expect fI| :=
        abs_sub_le _ _ _
      _ ≤ 4*A*n*K/totalWeight w+4*A*K/totalWeight w := add_le_add htail hstep
      _ = _ := by push_cast; ring

def pathProduct (h : ι → ℝ) : (n : ℕ) → Path ι n → ℝ
  | 0, _ => 1
  | n+1, p => h p.1*pathProduct h n p.2

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem pathProduct_bounds (h : ι → ℝ) (hh : ∀ a, h a ∈ Icc (0:ℝ) 1)
    (n : ℕ) (p : Path ι n) : pathProduct h n p ∈ Icc (0:ℝ) 1 := by
  induction n with
  | zero => simp [pathProduct]
  | succ n ih =>
    exact ⟨mul_nonneg (hh p.1).1 (ih p.2).1,
      (mul_le_mul (hh p.1).2 (ih p.2).2 (ih p.2).1 (by norm_num)).trans_eq
        (by norm_num)⟩

theorem iid_product_mean (w : Weights ι) (h : ι → ℝ)
    (hW : 0 < totalWeight w) (n : ℕ) :
    (iidPathLaw w n).expect (pathProduct h n) = (weightedMean w h)^n := by
  induction n with
  | zero => simp [iidPathLaw, pathProduct]
  | succ n ih =>
    rw [expect_iid_succ]
    simp only [pathProduct, expect_const_mul, ih]
    rw [expect_mul_const]
    change nextMean w h ∅*(weightedMean w h)^n = _
    rw [nextMean_empty w h hW, pow_succ]
    ring

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem pathProduct_exp (h : ι → ℝ) (θ : ℝ) (n : ℕ) (p : Path ι n) :
    pathProduct (fun a => Real.exp (-θ*h a)) n p =
      Real.exp (-θ*selectedSum h n p) := by
  induction n with
  | zero => simp [pathProduct, selectedSum]
  | succ n ih =>
    rw [pathProduct, ih]
    rw [← Real.exp_add]
    congr 1
    simp only [selectedSum]
    ring

theorem exponential_sample_error (w : Weights ι) (h : ι → ℝ)
    (hh : ∀ a, 0 ≤ h a) {θ : ℝ} (hθ : 0 ≤ θ)
    (K n : ℕ) (S : Finset ι)
    (hW : 0 < totalWeight w) (hhalf : 2*(K:ℝ) ≤ totalWeight w)
    (hbudget : S.card+n ≤ K) :
    |(pathLaw w n S).expect (fun p => Real.exp (-θ*selectedSum h n p))-
      (weightedMean w (fun a => Real.exp (-θ*h a)))^n| ≤
        4*n*K/totalWeight w := by
  have hexp (a : ι) : Real.exp (-θ*h a) ∈ Icc (0:ℝ) 1 := by
    exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hθ) (hh a))⟩
  have he := path_expectation_error w K n S (A := 1) (by norm_num)
    hW hhalf hbudget (pathProduct (fun a => Real.exp (-θ*h a)) n)
    (fun p => by
      have hp := pathProduct_bounds _ hexp n p
      simpa only [abs_of_nonneg hp.1] using hp.2)
  rw [iid_product_mean w _ hW] at he
  have hp : pathProduct (fun a => Real.exp (-θ*h a)) n =
      (fun p => Real.exp (-θ*selectedSum h n p)) := funext (pathProduct_exp h θ n)
  simpa only [hp, mul_one, one_mul] using he

end FCAppendix.Affine.Uniform06.WeightedReplacement
