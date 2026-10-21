import FCAppendix.Affine.WeightedSampling
import FCAppendix.Affine.WeightedSampler

set_option autoImplicit false

noncomputable section
namespace FCAppendix.Affine.Uniform06.WeightedMoments
open FCAppendix.Affine.WeightedSampling
open Set MeasureTheory
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def nextMean (w : Weights ι) (h : ι → ℝ) (S : Finset ι) : ℝ :=
  (oneDraw w S).expect h

def weightedMean (w : Weights ι) (h : ι → ℝ) : ℝ :=
  (∑ i, w.1 i*h i)/totalWeight w

lemma nextMean_empty (w : Weights ι) (h : ι → ℝ) (hW : 0 < totalWeight w) :
    nextMean w h ∅ = weightedMean w h := by
  have hr : remainingWeight w ∅ = totalWeight w := by simp [remainingWeight, totalWeight]
  simp [nextMean, oneDraw_expect w ∅ (by rwa [hr] : 0 < remainingWeight w ∅) h, weightedMean, hr]

lemma abs_nextMean_le (w : Weights ι) (h : ι → ℝ) {A : ℝ}
    (hh : ∀ i, |h i| ≤ A) (S : Finset ι) : |nextMean w h S| ≤ A := by
  exact (abs_expect_le (oneDraw w S) h).trans
    (expect_le_const _ _ A (fun i _ => hh i))

lemma abs_weightedMean_le (w : Weights ι) (h : ι → ℝ) {A : ℝ}
    (hh : ∀ i, |h i| ≤ A) (hW : 0 < totalWeight w) : |weightedMean w h| ≤ A := by
  rw [← nextMean_empty w h hW]
  exact abs_nextMean_le w h hh ∅

omit [Nonempty ι] in
private lemma remaining_numerator (w : Weights ι) (h : ι → ℝ) (S : Finset ι) :
    (∑ i, if i ∈ S then 0 else w.1 i*h i) =
      (∑ i, w.1 i*h i)-(∑ i ∈ S, w.1 i*h i) := by
  classical
  have hs : (∑ i, if i ∈ S then w.1 i*h i else 0) = ∑ i ∈ S, w.1 i*h i := by simp
  have he : (∑ i, if i ∈ S then 0 else w.1 i*h i)+
      (∑ i, if i ∈ S then w.1 i*h i else 0) = ∑ i, w.1 i*h i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ S <;> simp [hi]
  rw [hs] at he
  linarith

lemma nextMean_sub_weightedMean (w : Weights ι) (h : ι → ℝ) (S : Finset ι)
    (hW : 0 < totalWeight w) (hR : 0 < remainingWeight w S) :
    nextMean w h S-weightedMean w h =
      (∑ i ∈ S, w.1 i*(weightedMean w h-h i))/remainingWeight w S := by
  rw [nextMean, oneDraw_expect w S hR h, remaining_numerator]
  have hs : (∑ i ∈ S, w.1 i*(weightedMean w h-h i)) =
      removedWeight w S*weightedMean w h-(∑ i ∈ S, w.1 i*h i) := by
    simp [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, removedWeight]
  rw [hs, remaining_eq]
  unfold weightedMean
  have hden : totalWeight w-removedWeight w S ≠ 0 := by
    rw [← remaining_eq]
    exact hR.ne'
  field_simp [hW.ne', hden]
  ring

lemma nextMean_drift_bound (w : Weights ι) (h : ι → ℝ) {A : ℝ}
    (hA : 0 ≤ A) (hh : ∀ i, |h i| ≤ A) (K : ℕ) (S : Finset ι)
    (hW : 0 < totalWeight w) (hhalf : 2*(K : ℝ) ≤ totalWeight w)
    (hS : S.card ≤ K) :
    |nextMean w h S-weightedMean w h| ≤ 4*A*K/totalWeight w := by
  have hcard : (S.card : ℝ) ≤ K := by exact_mod_cast hS
  have hRlower : totalWeight w/2 ≤ remainingWeight w S := by
    linarith [denominator_lower w S]
  have hR : 0 < remainingWeight w S := lt_of_lt_of_le (half_pos hW) hRlower
  have hbar := abs_weightedMean_le w h hh hW
  have hnum : |∑ i ∈ S, w.1 i*(weightedMean w h-h i)| ≤ 2*A*K := by
    calc
      |∑ i ∈ S, w.1 i*(weightedMean w h-h i)|
          ≤ ∑ i ∈ S, |w.1 i*(weightedMean w h-h i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ S, w.1 i*(2*A) := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul, abs_of_nonneg (w.2 i).1]
        apply mul_le_mul_of_nonneg_left _ (w.2 i).1
        have hh' : |weightedMean w h-h i| ≤ |weightedMean w h|+|h i| := by
          simpa using abs_sub_le (weightedMean w h) 0 (h i)
        linarith [hh i]
      _ = removedWeight w S*(2*A) := by rw [← Finset.sum_mul]; rfl
      _ ≤ (K : ℝ)*(2*A) :=
        mul_le_mul_of_nonneg_right ((removed_le_card w S).trans hcard) (by positivity)
      _ = 2*A*K := by ring
  rw [nextMean_sub_weightedMean w h S hW hR, abs_div,
    abs_of_pos hR]
  apply (div_le_iff₀ hR).2
  have hcoeff : 0 ≤ 4*A*K/totalWeight w := by positivity
  have hmul := mul_le_mul_of_nonneg_left hRlower hcoeff
  have he : (4*A*K/totalWeight w)*(totalWeight w/2) = 2*A*K := by
    field_simp [hW.ne']
    ring
  rw [he] at hmul
  exact hnum.trans hmul

def innovationSum (w : Weights ι) (h : ι → ℝ) :
    (n : ℕ) → Finset ι → Path ι n → ℝ
  | 0, _, _ => 0
  | n+1, S, p => h p.1-nextMean w h S+innovationSum w h n (insert p.1 S) p.2

def driftSum (w : Weights ι) (h : ι → ℝ) :
    (n : ℕ) → Finset ι → Path ι n → ℝ
  | 0, _, _ => 0
  | n+1, S, p => nextMean w h S-weightedMean w h+
      driftSum w h n (insert p.1 S) p.2

lemma centeredSum_decomposition (w : Weights ι) (h : ι → ℝ)
    (n : ℕ) (S : Finset ι) (p : Path ι n) :
    selectedSum h n p-(n : ℝ)*weightedMean w h =
      innovationSum w h n S p+driftSum w h n S p := by
  induction n generalizing S with
  | zero => simp [selectedSum, innovationSum, driftSum]
  | succ n ih =>
    have ht := ih (insert p.1 S) p.2
    simp only [selectedSum, innovationSum, driftSum]
    push_cast
    linarith

lemma innovation_mean_zero (w : Weights ι) (h : ι → ℝ)
    (n : ℕ) (S : Finset ι) :
    (pathLaw w n S).expect (innovationSum w h n S) = 0 := by
  induction n generalizing S with
  | zero => exact expect_const _ 0
  | succ n ih =>
    rw [expect_path_succ]
    simp only [innovationSum, expect_add, expect_const, ih, add_zero]
    rw [expect_sub, expect_const]
    simp [nextMean]

private lemma expect_sq_add_const {Ω : Type*} [Fintype Ω]
    (P : FiniteLaw Ω) (c : ℝ) (f : Ω → ℝ) :
    P.expect (fun a => (c+f a)^2) =
      c^2+2*c*P.expect f+P.expect (fun a => (f a)^2) := by
  have he : (fun a => (c+f a)^2) =
      (fun a => c^2+(2*c)*f a+(f a)^2) := by ext a; ring
  rw [he, expect_add, expect_add, expect_const, expect_const_mul]

private lemma square_le_square_of_abs {a B : ℝ} (hB : 0 ≤ B) (h : |a| ≤ B) :
    a^2 ≤ B^2 := by
  have hm := mul_nonneg (sub_nonneg.mpr h) (add_nonneg hB (abs_nonneg a))
  nlinarith [sq_abs a]

lemma innovation_second_moment (w : Weights ι) (h : ι → ℝ) {A : ℝ}
    (hA : 0 ≤ A) (hh : ∀ i, |h i| ≤ A) (n : ℕ) (S : Finset ι) :
    (pathLaw w n S).expect (fun p => (innovationSum w h n S p)^2) ≤
      4*A^2*n := by
  induction n generalizing S with
  | zero => simp only [innovationSum, sq, mul_zero, expect_const, Nat.cast_zero, le_refl]
  | succ n ih =>
    rw [expect_path_succ]
    calc
      _ ≤ (oneDraw w S).expect (fun _ => (2*A)^2+4*A^2*n) := by
        apply expect_le_of_support
        intro i _
        change (pathLaw w n (insert i S)).expect
          (fun p => (h i-nextMean w h S+innovationSum w h n (insert i S) p)^2) ≤ _
        rw [expect_sq_add_const, innovation_mean_zero]
        have hm : |h i-nextMean w h S| ≤ 2*A := by
          have hsub := abs_sub_le (h i) 0 (nextMean w h S)
          simp only [sub_zero, zero_sub, abs_neg] at hsub
          linarith [hh i, abs_nextMean_le w h hh S]
        have hs := square_le_square_of_abs (by positivity : 0 ≤ 2*A) hm
        have ht := ih (insert i S)
        nlinarith
      _ = (2*A)^2+4*A^2*n := expect_const _ _
      _ ≤ _ := by push_cast; nlinarith

lemma driftSum_bound (w : Weights ι) (h : ι → ℝ) {A : ℝ}
    (hA : 0 ≤ A) (hh : ∀ i, |h i| ≤ A) (K n : ℕ) (S : Finset ι)
    (hW : 0 < totalWeight w) (hhalf : 2*(K : ℝ) ≤ totalWeight w)
    (hbudget : S.card+n ≤ K) (p : Path ι n)
    (hp : 0 < (pathLaw w n S).mass p) :
    |driftSum w h n S p| ≤ (n : ℝ)*(4*A*K/totalWeight w) := by
  classical
  induction n generalizing S with
  | zero => simp [driftSum]
  | succ n ih =>
    obtain ⟨hp1,hp2⟩ := path_support_succ w n S p hp
    have hS : S.card ≤ K := by omega
    have hSc : (S.card : ℝ) ≤ K := by exact_mod_cast hS
    have hR : 0 < remainingWeight w S := by
      linarith [denominator_lower w S]
    obtain ⟨hmem,_⟩ := oneDraw_support w S hR hp1
    have hbudget' : (insert p.1 S).card+n ≤ K := by
      rw [Finset.card_insert_of_notMem hmem]
      omega
    have ht := ih (insert p.1 S) hbudget' p.2 hp2
    have hs := nextMean_drift_bound w h hA hh K S hW hhalf hS
    calc
      |driftSum w h (n+1) S p|
          ≤ |nextMean w h S-weightedMean w h|+
              |driftSum w h n (insert p.1 S) p.2| := abs_add_le _ _
      _ ≤ 4*A*K/totalWeight w+(n : ℝ)*(4*A*K/totalWeight w) := add_le_add hs ht
      _ = ((n+1 : ℕ) : ℝ)*(4*A*K/totalWeight w) := by push_cast; ring

theorem sampling_mean_bound (w : Weights ι) (h : ι → ℝ) {A : ℝ}
    (hA : 0 ≤ A) (hh : ∀ i, |h i| ≤ A) (d : ℕ)
    (hW : 0 < totalWeight w) (hhalf : 2*(d : ℝ) ≤ totalWeight w) :
    |(pathLaw w d ∅).expect (selectedSum h d)-(d : ℝ)*weightedMean w h| ≤
      4*A*(d : ℝ)^2/totalWeight w := by
  have he : (fun p : Path ι d => selectedSum h d p-(d : ℝ)*weightedMean w h) =
      (fun p => innovationSum w h d ∅ p+driftSum w h d ∅ p) := by
    ext p
    exact centeredSum_decomposition w h d ∅ p
  rw [← expect_const (pathLaw w d ∅) ((d : ℝ)*weightedMean w h),
    ← expect_sub, he, expect_add, innovation_mean_zero, zero_add]
  apply (abs_expect_le _ _).trans
  apply expect_le_const
  intro p hp
  have hb := driftSum_bound w h hA hh d d ∅ hW hhalf (by simp) p hp
  convert! hb using 1; ring

theorem sampling_second_moment (w : Weights ι) (h : ι → ℝ) {A : ℝ}
    (hA : 0 ≤ A) (hh : ∀ i, |h i| ≤ A) (d : ℕ)
    (hW : 0 < totalWeight w) (hhalf : 2*(d : ℝ) ≤ totalWeight w) :
    (pathLaw w d ∅).expect
      (fun p => (selectedSum h d p-(d : ℝ)*weightedMean w h)^2) ≤
        8*A^2*d+32*A^2*(d : ℝ)^4/(totalWeight w)^2 := by
  let B : ℝ := 4*A*(d : ℝ)^2/totalWeight w
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpoint (p : Path ι d) (hp : 0 < (pathLaw w d ∅).mass p) :
      (selectedSum h d p-(d : ℝ)*weightedMean w h)^2 ≤
        2*(innovationSum w h d ∅ p)^2+2*B^2 := by
    have hb := driftSum_bound w h hA hh d d ∅ hW hhalf (by simp) p hp
    have hb' : |driftSum w h d ∅ p| ≤ B := by convert! hb using 1; dsimp [B]; ring
    have hs := square_le_square_of_abs hB hb'
    rw [centeredSum_decomposition]
    nlinarith [sq_nonneg (innovationSum w h d ∅ p-driftSum w h d ∅ p)]
  apply le_trans (expect_le_of_support _ _ _ hpoint)
  rw [expect_add, expect_const_mul, expect_const]
  have hv := innovation_second_moment w h hA hh d ∅
  have he : 2*(4*A^2*d)+2*B^2 =
      8*A^2*d+32*A^2*(d : ℝ)^4/(totalWeight w)^2 := by dsimp [B]; ring
  rw [← he]
  linarith

def uniformWeights : Weights ι := ⟨fun _ => 1, fun _ => by norm_num⟩

omit [DecidableEq ι] [Nonempty ι] in
lemma uniform_total : totalWeight (uniformWeights : Weights ι) = Fintype.card ι := by
  simp [totalWeight, uniformWeights]

omit [Nonempty ι] in
lemma uniform_remaining (S : Finset ι) :
    remainingWeight (uniformWeights : Weights ι) S = Fintype.card ι-(S.card : ℝ) := by
  rw [remaining_eq, uniform_total]
  simp [removedWeight, uniformWeights]

lemma uniform_draw_mass (S : Finset ι) (hS : S.card < Fintype.card ι) (i : ι) :
    (oneDraw (uniformWeights : Weights ι) S).mass i =
      if i ∈ S then 0 else 1/((Fintype.card ι : ℝ)-S.card) := by
  have hp : 0 < remainingWeight (uniformWeights : Weights ι) S := by
    rw [uniform_remaining]
    exact sub_pos.mpr (by exact_mod_cast hS)
  rw [oneDraw_mass _ _ hp, uniform_remaining]
  by_cases hi : i ∈ S <;> simp [hi, uniformWeights]

theorem integrate_listwise_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (h : ∀ᵐ ω ∂μ, f ω ≤ g ω) : (∫ ω, f ω ∂μ) ≤ ∫ ω, g ω ∂μ :=
  integral_mono_ae hf hg h

theorem finite_tilt_mean_bound {Ω : Type*} [Fintype Ω]
    (P : FiniteLaw Ω) (w : Ω → Weights ι) (h : Ω → ι → ℝ)
    (d : Ω → ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hh : ∀ ω i, |h ω i| ≤ A)
    (hW : ∀ ω, 0 < totalWeight (w ω))
    (hhalf : ∀ ω, 2*(d ω : ℝ) ≤ totalWeight (w ω)) :
    P.expect (fun ω => |(pathLaw (w ω) (d ω) ∅).expect (selectedSum (h ω) (d ω))-
      (d ω : ℝ)*weightedMean (w ω) (h ω)|) ≤
    P.expect (fun ω => 4*A*(d ω : ℝ)^2/totalWeight (w ω)) := by
  apply expect_le_of_support
  intro ω _
  exact sampling_mean_bound (w ω) (h ω) hA (hh ω) (d ω) (hW ω) (hhalf ω)

theorem finite_tilt_second_moment {Ω : Type*} [Fintype Ω]
    (P : FiniteLaw Ω) (w : Ω → Weights ι) (h : Ω → ι → ℝ)
    (d : Ω → ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hh : ∀ ω i, |h ω i| ≤ A)
    (hW : ∀ ω, 0 < totalWeight (w ω))
    (hhalf : ∀ ω, 2*(d ω : ℝ) ≤ totalWeight (w ω)) :
    P.expect (fun ω => (pathLaw (w ω) (d ω) ∅).expect
      (fun p => (selectedSum (h ω) (d ω) p-(d ω : ℝ)*weightedMean (w ω) (h ω))^2)) ≤
    P.expect (fun ω => 8*A^2*d ω+32*A^2*(d ω : ℝ)^4/(totalWeight (w ω))^2) := by
  apply expect_le_of_support
  intro ω _
  exact sampling_second_moment (w ω) (h ω) hA (hh ω) (d ω) (hW ω) (hhalf ω)

end FCAppendix.Affine.Uniform06.WeightedMoments

namespace FCAppendix.Affine.Uniform06.WeightedMoments
open FCAppendix.Affine.WeightedSampling
open MeasureTheory Set
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
lemma abs_selectedSum_le {h : ι → ℝ} {A : ℝ} (_hA : 0 ≤ A)
    (hh : ∀ i, |h i| ≤ A) (d : ℕ) (p : Path ι d) :
    |selectedSum h d p| ≤ (d : ℝ) * A := by
  induction d with
  | zero => simp [selectedSum]
  | succ d ih =>
    calc
      |selectedSum h (d+1) p| ≤ |h p.1| + |selectedSum h d p.2| := abs_add_le _ _
      _ ≤ A + (d : ℝ) * A := add_le_add (hh p.1) (ih p.2)
      _ = ((d+1 : ℕ) : ℝ) * A := by push_cast; ring

lemma abs_centeredSum_le (w : Weights ι) (h : ι → ℝ) {A : ℝ}
    (hA : 0 ≤ A) (hh : ∀ i, |h i| ≤ A) (hW : 0 < totalWeight w)
    (d : ℕ) (p : Path ι d) :
    |selectedSum h d p - (d : ℝ) * weightedMean w h| ≤ 2*A*d := by
  calc
    _ ≤ |selectedSum h d p| + |(d : ℝ)*weightedMean w h| := by simpa using abs_sub_le (selectedSum h d p) 0 ((d : ℝ)*weightedMean w h)
    _ = |selectedSum h d p| + (d : ℝ)*|weightedMean w h| := by
      have hd : |(d : ℝ)| = (d : ℝ) := abs_of_nonneg (Nat.cast_nonneg d)
      rw [abs_mul, hd]
    _ ≤ (d : ℝ)*A + (d : ℝ)*A := add_le_add
      (abs_selectedSum_le hA hh d p)
      (mul_le_mul_of_nonneg_left (abs_weightedMean_le w h hh hW) (Nat.cast_nonneg d))
    _ = _ := by ring

theorem sampling_mean_bound_all (w : Weights ι) (h : ι → ℝ) {A : ℝ}
    (hA : 0 ≤ A) (hh : ∀ i, |h i| ≤ A) (d : ℕ)
    (hW : 0 < totalWeight w) :
    |(pathLaw w d ∅).expect (selectedSum h d) - (d : ℝ)*weightedMean w h| ≤
      4*A*(d : ℝ)^2/totalWeight w := by
  by_cases hhalf : 2*(d : ℝ) ≤ totalWeight w
  · exact sampling_mean_bound w h hA hh d hW hhalf
  · have hsmall : totalWeight w ≤ 2*(d : ℝ) := (lt_of_not_ge hhalf).le
    have htriv : |(pathLaw w d ∅).expect (selectedSum h d) -
        (d : ℝ)*weightedMean w h| ≤ 2*A*d := by
      rw [← expect_const (pathLaw w d ∅) ((d : ℝ)*weightedMean w h), ← expect_sub]
      apply (abs_expect_le _ _).trans
      apply expect_le_const
      intro p _
      exact abs_centeredSum_le w h hA hh hW d p
    apply htriv.trans
    apply (le_div_iff₀ hW).2
    have hmul := mul_le_mul_of_nonneg_left hsmall
      (show 0 ≤ 2*A*(d : ℝ) by positivity)
    nlinarith

theorem sampling_second_moment_all (w : Weights ι) (h : ι → ℝ) {A : ℝ}
    (hA : 0 ≤ A) (hh : ∀ i, |h i| ≤ A) (d : ℕ)
    (hW : 0 < totalWeight w) :
    (pathLaw w d ∅).expect
      (fun p => (selectedSum h d p-(d : ℝ)*weightedMean w h)^2) ≤
      8*A^2*d + 32*A^2*(d : ℝ)^4/(totalWeight w)^2 := by
  by_cases hhalf : 2*(d : ℝ) ≤ totalWeight w
  · exact sampling_second_moment w h hA hh d hW hhalf
  · have hsmall : totalWeight w ≤ 2*(d : ℝ) := (lt_of_not_ge hhalf).le
    have htriv : (pathLaw w d ∅).expect
        (fun p => (selectedSum h d p-(d : ℝ)*weightedMean w h)^2) ≤
        (2*A*(d : ℝ))^2 := by
      apply expect_le_const
      intro p _
      exact square_le_square_of_abs (by positivity)
        (abs_centeredSum_le w h hA hh hW d p)
    have hs : (totalWeight w)^2 ≤ (2*(d : ℝ))^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hsmall) (by positivity : 0 ≤ 2*(d : ℝ)+totalWeight w)]
    have hb : (2*A*(d : ℝ))^2 ≤ 32*A^2*(d : ℝ)^4/(totalWeight w)^2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hW)).2
      have hm := mul_le_mul_of_nonneg_left hs
        (show 0 ≤ (2*A*(d : ℝ))^2 from sq_nonneg _)
      nlinarith [sq_nonneg (A*(d : ℝ)^2)]
    exact htriv.trans (hb.trans (le_add_of_nonneg_left (by positivity)))

theorem integrate_sampling_mean_all {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (w : Ω → Weights ι) (h : Ω → ι → ℝ)
    (d : Ω → ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hh : ∀ᵐ ω ∂μ, ∀ i, |h ω i| ≤ A)
    (hW : ∀ᵐ ω ∂μ, 0 < totalWeight (w ω))
    (hleft : Integrable (fun ω => |(pathLaw (w ω) (d ω) ∅).expect
      (selectedSum (h ω) (d ω))-(d ω : ℝ)*weightedMean (w ω) (h ω)|) μ)
    (hright : Integrable (fun ω => 4*A*(d ω : ℝ)^2/totalWeight (w ω)) μ) :
    (∫ ω, |(pathLaw (w ω) (d ω) ∅).expect (selectedSum (h ω) (d ω))-
      (d ω : ℝ)*weightedMean (w ω) (h ω)| ∂μ) ≤
    ∫ ω, 4*A*(d ω : ℝ)^2/totalWeight (w ω) ∂μ := by
  apply integral_mono_ae hleft hright
  filter_upwards [hh,hW] with ω hω hWω
  exact sampling_mean_bound_all (w ω) (h ω) hA hω (d ω) hWω

theorem exists_uniform_sampler_moment_identities (w : Weights ι) (d : ℕ) :
    ∃ F : unitInterval → Path ι d,
      Measurable F ∧
      volume.map F = FiniteLaw.probabilityMeasure (pathLaw w d ∅) := by
  obtain ⟨F,hF,hLaw⟩ := FCAppendix.Affine.WeightedSampling.exists_weighted_sampler
    (ι := ι) d ∅
  exact ⟨F w, hF.comp (measurable_const.prodMk measurable_id), hLaw w⟩

end FCAppendix.Affine.Uniform06.WeightedMoments
