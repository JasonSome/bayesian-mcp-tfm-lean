import FCAppendix.Affine.Tail04.TypicalLottery

noncomputable section
namespace FCAppendix.Affine.Tail04
open Set Classical
open scoped BigOperators
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]

def privateTypicalMixture (mu : FiniteLaw Ω) (xi : ℝ) (c : ℕ)
    (fixed : Ω → Finset ι) (I : Finset ι) (b : ι → ℝ) : FiniteLaw (Finset ι) :=
  FiniteLaw.finiteMix mu (fun omega => typicalLottery xi c (fixed omega) I b)

def receiptAgainstSelection (xi bi : ℝ) (i : ι) (S : Finset ι) : ℝ :=
  bi * (1 - xi * (if i ∈ S then 1 else 0))

omit [Fintype ι] in
theorem receiptAgainstSelection_eq (xi bi : ℝ) (i : ι) (S : Finset ι) :
    receiptAgainstSelection xi bi i S = if i ∈ S then (1 - xi) * bi else bi := by
  unfold receiptAgainstSelection
  split_ifs <;> ring

omit [Fintype ι] [DecidableEq ι] in
theorem realizedMixedMarginal_receipt {xi : ℝ} (hxi : 0 < xi)
    (c : ℕ) (fixed I : Finset ι) (b : ι → ℝ) (i : ι) (hb : 0 < b i) :
    b i * (1 - xi * realizedMixedMarginal xi c fixed I b i) =
      realizedMixedMultiplier xi c fixed I b := by
  unfold realizedMixedMarginal
  field_simp [ne_of_gt hxi, ne_of_gt hb] ; ring

theorem privateTypicalMixture_mixed_receipt (mu : FiniteLaw Ω)
    {xi : ℝ} (hxi : 0 < xi) (c : ℕ)
    (fixed : Ω → Finset ι) (I : Finset ι) (b : ι → ℝ)
    (hdis : ∀ omega, Disjoint (fixed omega) I)
    (hfixed : ∀ omega, (fixed omega).card ≤ c)
    (hW : 0 < mixedReciprocalSum I b)
    (hb : ∀ i ∈ I, 0 < b i)
    (hlo : ∀ omega i, i ∈ I →
      (1 - xi) * b i ≤ realizedMixedMultiplier xi c (fixed omega) I b)
    (hhi : ∀ omega i, i ∈ I →
      realizedMixedMultiplier xi c (fixed omega) I b ≤ b i)
    (i : ι) (hi : i ∈ I) :
    (privateTypicalMixture mu xi c fixed I b).expect (receiptAgainstSelection xi (b i) i) =
      mu.expect (fun omega => realizedMixedMultiplier xi c (fixed omega) I b) := by
  rw [privateTypicalMixture, FiniteLaw.expect_finiteMix]
  apply mu.expect_congr
  intro omega
  have himpl := typicalLottery_implements hxi c (fixed omega) I b
    (hdis omega) (hfixed omega) hW hb (hlo omega) (hhi omega)
  have hn : i ∉ fixed omega := fun hf => (Finset.disjoint_left.mp (hdis omega)) hf hi
  unfold receiptAgainstSelection
  rw [FiniteLaw.expect_const_mul, FiniteLaw.expect_sub, FiniteLaw.expect_const,
    FiniteLaw.expect_const_mul, ← FiniteLaw.prob_eq_expect, himpl.2 i]
  simp only [typicalMarginal, if_neg hn, if_pos hi]
  exact realizedMixedMarginal_receipt hxi c (fixed omega) I b i (hb i hi)

omit [Fintype ι] [DecidableEq ι] in
theorem expected_realizedMixedMultiplier (mu : FiniteLaw Ω) (xi : ℝ) (c : ℕ)
    (fixed : Ω → Finset ι) (I : Finset ι) (b : ι → ℝ)
    (hfixed : ∀ omega, (fixed omega).card ≤ c) :
    mu.expect (fun omega => realizedMixedMultiplier xi c (fixed omega) I b) =
      ((I.card : ℝ) - xi * ((c : ℝ) - mu.expect (fun omega => ((fixed omega).card : ℝ)))) /
        mixedReciprocalSum I b := by
  have hcast (omega : Ω) : (realizedResidual c (fixed omega) : ℝ) =
      (c : ℝ) - (fixed omega).card := by
    have hfc := hfixed omega
    have hn : (fixed omega).card + realizedResidual c (fixed omega) = c := by
      unfold realizedResidual
      omega
    have hr : ((fixed omega).card : ℝ) + (realizedResidual c (fixed omega) : ℝ) = c :=
      by exact_mod_cast hn
    linarith
  calc
    _ = mu.expect (fun omega =>
        ((I.card : ℝ) - xi * c) * (mixedReciprocalSum I b)⁻¹ +
          (xi * (mixedReciprocalSum I b)⁻¹) * ((fixed omega).card : ℝ)) := by
      apply mu.expect_congr
      intro omega
      unfold realizedMixedMultiplier
      rw [hcast omega]
      ring
    _ = _ := by
      rw [FiniteLaw.expect_add, FiniteLaw.expect_const, FiniteLaw.expect_const_mul]
      ring

theorem product_fixed_left_test {A B : Type*} [Fintype A] [Fintype B]
    (left : FiniteLaw A) (right : FiniteLaw B) (a : A) (f : B → ℝ) :
    (left.prod right).expect (fun z => if z.1 = a then f z.2 else 0) =
      left.mass a * right.expect f := by
  classical
  rw [FiniteLaw.expect_prod]
  calc
    left.expect (fun x => right.expect (fun y => if x = a then f y else 0)) =
        left.expect (fun x => if x = a then right.expect f else 0) := by
      apply left.expect_congr
      intro x
      by_cases hx : x = a <;> simp only [hx, if_true, if_false, FiniteLaw.expect_zero]
    _ = _ := by simp [FiniteLaw.expect]

theorem product_conditional_other_test {A B : Type*} [Fintype A] [Fintype B]
    (left : FiniteLaw A) (right : FiniteLaw B) (a : A) (ha : 0 < left.mass a)
    (f : B → ℝ) :
    ((left.prod right).expect (fun z => if z.1 = a then f z.2 else 0)) / left.mass a =
      right.expect f := by
  rw [product_fixed_left_test]
  field_simp [ne_of_gt ha]

end FCAppendix.Affine.Tail04
