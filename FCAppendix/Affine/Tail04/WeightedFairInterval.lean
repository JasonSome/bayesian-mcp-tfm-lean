import FCAppendix.Affine.Tail04.BidDependentFlags
import FCAppendix.Probability.FairBinomialBound
import Mathlib.Combinatorics.SetFamily.LYM

noncomputable section
namespace FCAppendix.Affine.Tail04.WeightedFlagBound
open Set Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def bit (b : Bool) : ℝ := if b then 1 else 0

def weightedSum (w : ι → ℝ) (flags : ι → Bool) : ℝ := ∑ i, w i * bit (flags i)

def setWeight (w : ι → ℝ) (S : Finset ι) : ℝ := ∑ i ∈ S, w i

def shortFamily (w : ι → ℝ) (a l : ℝ) : Finset (Finset ι) :=
  Finset.univ.filter (fun S => l ≤ setWeight w S ∧ setWeight w S < l + a)

omit [Fintype ι] in
theorem setWeight_gap (w : ι → ℝ) {a : ℝ} (ha : 0 < a)
    (hw : ∀ i, a ≤ w i) (S T : Finset ι) (hST : S ⊆ T) (hne : S ≠ T) :
    setWeight w S + a ≤ setWeight w T := by
  have hnot : ¬ T ⊆ S := fun h => hne (Finset.Subset.antisymm hST h)
  obtain ⟨i, hi⟩ := Finset.sdiff_nonempty.mpr hnot
  have hsum : a ≤ ∑ j ∈ T \ S, w j :=
    (hw i).trans (Finset.single_le_sum (fun j _ => ha.le.trans (hw j)) hi)
  have heq := Finset.sum_sdiff hST (f := w)
  dsimp [setWeight]
  linarith

theorem shortFamily_antichain (w : ι → ℝ) {a : ℝ} (l : ℝ)
    (ha : 0 < a) (hw : ∀ i, a ≤ w i) :
    IsAntichain (· ⊆ ·) (shortFamily w a l : Set (Finset ι)) := by
  intro S hS T hT hne hST
  have hS' := (Finset.mem_filter.mp hS).2
  have hT' := (Finset.mem_filter.mp hT).2
  have hgap := setWeight_gap w ha hw S T hST hne
  linarith

theorem shortFamily_card (w : ι → ℝ) {a : ℝ} (l : ℝ)
    (ha : 0 < a) (hw : ∀ i, a ≤ w i) :
    (shortFamily w a l).card ≤
      (Fintype.card ι).choose (Fintype.card ι / 2) :=
  (shortFamily_antichain w l ha hw).sperner

def fairFlags (ι : Type*) [Fintype ι] [DecidableEq ι] : FiniteLaw (ι → Bool) :=
  BidDependentFlags.flags (fun _ : ι => (1:ℝ)/2) (fun _ => by norm_num) (fun _ => by norm_num)

theorem fairFlags_mass (flags : ι → Bool) :
    (fairFlags ι).mass flags = 1 / (2:ℝ) ^ Fintype.card ι := by
  change (∏ i, if flags i then (1:ℝ)/2 else 1-1/2) = _
  norm_num only [show (1:ℝ)-1/2=1/2 by norm_num]
  simp only [ite_self, Finset.prod_const, Finset.card_univ, one_div_pow]

def boolSetEquiv : (ι → Bool) ≃ Finset ι where
  toFun flags := Finset.univ.filter (fun i => flags i = true)
  invFun S i := decide (i ∈ S)
  left_inv flags := by
    funext i
    cases h : flags i <;> simp [h]
  right_inv S := by ext i; simp

theorem weightedSum_eq_setWeight (w : ι → ℝ) (flags : ι → Bool) :
    weightedSum w flags = setWeight w (boolSetEquiv flags) := by
  change (∑ i, w i * bit (flags i)) =
    ∑ i ∈ Finset.univ.filter (fun i => flags i = true), w i
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases h : flags i <;> simp [bit]

theorem fair_short_probability_eq (w : ι → ℝ) (a l : ℝ) :
    (fairFlags ι).prob (fun flags => weightedSum w flags ∈ Ico l (l+a)) =
      ((shortFamily w a l).card : ℝ) / (2:ℝ)^Fintype.card ι := by
  classical
  rw [FiniteLaw.prob_eq_expect]
  unfold FiniteLaw.expect
  simp_rw [fairFlags_mass, weightedSum_eq_setWeight]
  rw [← Finset.mul_sum]
  have hsum : (∑ flags : ι → Bool,
      if setWeight w (boolSetEquiv flags) ∈ Ico l (l+a) then (1:ℝ) else 0) =
      ((shortFamily w a l).card : ℝ) := by
    rw [FiniteLaw.sum_equiv boolSetEquiv
      (fun S => if setWeight w S ∈ Ico l (l+a) then (1:ℝ) else 0)]
    simp only [shortFamily,Set.mem_Ico,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,
      Nat.cast_one,Nat.cast_zero]
  rw [hsum]
  ring

theorem fair_positive_short (w : ι → ℝ) {a : ℝ} (l : ℝ)
    (ha : 0 < a) (hw : ∀ i, a ≤ w i) :
    (fairFlags ι).prob (fun flags => weightedSum w flags ∈ Ico l (l+a)) ≤
      Real.sqrt (2 / ((Fintype.card ι : ℝ)+1)) := by
  rw [fair_short_probability_eq]
  calc
    _ ≤ (((Fintype.card ι).choose (Fintype.card ι / 2) : ℕ) : ℝ) /
        (2:ℝ)^Fintype.card ι :=
      div_le_div_of_nonneg_right (by exact_mod_cast shortFamily_card w l ha hw)
        (by positivity)
    _ = PiBinomial.pmf (Fintype.card ι) (1/2) (Fintype.card ι / 2) :=
      (PiBinomial.pmf_half_eq_choose_div _ _).symm
    _ ≤ _ := PiBinomial.pmf_half_le_sqrt _ _

def signedFlip (w : ι → ℝ) (flags : ι → Bool) : ι → Bool :=
  fun i => if 0 ≤ w i then flags i else !(flags i)

def negativeOffset (w : ι → ℝ) : ℝ := ∑ i, if 0 ≤ w i then 0 else w i

theorem signedFlip_fair_law (w : ι → ℝ) :
    (fairFlags ι).map (signedFlip w) = fairFlags ι := by
  unfold fairFlags BidDependentFlags.flags
  have hm := BidDependentFlags.map_product
    (fun _ : ι => IndependentCounts.bernoulli (1/2) (by norm_num) (by norm_num))
    (fun i (b : Bool) => if 0≤w i then b else !b)
  refine hm.trans ?_

  congr 1
  funext i
  apply FiniteLaw.ext_expect
  intro f
  rw [FiniteLaw.expect_map]
  simp only [IndependentCounts.expect_bernoulli]
  by_cases hw : 0 ≤ w i <;> simp [hw] ; ring

omit [DecidableEq ι] in
theorem signed_weight_decomposition (w : ι → ℝ) (flags : ι → Bool) :
    weightedSum w flags = negativeOffset w + weightedSum (fun i => |w i|) (signedFlip w flags) := by
  unfold weightedSum negativeOffset
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hw : 0 ≤ w i
  · simp [signedFlip, hw, abs_of_nonneg hw]
  · have hw' : w i ≤ 0 := (lt_of_not_ge hw).le
    cases h : flags i <;> simp [signedFlip, hw, abs_of_nonpos hw', bit, h]

theorem fair_signed_short (w : ι → ℝ) {a : ℝ} (l : ℝ)
    (ha : 0 < a) (hw : ∀ i, a ≤ |w i|) :
    (fairFlags ι).prob (fun flags => weightedSum w flags ∈ Ico l (l+a)) ≤
      Real.sqrt (2 / ((Fintype.card ι : ℝ)+1)) := by
  have heq : (fairFlags ι).prob (fun flags => weightedSum w flags ∈ Ico l (l+a)) =
      ((fairFlags ι).map (signedFlip w)).prob
        (fun flags => weightedSum (fun i => |w i|) flags ∈
          Ico (l-negativeOffset w) (l-negativeOffset w+a)) := by
    rw [FiniteLaw.prob_eq_expect, FiniteLaw.prob_eq_expect, FiniteLaw.expect_map]
    apply FiniteLaw.expect_congr
    intro flags
    congr 1
    rw [signed_weight_decomposition]
    simp only [Set.mem_Ico]
    apply propext
    constructor <;> intro h <;> constructor <;> linarith only [h.1,h.2]
  rw [heq, signedFlip_fair_law]
  exact fair_positive_short (fun i => |w i|) (l-negativeOffset w) ha hw

theorem fair_signed_interval (w : ι → ℝ) {a : ℝ} (l : ℝ) (r : ℕ)
    (ha : 0 < a) (hw : ∀ i, a ≤ |w i|) :
    (fairFlags ι).prob (fun flags => weightedSum w flags ∈ Ico l (l+(r:ℝ)*a)) ≤
      (r:ℝ) * Real.sqrt (2 / ((Fintype.card ι : ℝ)+1)) := by
  induction r generalizing l with
  | zero => simp
  | succ r ih =>
    have hsub : (fairFlags ι).prob
        (fun flags => weightedSum w flags ∈ Ico l (l+((r+1:ℕ):ℝ)*a)) ≤
        (fairFlags ι).prob (fun flags =>
          weightedSum w flags ∈ Ico l (l+a) ∨
          weightedSum w flags ∈ Ico (l+a) ((l+a)+(r:ℝ)*a)) := by
      apply FiniteLaw.prob_mono
      intro flags hflags
      by_cases hsmall : weightedSum w flags < l+a
      · exact Or.inl ⟨hflags.1,hsmall⟩
      · right
        refine ⟨le_of_not_gt hsmall, ?_⟩
        push_cast at hflags
        linarith [hflags.2]
    have hunion := (fairFlags ι).prob_union_le
      (fun flags => weightedSum w flags ∈ Ico l (l+a))
      (fun flags => weightedSum w flags ∈ Ico (l+a) ((l+a)+(r:ℝ)*a))
    have hfirst := fair_signed_short w l ha hw
    have hrest := ih (l+a)
    push_cast at hsub ⊢
    calc
      _ ≤ _ := hsub.trans hunion
      _ ≤ Real.sqrt (2 / ((Fintype.card ι : ℝ)+1))+
        (r:ℝ)*Real.sqrt (2 / ((Fintype.card ι : ℝ)+1)) := add_le_add hfirst hrest
      _ = _ := by ring

end FCAppendix.Affine.Tail04.WeightedFlagBound
