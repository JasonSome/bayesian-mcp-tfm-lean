import FCAppendix.Affine.WeightedSampling

noncomputable section
namespace FCAppendix.Affine.UniformFinite.Literal
open Set
open scoped BigOperators
open WeightedSampling

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem weighted_target_hit (w : Weights ι) (n : ℕ) (S : Finset ι) (i : ι)
    (hi : i ∉ S) (hW : (S.card : ℝ)+n < totalWeight w) :
    (pathLaw w n S).prob (fun p => i ∈ finalSet n S p) ≤
      (n : ℝ)/(totalWeight w-(S.card : ℝ)-n) := by
  classical
  induction n generalizing S with
  | zero => simp [FiniteLaw.prob_eq_expect, pathLaw, finalSet, hi]
  | succ n ih =>
      let D := totalWeight w-(S.card : ℝ)-(n+1 : ℕ)
      have hD : 0 < D := by
        dsimp [D]
        push_cast at hW ⊢
        linarith
      have hden : 0 < remainingWeight w S := by
        have hL := denominator_lower w S
        push_cast at hW
        nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
      have hnD : 0 ≤ (n : ℝ)/D := div_nonneg (Nat.cast_nonneg n) hD.le
      rw [FiniteLaw.prob_eq_expect, expect_path_succ]
      have hstep :
          (oneDraw w S).expect (fun a =>
            (pathLaw w n (insert a S)).expect (fun p =>
              if i ∈ finalSet (n+1) S (a,p) then (1 : ℝ) else 0)) ≤
          (oneDraw w S).expect (fun a => (if a=i then (1 : ℝ) else 0)+(n : ℝ)/D) := by
        apply WeightedSampling.expect_le_of_support
        intro a ha
        have haS := (oneDraw_support w S hden ha).1
        have hcard : (insert a S).card = S.card+1 := Finset.card_insert_of_notMem haS
        by_cases hai : a=i
        · have hb : (pathLaw w n (insert a S)).expect (fun p =>
              if i ∈ finalSet (n+1) S (a,p) then (1 : ℝ) else 0) ≤ 1 :=
            WeightedSampling.expect_le_const _ _ _ (fun p _ => by split_ifs <;> norm_num)
          simp only [if_pos hai]
          linarith
        · have hi' : i ∉ insert a S := by simp [hi, Ne.symm hai]
          have hW' : ((insert a S).card : ℝ)+n < totalWeight w := by
            rw [hcard]
            push_cast at hW ⊢
            linarith
          have hh := ih (insert a S) hi' hW'
          rw [FiniteLaw.prob_eq_expect] at hh
          simp only [if_neg hai, zero_add]
          change (pathLaw w n (insert a S)).expect
            (fun p => if i ∈ finalSet n (insert a S) p then (1 : ℝ) else 0) ≤ _
          convert! hh using 1
          dsimp [D]
          rw [hcard]
          push_cast
          ring
      have hdraw : (oneDraw w S).mass i ≤ 1/D := by
        rw [oneDraw_focal w S hden hi]
        calc
          w.1 i/remainingWeight w S ≤ 1/remainingWeight w S :=
            div_le_div_of_nonneg_right (w.2 i).2 hden.le
          _ ≤ 1/D := div_le_div_of_nonneg_left zero_le_one hD (by
            dsimp [D]
            push_cast
            nlinarith [denominator_lower w S, show (0 : ℝ) ≤ n from Nat.cast_nonneg n])
      have he : (oneDraw w S).expect
          (fun a => (if a=i then (1 : ℝ) else 0)+(n : ℝ)/D) =
          (oneDraw w S).mass i+(n : ℝ)/D := by
        rw [FiniteLaw.expect_add, FiniteLaw.expect_singleton, FiniteLaw.expect_const]
      rw [he] at hstep
      calc
        _ ≤ (oneDraw w S).mass i+(n : ℝ)/D := hstep
        _ ≤ 1/D+(n : ℝ)/D := by linarith
        _ = (n+1 : ℕ)/(totalWeight w-(S.card : ℝ)-(n+1 : ℕ)) := by
          dsimp [D]
          push_cast
          ring

theorem weighted_target_hit_empty (w : Weights ι) (n : ℕ) (i : ι)
    (hW : (n : ℝ) < totalWeight w) :
    (pathLaw w n ∅).prob (fun p => i ∈ finalSet n ∅ p) ≤
      (n : ℝ)/(totalWeight w-n) := by
  simpa using weighted_target_hit w n ∅ i (by simp) (by simpa using hW)

end FCAppendix.Affine.UniformFinite.Literal
