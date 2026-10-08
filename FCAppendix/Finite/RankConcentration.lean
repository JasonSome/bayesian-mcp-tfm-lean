import FCAppendix.Finite.ReceiptBoundsAE
import FCAppendix.Probability.BinomialShortfall

namespace FCAppendix.Bayes

open MeasureTheory Game
open scoped BigOperators

theorem binomBelow_eq_prob (N c : ℕ) (hc : c ≤ N + 1) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    binomBelow N p c = (IndependentCounts.binomial N p hp0 hp1).prob (fun r => r.val < c) := by
  classical
  unfold binomBelow FiniteLaw.prob FiniteLaw.expect
  simp_rw [PiBinomial.binomial_mass, mul_ite, mul_one, mul_zero]
  rw [Fin.sum_univ_eq_sum_range (fun r => if r < c then PiBinomial.pmf N p r else 0)]
  calc
    _ = ∑ r ∈ Finset.range c, (if r < c then PiBinomial.pmf N p r else 0) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [if_pos (Finset.mem_range.mp hr)]
    _ = _ := Finset.sum_subset (Finset.range_mono hc) (by
      intro r _ hr
      rw [if_neg (by simpa using hr)])

theorem binomBelow_lower_chebyshev (N c : ℕ) (hc : c ≤ N + 1) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hgap : N * p < (c : ℝ)) :
    1 - (N : ℝ) * p * (1 - p) / ((c : ℝ) - N * p) ^ 2 ≤ binomBelow N p c := by
  rw [binomBelow_eq_prob N c hc p hp0 hp1]
  have hcomp := (IndependentCounts.binomial N p hp0 hp1).prob_compl (fun r => c ≤ r.val)
  simp only [not_le] at hcomp
  rw [hcomp]
  linarith [IndependentCounts.binomial_tail_chebyshev N c p hp0 hp1 hgap]

theorem binomBelow_lower_of_gap (N c : ℕ) (hc : c ≤ N + 1) (p δ : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hδ : 0 < δ) (hgap : δ ≤ (c : ℝ) - N * p) :
    1 - N / (4 * δ ^ 2) ≤ binomBelow N p c := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hp : p * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg (p - 1 / 2)]
  have hg : 0 < (c : ℝ) - N * p := hδ.trans_le hgap
  have hvar : (N : ℝ) * p * (1 - p) ≤ N / 4 := by
    nlinarith [mul_le_mul_of_nonneg_left hp hN]
  have hsq : δ ^ 2 ≤ ((c : ℝ) - N * p) ^ 2 := by nlinarith
  have hbound : (N : ℝ) * p * (1 - p) / ((c : ℝ) - N * p) ^ 2 ≤ N / (4 * δ ^ 2) := by
    calc
      _ ≤ (N / 4) / ((c : ℝ) - N * p) ^ 2 :=
        div_le_div_of_nonneg_right hvar (sq_nonneg _)
      _ ≤ (N / 4) / δ ^ 2 := div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hδ) hsq
      _ = _ := by ring
  have h := binomBelow_lower_chebyshev N c hc p hp0 hp1 (by linarith)
  linarith

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem meanAcceptProb_lower_of_gap (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (hc : c ≤ m) (hΓ : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hatom : PositiveVisibleAtomless Γ) (i : Fin m) (j : Fin n)
    (a : ℝ) (ha : 0 < a)
    (hA : ∀ r : ℕ, 0 < r → r ≤ n → a * (r : ℝ) ≤ Γ.A.charge r)
    (b δ : ℝ) (hb : 0 < b) (hδ : 0 < δ)
    (hgap : δ ≤ (c : ℝ) - (m - 1 : ℕ) * alphaGt Γ j (a * b)) :
    1 - (m - 1 : ℕ) / (4 * δ ^ 2) ≤ meanAcceptProb Γ i b := by
  have hp0 : 0 ≤ alphaGt Γ j (a * b) := measureReal_nonneg
  have hp1 : alphaGt Γ j (a * b) ≤ 1 := measureReal_le_one
  exact (binomBelow_lower_of_gap (m - 1) c (by omega) (alphaGt Γ j (a * b)) δ hp0 hp1 hδ hgap).trans
    (meanAcceptProb_bounds_ae Γ hΓ hatom j i a ha hA b hb).1

end FCAppendix.Bayes
