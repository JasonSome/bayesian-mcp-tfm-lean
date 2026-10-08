import FCAppendix.Ample.SlackAccounting
import FCAppendix.Ample.FreeBaseIncentives
import FCAppendix.Ample.SmallTilt
import FCAppendix.Probability.ContactHoeffding

noncomputable section
namespace FCAppendix.Ample
open Finset Real
open scoped BigOperators

def subsetFactor (n : ℕ) : ℝ := 1 + ∑ j ∈ range (n + 1), (n.choose j : ℝ)

lemma subsetFactor_pos (n : ℕ) : 0 < subsetFactor n := by
  unfold subsetFactor
  have hh : 0 ≤ ∑ j ∈ range (n + 1), (n.choose j : ℝ) :=
    sum_nonneg (fun j _ => Nat.cast_nonneg _)
  linarith

lemma choose_le_subsetFactor {n k : ℕ} (hk : k ≤ n) :
    (n.choose k : ℝ) ≤ subsetFactor n := by
  have hh := single_le_sum (fun j (_ : j ∈ range (n + 1)) =>
    (Nat.cast_nonneg (n.choose j) : (0 : ℝ) ≤ n.choose j))
      (mem_range.mpr (Nat.lt_succ_of_le hk))
  unfold subsetFactor
  linarith

theorem congestProb_ge_common_subset {n N c k : ℕ} {lawWeights : ℕ → ℝ}
    (hlam : ValidLaw n lawWeights) (hk1 : 1 ≤ k) (hk : k ≤ n) (hc : c ≤ N) :
    (lawWeights k / (n.choose k : ℝ)) ^ N ≤ congestProb n N c k lawWeights := by
  classical
  let T := selected n k
  have hT : T ≠ ∅ := by
    intro hz
    have hh := card_selected hk
    change T.card = k at hh
    rw [hz, card_empty] at hh
    omega
  have hE : ∀ j ∈ T, c ≤ contacts (fun _ : Fin N => T) j := by
    intro j hj
    simpa [contacts, hj] using hc
  have hW : contactWeight n lawWeights T = lawWeights k / (n.choose k : ℝ) := by
    rw [contactWeight_of_ne lawWeights hT]
    simp only [T, card_selected hk]
  unfold congestProb congestProbAt
  have hh := single_le_sum
    (f := fun x : Fin N → Finset (Fin n) =>
      (∏ l, contactWeight n lawWeights (x l)) *
        (if ∀ j ∈ T, c ≤ contacts x j then (1 : ℝ) else 0))
    (fun x (_ : x ∈ (univ : Finset (Fin N → Finset (Fin n)))) =>
      mul_nonneg (prod_nonneg (fun l _ => contactWeight_nonneg hlam (x l)))
        (by split_ifs <;> norm_num))
    (mem_univ (fun _ : Fin N => T))
  change (∏ _l : Fin N, contactWeight n lawWeights T) *
    (if ∀ j ∈ T, c ≤ contacts (fun _ : Fin N => T) j then 1 else 0) ≤ _ at hh
  simpa only [if_pos hE, mul_one, prod_const, card_univ,
    Fintype.card_fin, hW] using hh

end FCAppendix.Ample

namespace FCAppendix.SimultaneousCongestion
open Finset Real CommonList Proposer
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem singleton_congestion_small_tail (μ : FiniteLaw (Finset ι)) (s : ι)
    (N c : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) (hp : marginal μ s ≤ exp (-θ)) :
    congestionProb μ {s} N c ≤ exp (-θ * c + N) := by
  classical
  have hpoint (T : Finset ι) :
      exp (θ * (selected {s} T : ℝ)) ≤ 1 + exp θ * (if s ∈ T then (1 : ℝ) else 0) := by
    have hy : (selected {s} T : ℝ) = if s ∈ T then 1 else 0 := by
      unfold selected
      by_cases hs : s ∈ T <;> simp [hs]
    rw [hy]
    by_cases h : s ∈ T
    · simp only [if_pos h, mul_one]
      linarith
    · simp only [if_neg h, mul_zero, exp_zero, add_zero, le_refl]
  have hmgf : mgf μ {s} θ ≤ exp 1 := by
    have hh := μ.expect_mono hpoint
    rw [μ.expect_add, μ.expect_const, μ.expect_const_mul,
      ← marginal_eq_expect] at hh
    have hm := mul_le_mul_of_nonneg_left hp (exp_pos θ).le
    rw [← exp_add] at hm
    simp only [add_neg_cancel, exp_zero] at hm
    have he : (2 : ℝ) ≤ exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    exact hh.trans (by linarith)
  have hpow := pow_le_pow_left₀ (mgf_pos μ {s} θ).le hmgf N
  have hh := (congestionProb_le μ {s} N c hθ).trans
    (mul_le_mul_of_nonneg_left hpow (exp_pos _).le)
  have he : exp (-(θ * (({s} : Finset ι).card * c))) * exp 1 ^ N =
      exp (-θ * c + N) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    simp only [Finset.card_singleton, Nat.cast_one, one_mul, mul_one]
    congr 1
    ring
  exact hh.trans_eq he

end FCAppendix.SimultaneousCongestion

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Finset Real
open scoped BigOperators
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma positiveRouteTail_multi_eq_visible (Γ : FiniteGame m n c Seed)
    (b : ℝ) (hb : 0 ≤ b) :
    positiveRouteTail Γ (fun k => 2 ≤ k) b =
      (visibleLaw Γ b).prob (fun T => 2 ≤ T.card) := by
  rw [← visibleLaw_prob_positiveClass Γ b hb]
  simp only [FiniteLaw.prob_eq_expect]
  apply FiniteLaw.expect_congr
  intro T
  have he : (0 < T.card ∧ 2 ≤ T.card) ↔ 2 ≤ T.card := by omega
  simp only [he]

lemma visibleLaw_expect_eq_n_mean (Γ : FiniteGame m n c Seed) (hn : 0 < n) (b : ℝ) :
    (visibleLaw Γ b).expect (fun T => (T.card : ℝ)) =
      (n : ℝ) * Ample.contactMarginal n (visibleClassMass Γ b) := by
  rw [visibleLaw_eq_contactLaw, Ample.contactLaw_expect_card, Ample.contactMarginal]
  field_simp [Nat.cast_ne_zero.mpr hn.ne']

lemma allPositiveCongestion_eq_source (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (i : Fin m) :
    allPositiveCongestion Γ i = Ample.congestProb n (m - 1) c n (visibleClassMass Γ 0) := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  simpa only [allPositiveCongestion, Ample.congestProbAt_eq_congestProb,
    Finset.card_univ, Fintype.card_fin, Nat.succ_sub_one, Finset.mem_univ, forall_true_left] using
      joint_rank_congestion_eq Γ i 0 (Finset.univ : Finset (Fin n))

lemma ppi_failure_eq_source (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j) (i : Fin m)
    (a : JointAction n) (hb : 0 < a.bid) :
    1 - ((problem Γ i).outcome a).success =
      Ample.congestProb n (m - 1) c a.routeCount (visibleClassMass Γ a.bid) := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  simpa using ppi_failure_eq_congestProb Γ hA hatom hj i a hb

lemma ppi_AM1_failure (Γ : FiniteGame m n c Seed) (hm : 0 < m) (hn : 0 < n)
    (hA : Γ.A = Schedule.ppi n) (hfree : FreeDuplicateBase Γ)
    (hatom : PositiveVisibleAtomless Γ) (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (i : Fin m) {w : ℝ} (hw : 0 < w) (a : JointAction n)
    (ha : (problem Γ i).BestResponse (w + Γ.g) a) :
    1 - ((problem Γ i).outcome a).success ≤ allPositiveCongestion Γ i := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  exact (ppi_free_AM1 Γ hA hfree hatom hj hn i hw a ha).2.1

theorem ppi_failure_ge_same_count (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (i : Fin m) (a : JointAction n) (hb : 0 < a.bid) (hk : 1 ≤ a.routeCount)
    (hc : c ≤ m - 1) {s : ℝ} (hs : 0 ≤ s)
    (htail : s ≤ positiveRouteTail Γ (fun k => k = a.routeCount) a.bid /
      (n.choose a.routeCount : ℝ)) :
    s ^ (m - 1) ≤ 1 - ((problem Γ i).outcome a).success := by
  rw [positiveRouteTail_class_eq Γ a.bid hb.le hk] at htail
  rw [ppi_failure_eq_source Γ hm hA hatom hj i a hb]
  exact (pow_le_pow_left₀ hs htail _).trans
    (Ample.congestProb_ge_common_subset (visibleClassMass_valid Γ a.bid)
      hk a.routeCount_le hc)

theorem ppi_rejection_le_small_tail (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (hn : 0 < n) (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (i : Fin m) (b : ℝ) (hb : 0 < b) {θ : ℝ} (hθ : 0 ≤ θ)
    (htail : positiveRouteTail Γ (fun _ => True) b ≤ exp (-θ)) :
    1 - meanAcceptProb Γ i b ≤ exp (-θ * c + (m - 1 : ℕ)) := by
  let s : Fin n := ⟨0, hn⟩
  let a : JointAction n := ⟨b, hb.le, 1, hn⟩
  have hp : Proposer.marginal (visibleLaw Γ b) s ≤ exp (-θ) := by
    rw [visibleLaw_eq_contactLaw, Ample.contactLaw_marginal]
    exact (arrivalMean_le_tail Γ hn b hb.le).trans htail
  have hh := SimultaneousCongestion.singleton_congestion_small_tail
    (visibleLaw Γ b) s (m - 1) c hθ hp
  rw [visibleLaw_eq_contactLaw, Ample.contactLaw_congestionProb,
    Ample.congestProbAt_eq_congestProb, Finset.card_singleton] at hh
  have he := ppi_failure_eq_source Γ hm hA hatom hj i a hb
  rw [singleton_success Γ hn i a rfl] at he
  exact he.trans_le hh

theorem ppi_rejection_le_exp_of_mean_gap (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (hn : 0 < n) (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (i : Fin m) (b : ℝ) (hb : 0 < b) {δ : ℝ} (hδ : 0 ≤ δ)
    (hc : ((m - 1 : ℕ) : ℝ) *
      (Ample.contactMarginal n (visibleClassMass Γ b) + δ) ≤ c) :
    1 - meanAcceptProb Γ i b ≤ exp (-2 * (m - 1 : ℕ) * δ ^ 2) := by
  let s : Fin n := ⟨0, hn⟩
  let a : JointAction n := ⟨b, hb.le, 1, hn⟩
  have hh := SimultaneousCongestion.congestionProb_le_exp_of_coordinate
    (visibleLaw Γ b) ({s} : Finset (Fin n)) (mem_singleton_self s) (m - 1) c hδ
    (by simpa only [visibleLaw_eq_contactLaw, Ample.contactLaw_marginal] using hc)
  rw [visibleLaw_eq_contactLaw, Ample.contactLaw_congestionProb,
    Ample.congestProbAt_eq_congestProb, Finset.card_singleton] at hh
  have he := ppi_failure_eq_source Γ hm hA hatom hj i a hb
  rw [singleton_success Γ hn i a rfl] at he
  exact he.trans_le hh

theorem ppi_acceptance_le_exp_of_mean_excess (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (hn : 0 < n) (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (i : Fin m) (b : ℝ) (hb : 0 < b) {δ : ℝ} (hδ : 0 ≤ δ)
    (hc : (c : ℝ) ≤ ((m - 1 : ℕ) : ℝ) *
      (Ample.contactMarginal n (visibleClassMass Γ b) - δ)) :
    meanAcceptProb Γ i b ≤ exp (-2 * (m - 1 : ℕ) * δ ^ 2) := by
  let s : Fin n := ⟨0, hn⟩
  let a : JointAction n := ⟨b, hb.le, 1, hn⟩
  have hh := SimultaneousCongestion.one_sub_congestionProb_le_exp
    (visibleLaw Γ b) ({s} : Finset (Fin n)) (m - 1) c hδ
    (fun t ht => by
      simpa only [visibleLaw_eq_contactLaw, Ample.contactLaw_marginal] using hc)
  rw [visibleLaw_eq_contactLaw, Ample.contactLaw_congestionProb,
    Ample.congestProbAt_eq_congestProb, Finset.card_singleton, Nat.cast_one, one_mul] at hh
  have he := ppi_failure_eq_source Γ hm hA hatom hj i a hb
  rw [singleton_success Γ hn i a rfl] at he
  rw [← he] at hh
  linarith

theorem ppi_failure_ge_small_tilt_of_tails (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hn : 0 < n) (hA : Γ.A = Schedule.ppi n)
    (hatom : PositiveVisibleAtomless Γ) (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (i : Fin m) (a : JointAction n) (hb : 0 < a.bid)
    {a₁ a₂ ρ δ : ℝ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hδ : 0 < δ)
    (h₁ : a₁ ≤ positiveRouteTail Γ (fun k => k = 1) a.bid)
    (h₂ : a₂ ≤ positiveRouteTail Γ (fun k => 2 ≤ k) a.bid)
    (hmean : ρ - 2 * δ ≤ Ample.contactMarginal n (visibleClassMass Γ a.bid))
    (hsmall : 4 * n * δ ≤ exp (-(n : ℝ)) * min a₁ a₂ / 4)
    (hc : (c : ℝ) ≤ ((m - 1 : ℕ) : ℝ) * (ρ + δ))
    (hM : (n : ℝ) ≤ 2 * (m - 1 : ℕ) * δ ^ 2) :
    exp (-((4 * n * δ / (exp (-(n : ℝ)) * min a₁ a₂ / 4)) * (m - 1 : ℕ) * n)) / 2 ≤
      1 - ((problem Γ i).outcome a).success := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  simp only [Nat.succ_sub_one] at hc hM ⊢
  apply ppi_failure_ge_small_tilt Γ hn hA hatom hj i a hb ha₁ ha₂ hδ
  · simpa only [positiveRouteTail_class_eq Γ a.bid hb.le (by omega : 1 ≤ 1)] using h₁
  · simpa only [positiveRouteTail_multi_eq_visible Γ a.bid hb.le] using h₂
  · rw [visibleLaw_expect_eq_n_mean Γ hn a.bid]
    exact mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg n)
  · exact hsmall
  · exact hc
  · exact hM

end FCAppendix.Bayes
