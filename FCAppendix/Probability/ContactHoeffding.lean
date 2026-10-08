import FCAppendix.Probability.FiniteHoeffding

namespace FCAppendix.SimultaneousCongestion

open Real Set Finset CommonList Proposer
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem marginal_congestion_le_exp (μ : FiniteLaw (Finset ι)) (s : ι)
    (N c : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hc : (N : ℝ) * (marginal μ s + δ) ≤ c) :
    (iid μ N).prob (fun T => c ≤ includers s T) ≤ exp (-2 * N * δ ^ 2) := by
  classical
  let X : Finset ι → ℝ := fun S => if s ∈ S then 1 else 0
  have hX : ∀ S, X S ∈ Icc (0 : ℝ) 1 := by intro S; dsimp [X]; split <;> norm_num
  have he : μ.expect X = marginal μ s := (marginal_eq_expect μ s).symm
  have hsum (T : Fin N → Finset ι) : ∑ i, X (T i) = (includers s T : ℝ) := by
    simp [X, includers]
  have hsub : ∀ T : Fin N → Finset ι, c ≤ includers s T →
      (N : ℝ) * (μ.expect X + δ) ≤ ∑ i, X (T i) := by
    intro T hT
    rw [he, hsum]
    exact hc.trans (by exact_mod_cast hT)
  exact ((iid μ N).prob_mono hsub).trans (FiniteCramer.iid_upper_hoeffding μ X hX N hδ)

theorem marginal_underload_le_exp (μ : FiniteLaw (Finset ι)) (s : ι)
    (N c : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hc : (c : ℝ) ≤ (N : ℝ) * (marginal μ s - δ)) :
    (iid μ N).prob (fun T => includers s T < c) ≤ exp (-2 * N * δ ^ 2) := by
  classical
  let X : Finset ι → ℝ := fun S => if s ∈ S then 1 else 0
  have hX : ∀ S, X S ∈ Icc (0 : ℝ) 1 := by intro S; dsimp [X]; split <;> norm_num
  have he : μ.expect X = marginal μ s := (marginal_eq_expect μ s).symm
  have hsum (T : Fin N → Finset ι) : ∑ i, X (T i) = (includers s T : ℝ) := by
    simp [X, includers]
  have hsub : ∀ T : Fin N → Finset ι, includers s T < c →
      (∑ i, X (T i)) ≤ (N : ℝ) * (μ.expect X - δ) := by
    intro T hT
    rw [he, hsum]
    exact (show (includers s T : ℝ) ≤ c by exact_mod_cast hT.le).trans hc
  exact ((iid μ N).prob_mono hsub).trans (FiniteCramer.iid_lower_hoeffding μ X hX N hδ)

theorem congestionProb_le_exp_of_coordinate (μ : FiniteLaw (Finset ι))
    (K : Finset ι) {s : ι} (hs : s ∈ K) (N c : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hc : (N : ℝ) * (marginal μ s + δ) ≤ c) :
    congestionProb μ K N c ≤ exp (-2 * N * δ ^ 2) :=
  ((iid μ N).prob_mono (fun _ hT => hT s hs)).trans
    (marginal_congestion_le_exp μ s N c hδ hc)

theorem one_sub_congestionProb_le_exp (μ : FiniteLaw (Finset ι))
    (K : Finset ι) (N c : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hc : ∀ s ∈ K, (c : ℝ) ≤ N * (marginal μ s - δ)) :
    1 - congestionProb μ K N c ≤ K.card * exp (-2 * N * δ ^ 2) := by
  classical
  have he : (fun T : Fin N → Finset ι => ¬ Congested K c T) =
      fun T => ∃ s ∈ K, includers s T < c := by
    funext T
    simp [Congested]
  change 1 - (iid μ N).prob (Congested K c) ≤ _
  rw [← FiniteLaw.prob_compl, he]
  apply (prob_exists_le (iid μ N) K (fun s T => includers s T < c)).trans
  calc
    _ ≤ ∑ _s ∈ K, exp (-2 * N * δ ^ 2) := Finset.sum_le_sum
      (fun s hs => marginal_underload_le_exp μ s N c hδ (hc s hs))
    _ = _ := by simp

end FCAppendix.SimultaneousCongestion
