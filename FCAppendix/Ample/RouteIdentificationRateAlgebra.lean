import FCAppendix.Ample.CongestionRate

noncomputable section
namespace FCAppendix.Bayes
open Filter Topology Real
open scoped BigOperators
open Ample

def prefixLaw (pi : ℕ → ℝ) (k : ℕ) (j : ℕ) : ℝ :=
  if j ≤ k then pi j else 0

lemma prefixLaw_nonneg {n : ℕ} {pi : ℕ → ℝ}
    (hp : ∀ j ∈ Finset.Icc 1 n, 0 ≤ pi j) (k : ℕ) :
    ∀ j ∈ Finset.Icc 1 n, 0 ≤ prefixLaw pi k j := by
  intro j hj
  simp only [prefixLaw]
  split_ifs
  · exact hp j hj
  · exact le_rfl

lemma prefixLaw_le {n : ℕ} {pi : ℕ → ℝ}
    (hp : ∀ j ∈ Finset.Icc 1 n, 0 ≤ pi j) (k : ℕ) :
    ∀ j ∈ Finset.Icc 1 n, prefixLaw pi k j ≤ pi j := by
  intro j hj
  simp only [prefixLaw]
  split_ifs
  · exact le_rfl
  · exact hp j hj

lemma prefixLaw_valid {n : ℕ} {pi : ℕ → ℝ}
    (hp : ValidLaw n pi) (k : ℕ) : ValidLaw n (prefixLaw pi k) := by
  refine ⟨prefixLaw_nonneg hp.nonneg k, ?_⟩
  exact (Finset.sum_le_sum (prefixLaw_le hp.nonneg k)).trans hp.total_le

lemma prefixLaw_marginal_le {n : ℕ} {pi : ℕ → ℝ}
    (hp : ∀ j ∈ Finset.Icc 1 n, 0 ≤ pi j) (k : ℕ) :
    contactMarginal n (prefixLaw pi k) ≤ contactMarginal n pi := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  apply Finset.sum_le_sum
  intro j hj
  exact mul_le_mul_of_nonneg_right (prefixLaw_le hp k j hj) (Nat.cast_nonneg j)

lemma prefixObjective_eq_rival {n k : ℕ} (hk : k ≤ n)
    (rho : ℝ) (pi : ℕ → ℝ) (theta : ℝ) :
    prefixObjective n rho k pi theta =
      rivalObjective n rho k (prefixLaw pi k) theta := by
  unfold prefixObjective rivalObjective prefixLaw
  rw [prefixMGF_eq_rivalMGF hk]

theorem finite_optimizer_prefix {n k : ℕ} {rho : ℝ} {pi : ℕ → ℝ}
    (hk : k ∈ Finset.Icc 1 n) (hp : ValidLaw n pi) (hrho : rho < 1)
    (hmean : contactMarginal n pi < rho) (hpk : 0 < pi k) :
    ∃ theta > 0, prefixObjective n rho k pi theta = prefixRate n rho k pi := by
  have hk1 := (Finset.mem_Icc.mp hk).1
  have hkn := (Finset.mem_Icc.mp hk).2
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hs : contactMarginal n (prefixLaw pi k) < rho :=
    (prefixLaw_marginal_le hp.nonneg k).trans_lt hmean
  have ht : ∃ j ∈ Finset.Icc 1 n, 0 < prefixLaw pi k j ∧
      (k : ℝ)*rho < (min k j : ℕ) := by
    refine ⟨k, hk, by simpa [prefixLaw] using hpk, ?_⟩
    simpa only [min_self, mul_one] using mul_lt_mul_of_pos_left hrho hkR
  obtain ⟨theta, htheta, _, hopt, _⟩ :=
    rival_optimizer_of_law hk1 hkn (prefixLaw_valid hp k) hs ht
  refine ⟨theta, htheta, ?_⟩
  rw [prefixObjective_eq_rival hkn, prefixRate_eq_rivalRate hkn]
  exact hopt

lemma prefixLaw_eq_of_zero_gap {pi : ℕ → ℝ} {r k : ℕ} (hrk : r ≤ k)
    (hz : ∀ j ∈ Finset.Icc (r+1) k, pi j = 0) :
    prefixLaw pi k = prefixLaw pi r := by
  funext j
  by_cases hjr : j ≤ r
  · simp [prefixLaw, hjr, hjr.trans hrk]
  · by_cases hjk : j ≤ k
    · have hj : j ∈ Finset.Icc (r+1) k := Finset.mem_Icc.mpr ⟨by omega, hjk⟩
      simp [prefixLaw, hjr, hjk, hz j hj]
    · simp [prefixLaw, hjr, hjk]

lemma rivalObjective_added_strict {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k+1 ≤ n)
    {rho theta : ℝ} {p : ℕ → ℝ}
    (hp : ∀ j ∈ Finset.Icc 1 n, 0 ≤ p j) (hp1 : 0 < p 1)
    (htheta : 0 < theta) :
    rivalObjective n rho k p theta <
      rivalObjective n rho (k+1) p (theta*(k : ℝ)/((k : ℝ)+1)) := by
  have hs : 0 ≤ theta*(k : ℝ)/((k : ℝ)+1) := by positivity
  have hm := rivalMGF_added_lt hk1 hkn hp hp1 htheta
  have hmp : 0 < rivalMGF n (k+1) p (theta*(k : ℝ)/((k : ℝ)+1)) :=
    lt_of_lt_of_le zero_lt_one (one_le_rivalMGF hkn hp hs)
  have hl := log_lt_log hmp hm
  have hlin : ((k+1 : ℕ) : ℝ)*rho*(theta*(k : ℝ)/((k : ℝ)+1)) =
      (k : ℝ)*rho*theta := by
    push_cast
    have hden : (k : ℝ)+1 ≠ 0 := ne_of_gt (by positivity)
    field_simp [hden]
  unfold rivalObjective
  rw [hlin]
  linarith

theorem rivalObjective_scaled_strict {n r k : ℕ} (hr : 1 ≤ r)
    (hrk : r < k) (hkn : k ≤ n) {rho theta : ℝ} {p : ℕ → ℝ}
    (hp : ∀ j ∈ Finset.Icc 1 n, 0 ≤ p j) (hp1 : 0 < p 1)
    (htheta : 0 < theta) :
    rivalObjective n rho r p theta <
      rivalObjective n rho k p (theta*(r : ℝ)/(k : ℝ)) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hstep (j : ℕ) (hrj : r ≤ j) (hjn : j+1 ≤ n) :
      rivalObjective n rho j p (theta*(r : ℝ)/(j : ℝ)) <
        rivalObjective n rho (j+1) p (theta*(r : ℝ)/((j+1 : ℕ) : ℝ)) := by
    have hjR : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    have hpos : 0 < theta*(r : ℝ)/(j : ℝ) := div_pos (mul_pos htheta hrR) hjR
    have hh := rivalObjective_added_strict (by omega : 1 ≤ j) hjn hp hp1 hpos
      (rho := rho)
    have harg : (theta*(r : ℝ)/(j : ℝ))*(j : ℝ)/((j : ℝ)+1) =
        theta*(r : ℝ)/((j+1 : ℕ) : ℝ) := by
      push_cast
      have hden : (j : ℝ)+1 ≠ 0 := ne_of_gt (by linarith)
      field_simp [hjR.ne', hden]
    rw [harg] at hh
    exact hh
  have hchain : ∀ j : ℕ, r < j → j ≤ n →
      rivalObjective n rho r p theta <
        rivalObjective n rho j p (theta*(r : ℝ)/(j : ℝ)) := by
    intro j
    induction j with
    | zero => intro hj; omega
    | succ j ih =>
      intro hrj hjn
      by_cases he : r = j
      · subst j
        simpa only [mul_div_cancel_right₀ theta hrR.ne'] using
          hstep r le_rfl hjn
      · exact (ih (by omega) (by omega)).trans (hstep j (by omega) hjn)
  exact hchain k hrk hkn

theorem strict_larger_constraint_finite_witness {n r k : ℕ} {rho J : ℝ}
    {pi : ℕ → ℝ} (hr : 1 ≤ r) (hrk : r < k) (hkn : k ≤ n)
    (hp : ∀ j ∈ Finset.Icc 1 n, 0 ≤ pi j) (hp1 : 0 < pi 1)
    (hz : ∀ j ∈ Finset.Icc (r+1) k, pi j = 0)
    {theta : ℝ} (htheta : 0 < theta)
    (hopt : prefixObjective n rho r pi theta = J) :
    ∃ s ≥ 0, J < prefixObjective n rho k pi s := by
  have hrn : r ≤ n := by omega
  have hpref1 : 0 < prefixLaw pi r 1 := by simpa [prefixLaw, hr] using hp1
  have hh := rivalObjective_scaled_strict hr hrk hkn
    (prefixLaw_nonneg hp r) hpref1 htheta (rho := rho)
  refine ⟨theta*(r : ℝ)/(k : ℝ), by positivity, ?_⟩
  rw [← prefixObjective_eq_rival hrn] at hh
  rw [hopt] at hh
  rw [prefixObjective_eq_rival hkn, prefixLaw_eq_of_zero_gap hrk.le hz]
  exact hh

theorem last_occupied_before {n k : ℕ} {pi : ℕ → ℝ}
    (hp : ∀ j ∈ Finset.Icc 1 n, 0 ≤ pi j) (hp1 : 0 < pi 1)
    (hk1 : 1 < k) (hkn : k ≤ n) (hpk : pi k = 0) :
    ∃ r : ℕ, 1 ≤ r ∧ r < k ∧ 0 < pi r ∧
      ∀ j ∈ Finset.Icc (r+1) k, pi j = 0 := by
  classical
  let S := (Finset.Icc 1 (k-1)).filter (fun j => 0 < pi j)
  have hS : S.Nonempty := by
    refine ⟨1, ?_⟩
    simp only [S, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨le_rfl, by omega⟩, hp1⟩
  let r := S.max' hS
  have hrS : r ∈ S := Finset.max'_mem S hS
  rcases Finset.mem_filter.mp hrS with ⟨hrI, hpr⟩
  rcases Finset.mem_Icc.mp hrI with ⟨hr1, hrk⟩
  refine ⟨r, hr1, by omega, hpr, ?_⟩
  intro j hj
  rcases Finset.mem_Icc.mp hj with ⟨hrj, hjk⟩
  by_cases he : j = k
  · simpa [he] using hpk
  · have hjn : j ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨by omega, hjk.trans hkn⟩
    apply le_antisymm _ (hp j hjn)
    by_contra hpos
    have hjS : j ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, lt_of_not_ge hpos⟩
    have hle : j ≤ r := Finset.le_max' S j hjS
    omega

end FCAppendix.Bayes
