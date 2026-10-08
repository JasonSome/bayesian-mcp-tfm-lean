import FCAppendix.Proposer.CommonListGame
import FCAppendix.Exclusive.Kernel

namespace FCAppendix
namespace Exclusive

open scoped BigOperators
open Proposer CommonList

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def exclusiveReceipt (b : ι → ℝ) : ι → ℕ → ℝ :=
  fun i K => if K = 1 then b i else 0

omit [DecidableEq ι] in
theorem exclusive_score (n : ℕ) (b : ι → ℝ) (μ : FiniteLaw (Finset ι)) (i : ι) :
    score n (exclusiveReceipt b) μ i = b i * (1 - marginal μ i) ^ (n - 1) := by
  rw [← exclusive_receipt (n - 1) (marginal μ i) (b i) (marginal_nonneg μ i)
    (marginal_le_one μ i), FiniteLaw.prob_eq_expect, ← FiniteLaw.expect_const_mul]
  unfold score exclusiveReceipt
  apply FiniteLaw.expect_congr
  intro r
  by_cases h : r.val = 0 <;> simp [h]

theorem exclusive_payoff_eq (n : ℕ) (b : ι → ℝ) (μ ν : FiniteLaw (Finset ι)) :
    payoff n (exclusiveReceipt b) μ ν =
      ∑ i, marginal ν i * (b i * (1 - marginal μ i) ^ (n - 1)) := by
  rw [payoff_eq]
  simp_rw [exclusive_score n b μ]

def ExclusiveEquilibrium (n c : ℕ) (b : ι → ℝ) (μ : FiniteLaw (Finset ι)) : Prop :=
  IsSymmetricEquilibrium n c (exclusiveReceipt b) μ

noncomputable def rate (n : ℕ) : ℝ := 1 / ((n - 1 : ℕ) : ℝ)

theorem rate_pos (n : ℕ) (hn : 2 ≤ n) : 0 < rate n := by
  have h : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - 1 by omega)
  exact div_pos one_pos h

theorem rate_mul (n : ℕ) (hn : 2 ≤ n) : rate n * ((n - 1 : ℕ) : ℝ) = 1 := by
  have h : ((n - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show n - 1 ≠ 0 by omega)
  exact one_div_mul_cancel h

noncomputable def demand (n : ℕ) (b lam : ℝ) : ℝ := max 0 (1 - (lam / b) ^ rate n)

theorem demand_nonneg (n : ℕ) (b lam : ℝ) : 0 ≤ demand n b lam := le_max_left _ _

theorem demand_le_one (n : ℕ) {b lam : ℝ} (hb : 0 < b) (hlam : 0 ≤ lam) :
    demand n b lam ≤ 1 := by
  have h := Real.rpow_nonneg (div_nonneg hlam (le_of_lt hb)) (rate n)
  exact max_le zero_le_one (by linarith)

theorem demand_lt_one (n : ℕ) {b lam : ℝ} (hb : 0 < b) (hlam : 0 < lam) :
    demand n b lam < 1 := by
  have h := Real.rpow_pos_of_pos (div_pos hlam hb) (rate n)
  exact max_lt zero_lt_one (by linarith)

theorem demand_zero_price (n : ℕ) (hn : 2 ≤ n) (b : ℝ) : demand n b 0 = 1 := by
  unfold demand
  rw [zero_div, Real.zero_rpow (ne_of_gt (rate_pos n hn))]
  norm_num

theorem demand_eq_zero_iff (n : ℕ) (hn : 2 ≤ n) {b lam : ℝ} (hb : 0 < b) (hlam : 0 ≤ lam) :
    demand n b lam = 0 ↔ b ≤ lam := by
  have hr := rate_pos n hn
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    have hx : lam / b < 1 := (div_lt_one hb).mpr hlt
    have hp := Real.rpow_lt_one (div_nonneg hlam (le_of_lt hb)) hx hr
    have hpos : 0 < 1 - (lam / b) ^ rate n := by linarith
    have : 0 < demand n b lam := lt_of_lt_of_le hpos (le_max_right _ _)
    linarith
  · intro h
    have hx : 1 ≤ lam / b := (one_le_div hb).mpr h
    have hp := Real.one_le_rpow hx (le_of_lt hr)
    exact max_eq_left (by linarith)

theorem demand_pos_iff (n : ℕ) (hn : 2 ≤ n) {b lam : ℝ} (hb : 0 < b) (hlam : 0 ≤ lam) :
    0 < demand n b lam ↔ lam < b := by
  rw [← not_le, ← not_le, ← demand_eq_zero_iff n hn hb hlam]
  constructor
  · intro h heq
    exact h (le_of_eq heq)
  · intro h hle
    exact h (le_antisymm hle (demand_nonneg n b lam))

theorem continuous_demand (n : ℕ) (hn : 2 ≤ n) (b : ℝ) :
    Continuous (fun lam => demand n b lam) := by
  unfold demand
  have hr := le_of_lt (rate_pos n hn)
  exact continuous_const.max (continuous_const.sub
    ((continuous_id.div_const b).rpow_const (fun _ => Or.inr hr)))

theorem demand_antitone (n : ℕ) (hn : 2 ≤ n) {b lam lam' : ℝ} (hb : 0 < b)
    (hlam : 0 ≤ lam) (hle : lam ≤ lam') : demand n b lam' ≤ demand n b lam := by
  have hp := Real.rpow_le_rpow (div_nonneg hlam (le_of_lt hb))
    (div_le_div_of_nonneg_right hle (le_of_lt hb)) (le_of_lt (rate_pos n hn))
  exact max_le_max le_rfl (by linarith)

theorem demand_strict (n : ℕ) (hn : 2 ≤ n) {b lam lam' : ℝ} (hb : 0 < b)
    (hlam : 0 ≤ lam) (hlt : lam < lam') (hpos : 0 < demand n b lam) :
    demand n b lam' < demand n b lam := by
  have hr := rate_pos n hn
  have hlb : lam < b := (demand_pos_iff n hn hb hlam).mp hpos
  have hp := Real.rpow_lt_rpow (div_nonneg hlam (le_of_lt hb))
    (div_lt_div_of_pos_right hlt hb) hr
  have hx : lam / b < 1 := (div_lt_one hb).mpr hlb
  have hq := Real.rpow_lt_one (div_nonneg hlam (le_of_lt hb)) hx hr
  have he : demand n b lam = 1 - (lam / b) ^ rate n := max_eq_right (by linarith)
  rw [he]
  exact max_lt (by linarith) (by linarith)

theorem demand_receipt (n : ℕ) (hn : 2 ≤ n) {b lam : ℝ} (hb : 0 < b) (hlam : 0 < lam) :
    b * (1 - demand n b lam) ^ (n - 1) = min b lam := by
  have hr := rate_pos n hn
  by_cases hlb : lam < b
  · have hx : lam / b < 1 := (div_lt_one hb).mpr hlb
    have hx0 : 0 ≤ lam / b := div_nonneg (le_of_lt hlam) (le_of_lt hb)
    have hq := Real.rpow_lt_one hx0 hx hr
    have he : demand n b lam = 1 - (lam / b) ^ rate n := max_eq_right (by linarith)
    have hpow : ((lam / b) ^ rate n) ^ (n - 1) = lam / b := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0, rate_mul n hn, Real.rpow_one]
    rw [he, sub_sub_cancel, hpow, min_eq_right (le_of_lt hlb)]
    field_simp
  · push Not at hlb
    rw [(demand_eq_zero_iff n hn hb (le_of_lt hlam)).mpr hlb, sub_zero, one_pow, mul_one,
      min_eq_left hlb]

omit [DecidableEq ι] in

theorem sum_demand_zero_price (n : ℕ) (hn : 2 ≤ n) (b : ι → ℝ) :
    ∑ i, demand n (b i) 0 = Fintype.card ι := by
  simp [demand_zero_price n hn]

omit [DecidableEq ι] in
theorem sum_demand_high_price (n : ℕ) (hn : 2 ≤ n) (b : ι → ℝ) (hb : ∀ i, 0 < b i)
    (lam : ℝ) (hlam : ∀ i, b i ≤ lam) : ∑ i, demand n (b i) lam = 0 := by
  have hl : ∀ i, 0 ≤ lam := fun i => le_trans (le_of_lt (hb i)) (hlam i)
  apply Finset.sum_eq_zero
  intro i _
  exact (demand_eq_zero_iff n hn (hb i) (hl i)).mpr (hlam i)

omit [DecidableEq ι] in

theorem exists_price (n : ℕ) (hn : 2 ≤ n) (b : ι → ℝ) (hb : ∀ i, 0 < b i) (c : ℕ)
    (hc : c < Fintype.card ι) : ∃ lam, 0 < lam ∧ ∑ i, demand n (b i) lam = c := by
  let M : ℝ := 1 + ∑ i, b i
  have hsum0 : 0 ≤ ∑ i, b i := Finset.sum_nonneg (fun i _ => le_of_lt (hb i))
  have hM : 0 ≤ M := by dsimp [M]; linarith
  have hbM : ∀ i, b i ≤ M := by
    intro i
    have h := Finset.single_le_sum (s := Finset.univ) (f := b)
      (fun j _ => le_of_lt (hb j)) (Finset.mem_univ i)
    dsimp [M]
    linarith
  let D : ℝ → ℝ := fun lam => ∑ i, demand n (b i) lam
  have hcont : Continuous D :=
    continuous_finsetSum _ (fun i _ => continuous_demand n hn (b i))
  have hD0 : D 0 = Fintype.card ι := sum_demand_zero_price n hn b
  have hDM : D M = 0 := sum_demand_high_price n hn b hb M hbM
  have hbetween : (c : ℝ) ∈ Set.Icc (D M) (D 0) := by
    rw [hDM, hD0]
    exact ⟨Nat.cast_nonneg _, by exact_mod_cast le_of_lt hc⟩
  obtain ⟨lam, hlam, hroot⟩ := intermediate_value_Icc' hM hcont.continuousOn hbetween
  refine ⟨lam, lt_of_le_of_ne hlam.1 ?_, hroot⟩
  intro h0
  rw [← h0, hD0] at hroot
  have : Fintype.card ι = c := by exact_mod_cast hroot
  omega

omit [DecidableEq ι] in

theorem sum_demand_strict (n : ℕ) (hn : 2 ≤ n) (b : ι → ℝ) (hb : ∀ i, 0 < b i)
    {lam lam' : ℝ} (hlam : 0 ≤ lam) (hlt : lam < lam')
    (hpos : 0 < ∑ i, demand n (b i) lam) :
    ∑ i, demand n (b i) lam' < ∑ i, demand n (b i) lam := by
  have hex : ∃ i, 0 < demand n (b i) lam := by
    by_contra hno
    push Not at hno
    have : (∑ i, demand n (b i) lam) ≤ 0 := Finset.sum_nonpos (fun i _ => hno i)
    linarith
  obtain ⟨i, hi⟩ := hex
  apply Finset.sum_lt_sum
  · intro j _
    exact demand_antitone n hn (hb j) hlam (le_of_lt hlt)
  · exact ⟨i, Finset.mem_univ _, demand_strict n hn (hb i) hlam hlt hi⟩

omit [DecidableEq ι] in

theorem exists_unique_price (n : ℕ) (hn : 2 ≤ n) (b : ι → ℝ) (hb : ∀ i, 0 < b i) (c : ℕ)
    (hc1 : 1 ≤ c) (hc : c < Fintype.card ι) :
    ∃! lam, 0 < lam ∧ ∑ i, demand n (b i) lam = c := by
  obtain ⟨lam, hlam, hroot⟩ := exists_price n hn b hb c hc
  refine ⟨lam, ⟨hlam, hroot⟩, ?_⟩
  rintro lam' ⟨hlam', hroot'⟩
  have hcpos : (0 : ℝ) < c := by exact_mod_cast hc1
  rcases lt_trichotomy lam' lam with h | h | h
  · have hs := sum_demand_strict n hn b hb (le_of_lt hlam') h (by rw [hroot']; exact hcpos)
    rw [hroot, hroot'] at hs
    exact absurd hs (lt_irrefl _)
  · exact h
  · have hs := sum_demand_strict n hn b hb (le_of_lt hlam) h (by rw [hroot]; exact hcpos)
    rw [hroot, hroot'] at hs
    exact absurd hs (lt_irrefl _)

omit [DecidableEq ι] in

theorem zero_capacity_roots (n : ℕ) (hn : 2 ≤ n) (b : ι → ℝ) (hb : ∀ i, 0 < b i)
    (lam : ℝ) (hlam : ∀ i, b i ≤ lam) : ∑ i, demand n (b i) lam = ((0 : ℕ) : ℝ) := by
  rw [sum_demand_high_price n hn b hb lam hlam]
  norm_num

omit [Fintype ι] [DecidableEq ι] in

theorem demand_threshold (n : ℕ) (hn : 2 ≤ n) (b : ι → ℝ) (hb : ∀ i, 0 < b i)
    (lam : ℝ) (hlam : 0 < lam) :
    Threshold (fun i => demand n (b i) lam)
      (fun i => b i * (1 - demand n (b i) lam) ^ (n - 1)) lam := by
  refine ⟨fun i _ => ?_, fun i hi => ?_, fun i hpos _ => ?_⟩
  · beta_reduce
    rw [demand_receipt n hn (hb i) hlam]
    exact min_le_right _ _
  · exact absurd hi (ne_of_lt (demand_lt_one n (hb i) hlam))
  · beta_reduce
    rw [demand_receipt n hn (hb i) hlam]
    exact min_eq_right (le_of_lt ((demand_pos_iff n hn (hb i) (le_of_lt hlam)).mp hpos))

omit [DecidableEq ι] in

theorem eq_demand_of_threshold (n : ℕ) (hn : 2 ≤ n) (b : ι → ℝ) (hb : ∀ i, 0 < b i)
    (c : ℕ) (lam : ℝ) (hlam : 0 < lam) (hroot : ∑ i, demand n (b i) lam = c)
    (q : ι → ℝ) (τ : ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) (hqs : ∑ i, q i = c)
    (hτ : 0 ≤ τ) (hq : Threshold q (fun i => b i * (1 - q i) ^ (n - 1)) τ) :
    q = fun i => demand n (b i) lam :=
  unique_marginals n hn b hb q _ τ lam c hq0 hq1 hqs (fun _ => demand_nonneg _ _ _)
    (fun i => demand_le_one n (hb i) (le_of_lt hlam)) hroot hτ (le_of_lt hlam) hq
    (demand_threshold n hn b hb lam hlam)

theorem demand_best_response (n : ℕ) (hn : 2 ≤ n) (b : ι → ℝ) (hb : ∀ i, 0 < b i) (c : ℕ)
    (lam : ℝ) (hlam : 0 < lam) (hroot : ∑ i, demand n (b i) lam = c)
    (μ ν : FiniteLaw (Finset ι)) (hμ : ∀ i, marginal μ i = demand n (b i) lam)
    (hν : ∀ i, marginal ν i = demand n (b i) lam)
    (ν' : FiniteLaw (Finset ι)) (hν' : Feasible c ν') :
    payoff n (exclusiveReceipt b) μ ν' ≤ payoff n (exclusiveReceipt b) μ ν := by
  rw [exclusive_payoff_eq, exclusive_payoff_eq]
  simp_rw [hμ, hν]
  exact threshold_linear_optimal (fun i => demand n (b i) lam) _ lam c
    (fun i => demand_nonneg _ _ _) (fun i => demand_le_one n (hb i) (le_of_lt hlam)) hroot
    (le_of_lt hlam) (demand_threshold n hn b hb lam hlam) (marginal ν')
    (marginal_nonneg ν') (marginal_le_one ν') (marginal_capacity ν' c hν')

theorem exists_exclusive_equilibrium (n : ℕ) (hn : 2 ≤ n) (b : ι → ℝ) (hb : ∀ i, 0 < b i)
    (c : ℕ) (lam : ℝ) (hlam : 0 < lam) (hroot : ∑ i, demand n (b i) lam = c) :
    ∃ μ : FiniteLaw (Finset ι), (∀ S, μ.mass S ≠ 0 → S.card = c) ∧
      (∀ i, marginal μ i = demand n (b i) lam) ∧ ExclusiveEquilibrium n c b μ := by
  obtain ⟨μ, hcap, hmarg⟩ := ExactCapacity.exists_lottery (fun i => demand n (b i) lam) c
    (fun i => demand_nonneg _ _ _) (fun i => demand_le_one n (hb i) (le_of_lt hlam)) hroot
  have hm : ∀ i, marginal μ i = demand n (b i) lam := hmarg
  exact ⟨μ, hcap, hm, fun S hS => le_of_eq (hcap S hS),
    fun ν hν => demand_best_response n hn b hb c lam hlam hroot μ μ hm hm ν hν⟩

theorem marginal_pos_of_mem (μ : FiniteLaw (Finset ι)) (S : Finset ι) (hS : μ.mass S ≠ 0)
    (i : ι) (hi : i ∈ S) : 0 < marginal μ i := by
  rw [marginal_eq_expect]
  unfold FiniteLaw.expect
  have hpos : 0 < μ.mass S := lt_of_le_of_ne (μ.nonneg S) (Ne.symm hS)
  calc
    0 < μ.mass S * (if i ∈ S then 1 else 0) := by simp [hi, hpos]
    _ ≤ ∑ T, μ.mass T * (if i ∈ T then 1 else 0) :=
      Finset.single_le_sum (f := fun T => μ.mass T * (if i ∈ T then (1 : ℝ) else 0))
        (fun T _ => mul_nonneg (μ.nonneg T) (by split <;> norm_num)) (Finset.mem_univ S)

theorem demand_support_optimal (n : ℕ) (hn : 2 ≤ n) (b : ι → ℝ) (hb : ∀ i, 0 < b i)
    (c : ℕ) (lam : ℝ) (hlam : 0 < lam) (μ : FiniteLaw (Finset ι))
    (hcap : ∀ S, μ.mass S ≠ 0 → S.card = c) (hμ : ∀ i, marginal μ i = demand n (b i) lam) :
    ∀ S, μ.mass S ≠ 0 →
      Finite.Optimal c (fun i => b i * (1 - demand n (b i) lam) ^ (n - 1)) S := by
  intro S hS
  refine ⟨le_of_eq (hcap S hS), fun T hT => ?_⟩
  have hr : ∀ i, b i * (1 - demand n (b i) lam) ^ (n - 1) = min (b i) lam :=
    fun i => demand_receipt n hn (hb i) hlam
  simp only [hr]
  have hS' : ∀ i ∈ S, min (b i) lam = lam := by
    intro i hi
    have hpos := marginal_pos_of_mem μ S hS i hi
    rw [hμ i] at hpos
    exact min_eq_right (le_of_lt ((demand_pos_iff n hn (hb i) (le_of_lt hlam)).mp hpos))
  calc
    (∑ i ∈ T, min (b i) lam) ≤ ∑ _i ∈ T, lam :=
      Finset.sum_le_sum (fun i _ => min_le_right _ _)
    _ = (T.card : ℝ) * lam := by simp
    _ ≤ (c : ℝ) * lam := mul_le_mul_of_nonneg_right (by exact_mod_cast hT) (le_of_lt hlam)
    _ = (S.card : ℝ) * lam := by rw [hcap S hS]
    _ = ∑ _i ∈ S, lam := by simp
    _ = ∑ i ∈ S, min (b i) lam := Finset.sum_congr rfl (fun i hi => (hS' i hi).symm)

theorem exclusive_small_list (n : ℕ) (hn : 2 ≤ n) (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i) (c : ℕ)
    (hc : (Finset.univ.filter (fun i => 0 < b i)).card ≤ c) :
    ExclusiveEquilibrium n c b (FiniteLaw.dirac (Finset.univ.filter (fun i => 0 < b i))) := by
  set P := Finset.univ.filter (fun i => 0 < b i)
  have hzero : ∀ i, b i * (1 - marginal (FiniteLaw.dirac P) i) ^ (n - 1) = 0 := by
    intro i
    rw [marginal_dirac]
    by_cases hi : i ∈ P
    · rw [if_pos hi, sub_self, zero_pow (by omega), mul_zero]
    · have hbi : b i = 0 := by
        have : ¬ 0 < b i := fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        linarith [hb i]
      rw [hbi, zero_mul]
  refine ⟨feasible_dirac c P hc, fun ν _ => ?_⟩
  rw [exclusive_payoff_eq, exclusive_payoff_eq]
  simp [hzero]

theorem exclusive_small_list_unique (n : ℕ) (hn : 2 ≤ n) (b : ι → ℝ) (hb : ∀ i, 0 < b i)
    (c : ℕ) (hc : Fintype.card ι ≤ c) (μ : FiniteLaw (Finset ι))
    (hμ : ExclusiveEquilibrium n c b μ) : μ = FiniteLaw.dirac Finset.univ := by
  apply eq_dirac_univ_of_marginal_eq_one
  have h := hμ.2 _ (feasible_dirac c Finset.univ (by rw [Finset.card_univ]; exact hc))
  rw [exclusive_payoff_eq, exclusive_payoff_eq] at h
  simp only [marginal_dirac, Finset.mem_univ, if_true, one_mul] at h
  set r : ι → ℝ := fun i => b i * (1 - marginal μ i) ^ (n - 1)
  have hterm : ∀ i, 0 ≤ (1 - marginal μ i) * r i := fun i =>
    mul_nonneg (sub_nonneg.mpr (marginal_le_one μ i))
      (mul_nonneg (le_of_lt (hb i)) (pow_nonneg (sub_nonneg.mpr (marginal_le_one μ i)) _))
  have hsum : (∑ i, (1 - marginal μ i) * r i) = 0 := by
    apply le_antisymm _ (Finset.sum_nonneg (fun i _ => hterm i))
    have he : (∑ i, (1 - marginal μ i) * r i) = (∑ i, r i) - ∑ i, marginal μ i * r i := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    rw [he]
    linarith
  intro i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hterm j)).mp hsum i
    (Finset.mem_univ i)
  have hpow : b i * (1 - marginal μ i) ^ n = 0 := by
    have he : (1 - marginal μ i) * r i = b i * (1 - marginal μ i) ^ n := by
      simp only [r]
      rw [show n = (n - 1) + 1 from by omega, pow_succ]
      simp only [Nat.add_sub_cancel]
      ring
    rw [← he]
    exact hi
  have hz : (1 - marginal μ i) ^ n = 0 :=
    (mul_eq_zero.mp hpow).resolve_left (ne_of_gt (hb i))
  have := pow_eq_zero_iff (n := n) (by omega) |>.mp hz
  linarith

theorem deviator_count_binomial (n : ℕ) (b : ι → ℝ) (hb : ∀ i, 0 < b i) (lam : ℝ)
    (hlam : 0 < lam) (μ : FiniteLaw (Finset ι)) (hμ : ∀ i, marginal μ i = demand n (b i) lam)
    (k : ℕ) (i : ι) :
    (iid μ k).map (includersCount i) =
      IndependentCounts.binomial k (demand n (b i) lam) (demand_nonneg _ _ _)
        (demand_le_one n (hb i) (le_of_lt hlam)) := by
  rw [iid_includers_law]
  exact binomial_congr k (hμ i) _ _ _ _

end Exclusive
end FCAppendix
