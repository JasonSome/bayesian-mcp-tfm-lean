import FCAppendix.Proposer.PayOnceExistence
import FCAppendix.Finite.ReceiptOrder

namespace FCAppendix
namespace CommonList

open scoped BigOperators
open Proposer

section IID

variable {Ω : Type*} [Fintype Ω]

noncomputable def iid (μ : FiniteLaw Ω) (k : ℕ) : FiniteLaw (Fin k → Ω) where
  mass f := ∏ j, μ.mass (f j)
  nonneg f := Finset.prod_nonneg (fun j _ => μ.nonneg (f j))
  total := by
    rw [← Fintype.prod_sum (fun (_ : Fin k) ω => μ.mass ω)]
    simp [μ.total]

theorem expect_iid_zero (μ : FiniteLaw Ω) (F : (Fin 0 → Ω) → ℝ) :
    (iid μ 0).expect F = F Fin.elim0 := by
  unfold FiniteLaw.expect
  simp [iid, Subsingleton.elim _ (Fin.elim0 : Fin 0 → Ω)]

theorem expect_iid_succ (μ : FiniteLaw Ω) (k : ℕ) (F : (Fin (k + 1) → Ω) → ℝ) :
    (iid μ (k + 1)).expect F =
      μ.expect (fun ω => (iid μ k).expect (fun f => F (Fin.cons ω f))) := by
  unfold FiniteLaw.expect
  rw [← FiniteLaw.sum_equiv (Fin.consEquiv (fun _ : Fin (k + 1) => Ω)),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  simp only [iid, Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  rw [mul_assoc]
  rfl

end IID

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def Feasible (c : ℕ) (μ : FiniteLaw (Finset ι)) : Prop :=
  ∀ S, μ.mass S ≠ 0 → S.card ≤ c

def includers (i : ι) {k : ℕ} (T : Fin k → Finset ι) : ℕ :=
  ∑ j, if i ∈ T j then 1 else 0

omit [Fintype ι] in
theorem includers_cons (i : ι) {k : ℕ} (S : Finset ι) (T : Fin k → Finset ι) :
    includers i (Fin.cons S T : Fin (k + 1) → Finset ι) =
      (if i ∈ S then 1 else 0) + includers i T := by
  unfold includers
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

omit [Fintype ι] in
theorem includers_le (i : ι) {k : ℕ} (T : Fin k → Finset ι) : includers i T ≤ k := by
  calc
    includers i T ≤ ∑ _j : Fin k, 1 :=
      Finset.sum_le_sum (fun j _ => by split <;> omega)
    _ = k := by simp

def includersCount (i : ι) {k : ℕ} (T : Fin k → Finset ι) : Fin (k + 1) :=
  ⟨includers i T, Nat.lt_succ_of_le (includers_le i T)⟩

omit [DecidableEq ι] in
theorem marginal_nonneg (μ : FiniteLaw (Finset ι)) (i : ι) : 0 ≤ marginal μ i :=
  μ.prob_nonneg _

omit [DecidableEq ι] in
theorem marginal_le_one (μ : FiniteLaw (Finset ι)) (i : ι) : marginal μ i ≤ 1 :=
  μ.prob_le_one _

theorem marginal_eq_expect (μ : FiniteLaw (Finset ι)) (i : ι) :
    marginal μ i = μ.expect (fun S => if i ∈ S then 1 else 0) := by
  unfold marginal
  rw [FiniteLaw.prob_eq_expect]

theorem binomial_congr (k : ℕ) {p q : ℝ} (h : p = q) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    IndependentCounts.binomial k p hp0 hp1 = IndependentCounts.binomial k q hq0 hq1 := by
  subst h
  rfl

theorem expect_includers (μ : FiniteLaw (Finset ι)) (i : ι) (k : ℕ) (φ : ℕ → ℝ) :
    (iid μ k).expect (fun T => φ (includers i T)) =
      (IndependentCounts.binomial k (marginal μ i) (marginal_nonneg μ i)
        (marginal_le_one μ i)).expect (fun r => φ r.val) := by
  induction k generalizing φ with
  | zero =>
    rw [expect_iid_zero]
    simp [IndependentCounts.binomial, IndependentCounts.independentCount, includers]
  | succ k ih =>
    rw [expect_iid_succ, IndependentCounts.expect_binomial_succ]
    simp only [includers_cons, IndependentCounts.val_add_false, IndependentCounts.val_add_true]
    set β := IndependentCounts.binomial k (marginal μ i) (marginal_nonneg μ i)
      (marginal_le_one μ i)
    have h : ∀ S : Finset ι,
        (iid μ k).expect (fun T => φ ((if i ∈ S then 1 else 0) + includers i T)) =
          (if i ∈ S then 1 else 0) * β.expect (fun r => φ (1 + r.val)) +
            (1 - (if i ∈ S then 1 else 0)) * β.expect (fun r => φ r.val) := by
      intro S
      rw [ih (fun m => φ ((if i ∈ S then 1 else 0) + m))]
      by_cases hS : i ∈ S <;> simp [hS]
    rw [FiniteLaw.expect_congr μ h, FiniteLaw.expect_add, FiniteLaw.expect_mul_const,
      FiniteLaw.expect_mul_const, FiniteLaw.expect_sub, FiniteLaw.expect_const,
      ← marginal_eq_expect]
    ring

theorem iid_includers_law (μ : FiniteLaw (Finset ι)) (i : ι) (k : ℕ) :
    (iid μ k).map (includersCount i) =
      IndependentCounts.binomial k (marginal μ i) (marginal_nonneg μ i)
        (marginal_le_one μ i) := by
  apply FiniteLaw.ext_expect
  intro f
  rw [FiniteLaw.expect_map]
  let φ : ℕ → ℝ := fun m => if h : m < k + 1 then f ⟨m, h⟩ else 0
  calc
    (iid μ k).expect (fun T => f (includersCount i T)) =
        (iid μ k).expect (fun T => φ (includers i T)) := by
      apply FiniteLaw.expect_congr
      intro T
      have h := Nat.lt_succ_of_le (includers_le i T)
      simp only [φ, dif_pos h]
      rfl
    _ = _ := expect_includers μ i k φ
    _ = _ := by
      apply FiniteLaw.expect_congr
      intro r
      simp only [φ, dif_pos r.isLt]

theorem iid_includers_law_eq_independentCount (μ : FiniteLaw (Finset ι)) (i : ι) (k : ℕ) :
    (iid μ k).map (includersCount i) =
      IndependentCounts.independentCount μ (fun S => decide (i ∈ S)) k := by
  rw [iid_includers_law, IndependentCounts.independentCount_bernoulli]
  apply binomial_congr
  simp [IndependentCounts.acceptance, marginal]

noncomputable def payoff (n : ℕ) (receipt : ι → ℕ → ℝ) (μ ν : FiniteLaw (Finset ι)) : ℝ :=
  (ν.prod (iid μ (n - 1))).expect (fun z => ∑ i ∈ z.1, receipt i (includers i z.2 + 1))

noncomputable def score (n : ℕ) (receipt : ι → ℕ → ℝ) (μ : FiniteLaw (Finset ι))
    (i : ι) : ℝ :=
  (IndependentCounts.binomial (n - 1) (marginal μ i) (marginal_nonneg μ i)
    (marginal_le_one μ i)).expect (fun r => receipt i (r.val + 1))

theorem payoff_eq_revenue (n : ℕ) (receipt : ι → ℕ → ℝ) (μ ν : FiniteLaw (Finset ι)) :
    payoff n receipt μ ν = revenue ν (score n receipt μ) := by
  unfold payoff revenue
  rw [FiniteLaw.expect_prod]
  apply FiniteLaw.expect_congr
  intro S
  rw [FiniteLaw.expect_finset_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact expect_includers μ i (n - 1) (fun m => receipt i (m + 1))

theorem payoff_eq (n : ℕ) (receipt : ι → ℕ → ℝ) (μ ν : FiniteLaw (Finset ι)) :
    payoff n receipt μ ν = ∑ i, marginal ν i * score n receipt μ i := by
  rw [payoff_eq_revenue, revenue_marginals]

def IsSymmetricEquilibrium (n c : ℕ) (receipt : ι → ℕ → ℝ) (μ : FiniteLaw (Finset ι)) :
    Prop :=
  Feasible c μ ∧ ∀ ν, Feasible c ν → payoff n receipt μ ν ≤ payoff n receipt μ μ

noncomputable def payOnceReceipt (b : ι → ℝ) : ι → ℕ → ℝ := fun i K => b i / (K : ℝ)

omit [DecidableEq ι] in
theorem payOnce_score (n : ℕ) (hn : 1 ≤ n) (b : ι → ℝ) (μ : FiniteLaw (Finset ι)) (i : ι) :
    score n (payOnceReceipt b) μ i = b i * PayOnce.H n (marginal μ i) := by
  unfold score payOnceReceipt
  have h := PayOnce.balanced_receipt (n - 1) (marginal μ i) (marginal_nonneg μ i)
    (marginal_le_one μ i)
  have hH : PayOnce.H (n - 1 + 1) (marginal μ i) = PayOnce.H n (marginal μ i) := by
    rw [Nat.sub_add_cancel hn]
  rw [← hH, ← h, ← FiniteLaw.expect_const_mul]
  apply FiniteLaw.expect_congr
  intro r
  push_cast
  ring

theorem payOnce_payoff_eq (n : ℕ) (hn : 1 ≤ n) (b : ι → ℝ) (μ ν : FiniteLaw (Finset ι)) :
    payoff n (payOnceReceipt b) μ ν =
      ∑ i, marginal ν i * (b i * PayOnce.H n (marginal μ i)) := by
  rw [payoff_eq]
  simp_rw [payOnce_score n hn b μ]

omit [DecidableEq ι] in
theorem exists_support (μ : FiniteLaw (Finset ι)) : ∃ S, μ.mass S ≠ 0 := by
  by_contra h
  push Not at h
  have ht := μ.total
  simp [h] at ht

theorem marginal_eq_one_of_forall (μ : FiniteLaw (Finset ι)) (i : ι)
    (h : ∀ S, μ.mass S ≠ 0 → i ∈ S) : marginal μ i = 1 := by
  rw [marginal_eq_expect]
  calc
    μ.expect (fun S => if i ∈ S then 1 else 0) = μ.expect (fun _ => 1) := by
      unfold FiniteLaw.expect
      refine Finset.sum_congr rfl (fun S _ => ?_)
      by_cases hS : μ.mass S = 0
      · simp [hS]
      · simp [h S hS]
    _ = 1 := μ.expect_const 1

theorem marginal_eq_zero_of_forall (μ : FiniteLaw (Finset ι)) (i : ι)
    (h : ∀ S, μ.mass S ≠ 0 → i ∉ S) : marginal μ i = 0 := by
  rw [marginal_eq_expect]
  calc
    μ.expect (fun S => if i ∈ S then 1 else 0) = μ.expect (fun _ => 0) := by
      unfold FiniteLaw.expect
      refine Finset.sum_congr rfl (fun S _ => ?_)
      by_cases hS : μ.mass S = 0
      · simp [hS]
      · simp [h S hS]
    _ = 0 := μ.expect_zero

theorem exists_mem_of_marginal_ne_zero (μ : FiniteLaw (Finset ι)) (i : ι)
    (h : marginal μ i ≠ 0) : ∃ S, μ.mass S ≠ 0 ∧ i ∈ S := by
  by_contra hno
  push Not at hno
  exact h (marginal_eq_zero_of_forall μ i hno)

theorem exists_not_mem_of_marginal_ne_one (μ : FiniteLaw (Finset ι)) (i : ι)
    (h : marginal μ i ≠ 1) : ∃ S, μ.mass S ≠ 0 ∧ i ∉ S := by
  by_contra hno
  push Not at hno
  exact h (marginal_eq_one_of_forall μ i hno)

theorem mass_eq_zero_of_marginal_eq_one (μ : FiniteLaw (Finset ι)) (i : ι)
    (h : marginal μ i = 1) (S : Finset ι) (hS : i ∉ S) : μ.mass S = 0 := by
  by_contra hne
  have hpos : 0 < μ.mass S := lt_of_le_of_ne (μ.nonneg S) (Ne.symm hne)
  have hlt : marginal μ i < 1 := by
    rw [marginal_eq_expect]
    unfold FiniteLaw.expect
    calc
      (∑ T, μ.mass T * (if i ∈ T then (1 : ℝ) else 0)) < ∑ T, μ.mass T * 1 := by
        apply Finset.sum_lt_sum
        · intro T _
          exact mul_le_mul_of_nonneg_left (by split <;> norm_num) (μ.nonneg T)
        · exact ⟨S, Finset.mem_univ _, by simpa [hS] using hpos⟩
      _ = 1 := by simp [μ.total]
  linarith

omit [DecidableEq ι] in
theorem feasible_dirac (c : ℕ) (S : Finset ι) (hS : S.card ≤ c) :
    Feasible c (FiniteLaw.dirac S) := by
  classical
  intro T hT
  have hTS : T = S := by
    by_contra hne
    exact hT (by simp [FiniteLaw.dirac, hne])
  rw [hTS]
  exact hS

omit [DecidableEq ι] in
theorem revenue_dirac (S : Finset ι) (r : ι → ℝ) :
    revenue (FiniteLaw.dirac S) r = ∑ i ∈ S, r i := by
  unfold revenue
  rw [FiniteLaw.expect_dirac]

omit [DecidableEq ι] in

theorem support_optimal (c : ℕ) (r : ι → ℝ) (μ : FiniteLaw (Finset ι)) (hμ : Feasible c μ)
    (hbr : ∀ ν, Feasible c ν → revenue ν r ≤ revenue μ r) :
    ∀ S, μ.mass S ≠ 0 → Finite.Optimal c r S := by
  classical
  obtain ⟨S₀, hS₀, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter (fun S : Finset ι => S.card ≤ c)) (fun S => ∑ i ∈ S, r i)
    ⟨∅, by simp⟩
  have hS₀c : S₀.card ≤ c := (Finset.mem_filter.mp hS₀).2
  have hle : ∀ T : Finset ι, T.card ≤ c → (∑ i ∈ T, r i) ≤ ∑ i ∈ S₀, r i :=
    fun T hT => hmax T (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT⟩)
  have hμS₀ : (∑ i ∈ S₀, r i) ≤ revenue μ r := by
    have h := hbr _ (feasible_dirac c S₀ hS₀c)
    rwa [revenue_dirac] at h
  intro S hS
  refine ⟨hμ S hS, fun T hT => le_trans (hle T hT) ?_⟩
  by_contra hlt
  push Not at hlt
  have hpos : 0 < μ.mass S := lt_of_le_of_ne (μ.nonneg S) (Ne.symm hS)
  have hrev : revenue μ r < ∑ i ∈ S₀, r i := by
    unfold revenue FiniteLaw.expect
    calc
      (∑ T, μ.mass T * ∑ i ∈ T, r i) < ∑ T, μ.mass T * ∑ i ∈ S₀, r i := by
        apply Finset.sum_lt_sum
        · intro T _
          by_cases hT : μ.mass T = 0
          · simp [hT]
          · exact mul_le_mul_of_nonneg_left (hle T (hμ T hT)) (μ.nonneg T)
        · exact ⟨S, Finset.mem_univ _, mul_lt_mul_of_pos_left hlt hpos⟩
      _ = _ := by rw [← Finset.sum_mul, μ.total, one_mul]
  linarith

omit [DecidableEq ι] in

theorem optimal_card_eq (c : ℕ) (r : ι → ℝ) (hr : ∀ i, 0 < r i) (hc : c ≤ Fintype.card ι)
    (S : Finset ι) (hS : Finite.Optimal c r S) : S.card = c := by
  by_cases h : ∃ j, j ∉ S
  · obtain ⟨j, hj⟩ := h
    exact Finite.optimal_fills c r S hS j hj (hr j)
  · push Not at h
    have hu : S = Finset.univ := Finset.eq_univ_of_forall h
    have hcap := hS.1
    rw [hu, Finset.card_univ] at hcap ⊢
    omega

omit [Fintype ι] [DecidableEq ι] in
theorem optimal_le_inf' (c : ℕ) (r : ι → ℝ) (S : Finset ι) (hS : Finite.Optimal c r S)
    (hne : S.Nonempty) (j : ι) (hj : j ∉ S) : r j ≤ S.inf' hne r := by
  obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_inf' hne r
  rw [hkeq]
  exact Finite.optimal_swap c r S hS k j hk hj

omit [Fintype ι] [DecidableEq ι] in

theorem optimal_inf'_le (c : ℕ) (r : ι → ℝ) (S T : Finset ι) (hT : Finite.Optimal c r T)
    (hSc : S.card = c) (hTc : T.card = c) (hSne : S.Nonempty) (hTne : T.Nonempty) :
    S.inf' hSne r ≤ T.inf' hTne r := by
  by_contra hlt
  push Not at hlt
  have hsub : S ⊆ T := by
    intro j hj
    by_contra hjT
    have h1 := optimal_le_inf' c r T hT hTne j hjT
    have h2 : S.inf' hSne r ≤ r j := Finset.inf'_le r hj
    linarith
  have heq : S = T := Finset.eq_of_subset_of_card_le hsub (by rw [hSc, hTc])
  subst heq
  exact lt_irrefl _ hlt

theorem threshold_of_support (μ : FiniteLaw (Finset ι)) (r : ι → ℝ) (τ : ℝ)
    (h : ∀ S, μ.mass S ≠ 0 → (∀ j, τ < r j → j ∈ S) ∧ (∀ j ∈ S, τ ≤ r j)) :
    Threshold (marginal μ) r τ := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    by_contra hlt
    push Not at hlt
    have h1 := marginal_eq_one_of_forall μ i (fun S hS => (h S hS).1 i hlt)
    rw [hi] at h1
    norm_num at h1
  · intro i hi
    obtain ⟨S, hS, hiS⟩ := exists_mem_of_marginal_ne_zero μ i (by rw [hi]; norm_num)
    exact (h S hS).2 i hiS
  · intro i hpos hlt
    obtain ⟨S, hS, hiS⟩ := exists_mem_of_marginal_ne_zero μ i (ne_of_gt hpos)
    obtain ⟨T, hT, hiT⟩ := exists_not_mem_of_marginal_ne_one μ i (ne_of_lt hlt)
    have h1 := (h S hS).2 i hiS
    have h2 : ¬ τ < r i := fun h' => hiT ((h T hT).1 i h')
    push Not at h2
    linarith

def PayOnceEquilibrium (n c : ℕ) (b : ι → ℝ) (μ : FiniteLaw (Finset ι)) : Prop :=
  IsSymmetricEquilibrium n c (payOnceReceipt b) μ

theorem payOnceEquilibrium_iff (n : ℕ) (hn : 1 ≤ n) (c : ℕ) (b : ι → ℝ)
    (μ : FiniteLaw (Finset ι)) :
    PayOnceEquilibrium n c b μ ↔ Feasible c μ ∧ ∀ ν, Feasible c ν →
      revenue ν (fun i => b i * PayOnce.H n (marginal μ i)) ≤
        revenue μ (fun i => b i * PayOnce.H n (marginal μ i)) := by
  have hs : score n (payOnceReceipt b) μ = fun i => b i * PayOnce.H n (marginal μ i) :=
    funext (payOnce_score n hn b μ)
  unfold PayOnceEquilibrium IsSymmetricEquilibrium
  simp only [payoff_eq_revenue, hs]

theorem equilibrium_structure (n : ℕ) (hn : 2 ≤ n) (b : ι → ℝ) (hb : ∀ i, 0 < b i)
    (c : ℕ) (hc : c ≤ Fintype.card ι) (μ : FiniteLaw (Finset ι))
    (hμ : PayOnceEquilibrium n c b μ) :
    (∀ S, μ.mass S ≠ 0 →
      Finite.Optimal c (fun i => b i * PayOnce.H n (marginal μ i)) S ∧ S.card = c) ∧
    (∑ i, marginal μ i = c) ∧
    ∃ L, 0 < L ∧ Threshold (marginal μ) (fun i => b i * PayOnce.H n (marginal μ i)) L := by
  set r : ι → ℝ := fun i => b i * PayOnce.H n (marginal μ i) with hr_def
  have hr : ∀ i, 0 < r i := fun i => mul_pos (hb i)
    (PayOnce.H_pos n (by omega) _ (marginal_nonneg μ i) (marginal_le_one μ i))
  obtain ⟨hfeas, hbr⟩ := (payOnceEquilibrium_iff n (by omega) c b μ).mp hμ
  have hopt := support_optimal c r μ hfeas hbr
  have hsupp : ∀ S, μ.mass S ≠ 0 → Finite.Optimal c r S ∧ S.card = c :=
    fun S hS => ⟨hopt S hS, optimal_card_eq c r hr hc S (hopt S hS)⟩
  refine ⟨hsupp, ?_, ?_⟩
  · rw [sum_marginal]
    calc
      μ.expect (fun S => (S.card : ℝ)) = μ.expect (fun _ => (c : ℝ)) := by
        unfold FiniteLaw.expect
        refine Finset.sum_congr rfl (fun S _ => ?_)
        by_cases hS : μ.mass S = 0
        · simp [hS]
        · simp only [(hsupp S hS).2]
      _ = c := μ.expect_const _
  · rcases Nat.eq_zero_or_pos c with hc0 | hc1
    · have hsum : 0 ≤ ∑ i, r i := Finset.sum_nonneg (fun i _ => le_of_lt (hr i))
      refine ⟨1 + ∑ i, r i, by linarith, threshold_of_support μ r _ ?_⟩
      intro S hS
      have hS0 : S = ∅ := Finset.card_eq_zero.mp ((hsupp S hS).2.trans hc0)
      subst hS0
      refine ⟨fun j hj => ?_, fun j hj => absurd hj (Finset.notMem_empty j)⟩
      exfalso
      have hj' : r j ≤ ∑ i, r i :=
        Finset.single_le_sum (fun i _ => le_of_lt (hr i)) (Finset.mem_univ j)
      linarith
    · obtain ⟨S₀, hS₀⟩ := exists_support μ
      have hne : S₀.Nonempty := Finset.card_pos.mp (by rw [(hsupp S₀ hS₀).2]; exact hc1)
      refine ⟨S₀.inf' hne r, ?_, threshold_of_support μ r _ ?_⟩
      · obtain ⟨k, _, hkeq⟩ := Finset.exists_mem_eq_inf' hne r
        rw [hkeq]
        exact hr k
      · intro S hS
        have hSne : S.Nonempty := Finset.card_pos.mp (by rw [(hsupp S hS).2]; exact hc1)
        have heq := le_antisymm
          (optimal_inf'_le c r S₀ S (hsupp S hS).1 (hsupp S₀ hS₀).2 (hsupp S hS).2 hne hSne)
          (optimal_inf'_le c r S S₀ (hsupp S₀ hS₀).1 (hsupp S hS).2 (hsupp S₀ hS₀).2 hSne hne)
        refine ⟨fun j hj => ?_, fun j hj => ?_⟩
        · by_contra hjS
          have h1 := optimal_le_inf' c r S (hsupp S hS).1 hSne j hjS
          linarith
        · have h1 : S.inf' hSne r ≤ r j := Finset.inf'_le r hj
          linarith

theorem exists_equilibrium (n : ℕ) (hn : 2 ≤ n) (b : ι → ℝ) (hb : ∀ i, 0 < b i)
    (c : ℕ) (hc : c ≤ Fintype.card ι) :
    ∃ μ : FiniteLaw (Finset ι), PayOnceEquilibrium n c b μ ∧
      ∀ S, μ.mass S ≠ 0 → S.card = c := by
  obtain ⟨p, _, μ, _, _, _, _, _, hcap, hmarg, hopt⟩ :=
    exists_pay_once_lottery n hn b hb c hc
  refine ⟨μ, (payOnceEquilibrium_iff n (by omega) c b μ).mpr
    ⟨fun S hS => le_of_eq (hcap S hS), ?_⟩, hcap⟩
  intro ν hν
  have hp : marginal μ = p := funext hmarg
  rw [hp]
  exact hopt ν hν

theorem eq_dirac_univ_of_marginal_eq_one (ν : FiniteLaw (Finset ι))
    (hone : ∀ i, marginal ν i = 1) : ν = FiniteLaw.dirac Finset.univ := by
  have hzero : ∀ S, S ≠ Finset.univ → ν.mass S = 0 := by
    intro S hS
    obtain ⟨i, hi⟩ : ∃ i, i ∉ S := by
      by_contra hall
      push Not at hall
      exact hS (Finset.eq_univ_of_forall hall)
    exact mass_eq_zero_of_marginal_eq_one ν i (hone i) S hi
  apply FiniteLaw.ext
  intro S
  classical
  by_cases hS : S = Finset.univ
  · subst hS
    have ht := ν.total
    rw [Finset.sum_eq_single (Finset.univ : Finset ι) (fun T _ hT => hzero T hT)
      (fun h => absurd (Finset.mem_univ _) h)] at ht
    simp [FiniteLaw.dirac, ht]
  · simp [FiniteLaw.dirac, hS, hzero S hS]

theorem marginal_dirac (S : Finset ι) (i : ι) :
    marginal (FiniteLaw.dirac S) i = if i ∈ S then 1 else 0 := by
  rw [marginal_eq_expect, FiniteLaw.expect_dirac]

theorem best_response_univ_iff (c : ℕ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hc : Fintype.card ι ≤ c) (ν : FiniteLaw (Finset ι)) :
    (Feasible c ν ∧ ∀ ν', Feasible c ν' → revenue ν' r ≤ revenue ν r) ↔
      ν = FiniteLaw.dirac Finset.univ := by
  constructor
  · rintro ⟨_, hbr⟩
    have h := hbr _ (feasible_dirac c Finset.univ (by rw [Finset.card_univ]; exact hc))
    rw [revenue_dirac, revenue_marginals] at h
    have hone : ∀ i, marginal ν i = 1 := by
      intro i
      by_contra hne
      have hlt : marginal ν i < 1 := lt_of_le_of_ne (marginal_le_one ν i) hne
      have hs : (∑ j, marginal ν j * r j) < ∑ j, r j := by
        apply Finset.sum_lt_sum
        · intro j _
          have := mul_le_mul_of_nonneg_right (marginal_le_one ν j) (le_of_lt (hr j))
          linarith
        · exact ⟨i, Finset.mem_univ _, by nlinarith [hr i]⟩
      linarith
    exact eq_dirac_univ_of_marginal_eq_one ν hone
  · rintro rfl
    refine ⟨feasible_dirac c Finset.univ (by rw [Finset.card_univ]; exact hc), ?_⟩
    intro ν' _
    rw [revenue_dirac, revenue_marginals]
    apply Finset.sum_le_sum
    intro j _
    have := mul_le_mul_of_nonneg_right (marginal_le_one ν' j) (le_of_lt (hr j))
    linarith

theorem payOnce_best_response_small_list (n : ℕ) (hn : 1 ≤ n) (b : ι → ℝ)
    (hb : ∀ i, 0 < b i) (c : ℕ) (hc : Fintype.card ι ≤ c) (μ ν : FiniteLaw (Finset ι)) :
    (Feasible c ν ∧ ∀ ν', Feasible c ν' →
        payoff n (payOnceReceipt b) μ ν' ≤ payoff n (payOnceReceipt b) μ ν) ↔
      ν = FiniteLaw.dirac Finset.univ := by
  have hs : score n (payOnceReceipt b) μ = fun i => b i * PayOnce.H n (marginal μ i) :=
    funext (payOnce_score n hn b μ)
  simp only [payoff_eq_revenue, hs]
  exact best_response_univ_iff c _ (fun i => mul_pos (hb i)
    (PayOnce.H_pos n hn _ (marginal_nonneg μ i) (marginal_le_one μ i))) hc ν

theorem payOnceEquilibrium_small_list_iff (n : ℕ) (hn : 1 ≤ n) (b : ι → ℝ)
    (hb : ∀ i, 0 < b i) (c : ℕ) (hc : Fintype.card ι ≤ c) (μ : FiniteLaw (Finset ι)) :
    PayOnceEquilibrium n c b μ ↔ μ = FiniteLaw.dirac Finset.univ := by
  constructor
  · intro h
    exact (payOnce_best_response_small_list n hn b hb c hc μ μ).mp h
  · intro h
    have h' := (payOnce_best_response_small_list n hn b hb c hc μ μ).mpr h
    exact h'

theorem exists_equilibrium_any (n : ℕ) (hn : 2 ≤ n) (b : ι → ℝ) (hb : ∀ i, 0 < b i)
    (c : ℕ) : ∃ μ : FiniteLaw (Finset ι), PayOnceEquilibrium n c b μ := by
  by_cases hc : c ≤ Fintype.card ι
  · obtain ⟨μ, hμ, _⟩ := exists_equilibrium n hn b hb c hc
    exact ⟨μ, hμ⟩
  · exact ⟨_, (payOnceEquilibrium_small_list_iff n (by omega) b hb c (by omega) _).mpr rfl⟩

theorem equilibrium_marginal_unique (n : ℕ) (hn : 2 ≤ n) (b : ι → ℝ) (hb : ∀ i, 0 < b i)
    (c : ℕ) (μ ν : FiniteLaw (Finset ι))
    (hμ : PayOnceEquilibrium n c b μ) (hν : PayOnceEquilibrium n c b ν) :
    marginal μ = marginal ν := by
  by_cases hc : c ≤ Fintype.card ι
  · obtain ⟨_, hμs, L, hL, hμt⟩ := equilibrium_structure n hn b hb c hc μ hμ
    obtain ⟨_, hνs, L', hL', hνt⟩ := equilibrium_structure n hn b hb c hc ν hν
    exact pay_once_unique n hn b hb (marginal μ) (marginal ν) L L' c
      (marginal_nonneg μ) (marginal_le_one μ) hμs (marginal_nonneg ν) (marginal_le_one ν) hνs
      (le_of_lt hL) (le_of_lt hL') hμt hνt
  · have h1 := (payOnceEquilibrium_small_list_iff n (by omega) b hb c (by omega) μ).mp hμ
    have h2 := (payOnceEquilibrium_small_list_iff n (by omega) b hb c (by omega) ν).mp hν
    rw [h1, h2]

theorem H_strictAntiOn (n : ℕ) (hn : 2 ≤ n) : StrictAntiOn (PayOnce.H n) (Set.Icc 0 1) :=
  fun _ _ _ hy hxy => PayOnce.H_strict n hn _ _ hxy hy.2

noncomputable def Hinv (n : ℕ) (y : ℝ) : ℝ :=
  Function.invFunOn (PayOnce.H n) (Set.Icc 0 1) y

theorem Hinv_spec (n : ℕ) (hn : 1 ≤ n) (y : ℝ) (hy1 : 1 / (n : ℝ) ≤ y) (hy2 : y ≤ 1) :
    Hinv n y ∈ Set.Icc (0 : ℝ) 1 ∧ PayOnce.H n (Hinv n y) = y := by
  apply Function.invFunOn_pos
  have hmem : y ∈ Set.Icc (PayOnce.H n 1) (PayOnce.H n 0) := by
    rw [PayOnce.H_one n (by omega), PayOnce.H_zero n (by omega)]
    exact ⟨hy1, hy2⟩
  obtain ⟨p, hp, hpy⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1)
    (PayOnce.continuous_H n).continuousOn hmem
  exact ⟨p, hp, hpy⟩

theorem Hinv_H (n : ℕ) (hn : 2 ≤ n) (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    Hinv n (PayOnce.H n p) = p := by
  have hb := PayOnce.H_bounds n (by omega) p hp.1 hp.2
  have hs := Hinv_spec n (by omega) (PayOnce.H n p) hb.1 hb.2
  exact (H_strictAntiOn n hn).injOn hs.1 hp hs.2

noncomputable def kernel (n : ℕ) (b L : ℝ) : ℝ :=
  if b ≤ L then 0 else if b < (n : ℝ) * L then Hinv n (L / b) else 1

theorem kernel_of_le (n : ℕ) {b L : ℝ} (h : b ≤ L) : kernel n b L = 0 := if_pos h

theorem kernel_of_mid (n : ℕ) {b L : ℝ} (h1 : L < b) (h2 : b < (n : ℝ) * L) :
    kernel n b L = Hinv n (L / b) := by
  unfold kernel
  rw [if_neg (not_le.mpr h1), if_pos h2]

theorem kernel_of_ge (n : ℕ) (hn : 2 ≤ n) {b L : ℝ} (hL : 0 < L) (h : (n : ℝ) * L ≤ b) :
    kernel n b L = 1 := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  unfold kernel
  rw [if_neg (by nlinarith), if_neg (not_lt.mpr h)]

theorem scalarThreshold_kernel (n : ℕ) (hn : 2 ≤ n) {b L : ℝ} (hb : 0 < b) (hL : 0 < L) :
    PayOnce.ScalarThreshold n b L (kernel n b L) := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  by_cases h1 : b ≤ L
  · rw [kernel_of_le n h1]
    refine ⟨le_rfl, by norm_num, fun _ => ?_, fun h => by norm_num at h, fun h => by
      norm_num at h⟩
    simpa [PayOnce.H_zero n hn0] using h1
  by_cases h2 : b < (n : ℝ) * L
  · push Not at h1
    rw [kernel_of_mid n h1 h2]
    have hy1 : 1 / (n : ℝ) ≤ L / b := by
      rw [div_le_div_iff₀ hnR hb]
      linarith
    have hy2 : L / b ≤ 1 := (div_le_one hb).mpr (le_of_lt h1)
    obtain ⟨hmem, hH⟩ := Hinv_spec n (by omega) (L / b) hy1 hy2
    have he : b * PayOnce.H n (Hinv n (L / b)) = L := by
      rw [hH]
      field_simp
    exact ⟨hmem.1, hmem.2, fun _ => le_of_eq he, fun _ => le_of_eq he.symm, fun _ _ => he⟩
  · push Not at h2
    rw [kernel_of_ge n hn hL h2]
    refine ⟨by norm_num, le_rfl, fun h => by norm_num at h, fun _ => ?_, fun _ h => by
      norm_num at h⟩
    rw [PayOnce.H_one n hn0]
    rw [mul_one_div, le_div_iff₀ hnR]
    linarith

theorem kernel_nonneg (n : ℕ) (hn : 2 ≤ n) {b L : ℝ} (hb : 0 < b) (hL : 0 < L) :
    0 ≤ kernel n b L :=
  (scalarThreshold_kernel n hn hb hL).1

theorem kernel_le_one (n : ℕ) (hn : 2 ≤ n) {b L : ℝ} (hb : 0 < b) (hL : 0 < L) :
    kernel n b L ≤ 1 :=
  (scalarThreshold_kernel n hn hb hL).2.1

theorem eq_kernel_of_scalarThreshold (n : ℕ) (hn : 2 ≤ n) {b L p : ℝ} (hb : 0 < b)
    (hL : 0 < L) (h : PayOnce.ScalarThreshold n b L p) : p = kernel n b L := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hd := PayOnce.scalar_difference_bound n hn b hb L L p (kernel n b L) h
    (scalarThreshold_kernel n hn hb hL)
  rw [sub_self, abs_zero] at hd
  have hc : 0 < b / n := div_pos hb hnR
  have habs : |p - kernel n b L| ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have := mul_pos hc hpos
    linarith
  have := abs_nonpos_iff.mp habs
  linarith

omit [Fintype ι] [DecidableEq ι] in

theorem threshold_iff_kernel (n : ℕ) (hn : 2 ≤ n) (b : ι → ℝ) (hb : ∀ i, 0 < b i)
    (L : ℝ) (hL : 0 < L) (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) :
    Threshold p (fun i => b i * PayOnce.H n (p i)) L ↔ ∀ i, p i = kernel n (b i) L := by
  constructor
  · intro ht i
    exact eq_kernel_of_scalarThreshold n hn (hb i) hL
      ⟨hp0 i, hp1 i, ht.1 i, ht.2.1 i, ht.2.2 i⟩
  · intro hk
    have hs : ∀ i, PayOnce.ScalarThreshold n (b i) L (p i) := by
      intro i
      rw [hk i]
      exact scalarThreshold_kernel n hn (hb i) hL
    exact ⟨fun i => (hs i).2.2.1, fun i => (hs i).2.2.2.1, fun i => (hs i).2.2.2.2⟩

theorem equilibrium_kernel (n : ℕ) (hn : 2 ≤ n) (b : ι → ℝ) (hb : ∀ i, 0 < b i)
    (c : ℕ) (hc : c ≤ Fintype.card ι) (μ : FiniteLaw (Finset ι))
    (hμ : PayOnceEquilibrium n c b μ) :
    ∃ L, 0 < L ∧ (∀ i, marginal μ i = kernel n (b i) L) ∧ ∑ i, kernel n (b i) L = c := by
  obtain ⟨_, hsum, L, hL, ht⟩ := equilibrium_structure n hn b hb c hc μ hμ
  have hk := (threshold_iff_kernel n hn b hb L hL (marginal μ) (marginal_nonneg μ)
    (marginal_le_one μ)).mp ht
  refine ⟨L, hL, hk, ?_⟩
  simp_rw [← hk]
  exact hsum

theorem equilibrium_eq_kernel_of_root (n : ℕ) (hn : 2 ≤ n) (b : ι → ℝ) (hb : ∀ i, 0 < b i)
    (c : ℕ) (L : ℝ) (hL : 0 < L) (hroot : ∑ i, kernel n (b i) L = c)
    (μ : FiniteLaw (Finset ι)) (hμ : PayOnceEquilibrium n c b μ) (i : ι) :
    marginal μ i = kernel n (b i) L := by
  have hc : c ≤ Fintype.card ι := by
    have h : (∑ i, kernel n (b i) L) ≤ ∑ _i : ι, (1 : ℝ) :=
      Finset.sum_le_sum (fun i _ => kernel_le_one n hn (hb i) hL)
    rw [hroot] at h
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
    exact_mod_cast h
  obtain ⟨_, hsum, L', hL', ht⟩ := equilibrium_structure n hn b hb c hc μ hμ
  have hkt := (threshold_iff_kernel n hn b hb L hL (fun i => kernel n (b i) L)
    (fun i => kernel_nonneg n hn (hb i) hL) (fun i => kernel_le_one n hn (hb i) hL)).mpr
    (fun i => rfl)
  have he := pay_once_unique n hn b hb (marginal μ) (fun i => kernel n (b i) L) L' L c
    (marginal_nonneg μ) (marginal_le_one μ) hsum (fun i => kernel_nonneg n hn (hb i) hL)
    (fun i => kernel_le_one n hn (hb i) hL) hroot (le_of_lt hL') (le_of_lt hL) ht hkt
  exact congrFun he i

def admissiblePrices (n : ℕ) (b p : ι → ℝ) : Set ℝ :=
  {L | 0 < L ∧ ∀ i, p i = kernel n (b i) L}

omit [Fintype ι] [DecidableEq ι] in

theorem admissiblePrices_interior (n : ℕ) (hn : 2 ≤ n) (b : ι → ℝ) (hb : ∀ i, 0 < b i)
    (p : ι → ℝ) (i : ι) (hi0 : 0 < p i) (hi1 : p i < 1) (L : ℝ)
    (hL : L ∈ admissiblePrices n b p) : L = b i * PayOnce.H n (p i) := by
  obtain ⟨hL0, hk⟩ := hL
  have hp0 : ∀ j, 0 ≤ p j := fun j => by rw [hk j]; exact kernel_nonneg n hn (hb j) hL0
  have hp1 : ∀ j, p j ≤ 1 := fun j => by rw [hk j]; exact kernel_le_one n hn (hb j) hL0
  have ht := (threshold_iff_kernel n hn b hb L hL0 p hp0 hp1).mpr hk
  exact (ht.2.2 i hi0 hi1).symm

omit [Fintype ι] [DecidableEq ι] in
theorem admissiblePrices_subsingleton_of_interior (n : ℕ) (hn : 2 ≤ n) (b : ι → ℝ)
    (hb : ∀ i, 0 < b i) (p : ι → ℝ) (i : ι) (hi0 : 0 < p i) (hi1 : p i < 1) :
    (admissiblePrices n b p).Subsingleton := by
  intro L hL L' hL'
  rw [admissiblePrices_interior n hn b hb p i hi0 hi1 L hL,
    admissiblePrices_interior n hn b hb p i hi0 hi1 L' hL']

theorem equilibrium_price_unique_of_interior (n : ℕ) (hn : 2 ≤ n) (b : ι → ℝ)
    (hb : ∀ i, 0 < b i) (c : ℕ) (hc : c ≤ Fintype.card ι) (μ : FiniteLaw (Finset ι))
    (hμ : PayOnceEquilibrium n c b μ) (i : ι) (hi0 : 0 < marginal μ i)
    (hi1 : marginal μ i < 1) :
    ∃! L, 0 < L ∧ ∀ j, marginal μ j = kernel n (b j) L := by
  obtain ⟨L, hL, hk, _⟩ := equilibrium_kernel n hn b hb c hc μ hμ
  exact ⟨L, ⟨hL, hk⟩, fun L' hL' =>
    admissiblePrices_subsingleton_of_interior n hn b hb (marginal μ) i hi0 hi1 hL' ⟨hL, hk⟩⟩

theorem kernel_eq_zero_iff (n : ℕ) (hn : 2 ≤ n) {b L : ℝ} (hb : 0 < b) (hL : 0 < L) :
    kernel n b L = 0 ↔ b ≤ L := by
  constructor
  · intro h
    have hs := (scalarThreshold_kernel n hn hb hL).2.2.1 h
    rw [h, PayOnce.H_zero n (by omega), mul_one] at hs
    exact hs
  · exact kernel_of_le n

theorem kernel_eq_one_iff (n : ℕ) (hn : 2 ≤ n) {b L : ℝ} (hb : 0 < b) (hL : 0 < L) :
    kernel n b L = 1 ↔ L ≤ b / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  constructor
  · intro h
    have hs := (scalarThreshold_kernel n hn hb hL).2.2.2.1 h
    rw [h, PayOnce.H_one n (by omega), mul_one_div] at hs
    exact hs
  · intro h
    apply kernel_of_ge n hn hL
    rw [le_div_iff₀ hnR] at h
    linarith

omit [Fintype ι] [DecidableEq ι] in

theorem admissiblePrices_of_endpoints (n : ℕ) (hn : 2 ≤ n) (b : ι → ℝ) (hb : ∀ i, 0 < b i)
    (p : ι → ℝ) (hend : ∀ i, p i = 0 ∨ p i = 1) :
    admissiblePrices n b p =
      {L | 0 < L ∧ (∀ i, p i = 0 → b i ≤ L) ∧ (∀ i, p i = 1 → L ≤ b i / n)} := by
  ext L
  constructor
  · rintro ⟨hL, hk⟩
    refine ⟨hL, fun i hi => ?_, fun i hi => ?_⟩
    · exact (kernel_eq_zero_iff n hn (hb i) hL).mp ((hk i).symm.trans hi)
    · exact (kernel_eq_one_iff n hn (hb i) hL).mp ((hk i).symm.trans hi)
  · rintro ⟨hL, h0, h1⟩
    refine ⟨hL, fun i => ?_⟩
    rcases hend i with hi | hi
    · rw [hi, (kernel_eq_zero_iff n hn (hb i) hL).mpr (h0 i hi)]
    · rw [hi, (kernel_eq_one_iff n hn (hb i) hL).mpr (h1 i hi)]

omit [DecidableEq ι] in

theorem admissiblePrices_eq_Icc (n : ℕ) (hn : 2 ≤ n) (b : ι → ℝ) (hb : ∀ i, 0 < b i)
    (p : ι → ℝ) (hend : ∀ i, p i = 0 ∨ p i = 1)
    (hz : (Finset.univ.filter (fun i => p i = 0)).Nonempty)
    (ho : (Finset.univ.filter (fun i => p i = 1)).Nonempty) :
    admissiblePrices n b p =
      Set.Icc ((Finset.univ.filter (fun i => p i = 0)).sup' hz b)
        ((Finset.univ.filter (fun i => p i = 1)).inf' ho (fun i => b i / n)) := by
  rw [admissiblePrices_of_endpoints n hn b hb p hend]
  ext L
  simp only [Set.mem_setOf_eq, Set.mem_Icc, Finset.sup'_le_iff, Finset.le_inf'_iff,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, h0, h1⟩
    exact ⟨h0, h1⟩
  · rintro ⟨h0, h1⟩
    obtain ⟨k, hk⟩ := hz
    have hk0 : p k = 0 := (Finset.mem_filter.mp hk).2
    exact ⟨lt_of_lt_of_le (hb k) (h0 k hk0), h0, h1⟩

theorem equilibrium_endpoint_classes (n : ℕ) (hn : 2 ≤ n) (b : ι → ℝ) (hb : ∀ i, 0 < b i)
    (c : ℕ) (hc1 : 1 ≤ c) (hc : c < Fintype.card ι) (μ : FiniteLaw (Finset ι))
    (hμ : PayOnceEquilibrium n c b μ) (hend : ∀ i, marginal μ i = 0 ∨ marginal μ i = 1) :
    (Finset.univ.filter (fun i => marginal μ i = 0)).Nonempty ∧
      (Finset.univ.filter (fun i => marginal μ i = 1)).Nonempty := by
  obtain ⟨_, hsum, _⟩ := equilibrium_structure n hn b hb c (le_of_lt hc) μ hμ
  constructor
  · by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hne
    have hall : ∀ i, marginal μ i = 1 := fun i =>
      (hend i).resolve_left (hne (Finset.mem_univ i))
    simp only [hall, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hsum
    have : Fintype.card ι = c := by exact_mod_cast hsum
    omega
  · by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hne
    have hall : ∀ i, marginal μ i = 0 := fun i =>
      (hend i).resolve_right (hne (Finset.mem_univ i))
    simp only [hall, Finset.sum_const_zero] at hsum
    have : c = 0 := by exact_mod_cast hsum.symm
    omega

theorem equilibrium_admissiblePrices_Icc (n : ℕ) (hn : 2 ≤ n) (b : ι → ℝ)
    (hb : ∀ i, 0 < b i) (c : ℕ) (hc1 : 1 ≤ c) (hc : c < Fintype.card ι)
    (μ : FiniteLaw (Finset ι)) (hμ : PayOnceEquilibrium n c b μ)
    (hend : ∀ i, marginal μ i = 0 ∨ marginal μ i = 1) :
    ∃ (hz : (Finset.univ.filter (fun i => marginal μ i = 0)).Nonempty)
      (ho : (Finset.univ.filter (fun i => marginal μ i = 1)).Nonempty),
      admissiblePrices n b (marginal μ) =
        Set.Icc ((Finset.univ.filter (fun i => marginal μ i = 0)).sup' hz b)
          ((Finset.univ.filter (fun i => marginal μ i = 1)).inf' ho (fun i => b i / n)) := by
  obtain ⟨hz, ho⟩ := equilibrium_endpoint_classes n hn b hb c hc1 hc μ hμ hend
  exact ⟨hz, ho, admissiblePrices_eq_Icc n hn b hb (marginal μ) hend hz ho⟩

noncomputable def intervalBids : Fin 2 → ℝ := ![4, 1]

theorem interval_example_marginal (μ : FiniteLaw (Finset (Fin 2)))
    (hμ : PayOnceEquilibrium 2 1 intervalBids μ) : marginal μ = ![1, 0] := by
  have hb : ∀ i, 0 < intervalBids i := by
    intro i
    fin_cases i <;> norm_num [intervalBids]
  have k0 : kernel 2 (intervalBids 0) (3 / 2) = 1 :=
    kernel_of_ge 2 le_rfl (by norm_num) (by norm_num [intervalBids])
  have k1 : kernel 2 (intervalBids 1) (3 / 2) = 0 :=
    kernel_of_le 2 (by norm_num [intervalBids])
  have hroot : ∑ i, kernel 2 (intervalBids i) (3 / 2) = (1 : ℕ) := by
    rw [Fin.sum_univ_two, k0, k1]
    norm_num
  funext i
  rw [equilibrium_eq_kernel_of_root 2 le_rfl intervalBids hb 1 (3 / 2) (by norm_num) hroot μ hμ i]
  fin_cases i
  · simpa using k0
  · simpa using k1

theorem interval_example_prices :
    admissiblePrices 2 intervalBids ![1, 0] = Set.Icc 1 2 := by
  have hb : ∀ i, 0 < intervalBids i := by
    intro i
    fin_cases i <;> norm_num [intervalBids]
  rw [admissiblePrices_of_endpoints 2 le_rfl intervalBids hb ![1, 0]
    (by intro i; fin_cases i <;> simp)]
  ext L
  simp only [Set.mem_setOf_eq, Set.mem_Icc, Fin.forall_fin_two]
  norm_num [intervalBids]
  intro h1 _
  linarith

theorem interval_example_exists : ∃ μ : FiniteLaw (Finset (Fin 2)),
    PayOnceEquilibrium 2 1 intervalBids μ :=
  exists_equilibrium_any 2 le_rfl intervalBids
    (by intro i; fin_cases i <;> norm_num [intervalBids]) 1

theorem interval_example : ∃ μ : FiniteLaw (Finset (Fin 2)),
    PayOnceEquilibrium 2 1 intervalBids μ ∧
      admissiblePrices 2 intervalBids (marginal μ) = Set.Icc 1 2 := by
  obtain ⟨μ, hμ⟩ := interval_example_exists
  exact ⟨μ, hμ, by rw [interval_example_marginal μ hμ]; exact interval_example_prices⟩

theorem equilibrium_count_binomial (n : ℕ) (hn : 2 ≤ n) (b : ι → ℝ) (hb : ∀ i, 0 < b i)
    (c : ℕ) (L : ℝ) (hL : 0 < L) (hroot : ∑ i, kernel n (b i) L = c)
    (μ : FiniteLaw (Finset ι)) (hμ : PayOnceEquilibrium n c b μ) (i : ι) :
    (iid μ n).map (includersCount i) =
      IndependentCounts.binomial n (kernel n (b i) L) (kernel_nonneg n hn (hb i) hL)
        (kernel_le_one n hn (hb i) hL) := by
  rw [iid_includers_law]
  exact binomial_congr n (equilibrium_eq_kernel_of_root n hn b hb c L hL hroot μ hμ i) _ _ _ _

end CommonList
end FCAppendix
