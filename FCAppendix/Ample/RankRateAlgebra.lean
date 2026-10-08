import FCAppendix.Ample.RankFiniteIdentities
import FCAppendix.Ample.CongestionRate

noncomputable section
namespace FCAppendix.Ample
open MeasureTheory Set Filter Topology Real
open scoped BigOperators

theorem hyperPGF_first_route {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) (z : ℝ) :
    hyperPGF n k 1 z = 1 + (k : ℝ) / n * (z-1) := by
  unfold hyperPGF hyperNum
  rw [Finset.Nat.sum_antidiagonal_succ]
  simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton,
    Nat.choose_one_right, Nat.choose_zero_right, Nat.cast_one,
    pow_zero, pow_one, zero_add, mul_one, one_mul]
  rw [Nat.cast_sub hk]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  ring

theorem contactGain_first_member {n k j : ℕ}
    (hk : k ∈ Finset.Icc 1 n) (hj : j ∈ Finset.Icc 1 n)
    {θ : ℝ} (hθ : 0 ≤ θ) :
    (k : ℝ) / n * (exp θ-1) ≤ contactGain n k j θ := by
  have hkn := (Finset.mem_Icc.mp hk).2
  have hn : 0 < n := by
    have := (Finset.mem_Icc.mp hk).1
    omega
  have hg := hyperPGF_mono n k hkn (Real.one_le_exp hθ)
    (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2
  rw [hyperPGF_first_route hn hkn] at hg
  unfold contactGain
  linarith

theorem weighted_tail_gap {n k : ℕ} (hk : k ∈ Finset.Icc 1 n)
    {p q : ℕ → ℝ} {d θ : ℝ}
    (hpq : ∀ j ∈ Finset.Icc 1 n, 0 ≤ p j-q j)
    (hsum : (∑ j ∈ Finset.Icc 1 n, (p j-q j)) = d) (hθ : 0 ≤ θ) :
    d * ((k : ℝ)/n*(exp θ-1)) ≤ rivalMGF n k p θ-rivalMGF n k q θ := by
  have hh : (∑ j ∈ Finset.Icc 1 n,
      (p j-q j)*((k : ℝ)/n*(exp θ-1))) ≤
      ∑ j ∈ Finset.Icc 1 n, (p j-q j)*contactGain n k j θ := by
    exact Finset.sum_le_sum (fun j hj =>
      mul_le_mul_of_nonneg_left (contactGain_first_member hk hj hθ) (hpq j hj))
  rw [← Finset.sum_mul, hsum] at hh
  convert hh using 1
  simp only [rivalMGF, sub_mul, Finset.sum_sub_distrib]
  ring

theorem rival_objective_le_rate_of_interior {n k : ℕ}
    (hk1 : 1 ≤ k) (hk : k ≤ n) {p : ℕ → ℝ} (hp : ValidLaw n p)
    {ρ : ℝ} (hslack : contactMarginal n p < ρ)
    (htop : ∃ j ∈ Finset.Icc 1 n, 0 < p j ∧ (k : ℝ)*ρ < (min k j : ℕ))
    (θ : ℝ) : rivalObjective n ρ k p θ ≤ rivalRate n ρ k p := by
  obtain ⟨t, ht, hmean, heq⟩ :=
    FiniteCramer.optimizer (contactLaw_interior hk1 hk hp hslack htop)
  have hb := FiniteCramer.objective_le_at_mean
    (contactLaw n p hp) (SimultaneousCongestion.count (selected n k)) hmean θ
  rw [← heq, contactLaw_rate hk] at hb
  simpa only [FiniteCramer.objective, contactLaw_cgf, card_selected hk,
    rivalObjective] using hb

theorem rivalMGF_tendsto_weights {α : Type*} {l : Filter α} {n k : ℕ}
    {p : α → ℕ → ℝ} {q : ℕ → ℝ}
    (hp : ∀ j ∈ Finset.Icc 1 n, Tendsto (fun a => p a j) l (𝓝 (q j))) (θ : ℝ) :
    Tendsto (fun a => rivalMGF n k (p a) θ) l (𝓝 (rivalMGF n k q θ)) := by
  exact tendsto_const_nhds.add
    (tendsto_finsetSum _ (fun j hj => (hp j hj).mul_const _))

end FCAppendix.Ample

namespace FCAppendix.Bayes.RankLimit
open MeasureTheory Set Filter Topology Real
open scoped BigOperators
open Ample Ample.RankMeasureTools

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed] {M C : ℕ → ℕ}
    {Γ : ∀ t, FiniteGame (M t) n (C t) Seed} {pi : ℕ → ℝ} {h : ℝ}
    {nu : ℕ → Measure ℝ} (hr : RankLimit Γ pi h nu)

include hr

theorem objective_strict {ρ : ℝ} {k : ℕ} (hk : k ∈ Finset.Icc 1 n)
    {u v θ : ℝ} (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ h) (hθ : 0 < θ) :
    rivalObjective n ρ k (rankTail nu h u) θ <
      rivalObjective n ρ k (rankTail nu h v) θ := by
  have hm := hr.interval_mass hu huv.le hv
  have hg := weighted_tail_gap hk hm.1 hm.2 hθ.le
  have hk0 : (0 : ℝ) < k := by
    exact_mod_cast (show 0 < k from lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hk).1)
  have hn0 : (0 : ℝ) < n := hk0.trans_le (by exact_mod_cast (Finset.mem_Icc.mp hk).2)
  have hpos : 0 < (v-u)*((k : ℝ)/n*(exp θ-1)) :=
    mul_pos (sub_pos.mpr huv) (mul_pos (div_pos hk0 hn0)
      (sub_pos.mpr (Real.one_lt_exp_iff.mpr hθ)))
  have hmgf : rivalMGF n k (rankTail nu h v) θ < rivalMGF n k (rankTail nu h u) θ := by
    linarith
  have hmgf0 : 0 < rivalMGF n k (rankTail nu h v) θ :=
    zero_lt_one.trans_le (one_le_rivalMGF (Finset.mem_Icc.mp hk).2
      (fun _ _ => measureReal_nonneg) hθ.le)
  have hl := Real.log_lt_log hmgf0 hmgf
  unfold rivalObjective
  linarith

theorem mean_tail_lt {ρ : ℝ} (hn : 0 < n)
    (hmean : (∑ j ∈ Finset.Icc 1 n, (j : ℝ)*pi j) < n*ρ) (u : ℝ) :
    contactMarginal n (rankTail nu h u) < ρ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  apply (div_lt_iff₀ hn0).mpr
  calc
    (∑ j ∈ Finset.Icc 1 n, rankTail nu h u j*(j : ℝ))
        ≤ ∑ j ∈ Finset.Icc 1 n, (j : ℝ)*pi j := by
          apply Finset.sum_le_sum
          intro j hj
          simpa only [mul_comm] using mul_le_mul_of_nonneg_right
            (hr.tail_le_mass hj u) (Nat.cast_nonneg j)
    _ < ρ*n := by simpa only [mul_comm] using hmean

omit hr in

theorem own_tail_support_guard (_hr : RankLimit Γ pi h nu) {ρ : ℝ} (hρ : ρ < 1) {k : ℕ}
    (hk : k ∈ Finset.Icc 1 n) {u : ℝ} (hu : 0 < rankTail nu h u k) :
    ∃ j ∈ Finset.Icc 1 n, 0 < rankTail nu h u j ∧ (k : ℝ)*ρ < (min k j : ℕ) := by
  refine ⟨k, hk, hu, ?_⟩
  rw [min_self]
  have hk0 : (0 : ℝ) < k := by exact_mod_cast
    (show 0 < k from lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hk).1)
  simpa only [mul_one] using mul_lt_mul_of_pos_left hρ hk0

theorem used_optimizer {ρ : ℝ} (hh : h ≤ 1) (hρ : ρ < 1)
    (hmean : (∑ j ∈ Finset.Icc 1 n, (j : ℝ)*pi j) < n*ρ)
    {k : ℕ} (hk : k ∈ Finset.Icc 1 n) :
    ∀ᵐ u ∂nu k, 0 < u ∧ u < h ∧ 0 < rankTail nu h u k ∧
      ∃ θ > 0, rivalObjective n ρ k (rankTail nu h u) θ = rivalRate n ρ k (rankTail nu h u) ∧
        ∀ s : ℝ, rivalObjective n ρ k (rankTail nu h u) s ≤ rivalRate n ρ k (rankTail nu h u) := by
  have hn : 0 < n := lt_of_lt_of_le
    (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hk).1) (Finset.mem_Icc.mp hk).2
  filter_upwards [hr.used_tail_positive hk] with u hu
  have hsl := hr.mean_tail_lt hn hmean u
  have htop := hr.own_tail_support_guard hρ hk hu.2.2
  obtain ⟨θ, hθ, _, heq, _⟩ := rival_optimizer_of_law (Finset.mem_Icc.mp hk).1
    (Finset.mem_Icc.mp hk).2 (hr.valid_tail hh u) hsl htop
  exact ⟨hu.1, hu.2.1, hu.2.2, θ, hθ, heq,
    rival_objective_le_rate_of_interior (Finset.mem_Icc.mp hk).1
      (Finset.mem_Icc.mp hk).2 (hr.valid_tail hh u) hsl htop⟩

theorem chernoff_gap_of_rate_ge {ρ J : ℝ} (hh : h ≤ 1) (hρ : ρ < 1)
    (hmean : (∑ j ∈ Finset.Icc 1 n, (j : ℝ)*pi j) < n*ρ)
    {k : ℕ} (hk : k ∈ Finset.Icc 1 n)
    (hge : ∀ᵐ u ∂nu k, J ≤ rivalRate n ρ k (rankTail nu h u)) :
    ∀ᵐ u ∂nu k, ∃ θ ≥ 0, J < rivalObjective n ρ k (rankTail nu h u) θ := by
  let P : ℝ → Prop := fun u => 0 < u ∧ u < h ∧ 0 < rankTail nu h u k ∧
    ∃ θ > 0, rivalObjective n ρ k (rankTail nu h u) θ = rivalRate n ρ k (rankTail nu h u) ∧
      ∀ s : ℝ, rivalObjective n ρ k (rankTail nu h u) s ≤ rivalRate n ρ k (rankTail nu h u)
  have hP : ∀ᵐ u ∂nu k, P u := hr.used_optimizer hh hρ hmean hk
  have hstrict : ∀ u, P u → ∀ v, P v → u < v →
      rivalRate n ρ k (rankTail nu h u) < rivalRate n ρ k (rankTail nu h v) := by
    intro u hu v hv huv
    obtain ⟨θ, hθ, heq, _⟩ := hu.2.2.2
    obtain ⟨_, _, _, hvmax⟩ := hv.2.2.2
    rw [← heq]
    exact (hr.objective_strict hk hu.1.le huv hv.2.1.le hθ).trans_le (hvmax θ)
  have hgt := strictOn_gt_ae (nu k) (hr.atomless hk) hP hge hstrict
  filter_upwards [hP, hgt] with u hu hgt
  obtain ⟨θ, hθ, heq, _⟩ := hu.2.2.2
  refine ⟨θ, hθ.le, ?_⟩
  simpa only [heq] using hgt

end FCAppendix.Bayes.RankLimit
