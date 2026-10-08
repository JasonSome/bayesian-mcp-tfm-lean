import FCAppendix.Proposer.CommonListGame
import FCAppendix.Probability.BinomialTails

namespace FCAppendix
namespace SimultaneousCongestion

open scoped BigOperators
open Finset CommonList Proposer

section General

variable {Ω : Type*} [Fintype Ω]

theorem exists_mass_pos (μ : FiniteLaw Ω) : ∃ ω, 0 < μ.mass ω := by
  by_contra h
  simp only [not_exists, not_lt] at h
  have h1 : ∑ ω, μ.mass ω ≤ 0 := Finset.sum_nonpos (fun ω _ => h ω)
  linarith [μ.total]

theorem expect_pos (μ : FiniteLaw Ω) {f : Ω → ℝ} (hf : ∀ ω, 0 < f ω) : 0 < μ.expect f := by
  obtain ⟨ω, hω⟩ := exists_mass_pos μ
  unfold FiniteLaw.expect
  exact Finset.sum_pos' (fun x _ => mul_nonneg (μ.nonneg x) (hf x).le)
    ⟨ω, Finset.mem_univ _, mul_pos hω (hf ω)⟩

noncomputable def tilt (μ : FiniteLaw Ω) (g : Ω → ℝ) : FiniteLaw Ω where
  mass ω := μ.mass ω * Real.exp (g ω) / μ.expect (fun ω => Real.exp (g ω))
  nonneg ω := div_nonneg (mul_nonneg (μ.nonneg ω) (Real.exp_pos _).le)
    (expect_pos μ (fun ω => Real.exp_pos (g ω))).le
  total := by
    rw [← Finset.sum_div]
    exact div_self (expect_pos μ (fun ω => Real.exp_pos (g ω))).ne'

theorem tilt_mass (μ : FiniteLaw Ω) (g : Ω → ℝ) (ω : Ω) :
    (tilt μ g).mass ω = μ.mass ω * Real.exp (g ω) / μ.expect (fun ω => Real.exp (g ω)) := rfl

theorem expect_tilt (μ : FiniteLaw Ω) (g f : Ω → ℝ) :
    (tilt μ g).expect f =
      μ.expect (fun ω => f ω * Real.exp (g ω)) / μ.expect (fun ω => Real.exp (g ω)) := by
  simp only [FiniteLaw.expect, tilt_mass]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  ring

theorem expect_iid_prod (μ : FiniteLaw Ω) (N : ℕ) (f : Ω → ℝ) :
    (iid μ N).expect (fun T => ∏ i, f (T i)) = (μ.expect f) ^ N := by
  classical
  unfold FiniteLaw.expect
  simp only [iid]
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : Fin N) ω => μ.mass ω * f ω)]
  simp

theorem expect_iid_eq_tilt (μ : FiniteLaw Ω) (g : Ω → ℝ) (N : ℕ)
    (F : (Fin N → Ω) → ℝ) :
    (iid μ N).expect F = (μ.expect (fun ω => Real.exp (g ω))) ^ N *
      (iid (tilt μ g) N).expect (fun T => F T * Real.exp (-(∑ i, g (T i)))) := by
  have hZ : μ.expect (fun ω => Real.exp (g ω)) ≠ 0 :=
    (expect_pos μ (fun ω => Real.exp_pos (g ω))).ne'
  unfold FiniteLaw.expect
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  simp only [iid, tilt_mass]
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Real.exp_neg, Real.exp_sum]
  have hE : ∏ i, Real.exp (g (T i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => (Real.exp_pos _).ne')
  field_simp
  rfl

theorem prob_exists_le (μ : FiniteLaw Ω) {κ : Type*} (s : Finset κ) (E : κ → Ω → Prop) :
    μ.prob (fun ω => ∃ i ∈ s, E i ω) ≤ ∑ i ∈ s, μ.prob (E i) := by
  classical
  rw [FiniteLaw.prob_eq_expect]
  simp_rw [FiniteLaw.prob_eq_expect]
  rw [← FiniteLaw.expect_finset_sum]
  apply μ.expect_mono
  intro ω
  by_cases h : ∃ i ∈ s, E i ω
  · rw [if_pos h]
    obtain ⟨i, hi, hE⟩ := h
    have := Finset.single_le_sum (f := fun i => if E i ω then (1 : ℝ) else 0)
      (fun j _ => by split <;> norm_num) hi
    simpa [hE] using this
  · rw [if_neg h]
    exact Finset.sum_nonneg (fun j _ => by split <;> norm_num)

end General

variable {ι : Type*} [DecidableEq ι]

def selected (K S : Finset ι) : ℕ := (S ∩ K).card

theorem selected_le (K S : Finset ι) : selected K S ≤ K.card :=
  Finset.card_le_card Finset.inter_subset_right

theorem selected_eq_sum (K S : Finset ι) :
    (selected K S : ℝ) = ∑ s ∈ K, if s ∈ S then (1 : ℝ) else 0 := by
  rw [Finset.sum_boole]
  unfold selected
  congr 2
  ext x
  simp [and_comm]

theorem includers_cast {N : ℕ} (s : ι) (T : Fin N → Finset ι) :
    (includers s T : ℝ) = ∑ i, if s ∈ T i then (1 : ℝ) else 0 := by
  unfold includers
  push_cast
  rfl

theorem sum_selected_eq {N : ℕ} (K : Finset ι) (T : Fin N → Finset ι) :
    (∑ i, (selected K (T i) : ℝ)) = ∑ s ∈ K, (includers s T : ℝ) := by
  simp_rw [selected_eq_sum, includers_cast]
  exact Finset.sum_comm

variable [Fintype ι]

noncomputable def mgf (μ : FiniteLaw (Finset ι)) (K : Finset ι) (θ : ℝ) : ℝ :=
  μ.expect (fun S => Real.exp (θ * selected K S))

theorem mgf_pos (μ : FiniteLaw (Finset ι)) (K : Finset ι) (θ : ℝ) : 0 < mgf μ K θ :=
  expect_pos μ (fun _ => Real.exp_pos _)

def Congested (K : Finset ι) (c : ℕ) {N : ℕ} (T : Fin N → Finset ι) : Prop :=
  ∀ s ∈ K, c ≤ includers s T

noncomputable def congestionProb (μ : FiniteLaw (Finset ι)) (K : Finset ι) (N c : ℕ) : ℝ :=
  (iid μ N).prob (Congested K c)

theorem congestionProb_nonneg (μ : FiniteLaw (Finset ι)) (K : Finset ι) (N c : ℕ) :
    0 ≤ congestionProb μ K N c :=
  FiniteLaw.prob_nonneg _ _

theorem congestionProb_le (μ : FiniteLaw (Finset ι)) (K : Finset ι) (N c : ℕ) {θ : ℝ}
    (hθ : 0 ≤ θ) :
    congestionProb μ K N c ≤ Real.exp (-(θ * (K.card * c))) * (mgf μ K θ) ^ N := by
  classical
  unfold congestionProb mgf
  rw [FiniteLaw.prob_eq_expect, ← expect_iid_prod, ← FiniteLaw.expect_const_mul]
  apply FiniteLaw.expect_mono
  intro T
  have hprod : Real.exp (-(θ * (K.card * c))) * ∏ i, Real.exp (θ * selected K (T i)) =
      Real.exp (θ * ((∑ s ∈ K, (includers s T : ℝ)) - K.card * c)) := by
    rw [← Real.exp_sum, ← Real.exp_add, ← Finset.mul_sum, sum_selected_eq]
    ring_nf
  rw [hprod]
  by_cases hE : Congested K c T
  · rw [if_pos hE]
    apply Real.one_le_exp
    apply mul_nonneg hθ
    have : (K.card : ℝ) * c = ∑ s ∈ K, (c : ℝ) := by simp
    rw [this, sub_nonneg]
    exact Finset.sum_le_sum (fun s hs => by exact_mod_cast hE s hs)
  · rw [if_neg hE]
    exact (Real.exp_pos _).le

noncomputable def selTilt (μ : FiniteLaw (Finset ι)) (K : Finset ι) (θ : ℝ) :
    FiniteLaw (Finset ι) :=
  tilt μ (fun S => θ * selected K S)

noncomputable def tiltMean (μ : FiniteLaw (Finset ι)) (K : Finset ι) (θ : ℝ) : ℝ :=
  (selTilt μ K θ).expect (fun S => (selected K S : ℝ))

theorem sum_marginal_eq (ν : FiniteLaw (Finset ι)) (K : Finset ι) :
    ∑ s ∈ K, marginal ν s = ν.expect (fun S => (selected K S : ℝ)) := by
  simp_rw [marginal_eq_expect]
  rw [← FiniteLaw.expect_finset_sum]
  apply FiniteLaw.expect_congr
  intro S
  rw [selected_eq_sum]

theorem includers_deviation_le (ν : FiniteLaw (Finset ι)) (s : ι) (N : ℕ) {t : ℝ}
    (ht : 0 < t) :
    (iid ν N).prob (fun T => t ≤ |(includers s T : ℝ) - N * marginal ν s|) ≤
      N * marginal ν s * (1 - marginal ν s) / t ^ 2 := by
  classical
  have h := expect_includers ν s N
    (fun m => if t ≤ |(m : ℝ) - N * marginal ν s| then (1 : ℝ) else 0)
  rw [FiniteLaw.prob_eq_expect, h]
  have hc := (IndependentCounts.binomial N (marginal ν s) (marginal_nonneg ν s)
    (marginal_le_one ν s)).chebyshev (fun r => (r.val : ℝ)) t ht
  have hl := IndependentCounts.binomial_load N (marginal ν s) (marginal_nonneg ν s)
    (marginal_le_one ν s)
  unfold CountLaw.load at hl
  rw [hl, IndependentCounts.binomial_variance, FiniteLaw.prob_eq_expect] at hc
  exact hc

theorem prob_all_near_ge (ν : FiniteLaw (Finset ι)) (K : Finset ι) (N : ℕ) {η : ℝ}
    (hη : 0 < η) (hN : (K.card : ℝ) ≤ 2 * N * η ^ 2) :
    1 / 2 ≤ (iid ν N).prob
      (fun T => ∀ s ∈ K, |(includers s T : ℝ) - N * marginal ν s| < N * η) := by
  have hbad : (iid ν N).prob
      (fun T => ¬ ∀ s ∈ K, |(includers s T : ℝ) - N * marginal ν s| < N * η) ≤ 1 / 2 := by
    calc
      _ ≤ (iid ν N).prob
          (fun T => ∃ s ∈ K, N * η ≤ |(includers s T : ℝ) - N * marginal ν s|) := by
        apply FiniteLaw.prob_mono
        intro T hT
        simp only [not_forall, not_lt, exists_prop] at hT
        exact hT
      _ ≤ ∑ s ∈ K, (iid ν N).prob
          (fun T => N * η ≤ |(includers s T : ℝ) - N * marginal ν s|) := prob_exists_le _ _ _
      _ ≤ ∑ _s ∈ K, 1 / (4 * N * η ^ 2) := by
        apply Finset.sum_le_sum
        intro s hs
        have hk : (1 : ℝ) ≤ K.card := by exact_mod_cast Finset.card_pos.mpr ⟨s, hs⟩
        have hNpos : (0 : ℝ) < N := by
          by_contra h0
          have : (N : ℝ) = 0 := le_antisymm (not_lt.mp h0) (Nat.cast_nonneg N)
          rw [this] at hN
          linarith
        have ht : 0 < (N : ℝ) * η := mul_pos hNpos hη
        refine (includers_deviation_le ν s N ht).trans ?_
        have hp0 := marginal_nonneg ν s
        have hp1 := marginal_le_one ν s
        have hpq : marginal ν s * (1 - marginal ν s) ≤ 1 / 4 := by
          nlinarith [sq_nonneg (marginal ν s - 1 / 2)]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have : (N : ℝ) * marginal ν s * (1 - marginal ν s) ≤ N * (1 / 4) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hpq hNpos.le
        nlinarith [sq_nonneg η, mul_pos hNpos (sq_pos_of_pos hη)]
      _ = K.card / (4 * N * η ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ 1 / 2 := by
        rcases Nat.eq_zero_or_pos K.card with hk | hk
        · rw [hk]
          simp
        · have hk' : (1 : ℝ) ≤ K.card := by exact_mod_cast hk
          have hpos : 0 < 4 * (N : ℝ) * η ^ 2 := by nlinarith
          rw [div_le_div_iff₀ hpos (by norm_num)]
          linarith
  have hc := (iid ν N).prob_compl
    (fun T => ∀ s ∈ K, |(includers s T : ℝ) - N * marginal ν s| < N * η)
  linarith

theorem congestionProb_ge (μ : FiniteLaw (Finset ι)) (K : Finset ι) (N c : ℕ) {θ η : ℝ}
    (hθ : 0 ≤ θ) (hη : 0 < η) (hN : (K.card : ℝ) ≤ 2 * N * η ^ 2)
    (hc : ∀ s ∈ K, (c : ℝ) ≤ N * (marginal (selTilt μ K θ) s - η)) :
    Real.exp (-(θ * (N * (tiltMean μ K θ + K.card * η)))) * (mgf μ K θ) ^ N / 2 ≤
      congestionProb μ K N c := by
  classical
  set ν := selTilt μ K θ with hν
  set B : ℝ := N * (tiltMean μ K θ + K.card * η) with hB
  let G : (Fin N → Finset ι) → Prop :=
    fun T => ∀ s ∈ K, |(includers s T : ℝ) - N * marginal ν s| < N * η
  have hG := prob_all_near_ge ν K N hη hN
  have hchange := expect_iid_eq_tilt μ (fun S => θ * selected K S) N
    (fun T => if Congested K c T then (1 : ℝ) else 0)
  have hpoint : ∀ T : Fin N → Finset ι,
      Real.exp (-(θ * B)) * (if G T then (1 : ℝ) else 0) ≤
        (if Congested K c T then (1 : ℝ) else 0) *
          Real.exp (-(∑ i, θ * (selected K (T i) : ℝ))) := by
    intro T
    by_cases hGT : G T
    · have hE : Congested K c T := by
        intro s hs
        have h1 := (abs_lt.mp (hGT s hs)).1
        have h2 := hc s hs
        have : (c : ℝ) < includers s T := by linarith
        exact_mod_cast this.le
      rw [if_pos hGT, if_pos hE, mul_one, one_mul]
      apply Real.exp_le_exp.mpr
      apply neg_le_neg
      rw [← Finset.mul_sum, sum_selected_eq]
      apply mul_le_mul_of_nonneg_left _ hθ
      have hsum : ∑ s ∈ K, (includers s T : ℝ) ≤ ∑ s ∈ K, (N * marginal ν s + N * η) :=
        Finset.sum_le_sum (fun s hs => by linarith [(abs_lt.mp (hGT s hs)).2])
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_marginal_eq, Finset.sum_const,
        nsmul_eq_mul] at hsum
      rw [hB]
      unfold tiltMean
      rw [← hν]
      nlinarith
    · rw [if_neg hGT, mul_zero]
      exact mul_nonneg (by split <;> norm_num) (Real.exp_pos _).le
  have hmono : Real.exp (-(θ * B)) * (iid ν N).prob G ≤
      (iid ν N).expect (fun T => (if Congested K c T then (1 : ℝ) else 0) *
        Real.exp (-(∑ i, θ * (selected K (T i) : ℝ)))) := by
    rw [FiniteLaw.prob_eq_expect, ← FiniteLaw.expect_const_mul]
    exact FiniteLaw.expect_mono _ hpoint
  have hP : congestionProb μ K N c = (mgf μ K θ) ^ N *
      (iid ν N).expect (fun T => (if Congested K c T then (1 : ℝ) else 0) *
        Real.exp (-(∑ i, θ * (selected K (T i) : ℝ)))) := by
    unfold congestionProb
    rw [FiniteLaw.prob_eq_expect, hchange]
    rfl
  rw [hP]
  have hM : 0 ≤ (mgf μ K θ) ^ N := pow_nonneg (mgf_pos μ K θ).le N
  have he : 0 < Real.exp (-(θ * B)) := Real.exp_pos _
  calc
    Real.exp (-(θ * B)) * (mgf μ K θ) ^ N / 2
        ≤ (mgf μ K θ) ^ N * (Real.exp (-(θ * B)) * (iid ν N).prob G) := by
          nlinarith [mul_le_mul_of_nonneg_left hG (mul_nonneg hM he.le)]
    _ ≤ _ := mul_le_mul_of_nonneg_left hmono hM

def SwapInvariant (μ : FiniteLaw (Finset ι)) (K : Finset ι) : Prop :=
  ∀ s ∈ K, ∀ t ∈ K, ∀ S : Finset ι, μ.mass ((Equiv.swap s t).finsetCongr S) = μ.mass S

omit [Fintype ι] in
theorem mem_swap_finsetCongr (s t : ι) (S : Finset ι) (x : ι) :
    x ∈ (Equiv.swap s t).finsetCongr S ↔ Equiv.swap s t x ∈ S := by
  rw [Equiv.finsetCongr_apply, Finset.mem_map_equiv, Equiv.symm_swap]

omit [Fintype ι] in
theorem swap_finsetCongr_self {K : Finset ι} {s t : ι} (hs : s ∈ K) (ht : t ∈ K) :
    (Equiv.swap s t).finsetCongr K = K := by
  ext x
  rw [mem_swap_finsetCongr]
  by_cases hxs : x = s
  · subst hxs
    rw [Equiv.swap_apply_left]
    exact ⟨fun _ => hs, fun _ => ht⟩
  · by_cases hxt : x = t
    · subst hxt
      rw [Equiv.swap_apply_right]
      exact ⟨fun _ => ht, fun _ => hs⟩
    · rw [Equiv.swap_apply_of_ne_of_ne hxs hxt]

omit [Fintype ι] in
theorem selected_swap {K : Finset ι} {s t : ι} (hs : s ∈ K) (ht : t ∈ K) (S : Finset ι) :
    selected K ((Equiv.swap s t).finsetCongr S) = selected K S := by
  unfold selected
  conv_lhs => rw [← swap_finsetCongr_self hs ht]
  rw [Equiv.finsetCongr_apply, Equiv.finsetCongr_apply, ← Finset.map_inter, Finset.card_map]

theorem selTilt_swapInvariant {μ : FiniteLaw (Finset ι)} {K : Finset ι}
    (h : SwapInvariant μ K) (θ : ℝ) : SwapInvariant (selTilt μ K θ) K := by
  intro s hs t ht S
  simp only [selTilt, tilt_mass]
  rw [h s hs t ht S, selected_swap hs ht S]

theorem marginal_eq_of_swap {ν : FiniteLaw (Finset ι)} {s t : ι}
    (h : ∀ S : Finset ι, ν.mass ((Equiv.swap s t).finsetCongr S) = ν.mass S) :
    marginal ν s = marginal ν t := by
  rw [marginal_eq_expect, marginal_eq_expect]
  unfold FiniteLaw.expect
  rw [← Equiv.sum_comp (Equiv.swap s t).finsetCongr]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  dsimp only
  have hm : s ∈ (Equiv.swap s t).finsetCongr S ↔ t ∈ S := by
    rw [mem_swap_finsetCongr, Equiv.swap_apply_left]
  rw [h S]
  simp only [hm]

theorem marginal_selTilt {μ : FiniteLaw (Finset ι)} {K : Finset ι} (h : SwapInvariant μ K)
    (θ : ℝ) {s : ι} (hs : s ∈ K) :
    marginal (selTilt μ K θ) s = tiltMean μ K θ / K.card := by
  have hk : (0 : ℝ) < K.card := by exact_mod_cast Finset.card_pos.mpr ⟨s, hs⟩
  have hsum := sum_marginal_eq (selTilt μ K θ) K
  have hall : ∀ t ∈ K, marginal (selTilt μ K θ) t = marginal (selTilt μ K θ) s :=
    fun t ht => marginal_eq_of_swap (selTilt_swapInvariant h θ t ht s hs)
  rw [Finset.sum_congr rfl hall, Finset.sum_const, nsmul_eq_mul] at hsum
  unfold tiltMean
  rw [← hsum]
  field_simp

theorem congestionProb_ge_of_swap {μ : FiniteLaw (Finset ι)} {K : Finset ι}
    (h : SwapInvariant μ K) (N c : ℕ) {θ η : ℝ} (hθ : 0 ≤ θ) (hη : 0 < η)
    (hN : (K.card : ℝ) ≤ 2 * N * η ^ 2)
    (hc : (c : ℝ) ≤ N * (tiltMean μ K θ / K.card - η)) :
    Real.exp (-(θ * (N * (tiltMean μ K θ + K.card * η)))) * (mgf μ K θ) ^ N / 2 ≤
      congestionProb μ K N c :=
  congestionProb_ge μ K N c hθ hη hN (fun s hs => by rw [marginal_selTilt h θ hs]; exact hc)

end SimultaneousCongestion
end FCAppendix
