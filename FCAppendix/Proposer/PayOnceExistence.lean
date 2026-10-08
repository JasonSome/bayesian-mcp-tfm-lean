import FCAppendix.Proposer.Threshold

namespace FCAppendix
namespace PayOnce

open scoped BigOperators

theorem H_decrease_lower (n : ℕ) (hn : 2 ≤ n) (p q : ℝ)
    (hpq : p ≤ q) (hq : q ≤ 1) :
    (q - p) / (n : ℝ) ≤ H n p - H n q := by
  have hs := Finset.single_le_sum
    (s := Finset.range n) (f := fun j => (1 - p) ^ j - (1 - q) ^ j)
    (fun j _ => sub_nonneg.mpr (power_mono (sub_nonneg.mpr hq) (by linarith) j))
    (Finset.mem_range.mpr (show 1 < n by omega))
  have hs' : q - p ≤ ∑ j ∈ Finset.range n, ((1 - p) ^ j - (1 - q) ^ j) := by
    simp only [pow_one] at hs
    linarith
  have hd := div_le_div_of_nonneg_right hs' (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  simpa only [Finset.sum_sub_distrib, sub_div, H] using hd

def ScalarThreshold (n : ℕ) (b lam p : ℝ) : Prop :=
  0 ≤ p ∧ p ≤ 1 ∧
  (p = 0 → b * H n p ≤ lam) ∧
  (p = 1 → lam ≤ b * H n p) ∧
  (0 < p → p < 1 → b * H n p = lam)

theorem exists_scalar_threshold (n : ℕ) (hn : 2 ≤ n) (b : ℝ) (_hb : 0 < b) (lam : ℝ) :
    ∃ p : ℝ, ScalarThreshold n b lam p := by
  have hn0 : 0 < n := by omega
  by_cases hhigh : b ≤ lam
  · refine ⟨0, le_rfl, by norm_num, ?_, ?_, ?_⟩
    · intro _
      simpa [H_zero n hn0] using hhigh
    · intro h
      norm_num at h
    · intro h
      linarith
  by_cases hlow : lam ≤ b / n
  · refine ⟨1, by norm_num, le_rfl, ?_, ?_, ?_⟩
    · intro h
      norm_num at h
    · intro _
      simpa [H_one n hn0, div_eq_mul_inv] using hlow
    · intro _ h
      linarith
  · have hc : Continuous (fun p : ℝ => b * H n p) :=
      continuous_const.mul (continuous_H n)
    have hlam : lam ∈ Set.Icc (b * H n 1) (b * H n 0) := by
      constructor
      · simpa [H_one n hn0, div_eq_mul_inv] using le_of_lt (lt_of_not_ge hlow)
      · simpa [H_zero n hn0] using le_of_lt (lt_of_not_ge hhigh)
    obtain ⟨p, hp, he⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1)
      hc.continuousOn hlam
    exact ⟨p, hp.1, hp.2, (fun _ => le_of_eq he), (fun _ => le_of_eq he.symm),
      (fun _ _ => he)⟩

noncomputable def scalarDemand (n : ℕ) (hn : 2 ≤ n) (b : ℝ) (hb : 0 < b) (lam : ℝ) : ℝ :=
  Classical.choose (exists_scalar_threshold n hn b hb lam)

theorem scalarDemand_spec (n : ℕ) (hn : 2 ≤ n) (b : ℝ) (hb : 0 < b) (lam : ℝ) :
    ScalarThreshold n b lam (scalarDemand n hn b hb lam) :=
  Classical.choose_spec (exists_scalar_threshold n hn b hb lam)

theorem scalar_receipt_le_of_lt_one (n : ℕ) (b lam p : ℝ)
    (hp : ScalarThreshold n b lam p) (hlt : p < 1) : b * H n p ≤ lam := by
  by_cases hz : p = 0
  · exact hp.2.2.1 hz
  · exact le_of_eq (hp.2.2.2.2 (lt_of_le_of_ne hp.1 (Ne.symm hz)) hlt)

theorem scalar_price_le_of_pos (n : ℕ) (b lam p : ℝ)
    (hp : ScalarThreshold n b lam p) (hpos : 0 < p) : lam ≤ b * H n p := by
  by_cases ho : p = 1
  · exact hp.2.2.2.1 ho
  · exact le_of_eq (hp.2.2.2.2 hpos (lt_of_le_of_ne hp.2.1 ho)).symm

theorem scalar_difference_bound (n : ℕ) (hn : 2 ≤ n) (b : ℝ) (hb : 0 < b)
    (lam τ p q : ℝ) (hp : ScalarThreshold n b lam p) (hq : ScalarThreshold n b τ q) :
    (b / n) * |p - q| ≤ |lam - τ| := by
  have hforward : ∀ p q lam τ : ℝ, ScalarThreshold n b lam p →
      ScalarThreshold n b τ q → p < q → (b / n) * (q - p) ≤ lam - τ := by
    intro x y l t hx hy hxy
    have hlo := scalar_receipt_le_of_lt_one n b l x hx (lt_of_lt_of_le hxy hy.2.1)
    have hhi := scalar_price_le_of_pos n b t y hy (lt_of_le_of_lt hx.1 hxy)
    have hd := H_decrease_lower n hn x y (le_of_lt hxy) hy.2.1
    have hm := mul_le_mul_of_nonneg_left hd (le_of_lt hb)
    have he : b * ((y - x) / (n : ℝ)) = (b / n) * (y - x) := by ring
    rw [he] at hm
    nlinarith
  rcases lt_trichotomy p q with hl | he | hr
  · rw [abs_of_nonpos (by linarith : p - q ≤ 0)]
    have h := hforward p q lam τ hp hq hl
    have habs := le_abs_self (lam - τ)
    nlinarith
  · simp [he]
  · rw [abs_of_nonneg (by linarith : 0 ≤ p - q)]
    have h := hforward q p τ lam hq hp hr
    have habs := neg_abs_le (lam - τ)
    nlinarith

theorem scalarDemand_continuous (n : ℕ) (hn : 2 ≤ n) (b : ℝ) (hb : 0 < b) :
    Continuous (scalarDemand n hn b hb) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hcoef : 0 < b / n := div_pos hb hnR
  apply Metric.continuous_iff.mpr
  intro lam ε hε
  refine ⟨(b / n) * ε, mul_pos hcoef hε, ?_⟩
  intro τ hτ
  have h := scalar_difference_bound n hn b hb τ lam
    (scalarDemand n hn b hb τ) (scalarDemand n hn b hb lam)
    (scalarDemand_spec n hn b hb τ) (scalarDemand_spec n hn b hb lam)
  rw [Real.dist_eq] at hτ ⊢
  nlinarith

theorem scalarDemand_zero_price (n : ℕ) (hn : 2 ≤ n) (b : ℝ) (hb : 0 < b) :
    scalarDemand n hn b hb 0 = 1 := by
  have hs := scalarDemand_spec n hn b hb 0
  by_contra hne
  have hlt : scalarDemand n hn b hb 0 < 1 := lt_of_le_of_ne hs.2.1 hne
  have hle := scalar_receipt_le_of_lt_one n b 0 _ hs hlt
  have hpos := mul_pos hb (H_pos n (by omega) _ hs.1 hs.2.1)
  linarith

theorem scalarDemand_high_price (n : ℕ) (hn : 2 ≤ n) (b : ℝ) (hb : 0 < b)
    (lam : ℝ) (hlam : b ≤ lam) : scalarDemand n hn b hb lam = 0 := by
  have hs := scalarDemand_spec n hn b hb lam
  by_contra hne
  have hpos : 0 < scalarDemand n hn b hb lam := lt_of_le_of_ne hs.1 (Ne.symm hne)
  have hle := scalar_price_le_of_pos n b lam _ hs hpos
  have hstrict := H_strict n hn 0 _ hpos hs.2.1
  rw [H_zero n (by omega)] at hstrict
  have hmul := mul_lt_mul_of_pos_left hstrict hb
  nlinarith

end PayOnce
namespace Proposer

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem exists_pay_once_threshold (n : ℕ) (hn : 2 ≤ n) (b : ι → ℝ)
    (hb : ∀ i, 0 < b i) (c : ℕ) (hc : c ≤ Fintype.card ι) :
    ∃ p : ι → ℝ, ∃ lam : ℝ,
      (∀ i, 0 ≤ p i) ∧ (∀ i, p i ≤ 1) ∧ (∑ i, p i = c) ∧ 0 ≤ lam ∧
      Threshold p (fun i => b i * PayOnce.H n (p i)) lam := by
  classical
  let M : ℝ := 1 + ∑ i, b i
  have hsum0 : 0 ≤ ∑ i, b i := Finset.sum_nonneg (fun i _ => le_of_lt (hb i))
  have hM : 0 ≤ M := by dsimp [M]; linarith
  have hbi : ∀ i, b i ≤ M := by
    intro i
    have h := Finset.single_le_sum (s := Finset.univ) (f := b)
      (fun j _ => le_of_lt (hb j)) (Finset.mem_univ i)
    dsimp [M]
    linarith
  let d : ι → ℝ → ℝ := fun i lam => PayOnce.scalarDemand n hn (b i) (hb i) lam
  let D : ℝ → ℝ := fun lam => ∑ i, d i lam
  have hcontS : ∀ s : Finset ι, Continuous (fun lam => ∑ i ∈ s, d i lam) := by
    intro s
    exact continuous_finsetSum s fun i _ => PayOnce.scalarDemand_continuous n hn (b i) (hb i)

  have hcont : Continuous D := hcontS Finset.univ
  have hD0 : D 0 = (Fintype.card ι : ℝ) := by
    dsimp [D, d]
    simp only [PayOnce.scalarDemand_zero_price, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one]
  have hdM : ∀ i, d i M = 0 := by
    intro i
    exact PayOnce.scalarDemand_high_price n hn (b i) (hb i) M (hbi i)
  have hDM : D M = 0 := by
    dsimp [D]
    simp_rw [hdM]
    simp
  have hbetween : (c : ℝ) ∈ Set.Icc (D M) (D 0) := by
    rw [hDM, hD0]
    exact ⟨Nat.cast_nonneg _, by exact_mod_cast hc⟩
  obtain ⟨lam, hlam, hroot⟩ := intermediate_value_Icc' hM hcont.continuousOn hbetween
  refine ⟨fun i => d i lam, lam, ?_, ?_, hroot, hlam.1, ?_⟩
  · intro i
    exact (PayOnce.scalarDemand_spec n hn (b i) (hb i) lam).1
  · intro i
    exact (PayOnce.scalarDemand_spec n hn (b i) (hb i) lam).2.1
  · refine ⟨?_, ?_, ?_⟩
    · intro i hi
      exact (PayOnce.scalarDemand_spec n hn (b i) (hb i) lam).2.2.1 hi
    · intro i hi
      exact (PayOnce.scalarDemand_spec n hn (b i) (hb i) lam).2.2.2.1 hi
    · intro i hi hj
      exact (PayOnce.scalarDemand_spec n hn (b i) (hb i) lam).2.2.2.2 hi hj

theorem pay_once_threshold_price_pos (n : ℕ) (hn : 2 ≤ n) (b p : ι → ℝ)
    (hb : ∀ i, 0 < b i) (c : ℕ) (hc : c < Fintype.card ι) (lam : ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (hsum : ∑ i, p i = c)
    (hlam : 0 ≤ lam) (ht : Threshold p (fun i => b i * PayOnce.H n (p i)) lam) : 0 < lam := by
  have hne : lam ≠ 0 := by
    intro hz
    have hpall : ∀ i, p i = 1 := by
      intro i
      by_contra hi
      have hpi : p i < 1 := lt_of_le_of_ne (hp1 i) hi
      have hscalar : PayOnce.ScalarThreshold n (b i) lam (p i) :=
        ⟨hp0 i, hp1 i, ht.1 i, ht.2.1 i, ht.2.2 i⟩
      have hle := PayOnce.scalar_receipt_le_of_lt_one n (b i) lam (p i) hscalar hpi
      have hpos := mul_pos (hb i) (PayOnce.H_pos n (by omega) (p i) (hp0 i) (hp1 i))
      rw [hz] at hle
      linarith
    have hsumN : (∑ i, p i) = (Fintype.card ι : ℝ) := by simp_rw [hpall]; simp
    have hcn : (c : ℝ) < Fintype.card ι := by exact_mod_cast hc
    linarith
  exact lt_of_le_of_ne hlam (Ne.symm hne)

theorem exists_pay_once_lottery (n : ℕ) (hn : 2 ≤ n) (b : ι → ℝ)
    (hb : ∀ i, 0 < b i) (c : ℕ) (hc : c ≤ Fintype.card ι) :
    ∃ p : ι → ℝ, ∃ lam : ℝ, ∃ μ : FiniteLaw (Finset ι),
      (∀ i, 0 ≤ p i) ∧ (∀ i, p i ≤ 1) ∧ (∑ i, p i = c) ∧ 0 ≤ lam ∧
      Threshold p (fun i => b i * PayOnce.H n (p i)) lam ∧
      (∀ S, μ.mass S ≠ 0 → S.card = c) ∧
      (∀ i, marginal μ i = p i) ∧
      (∀ ν : FiniteLaw (Finset ι), (∀ S, ν.mass S ≠ 0 → S.card ≤ c) →
        revenue ν (fun i => b i * PayOnce.H n (p i)) ≤
        revenue μ (fun i => b i * PayOnce.H n (p i))) := by
  obtain ⟨p, lam, hp0, hp1, hsum, hlam, ht⟩ := exists_pay_once_threshold n hn b hb c hc
  obtain ⟨μ, hcap, hmarg, hopt⟩ := implement_best_response p
    (fun i => b i * PayOnce.H n (p i)) lam c hp0 hp1 hsum hlam ht
  exact ⟨p, lam, μ, hp0, hp1, hsum, hlam, ht, hcap, hmarg, hopt⟩

end Proposer
end FCAppendix
