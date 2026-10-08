import FCAppendix.Proposer.CommonListGame

namespace FCAppendix
namespace CommonList

open scoped BigOperators
open Proposer

variable {ι : Type*} [Fintype ι]

def IsKernel (n c : ℕ) (b p : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ (∀ i, p i ≤ 1) ∧ (∑ i, p i = (min c (Fintype.card ι) : ℕ)) ∧
    ∃ L, 0 ≤ L ∧ Threshold p (fun i => b i * PayOnce.H n (p i)) L

theorem exists_isKernel (n : ℕ) (hn : 2 ≤ n) (c : ℕ) (b : ι → ℝ) (hb : ∀ i, 0 < b i) :
    ∃ p, IsKernel n c b p := by
  obtain ⟨p, L, hp0, hp1, hsum, hL, ht⟩ :=
    exists_pay_once_threshold n hn b hb (min c (Fintype.card ι)) (min_le_right _ _)
  exact ⟨p, hp0, hp1, hsum, L, hL, ht⟩

theorem isKernel_unique (n : ℕ) (hn : 2 ≤ n) (c : ℕ) (b : ι → ℝ) (hb : ∀ i, 0 < b i)
    (p q : ι → ℝ) (hp : IsKernel n c b p) (hq : IsKernel n c b q) : p = q := by
  obtain ⟨hp0, hp1, hps, L, hL, hpt⟩ := hp
  obtain ⟨hq0, hq1, hqs, L', hL', hqt⟩ := hq
  exact pay_once_unique n hn b hb p q L L' _ hp0 hp1 hps hq0 hq1 hqs hL hL' hpt hqt

noncomputable def kernelMarginal (n c : ℕ) (b : ι → ℝ) : ι → ℝ := by
  classical
  exact if h : ∃ p, IsKernel n c b p then Classical.choose h else fun _ => 0

theorem kernelMarginal_spec (n : ℕ) (hn : 2 ≤ n) (c : ℕ) (b : ι → ℝ) (hb : ∀ i, 0 < b i) :
    IsKernel n c b (kernelMarginal n c b) := by
  have h := exists_isKernel n hn c b hb
  unfold kernelMarginal
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem eq_kernelMarginal (n : ℕ) (hn : 2 ≤ n) (c : ℕ) (b : ι → ℝ) (hb : ∀ i, 0 < b i)
    (p : ι → ℝ) (hp : IsKernel n c b p) : p = kernelMarginal n c b :=
  isKernel_unique n hn c b hb p _ hp (kernelMarginal_spec n hn c b hb)

theorem equilibrium_marginal_eq_kernelMarginal [DecidableEq ι] (n : ℕ) (hn : 2 ≤ n) (c : ℕ)
    (b : ι → ℝ) (hb : ∀ i, 0 < b i) (μ : FiniteLaw (Finset ι))
    (hμ : PayOnceEquilibrium n c b μ) : marginal μ = kernelMarginal n c b := by
  apply eq_kernelMarginal n hn c b hb
  by_cases hc : c ≤ Fintype.card ι
  · obtain ⟨_, hsum, L, hL, ht⟩ := equilibrium_structure n hn b hb c hc μ hμ
    refine ⟨marginal_nonneg μ, marginal_le_one μ, ?_, L, le_of_lt hL, ht⟩
    rw [Nat.min_eq_left hc]
    exact hsum
  · have hμu := (payOnceEquilibrium_small_list_iff n (by omega) b hb c (by omega) μ).mp hμ
    have hone : ∀ i, marginal μ i = 1 := by
      intro i
      apply marginal_eq_one_of_forall
      intro S hS
      have hSu : S = Finset.univ := by
        by_contra hne
        apply hS
        rw [hμu]
        simp [FiniteLaw.dirac, hne]
      rw [hSu]
      exact Finset.mem_univ i
    refine ⟨marginal_nonneg μ, marginal_le_one μ, ?_, 0, le_rfl, ?_, ?_, ?_⟩
    · rw [Nat.min_eq_right (by omega)]
      simp [hone]
    · intro i hi
      rw [hone i] at hi
      norm_num at hi
    · intro i _
      exact le_of_lt (mul_pos (hb i)
        (PayOnce.H_pos n (by omega) _ (marginal_nonneg μ i) (marginal_le_one μ i)))
    · intro i _ hi
      rw [hone i] at hi
      norm_num at hi

theorem kernel_cross (n c : ℕ) (b b' p q : ι → ℝ) (hp : IsKernel n c b p)
    (hq : IsKernel n c b' q) :
    ∑ i, (q i - p i) * (b i * PayOnce.H n (p i) - b' i * PayOnce.H n (q i)) ≤ 0 := by
  obtain ⟨hp0, hp1, hps, L, hL, hpt⟩ := hp
  obtain ⟨hq0, hq1, hqs, L', hL', hqt⟩ := hq
  have h1 := threshold_linear_optimal p (fun i => b i * PayOnce.H n (p i)) L _
    hp0 hp1 hps hL hpt q hq0 hq1 (le_of_eq hqs)
  have h2 := threshold_linear_optimal q (fun i => b' i * PayOnce.H n (q i)) L' _
    hq0 hq1 hqs hL' hqt p hp0 hp1 (le_of_eq hps)
  have he : (∑ i, (q i - p i) * (b i * PayOnce.H n (p i) - b' i * PayOnce.H n (q i))) =
      ((∑ i, q i * (b i * PayOnce.H n (p i))) - ∑ i, p i * (b i * PayOnce.H n (p i))) +
      ((∑ i, p i * (b' i * PayOnce.H n (q i))) - ∑ i, q i * (b' i * PayOnce.H n (q i))) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [he]
  linarith

theorem H_gap (n : ℕ) (hn : 2 ≤ n) (x y : ℝ) (hx1 : x ≤ 1) (hy1 : y ≤ 1) :
    (y - x) ^ 2 / n ≤ (y - x) * (PayOnce.H n x - PayOnce.H n y) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rcases le_total x y with hxy | hyx
  · have hd := PayOnce.H_decrease_lower n hn x y hxy hy1
    have hm := mul_le_mul_of_nonneg_left hd (sub_nonneg.mpr hxy)
    calc
      (y - x) ^ 2 / n = (y - x) * ((y - x) / n) := by ring
      _ ≤ _ := hm
  · have hd := PayOnce.H_decrease_lower n hn y x hyx hx1
    have hm := mul_le_mul_of_nonneg_left hd (sub_nonneg.mpr hyx)
    calc
      (y - x) ^ 2 / n = (x - y) * ((x - y) / n) := by ring
      _ ≤ (x - y) * (PayOnce.H n y - PayOnce.H n x) := hm
      _ = _ := by ring

theorem kernel_gap_le (n c : ℕ) (b b' p q : ι → ℝ) (hp : IsKernel n c b p)
    (hq : IsKernel n c b' q) :
    ∑ j, b j * ((q j - p j) * (PayOnce.H n (p j) - PayOnce.H n (q j))) ≤
      ∑ j, (q j - p j) * (b' j - b j) * PayOnce.H n (q j) := by
  have h := kernel_cross n c b b' p q hp hq
  have he : (∑ j, (q j - p j) * (b j * PayOnce.H n (p j) - b' j * PayOnce.H n (q j))) =
      (∑ j, b j * ((q j - p j) * (PayOnce.H n (p j) - PayOnce.H n (q j)))) -
        ∑ j, (q j - p j) * (b' j - b j) * PayOnce.H n (q j) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [he] at h
  linarith

theorem gap_term_nonneg (n : ℕ) (hn : 2 ≤ n) (b p q : ℝ) (hb : 0 ≤ b) (hp1 : p ≤ 1)
    (hq1 : q ≤ 1) :
    b * (q - p) ^ 2 / n ≤ b * ((q - p) * (PayOnce.H n p - PayOnce.H n q)) := by
  have h := mul_le_mul_of_nonneg_left (H_gap n hn p q hp1 hq1) hb
  calc
    b * (q - p) ^ 2 / n = b * ((q - p) ^ 2 / n) := by ring
    _ ≤ _ := h

theorem kernel_perturbation (n : ℕ) (hn : 2 ≤ n) (c : ℕ) (b b' p q : ι → ℝ)
    (hb : ∀ i, 0 < b i) (hp : IsKernel n c b p) (hq : IsKernel n c b' q) (i : ι) :
    b i * (q i - p i) ^ 2 / n ≤ ∑ j, |b' j - b j| := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hgap := kernel_gap_le n c b b' p q hp hq
  have hterm : ∀ j, 0 ≤ b j * ((q j - p j) * (PayOnce.H n (p j) - PayOnce.H n (q j))) := by
    intro j
    have h := gap_term_nonneg n hn (b j) (p j) (q j) (le_of_lt (hb j)) (hp.2.1 j) (hq.2.1 j)
    have h0 : 0 ≤ b j * (q j - p j) ^ 2 / n := by
      have := hb j
      positivity
    linarith
  have hsingle := Finset.single_le_sum (fun j _ => hterm j) (Finset.mem_univ i)
  have hi := gap_term_nonneg n hn (b i) (p i) (q i) (le_of_lt (hb i)) (hp.2.1 i) (hq.2.1 i)
  have hright : (∑ j, (q j - p j) * (b' j - b j) * PayOnce.H n (q j)) ≤
      ∑ j, |b' j - b j| := by
    apply Finset.sum_le_sum
    intro j _
    have hx : |q j - p j| ≤ 1 := abs_le.mpr
      ⟨by linarith [hp.2.1 j, hq.1 j], by linarith [hq.2.1 j, hp.1 j]⟩
    have hHb := PayOnce.H_bounds n hn0 (q j) (hq.1 j) (hq.2.1 j)
    have hH0 : 0 ≤ 1 / (n : ℝ) := by positivity
    have hz : |PayOnce.H n (q j)| ≤ 1 := abs_le.mpr ⟨by linarith, hHb.2⟩
    calc
      (q j - p j) * (b' j - b j) * PayOnce.H n (q j) ≤
          |(q j - p j) * (b' j - b j) * PayOnce.H n (q j)| := le_abs_self _
      _ = |q j - p j| * |b' j - b j| * |PayOnce.H n (q j)| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * |b' j - b j| * 1 := by gcongr
      _ = |b' j - b j| := by ring
  linarith

theorem isOpen_positive : IsOpen {b : ι → ℝ | ∀ i, 0 < b i} := by
  have h : {b : ι → ℝ | ∀ i, 0 < b i} = ⋂ i, {b | 0 < b i} := by
    ext b
    simp
  rw [h]
  exact isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (continuous_apply i))

theorem continuousOn_kernelMarginal (n : ℕ) (hn : 2 ≤ n) (c : ℕ) :
    ContinuousOn (kernelMarginal (ι := ι) n c) {b | ∀ i, 0 < b i} := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [continuousOn_pi]
  intro i
  rw [Metric.continuousOn_iff]
  intro b hb ε hε
  set N : ℝ := (Fintype.card ι : ℝ) with hN_def
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hbi : 0 < b i := hb i
  refine ⟨ε ^ 2 * b i / (n * (N + 1)), by positivity, ?_⟩
  intro b' hb' hdist
  have hbound := kernel_perturbation n hn c b b' (kernelMarginal n c b)
    (kernelMarginal n c b') hb (kernelMarginal_spec n hn c b hb)
    (kernelMarginal_spec n hn c b' hb') i
  have hsum : (∑ j, |b' j - b j|) ≤ N * dist b' b := by
    calc
      (∑ j, |b' j - b j|) ≤ ∑ _j : ι, dist b' b := by
        apply Finset.sum_le_sum
        intro j _
        rw [← Real.dist_eq]
        exact dist_le_pi_dist b' b j
      _ = N * dist b' b := by simp [hN_def]
  set d : ℝ := kernelMarginal n c b' i - kernelMarginal n c b i with hd_def
  have key : d ^ 2 * (b i / n) ≤ (N / (N + 1) * ε ^ 2) * (b i / n) := by
    calc
      d ^ 2 * (b i / n) = b i * d ^ 2 / n := by ring
      _ ≤ N * dist b' b := le_trans hbound hsum
      _ ≤ N * (ε ^ 2 * b i / (n * (N + 1))) :=
        mul_le_mul_of_nonneg_left (le_of_lt hdist) hN
      _ = (N / (N + 1) * ε ^ 2) * (b i / n) := by
        field_simp
  have hD : d ^ 2 ≤ N / (N + 1) * ε ^ 2 := le_of_mul_le_mul_right key (div_pos hbi hnR)
  have hfrac : N / (N + 1) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have hε2 : 0 < ε ^ 2 := by positivity
  have hlt : d ^ 2 < ε ^ 2 := by nlinarith
  rw [Real.dist_eq]
  exact abs_lt_of_sq_lt_sq hlt (le_of_lt hε)

theorem continuousAt_kernelMarginal (n : ℕ) (hn : 2 ≤ n) (c : ℕ) (b : ι → ℝ)
    (hb : ∀ i, 0 < b i) : ContinuousAt (kernelMarginal n c) b :=
  (continuousOn_kernelMarginal n hn c).continuousAt (isOpen_positive.mem_nhds hb)

theorem kernelMarginal_mono_own [DecidableEq ι] (n : ℕ) (hn : 2 ≤ n) (c : ℕ)
    (b b' : ι → ℝ) (hb : ∀ i, 0 < b i) (hb' : ∀ i, 0 < b' i) (i : ι)
    (hother : ∀ j, j ≠ i → b' j = b j) (hle : b i ≤ b' i) :
    kernelMarginal n c b i ≤ kernelMarginal n c b' i := by
  set p := kernelMarginal n c b
  set q := kernelMarginal n c b'
  have hp := kernelMarginal_spec n hn c b hb
  have hq := kernelMarginal_spec n hn c b' hb'
  have hgap := kernel_gap_le n c b b' p q hp hq
  have hR : (∑ j, (q j - p j) * (b' j - b j) * PayOnce.H n (q j)) =
      (q i - p i) * (b' i - b i) * PayOnce.H n (q i) :=
    Finset.sum_eq_single i (fun j _ hj => by rw [hother j hj, sub_self, mul_zero, zero_mul])
      (fun h => absurd (Finset.mem_univ i) h)
  rw [hR] at hgap
  by_contra hlt
  push Not at hlt
  have hterm : ∀ j, 0 ≤ b j * ((q j - p j) * (PayOnce.H n (p j) - PayOnce.H n (q j))) := by
    intro j
    have h := gap_term_nonneg n hn (b j) (p j) (q j) (le_of_lt (hb j)) (hp.2.1 j) (hq.2.1 j)
    have h0 : 0 ≤ b j * (q j - p j) ^ 2 / n := by
      have := hb j
      positivity
    linarith
  have hsingle := Finset.single_le_sum (fun j _ => hterm j) (Finset.mem_univ i)
  have hi := gap_term_nonneg n hn (b i) (p i) (q i) (le_of_lt (hb i)) (hp.2.1 i) (hq.2.1 i)
  have hpos : 0 < b i * (q i - p i) ^ 2 / n := by
    have hne : q i - p i ≠ 0 := by linarith
    have := hb i
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    positivity
  have hH := PayOnce.H_pos n (by omega) (q i) (hq.1 i) (hq.2.1 i)
  have hneg : (q i - p i) * (b' i - b i) * PayOnce.H n (q i) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)) (le_of_lt hH)
  linarith

theorem kernelMarginal_monotoneOn_own [DecidableEq ι] (n : ℕ) (hn : 2 ≤ n) (c : ℕ)
    (b : ι → ℝ) (hb : ∀ i, 0 < b i) (i : ι) :
    MonotoneOn (fun t => kernelMarginal n c (Function.update b i t) i) (Set.Ioi 0) := by
  intro s hs t ht hst
  have hpos : ∀ u : ℝ, 0 < u → ∀ j, 0 < Function.update b i u j := by
    intro u hu j
    by_cases hj : j = i
    · subst hj
      simpa using hu
    · rw [Function.update_of_ne hj]
      exact hb j
  apply kernelMarginal_mono_own n hn c _ _ (hpos s hs) (hpos t ht) i
  · intro j hj
    rw [Function.update_of_ne hj, Function.update_of_ne hj]
  · simpa using hst

theorem kernelMarginal_saturates (n : ℕ) (hn : 2 ≤ n) (c : ℕ) (hc1 : 1 ≤ c)
    (b : ι → ℝ) (hb : ∀ i, 0 < b i) (i : ι) (hdom : ∀ j, j ≠ i → b j < b i / n) :
    kernelMarginal n c b i = 1 := by
  classical
  have hn0 : 0 < n := by omega
  set p := kernelMarginal n c b
  obtain ⟨hp0, hp1, hsum, L, _, ht⟩ := kernelMarginal_spec n hn c b hb
  by_contra hne
  have hlt : p i < 1 := lt_of_le_of_ne (hp1 i) hne
  have hscalar : PayOnce.ScalarThreshold n (b i) L (p i) :=
    ⟨hp0 i, hp1 i, ht.1 i, ht.2.1 i, ht.2.2 i⟩
  have hri : b i * PayOnce.H n (p i) ≤ L :=
    PayOnce.scalar_receipt_le_of_lt_one n (b i) L (p i) hscalar hlt
  have hHi := (PayOnce.H_bounds n hn0 (p i) (hp0 i) (hp1 i)).1
  have hlow : b i / n ≤ b i * PayOnce.H n (p i) := by
    have := mul_le_mul_of_nonneg_left hHi (le_of_lt (hb i))
    simpa [div_eq_mul_inv] using this
  have hzero : ∀ j, j ≠ i → p j = 0 := by
    intro j hj
    by_contra hpj
    have hpos : 0 < p j := lt_of_le_of_ne (hp0 j) (Ne.symm hpj)
    have hsj : PayOnce.ScalarThreshold n (b j) L (p j) :=
      ⟨hp0 j, hp1 j, ht.1 j, ht.2.1 j, ht.2.2 j⟩
    have hLj := PayOnce.scalar_price_le_of_pos n (b j) L (p j) hsj hpos
    have hHj := (PayOnce.H_bounds n hn0 (p j) (hp0 j) (hp1 j)).2
    have hrj : b j * PayOnce.H n (p j) ≤ b j := by
      have := mul_le_mul_of_nonneg_left hHj (le_of_lt (hb j))
      simpa using this
    have := hdom j hj
    linarith
  have hsi : (∑ j, p j) = p i :=
    Finset.sum_eq_single i (fun j _ hj => hzero j hj) (fun h => absurd (Finset.mem_univ i) h)
  have hcard : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  have hmin : 1 ≤ min c (Fintype.card ι) := le_min hc1 hcard
  have hminR : (1 : ℝ) ≤ ((min c (Fintype.card ι) : ℕ) : ℝ) := by exact_mod_cast hmin
  rw [hsi] at hsum
  linarith

end CommonList
end FCAppendix
