import FCAppendix.PayOnce.KernelTailEvent

namespace FCAppendix.PayOnce.OwnImpact

open Finset Set
open scoped BigOperators

noncomputable def Hslope (n : ℕ) (p : ℝ) : ℝ :=
  (∑ j ∈ Finset.range n, (j : ℝ) * (1 - p) ^ (j - 1)) / n

theorem hasDerivAt_H (n : ℕ) (p : ℝ) : HasDerivAt (H n) (-Hslope n p) p := by
  have hterm (j : ℕ) : HasDerivAt (fun x : ℝ => (1 - x) ^ j)
      (-((j : ℝ) * (1 - p) ^ (j - 1))) p := by
    convert ((hasDerivAt_id p).const_sub 1).pow j using 1 <;> first | rfl | (simp only [id_eq]; ring)
  have hs := (HasDerivAt.fun_sum (fun j (_ : j ∈ range n) => hterm j)).div_const (n : ℝ)
  convert hs using 1 <;> first | rfl | simp [Hslope, Finset.sum_neg_distrib, neg_div]

theorem Hslope_bounds {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    1 / (n : ℝ) ≤ Hslope n p ∧ Hslope n p ≤ n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hterm (j : ℕ) : 0 ≤ (j : ℝ) * (1 - p) ^ (j - 1) :=
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (sub_nonneg.mpr hp.2) _)
  constructor
  · apply div_le_div_of_nonneg_right _ hnR.le
    have hh := single_le_sum (s := range n) (fun j _ => hterm j)
      (show 1 ∈ range n by simp; omega)
    simpa using hh
  · apply (div_le_iff₀ hnR).mpr
    calc
      (∑ j ∈ range n, (j : ℝ) * (1 - p) ^ (j - 1)) ≤ ∑ _j ∈ range n, (n : ℝ) := by
        apply sum_le_sum
        intro j hj
        have hjn : (j : ℝ) ≤ n := by exact_mod_cast (mem_range.mp hj).le
        have hpow : (1 - p) ^ (j - 1) ≤ 1 :=
          pow_le_one₀ (sub_nonneg.mpr hp.2) (by linarith [hp.1])
        exact (mul_le_of_le_one_right (Nat.cast_nonneg j) hpow).trans hjn
      _ = (n : ℝ) * n := by simp

theorem Hslope_pos {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    0 < Hslope n p :=
  (one_div_pos.mpr (Nat.cast_pos.mpr (show 0 < n by omega))).trans_le (Hslope_bounds hn hp).1

theorem neg_deriv_H_eq_Hslope (n : ℕ) (p : ℝ) : -deriv (H n) p = Hslope n p := by
  rw [(hasDerivAt_H n p).deriv, neg_neg]

theorem exists_other_interior {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (c : ℕ) (hp : ∀ i, p i ∈ Icc (0 : ℝ) 1)
    (hcap : ∑ i, p i = c) (i : ι) (hi : p i ∈ Ioo (0 : ℝ) 1) :
    ∃ j, j ≠ i ∧ p j ∈ Ioo (0 : ℝ) 1 := by
  classical
  by_contra hnot
  have hends (j : ι) (hj : j ≠ i) : p j = 0 ∨ p j = 1 := by
    by_contra he
    have hn0 : p j ≠ 0 := fun hh => he (Or.inl hh)
    have hn1 : p j ≠ 1 := fun hh => he (Or.inr hh)
    exact hnot ⟨j, hj, lt_of_le_of_ne (hp j).1 hn0.symm,
      lt_of_le_of_ne (hp j).2 hn1⟩
  let J := (univ.erase i).filter fun j => p j = 1
  have hs : ∑ j ∈ univ.erase i, p j = (J.card : ℝ) := by
    calc
      _ = ∑ j ∈ univ.erase i, if p j = 1 then (1 : ℝ) else 0 := by
        apply sum_congr rfl
        intro j hj
        rcases hends j (mem_erase.mp hj).1 with hz | ho
        · simp [hz]
        · simp [ho]
      _ = _ := by simp [J]
  have hsum : p i + (J.card : ℝ) = (c : ℝ) := by
    rw [← hs]
    exact (add_sum_erase univ p (mem_univ i)).trans hcap
  have hjc : (J.card : ℝ) < c := by linarith [hi.1]
  have hjcNat : J.card < c := by exact_mod_cast hjc
  have hnext : (J.card : ℝ) + 1 ≤ c := by exact_mod_cast (Nat.succ_le_of_lt hjcNat)
  linarith [hi.2]

noncomputable def sensitivity (n : ℕ) (b p : ℝ) : ℝ := 1 / (b * Hslope n p)

theorem sensitivity_pos {n : ℕ} (hn : 2 ≤ n) {b p : ℝ}
    (hb : 0 < b) (hp : p ∈ Icc (0 : ℝ) 1) : 0 < sensitivity n b p :=
  one_div_pos.mpr (mul_pos hb (Hslope_pos hn hp))

theorem sensitivity_ratio_bound {n : ℕ} (hn : 2 ≤ n) {b a p q : ℝ}
    (hb : 0 < b) (ha : 0 < a) (hp : p ∈ Icc (0 : ℝ) 1)
    (hq : q ∈ Icc (0 : ℝ) 1) (he : b * H n p = a * H n q) :
    sensitivity n b p ≤ (n : ℝ) ^ 3 * sensitivity n a q := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hpH := H_bounds n hn0 p hp.1 hp.2
  have hqH := H_bounds n hn0 q hq.1 hq.2
  have hba : a ≤ (n : ℝ) * b := by
    have ha1 := mul_le_mul_of_nonneg_left hqH.1 ha.le
    have hb1 := mul_le_mul_of_nonneg_left hpH.2 hb.le
    have har : a / (n : ℝ) ≤ b := by
      rw [mul_one] at hb1
      rw [← he] at ha1
      simpa [div_eq_mul_inv] using ha1.trans hb1
    exact (div_le_iff₀ hnR).mp har |>.trans_eq (mul_comm _ _)
  have hslp := Hslope_bounds hn hp
  have hslq := Hslope_bounds hn hq
  have hsratio : Hslope n q ≤ (n : ℝ) ^ 2 * Hslope n p := by
    have hh := (div_le_iff₀ hnR).mp hslp.1
    have hh' := mul_le_mul_of_nonneg_left hh hnR.le
    nlinarith
  have hden : a * Hslope n q ≤ (n : ℝ) ^ 3 * (b * Hslope n p) := by
    have hh := mul_le_mul hba hsratio (Hslope_pos hn hq).le (mul_nonneg hnR.le hb.le)
    nlinarith [hh]
  have hd1 := mul_pos hb (Hslope_pos hn hp)
  have hd2 := mul_pos ha (Hslope_pos hn hq)
  unfold sensitivity
  rw [mul_one_div]
  exact (div_le_div_iff₀ hd1 hd2).mpr (by simpa using hden)

theorem normalized_weight_gap {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (d : ι → ℝ) (hpos : ∀ i ∈ I, 0 < d i)
    {i j : ι} (hi : i ∈ I) (hj : j ∈ I) (hji : j ≠ i)
    {C : ℝ} (hC : 0 ≤ C) (hij : d i ≤ C * d j) :
    1 / (C + 1) ≤ 1 - d i / (∑ l ∈ I, d l) := by
  have hspos : 0 < ∑ l ∈ I, d l :=
    sum_pos' (fun l hl => (hpos l hl).le) ⟨i, hi, hpos i hi⟩
  have hpairs : d i + d j ≤ ∑ l ∈ I, d l := by
    have hh := sum_le_sum_of_subset_of_nonneg
      (show ({i, j} : Finset ι) ⊆ I by simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]; exact ⟨hi, hj⟩)
      (fun l hl _ => (hpos l hl).le)
    simpa [hji, hji.symm] using hh
  apply (div_le_iff₀ (by linarith : 0 < C + 1)).mpr
  apply (mul_le_mul_iff_right₀ hspos).mp
  field_simp
  nlinarith [mul_nonneg hC (sub_nonneg.mpr hpairs)]

noncomputable def interiorSet {ι : Type*} [Fintype ι] (p : ι → ℝ) : Finset ι :=
  Finset.univ.filter fun i => 0 < p i ∧ p i < 1

noncomputable def impactWeight {ι : Type*} [Fintype ι]
    (n : ℕ) (b p : ι → ℝ) (i : ι) : ℝ :=
  sensitivity n (b i) (p i) /
    ∑ j ∈ interiorSet p, sensitivity n (b j) (p j)

theorem sum_impactWeight_le_one {ι : Type*} [Fintype ι]
    (n : ℕ) (b p : ι → ℝ) :
    ∑ i ∈ interiorSet p, impactWeight n b p i ≤ 1 := by
  classical
  unfold impactWeight
  rw [← sum_div]
  by_cases hz : (∑ i ∈ interiorSet p, sensitivity n (b i) (p i)) = 0
  · rw [hz]
    norm_num
  · rw [div_self hz]

theorem impactWeight_gap {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (hn : 2 ≤ n) (b p : ι → ℝ) (hb : ∀ i, 0 < b i)
    {L : ℝ} (hL : 0 < L) (hkernel : ∀ i, p i = CommonList.kernel n (b i) L)
    (c : ℕ) (hcap : ∑ i, p i = c) (i : ι) (hi : p i ∈ Ioo (0 : ℝ) 1) :
    1 / ((n : ℝ) ^ 3 + 1) ≤ 1 - impactWeight n b p i := by
  have hp (j : ι) : p j ∈ Icc (0 : ℝ) 1 := by
    rw [hkernel j]
    exact ⟨CommonList.kernel_nonneg n hn (hb j) hL,
      CommonList.kernel_le_one n hn (hb j) hL⟩
  obtain ⟨j, hji, hj⟩ := exists_other_interior p c hp hcap i hi
  have hscore (l : ι) (hl : p l ∈ Ioo (0 : ℝ) 1) : b l * H n (p l) = L := by
    have hh := CommonList.scalarThreshold_kernel n hn (hb l) hL
    rw [← hkernel l] at hh
    exact hh.2.2.2.2 hl.1 hl.2
  have hij := sensitivity_ratio_bound hn (hb i) (hb j) (hp i) (hp j)
    ((hscore i hi).trans (hscore j hj).symm)
  exact normalized_weight_gap (interiorSet p) (fun l => sensitivity n (b l) (p l))
    (fun l _ => sensitivity_pos hn (hb l) (hp l))
    (by simp [interiorSet, hi.1, hi.2]) (by simp [interiorSet, hj.1, hj.2]) hji
    (by positivity) hij

theorem commonList_own_impact_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (hn : 2 ≤ n) (b : ι → ℝ) (hb : ∀ i, 0 < b i)
    (c : ℕ) (hc : c ≤ Fintype.card ι) (μ : FiniteLaw (Finset ι))
    (hμ : CommonList.PayOnceEquilibrium n c b μ) :
    (∑ i ∈ interiorSet (Proposer.marginal μ), impactWeight n b (Proposer.marginal μ) i ≤ 1) ∧
      ∀ i, Proposer.marginal μ i ∈ Ioo (0 : ℝ) 1 →
        1 / ((n : ℝ) ^ 3 + 1) ≤ 1 - impactWeight n b (Proposer.marginal μ) i := by
  obtain ⟨L, hL, hk, hsum⟩ := CommonList.equilibrium_kernel n hn b hb c hc μ hμ
  refine ⟨sum_impactWeight_le_one n b _, fun i hi => ?_⟩
  apply impactWeight_gap hn b _ hb hL hk c _ i hi
  simpa only [hk] using hsum

end FCAppendix.PayOnce.OwnImpact
