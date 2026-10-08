import FCAppendix.Ample.RankMeasureTools
import FCAppendix.Ample.RateSystem
import Mathlib.Data.Finset.Powerset

noncomputable section
namespace FCAppendix.Ample.CompletionDraft
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open RankMeasureTools
open scoped BigOperators

def containsCoefficient (n k j : ℕ) : ℝ :=
  if k ≤ j then ((n-k).choose (j-k) : ℝ) / (n.choose j : ℝ) else 0

theorem containsCoefficient_nonneg (n k j : ℕ) :
    0 ≤ containsCoefficient n k j := by
  unfold containsCoefficient
  split_ifs <;> positivity

@[simp] theorem containsCoefficient_self (n k : ℕ) :
    containsCoefficient n k k = 1 / (n.choose k : ℝ) := by
  simp [containsCoefficient]

@[simp] theorem containsCoefficient_of_lt {n k j : ℕ} (h : j < k) :
    containsCoefficient n k j = 0 := by simp [containsCoefficient, not_le.mpr h]

theorem containing_subsets_card {n j : ℕ} (S : Finset (Fin n))
    (hSj : S.card ≤ j) :
    (((Finset.univ : Finset (Fin n)).powersetCard j).filter (S ⊆ ·)).card =
      (n-S.card).choose (j-S.card) := by
  simpa using Finset.card_filter_powersetCard_subset S Finset.univ j
    (Finset.subset_univ S) hSj

def allContactTail (n k : ℕ) (ν : ℕ → Measure ℝ) (h u : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 n, containsCoefficient n k j * (ν j).real (Ioc u h)

theorem tail_difference {μ : Measure ℝ} [IsFiniteMeasure μ]
    {u v h : ℝ} (huv : u ≤ v) (hvh : v ≤ h) :
    μ.real (Ioc u h) - μ.real (Ioc v h) = μ.real (Ioc u v) := by
  have hsplit : Ioc u h = Ioc u v ∪ Ioc v h := by
    ext x
    simp only [mem_Ioc, mem_union]
    constructor
    · intro hx
      rcases le_total x v with hxv | hvx
      · exact Or.inl ⟨hx.1, hxv⟩
      · by_cases he : x = v
        · exact Or.inl ⟨hx.1, he.le⟩
        · exact Or.inr ⟨lt_of_le_of_ne hvx (Ne.symm he), hx.2⟩
    · rintro (hx | hx)
      · exact ⟨hx.1, hx.2.trans hvh⟩
      · exact ⟨huv.trans_lt hx.1, hx.2⟩
  have hdis : Disjoint (Ioc u v) (Ioc v h) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact (not_lt_of_ge hx.2) hy.1
  rw [hsplit, measureReal_union hdis measurableSet_Ioc]
  ring

theorem allContactTail_gap {n k : ℕ} (hk : k ∈ Finset.Icc 1 n)
    (ν : ℕ → Measure ℝ) [∀ j, IsFiniteMeasure (ν j)]
    {u v h : ℝ} (huv : u ≤ v) (hvh : v ≤ h) :
    (ν k).real (Ioc u v) / (n.choose k : ℝ) ≤
      allContactTail n k ν h u - allContactTail n k ν h v := by
  have he : allContactTail n k ν h u - allContactTail n k ν h v =
      ∑ j ∈ Finset.Icc 1 n, containsCoefficient n k j * (ν j).real (Ioc u v) := by
    unfold allContactTail
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← mul_sub, tail_difference huv hvh]
  rw [he]
  have hsum := Finset.single_le_sum
    (f := fun j => containsCoefficient n k j * (ν j).real (Ioc u v))
    (fun j _ => mul_nonneg (containsCoefficient_nonneg n k j) measureReal_nonneg) hk
  simpa [containsCoefficient_self, div_eq_mul_inv, mul_comm] using hsum

theorem plateau_has_no_class_mass {n k : ℕ} (hk : k ∈ Finset.Icc 1 n)
    (ν : ℕ → Measure ℝ) [∀ j, IsFiniteMeasure (ν j)]
    {u v h : ℝ} (huv : u ≤ v) (hvh : v ≤ h)
    (heq : allContactTail n k ν h u = allContactTail n k ν h v) :
    (ν k).real (Ioc u v) = 0 := by
  have hC : (0 : ℝ) < n.choose k := by
    exact_mod_cast Nat.choose_pos (Finset.mem_Icc.mp hk).2
  have hh := allContactTail_gap hk ν huv hvh
  rw [heq, sub_self] at hh
  have hzero : (ν k).real (Ioc u v) ≤ 0 := by
    have hx := (div_le_iff₀ hC).mp hh
    simpa only [zero_mul] using hx
  exact le_antisymm hzero measureReal_nonneg

theorem allContactTail_continuous (n k : ℕ) (ν : ℕ → Measure ℝ)
    [∀ j, IsFiniteMeasure (ν j)]
    (hatom : ∀ j ∈ Finset.Icc 1 n, ∀ u : ℝ, ν j {u} = 0) (h : ℝ) :
    Continuous (allContactTail n k ν h) := by
  unfold allContactTail
  apply continuous_finsetSum
  intro j hj
  exact continuous_const.mul (continuous_bounded_tail (ν j) (hatom j hj) h)

theorem allContactTail_nonneg (n k : ℕ) (ν : ℕ → Measure ℝ) (h u : ℝ) :
    0 ≤ allContactTail n k ν h u := by
  exact Finset.sum_nonneg (fun j _ =>
    mul_nonneg (containsCoefficient_nonneg n k j) measureReal_nonneg)

theorem own_tail_div_le_allContactTail {n k : ℕ} (hk : k ∈ Finset.Icc 1 n)
    (ν : ℕ → Measure ℝ) (h u : ℝ) :
    (ν k).real (Ioc u h) / (n.choose k : ℝ) ≤ allContactTail n k ν h u := by
  have hs := Finset.single_le_sum
    (f := fun j => containsCoefficient n k j * (ν j).real (Ioc u h))
    (fun j _ => mul_nonneg (containsCoefficient_nonneg n k j) measureReal_nonneg) hk
  simpa only [allContactTail, containsCoefficient_self, one_div, div_eq_mul_inv,
    mul_comm, mul_one] using hs

theorem allContactTail_pos_of_own_tail {n k : ℕ} (hk : k ∈ Finset.Icc 1 n)
    (ν : ℕ → Measure ℝ) {h u : ℝ} (ht : 0 < (ν k).real (Ioc u h)) :
    0 < allContactTail n k ν h u := by
  have hc : (0 : ℝ) < n.choose k := by
    exact_mod_cast Nat.choose_pos (Finset.mem_Icc.mp hk).2
  exact (div_pos ht hc).trans_le (own_tail_div_le_allContactTail hk ν h u)

theorem plateau_level_null {n k : ℕ} (hk : k ∈ Finset.Icc 1 n)
    (ν : ℕ → Measure ℝ) [∀ j, IsFiniteMeasure (ν j)]
    (hatom : ∀ j ∈ Finset.Icc 1 n, ∀ u : ℝ, ν j {u} = 0) (h a : ℝ) :
    ν k {u | u ≤ h ∧ allContactTail n k ν h u = a} = 0 := by
  apply closed_set_null_of_interval_null (ν k) (hatom k hk)
    ((isClosed_le continuous_id continuous_const).inter
      (isClosed_eq (allContactTail_continuous n k ν hatom h) continuous_const))
  intro u hu v hv huv
  apply (measureReal_eq_zero_iff (measure_ne_top _ _)).mp
  exact plateau_has_no_class_mass hk ν huv hv.1 (hu.2.trans hv.2.symm)

theorem allContactTail_level_null {n k : ℕ} (hk : k ∈ Finset.Icc 1 n)
    (ν : ℕ → Measure ℝ) [∀ j, IsFiniteMeasure (ν j)]
    (hatom : ∀ j ∈ Finset.Icc 1 n, ∀ u : ℝ, ν j {u} = 0) (h a : ℝ)
    (hs : ∀ᵐ u ∂ν k, u ≤ h) :
    ν k {u | allContactTail n k ν h u = a} = 0 := by
  have he : {u | allContactTail n k ν h u = a} =ᵐ[ν k]
      {u | u ≤ h ∧ allContactTail n k ν h u = a} := by
    filter_upwards [hs] with u hu
    change (allContactTail n k ν h u = a) = (u ≤ h ∧ allContactTail n k ν h u = a)
    simp only [hu, true_and]
  rw [measure_congr he]
  exact plateau_level_null hk ν hatom h a

theorem allContactTail_lt_ae {n k : ℕ} (hk : k ∈ Finset.Icc 1 n)
    (ν : ℕ → Measure ℝ) [∀ j, IsFiniteMeasure (ν j)]
    (hatom : ∀ j ∈ Finset.Icc 1 n, ∀ u : ℝ, ν j {u} = 0) {h a : ℝ}
    (hs : ∀ᵐ u ∂ν k, u ≤ h)
    (hle : ∀ᵐ u ∂ν k, allContactTail n k ν h u ≤ a) :
    ∀ᵐ u ∂ν k, allContactTail n k ν h u < a := by
  have hne : ∀ᵐ u ∂ν k, allContactTail n k ν h u ≠ a := by
    rw [ae_iff]
    simpa only [not_not] using allContactTail_level_null hk ν hatom h a hs
  filter_upwards [hle, hne] with u hu hnu
  exact lt_of_le_of_ne hu hnu

theorem allContactTail_at_prefix {n k : ℕ} (hk : k ∈ Finset.Icc 1 n)
    (pi : ℕ → ℝ) (ν : ℕ → Measure ℝ) (h u : ℝ)
    (hp : ∀ j ∈ Finset.Icc 1 n, (ν j).real (Ioc u h) = if j ≤ k then pi j else 0) :
    allContactTail n k ν h u = pi k / (n.choose k : ℝ) := by
  unfold allContactTail
  rw [Finset.sum_eq_single_of_mem k hk]
  · rw [hp k hk]
    simp [containsCoefficient_self, div_eq_mul_inv, mul_comm]
  · intro j hj hne
    rw [hp j hj]
    by_cases hjk : j ≤ k
    · have hjlt : j < k := lt_of_le_of_ne hjk hne
      simp [hjk, containsCoefficient_of_lt hjlt]
    · simp [hjk]

theorem identify_boundary_from_prefix_rates {n : ℕ} (hn : 1 ≤ n)
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (pi : ℕ → ℝ)
    (hmass : ∑ k ∈ Finset.Icc 1 n, pi k = h)
    (hprefix : ∀ k ∈ Finset.Icc 1 n, pi k / (n.choose k : ℝ) = a) :
    a = h / (2 ^ n - 1) ∧
    -log a = log ((2 ^ n - 1) / h) ∧
    (∀ k ∈ Finset.Icc 1 n, pi k = boundaryMass n h k) ∧
    (∑ k ∈ Finset.Icc 1 n, (k : ℝ) * pi k) / h =
      (n : ℝ) * 2 ^ (n-1) / (2 ^ n - 1) := by
  have he : exp (-(-log a)) = a := by rw [neg_neg, exp_log ha]
  have h := upperBoundary_algebra hn hh
    (J := -log a) («π» := pi) (by intro k hk; rw [he]; exact hprefix k hk) hmass
  simpa only [he] using h

end FCAppendix.Ample.CompletionDraft
