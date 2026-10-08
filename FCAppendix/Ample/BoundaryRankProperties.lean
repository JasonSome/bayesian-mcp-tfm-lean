import FCAppendix.Ample.BoundaryRankContact

noncomputable section
namespace FCAppendix.Bayes.RankLimit
open MeasureTheory ProbabilityTheory Game Set Filter Topology Real
open scoped BigOperators
open Ample Ample.CompletionDraft
variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed] {M C : ℕ → ℕ}
    {Γ : ∀ t, FiniteGame (M t) n (C t) Seed} {pi : ℕ → ℝ} {h : ℝ}
    {nu : ℕ → Measure ℝ} (hr : RankLimit Γ pi h nu)

include hr

theorem allContact_continuous (k : ℕ) :
    Continuous (allContactTail n k nu h) := by
  unfold allContactTail
  apply continuous_finsetSum
  intro j hj
  exact continuous_const.mul (hr.continuous_tail hj)

theorem allContact_gap {k : ℕ} (hk : k ∈ Finset.Icc 1 n)
    {u v : ℝ} (huv : u ≤ v) (hvh : v ≤ h) :
    (nu k).real (Ioc u v)/(n.choose k:ℝ) ≤
      allContactTail n k nu h u - allContactTail n k nu h v := by
  classical
  let ν : ℕ → Measure ℝ := fun j => if j ∈ Finset.Icc 1 n then nu j else 0
  letI (j : ℕ) : IsFiniteMeasure (ν j) := by
    by_cases hj : j ∈ Finset.Icc 1 n
    · simpa only [ν, if_pos hj] using hr.finite hj
    · simp only [ν, if_neg hj]
      infer_instance
  have he (x : ℝ) : allContactTail n k ν h x = allContactTail n k nu h x := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [ν, if_pos hj]
  simpa only [he, ν, if_pos hk] using allContactTail_gap hk ν huv hvh

theorem allContact_level_null {k : ℕ} (hk : k ∈ Finset.Icc 1 n) (a : ℝ) :
    nu k {u | allContactTail n k nu h u = a} = 0 := by
  classical
  let ν : ℕ → Measure ℝ := fun j => if j ∈ Finset.Icc 1 n then nu j else 0
  letI (j : ℕ) : IsFiniteMeasure (ν j) := by
    by_cases hj : j ∈ Finset.Icc 1 n
    · simpa only [ν, if_pos hj] using hr.finite hj
    · simp only [ν, if_neg hj]
      infer_instance
  have hatom : ∀ j ∈ Finset.Icc 1 n, ∀ u : ℝ, ν j {u} = 0 := by
    intro j hj u
    simpa only [ν, if_pos hj] using hr.atomless hj u
  have he (u : ℝ) : allContactTail n k ν h u = allContactTail n k nu h u := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [ν, if_pos hj]
  have hs : ∀ᵐ u ∂ν k, u ≤ h := by
    simpa only [ν, if_pos hk] using (hr.supported hk).mono (fun _ hu => hu.2)
  simpa only [ν, if_pos hk, he] using allContactTail_level_null hk ν hatom h a hs

theorem used_allContact_positive {k : ℕ} (hk : k ∈ Finset.Icc 1 n) :
    ∀ᵐ u ∂nu k, 0 < u ∧ u < h ∧ 0 < allContactTail n k nu h u := by
  filter_upwards [hr.used_tail_positive hk] with u hu
  exact ⟨hu.1, hu.2.1, allContactTail_pos_of_own_tail hk nu hu.2.2⟩

theorem used_allContact_lt_of_le {k : ℕ} (hk : k ∈ Finset.Icc 1 n) {a : ℝ}
    (hle : ∀ᵐ u ∂nu k, allContactTail n k nu h u ≤ a) :
    ∀ᵐ u ∂nu k, allContactTail n k nu h u < a := by
  have hne : ∀ᵐ u ∂nu k, allContactTail n k nu h u ≠ a := by
    rw [ae_iff]
    simpa only [not_not] using hr.allContact_level_null hk a
  filter_upwards [hle, hne] with u hu hnu
  exact lt_of_le_of_ne hu hnu

end FCAppendix.Bayes.RankLimit

namespace FCAppendix.Ample.CompletionDraft
open Filter Topology Real

theorem boundary_finite_tilt_gap {A a : ℝ} (hA : 0 ≤ A) (ha : a ≤ 1)
    (hgap : A < a) :
    ∃ θ : ℝ, 0 ≤ θ ∧ 0 < A+(1-A)*exp (-θ) ∧
      A+(1-A)*exp (-θ) < a := by
  have hA1 : A < 1 := hgap.trans_le ha
  have ht : Tendsto (fun θ : ℝ => A+(1-A)*exp (-θ)) atTop (𝓝 A) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_exp_neg_atTop_nhds_zero.const_mul (1-A)).const_add A
  obtain ⟨θ, hθ, hθa⟩ := ((eventually_ge_atTop (0:ℝ)).and
    (ht.eventually_lt_const hgap)).exists
  exact ⟨θ, hθ, add_pos_of_nonneg_of_pos hA
    (mul_pos (sub_pos.mpr hA1) (exp_pos _)), hθa⟩

end FCAppendix.Ample.CompletionDraft
