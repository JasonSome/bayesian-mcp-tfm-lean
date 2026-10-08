import FCAppendix.PayOnce.AnalyticalKernel

namespace FCAppendix.PayOnce.DummyKernel
open MeasureTheory Set CommonList
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

abbrev Active (r : ι → ℝ) := {i : ι // 0 < r i}
noncomputable instance (r : ι → ℝ) : Fintype (Active r) := by
  classical
  exact Subtype.fintype _

theorem sum_active {n : ℕ} (r : ι → ℝ) {L : ℝ} (hL : 0 < L) :
    (∑ i : Active r, kernel n (r i.val) L) = ∑ i, kernel n (r i) L := by
  classical
  have h := Fintype.sum_subtype_add_sum_subtype (p := fun i => 0 < r i)
    (fun i => kernel n (r i) L)
  have hz : (∑ i : {i // ¬ 0 < r i}, kernel n (r i.val) L) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact kernel_of_le n ((le_of_not_gt i.property).trans hL.le)
  rw [hz, add_zero] at h
  exact h

theorem sum_kernel_le_active_card {n : ℕ} (hn : 2 ≤ n) (r : ι → ℝ) {L : ℝ} (hL : 0 < L) :
    (∑ i, kernel n (r i) L) ≤ (Fintype.card (Active r):ℝ) := by
  rw [← sum_active r hL]
  calc
    _ ≤ ∑ _ : Active r, (1:ℝ) := Finset.sum_le_sum fun i _ =>
      kernel_le_one n hn i.property hL
    _ = _ := by simp

noncomputable def allocation (n c : ℕ) (hn : 2 ≤ n) (r : ι → ℝ) (b : ℝ) : ℝ :=
  AnalyticalKernel.allocation n (min c (Fintype.card (Active r)+1)) hn
    (min_le_right _ _) (fun i : Active r => r i.val) b

theorem allocation_bounds {n c : ℕ} (hn : 2 ≤ n) (r : ι → ℝ) (b : ℝ) :
    allocation n c hn r b ∈ Icc (0:ℝ) 1 :=
  AnalyticalKernel.allocation_bounds hn (min_le_right _ _) _ b

theorem allocation_root {n c : ℕ} (hn : 2 ≤ n) (r : ι → ℝ) {b : ℝ} (hb : 0 < b) :
    ∃ L, 0 < L ∧ allocation n c hn r b = kernel n b L ∧
      kernel n b L + ∑ i, kernel n (r i) L = min c (Fintype.card (Active r)+1) := by
  obtain ⟨L,hL,he,hcap⟩ := AnalyticalKernel.allocation_root hn (min_le_right c _)
    (fun i : Active r => r i.val) (fun i => i.property) hb
  rw [sum_active r hL] at hcap
  exact ⟨L,hL,he,hcap⟩

theorem allocation_eq_kernel {n c : ℕ} (hn : 2 ≤ n) (r : ι → ℝ)
    {b L : ℝ} (hb : 0 < b) (hL : 0 < L)
    (hcap : kernel n b L + ∑ i, kernel n (r i) L = min c (Fintype.card (Active r)+1)) :
    allocation n c hn r b = kernel n b L := by
  obtain ⟨T,hT,he,hTcap⟩ := allocation_root hn r hb
  exact he.trans (OwnImpact.focal_kernel_eq_of_roots hn b r hT hL hTcap hcap)

theorem allocation_eq_zero_of_nonpos {n c : ℕ} (hn : 2 ≤ n) (r : ι → ℝ)
    {b : ℝ} (hb : b ≤ 0) : allocation n c hn r b = 0 := by
  unfold allocation AnalyticalKernel.allocation
  rw [dif_neg (fun h => (not_lt_of_ge hb) h.1)]

theorem allocation_eq_one_of_room {n c : ℕ} (hn : 2 ≤ n) (r : ι → ℝ)
    {b : ℝ} (hb : 0 < b) (hc : Fintype.card (Active r)+1 ≤ c) :
    allocation n c hn r b = 1 := by
  obtain ⟨L,hL,he,hcap⟩ := allocation_root hn r hb
  rw [min_eq_right hc, Nat.cast_add, Nat.cast_one] at hcap
  have hs : (∑ i, kernel n (r i) L) ≤ (Fintype.card (Active r):ℝ) := by
    rw [← sum_active r hL]
    calc
      _ ≤ ∑ _ : Active r, (1:ℝ) := Finset.sum_le_sum fun i _ =>
        kernel_le_one n hn i.property hL
      _ = _ := by simp
  have hb1 := (allocation_bounds (c := c) hn r b).2
  rw [he] at hb1 ⊢
  linarith

theorem le_allocation_iff {n c : ℕ} (hn : 2 ≤ n) (r : ι → ℝ)
    {b s : ℝ} (hb : 0 < b) (hs : 0 < s) (hs1 : s ≤ 1) :
    s ≤ allocation n c hn r b ↔
      ∑ i, kernel n (r i) (b * H n s) ≤ (c:ℝ)-s := by
  have hscore : 0 < b * H n s := mul_pos hb (H_pos n (by omega) s hs.le hs1)
  by_cases hc : c ≤ Fintype.card (Active r)+1
  · obtain ⟨L,hL,he,hcap⟩ := allocation_root hn r hb
    rw [min_eq_left hc] at hcap
    rw [he]
    exact KernelTailEvent.focal_tail_iff_rival_sum hn r hb hL hs hs1 hcap
  · have hroom : Fintype.card (Active r)+1 ≤ c := by omega
    rw [allocation_eq_one_of_room hn r hb hroom]
    constructor
    · intro _
      have hsbound : (∑ i, kernel n (r i) (b * H n s)) ≤ (Fintype.card (Active r):ℝ) := by
        rw [← sum_active r hscore]
        calc
          _ ≤ ∑ _ : Active r, (1:ℝ) := Finset.sum_le_sum fun i _ =>
            kernel_le_one n hn i.property hscore
          _ = _ := by simp
      have hcR : (Fintype.card (Active r):ℝ)+1 ≤ c := by exact_mod_cast hroom
      linarith
    · intro _
      exact hs1

theorem measurable_allocation_rivals {n c : ℕ} (hn : 2 ≤ n) {b : ℝ} (hb : 0 < b) :
    Measurable (fun r : ι → ℝ => allocation n c hn r b) := by
  classical
  apply measurable_of_Ici
  intro s
  by_cases hs0 : s ≤ 0
  · have he : (fun r : ι → ℝ => allocation n c hn r b) ⁻¹' Ici s = univ := by
      ext r
      simp only [mem_preimage,mem_Ici,mem_univ,iff_true]
      exact hs0.trans (allocation_bounds hn r b).1
    rw [he]
    exact MeasurableSet.univ
  have hs : 0 < s := lt_of_not_ge hs0
  by_cases hs1 : s ≤ 1
  · have he : (fun r : ι → ℝ => allocation n c hn r b) ⁻¹' Ici s =
        {r | ∑ i, kernel n (r i) (b * H n s) ≤ (c:ℝ)-s} := by
      ext r
      exact le_allocation_iff hn r hb hs hs1
    rw [he]
    apply measurableSet_le _ measurable_const
    apply Finset.measurable_sum
    intro i _
    exact (KernelTailEvent.continuous_kernel_bid hn
      (mul_pos hb (H_pos n (by omega) s hs.le hs1))).measurable.comp (measurable_pi_apply i)
  · have he : (fun r : ι → ℝ => allocation n c hn r b) ⁻¹' Ici s = ∅ := by
      ext r
      simp only [mem_preimage,mem_Ici,mem_empty_iff_false,iff_false]
      exact not_le_of_gt ((allocation_bounds hn r b).2.trans_lt (lt_of_not_ge hs1))
    rw [he]
    exact MeasurableSet.empty

theorem allocation_eq_positive {n c : ℕ} (hn : 2 ≤ n) (hc : c ≤ Fintype.card ι+1)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) {b : ℝ} (hb : 0 < b) :
    allocation n c hn r b = AnalyticalKernel.allocation n c hn hc r b := by
  have hp := allocation_bounds (c := c) hn r b
  have hq := AnalyticalKernel.allocation_bounds hn hc r b
  apply le_antisymm
  · by_cases hh : 0 < allocation n c hn r b
    · exact (AnalyticalKernel.le_allocation_iff hn hc r hr hb hh hp.2).mpr
        ((le_allocation_iff hn r hb hh hp.2).mp le_rfl)
    · exact (le_of_not_gt hh).trans hq.1
  · by_cases hh : 0 < AnalyticalKernel.allocation n c hn hc r b
    · exact (le_allocation_iff hn r hb hh hq.2).mpr
        ((AnalyticalKernel.le_allocation_iff hn hc r hr hb hh hq.2).mp le_rfl)
    · exact (le_of_not_gt hh).trans hp.1

end FCAppendix.PayOnce.DummyKernel
