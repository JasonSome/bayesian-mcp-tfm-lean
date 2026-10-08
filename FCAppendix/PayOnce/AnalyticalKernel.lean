import FCAppendix.PayOnce.FocalDerivative

namespace FCAppendix.PayOnce.AnalyticalKernel

open MeasureTheory Filter Topology Set CommonList OwnImpact
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem exists_focal_root {n c : ℕ} (hn : 2 ≤ n) (hc : c ≤ Fintype.card ι + 1)
    (rivals : ι → ℝ) (hr : ∀ j, 0 < rivals j) {b : ℝ} (hb : 0 < b) :
    ∃ L, 0 < L ∧ kernel n b L + ∑ j, kernel n (rivals j) L = c := by
  classical
  let bids : Option ι → ℝ := fun j => j.elim b rivals
  have hpos (j : Option ι) : 0 < bids j := by cases j <;> simp [bids, hb, hr]
  obtain ⟨μ, hμ, _⟩ := exists_equilibrium n hn bids hpos c (by simpa using hc)
  obtain ⟨L, hL, _, hsum⟩ := equilibrium_kernel n hn bids hpos c (by simpa using hc) μ hμ
  exact ⟨L, hL, by simpa [bids, Fintype.sum_option] using hsum⟩

noncomputable def allocation (n c : ℕ) (hn : 2 ≤ n) (hc : c ≤ Fintype.card ι + 1)
    (rivals : ι → ℝ) (b : ℝ) : ℝ :=
  if h : 0 < b ∧ ∀ j, 0 < rivals j then
    kernel n b (exists_focal_root hn hc rivals h.2 h.1).choose else 0

theorem allocation_root {n c : ℕ} (hn : 2 ≤ n) (hc : c ≤ Fintype.card ι + 1)
    (rivals : ι → ℝ) (hr : ∀ j, 0 < rivals j) {b : ℝ} (hb : 0 < b) :
    ∃ L, 0 < L ∧ allocation n c hn hc rivals b = kernel n b L ∧
      kernel n b L + ∑ j, kernel n (rivals j) L = c := by
  refine ⟨(exists_focal_root hn hc rivals hr hb).choose,
    (exists_focal_root hn hc rivals hr hb).choose_spec.1, ?_,
    (exists_focal_root hn hc rivals hr hb).choose_spec.2⟩
  unfold allocation
  rw [dif_pos (show 0 < b ∧ ∀ j, 0 < rivals j from ⟨hb, hr⟩)]

theorem allocation_bounds {n c : ℕ} (hn : 2 ≤ n) (hc : c ≤ Fintype.card ι + 1)
    (rivals : ι → ℝ) (b : ℝ) : allocation n c hn hc rivals b ∈ Icc (0 : ℝ) 1 := by
  classical
  by_cases h : 0 < b ∧ ∀ j, 0 < rivals j
  · obtain ⟨L, hL, he, _⟩ := allocation_root hn hc rivals h.2 h.1
    rw [he]
    exact ⟨kernel_nonneg n hn h.1 hL, kernel_le_one n hn h.1 hL⟩
  · simp only [allocation, dif_neg h]
    exact ⟨le_rfl, zero_le_one⟩

theorem allocation_eq_kernel {n c : ℕ} (hn : 2 ≤ n) (hc : c ≤ Fintype.card ι + 1)
    (rivals : ι → ℝ) (hr : ∀ j, 0 < rivals j) {b L : ℝ} (hb : 0 < b) (hL : 0 < L)
    (hcap : kernel n b L + ∑ j, kernel n (rivals j) L = c) :
    allocation n c hn hc rivals b = kernel n b L := by
  obtain ⟨T, hT, he, hTcap⟩ := allocation_root hn hc rivals hr hb
  exact he.trans (focal_kernel_eq_of_roots hn b rivals hT hL hTcap hcap)

theorem le_allocation_iff {n c : ℕ} (hn : 2 ≤ n) (hc : c ≤ Fintype.card ι + 1)
    (rivals : ι → ℝ) (hr : ∀ j, 0 < rivals j) {b s : ℝ}
    (hb : 0 < b) (hs : 0 < s) (hs1 : s ≤ 1) :
    s ≤ allocation n c hn hc rivals b ↔
      ∑ j, kernel n (rivals j) (b * H n s) ≤ (c : ℝ) - s := by
  obtain ⟨L, hL, he, hcap⟩ := allocation_root hn hc rivals hr hb
  rw [he]
  exact KernelTailEvent.focal_tail_iff_rival_sum hn rivals hb hL hs hs1 hcap

theorem measurable_allocation_rivals {n c : ℕ} (hn : 2 ≤ n) (hc : c ≤ Fintype.card ι + 1)
    {b : ℝ} (hb : 0 < b) : Measurable (fun rivals : ι → ℝ => allocation n c hn hc rivals b) := by
  classical
  apply measurable_of_Ici
  intro s
  by_cases hs0 : s ≤ 0
  · have he : (fun rivals : ι → ℝ => allocation n c hn hc rivals b) ⁻¹' Ici s = Set.univ := by
      ext rivals
      simp only [mem_preimage, mem_Ici, mem_univ, iff_true]
      exact hs0.trans (allocation_bounds hn hc rivals b).1
    rw [he]
    exact MeasurableSet.univ
  have hs : 0 < s := lt_of_not_ge hs0
  by_cases hs1 : s ≤ 1
  · have he : (fun rivals : ι → ℝ => allocation n c hn hc rivals b) ⁻¹' Ici s =
        {rivals | ∀ j, 0 < rivals j} ∩
          {rivals | ∑ j, kernel n (rivals j) (b * H n s) ≤ (c : ℝ) - s} := by
      ext rivals
      simp only [mem_preimage, mem_Ici, mem_inter_iff, mem_setOf_eq]
      by_cases hr : ∀ j, 0 < rivals j
      · exact ⟨fun hh => ⟨hr, (le_allocation_iff hn hc rivals hr hb hs hs1).mp hh⟩,
          fun hh => (le_allocation_iff hn hc rivals hr hb hs hs1).mpr hh.2⟩
      · have ha : allocation n c hn hc rivals b = 0 := by
          unfold allocation
          rw [dif_neg (show ¬ (0 < b ∧ ∀ j, 0 < rivals j) from fun h => hr h.2)]
        simp only [ha, hr, false_and, iff_false]
        exact not_le_of_gt hs
    rw [he]
    have hm : MeasurableSet {rivals : ι → ℝ | ∀ j, 0 < rivals j} := by
      have he : {rivals : ι → ℝ | ∀ j, 0 < rivals j} = ⋂ j, {rivals | 0 < rivals j} := by
        ext rivals
        simp only [mem_setOf_eq, mem_iInter]
      rw [he]
      exact MeasurableSet.iInter fun j => measurableSet_lt measurable_const (measurable_pi_apply j)
    refine hm.inter (measurableSet_le ?_ measurable_const)
    apply Finset.measurable_sum
    intro j _
    exact (KernelTailEvent.continuous_kernel_bid hn
      (mul_pos hb (H_pos n (by omega) s hs.le hs1))).measurable.comp (measurable_pi_apply j)
  · have he : (fun rivals : ι → ℝ => allocation n c hn hc rivals b) ⁻¹' Ici s = ∅ := by
      ext rivals
      simp only [mem_preimage, mem_Ici, mem_empty_iff_false, iff_false]
      exact not_le_of_gt ((allocation_bounds hn hc rivals b).2.trans_lt (lt_of_not_ge hs1))
    rw [he]
    exact MeasurableSet.empty

end FCAppendix.PayOnce.AnalyticalKernel
