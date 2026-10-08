import FCAppendix.PayOnce.DummyKernel

namespace FCAppendix.PayOnce.DummyKernel
open MeasureTheory Set CommonList
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

noncomputable def measurableKernel (n : ℕ) (hn : 2 ≤ n) (b L : ℝ) : ℝ :=
  if 0 < b then scalarDemand n hn 1 (by norm_num) (L/b) else 0

theorem measurableKernel_eq {n : ℕ} (hn : 2 ≤ n) (b : ℝ) {L : ℝ} (hL : 0 < L) :
    measurableKernel n hn b L = kernel n b L := by
  by_cases hb : 0 < b
  · simp only [measurableKernel,if_pos hb]
    exact (KernelTailEvent.kernel_eq_scalarDemand_ratio hn hb hL).symm
  · rw [measurableKernel,if_neg hb,kernel_of_le n ((le_of_not_gt hb).trans hL.le)]

theorem measurable_measurableKernel {n : ℕ} (hn : 2 ≤ n) :
    Measurable (fun z : ℝ × ℝ => measurableKernel n hn z.1 z.2) := by
  apply Measurable.ite (measurableSet_lt measurable_const measurable_fst)
  · exact (scalarDemand_continuous n hn 1 (by norm_num)).measurable.comp (measurable_snd.div measurable_fst)
  · exact measurable_const

theorem measurable_allocation_joint {n c : ℕ} (hn : 2 ≤ n) :
    Measurable (fun z : ℝ × (ι → ℝ) => allocation n c hn z.2 z.1) := by
  classical
  apply measurable_of_Ici
  intro s
  by_cases hs0 : s ≤ 0
  · have he : (fun z : ℝ × (ι → ℝ) => allocation n c hn z.2 z.1) ⁻¹' Ici s = univ := by
      ext z
      simp only [mem_preimage,mem_Ici,mem_univ,iff_true]
      exact hs0.trans (allocation_bounds hn z.2 z.1).1
    rw [he]
    exact MeasurableSet.univ
  have hs : 0 < s := lt_of_not_ge hs0
  by_cases hs1 : s ≤ 1
  · have he : (fun z : ℝ × (ι → ℝ) => allocation n c hn z.2 z.1) ⁻¹' Ici s =
        {z | 0 < z.1} ∩
        {z | ∑ j, measurableKernel n hn (z.2 j) (z.1*H n s) ≤ (c:ℝ)-s} := by
      ext z
      simp only [mem_preimage,mem_Ici,mem_inter_iff,mem_setOf_eq]
      by_cases hb : 0 < z.1
      · have hL := mul_pos hb (H_pos n (by omega) s hs.le hs1)
        have hsum : (∑ j, measurableKernel n hn (z.2 j) (z.1*H n s)) =
            ∑ j, kernel n (z.2 j) (z.1*H n s) :=
          Finset.sum_congr rfl fun j _ => measurableKernel_eq hn _ hL
        rw [hsum]
        exact ⟨fun h => ⟨hb,(le_allocation_iff hn z.2 hb hs hs1).mp h⟩,
          fun h => (le_allocation_iff hn z.2 hb hs hs1).mpr h.2⟩
      · rw [allocation_eq_zero_of_nonpos hn z.2 (le_of_not_gt hb)]
        simp only [hb,false_and,iff_false]
        exact not_le_of_gt hs
    rw [he]
    refine (measurableSet_lt measurable_const measurable_fst).inter (measurableSet_le ?_ measurable_const)
    apply Finset.measurable_sum
    intro j _
    have hm : Measurable (fun z : ℝ × (ι → ℝ) => (z.2 j,z.1*H n s)) :=
      ((measurable_pi_apply j).comp measurable_snd).prodMk (measurable_fst.mul_const (H n s))
    exact (measurable_measurableKernel hn).comp hm
  · have he : (fun z : ℝ × (ι → ℝ) => allocation n c hn z.2 z.1) ⁻¹' Ici s = ∅ := by
      ext z
      simp only [mem_preimage,mem_Ici,mem_empty_iff_false,iff_false]
      exact not_le_of_gt ((allocation_bounds hn z.2 z.1).2.trans_lt (lt_of_not_ge hs1))
    rw [he]
    exact MeasurableSet.empty

end FCAppendix.PayOnce.DummyKernel
