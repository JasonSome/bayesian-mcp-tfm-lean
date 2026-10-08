import FCAppendix.PayOnce.DummyProfileKernel

namespace FCAppendix.PayOnce.DummyKernel
open MeasureTheory Set CommonList Bayes
open scoped BigOperators
variable {m n c : ℕ}

noncomputable def interiorCount (n c : ℕ) (hn : 2 ≤ n) (b : Fin m → ℝ) : ℝ :=
  ∑ i, if 0 < profileMarginal n c hn b i ∧ profileMarginal n c hn b i < 1 then 1 else 0

noncomputable def interiorPrice (n c : ℕ) (hn : 2 ≤ n) (b : Fin m → ℝ) : ℝ :=
  (∑ i, if 0 < profileMarginal n c hn b i ∧ profileMarginal n c hn b i < 1
    then b i * H n (profileMarginal n c hn b i) else 0) / interiorCount n c hn b

theorem measurableSet_interior (hn : 2 ≤ n) (i : Fin m) :
    MeasurableSet {b : Fin m → ℝ | 0 < profileMarginal n c hn b i ∧
      profileMarginal n c hn b i < 1} :=
  (measurableSet_lt measurable_const (measurable_profileMarginal hn i)).inter
    (measurableSet_lt (measurable_profileMarginal hn i) measurable_const)

theorem measurable_interiorCount (hn : 2 ≤ n) :
    Measurable (interiorCount (m := m) n c hn) := by
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (measurableSet_interior hn i) measurable_const measurable_const

theorem measurable_interiorPrice (hn : 2 ≤ n) :
    Measurable (interiorPrice (m := m) n c hn) := by
  apply Measurable.div _ (measurable_interiorCount hn)
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (measurableSet_interior hn i)
    ((measurable_pi_apply i).mul ((continuous_H n).measurable.comp
      (measurable_profileMarginal hn i))) measurable_const

theorem interiorCount_pos_of_interior (hn : 2 ≤ n) (b : Fin m → ℝ)
    (hi : ∃ i, 0 < profileMarginal n c hn b i ∧ profileMarginal n c hn b i < 1) :
    0 < interiorCount n c hn b := by
  classical
  obtain ⟨i,hi⟩ := hi
  unfold interiorCount
  apply Finset.sum_pos'
  · intro j _
    split_ifs <;> norm_num
  · exact ⟨i,Finset.mem_univ _,by rw [if_pos hi]; norm_num⟩

theorem interiorPrice_eq_of_root (hn : 2 ≤ n) (b : Fin m → ℝ) {L : ℝ} (hL : 0 < L)
    (hp : ∀ i, profileMarginal n c hn b i = kernel n (b i) L)
    (hi : ∃ i, 0 < profileMarginal n c hn b i ∧ profileMarginal n c hn b i < 1) :
    interiorPrice n c hn b = L := by
  have hc := interiorCount_pos_of_interior hn b hi
  have he i : (if 0 < profileMarginal n c hn b i ∧ profileMarginal n c hn b i < 1
      then b i*H n (profileMarginal n c hn b i) else 0) =
      L*(if 0 < profileMarginal n c hn b i ∧ profileMarginal n c hn b i < 1 then 1 else 0) := by
    split_ifs with hi
    · have hb : 0 < b i := by
        by_contra h
        have hz := kernel_of_le n ((le_of_not_gt h).trans hL.le)
        rw [hp i,hz] at hi
        exact (lt_irrefl _) hi.1
      rw [hp i] at hi ⊢
      simpa only [mul_one] using (scalarThreshold_kernel n hn hb hL).2.2.2.2 hi.1 hi.2
    · simp only [mul_zero]
  unfold interiorPrice
  simp_rw [he]
  rw [← Finset.mul_sum]
  exact mul_div_cancel_right₀ L hc.ne'

private theorem univ_nonempty (hm : 0 < m) : (Finset.univ : Finset (Fin m)).Nonempty :=
  ⟨⟨0,hm⟩,Finset.mem_univ _⟩

noncomputable def priceSentinel (hm : 0 < m) (b : Fin m → ℝ) : ℝ :=
  max 0 (Finset.univ.sup' (univ_nonempty hm) b)+1

theorem priceSentinel_pos (hm : 0 < m) (b : Fin m → ℝ) : 0 < priceSentinel hm b := by
  unfold priceSentinel
  linarith [le_max_left (0:ℝ) (Finset.univ.sup' (univ_nonempty hm) b)]

theorem bid_le_priceSentinel (hm : 0 < m) (b : Fin m → ℝ) (i : Fin m) :
    b i ≤ priceSentinel hm b := by
  have hh := Finset.le_sup' b (Finset.mem_univ i)
  unfold priceSentinel
  linarith [le_max_right (0:ℝ) (Finset.univ.sup' (univ_nonempty hm) b)]

theorem measurable_priceSentinel (hm : 0 < m) : Measurable (priceSentinel hm) := by
  have hs : Measurable (fun b : Fin m → ℝ => Finset.univ.sup' (univ_nonempty hm) b) := by
    convert (Finset.measurable_sup' (α := ℝ) (univ_nonempty hm)
      (fun i _ => measurable_pi_apply i)) using 1
    ext b
    simp only [Finset.sup'_apply]
  exact (measurable_const.max hs).add_const 1

noncomputable def endpointPrice (n c : ℕ) (hn : 2 ≤ n) (hm : 0 < m) (b : Fin m → ℝ) : ℝ :=
  Finset.univ.inf' (univ_nonempty hm)
    (fun i => if profileMarginal n c hn b i = 1 then b i/(n:ℝ) else priceSentinel hm b)

theorem measurable_endpointPrice (hn : 2 ≤ n) (hm : 0 < m) :
    Measurable (endpointPrice n c hn hm) := by
  have h i : Measurable (fun b : Fin m → ℝ => if profileMarginal n c hn b i = 1
      then b i/(n:ℝ) else priceSentinel hm b) :=
    Measurable.ite (measurableSet_eq_fun (measurable_profileMarginal hn i) measurable_const)
      (by fun_prop) (measurable_priceSentinel hm)
  have hh : Measurable ((Finset.univ : Finset (Fin m)).inf' (univ_nonempty hm)
      (fun i (b : Fin m → ℝ) => if profileMarginal n c hn b i = 1
        then b i/(n:ℝ) else priceSentinel hm b)) :=
    Finset.measurable_sup' (α := OrderDual ℝ) (univ_nonempty hm) (fun i _ => h i)
  convert hh using 1
  ext b
  simp only [endpointPrice,Finset.inf'_apply]

theorem endpointPrice_spec (hn : 2 ≤ n) (hm : 0 < m) (b : Fin m → ℝ)
    {L : ℝ} (hL : 0 < L) (hp : ∀ i, profileMarginal n c hn b i = kernel n (b i) L)
    (hi : ¬ ∃ i, 0 < profileMarginal n c hn b i ∧ profileMarginal n c hn b i < 1) :
    0 < endpointPrice n c hn hm b ∧
      ∀ i, profileMarginal n c hn b i = kernel n (b i) (endpointPrice n c hn hm b) := by
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hpos i (hpi : profileMarginal n c hn b i = 1) : 0 < b i := by
    by_contra hb
    have hz := kernel_of_le n ((le_of_not_gt hb).trans hL.le)
    rw [hp i,hz] at hpi
    norm_num at hpi
  have hT : 0 < endpointPrice n c hn hm b := by
    unfold endpointPrice
    apply (Finset.lt_inf'_iff _).mpr
    intro i _
    split_ifs with hpi
    · exact div_pos (hpos i hpi) hnR
    · exact priceSentinel_pos hm b
  refine ⟨hT,fun i => ?_⟩
  have hpi := profileMarginal_bounds (c := c) hn b i
  have he : profileMarginal n c hn b i = 0 ∨ profileMarginal n c hn b i = 1 := by
    by_contra h
    push Not at h
    exact hi ⟨i,lt_of_le_of_ne hpi.1 h.1.symm,lt_of_le_of_ne hpi.2 h.2⟩
  rcases he with he | he
  · rw [he]
    symm
    apply kernel_of_le n
    unfold endpointPrice
    apply (Finset.le_inf'_iff _ _).mpr
    intro j _
    split_ifs with hj
    · have hiL : b i ≤ L := by
        by_cases hb : 0 < b i
        · exact (kernel_eq_zero_iff n hn hb hL).mp ((hp i).symm.trans he)
        · exact (le_of_not_gt hb).trans hL.le
      exact hiL.trans ((kernel_eq_one_iff n hn (hpos j hj) hL).mp ((hp j).symm.trans hj))
    · exact bid_le_priceSentinel hm b i
  · rw [he]
    symm
    apply (kernel_eq_one_iff n hn (hpos i he) hT).mpr
    have hh := Finset.inf'_le (fun j => if profileMarginal n c hn b j = 1
      then b j/(n:ℝ) else priceSentinel hm b) (Finset.mem_univ i)
    simpa only [endpointPrice,if_pos he] using hh

noncomputable def profilePrice (n c : ℕ) (hn : 2 ≤ n) (hm : 0 < m) (b : Fin m → ℝ) : ℝ :=
  if ∃ i, 0 < profileMarginal n c hn b i ∧ profileMarginal n c hn b i < 1
    then interiorPrice n c hn b else endpointPrice n c hn hm b

theorem measurable_profilePrice (hn : 2 ≤ n) (hm : 0 < m) :
    Measurable (profilePrice n c hn hm) := by
  apply Measurable.ite _ (measurable_interiorPrice hn) (measurable_endpointPrice hn hm)
  rw [Set.setOf_exists]
  exact MeasurableSet.iUnion fun i => measurableSet_interior hn i

theorem profilePrice_spec (hn : 2 ≤ n) (hm : 0 < m) (b : Fin m → ℝ) :
    0 < profilePrice n c hn hm b ∧
      (∀ i, profileMarginal n c hn b i = kernel n (b i) (profilePrice n c hn hm b)) ∧
      (∑ i, kernel n (b i) (profilePrice n c hn hm b)) = min c (Fintype.card (Active b)) := by
  obtain ⟨L,hL,hp,hcap⟩ := profileMarginal_root (c := c) hn b
  by_cases hi : ∃ i, 0 < profileMarginal n c hn b i ∧ profileMarginal n c hn b i < 1
  · rw [profilePrice,if_pos hi,interiorPrice_eq_of_root hn b hL hp hi]
    exact ⟨hL,hp,hcap⟩
  · rw [profilePrice,if_neg hi]
    obtain ⟨hT,hTp⟩ := endpointPrice_spec hn hm b hL hp hi
    refine ⟨hT,hTp,?_⟩
    simpa only [← hTp, hp] using hcap

theorem profilePrice_eq_of_interior_root (hn : 2 ≤ n) (hm : 0 < m) (b : Fin m → ℝ)
    {L : ℝ} (hL : 0 < L)
    (hcap : (∑ i, kernel n (b i) L) = min c (Fintype.card (Active b)))
    (hi : ∃ i, 0 < kernel n (b i) L ∧ kernel n (b i) L < 1) : profilePrice n c hn hm b = L := by
  have hp := profileMarginal_eq_kernel hn b hL hcap
  have hi' : ∃ i, 0 < profileMarginal n c hn b i ∧ profileMarginal n c hn b i < 1 := by
    simpa only [hp] using hi
  rw [profilePrice,if_pos hi']
  exact interiorPrice_eq_of_root hn b hL hp hi'

end FCAppendix.PayOnce.DummyKernel
