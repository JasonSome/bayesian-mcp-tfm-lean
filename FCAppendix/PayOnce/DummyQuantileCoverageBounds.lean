import FCAppendix.PayOnce.DummyRareSuccess

namespace FCAppendix.PayOnce.DummyKernel
open MeasureTheory ProbabilityTheory Set Filter Topology CommonList
open scoped BigOperators
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]

theorem coverage_pi_map {n c : ℕ} (hn : 2 ≤ n)
    (F : Measure Ω) [IsProbabilityMeasure F] (bid : Ω → ℝ) (hbid : Measurable bid)
    {b : ℝ} (hb : 0 < b) :
    coverage n c hn (Measure.pi (fun _ : ι => F.map bid)) b =
      ∫ ω, success n (allocation n c hn (fun j => bid (ω j)) b)
        ∂Measure.pi (fun _ : ι => F) := by
  let T : (ι → Ω) → (ι → ℝ) := fun ω j => bid (ω j)
  have hT : Measurable T := measurable_pi_lambda _ fun j => hbid.comp (measurable_pi_apply j)
  have hm : (Measure.pi (fun _ : ι => F)).map T = Measure.pi (fun _ : ι => F.map bid) :=
    Measure.pi_map_pi (fun _ : ι => hbid.aemeasurable)
  rw [coverage, ← hm, integral_map hT.aemeasurable
    (show AEStronglyMeasurable (fun r : ι → ℝ => success n (allocation n c hn r b))
      ((Measure.pi fun _ : ι => F).map T) from
      ((continuous_success n).measurable.comp (measurable_allocation_rivals hn hb)).aestronglyMeasurable)]

omit [MeasurableSpace Ω] in

theorem allocation_eq_zero_of_high_count {n c : ℕ} (hn : 2 ≤ n)
    (bid : Ω → ℝ) (T : Set Ω) (ω : ι → Ω)
    {b : ℝ} (hb : 0 < b) (hhigh : ∀ v ∈ T, (n:ℝ)*b ≤ bid v)
    (hcount : (c:ℝ) < ∑ j, T.indicator (fun _ => (1:ℝ)) (ω j)) :
    allocation n c hn (fun j => bid (ω j)) b = 0 := by
  classical
  obtain ⟨L,hL,he,hcap⟩ := allocation_root (c := c) hn (fun j => bid (ω j)) hb
  rw [he]
  by_contra hz
  have hp : 0 < kernel n b L := lt_of_le_of_ne (kernel_nonneg n hn hb hL) (Ne.symm hz)
  have hLb : L < b := lt_of_not_ge fun h => by rw [kernel_of_le n h] at hp; exact lt_irrefl _ hp
  have hsum : (∑ j, T.indicator (fun _ => (1:ℝ)) (ω j)) ≤ ∑ j, kernel n (bid (ω j)) L := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : ω j ∈ T
    · rw [indicator_of_mem hj, ← kernel_of_ge n hn hb (hhigh (ω j) hj)]
      exact KernelTailEvent.kernel_antitone_price hn hL hb hLb.le
    · rw [indicator_of_notMem hj]
      exact (KernelTailEvent.kernel_bounds hn hL (bid (ω j))).1
  have hcap' := Nat.cast_le (α := ℝ).mpr (min_le_left c (Fintype.card (Active (fun j => bid (ω j)))+1))
  linarith

theorem coverage_le_high_count {n c : ℕ} (hn : 2 ≤ n)
    (F : Measure Ω) [IsProbabilityMeasure F] (bid : Ω → ℝ) (hbid : Measurable bid)
    {T : Set Ω} (hT : MeasurableSet T) {b : ℝ} (hb : 0 < b)
    (hhigh : ∀ v ∈ T, (n:ℝ)*b ≤ bid v) :
    coverage n c hn (Measure.pi (fun _ : ι => F.map bid)) b ≤
      (Measure.pi (fun _ : ι => F)).real
        {ω | ∑ j, T.indicator (fun _ => (1:ℝ)) (ω j) ≤ (c:ℝ)} := by
  classical
  let P := Measure.pi (fun _ : ι => F)
  let E := {ω : ι → Ω | ∑ j, T.indicator (fun _ => (1:ℝ)) (ω j) ≤ (c:ℝ)}
  have hE : MeasurableSet E := measurableSet_le
    (Finset.measurable_sum _ fun j _ => (measurable_const.indicator hT).comp (measurable_pi_apply j))
    measurable_const
  have hm : Measurable (fun ω : ι → Ω => allocation n c hn (fun j => bid (ω j)) b) :=
    (measurable_allocation_rivals hn hb).comp
      (measurable_pi_lambda _ fun j => hbid.comp (measurable_pi_apply j))
  have hi := UnitInterval.integrable_success P _ hm
    (fun ω => (allocation_bounds hn (fun j => bid (ω j)) b).1)
    (fun ω => (allocation_bounds hn (fun j => bid (ω j)) b).2) n
  rw [coverage_pi_map hn F bid hbid hb]
  have hh := integral_mono hi ((integrable_const (1:ℝ)).indicator hE) (fun ω => by
    by_cases he : ω ∈ E
    · rw [indicator_of_mem he]
      exact success_le_one n _ (allocation_bounds hn _ b).2
    · rw [indicator_of_notMem he, allocation_eq_zero_of_high_count hn bid T ω hb hhigh
        (lt_of_not_ge he)]
      simp only [success, sub_zero, one_pow, sub_self, le_refl])
  simpa only [integral_indicator hE, setIntegral_const, smul_eq_mul, mul_one] using hh

theorem low_count_le_coverage {n c : ℕ} (hn : 2 ≤ n)
    (F : Measure Ω) [IsProbabilityMeasure F] (bid : Ω → ℝ) (hbid : Measurable bid)
    {S : Set Ω} (hS : MeasurableSet S)
    {b s : ℝ} (hb : 0 < b) (hs : 0 < s) (hs1 : s ≤ 1)
    (hlow : ∀ v ∉ S, bid v ≤ b * H n s) :
    success n s * (Measure.pi (fun _ : ι => F)).real
      {ω | ∑ j, S.indicator (fun _ => (1:ℝ)) (ω j) ≤ (c:ℝ)-s} ≤
    coverage n c hn (Measure.pi (fun _ : ι => F.map bid)) b := by
  classical
  let P := Measure.pi (fun _ : ι => F)
  let p := fun ω : ι → Ω => allocation n c hn (fun j => bid (ω j)) b
  have hp : Measurable p := (measurable_allocation_rivals hn hb).comp
    (measurable_pi_lambda _ fun j => hbid.comp (measurable_pi_apply j))
  have hE : MeasurableSet {ω : ι → Ω |
      ∑ j, S.indicator (fun _ => (1:ℝ)) (ω j) ≤ (c:ℝ)-s} := measurableSet_le
    (Finset.measurable_sum _ fun j _ => (measurable_const.indicator hS).comp (measurable_pi_apply j))
    measurable_const
  have hsub : {ω : ι → Ω | ∑ j, S.indicator (fun _ => (1:ℝ)) (ω j) ≤ (c:ℝ)-s}
      ≤ᵐ[P] {ω | s ≤ p ω} := by
    apply Filter.Eventually.of_forall
    intro ω hcount
    apply (le_allocation_iff hn _ hb hs hs1).mpr
    apply le_trans _ hcount
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : ω j ∈ S
    · rw [indicator_of_mem hj]
      exact (KernelTailEvent.kernel_bounds hn (mul_pos hb (H_pos n (by omega) s hs.le hs1)) (bid (ω j))).2
    · rw [indicator_of_notMem hj, kernel_of_le n (hlow (ω j) hj)]
  have hmeasure : P.real {ω | ∑ j, S.indicator (fun _ => (1:ℝ)) (ω j) ≤ (c:ℝ)-s} ≤
      P.real {ω | s ≤ p ω} := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  have hlower := RareSuccessCoverage.integral_success_ge_tail P (by omega : 0 < n) hp
    (fun ω => allocation_bounds hn (fun j => bid (ω j)) b) s
  rw [coverage_pi_map hn F bid hbid hb]
  exact (mul_le_mul_of_nonneg_left hmeasure (success_pos n (by omega) s hs hs1).le).trans hlower

end FCAppendix.PayOnce.DummyKernel
