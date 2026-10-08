import FCAppendix.PayOnce.DummyKernel
import FCAppendix.Probability.TiltedProduct

namespace FCAppendix.PayOnce.DummyKernel
open MeasureTheory ProbabilityTheory Set CommonList KernelTailEvent
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

theorem allocation_pos_iff_rival_sum_lt {n c : ℕ} (hn : 2 ≤ n) (r : ι → ℝ)
    {b : ℝ} (hb : 0 < b) :
    0 < allocation n c hn r b ↔ ∑ i, kernel n (r i) b < (c:ℝ) := by
  obtain ⟨L,hL,he,hcap⟩ := allocation_root (c := c) hn r hb
  constructor
  · intro hp
    have hLb : L < b := by
      by_contra h
      rw [he,kernel_of_le n (le_of_not_gt h)] at hp
      exact hp.false
    have hsum : (∑ i, kernel n (r i) b) ≤ ∑ i, kernel n (r i) L :=
      Finset.sum_le_sum fun i _ => kernel_antitone_price hn hL hb hLb.le
    have hmin : ((min c (Fintype.card (Active r)+1):ℕ):ℝ) ≤ c :=
      Nat.cast_le.mpr (min_le_left _ _)
    rw [he] at hp
    linarith
  · intro hsum
    by_cases hc : c ≤ Fintype.card (Active r)+1
    · rw [min_eq_left hc] at hcap
      by_contra hp
      have hz : allocation n c hn r b = 0 :=
        le_antisymm (le_of_not_gt hp) (allocation_bounds hn r b).1
      rw [he] at hz
      have hbL := (kernel_eq_zero_iff n hn hb hL).mp hz
      have hs : (∑ i, kernel n (r i) L) ≤ ∑ i, kernel n (r i) b :=
        Finset.sum_le_sum fun i _ => kernel_antitone_price hn hb hL hbL
      linarith
    · rw [allocation_eq_one_of_room hn r hb (by omega)]
      norm_num

theorem allocation_entry_probability_eq {N n c : ℕ} (G : Measure ℝ)
    (hn : 2 ≤ n) {b : ℝ} (hb : 0 < b) :
    (Measure.pi (fun _ : Fin N => G)).real
      {r | 0 < allocation n c hn r b} =
    (Measure.pi (fun _ : Fin N => G)).real
      {r | ExponentialTilt.iidSum (fun B => kernel n B b) N r < (c:ℝ)} := by
  congr 1
  ext r
  exact allocation_pos_iff_rival_sum_lt hn r hb

theorem allocation_tail_probability_eq_iidSum {N n c : ℕ} (G : Measure ℝ)
    (hn : 2 ≤ n) {b s : ℝ} (hb : 0 < b) (hs : 0 < s) (hs1 : s ≤ 1) :
    (Measure.pi (fun _ : Fin N => G)).real
      {r | s ≤ allocation n c hn r b} =
    (Measure.pi (fun _ : Fin N => G)).real
      {r | ExponentialTilt.iidSum (fun B => kernel n B (b*H n s)) N r ≤ (c:ℝ)-s} := by
  congr 1
  ext r
  exact le_allocation_iff hn r hb hs hs1

end FCAppendix.PayOnce.DummyKernel
