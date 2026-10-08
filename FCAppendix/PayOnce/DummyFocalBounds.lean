import FCAppendix.PayOnce.DummyKernel
import FCAppendix.PayOnce.KernelLawConvergence

namespace FCAppendix.PayOnce.DummyKernel
open MeasureTheory Set Filter Topology CommonList KernelTailEvent KernelLawConvergence
open scoped BigOperators

theorem allocation_error_le_rival_errors
    {N n c : ℕ} (hN : 0 < N) (hn : 2 ≤ n)
    (r : Fin N → ℝ) {b L η Dlo Dhi δlo δhi : ℝ}
    (hb : 0 < b) (hL : 0 < L) (hη : 0 < η) (hηL : η ≤ L/2)
    (hδlo : 0 < δlo) (hδhi : 0 < δhi)
    (hclo : (c:ℝ)/N ≤ Dlo-δlo) (hchi : Dhi+δhi ≤ ((c:ℝ)-1)/N) :
    |allocation n c hn r b-kernel n b L| ≤
      ((n:ℝ)/(L/2))*η +
        |(∑ j, kernel n (r j) (L-η))/(N:ℝ)-Dlo|/δlo +
        |(∑ j, kernel n (r j) (L+η))/(N:ℝ)-Dhi|/δhi := by
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hlo : 0 < L-η := by linarith
  have hhi : 0 < L+η := by linarith
  have he0 : 0 ≤ ((n:ℝ)/(L/2))*η := by positivity
  have helo : 0 ≤ |(∑ j, kernel n (r j) (L-η))/(N:ℝ)-Dlo|/δlo := by positivity
  have hehi : 0 ≤ |(∑ j, kernel n (r j) (L+η))/(N:ℝ)-Dhi|/δhi := by positivity
  have hbound : |allocation n c hn r b-kernel n b L| ≤ 1 := by
    apply abs_le.mpr
    have hp := allocation_bounds (c := c) hn r b
    have hq := kernel_bounds hn hL b
    constructor <;> linarith [hp.1,hp.2,hq.1,hq.2]
  by_cases hcapacity : c ≤ Fintype.card (Active r)+1
  ·
    obtain ⟨T,hT,hp,hcap⟩ := allocation_root hn r hb
    rw [min_eq_left hcapacity] at hcap
    by_cases hTlo : T < L-η
    · have hs : (∑ j, kernel n (r j) (L-η)) ≤ c := by
        have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
          kernel_antitone_price hn hT hlo hTlo.le (b := r j))
        have hp0 := kernel_nonneg n hn hb hT
        linarith
      have hm := div_le_div_of_nonneg_right hs hNR.le
      have hd : δlo ≤ Dlo-(∑ j, kernel n (r j) (L-η))/(N:ℝ) := by linarith
      have habs : δlo ≤ |(∑ j, kernel n (r j) (L-η))/(N:ℝ)-Dlo| := by
        have hh := neg_le_abs ((∑ j, kernel n (r j) (L-η))/(N:ℝ)-Dlo)
        linarith
      have hge : 1 ≤ |(∑ j, kernel n (r j) (L-η))/(N:ℝ)-Dlo|/δlo :=
        (le_div_iff₀ hδlo).mpr (by simpa only [one_mul] using habs)
      linarith
    by_cases hThi : L+η < T
    · have hs : (c:ℝ)-1 ≤ ∑ j, kernel n (r j) (L+η) := by
        have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
          kernel_antitone_price hn hhi hT hThi.le (b := r j))
        have hp1 := kernel_le_one n hn hb hT
        linarith
      have hm := div_le_div_of_nonneg_right hs hNR.le
      have hd : δhi ≤ (∑ j, kernel n (r j) (L+η))/(N:ℝ)-Dhi := by linarith
      have habs := hd.trans (le_abs_self _)
      have hge : 1 ≤ |(∑ j, kernel n (r j) (L+η))/(N:ℝ)-Dhi|/δhi :=
        (le_div_iff₀ hδhi).mpr (by simpa only [one_mul] using habs)
      linarith
    have hTlower : L/2 ≤ T := by linarith [le_of_not_gt hTlo]
    have hnear : |T-L| ≤ η := abs_le.mpr ⟨by linarith [le_of_not_gt hTlo], by linarith [le_of_not_gt hThi]⟩
    have hk := kernel_price_difference hn (by linarith : 0 < L/2) hTlower (by linarith : L/2 ≤ L) b
    rw [hp]
    have hfac : 0 ≤ (n:ℝ)/(L/2) := by positivity
    have hh := hk.trans (mul_le_mul_of_nonneg_left hnear hfac)
    linarith
  · have hs : (∑ j, kernel n (r j) (L-η)) ≤ (c:ℝ) := by
      have hcR : (Fintype.card (Active r):ℝ) ≤ c := by
        exact_mod_cast (show Fintype.card (Active r) ≤ c by omega)
      exact (sum_kernel_le_active_card hn r hlo).trans hcR
    have hm := div_le_div_of_nonneg_right hs hNR.le
    have hd : δlo ≤ Dlo-(∑ j, kernel n (r j) (L-η))/(N:ℝ) := by linarith
    have habs : δlo ≤ |(∑ j, kernel n (r j) (L-η))/(N:ℝ)-Dlo| := by
      have hh := neg_le_abs ((∑ j, kernel n (r j) (L-η))/(N:ℝ)-Dlo)
      linarith
    have hge : 1 ≤ |(∑ j, kernel n (r j) (L-η))/(N:ℝ)-Dlo|/δlo :=
      (le_div_iff₀ hδlo).mpr (by simpa only [one_mul] using habs)
    linarith

end FCAppendix.PayOnce.DummyKernel
