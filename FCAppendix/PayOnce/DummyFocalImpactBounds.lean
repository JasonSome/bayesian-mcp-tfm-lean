import FCAppendix.PayOnce.FocalImpactBounds
import FCAppendix.PayOnce.DummyWeightedDerivative

namespace FCAppendix.PayOnce.DummyKernel
open MeasureTheory Set Filter Topology CommonList OwnImpact RareSuccessSlope TruncatedFOC
open KernelLawConvergence KernelTailEvent
open AnalyticalKernel (root_mem_Icc_of_rival_errors kernel_interior_of_window slope_correction_bounds phi_pos_interior)
open scoped BigOperators

theorem slope_correction_le_rival_errors
    {N n c : ℕ} (hN : 0 < N) (hn : 2 ≤ n)
    (r : Fin N → ℝ) {b L η a z Dlo Dhi δlo δhi q m w : ℝ}
    (hb : 0 < b) (hreg : RegularClearing n c r b)
    (hlo : 0 < L-η) (hhi : 0 < L+η)
    (ha : L+η < a) (hz : z < (n:ℝ)*(L-η))
    (hδlo : 0 < δlo) (hδhi : 0 < δhi) (hq : 0 < q) (hm : q ≤ m)
    (hclo : (c:ℝ)/N ≤ Dlo-δlo) (hchi : Dhi+δhi ≤ ((c:ℝ)-1)/N)
    (hw : w ∈ Icc (0:ℝ) 1)
    (hweight : b*deriv (fun x => success n (allocation n c hn r x)) b =
      weightedSlope n (allocation n c hn r b) w) :
    baseSlope n (allocation n c hn r b)-weightedSlope n (allocation n c hn r b) w ≤
      (n:ℝ)^2*(2*(n:ℝ)^3/(q*N) +
        |(∑ j, kernel n (r j) (L-η))/(N:ℝ)-Dlo|/δlo +
        |(∑ j, kernel n (r j) (L+η))/(N:ℝ)-Dhi|/δhi +
        2*|((Finset.univ.filter fun j => r j ∈ Ioo a z).card:ℝ)/N-m|/q) := by
  classical
  let J := Finset.univ.filter fun j => r j ∈ Ioo a z
  let e₀ := |(∑ j, kernel n (r j) (L-η))/(N:ℝ)-Dlo|/δlo
  let e₁ := |(∑ j, kernel n (r j) (L+η))/(N:ℝ)-Dhi|/δhi
  let e₂ := 2*|(J.card:ℝ)/N-m|/q
  let s := 2*(n:ℝ)^3/(q*N)
  have he₀ : 0 ≤ e₀ := by positivity
  have he₁ : 0 ≤ e₁ := by positivity
  have he₂ : 0 ≤ e₂ := by positivity
  have hs : 0 ≤ s := by positivity
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hpb := allocation_bounds (c := c) hn r b
  have hcor := slope_correction_bounds hn hpb hw
  have hcoarse : baseSlope n (allocation n c hn r b)-
      weightedSlope n (allocation n c hn r b) w ≤ (n:ℝ)^2 :=
    hcor.2.trans (mul_le_of_le_one_right (sq_nonneg _) hw.2)
  change _ ≤ (n:ℝ)^2*(s+e₀+e₁+e₂)
  have hbad (h : 1 ≤ s+e₀+e₁+e₂) :
      baseSlope n (allocation n c hn r b)-weightedSlope n (allocation n c hn r b) w ≤
        (n:ℝ)^2*(s+e₀+e₁+e₂) :=
    hcoarse.trans (le_mul_of_one_le_right (sq_nonneg _) h)
  by_cases hloerr : |(∑ j, kernel n (r j) (L-η))/(N:ℝ)-Dlo| < δlo
  swap
  · have he : 1 ≤ e₀ := (le_div_iff₀ hδlo).mpr (by simpa using le_of_not_gt hloerr)
    exact hbad (by linarith)
  by_cases hhierr : |(∑ j, kernel n (r j) (L+η))/(N:ℝ)-Dhi| < δhi
  swap
  · have he : 1 ≤ e₁ := (le_div_iff₀ hδhi).mpr (by simpa using le_of_not_gt hhierr)
    exact hbad (by linarith)
  by_cases hcount : q*(N:ℝ)/2 ≤ J.card
  swap
  · have hcnt : (J.card:ℝ)/N < q/2 := (div_lt_iff₀ hNR).mpr (by linarith [lt_of_not_ge hcount])
    have habs : q/2 ≤ |(J.card:ℝ)/N-m| := by
      have hh := neg_le_abs ((J.card:ℝ)/N-m)
      linarith
    have he : 1 ≤ e₂ := (le_div_iff₀ hq).mpr (by nlinarith)
    exact hbad (by linarith)
  have hcapacity : c ≤ Fintype.card (Active r)+1 := by
    by_contra hbadcap
    have hs : (∑ j, kernel n (r j) (L-η)) ≤ (c:ℝ) := by
      have hcard : (Fintype.card (Active r):ℝ) ≤ c := by
        exact_mod_cast (show Fintype.card (Active r) ≤ c by omega)
      exact (sum_kernel_le_active_card hn r hlo).trans hcard
    have hh := div_le_div_of_nonneg_right hs hNR.le
    have he := (abs_lt.mp hloerr).1
    linarith
  obtain ⟨hr,T,hT,hcapA,_hzero,_hone,hclip0,hclip1⟩ := hreg
  have hcap := hcapA
  rw [sum_active r hT, min_eq_left hcapacity] at hcap
  have hbracket := root_mem_Icc_of_rival_errors hN hn r hb hT hlo hhi hcap hclo hchi hloerr hhierr
  have hp : allocation n c hn r b = kernel n b T :=
    AnalyticalKernel.allocation_eq_kernel hn (min_le_right c _) _ hr hb hT hcapA
  by_cases hi : kernel n b T ∈ Ioo (0:ℝ) 1
  swap
  · have hi' : ¬(0 < allocation n c hn r b ∧ allocation n c hn r b < 1) := by
      simpa only [hp, mem_Ioo] using hi
    simp only [baseSlope, weightedSlope, if_neg hi', sub_self]
    positivity
  let JA := Finset.univ.filter fun j : Active r => r j.val ∈ Ioo a z
  have hJAcard : JA.card = J.card := by
    apply Finset.card_bij (fun j _ => j.val)
    · intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hj).2⟩
    · intro i _ j _ hij
      exact Subtype.ext hij
    · intro j hj
      have hwindow := (Finset.mem_filter.mp hj).2
      have hpositive : 0 < r j := hhi.trans (ha.trans hwindow.1)
      exact ⟨⟨j,hpositive⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hwindow⟩,rfl⟩
  have hJA : ∀ j ∈ JA, kernel n (r j.val) T ∈ Ioo (0:ℝ) 1 := by
    intro j hj
    exact kernel_interior_of_window hn hT hbracket ha hz (Finset.mem_filter.mp hj).2
  have hshare := focalWeight_le_of_interior_subset hn (fun j : Active r => r j.val) hr hb hT hi JA hJA
    (show 0 < q*(N:ℝ)/2 by positivity) (by simpa only [hJAcard] using hcount)
  have hweq : w = focalWeight n b (kernel n b T) (rivalSensitivity n (fun j : Active r => r j.val) T) := by
    have hd := focal_success_derivative_ownImpact hn (fun j : Active r => r j.val) hr
      (allocation n c hn r) hb hT hcapA hi hclip0 hclip1
      (fun x hx => AnalyticalKernel.allocation_root hn (min_le_right c _) _ hr hx)
    rw [hp, weightedSlope, if_pos (show 0 < kernel n b T ∧ kernel n b T < 1 from hi)] at hweight
    change b*deriv _ b = phi n (kernel n b T)*(1-_) at hd
    have hφ := phi_pos_interior hn hi
    nlinarith [hweight,hd]
  have hws : w ≤ s := by
    rw [hweq]
    convert hshare using 1
    dsimp only [s]
    field_simp
  have hh := hcor.2.trans (mul_le_mul_of_nonneg_left hws (sq_nonneg _))
  exact hh.trans (mul_le_mul_of_nonneg_left (by linarith : s ≤ s+e₀+e₁+e₂) (sq_nonneg _))

end FCAppendix.PayOnce.DummyKernel
