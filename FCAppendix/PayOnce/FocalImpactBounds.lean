import FCAppendix.PayOnce.FocalAllocationBounds
import FCAppendix.PayOnce.TruncatedFOC

namespace FCAppendix.PayOnce.OwnImpact
open Set CommonList
open scoped BigOperators

theorem focalWeight_le_of_interior_subset {ι : Type*} [Fintype ι]
    {n : ℕ} (hn : 2 ≤ n) (r : ι → ℝ) (hr : ∀ j, 0 < r j)
    {b L : ℝ} (hb : 0 < b) (hL : 0 < L)
    (hi : kernel n b L ∈ Ioo (0:ℝ) 1)
    (J : Finset ι) (hJ : ∀ j ∈ J, kernel n (r j) L ∈ Ioo (0:ℝ) 1)
    {q : ℝ} (hq : 0 < q) (hcount : q ≤ J.card) :
    focalWeight n b (kernel n b L) (rivalSensitivity n r L) ≤ (n:ℝ)^3/q := by
  classical
  let d := sensitivity n b (kernel n b L)
  let D := rivalSensitivity n r L
  have hd : 0 < d := sensitivity_pos hn hb ⟨hi.1.le,hi.2.le⟩
  have hD : 0 ≤ D := rivalSensitivity_nonneg hn r hr L
  have hs : (J.card:ℝ)*d ≤ (n:ℝ)^3*D := by
    have hsum : (J.card:ℝ)*d ≤ ∑ j ∈ J,
        (n:ℝ)^3*sensitivity n (r j) (kernel n (r j) L) := by
      calc
        _ = ∑ _j ∈ J, d := by simp
        _ ≤ _ := Finset.sum_le_sum fun j hj => by
          have hjp := hJ j hj
          exact sensitivity_ratio_bound hn hb (hr j) ⟨hi.1.le,hi.2.le⟩
            ⟨hjp.1.le,hjp.2.le⟩
            (((scalarThreshold_kernel n hn hb hL).2.2.2.2 hi.1 hi.2).trans
              ((scalarThreshold_kernel n hn (hr j) hL).2.2.2.2 hjp.1 hjp.2).symm)
    have hsub : (∑ j ∈ J, sensitivity n (r j) (kernel n (r j) L)) ≤ D := by
      calc
        _ = ∑ j ∈ J, if 0 < kernel n (r j) L ∧ kernel n (r j) L < 1 then
            sensitivity n (r j) (kernel n (r j) L) else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [if_pos (show 0 < kernel n (r j) L ∧ kernel n (r j) L < 1 from hJ j hj)]
        _ ≤ ∑ j, if 0 < kernel n (r j) L ∧ kernel n (r j) L < 1 then
            sensitivity n (r j) (kernel n (r j) L) else 0 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J)
          intro j _ _
          split_ifs with hj
          · exact (sensitivity_pos hn (hr j) ⟨hj.1.le,hj.2.le⟩).le
          · exact le_rfl
        _ = D := rfl
    rw [← Finset.mul_sum] at hsum
    exact hsum.trans (mul_le_mul_of_nonneg_left hsub (by positivity))
  have hqd : q*d ≤ (n:ℝ)^3*D :=
    (mul_le_mul_of_nonneg_right hcount hd.le).trans hs
  have hden : 0 < d+D := by positivity
  change d/(d+D) ≤ (n:ℝ)^3/q
  apply (div_le_div_iff₀ hden hq).mpr
  have hc : 0 ≤ (n:ℝ)^3*d := by positivity
  nlinarith

end FCAppendix.PayOnce.OwnImpact

namespace FCAppendix.PayOnce.AnalyticalKernel
open MeasureTheory Set Filter Topology CommonList OwnImpact RareSuccessSlope TruncatedFOC
open KernelLawConvergence KernelTailEvent
open scoped BigOperators

theorem root_mem_Icc_of_rival_errors
    {N n c : ℕ} (hN : 0 < N) (hn : 2 ≤ n)
    (r : Fin N → ℝ) {b L T η Dlo Dhi δlo δhi : ℝ}
    (hb : 0 < b) (hT : 0 < T) (hlo : 0 < L-η) (hhi : 0 < L+η)
    (hcap : kernel n b T + ∑ j, kernel n (r j) T = c)
    (hclo : (c:ℝ)/N ≤ Dlo-δlo) (hchi : Dhi+δhi ≤ ((c:ℝ)-1)/N)
    (helo : |(∑ j, kernel n (r j) (L-η))/(N:ℝ)-Dlo| < δlo)
    (hehi : |(∑ j, kernel n (r j) (L+η))/(N:ℝ)-Dhi| < δhi) :
    T ∈ Icc (L-η) (L+η) := by
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  constructor
  · by_contra hbad
    have hs : (∑ j, kernel n (r j) (L-η)) ≤ c := by
      have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
        kernel_antitone_price hn hT hlo (le_of_not_ge hbad) (b := r j))
      have hp0 := kernel_nonneg n hn hb hT
      linarith
    have hm := div_le_div_of_nonneg_right hs hNR.le
    have hh := (abs_lt.mp helo).1
    linarith
  · by_contra hbad
    have hs : (c:ℝ)-1 ≤ ∑ j, kernel n (r j) (L+η) := by
      have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
        kernel_antitone_price hn hhi hT (le_of_not_ge hbad) (b := r j))
      have hp1 := kernel_le_one n hn hb hT
      linarith
    have hm := div_le_div_of_nonneg_right hs hNR.le
    have hh := (abs_lt.mp hehi).2
    linarith

theorem kernel_interior_of_window {n : ℕ} (hn : 2 ≤ n)
    {b T L η a z : ℝ} (hT : 0 < T) (hbracket : T ∈ Icc (L-η) (L+η))
    (ha : L+η < a) (hz : z < (n:ℝ)*(L-η)) (hb : b ∈ Ioo a z) :
    kernel n b T ∈ Ioo (0:ℝ) 1 := by
  have hbt : T < b := hbracket.2.trans_lt (ha.trans hb.1)
  have hbpos : 0 < b := hT.trans hbt
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hbn : b < (n:ℝ)*T := hb.2.trans (hz.trans_le
    (mul_le_mul_of_nonneg_left hbracket.1 hnR.le))
  have hp := kernel_bounds hn hT b
  constructor
  · apply lt_of_le_of_ne hp.1
    intro he
    exact hbt.not_ge ((kernel_eq_zero_iff n hn hbpos hT).mp he.symm)
  · apply lt_of_le_of_ne hp.2
    intro he
    have hh := (kernel_eq_one_iff n hn hbpos hT).mp he
    have hbt' := (le_div_iff₀ hnR).mp hh
    nlinarith

theorem slope_correction_bounds {n : ℕ} (hn : 2 ≤ n) {p w : ℝ}
    (hp : p ∈ Icc (0:ℝ) 1) (hw : w ∈ Icc (0:ℝ) 1) :
    0 ≤ baseSlope n p-weightedSlope n p w ∧
      baseSlope n p-weightedSlope n p w ≤ (n:ℝ)^2*w := by
  unfold baseSlope weightedSlope
  split_ifs with hi
  · have hφ := phi_nonneg hn hp
    have hφb := phi_le_sq hn hp
    constructor
    · nlinarith [mul_nonneg hφ hw.1]
    · nlinarith [mul_le_mul_of_nonneg_right hφb hw.1]
  · exact ⟨by simp, by simpa using mul_nonneg (sq_nonneg (n:ℝ)) hw.1⟩

theorem slope_correction_le_rival_errors
    {N n c : ℕ} (hN : 0 < N) (hn : 2 ≤ n) (hc : c ≤ Fintype.card (Fin N)+1)
    (r : Fin N → ℝ) {b L η a z Dlo Dhi δlo δhi q m w : ℝ}
    (hb : 0 < b) (hreg : RegularClearing n c r b)
    (hlo : 0 < L-η) (hhi : 0 < L+η)
    (ha : L+η < a) (hz : z < (n:ℝ)*(L-η))
    (hδlo : 0 < δlo) (hδhi : 0 < δhi) (hq : 0 < q) (hm : q ≤ m)
    (hclo : (c:ℝ)/N ≤ Dlo-δlo) (hchi : Dhi+δhi ≤ ((c:ℝ)-1)/N)
    (hw : w ∈ Icc (0:ℝ) 1)
    (hweight : b*deriv (fun x => success n (allocation n c hn hc r x)) b =
      weightedSlope n (allocation n c hn hc r b) w) :
    baseSlope n (allocation n c hn hc r b)-weightedSlope n (allocation n c hn hc r b) w ≤
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
  have hpb := allocation_bounds hn hc r b
  have hcor := slope_correction_bounds hn hpb hw
  have hcoarse : baseSlope n (allocation n c hn hc r b)-
      weightedSlope n (allocation n c hn hc r b) w ≤ (n:ℝ)^2 :=
    hcor.2.trans (mul_le_of_le_one_right (sq_nonneg _) hw.2)
  change _ ≤ (n:ℝ)^2*(s+e₀+e₁+e₂)
  have hbad (h : 1 ≤ s+e₀+e₁+e₂) :
      baseSlope n (allocation n c hn hc r b)-weightedSlope n (allocation n c hn hc r b) w ≤
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
  obtain ⟨hr,T,hT,hcap,_hzero,_hone,hclip0,hclip1⟩ := hreg
  have hbracket := root_mem_Icc_of_rival_errors hN hn r hb hT hlo hhi hcap hclo hchi hloerr hhierr
  have hp := allocation_eq_kernel hn hc r hr hb hT hcap
  by_cases hi : kernel n b T ∈ Ioo (0:ℝ) 1
  swap
  · have hi' : ¬(0 < allocation n c hn hc r b ∧ allocation n c hn hc r b < 1) := by
      simpa only [hp, mem_Ioo] using hi
    simp only [baseSlope, weightedSlope, if_neg hi', sub_self]
    positivity
  have hJ : ∀ j ∈ J, kernel n (r j) T ∈ Ioo (0:ℝ) 1 := by
    intro j hj
    exact kernel_interior_of_window hn hT hbracket ha hz (Finset.mem_filter.mp hj).2
  have hshare := focalWeight_le_of_interior_subset hn r hr hb hT hi J hJ
    (show 0 < q*(N:ℝ)/2 by positivity) hcount
  have hweq : w = focalWeight n b (kernel n b T) (rivalSensitivity n r T) := by
    have hd := focal_success_derivative_ownImpact hn r hr _ hb hT hcap hi hclip0 hclip1
      (fun x hx => allocation_root hn hc r hr hx)
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

end FCAppendix.PayOnce.AnalyticalKernel
