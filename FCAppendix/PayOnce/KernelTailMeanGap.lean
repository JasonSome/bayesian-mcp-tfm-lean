import FCAppendix.PayOnce.KernelTailMeanGrowth

namespace FCAppendix.PayOnce.KernelTailMeanGap
open MeasureTheory ProbabilityTheory Set Real CommonList
open OwnImpact KernelTailEvent KernelTailMeanGrowth KernelLawConvergence KernelDemand

theorem capacity_bias_bounds {N C : ℕ} (hN : 0 < N) (hC : C ≤ N+1)
    {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) :
    -(1/(N:ℝ)) ≤ (C:ℝ)/((N:ℝ)+1)-((C:ℝ)-s)/(N:ℝ) ∧
      (C:ℝ)/((N:ℝ)+1)-((C:ℝ)-s)/(N:ℝ) ≤ 1/(N:ℝ) := by
  have hNr : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hNp : 0 < (N:ℝ)+1 := by positivity
  have hCr : (C:ℝ) ≤ (N:ℝ)+1 := by exact_mod_cast hC
  have hCp : 0 ≤ (C:ℝ)/((N:ℝ)+1) := div_nonneg (Nat.cast_nonneg C) hNp.le
  have hCu : (C:ℝ)/((N:ℝ)+1) ≤ 1 := (div_le_one hNp).mpr hCr
  have he : (C:ℝ)/((N:ℝ)+1)-((C:ℝ)-s)/(N:ℝ) =
      (s-(C:ℝ)/((N:ℝ)+1))/(N:ℝ) := by field_simp; ring
  rw [he, ← neg_div]
  exact ⟨div_le_div_of_nonneg_right (by linarith [hs.1]) hNr.le,
    div_le_div_of_nonneg_right (by linarith [hs.2]) hNr.le⟩

theorem tail_mean_gap_bounds (G : Measure ℝ) [IsProbabilityMeasure G]
    {n N C : ℕ} (hn : 2 ≤ n) (hN : 0 < N) (hC : C ≤ N+1)
    {ell blo bhi U V q b T s : ℝ}
    (hell : 0 < ell) (hlo : ell < blo)
    (hb : b ∈ Icc blo bhi) (hT : T ∈ Icc blo bhi) (hbT : b ≤ T)
    (hU : bhi < U) (hUV : U ≤ V) (hV : V < (n:ℝ)*ell)
    (hq : 0 < q) (hmass : q ≤ G.real (Icc U V))
    (hs : s ∈ Icc (0:ℝ) (min 1 ((blo-ell)/((n:ℝ)*bhi))))
    (hmean : (∫ B, kernel n B T ∂G) = (C:ℝ)/((N:ℝ)+1)) :
    q/((n:ℝ)*V)*(T-b)+(q*ell/((n:ℝ)^2*V))*s-1/(N:ℝ) ≤
      (∫ B, kernel n B (b*H n s) ∂G)-((C:ℝ)-s)/(N:ℝ) ∧
    (∫ B, kernel n B (b*H n s) ∂G)-((C:ℝ)-s)/(N:ℝ) ≤
      ((n:ℝ)/ell)*(T-b)+((n:ℝ)^2*bhi/ell)*s+1/(N:ℝ) := by
  have hbp : 0 < b := (hell.trans hlo).trans_le hb.1
  have hTp : 0 < T := (hell.trans hlo).trans_le hT.1
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hs1 : s ∈ Icc (0:ℝ) 1 := ⟨hs.1,hs.2.trans (min_le_left _ _)⟩
  have hbs := receipt_price_mem_of_small_tail hn hell hlo hb hs
  have hb' : b ∈ Icc ell bhi := ⟨hlo.le.trans hb.1,hb.2⟩
  have hT' : T ∈ Icc ell bhi := ⟨hlo.le.trans hT.1,hT.2⟩
  have hLp : 0 < b*H n s := hell.trans_le hbs.1
  have hiL := integrable_real_kernel G hn hLp
  have hib := integrable_real_kernel G hn hbp
  have hiT := integrable_real_kernel G hn hTp
  have hlo1 := tail_mean_growth G hn hell hb' hbs hs1 hU hUV hV hq hmass
  have hlo2 := mean_kernel_gap_ge G hn hell hb' hT' hbT hU hUV hV hmass
  rw [integral_sub hiL hib] at hlo1
  rw [integral_sub hib hiT] at hlo2
  have hHs := H_bounds n (by omega) s hs1.1 hs1.2
  have hLb : b*H n s ≤ b := by nlinarith [hHs.2]
  have hLT : b*H n s ≤ T := hLb.trans hbT
  have hdrop : T-b*H n s ≤ (T-b)+bhi*(n:ℝ)*s := by
    have hd := mul_le_mul_of_nonneg_left (one_sub_H_bounds hn hs1).2 hbp.le
    have hbhi := mul_le_mul_of_nonneg_right hb.2 (mul_nonneg hnR.le hs.1)
    nlinarith
  have hpoint (B : ℝ) : kernel n B (b*H n s)-kernel n B T ≤
      ((n:ℝ)/ell)*(T-b)+((n:ℝ)^2*bhi/ell)*s := by
    have hh := (le_abs_self (kernel n B (b*H n s)-kernel n B T)).trans
      (kernel_price_difference hn hell hbs.1 hT'.1 B)
    rw [abs_of_nonpos (sub_nonpos.mpr hLT),neg_sub] at hh
    have hd := mul_le_mul_of_nonneg_left hdrop (div_nonneg hnR.le hell.le)
    calc
      kernel n B (b*H n s)-kernel n B T ≤ ((n:ℝ)/ell)*(T-b*H n s) := hh
      _ ≤ ((n:ℝ)/ell)*((T-b)+bhi*(n:ℝ)*s) := hd
      _ = ((n:ℝ)/ell)*(T-b)+((n:ℝ)^2*bhi/ell)*s := by ring
  have hupper := integral_mono_ae (hiL.sub hiT)
    (integrable_const (((n:ℝ)/ell)*(T-b)+((n:ℝ)^2*bhi/ell)*s))
    (Filter.Eventually.of_forall hpoint)
  simp only [Pi.sub_apply] at hupper
  rw [integral_sub hiL hiT,integral_const,probReal_univ,one_smul] at hupper
  have hcap := capacity_bias_bounds hN hC hs1
  rw [← hmean] at hcap
  constructor <;> linarith

theorem tail_mean_gap_bounds_on_compact {n : ℕ} (hn : 2 ≤ n)
    {ell blo bhi U V q : ℝ}
    (hell : 0 < ell) (hlo : ell < blo) (hbb : blo ≤ bhi)
    (hU : bhi < U) (hUV : U ≤ V) (hV : V < (n:ℝ)*ell) (hq : 0 < q) :
    let s₀ := min 1 ((blo-ell)/((n:ℝ)*bhi))
    let α := min (q/((n:ℝ)*V)) (q*ell/((n:ℝ)^2*V))
    let β := max ((n:ℝ)/ell) ((n:ℝ)^2*bhi/ell)
    0 < s₀ ∧ s₀ ≤ 1 ∧ 0 < α ∧ 0 < β ∧
      ∀ (G : Measure ℝ) [IsProbabilityMeasure G] (N C : ℕ),
        0 < N → C ≤ N+1 → q ≤ G.real (Icc U V) →
        ∀ b ∈ Icc blo bhi, ∀ T ∈ Icc blo bhi, b ≤ T →
        ∀ s ∈ Icc (0:ℝ) s₀,
          (∫ B, kernel n B T ∂G) = (C:ℝ)/((N:ℝ)+1) →
          α*((T-b)+s)-1/(N:ℝ) ≤
            (∫ B, kernel n B (b*H n s) ∂G)-((C:ℝ)-s)/(N:ℝ) ∧
          (∫ B, kernel n B (b*H n s) ∂G)-((C:ℝ)-s)/(N:ℝ) ≤
            β*((T-b)+s)+1/(N:ℝ) := by
  dsimp only
  have hhip := (hell.trans hlo).trans_le hbb
  have hVp := hhip.trans (hU.trans_le hUV)
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hs0 : 0 < min 1 ((blo-ell)/((n:ℝ)*bhi)) :=
    lt_min (by norm_num) (div_pos (sub_pos.mpr hlo) (mul_pos hnR hhip))
  have hα : 0 < min (q/((n:ℝ)*V)) (q*ell/((n:ℝ)^2*V)) := by positivity
  have hβ : 0 < max ((n:ℝ)/ell) ((n:ℝ)^2*bhi/ell) :=
    (div_pos hnR hell).trans_le (le_max_left _ _)
  refine ⟨hs0,min_le_left _ _,hα,hβ,?_⟩
  intro G _ N C hN hC hmass b hb T hT hbT s hs hmean
  have hh := tail_mean_gap_bounds G hn hN hC hell hlo hb hT hbT hU hUV hV hq hmass hs hmean
  have hgap : 0 ≤ T-b := sub_nonneg.mpr hbT
  have hlo1 := mul_le_mul_of_nonneg_right
    (min_le_left (q/((n:ℝ)*V)) (q*ell/((n:ℝ)^2*V))) hgap
  have hlo2 := mul_le_mul_of_nonneg_right
    (min_le_right (q/((n:ℝ)*V)) (q*ell/((n:ℝ)^2*V))) hs.1
  have hhi1 := mul_le_mul_of_nonneg_right
    (le_max_left ((n:ℝ)/ell) ((n:ℝ)^2*bhi/ell)) hgap
  have hhi2 := mul_le_mul_of_nonneg_right
    (le_max_right ((n:ℝ)/ell) ((n:ℝ)^2*bhi/ell)) hs.1
  constructor <;> nlinarith [hh.1,hh.2]

end FCAppendix.PayOnce.KernelTailMeanGap
