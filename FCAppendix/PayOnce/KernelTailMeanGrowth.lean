import FCAppendix.PayOnce.PriceInteriorBounds
import FCAppendix.PayOnce.KernelDemandDerivative
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace FCAppendix.PayOnce.KernelTailMeanGrowth
open MeasureTheory ProbabilityTheory Filter Topology Set Real CommonList
open OwnImpact KernelTailEvent PriceInteriorBounds KernelDemand

theorem one_sub_H_bounds {n : ℕ} (hn : 2 ≤ n) {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) :
    s/(n:ℝ) ≤ 1-H n s ∧ 1-H n s ≤ (n:ℝ)*s := by
  by_cases hz : s = 0
  · subst s
    simp only [H_zero n (by omega),zero_div,sub_self,mul_zero,le_refl,and_self]
  have hsp : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hz)
  obtain ⟨v,hv,he⟩ := exists_hasDerivAt_eq_slope (H n) (fun v => -Hslope n v)
    hsp (fun v _ => (hasDerivAt_H n v).continuousAt.continuousWithinAt)
    (fun v _ => hasDerivAt_H n v)
  rw [H_zero n (by omega),sub_zero] at he
  have he' := (eq_div_iff hsp.ne').mp he
  have hb := Hslope_bounds hn (show v ∈ Icc (0:ℝ) 1 from ⟨hv.1.le,hv.2.le.trans hs.2⟩)
  constructor
  · have hh := mul_le_mul_of_nonneg_right hb.1 hs.1
    have hd : (1/(n:ℝ))*s = s/(n:ℝ) := by ring
    rw [hd] at hh
    nlinarith
  · have hh := mul_le_mul_of_nonneg_right hb.2 hs.1
    nlinarith

theorem kernel_interior_on_closed_block {n : ℕ} (hn : 2 ≤ n)
    {ell u U V B L : ℝ} (hell : 0 < ell) (hL : L ∈ Icc ell u)
    (hU : u < U) (hV : V < (n:ℝ)*ell) (hB : B ∈ Icc U V) :
    kernel n B L ∈ Ioo (0:ℝ) 1 := by
  apply (kernel_interior_iff hn (hell.trans_le hL.1)).mpr
  exact ⟨hL.2.trans_lt (hU.trans_le hB.1),hB.2.trans_lt
    (hV.trans_le (mul_le_mul_of_nonneg_left hL.1 (Nat.cast_nonneg n)))⟩

theorem mean_kernel_gap_ge (G : Measure ℝ) [IsProbabilityMeasure G]
    {n : ℕ} (hn : 2 ≤ n) {ell u U V L T q : ℝ}
    (hell : 0 < ell) (hL : L ∈ Icc ell u) (hT : T ∈ Icc ell u) (hLT : L ≤ T)
    (hU : u < U) (hUV : U ≤ V) (hV : V < (n:ℝ)*ell)
    (hmass : q ≤ G.real (Icc U V)) :
    q/((n:ℝ)*V)*(T-L) ≤ ∫ B, kernel n B L-kernel n B T ∂G := by
  classical
  have hLp := hell.trans_le hL.1
  have hTp := hell.trans_le hT.1
  have hVp : 0 < V := (hLp.trans_le hL.2).trans_le (hU.le.trans hUV)
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hden := mul_pos hnR hVp
  have hmono (B : ℝ) : 0 ≤ kernel n B L-kernel n B T :=
    sub_nonneg.mpr (kernel_antitone_price hn hLp hTp hLT)
  have hpoint (B : ℝ) (hB : B ∈ Icc U V) :
      (T-L)/((n:ℝ)*V) ≤ kernel n B L-kernel n B T := by
    have hBp : 0 < B := (hLp.trans_le hL.2).trans (hU.trans_le hB.1)
    have hh := price_gap_le_kernel_gap hn hBp hLp hTp
      (kernel_interior_on_closed_block hn hell hL hU hV hB)
      (kernel_interior_on_closed_block hn hell hT hU hV hB)
    rw [abs_of_nonpos (sub_nonpos.mpr hLT),neg_sub,abs_of_nonneg (hmono B)] at hh
    apply (div_le_iff₀ hden).mpr
    have hh' := hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hB.2 hnR.le) (hmono B))
    nlinarith
  let d := (T-L)/((n:ℝ)*V)
  have hd : 0 ≤ d := div_nonneg (sub_nonneg.mpr hLT) hden.le
  have hind : ∀ B, (Icc U V).indicator (fun _ => d) B ≤ kernel n B L-kernel n B T := by
    intro B
    by_cases hB : B ∈ Icc U V
    · rw [indicator_of_mem hB]
      exact hpoint B hB
    · rw [indicator_of_notMem hB]
      exact hmono B
  have hi := integral_mono_ae ((integrable_const d).indicator measurableSet_Icc)
    ((integrable_real_kernel G hn hLp).sub (integrable_real_kernel G hn hTp))
    (Eventually.of_forall hind)
  rw [integral_indicator measurableSet_Icc,setIntegral_const,smul_eq_mul] at hi
  calc
    q/((n:ℝ)*V)*(T-L) = q*d := by dsimp [d]; ring
    _ ≤ G.real (Icc U V)*d := mul_le_mul_of_nonneg_right hmass hd
    _ ≤ _ := hi

theorem tail_kernel_order_bounds {n : ℕ} (hn : 2 ≤ n) {b s : ℝ}
    (hb : 0 < b) (hs : s ∈ Icc (0:ℝ) 1) (B : ℝ) :
    kernel n B b ∈ Icc (0:ℝ) 1 ∧
      kernel n B (b*H n s) ∈ Icc (0:ℝ) 1 ∧
      kernel n B b ≤ kernel n B (b*H n s) := by
  have hHs := H_bounds n (by omega) s hs.1 hs.2
  have hprice := mul_pos hb (H_pos n (by omega) s hs.1 hs.2)
  exact ⟨kernel_bounds hn hb B,kernel_bounds hn hprice B,
    kernel_antitone_price hn hprice hb (by nlinarith [hHs.2])⟩

theorem tail_mean_growth (G : Measure ℝ) [IsProbabilityMeasure G]
    {n : ℕ} (hn : 2 ≤ n) {ell u U V b s q : ℝ}
    (hell : 0 < ell) (hb : b ∈ Icc ell u) (hbs : b*H n s ∈ Icc ell u)
    (hs : s ∈ Icc (0:ℝ) 1)
    (hU : u < U) (hUV : U ≤ V) (hV : V < (n:ℝ)*ell)
    (hq : 0 < q) (hmass : q ≤ G.real (Icc U V)) :
    (q*ell/((n:ℝ)^2*V))*s ≤ ∫ B, kernel n B (b*H n s)-kernel n B b ∂G := by
  have hbp := hell.trans_le hb.1
  have hHs := H_bounds n (by omega) s hs.1 hs.2
  have hle : b*H n s ≤ b := by nlinarith [hHs.2]
  have hm := mean_kernel_gap_ge G hn hell hbs hb hle hU hUV hV hmass
  have hVp : 0 < V := (hbp.trans_le hb.2).trans_le (hU.le.trans hUV)
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hgap : ell*s/(n:ℝ) ≤ b-b*H n s := by
    have hh := mul_le_mul_of_nonneg_left (one_sub_H_bounds hn hs).1 hbp.le
    have hmul := mul_le_mul_of_nonneg_right hb.1 (div_nonneg hs.1 hnR.le)
    calc
      ell*s/(n:ℝ) = ell*(s/(n:ℝ)) := by ring
      _ ≤ b*(s/(n:ℝ)) := hmul
      _ ≤ b*(1-H n s) := hh
      _ = b-b*H n s := by ring
  have hh := mul_le_mul_of_nonneg_left hgap
    (div_nonneg hq.le (mul_pos hnR hVp).le)
  have he : q/((n:ℝ)*V)*(ell*s/(n:ℝ)) = (q*ell/((n:ℝ)^2*V))*s := by ring
  rw [he] at hh
  exact hh.trans hm

theorem receipt_price_mem_of_small_tail {n : ℕ} (hn : 2 ≤ n)
    {ell blo bhi b s : ℝ} (hell : 0 < ell) (hlo : ell < blo)
    (hb : b ∈ Icc blo bhi)
    (hs : s ∈ Icc (0:ℝ) (min 1 ((blo-ell)/((n:ℝ)*bhi)))) :
    b*H n s ∈ Icc ell bhi := by
  have hbp : 0 < b := (hell.trans hlo).trans_le hb.1
  have hhip : 0 < bhi := hbp.trans_le hb.2
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hs1 : s ∈ Icc (0:ℝ) 1 := ⟨hs.1,hs.2.trans (min_le_left _ _)⟩
  have hHs := H_bounds n (by omega) s hs1.1 hs1.2
  have hsbound := (le_div_iff₀ (mul_pos hnR hhip)).mp (hs.2.trans (min_le_right _ _))
  have hdrop : b-b*H n s ≤ blo-ell := by
    calc
      b-b*H n s = b*(1-H n s) := by ring
      _ ≤ b*((n:ℝ)*s) := mul_le_mul_of_nonneg_left (one_sub_H_bounds hn hs1).2 hbp.le
      _ ≤ bhi*((n:ℝ)*s) := mul_le_mul_of_nonneg_right hb.2 (mul_nonneg hnR.le hs.1)
      _ ≤ blo-ell := by nlinarith [hsbound]
  exact ⟨by linarith [hb.1],(show b*H n s ≤ b by nlinarith [hHs.2]).trans hb.2⟩

theorem tail_mean_growth_on_compact (G : Measure ℝ) [IsProbabilityMeasure G]
    {n : ℕ} (hn : 2 ≤ n) {ell blo bhi U V q : ℝ}
    (hell : 0 < ell) (hlo : ell < blo) (hbb : blo ≤ bhi)
    (hU : bhi < U) (hUV : U ≤ V) (hV : V < (n:ℝ)*ell)
    (hq : 0 < q) (hmass : q ≤ G.real (Icc U V)) :
    let s₀ := min 1 ((blo-ell)/((n:ℝ)*bhi))
    let c := q*ell/((n:ℝ)^2*V)
    0 < s₀ ∧ 0 < c ∧ ∀ b ∈ Icc blo bhi, ∀ s ∈ Icc (0:ℝ) s₀,
      b*H n s ∈ Icc ell bhi ∧
      (∀ B : ℝ, kernel n B b ∈ Icc (0:ℝ) 1 ∧
        kernel n B (b*H n s) ∈ Icc (0:ℝ) 1 ∧
        kernel n B b ≤ kernel n B (b*H n s)) ∧
      c*s ≤ ∫ B, kernel n B (b*H n s)-kernel n B b ∂G := by
  dsimp only
  have hhip := (hell.trans hlo).trans_le hbb
  have hVp := hhip.trans (hU.trans_le hUV)
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  refine ⟨lt_min (by norm_num) (div_pos (sub_pos.mpr hlo) (mul_pos hnR hhip)),by positivity,?_⟩
  intro b hb s hs
  have hbs := receipt_price_mem_of_small_tail hn hell hlo hb hs
  have hs1 : s ∈ Icc (0:ℝ) 1 := ⟨hs.1,hs.2.trans (min_le_left _ _)⟩
  refine ⟨hbs,tail_kernel_order_bounds hn ((hell.trans hlo).trans_le hb.1) hs1,?_⟩
  exact tail_mean_growth G hn hell ⟨hlo.le.trans hb.1,hb.2⟩ hbs hs1 hU hUV hV hq hmass

theorem exists_tail_mean_growth_near_price (G : Measure ℝ) [IsProbabilityMeasure G]
    {n : ℕ} (hn : 2 ≤ n) {T U V q : ℝ}
    (hT : 0 < T) (hU : T < U) (hUV : U ≤ V) (hV : V < (n:ℝ)*T)
    (hq : 0 < q) (hmass : q ≤ G.real (Icc U V)) :
    ∃ η s₀ c : ℝ, 0 < η ∧ η < T ∧ 0 < s₀ ∧ s₀ ≤ 1 ∧ 0 < c ∧
      ∀ b ∈ Icc (T-η) (T+η), ∀ s ∈ Icc (0:ℝ) s₀,
        Measurable (fun B : ℝ => kernel n B b) ∧
        Measurable (fun B : ℝ => kernel n B (b*H n s)) ∧
        (∀ B : ℝ, kernel n B b ∈ Icc (0:ℝ) 1 ∧
          kernel n B (b*H n s) ∈ Icc (0:ℝ) 1 ∧
          kernel n B b ≤ kernel n B (b*H n s)) ∧
        c*s ≤ ∫ B, kernel n B (b*H n s)-kernel n B b ∂G := by
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hVp : 0 < V := hT.trans (hU.trans_le hUV)
  have hVT : V/(n:ℝ) < T := (div_lt_iff₀ hnR).mpr (by nlinarith [hV])
  obtain ⟨ell,hellV,hellT⟩ := exists_between hVT
  have hell : 0 < ell := (div_pos hVp hnR).trans hellV
  have hVell : V < (n:ℝ)*ell := by
    have hh := (div_lt_iff₀ hnR).mp hellV
    nlinarith
  let blo := (ell+T)/2
  let bhi := (T+U)/2
  have hlo : ell < blo := by dsimp [blo]; linarith
  have hblo : blo < T := by dsimp [blo]; linarith
  have hbhi : T < bhi := by dsimp [bhi]; linarith
  have hhi : bhi < U := by dsimp [bhi]; linarith
  let η := min (T-blo) (bhi-T)
  have hη : 0 < η := lt_min (sub_pos.mpr hblo) (sub_pos.mpr hbhi)
  have hηT : η < T := (min_le_left _ _).trans_lt (sub_lt_self T (hell.trans hlo))
  let s₀ := min 1 ((blo-ell)/((n:ℝ)*bhi))
  let c := q*ell/((n:ℝ)^2*V)
  have hc := tail_mean_growth_on_compact G hn hell hlo (hblo.le.trans hbhi.le)
    hhi hUV hVell hq hmass
  refine ⟨η,s₀,c,hη,hηT,hc.1,min_le_left _ _,hc.2.1,?_⟩
  intro b hb s hs
  have hb' : b ∈ Icc blo bhi := by
    have hηlo : η ≤ T-blo := min_le_left _ _
    have hηhi : η ≤ bhi-T := min_le_right _ _
    exact ⟨by linarith [hb.1],by linarith [hb.2]⟩
  have hstat := hc.2.2 b hb' s hs
  exact ⟨(continuous_kernel_bid hn ((hell.trans hlo).trans_le hb'.1)).measurable,
    (continuous_kernel_bid hn (hell.trans_le hstat.1.1)).measurable,hstat.2⟩

end FCAppendix.PayOnce.KernelTailMeanGrowth
