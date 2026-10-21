import FCAppendix.Affine.Uniform06.LiteralSuccessLower

noncomputable section
namespace FCAppendix.Affine.Uniform06.LiteralWeakRent

open MeasureTheory Set Filter Topology
open LiteralExperiment LiteralPrefixStieltjes LiteralKernelDecomposition
open LiteralLowDuplicate LiteralSuccessLower SourceRankRates Rank
open FCAppendix.Affine.Uniform07

theorem source_floor_bounds (i : Row) {v : ℝ} (hv : 0 ≤ v) :
    LowChernoff.physicalFloor i v ∈ Icc (0:ℝ) ((69/100)*v) := by
  have hm : max 0 (v-cutoff i/200) ≤ v := max_le hv (by linarith [cutoff_pos i])
  have hc0 : 0 ≤ min (1:ℝ) (max 0 ((v-(entry i+cutoff i/400))/(cutoff i/400))) :=
    le_min (by norm_num) (le_max_left _ _)
  have hc1 : min (1:ℝ) (max 0 ((v-(entry i+cutoff i/400))/(cutoff i/400))) ≤ 1 := min_le_left _ _
  unfold LowChernoff.physicalFloor
  refine ⟨by positivity,?_⟩
  have hh := mul_le_mul_of_nonneg_left hc1
    (show 0 ≤ (69/100:ℝ)*max 0 (v-cutoff i/200) by positivity)
  have hh' := mul_le_mul_of_nonneg_left hm (show (0:ℝ) ≤ 69/100 by norm_num)
  nlinarith

theorem capped_menu_weak_rent
    {η L v b U ell B : ℝ} {S D : ℝ → ℝ}
    (hη : η ∈ Icc (0:ℝ) 1) (hL : L ∈ Ioc (0:ℝ) 1)
    (hb : 0 < b) (hmenu : b ∈ Icc ell (min v U)) (hbB : b ≤ B)
    (hell : ell ∈ Icc (0:ℝ) ((69/100)*v))
    (hSb : ∀ a ∈ Icc (0:ℝ) B, S a ≤ 1)
    (hD0 : ∀ a ∈ Icc (0:ℝ) B, 0 ≤ D a)
    (hSl : ∀ a ∈ Ioc (0:ℝ) B, L ≤ S a)
    (hDl : ∀ a ∈ Ioc (0:ℝ) B, D a ≤ L/10)
    (hIC : ∀ a ∈ Icc ell (min v U), payoff η v a (S a) (D a) ≤ payoff η v b (S b) (D b)) :
    (L/10)*b ≤ v-b := by
  have hbv : b ≤ v := hmenu.2.trans (min_le_left _ _)
  have hv : 0 < v := hb.trans_le hbv
  have hLb : L*b ≤ b := by nlinarith [mul_le_mul_of_nonneg_right hL.2 hb.le]
  by_cases hhalf : b ≤ v/2
  · nlinarith
  let a := max ell (v/2)
  have ha0 : 0 < a := (half_pos hv).trans_le (le_max_right _ _)
  have hab : a ≤ b := max_le hmenu.1 (le_of_lt (lt_of_not_ge hhalf))
  have haB : a ≤ B := hab.trans hbB
  have hav : a ≤ (69/100)*v := max_le hell.2 (by linarith)
  have harem : (31/100)*v ≤ v-a := by linarith
  have hapos : 0 ≤ v-a := by linarith
  have hamenu : a ∈ Icc ell (min v U) := ⟨le_max_left _ _,hab.trans hmenu.2⟩
  have hSa := hSl a ⟨ha0,haB⟩
  have hDa := hDl a ⟨ha0,haB⟩
  have hDa0 := hD0 a ⟨ha0.le,haB⟩
  have hDb0 := hD0 b ⟨hb.le,hbB⟩
  have hSb1 := hSb b ⟨hb.le,hbB⟩
  have hgain₁ := mul_le_mul_of_nonneg_left hSa hapos
  have hgain₂ := mul_le_mul_of_nonneg_right harem hL.1.le
  have hcost₁ := mul_le_mul_of_nonneg_left hDa ha0.le
  have hcost₂ := mul_le_mul_of_nonneg_right hav (div_nonneg hL.1.le (by norm_num : (0:ℝ) ≤ 10))
  have hcost₃ := mul_le_mul_of_nonneg_right hη.2 (mul_nonneg ha0.le hDa0)
  have hused := mul_le_mul_of_nonneg_left hSb1 (sub_nonneg.mpr hbv)
  have husedD := mul_nonneg (mul_nonneg hη.1 hb.le) hDb0
  have hic := hIC a hamenu
  unfold payoff at hic
  nlinarith [mul_nonneg (sub_nonneg.mpr hbv) hL.1.le]

theorem tendsto_exp_affine_nat {a : ℝ} (ha : 0 < a) (C : ℝ) :
    Tendsto (fun m : ℕ => Real.exp (C-(m:ℝ)*a)) atTop (𝓝 0) := by
  have hm : Tendsto (fun m : ℕ => (m:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have he := (Real.tendsto_exp_neg_atTop_nhds_zero.comp (hm.const_mul_atTop ha)).const_mul (Real.exp C)
  convert! he using 1
  · funext m
    change Real.exp (C-(m:ℝ)*a)=Real.exp C*Real.exp (-(a*(m:ℝ)))
    rw [← Real.exp_add]
    congr 1
    ring
  · simp

theorem eventually_source_rare_small (i : Row) :
    ∀ᶠ m : ℕ in atTop,
      pureRare m+equalRare i m ≤ Lm i m/10 ∧
      pureRare m < (Lm i m)^2/10000000 := by
  have ht₁ := tendsto_exp_affine_nat (by norm_num : (0:ℝ) < 6/1000000) 0
  have ht₂ := tendsto_exp_affine_nat (equalRelativeGap_pos i) (equalRateConstant i)
  have ht₃ := tendsto_exp_affine_nat (by norm_num : (0:ℝ) < 3/1000000) 0
  have hsum : Tendsto (fun m : ℕ => Real.exp (-(m:ℝ)*(6/1000000))+
      Real.exp (equalRateConstant i-(m:ℝ)*equalRelativeGap i)) atTop (𝓝 0) := by
    simpa only [zero_sub,zero_add,neg_mul] using! ht₁.add ht₂
  filter_upwards [eventually_Lm_lower i,eventually_ge_atTop (4:ℕ),
    hsum.eventually_lt_const (by norm_num : (0:ℝ) < 1/10),
    ht₃.eventually_lt_const (by norm_num : (0:ℝ) < 1/10000000)] with m hLm hm hsmall hsq
  have hL0 : 0 < Lm i m := (Real.exp_pos _).trans_le hLm
  have hP : pureRare m ≤ Real.exp (-(m:ℝ)*(6/1000000))*Lm i m := by
    have hh := mul_le_mul_of_nonneg_left hLm (Real.exp_pos (-(m:ℝ)*(6/1000000))).le
    unfold pureRare
    convert! hh using 1
    rw [← Real.exp_add]
    congr 1
    ring
  have hE : equalRare i m ≤ Real.exp (equalRateConstant i-(m:ℝ)*equalRelativeGap i)*Lm i m := by
    have hh := mul_le_mul_of_nonneg_left hLm
      (Real.exp_pos (equalRateConstant i-(m:ℝ)*equalRelativeGap i)).le
    have he : Real.exp (equalRateConstant i-(m:ℝ)*equalRelativeGap i)*
        Real.exp (-(m:ℝ)*(3/1000000))=
          Real.exp (equalRateConstant i-(m:ℝ)*LowChernoff.sourceGap i) := by
      rw [← Real.exp_add]
      congr 1
      unfold equalRelativeGap
      ring
    rw [he] at hh
    exact (Real.exp_le_exp.mpr (source_equal_exponent_upper i (by omega))).trans hh
  have hLsq : Real.exp (-(m:ℝ)*(6/1000000)) ≤ (Lm i m)^2 := by
    have hh := mul_self_le_mul_self (Real.exp_pos _).le hLm
    convert! hh using 1
    · rw [← Real.exp_add]
      congr 1
      ring
    · ring
  have hP2 : pureRare m ≤ Real.exp (-(m:ℝ)*(3/1000000))*(Lm i m)^2 := by
    have hh := mul_le_mul_of_nonneg_left hLsq (Real.exp_pos (-(m:ℝ)*(3/1000000))).le
    unfold pureRare
    convert! hh using 1
    rw [← Real.exp_add]
    congr 1
    ring
  constructor
  · have hh := mul_le_mul_of_nonneg_right hsmall.le hL0.le
    nlinarith
  · have hsq' : Real.exp (-(m:ℝ)*(3/1000000)) < 1/10000000 := by
      simpa only [zero_sub,neg_mul] using! hsq
    have hh := mul_lt_mul_of_pos_right hsq' (sq_pos_of_pos hL0)
    exact hP2.trans_lt (by simpa only [div_eq_mul_inv,mul_comm,one_mul] using hh)

theorem eventually_source_low_used_rent (i : Row) :
    ∀ᶠ m : ℕ in atTop, ∀ (G : Measure (ℝ × ℝ)) (_hG : IsProbabilityMeasure G),
      G.map Prod.fst=LowChernoff.conditionalValueLaw i →
      (∀ᵐ p ∂G, LowChernoff.physicalFloor i p.1 ≤ p.2) →
      (∀ b : ℝ, (G.map Prod.snd) {b}=0) →
      ∀ (g : GuardData) (B U : ℝ) (margin : (Fin (m-1) → Fin 4) → ℝ),
      PrefixConditions (xi i) g B → B ≤ g.multiplier-g.radius →
      B ≤ RankCutoff.Mstar i → B ≤ (501/1000:ℝ)*cutoff i →
      ∀ v b : ℝ, 0 < b → b ∈ Icc (LowChernoff.physicalFloor i v) (min v U) → b ≤ B →
      (∀ a ∈ Icc (LowChernoff.physicalFloor i v) (min v U),
        payoff (eta i) v a (sourceSuccess i m G g margin a) (sourceDuplicate i m G g margin a) ≤
          payoff (eta i) v b (sourceSuccess i m G g margin b) (sourceDuplicate i m G g margin b)) →
      (Lm i m/10)*b ≤ v-b := by
  filter_upwards [eventually_source_rare_small i,eventually_ge_atTop (4:ℕ)] with m hrare hm
  intro G hG hv hf ha g B U margin hg hBL hBM hBH v b hb hmenu hbB hIC
  letI := hG
  have hv0 : 0 ≤ v := hb.le.trans (hmenu.2.trans (min_le_left _ _))
  have hD := (source_actual_duplicate_level_and_interval i G hv hf ha hm g hg hBL hBM hBH margin).1
  apply capped_menu_weak_rent
    (show eta i ∈ Icc (0:ℝ) 1 by cases i <;> norm_num [eta,etaQ]) (Lm_mem_Ioc i hm)
    hb hmenu hbB (source_floor_bounds i hv0)
    (fun a _ => (source_first_duplicate_bounds i m G g margin a).1.2)
    (fun a _ => (source_first_duplicate_bounds i m G g margin a).2.1)
    (fun a ha' => source_actual_success_ge_Lm i hm G g hg margin ha'.1 ha'.2 (ha a))
    (fun a ha' => (hD a ha'.1 ha'.2).trans hrare.1) hIC

end FCAppendix.Affine.Uniform06.LiteralWeakRent
