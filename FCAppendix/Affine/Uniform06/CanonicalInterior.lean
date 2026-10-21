import FCAppendix.Affine.Uniform06.CanonicalRootAdapter

noncomputable section
namespace FCAppendix.Affine.Uniform06.CanonicalInterior

open Set
open scoped BigOperators
open FCAppendix.Affine.ClippedResidual
open EntryOwnImpact CanonicalRootAdapter EqualCanonicalRegularity

theorem scalar_threshold_eq_exposure {ξ B Λ p : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hΛ : 0 < Λ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hzero : p=0 → B*(1-ξ*p) ≤ Λ)
    (hone : p=1 → Λ ≤ B*(1-ξ*p))
    (hinterior : 0 < p → p < 1 → B*(1-ξ*p)=Λ) :
    p=exposure ξ Λ B := by
  by_cases hpz : p=0
  · have hBΛ : B ≤ Λ := by simpa only [hpz,mul_zero,sub_zero,mul_one] using hzero hpz
    rw [hpz,exposure_zero hBΛ]
  · by_cases hpo : p=1
    · have hl : Λ ≤ B*(1-ξ) := by simpa only [hpo,mul_one] using hone hpo
      have hκ : 0 < 1-ξ := sub_pos.mpr hξ1
      have hB : 0 < B := by
        by_contra hn
        have hh := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hκ.le
        linarith
      have hΛB : Λ < B := by nlinarith [mul_pos hξ hB]
      have hr : 1 ≤ (B-Λ)/(ξ*B) := (le_div_iff₀ (mul_pos hξ hB)).mpr (by nlinarith)
      rw [hpo,exposure,max_eq_left hΛB.le,max_eq_right (sub_nonneg.mpr hΛB.le),
        min_eq_left hr]
    · have hp : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hpz)
      have hpl : p < 1 := lt_of_le_of_ne hp1 hpo
      have hfactor : 0 < 1-ξ*p := by
        have hh := mul_le_mul_of_nonneg_left hp1 hξ.le
        nlinarith [hh]
      have hr := hinterior hp hpl
      have hB : 0 < B := by
        by_contra hn
        have hh := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hfactor.le
        rw [hr] at hh
        linarith
      have hΛB : Λ < B := by nlinarith [mul_pos hB (mul_pos hξ hp)]
      have hclip : (1-ξ)*B ≤ Λ := by nlinarith [mul_nonneg (mul_pos hB hξ).le (sub_nonneg.mpr hp1)]
      rw [exposure_of_between hξ hΛ hΛB hclip]
      field_simp [hξ.ne',hB.ne']
      nlinarith [hr]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma sum_remove_focal (f : ι → ℝ) (j : ι) :
    (∑ k, if k=j then 0 else f k)+f j = ∑ k, f k := by
  classical
  calc
    _ = ∑ k, ((if k=j then 0 else f k)+(if k=j then f j else 0)) := by
      rw [Finset.sum_add_distrib]
      simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k=j <;> simp [hk]

theorem actual_interior_positive_part {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (B : ι → ℝ) (j : ι) (hb : 0 < B j)
    (hp1 : EqualCapacity.positiveMarginal ξ c B j < 1) :
    EqualCapacity.positiveMarginal ξ c B j =
      max 0 ((c : ℝ)-remainingDemand ξ B {j} (B j)) /
        (1+B j*rightSecant ξ B {j}
          (B j*(1-ξ*EqualCapacity.positiveMarginal ξ c B j)) (B j)) := by
  let p := EqualCapacity.positiveMarginal ξ c B
  have hp := EqualCapacity.positiveMarginal_spec ξ c hξ hξ1 B
  obtain ⟨Λ,hΛ0,hT,hslack⟩ := EqualCapacity.positiveMarginal_threshold hξ hξ1 c B
  have hΛ : 0 < Λ := by
    by_cases hpz : p j=0
    · have hh := hT.1 j hpz
      change B j*(1-ξ*p j) ≤ Λ at hh
      simp only [hpz,mul_zero,sub_zero,mul_one] at hh
      exact hb.trans_le hh
    · have hpp : 0 < p j := lt_of_le_of_ne (hp.1 j) (Ne.symm hpz)
      have hh := hT.2.2 j hpp hp1
      have hf : 0 < 1-ξ*p j := by
        have hmul := mul_le_mul_of_nonneg_left (hp.2.1 j) hξ.le
        nlinarith [hmul]
      rw [← hh]
      exact mul_pos hb hf
  have he (k : ι) : p k=exposure ξ Λ (B k) :=
    scalar_threshold_eq_exposure hξ hξ1 hΛ (hp.1 k) (hp.2.1 k)
      (hT.1 k) (hT.2.1 k) (hT.2.2 k)
  have hsum : (∑ k, p k)=(c : ℝ) := by
    have hh : (c : ℝ)-(∑ k,p k)=0 := (mul_eq_zero.mp hslack).resolve_left hΛ.ne'
    linarith
  have hroot : remainingDemand ξ B ∅ Λ=(c : ℝ) := by
    simpa only [remainingDemand,Finset.notMem_empty,if_false,← he] using hsum
  have hfocal : remainingDemand ξ B {j} Λ+p j=(c : ℝ) := by
    rw [he j]
    simpa only [Finset.insert_empty] using
      (remainingDemand_insert ξ Λ B ∅ j (Finset.notMem_empty j)).symm.trans hroot
  by_cases hpz : p j=0
  · have hBΛ : B j ≤ Λ := by
      have hh := hT.1 j hpz
      change B j*(1-ξ*p j) ≤ Λ at hh
      simpa only [hpz,mul_zero,sub_zero,mul_one] using hh
    have hm := remainingDemand_antitone_price ξ B ∅ hξ hb hBΛ
    rw [hroot,remainingDemand_insert ξ (B j) B ∅ j (Finset.notMem_empty j),
      exposure_zero (le_refl (B j)),add_zero] at hm
    have hD : (c : ℝ)-remainingDemand ξ B {j} (B j) ≤ 0 := by simpa using sub_nonpos.mpr hm
    change p j = _
    rw [hpz,max_eq_left hD,zero_div]
  · have hpp : 0 < p j := lt_of_le_of_ne (hp.1 j) (Ne.symm hpz)
    have hprice : Λ=B j*(1-ξ*p j) := (hT.2.2 j hpp hp1).symm
    have hh := focal_right_deficit B {j} hξ hb hΛ hpp hfocal hprice
    have hK := rightSecant_nonneg (b := B j) B {j} hξ hΛ
    have hden : 0 < 1+B j*rightSecant ξ B {j} Λ (B j) := by positivity
    have hD : 0 < (c : ℝ)-remainingDemand ξ B {j} (B j) := by
      have hr := (eq_div_iff hden.ne').mp hh
      rw [← hr]
      exact mul_pos hpp hden
    change p j = _
    rw [max_eq_right hD.le,← hprice]
    exact hh

theorem actual_saturation_deficit_lower {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (B : ι → ℝ) (j : ι) (hb : 0 < B j)
    (hps : EqualCapacity.positiveMarginal ξ c B j=1) :
    1+remainingDemand ξ B {j} ((1-ξ)*B j)-remainingDemand ξ B {j} (B j) ≤
      (c : ℝ)-remainingDemand ξ B {j} (B j) := by
  let p := EqualCapacity.positiveMarginal ξ c B
  have hp := EqualCapacity.positiveMarginal_spec ξ c hξ hξ1 B
  obtain ⟨Λ,hΛ,hT,_⟩ := EqualCapacity.positiveMarginal_threshold hξ hξ1 c B
  have hprice : Λ ≤ (1-ξ)*B j := by
    have hh := hT.2.1 j hps
    simpa only [hps,mul_one,mul_comm (B j)] using hh
  have hκb : 0 < (1-ξ)*B j := mul_pos (sub_pos.mpr hξ1) hb
  have hcoord (k : ι) : exposure ξ ((1-ξ)*B j) (B k) ≤ p k :=
    exposure_le_of_scalar_threshold hξ hκb hprice (hp.1 k) (hp.2.1 k)
      (hT.1 k) (hT.2.2 k)
  have hsum : remainingDemand ξ B {j} ((1-ξ)*B j)+1 ≤ (c : ℝ) := by
    calc
      _ ≤ (∑ k, if k=j then 0 else p k)+1 := by
        apply add_le_add _ le_rfl
        unfold remainingDemand
        apply Finset.sum_le_sum
        intro k _
        by_cases hk : k=j
        · simp [hk]
        · simpa only [Finset.mem_singleton,hk,if_false] using hcoord k
      _ = ∑ k,p k := by
        rw [show (1 : ℝ)=p j from hps.symm,sum_remove_focal]
      _ = ((min c (Existence.PayOnceBounded.positiveSupport B).card : ℕ) : ℝ) := hp.2.2
      _ ≤ (c : ℝ) := by exact_mod_cast min_le_left c (Existence.PayOnceBounded.positiveSupport B).card
  linarith

end FCAppendix.Affine.Uniform06.CanonicalInterior
