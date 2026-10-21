import FCAppendix.Affine.Uniform06.LiteralExperiment
import FCAppendix.Affine.Uniform06.SourceGuardGeometry
import FCAppendix.Affine.Uniform06.ReciprocalSecantBounds

noncomputable section
namespace FCAppendix.Affine.Uniform06.CanonicalRootAdapter

open Set LowBody
open scoped BigOperators
open FCAppendix.Affine.ClippedResidual
open FCAppendix.Affine.EqualCapacity
open Existence.PayOnceBounded (positiveSupport mem_positiveSupport)
open LiteralExperiment EntryOwnImpact SourceGuardGeometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem positiveMarginal_eq_exposure {ξ U Λ : ℝ} (c : ℕ) (B : ι → ℝ)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hΛ : 0 < Λ)
    (hguard : (1-ξ)*U ≤ Λ) (hBU : ∀ j, B j ≤ U)
    (hroot : (∑ j, exposure ξ Λ (B j)) = (c : ℝ)) :
    positiveMarginal ξ c B = fun j => exposure ξ Λ (B j) := by
  classical
  let S := positiveSupport B
  have hB (j : S) : 0 < B j.1 := (mem_positiveSupport B j.1).mp j.2
  have hout (j : ι) (hj : j ∉ S) : exposure ξ Λ (B j) = 0 := by
    apply exposure_zero
    exact (le_of_not_gt (fun h => hj ((mem_positiveSupport B j).mpr h))).trans hΛ.le
  have hsum : (∑ j : S, exposure ξ Λ (B j.1)) = (c : ℝ) := by
    calc
      _ = ∑ j ∈ S, exposure ξ Λ (B j) := (Finset.sum_attach S _)
      _ = ∑ j, exposure ξ Λ (B j) := by
        apply Finset.sum_subset (Finset.subset_univ S)
        intro j _ hj
        exact hout j hj
      _ = _ := hroot
  have hcapR : (c : ℝ) ≤ (Fintype.card S : ℝ) := by
    rw [← hsum]
    calc
      _ ≤ ∑ _j : S, (1 : ℝ) :=
        Finset.sum_le_sum (fun j _ => exposure_le_one ξ Λ (B j.1))
      _ = _ := by simp
  have hcap : c ≤ Fintype.card S := by exact_mod_cast hcapR
  have hq : IsKernel ξ c (fun j : S => B j.1)
      (fun j => exposure ξ Λ (B j.1)) := by
    refine ⟨fun _ => exposure_nonneg hξ hΛ,
      fun j => exposure_le_one ξ Λ (B j.1), ?_, Λ, hΛ.le, ?_⟩
    · simpa only [min_eq_left hcap] using hsum
    · exact exposure_threshold hξ hξ1 hΛ hguard
        (fun j : S => B j.1) (fun j => hBU j.1)
  have heq := isKernel_unique hξ c (fun j : S => B j.1) hB
    (kernelMarginal ξ c (fun j : S => B j.1))
    (fun j => exposure ξ Λ (B j.1))
    (kernelMarginal_spec hξ hξ1 c _ hB) hq
  funext j
  by_cases hj : j ∈ S
  · change onSupport ξ c S B j = _
    rw [onSupport, dif_pos hj]
    exact congrFun heq ⟨j,hj⟩
  · change onSupport ξ c S B j = _
    rw [onSupport, dif_neg hj, hout j hj]

lemma remainingDemand_insert (ξ z : ℝ) (B : ι → ℝ) (E : Finset ι)
    (j : ι) (hj : j ∉ E) :
    remainingDemand ξ B E z =
      remainingDemand ξ B (insert j E) z + exposure ξ z (B j) := by
  classical
  have hpoint (k : ι) :
      (if k ∈ E then 0 else exposure ξ z (B k)) =
      (if k ∈ insert j E then 0 else exposure ξ z (B k)) +
        (if k = j then exposure ξ z (B j) else 0) := by
    by_cases hk : k = j
    · subst k
      simp [hj]
    · by_cases hE : k ∈ E <;> simp [hk,hE]
  unfold remainingDemand
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  simp

theorem exposure_eq_positive_deficit {ξ U Λ : ℝ} (c : ℕ)
    (B : ι → ℝ) (E : Finset ι) (j : ι)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hΛ : 0 < Λ)
    (hguard : (1-ξ)*U ≤ Λ) (hBU : ∀ k, B k ≤ U)
    (hj : j ∉ E) (hb : 0 < B j)
    (hroot : remainingDemand ξ B E Λ = (c : ℝ)) :
    exposure ξ Λ (B j) =
      max 0 ((c : ℝ)-remainingDemand ξ B (insert j E) (B j)) /
        (1+B j*rightSecant ξ B (insert j E) Λ (B j)) := by
  have hfocal : remainingDemand ξ B (insert j E) Λ + exposure ξ Λ (B j) =
      (c : ℝ) := by rw [← remainingDemand_insert ξ Λ B E j hj]; exact hroot
  have hkg : 0 ≤ rightSecant ξ B (insert j E) Λ (B j) :=
    rightSecant_nonneg B (insert j E) hξ hΛ
  have hden : 0 < 1+B j*rightSecant ξ B (insert j E) Λ (B j) := by positivity
  by_cases hΛb : Λ < B j
  · have hp : 0 < exposure ξ Λ (B j) := exposure_pos hξ hΛ hΛb
    have hprice : Λ = B j*(1-ξ*exposure ξ Λ (B j)) :=
      (exposure_receipt hξ hΛ hΛb
        ((mul_le_mul_of_nonneg_left (hBU j) (by linarith)).trans hguard)).symm
    have he := focal_right_deficit B (insert j E) hξ hb hΛ hp hfocal hprice
    have hD : 0 < (c : ℝ)-remainingDemand ξ B (insert j E) (B j) := by
      have hm := (eq_div_iff hden.ne').mp he
      rw [← hm]
      exact mul_pos hp hden
    rw [max_eq_right hD.le]
    exact he
  · have hbΛ : B j ≤ Λ := le_of_not_gt hΛb
    have hm := remainingDemand_antitone_price ξ B E hξ hb hbΛ
    rw [hroot, remainingDemand_insert ξ (B j) B E j hj,
      exposure_zero (le_refl (B j)), add_zero] at hm
    have hD : (c : ℝ)-remainingDemand ξ B (insert j E) (B j) ≤ 0 := by linarith
    rw [exposure_zero hbΛ, max_eq_left hD, zero_div]

variable [Nonempty ι]

omit [Nonempty ι] in

theorem complementMarginal_at_root {ξ U Λ : ℝ}
    (T : PureTemplate ι) (B : ι → ℝ) (E : Finset ι)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hU : 0 < U) (hΛ : 0 < Λ)
    (hguard : (1-ξ)*U ≤ Λ) (hBU : ∀ j, B j ≤ U)
    (hout : ∀ j, j ∉ T.support → B j=0)
    (hroot : remainingDemand ξ B E Λ = (small T : ℝ)) :
    complementMarginal ξ T B E = fun j => if j ∈ E then 0 else exposure ξ Λ (B j) := by
  have hmasked : ∀ j, maskedBids T B E j ≤ U := by
    intro j
    unfold maskedBids
    split_ifs
    · exact hBU j
    · exact hU.le
  have he := positiveMarginal_eq_exposure (small T) (maskedBids T B E)
    hξ hξ1 hΛ hguard hmasked
    (by rw [masked_exposure_sum hΛ T B E hout]; exact hroot)
  funext j
  change positiveMarginal ξ (small T) (maskedBids T B E) j = _
  rw [congrFun he j]
  by_cases hjE : j ∈ E
  · simp [maskedBids,hjE,exposure_zero hΛ.le]
  · by_cases hjT : j ∈ T.support
    · simp [maskedBids,hjE,hjT]
    · simp [maskedBids,hjE,hjT,hout j hjT,exposure_zero hΛ.le]

omit [Nonempty ι] in

theorem exists_literal_complement_root {ξ U lo hi slack : ℝ}
    (T : PureTemplate ι) (B : ι → ℝ) (E : Finset ι)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hU : 0 < U)
    (hlo : 0 < lo) (hlh : lo < hi) (hguard : (1-ξ)*U ≤ lo)
    (hBU : ∀ j, B j ≤ U) (hout : ∀ j, j ∉ T.support → B j=0)
    (hd : 0 < small T) (heps : 0 < slack)
    (hlow : (small T : ℝ)+(E.card : ℝ)+slack < ∑ j, exposure ξ lo (B j))
    (hhigh : (∑ j, exposure ξ hi (B j)) < (small T : ℝ)-slack) :
    ∃ Λ ∈ Ioo lo hi,
      IsLargestPositiveRoot ξ B E (small T : ℝ) Λ ∧
      complementMarginal ξ T B E =
        fun j => if j ∈ E then 0 else exposure ξ Λ (B j) := by
  obtain ⟨Λ,hΛ,hroot⟩ := exists_largest_positive_root B E hξ hξ1 hU hlo hlh
    hguard hBU (by exact_mod_cast hd) heps hlow hhigh
  exact ⟨Λ,hΛ,hroot,complementMarginal_at_root T B E hξ hξ1 hU hroot.1
    (hguard.trans hΛ.1.le) hBU hout hroot.2.1⟩

omit [Nonempty ι] in

theorem literal_complement_positive_part {ξ U lo hi slack : ℝ}
    (T : PureTemplate ι) (B : ι → ℝ) (E : Finset ι) (j : ι)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hU : 0 < U)
    (hlo : 0 < lo) (hlh : lo < hi) (hguard : (1-ξ)*U ≤ lo)
    (hBU : ∀ k, B k ≤ U) (hout : ∀ k, k ∉ T.support → B k=0)
    (hd : 0 < small T) (heps : 0 < slack) (hj : j ∉ E) (hb : 0 < B j)
    (hlow : (small T : ℝ)+(E.card : ℝ)+slack < ∑ k, exposure ξ lo (B k))
    (hhigh : (∑ k, exposure ξ hi (B k)) < (small T : ℝ)-slack) :
    ∃ Λ ∈ Ioo lo hi,
      IsLargestPositiveRoot ξ B E (small T : ℝ) Λ ∧
      complementMarginal ξ T B E j =
        max 0 ((small T : ℝ)-remainingDemand ξ B (insert j E) (B j)) /
          (1+B j*rightSecant ξ B (insert j E) Λ (B j)) := by
  obtain ⟨Λ,hΛ,hroot,hp⟩ := exists_literal_complement_root T B E hξ hξ1 hU hlo hlh
    hguard hBU hout hd heps hlow hhigh
  refine ⟨Λ,hΛ,hroot,?_⟩
  rw [congrFun hp j, if_neg hj]
  exact exposure_eq_positive_deficit (small T) B E j hξ hξ1 hroot.1
    (hguard.trans hΛ.1.le) hBU hj hb hroot.2.1

end FCAppendix.Affine.Uniform06.CanonicalRootAdapter
