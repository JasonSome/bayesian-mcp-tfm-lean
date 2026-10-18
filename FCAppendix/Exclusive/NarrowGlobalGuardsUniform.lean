import FCAppendix.Exclusive.NarrowGlobalGuardsOptimum

noncomputable section
namespace FCAppendix.Exclusive.Narrow.Global
open Set

def normalizedPrice (d : ℕ) (a : UserTariff) (p0 : ℝ) : ℝ := 1/fTariff d a p0

def referenceRouteGap (d k : ℕ) (a : UserTariff) (p0 A : ℝ) : ℝ :=
  referenceUtility d a (normalizedPrice d a p0) 1 p0-
    referenceRouteUtility (d+1) k a (normalizedPrice d a p0) 1 A

def gapCost (d k : ℕ) (a : UserTariff) (p0 A : ℝ) : ℝ :=
  referenceBidCost d a 1 p0-fixedSuccessCost (d+1) a 1 A (A/k)

lemma referenceBidCost_linear_price (d : ℕ) (a : UserTariff) (lam p : ℝ) :
    referenceBidCost d a lam p = lam*referenceBidCost d a 1 p := by
  cases a <;> dsimp [referenceBidCost,referenceBid] <;> ring

lemma fixedSuccessCost_linear_price (n : ℕ) (a : UserTariff) (lam A y : ℝ) :
    fixedSuccessCost n a lam A y = lam*fixedSuccessCost n a 1 A y := by
  cases a <;> dsimp [fixedSuccessCost] <;> ring

lemma bidCostAtSuccess_eq_nonneg (n k : ℕ) (hk : 0 < k) (a : UserTariff)
    (lam A : ℝ) (hA : 0 ≤ A) :
    bidCostAtSuccess n k a lam A = fixedSuccessCost n a lam A (A/k) := by
  by_cases hz : A = 0
  · rw [hz,bidCostAtSuccess_zero]
    cases a <;> simp [fixedSuccessCost]
  · exact bidCostAtSuccess_eq n k hk a lam A (lt_of_le_of_ne hA (Ne.symm hz))

lemma referenceRouteGap_eq (d k : ℕ) (hk : 0 < k) (a : UserTariff)
    (p0 A : ℝ) (hA : 0 ≤ A) :
    referenceRouteGap d k a p0 A =
      (PayOnce.success (d+1) p0-(1-Real.exp (-A)))-gapCost d k a p0 A/fTariff d a p0 := by
  unfold referenceRouteGap referenceUtility referenceRouteUtility normalizedPrice gapCost
  rw [bidCostAtSuccess_eq_nonneg (d+1) k hk a _ A hA,
    referenceBidCost_linear_price,fixedSuccessCost_linear_price]
  ring

lemma gapCost_affine (d k : ℕ) (eta p0 A : ℝ) :
    gapCost d k (.affine eta) p0 A =
      (1-eta)*gapCost d k (.affine 0) p0 A+eta*gapCost d k (.affine 1) p0 A := by
  dsimp [gapCost,referenceBidCost,fixedSuccessCost]
  ring

lemma normalized_affine_gap_ge (eta f0 f1 C0 C1 X gap : ℝ)
    (he0 : 0 ≤ eta) (he1 : eta ≤ 1) (hf0 : 0 < f0) (hf1 : 0 < f1)
    (h0 : gap ≤ X-C0/f0) (h1 : gap ≤ X-C1/f1) :
    gap ≤ X-((1-eta)*C0+eta*C1)/((1-eta)*f0+eta*f1) := by
  have hF : 0 < (1-eta)*f0+eta*f1 := by
    by_cases he : eta = 1
    · simpa only [he,sub_self,zero_mul,one_mul,zero_add] using hf1
    · exact add_pos_of_pos_of_nonneg
        (mul_pos (sub_pos.mpr (lt_of_le_of_ne he1 he)) hf0) (mul_nonneg he0 hf1.le)
  have hC0 : C0 ≤ (X-gap)*f0 := (div_le_iff₀ hf0).mp (by linarith)
  have hC1 : C1 ≤ (X-gap)*f1 := (div_le_iff₀ hf1).mp (by linarith)
  have hh := add_le_add
    (mul_le_mul_of_nonneg_left hC0 (sub_nonneg.mpr he1))
    (mul_le_mul_of_nonneg_left hC1 he0)
  have hquot : ((1-eta)*C0+eta*C1)/((1-eta)*f0+eta*f1) ≤ X-gap :=
    (div_le_iff₀ hF).mpr (by nlinarith only [hh])
  linarith

theorem referenceRouteGap_uniform_compact (d k : ℕ) (hd : 1 ≤ d)
    (hk : 0 < k) (hkn : k < d+1) (p0 : ℝ) (hp0 : 0 < p0) (hp1 : p0 < 1)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ gap : ℝ, 0 < gap ∧ ∀ a : UserTariff, a.Allowed → ∀ A ∈ Icc (0:ℝ) R,
      gap ≤ referenceRouteGap d k a p0 A := by
  have hprice (a : UserTariff) (ha : a.Allowed) : 0 < normalizedPrice d a p0 :=
    one_div_pos.mpr (fTariff_pos_and_derivative_pos d hd a ha hp0.le hp1).1
  have hFOC (a : UserTariff) (ha : a.Allowed) : 1 = normalizedPrice d a p0*fTariff d a p0 := by
    exact (one_div_mul_cancel ((fTariff_pos_and_derivative_pos d hd a ha hp0.le hp1).1.ne')).symm
  have hu : UserTariff.unique.Allowed := trivial
  have h0 : (UserTariff.affine 0).Allowed := ⟨le_refl _,zero_le_one⟩
  have h1 : (UserTariff.affine 1).Allowed := ⟨zero_le_one,le_refl _⟩
  obtain ⟨gu,hgu,hbu⟩ := referenceRouteUtility_compact_gap d k hd hk hkn .unique hu
    _ 1 p0 (hprice _ hu) hp0 hp1 (hFOC _ hu) R hR
  obtain ⟨g0,hg0,hb0⟩ := referenceRouteUtility_compact_gap d k hd hk hkn (.affine 0) h0
    _ 1 p0 (hprice _ h0) hp0 hp1 (hFOC _ h0) R hR
  obtain ⟨g1,hg1,hb1⟩ := referenceRouteUtility_compact_gap d k hd hk hkn (.affine 1) h1
    _ 1 p0 (hprice _ h1) hp0 hp1 (hFOC _ h1) R hR
  let gap := min gu (min g0 g1)
  have hgap : 0 < gap := lt_min hgu (lt_min hg0 hg1)
  refine ⟨gap,hgap,?_⟩
  intro a ha A hA
  have hboundu : gap ≤ referenceRouteGap d k .unique p0 A := by
    have hb := hbu A hA
    have hh : gu ≤ referenceRouteGap d k .unique p0 A := by
      apply (le_sub_iff_add_le).mpr
      simpa only [add_comm] using hb
    exact (min_le_left _ _).trans hh
  have hbound0 : gap ≤ referenceRouteGap d k (.affine 0) p0 A := by
    have hb := hb0 A hA
    have hh : g0 ≤ referenceRouteGap d k (.affine 0) p0 A := by
      apply (le_sub_iff_add_le).mpr
      simpa only [add_comm] using hb
    exact ((min_le_right _ _).trans (min_le_left _ _)).trans hh
  have hbound1 : gap ≤ referenceRouteGap d k (.affine 1) p0 A := by
    have hb := hb1 A hA
    have hh : g1 ≤ referenceRouteGap d k (.affine 1) p0 A := by
      apply (le_sub_iff_add_le).mpr
      simpa only [add_comm] using hb
    exact ((min_le_right _ _).trans (min_le_right _ _)).trans hh
  cases a with
  | unique => exact hboundu
  | affine eta =>
    rw [referenceRouteGap_eq d k hk (.affine eta) p0 A hA.1,gapCost_affine]
    rw [referenceRouteGap_eq d k hk (.affine 0) p0 A hA.1] at hbound0
    rw [referenceRouteGap_eq d k hk (.affine 1) p0 A hA.1] at hbound1
    simp only [fTariff,sub_zero,one_mul,zero_mul,add_zero,sub_self,zero_add] at hbound0 hbound1 ⊢
    exact normalized_affine_gap_ge eta _ _ _ _ _ gap ha.1 ha.2
      (fOnce_pos d hd hp1) (fPerInclusion_pos d hd hp0.le hp1) hbound0 hbound1

end FCAppendix.Exclusive.Narrow.Global
