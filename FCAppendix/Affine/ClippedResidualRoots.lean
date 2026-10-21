import FCAppendix.Affine.TaggedPureResidual

noncomputable section
namespace FCAppendix.Affine.ClippedResidual
open Set Filter Topology
open scoped BigOperators

def exposure (ξ z b : ℝ) : ℝ :=
  min 1 (max 0 (b-z) / (ξ * max b z))

lemma exposure_nonneg {ξ z b : ℝ} (hξ : 0 < ξ) (hz : 0 < z) :
    0 ≤ exposure ξ z b := by
  apply le_min (by norm_num)
  exact div_nonneg (le_max_left _ _) (mul_nonneg hξ.le (hz.le.trans (le_max_right _ _)))

lemma exposure_le_one (ξ z b : ℝ) : exposure ξ z b ≤ 1 := min_le_left _ _

lemma exposure_zero {ξ z b : ℝ} (hb : b ≤ z) : exposure ξ z b = 0 := by
  simp [exposure, max_eq_left (sub_nonpos.mpr hb)]

lemma exposure_of_between {ξ z b : ℝ} (hξ : 0 < ξ)
    (hz : 0 < z) (hzb : z < b) (hclip : (1-ξ)*b ≤ z) :
    exposure ξ z b = (1-z/b)/ξ := by
  have hb : 0 < b := hz.trans hzb
  have hnum : 0 ≤ b-z := by linarith
  have hden : 0 < ξ*b := mul_pos hξ hb
  have hupper : (b-z)/(ξ*b) ≤ 1 := (div_le_iff₀ hden).2 (by nlinarith)
  rw [exposure, max_eq_left hzb.le, max_eq_right hnum, min_eq_right hupper]
  field_simp [hξ.ne', hb.ne']

lemma continuous_exposure {ξ z : ℝ} (hξ : 0 < ξ) (hz : 0 < z) :
    Continuous (exposure ξ z) := by
  unfold exposure
  apply continuous_const.min
  apply (continuous_const.max (continuous_id.sub continuous_const)).div
    (continuous_const.mul (continuous_id.max continuous_const))
  intro b
  exact ne_of_gt (mul_pos hξ (lt_of_lt_of_le hz (le_max_right _ _)))

lemma exposure_drop {ξ U z₁ z₂ b : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hU : 0 < U)
    (hz : 0 < z₁) (hguard : (1-ξ)*U ≤ z₁)
    (h12 : z₁ ≤ z₂) (hbU : b ≤ U) :
    (z₂-z₁)/(ξ*U)*exposure ξ z₂ b ≤
      exposure ξ z₁ b-exposure ξ z₂ b := by
  have hz₂ : 0 < z₂ := hz.trans_le h12
  have hc : 0 ≤ (z₂-z₁)/(ξ*U) := by positivity
  by_cases hb : b ≤ z₂
  · rw [exposure_zero hb, mul_zero, sub_zero]
    exact exposure_nonneg hξ hz
  · have hzb : z₂ < b := lt_of_not_ge hb
    have hb0 : 0 < b := hz₂.trans hzb
    have hb1 : z₁ < b := h12.trans_lt hzb
    have hκ : 0 ≤ 1-ξ := by linarith
    have hg₁ : (1-ξ)*b ≤ z₁ :=
      (mul_le_mul_of_nonneg_left hbU hκ).trans hguard
    have hg₂ : (1-ξ)*b ≤ z₂ := hg₁.trans h12
    have he : exposure ξ z₁ b-exposure ξ z₂ b = (z₂-z₁)/(ξ*b) := by
      rw [exposure_of_between hξ hz hb1 hg₁, exposure_of_between hξ hz₂ hzb hg₂]
      field_simp [hξ.ne', hb0.ne']
      ring
    apply le_trans (mul_le_mul_of_nonneg_left (exposure_le_one ξ z₂ b) hc)
    rw [mul_one, he]
    exact div_le_div_of_nonneg_left (sub_nonneg.mpr h12) (mul_pos hξ hb0)
      (mul_le_mul_of_nonneg_left hbU hξ.le)

section FiniteDemand
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def remainingDemand (ξ : ℝ) (b : ι → ℝ) (E : Finset ι) (z : ℝ) : ℝ :=
  ∑ i, if i ∈ E then 0 else exposure ξ z (b i)

lemma removal_changes_demand_by_at_most_card (ξ z : ℝ) (b : ι → ℝ)
    (hξ : 0 < ξ) (hz : 0 < z) (E : Finset ι) :
    (∑ i, exposure ξ z (b i))-(E.card : ℝ) ≤ remainingDemand ξ b E z ∧
      remainingDemand ξ b E z ≤ ∑ i, exposure ξ z (b i) := by
  classical
  have hid : (∑ i, exposure ξ z (b i)) =
      remainingDemand ξ b E z+(∑ i ∈ E, exposure ξ z (b i)) := by
    have hE : (∑ i, if i ∈ E then exposure ξ z (b i) else 0) =
        ∑ i ∈ E, exposure ξ z (b i) := by simp
    rw [← hE, remainingDemand, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ E <;> simp [hi]
  have h0 : 0 ≤ ∑ i ∈ E, exposure ξ z (b i) :=
    Finset.sum_nonneg (fun i _ => exposure_nonneg hξ hz)
  have h1 : (∑ i ∈ E, exposure ξ z (b i)) ≤ E.card := by
    calc
      (∑ i ∈ E, exposure ξ z (b i)) ≤ ∑ _i ∈ E, (1 : ℝ) :=
        Finset.sum_le_sum (fun i _ => exposure_le_one _ _ _)
      _ = E.card := by simp
  constructor <;> linarith

lemma remainingDemand_drop {ξ U lo z₁ z₂ : ℝ} (b : ι → ℝ) (E : Finset ι)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hU : 0 < U) (hlo : 0 < lo)
    (hguard : (1-ξ)*U ≤ lo) (hz₁ : lo ≤ z₁) (h12 : z₁ ≤ z₂)
    (hbU : ∀ i, b i ≤ U) :
    (z₂-z₁)/(ξ*U)*remainingDemand ξ b E z₂ ≤
      remainingDemand ξ b E z₁-remainingDemand ξ b E z₂ := by
  unfold remainingDemand
  rw [Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i ∈ E
  · simp [hi]
  · simp only [hi, if_false]
    exact exposure_drop hξ hξ1 hU (hlo.trans_le hz₁) (hguard.trans hz₁) h12 (hbU i)

lemma continuousOn_remainingDemand {ξ lo hi : ℝ} (b : ι → ℝ) (E : Finset ι)
    (hξ : 0 < ξ) (hlo : 0 < lo) :
    ContinuousOn (remainingDemand ξ b E) (Icc lo hi) := by
  classical
  unfold remainingDemand
  apply continuousOn_finsetSum
  intro i _
  by_cases hiE : i ∈ E
  · simp only [hiE, if_true]
    exact continuousOn_const
  · simp only [hiE, if_false, exposure]
    have hratio : ContinuousOn (fun z : ℝ => max 0 (b i-z)/(ξ*max (b i) z)) (Icc lo hi) :=
      ((continuous_const.max (continuous_const.sub continuous_id)).continuousOn).div
        ((continuous_const.mul (continuous_const.max continuous_id)).continuousOn)
        (fun z hz => ne_of_gt (mul_pos hξ ((hlo.trans_le hz.1).trans_le (le_max_right _ _))))
    exact (continuous_const.min continuous_id).comp_continuousOn hratio

theorem exists_unique_balanced_root {ξ U lo hi d slack : ℝ}
    (b : ι → ℝ) (E : Finset ι)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hU : 0 < U)
    (hlo : 0 < lo) (hlh : lo < hi) (hguard : (1-ξ)*U ≤ lo)
    (hbU : ∀ i, b i ≤ U) (hd : 0 < d) (heps : 0 < slack)
    (hlow : d+(E.card : ℝ)+slack < ∑ i, exposure ξ lo (b i))
    (hhigh : (∑ i, exposure ξ hi (b i)) < d-slack) :
    ∃! L : ℝ, L ∈ Icc lo hi ∧ remainingDemand ξ b E L = d := by
  have hhi : 0 < hi := hlo.trans hlh
  have hl := (removal_changes_demand_by_at_most_card ξ lo b hξ hlo E).1
  have hh := (removal_changes_demand_by_at_most_card ξ hi b hξ hhi E).2
  have hDl : d < remainingDemand ξ b E lo := by linarith
  have hDh : remainingDemand ξ b E hi < d := by linarith
  obtain ⟨L,hL,hLd⟩ :=
    intermediate_value_Icc' hlh.le (continuousOn_remainingDemand b E hξ hlo)
      (show d ∈ Icc (remainingDemand ξ b E hi) (remainingDemand ξ b E lo)
        from ⟨hDh.le,hDl.le⟩)
  refine ⟨L, ⟨hL,hLd⟩, ?_⟩
  intro z hz
  rcases hz with ⟨hz,hzd⟩
  apply le_antisymm
  · by_contra h
    have hzL : L < z := lt_of_not_ge h
    have hdrop := remainingDemand_drop b E hξ hξ1 hU hlo hguard hL.1 hzL.le hbU
    rw [hLd,hzd] at hdrop
    have hp : 0 < (z-L)/(ξ*U)*d := by positivity
    linarith
  · by_contra h
    have hzL : z < L := lt_of_not_ge h
    have hdrop := remainingDemand_drop b E hξ hξ1 hU hlo hguard hz.1 hzL.le hbU
    rw [hLd,hzd] at hdrop
    have hp : 0 < (L-z)/(ξ*U)*d := by positivity
    linarith

end FiniteDemand

end FCAppendix.Affine.ClippedResidual
