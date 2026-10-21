import FCAppendix.Affine.Uniform06.EntryOwnImpact

noncomputable section

namespace FCAppendix.Affine.Uniform06.ReciprocalSecantBounds

open Set
open scoped BigOperators
open FCAppendix.Affine.ClippedResidual
open EntryOwnImpact

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def reciprocalTerm (B z : ℝ) : ℝ := if z < B then B⁻¹ else 0

def reciprocalSum (B : ι → ℝ) (E : Finset ι) (z : ℝ) : ℝ :=
  ∑ j, if j ∈ E then 0 else reciprocalTerm (B j) z

def boundaryCount (B : ι → ℝ) (E : Finset ι) (lo hi : ℝ) : ℕ :=
  (Finset.univ.filter fun j => j ∉ E ∧ lo < B j ∧ B j ≤ hi).card

lemma reciprocalTerm_nonneg {B z : ℝ} (hz : 0 < z) : 0 ≤ reciprocalTerm B z := by
  by_cases h : z < B
  · rw [reciprocalTerm, if_pos h]
    exact inv_nonneg.mpr (hz.trans h).le
  · simp only [reciprocalTerm, if_neg h, le_refl]

lemma reciprocalSum_nonneg (B : ι → ℝ) (E : Finset ι) {z : ℝ} (hz : 0 < z) :
    0 ≤ reciprocalSum B E z := by
  apply Finset.sum_nonneg
  intro j _
  by_cases h : j ∈ E <;> simp only [h, if_true, if_false]
  · rfl
  · exact reciprocalTerm_nonneg hz

lemma reciprocalTerm_le {B z : ℝ} (hz : 0 < z) : reciprocalTerm B z ≤ z⁻¹ := by
  by_cases h : z < B
  · rw [reciprocalTerm, if_pos h]
    simpa only [one_div] using one_div_le_one_div_of_le hz h.le
  · rw [reciprocalTerm, if_neg h]
    positivity

lemma reciprocalSum_le (B : ι → ℝ) (E : Finset ι) {z : ℝ} (hz : 0 < z) :
    reciprocalSum B E z ≤ (Fintype.card ι : ℝ) / z := by
  calc
    _ ≤ ∑ _j : ι, z⁻¹ := by
      apply Finset.sum_le_sum
      intro j _
      by_cases h : j ∈ E
      · simp only [h, if_true]
        positivity
      · simp only [h, if_false]
        exact reciprocalTerm_le hz
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, div_eq_mul_inv]

lemma exposure_secant_bracket {ξ U lo hi B : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hlo : 0 < lo) (hlh : lo < hi)
    (hBU : B ≤ U) (hguard : (1 - ξ) * U ≤ lo) :
    (hi - lo) * reciprocalTerm B hi ≤
        ξ * (exposure ξ lo B - exposure ξ hi B) ∧
      ξ * (exposure ξ lo B - exposure ξ hi B) ≤
        (hi - lo) * reciprocalTerm B lo := by
  have hhi : 0 < hi := hlo.trans hlh
  have hglo : (1 - ξ) * B ≤ lo :=
    (mul_le_mul_of_nonneg_left hBU (by linarith)).trans hguard
  have hghi : (1 - ξ) * B ≤ hi := hglo.trans hlh.le
  by_cases hbhi : hi < B
  · have hBlo : lo < B := hlh.trans hbhi
    have hB : 0 < B := hlo.trans hBlo
    rw [reciprocalTerm, if_pos hbhi, reciprocalTerm, if_pos hBlo,
      exposure_of_between hξ hlo hBlo hglo, exposure_of_between hξ hhi hbhi hghi]
    have heq : ξ * ((1 - lo / B) / ξ - (1 - hi / B) / ξ) =
        (hi - lo) * B⁻¹ := by
      field_simp [hξ.ne', hB.ne']
      ring
    rw [heq]
    exact ⟨le_rfl, le_rfl⟩
  · have hBhi : B ≤ hi := le_of_not_gt hbhi
    rw [reciprocalTerm, if_neg hbhi, exposure_zero hBhi, mul_zero, sub_zero]
    by_cases hBlo : lo < B
    · have hB : 0 < B := hlo.trans hBlo
      rw [reciprocalTerm, if_pos hBlo, exposure_of_between hξ hlo hBlo hglo]
      have heq : ξ * ((1 - lo / B) / ξ) = (B - lo) / B := by
        field_simp [hξ.ne', hB.ne']
      rw [heq]
      refine ⟨div_nonneg (sub_nonneg.mpr hBlo.le) hB.le, ?_⟩
      simpa only [div_eq_mul_inv] using
        div_le_div_of_nonneg_right (sub_le_sub_right hBhi lo) hB.le
    · have hBl : B ≤ lo := le_of_not_gt hBlo
      simp only [reciprocalTerm, if_neg hBlo, exposure_zero hBl, mul_zero, le_refl, and_self]

theorem demand_secant_bracket {ξ U lo hi : ℝ} (B : ι → ℝ) (E : Finset ι)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hlo : 0 < lo) (hlh : lo < hi)
    (hBU : ∀ j, B j ≤ U) (hguard : (1 - ξ) * U ≤ lo) :
    (hi - lo) * reciprocalSum B E hi ≤
        ξ * (remainingDemand ξ B E lo - remainingDemand ξ B E hi) ∧
      ξ * (remainingDemand ξ B E lo - remainingDemand ξ B E hi) ≤
        (hi - lo) * reciprocalSum B E lo := by
  have hpoint (j : ι) := exposure_secant_bracket hξ hξ1 hlo hlh (hBU j) hguard
  constructor
  · unfold reciprocalSum remainingDemand
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases h : j ∈ E <;> simp only [h, if_true, if_false]
    · simp
    · exact (hpoint j).1
  · unfold reciprocalSum remainingDemand
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases h : j ∈ E <;> simp only [h, if_true, if_false]
    · simp
    · exact (hpoint j).2

theorem rightSecant_bracket {ξ U Λ b : ℝ} (B : ι → ℝ) (E : Finset ι)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hΛ : 0 < Λ) (hΛb : Λ < b)
    (hBU : ∀ j, B j ≤ U) (hguard : (1 - ξ) * U ≤ Λ) :
    reciprocalSum B E b ≤ rightSecant ξ B E Λ b ∧
      rightSecant ξ B E Λ b ≤ reciprocalSum B E Λ := by
  have h := demand_secant_bracket B E hξ hξ1 hΛ hΛb hBU hguard
  rw [rightSecant, if_pos hΛb]
  constructor
  · apply (le_div_iff₀ (sub_pos.mpr hΛb)).mpr
    simpa only [mul_comm] using h.1
  · apply (div_le_iff₀ (sub_pos.mpr hΛb)).mpr
    simpa only [mul_comm] using h.2

lemma reciprocalTerm_difference {B lo hi : ℝ} (_hlo : 0 < lo) (hlh : lo ≤ hi) :
    reciprocalTerm B lo - reciprocalTerm B hi =
      if lo < B ∧ B ≤ hi then B⁻¹ else 0 := by
  by_cases h1 : lo < B <;> by_cases h2 : hi < B
  · simp only [reciprocalTerm, if_pos h1, if_pos h2, not_le.mpr h2,
      and_false, if_false, sub_self]
  · simp only [reciprocalTerm, if_neg h2, le_of_not_gt h2,
      h1, and_true, if_true, sub_zero]
  · exact (h1 (hlh.trans_lt h2)).elim
  · simp [reciprocalTerm, h1, h2]

theorem reciprocalSum_boundary_bound (B : ι → ℝ) (E : Finset ι)
    {lo hi : ℝ} (hlo : 0 < lo) (hlh : lo ≤ hi) :
    0 ≤ reciprocalSum B E lo - reciprocalSum B E hi ∧
      reciprocalSum B E lo - reciprocalSum B E hi ≤
        (boundaryCount B E lo hi : ℝ) / lo := by
  have heq : reciprocalSum B E lo - reciprocalSum B E hi =
      ∑ j, if j ∉ E ∧ lo < B j ∧ B j ≤ hi then (B j)⁻¹ else 0 := by
    unfold reciprocalSum
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : j ∈ E
    · simp [h]
    · simp only [h, if_false, not_false_eq_true, true_and,
        reciprocalTerm_difference hlo hlh]
  rw [heq]
  constructor
  · apply Finset.sum_nonneg
    intro j _
    split_ifs with h
    · exact inv_nonneg.mpr (hlo.trans h.2.1).le
    · rfl
  · calc
      _ ≤ ∑ j : ι, if j ∉ E ∧ lo < B j ∧ B j ≤ hi then lo⁻¹ else 0 := by
        apply Finset.sum_le_sum
        intro j _
        split_ifs with h
        · simpa only [one_div] using one_div_le_one_div_of_le hlo h.2.1.le
        · rfl
      _ = (boundaryCount B E lo hi : ℝ) / lo := by
        simp only [boundaryCount, ← Finset.sum_filter, Finset.sum_const,
          nsmul_eq_mul, div_eq_mul_inv]

theorem rightSecant_boundary_error {ξ U Λ b : ℝ} (B : ι → ℝ) (E : Finset ι)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hΛ : 0 < Λ) (hΛb : Λ < b)
    (hBU : ∀ j, B j ≤ U) (hguard : (1 - ξ) * U ≤ Λ) :
    |rightSecant ξ B E Λ b - reciprocalSum B E b| ≤
      (boundaryCount B E Λ b : ℝ) / Λ := by
  have hK := rightSecant_bracket B E hξ hξ1 hΛ hΛb hBU hguard
  rw [abs_of_nonneg (sub_nonneg.mpr hK.1)]
  exact (sub_le_sub_right hK.2 _).trans
    (reciprocalSum_boundary_bound B E hΛ hΛb.le).2

theorem reciprocalSum_active_strip_lower (B : ι → ℝ) (E S : Finset ι)
    {z U : ℝ} (hz : 0 < z) (hU : 0 < U)
    (hS : ∀ j ∈ S, z < B j ∧ B j ≤ U) :
    ((S.card : ℝ)-(E.card : ℝ))/U ≤ reciprocalSum B E z := by
  have hcard : (S.card : ℝ)-(E.card : ℝ) ≤ ((S \ E).card : ℝ) := by
    have hc : S.card ≤ (S \ E).card+E.card := by
      calc
        S.card ≤ ((S \ E) ∪ E).card := Finset.card_le_card (by
          intro j hj
          by_cases he : j ∈ E
          · exact Finset.mem_union_right _ he
          · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hj,he⟩))
        _ ≤ (S \ E).card+E.card := Finset.card_union_le _ _
    have hcR : (S.card : ℝ) ≤ ((S \ E).card : ℝ)+(E.card : ℝ) := by exact_mod_cast hc
    linarith
  calc
    ((S.card : ℝ)-(E.card : ℝ))/U ≤ ((S \ E).card : ℝ)/U :=
      div_le_div_of_nonneg_right hcard hU.le
    _ = ∑ j ∈ S \ E, U⁻¹ := by simp [div_eq_mul_inv]
    _ ≤ ∑ j ∈ S \ E, if j ∈ E then 0 else reciprocalTerm (B j) z := by
      apply Finset.sum_le_sum
      intro j hj
      have hs := Finset.mem_sdiff.mp hj
      rw [if_neg hs.2,reciprocalTerm,if_pos (hS j hs.1).1]
      simpa only [one_div] using
        one_div_le_one_div_of_le (hz.trans (hS j hs.1).1) (hS j hs.1).2
    _ ≤ reciprocalSum B E z := by
      unfold reciprocalSum
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro j _ _
      by_cases hj : j ∈ E
      · simp only [if_pos hj,le_refl]
      · simp only [if_neg hj]
        exact reciprocalTerm_nonneg hz

theorem rightSecant_active_strip_bounds {ξ U lo Λ b n q r : ℝ}
    (B : ι → ℝ) (E S : Finset ι)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hU : 0 < U) (hlo : 0 < lo)
    (hΛ : lo ≤ Λ) (hΛb : Λ < b) (hguard : (1-ξ)*U ≤ lo)
    (hBU : ∀ j, B j ≤ U) (hS : ∀ j ∈ S, b < B j ∧ B j ≤ U)
    (hcount : q*n ≤ (S.card : ℝ)) (hremoved : (E.card : ℝ) ≤ r*n) :
    ((q-r)/U)*n ≤ rightSecant ξ B E Λ b ∧
      rightSecant ξ B E Λ b ≤ (Fintype.card ι : ℝ)/lo := by
  have hΛ0 := hlo.trans_le hΛ
  have hb := hΛ0.trans hΛb
  have hK := rightSecant_bracket B E hξ hξ1 hΛ0 hΛb hBU (hguard.trans hΛ)
  constructor
  · calc
      ((q-r)/U)*n = (q*n-r*n)/U := by ring
      _ ≤ ((S.card : ℝ)-(E.card : ℝ))/U :=
        div_le_div_of_nonneg_right (sub_le_sub hcount hremoved) hU.le
      _ ≤ reciprocalSum B E b := reciprocalSum_active_strip_lower B E S hb hU hS
      _ ≤ _ := hK.1
  · calc
      _ ≤ reciprocalSum B E Λ := hK.2
      _ ≤ (Fintype.card ι : ℝ)/Λ := reciprocalSum_le B E hΛ0
      _ ≤ (Fintype.card ι : ℝ)/lo :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg _) hlo hΛ

theorem leftSecant_bracket {ξ U L Λ : ℝ} (B : ι → ℝ) (E : Finset ι)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hL : 0 < L) (hLΛ : L < Λ)
    (hBU : ∀ j, B j ≤ U) (hguard : (1-ξ)*U ≤ L) :
    reciprocalSum B E Λ ≤ leftSecant ξ B E L Λ ∧
      leftSecant ξ B E L Λ ≤ reciprocalSum B E L := by
  have h := demand_secant_bracket B E hξ hξ1 hL hLΛ hBU hguard
  rw [leftSecant,if_pos hLΛ]
  constructor
  · apply (le_div_iff₀ (sub_pos.mpr hLΛ)).mpr
    simpa only [mul_comm] using h.1
  · apply (div_le_iff₀ (sub_pos.mpr hLΛ)).mpr
    simpa only [mul_comm] using h.2

theorem leftSecant_active_strip_bounds {ξ U lo L Λ n q r : ℝ}
    (B : ι → ℝ) (E S : Finset ι)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hU : 0 < U) (hlo : 0 < lo)
    (hL : lo ≤ L) (hLΛ : L < Λ) (hguard : (1-ξ)*U ≤ lo)
    (hBU : ∀ j, B j ≤ U) (hS : ∀ j ∈ S, Λ < B j ∧ B j ≤ U)
    (hcount : q*n ≤ (S.card : ℝ)) (hremoved : (E.card : ℝ) ≤ r*n) :
    ((q-r)/U)*n ≤ leftSecant ξ B E L Λ ∧
      leftSecant ξ B E L Λ ≤ (Fintype.card ι : ℝ)/lo := by
  have hL0 := hlo.trans_le hL
  have hΛ := hL0.trans hLΛ
  have hK := leftSecant_bracket B E hξ hξ1 hL0 hLΛ hBU (hguard.trans hL)
  constructor
  · calc
      ((q-r)/U)*n = (q*n-r*n)/U := by ring
      _ ≤ ((S.card : ℝ)-(E.card : ℝ))/U :=
        div_le_div_of_nonneg_right (sub_le_sub hcount hremoved) hU.le
      _ ≤ reciprocalSum B E Λ := reciprocalSum_active_strip_lower B E S hΛ hU hS
      _ ≤ _ := hK.1
  · exact hK.2.trans ((reciprocalSum_le B E hL0).trans
      (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hlo hL))

end FCAppendix.Affine.Uniform06.ReciprocalSecantBounds
