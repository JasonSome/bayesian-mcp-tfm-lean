import FCAppendix.Affine.Uniform06.RawPathGlobalResponse
import FCAppendix.Affine.Uniform06.RawMomentPartition

noncomputable section
namespace FCAppendix.Affine.Uniform06.GlobalDerivativeReplacement

open Set MeasureTheory LowBody
open scoped BigOperators
open FCAppendix.Affine.ClippedResidual
open ActualRootDerivative FiniteRootReplacements ReciprocalSecantBounds
open RawMomentPartition CanonicalCoarse

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma reciprocalSum_antitone_price (B : ι → ℝ) (E : Finset ι)
    {a b : ℝ} (ha : 0< a) (hab : a≤ b) : reciprocalSum B E b≤ reciprocalSum B E a := by
  unfold reciprocalSum
  apply Finset.sum_le_sum
  intro j hj
  by_cases hjE : j∈E
  · simp only [hjE,if_true,le_refl]
  · simp only [hjE,if_false]
    by_cases hbj : b< B j
    · simp only [reciprocalTerm,if_pos hbj,if_pos (hab.trans_lt hbj),le_refl]
    · rw [reciprocalTerm,if_neg hbj]
      exact reciprocalTerm_nonneg ha

lemma reciprocal_update (ξ : ℝ) (B : ι → ℝ) (j : ι) (a z : ℝ) :
    reciprocal ξ (Function.update B j a) j z=reciprocal ξ B j z := by
  unfold reciprocal
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hkj : k=j
  · simp [hkj]
  · simp only [Function.update_of_ne hkj]

lemma derivative_update (ξ : ℝ) (c : ℕ) (B : ι → ℝ) (j : ι) (a b : ℝ) :
    derivative ξ c (Function.update B j a) j b=derivative ξ c B j b := by
  have hm : marginal ξ c (Function.update B j a) j b=marginal ξ c B j b := by
    simp only [marginal,Function.update_idem]
  have hr : receipt ξ c (Function.update B j a) j b=receipt ξ c B j b := by
    simp only [receipt,hm]
  simp only [derivative,hm,hr,reciprocal_update]

theorem actual_positive_iff_deficit {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (C : ℕ) (B : ι → ℝ) (j : ι) (hb : 0< B j) :
    0< EqualCapacity.positiveMarginal ξ C B j ↔ 0<(C:ℝ)-remainingDemand ξ B {j} (B j) := by
  constructor
  · exact actual_positive_implies_deficit_positive hξ hξ1 C B j hb
  · intro hD
    have hP := (EqualCapacity.positiveMarginal_spec ξ C hξ hξ1 B).1 j
    apply lt_of_le_of_ne hP
    intro hzero
    have hu : Function.update B j (B j)=B := Function.update_eq_self _ _
    have hh := RootFlatFaces.zero_implies_capacity_le hξ hξ1 C B j hb
      (by simpa only [marginal,hu] using hzero.symm)
    linarith

theorem actual_global_velocity_error {ξ lo U γ N : ℝ}
    (hξ : 0<ξ) (hξ1 : ξ<1) (hlo : 0< lo) (hγ : 0<γ) (hN : 0< N)
    (C : ℕ) (B : ι → ℝ) (j : ι) (hlb : lo< B j)
    (hBU : ∀ k,B k≤ U) (hclip : (1-ξ)*U≤ lo)
    (hR : γ*N≤ reciprocalSum B {j} (B j)) :
    let p := EqualCapacity.positiveMarginal ξ C B j
    let D := (C:ℝ)-remainingDemand ξ B {j} (B j)
    |derivative ξ C B j (B j)-strictPower 0 D/(ξ*B j)|≤
      p/(B j-lo)+strictPower 0 D/(ξ*(B j)^2*γ*N) := by
  dsimp only
  let p := EqualCapacity.positiveMarginal ξ C B j
  let z := B j*(1-ξ*p)
  let R := reciprocalSum B {j} (B j)
  have hb := hlo.trans hlb
  have hgap := sub_pos.mpr hlb
  have hu : Function.update B j (B j)=B := Function.update_eq_self _ _
  have hp := marginal_bounds hξ hξ1 C B j (B j)
  have hp' : p ∈ Icc (0:ℝ) 1 := by simpa only [marginal,hu] using hp
  have hv := actual_derivative_bounds hξ hξ1 C B j hb
  have hpositive := actual_positive_iff_deficit hξ hξ1 C B j hb
  by_cases hpp : 0< p
  · have hD : 0<(C:ℝ)-remainingDemand ξ B {j} (B j) := hpositive.mp hpp
    rw [strictPower,if_pos hD,pow_zero]
    by_cases hz : lo< z
    · have hp1 : p<1 := by
        have hκb := (mul_le_mul_of_nonneg_left (hBU j) (sub_pos.mpr hξ1).le).trans hclip
        dsimp [z] at hz
        nlinarith [mul_pos hb hξ]
      have hzb : z< B j := by dsimp [z]; nlinarith [mul_pos hb (mul_pos hξ hpp)]
      have hzr := derivative_reciprocal_eq hξ1 B j hBU (hclip.trans_lt hz)
      have hRK : R≤ reciprocal ξ B j z := by
        rw [hzr]
        exact reciprocalSum_antitone_price B {j} (hlo.trans hz) hzb.le
      have hK : 0< reciprocal ξ B j z := (mul_pos hγ hN).trans_le (hR.trans hRK)
      have hvel : derivative ξ C B j (B j)=impact ξ (B j) p (reciprocal ξ B j z) := by
        have hcase : 0 < EqualCapacity.positiveMarginal ξ C B j ∧
            EqualCapacity.positiveMarginal ξ C B j < 1 := ⟨hpp,hp1⟩
        simp only [derivative,marginal,hu,if_pos hcase,receipt,impact,p,z]
      rw [hvel]
      have he := (impact_error hξ hξ1 hb hp' hK).2.2
      refine he.trans (add_le_add ?_ ?_)
      · exact div_le_div_of_nonneg_left hp'.1 hgap (by linarith)
      · have hden : ξ*(B j)^2*(γ*N)≤ξ*(B j)^2*reciprocal ξ B j z :=
          mul_le_mul_of_nonneg_left (hR.trans hRK) (by positivity)
        simpa only [mul_assoc] using one_div_le_one_div_of_le (by positivity) hden
    · have hzle : z≤ lo := le_of_not_gt hz
      have haP : 1/(ξ*B j)≤ p/(B j-lo) := by
        apply (div_le_div_iff₀ (mul_pos hξ hb) hgap).mpr
        dsimp [z] at hzle
        nlinarith
      have he : |derivative ξ C B j (B j)-1/(ξ*B j)|≤1/(ξ*B j) := by
        rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr hv.2)]
        linarith [hv.1]
      exact he.trans (haP.trans (le_add_of_nonneg_right (by positivity)))
  · have hz : p=0 := le_antisymm (le_of_not_gt hpp) hp'.1
    have hD : ¬0<(C:ℝ)-remainingDemand ξ B {j} (B j) := fun h => hpp (hpositive.mpr h)
    have hd : derivative ξ C B j (B j)=0 := by
      simp only [derivative,marginal,hu,show EqualCapacity.positiveMarginal ξ C B j=0 from hz,
        lt_self_iff_false,false_and,if_false]
    change EqualCapacity.positiveMarginal ξ C B j=0 at hz
    rw [hd,strictPower,if_neg hD,zero_div,sub_zero,abs_zero,hz,zero_div,zero_add]
    simp only [zero_div,le_refl]

theorem actual_global_square_velocity_error {ξ lo U γ N : ℝ}
    (hξ : 0<ξ) (hξ1 : ξ<1) (hlo : 0< lo) (hγ : 0<γ) (hN : 0< N)
    (C : ℕ) (B : ι → ℝ) (j : ι) (hlb : lo< B j)
    (hBU : ∀ k,B k≤ U) (hclip : (1-ξ)*U≤ lo)
    (hR : γ*N≤ reciprocalSum B {j} (B j)) :
    let p := EqualCapacity.positiveMarginal ξ C B j
    |2*p*derivative ξ C B j (B j)-2*p/(ξ*B j)|≤
      2*p^2/(B j-lo)+2*p/(ξ*(B j)^2*γ*N) := by
  dsimp only
  let p := EqualCapacity.positiveMarginal ξ C B j
  have hp := (EqualCapacity.positiveMarginal_spec ξ C hξ hξ1 B).1 j
  have he := actual_global_velocity_error hξ hξ1 hlo hγ hN C B j hlb hBU hclip hR
  dsimp only at he
  by_cases hpp : 0< p
  · have hD := (actual_positive_iff_deficit hξ hξ1 C B j (hlo.trans hlb)).mp hpp
    rw [strictPower,if_pos hD,pow_zero] at he
    have hm := mul_le_mul_of_nonneg_left he (mul_nonneg (by norm_num : (0:ℝ)≤2) hp)
    have hi : 2*p*derivative ξ C B j (B j)-2*p/(ξ*B j)=
        (2*p)*(derivative ξ C B j (B j)-1/(ξ*B j)) := by ring
    rw [hi,abs_mul,abs_of_nonneg (by positivity : 0≤2*p)]
    dsimp only [p] at hm ⊢
    convert! hm using 1
    ring
  · have hz : p=0 := le_antisymm (le_of_not_gt hpp) hp
    change |2*p*derivative ξ C B j (B j)-2*p/(ξ*B j)|≤
      2*p^2/(B j-lo)+2*p/(ξ*(B j)^2*γ*N)
    rw [hz]
    norm_num

end FCAppendix.Affine.Uniform06.GlobalDerivativeReplacement
