import FCAppendix.Affine.Uniform06.CanonicalInterior

noncomputable section
namespace FCAppendix.Affine.Uniform06.CanonicalCoarse

open Set
open scoped BigOperators
open FCAppendix.Affine.ClippedResidual
open EntryOwnImpact CanonicalInterior CanonicalRootAdapter
open EqualCanonicalRegularity ReciprocalSecantBounds

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def gain (ξ lo b R : ℝ) : ℝ := (b-lo)*R/ξ

lemma gain_pos {ξ lo b R : ℝ} (hξ : 0 < ξ) (hlb : lo < b) (hR : 0 < R) :
    0 < gain ξ lo b R := div_pos (mul_pos (sub_pos.mpr hlb) hR) hξ

lemma gain_le_b_mul {ξ lo b R : ℝ} (hξ : 0 < ξ) (hR : 0 ≤ R)
    (hκb : (1-ξ)*b ≤ lo) : gain ξ lo b R ≤ b*R := by
  apply (div_le_iff₀ hξ).mpr
  have h := mul_le_mul_of_nonneg_right (show b-lo ≤ ξ*b by nlinarith) hR
  nlinarith

lemma demand_plus_focal_le_capacity {ξ z Λ : ℝ} (hξ : 0 < ξ) (hz : 0 < z)
    (hΛz : Λ ≤ z) (c : ℕ) (B p : ι → ℝ) (j : ι)
    (hp0 : ∀ k,0 ≤ p k) (hp1 : ∀ k,p k ≤ 1)
    (hzero : ∀ k,p k=0 → B k*(1-ξ*p k) ≤ Λ)
    (hinterior : ∀ k,0 < p k → p k < 1 → B k*(1-ξ*p k)=Λ)
    (hcap : (∑ k,p k) ≤ (c : ℝ)) :
    remainingDemand ξ B {j} z+p j ≤ (c : ℝ) := by
  have hcoord (k : ι) : exposure ξ z (B k) ≤ p k :=
    exposure_le_of_scalar_threshold hξ hz hΛz (hp0 k) (hp1 k) (hzero k) (hinterior k)
  calc
    _ ≤ (∑ k,if k=j then 0 else p k)+p j := by
      apply add_le_add _ le_rfl
      unfold remainingDemand
      apply Finset.sum_le_sum
      intro k _
      by_cases hk : k=j
      · simp [hk]
      · simpa only [Finset.mem_singleton,hk,if_false] using hcoord k
    _ = ∑ k,p k := sum_remove_focal p j
    _ ≤ _ := hcap

theorem actual_positive_implies_deficit_positive {ξ : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ) (B : ι → ℝ) (j : ι)
    (hb : 0 < B j) (hpos : 0 < EqualCapacity.positiveMarginal ξ c B j) :
    0 < (c : ℝ)-remainingDemand ξ B {j} (B j) := by
  have hp := EqualCapacity.positiveMarginal_spec ξ c hξ hξ1 B
  by_cases hs : EqualCapacity.positiveMarginal ξ c B j=1
  · have hh := actual_saturation_deficit_lower hξ hξ1 c B j hb hs
    have hκb : 0 < (1-ξ)*B j := mul_pos (sub_pos.mpr hξ1) hb
    have hκbb : (1-ξ)*B j ≤ B j := by nlinarith [mul_pos hξ hb]
    have hd := remainingDemand_antitone_price ξ B {j} hξ hκb hκbb
    linarith
  · have hi : EqualCapacity.positiveMarginal ξ c B j < 1 :=
      lt_of_le_of_ne (hp.2.1 j) hs
    have he := actual_interior_positive_part hξ hξ1 c B j hb hi
    have hΛ : 0 < B j*(1-ξ*EqualCapacity.positiveMarginal ξ c B j) := by
      apply mul_pos hb
      have hh := mul_le_mul_of_nonneg_left (hp.2.1 j) hξ.le
      nlinarith
    have hk := rightSecant_nonneg (b := B j) B {j} hξ hΛ
    have hden : 0 < 1+B j*rightSecant ξ B {j}
        (B j*(1-ξ*EqualCapacity.positiveMarginal ξ c B j)) (B j) := by positivity
    have hmax : 0 < max 0 ((c : ℝ)-remainingDemand ξ B {j} (B j)) := by
      have hh := (eq_div_iff hden.ne').mp he
      rw [← hh]
      exact mul_pos hpos hden
    by_contra hn
    rw [max_eq_left (le_of_not_gt hn)] at hmax
    exact lt_irrefl _ hmax

theorem actual_marginal_upper {ξ lo U : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hlo : 0 < lo)
    (c : ℕ) (B : ι → ℝ) (j : ι)
    (hlb : lo < B j) (hBU : ∀ k,B k ≤ U) (hguard : (1-ξ)*U ≤ lo)
    (hR : 0 < reciprocalSum B {j} (B j)) :
    EqualCapacity.positiveMarginal ξ c B j ≤
      max 0 ((c : ℝ)-remainingDemand ξ B {j} (B j)) /
        gain ξ lo (B j) (reciprocalSum B {j} (B j)) := by
  let p := EqualCapacity.positiveMarginal ξ c B
  let R := reciprocalSum B {j} (B j)
  let D := (c : ℝ)-remainingDemand ξ B {j} (B j)
  let A := gain ξ lo (B j) R
  have hA : 0 < A := gain_pos hξ hlb hR
  have hb : 0 < B j := hlo.trans hlb
  have hκb : (1-ξ)*B j ≤ lo :=
    (mul_le_mul_of_nonneg_left (hBU j) (sub_pos.mpr hξ1).le).trans hguard
  have hp := EqualCapacity.positiveMarginal_spec ξ c hξ hξ1 B
  have hcap : (∑ k,p k) ≤ (c : ℝ) := by
    rw [show (∑ k,p k)=((min c (Existence.PayOnceBounded.positiveSupport B).card : ℕ) : ℝ)
      from hp.2.2]
    exact_mod_cast min_le_left c (Existence.PayOnceBounded.positiveSupport B).card
  obtain ⟨Λ,hΛ0,hT,hslack⟩ := EqualCapacity.positiveMarginal_threshold hξ hξ1 c B
  change p j ≤ max 0 D/A
  by_cases hΛlo : Λ ≤ lo
  · have hh := demand_plus_focal_le_capacity hξ hlo hΛlo c B p j hp.1 hp.2.1
      hT.1 hT.2.2 hcap
    have hg := (demand_secant_bracket B {j} hξ hξ1 hlo hlb hBU hguard).1
    have hAD : A ≤ D := by
      have hgap : A ≤ remainingDemand ξ B {j} lo-remainingDemand ξ B {j} (B j) := by
        apply (div_le_iff₀ hξ).mpr
        simpa only [R,mul_comm] using hg
      dsimp [D] at *
      linarith [hp.1 j]
    have hD : 0 ≤ D := hA.le.trans hAD
    rw [max_eq_right hD]
    exact (hp.2.1 j).trans ((le_div_iff₀ hA).mpr (by simpa using hAD))
  · have hloΛ : lo < Λ := lt_of_not_ge hΛlo
    have hΛ : 0 < Λ := hlo.trans hloΛ
    by_cases hpz : p j=0
    · rw [hpz]
      exact div_nonneg (le_max_left _ _) hA.le
    · have hpj : 0 < p j := lt_of_le_of_ne (hp.1 j) (Ne.symm hpz)
      have hpj1 : p j < 1 := by
        apply lt_of_le_of_ne (hp.2.1 j)
        intro he
        have hh := hT.2.1 j he
        simp only [he,mul_one] at hh
        nlinarith
      have hprice : Λ=B j*(1-ξ*p j) := (hT.2.2 j hpj hpj1).symm
      have hΛb : Λ < B j := by nlinarith [mul_pos hb (mul_pos hξ hpj)]
      have hRle := (rightSecant_bracket B {j} hξ hξ1 hΛ hΛb hBU
        (hguard.trans hloΛ.le)).1
      have hden : 0 < 1+B j*rightSecant ξ B {j} Λ (B j) := by
        have hk : 0 < rightSecant ξ B {j} Λ (B j) := hR.trans_le hRle
        positivity
      have hAden : A ≤ 1+B j*rightSecant ξ B {j} Λ (B j) := by
        have hAb := gain_le_b_mul hξ hR.le hκb
        have hmul := mul_le_mul_of_nonneg_left hRle hb.le
        dsimp [A,R] at *
        linarith
      have he := actual_interior_positive_part hξ hξ1 c B j hb hpj1
      change p j = max 0 D/(1+B j*rightSecant ξ B {j}
        (B j*(1-ξ*p j)) (B j)) at he
      rw [← hprice] at he
      rw [he]
      exact div_le_div_of_nonneg_left (le_max_left _ _) hA hAden

theorem actual_root_located_on_window {ξ lo U dhi : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hlo : 0 < lo)
    (c : ℕ) (B : ι → ℝ) (j : ι)
    (hlb : lo < B j) (hBU : ∀ k,B k ≤ U) (hguard : (1-ξ)*U ≤ lo)
    (hR : 0 < reciprocalSum B {j} (B j))
    (hD : 0 < (c : ℝ)-remainingDemand ξ B {j} (B j))
    (hDhi : (c : ℝ)-remainingDemand ξ B {j} (B j) ≤ dhi)
    (hsmall : dhi/gain ξ lo (B j) (reciprocalSum B {j} (B j)) <
      (B j-lo)/(ξ*B j)) :
    lo < B j*(1-ξ*EqualCapacity.positiveMarginal ξ c B j) ∧
      EqualCapacity.positiveMarginal ξ c B j < 1 := by
  have hpup := actual_marginal_upper hξ hξ1 hlo c B j hlb hBU hguard hR
  have hA := gain_pos hξ hlb hR
  rw [max_eq_right hD.le] at hpup
  have hpbound := hpup.trans (div_le_div_of_nonneg_right hDhi hA.le)
  have hpb : EqualCapacity.positiveMarginal ξ c B j < (B j-lo)/(ξ*B j) :=
    hpbound.trans_lt hsmall
  have hb : 0 < B j := hlo.trans hlb
  have hmult := (lt_div_iff₀ (mul_pos hξ hb)).mp hpb
  have hκb : (1-ξ)*B j ≤ lo :=
    (mul_le_mul_of_nonneg_left (hBU j) (sub_pos.mpr hξ1).le).trans hguard
  constructor
  · nlinarith
  · have hratio : (B j-lo)/(ξ*B j) ≤ 1 := by
      apply (div_le_iff₀ (mul_pos hξ hb)).mpr
      nlinarith
    exact hpb.trans_le hratio

theorem actual_marginal_lower_on_window {ξ lo U dhi : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hlo : 0 < lo)
    (c : ℕ) (B : ι → ℝ) (j : ι)
    (hlb : lo < B j) (hBU : ∀ k,B k ≤ U) (hguard : (1-ξ)*U ≤ lo)
    (hR : 0 < reciprocalSum B {j} (B j))
    (hD : 0 < (c : ℝ)-remainingDemand ξ B {j} (B j))
    (hDhi : (c : ℝ)-remainingDemand ξ B {j} (B j) ≤ dhi)
    (hsmall : dhi/gain ξ lo (B j) (reciprocalSum B {j} (B j)) <
      (B j-lo)/(ξ*B j)) :
    ((c : ℝ)-remainingDemand ξ B {j} (B j)) /
        (1+B j*(Fintype.card ι : ℝ)/lo) ≤
      EqualCapacity.positiveMarginal ξ c B j := by
  let p := EqualCapacity.positiveMarginal ξ c B j
  let Λ := B j*(1-ξ*p)
  have hloc := actual_root_located_on_window hξ hξ1 hlo c B j hlb hBU hguard hR
    hD hDhi hsmall
  have hp := EqualCapacity.positiveMarginal_spec ξ c hξ hξ1 B
  have hb : 0 < B j := hlo.trans hlb
  have hΛ : 0 < Λ := hlo.trans hloc.1
  have he := actual_interior_positive_part hξ hξ1 c B j hb hloc.2
  rw [max_eq_right hD.le] at he
  have hK0 := rightSecant_nonneg (b := B j) B {j} hξ hΛ
  have hden : 0 < 1+B j*rightSecant ξ B {j} Λ (B j) := by positivity
  have hp0 : 0 < p := by
    change 0 < EqualCapacity.positiveMarginal ξ c B j
    rw [he]
    exact div_pos hD hden
  have hΛb : Λ < B j := by dsimp [Λ]; nlinarith [mul_pos hb (mul_pos hξ hp0)]
  have hK := (rightSecant_bracket B {j} hξ hξ1 hΛ hΛb hBU
    (hguard.trans hloc.1.le)).2
  have hKup : rightSecant ξ B {j} Λ (B j) ≤ (Fintype.card ι : ℝ)/lo := by
    calc
      _ ≤ reciprocalSum B {j} Λ := hK
      _ ≤ (Fintype.card ι : ℝ)/Λ := reciprocalSum_le B {j} hΛ
      _ ≤ (Fintype.card ι : ℝ)/lo :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg _) hlo hloc.1.le
  have hdenup : 1+B j*rightSecant ξ B {j} Λ (B j) ≤
      1+B j*(Fintype.card ι : ℝ)/lo := by
    have hh := mul_le_mul_of_nonneg_left hKup hb.le
    calc
      _ ≤ 1+B j*((Fintype.card ι:ℝ)/lo) := by linarith only [hh]
      _ = _ := by ring
  rw [he]
  exact div_le_div_of_nonneg_left hD.le hden hdenup

end FCAppendix.Affine.Uniform06.CanonicalCoarse
