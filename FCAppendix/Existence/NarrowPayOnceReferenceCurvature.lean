import FCAppendix.Existence.NarrowPayOnceReference
import FCAppendix.Existence.NarrowPayOnceReceiptCurvature

noncomputable section
namespace FCAppendix.Existence.NarrowPayOnce
open Set
open PayOnce PayOnce.OwnImpact
open scoped BigOperators

theorem weighted_Hslope_gap {n : ℕ} (hn : 2≤n) {p : ℝ} (hp : p∈Icc (0:ℝ) 1) :
    (1-p)*Hslope n p ≤ ((n:ℝ)-1)*(H n p-1/(n:ℝ)) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hz : 0≤1-p := sub_nonneg.mpr hp.2
  have hsum : ∑ j∈Finset.range n,
      ((j:ℝ)*(1-p)^j+(if j=0 then (n:ℝ)-1 else 0)) ≤
      ∑ j∈Finset.range n, ((n:ℝ)-1)*(1-p)^j := by
    apply Finset.sum_le_sum
    intro j hj
    by_cases hj0 : j=0
    · simp [hj0]
    · simp only [if_neg hj0,add_zero]
      have hjn : (j:ℝ)≤(n:ℝ)-1 := by
        have hjn : j+1≤n := Finset.mem_range.mp hj
        have hh : (j:ℝ)+1≤n := by exact_mod_cast hjn
        linarith
      exact mul_le_mul_of_nonneg_right hjn (pow_nonneg hz _)
  have hpow : (1-p)*(∑ j∈Finset.range n, (j:ℝ)*(1-p)^(j-1))=
      ∑ j∈Finset.range n, (j:ℝ)*(1-p)^j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj0 : j=0
    · simp [hj0]
    · calc
        _=(j:ℝ)*((1-p)*(1-p)^(j-1)) := by ring
        _=_ := by rw [← pow_succ',Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hj0)]
  have hsum0 : (∑ j∈Finset.range n, if j=0 then (n:ℝ)-1 else 0)=(n:ℝ)-1 := by
    simp [Finset.mem_range.mpr (show 0<n by omega)]
  rw [Finset.sum_add_distrib,hsum0,← Finset.mul_sum] at hsum
  unfold Hslope H
  rw [← mul_div_assoc,hpow]
  apply (div_le_iff₀ hnR).mpr
  have he : (((n:ℝ)-1)*((∑ j∈Finset.range n, (1-p)^j)/(n:ℝ)-1/(n:ℝ)))*(n:ℝ)=
      ((n:ℝ)-1)*((∑ j∈Finset.range n, (1-p)^j)-1) := by field_simp
  rw [he]
  linarith

theorem weighted_Hslope_relative_gap {n : ℕ} (hn : 2≤n) {p : ℝ}
    (hp : p∈Icc (0:ℝ) 1) :
    (1-p)*Hslope n p ≤ ((n:ℝ)-1)*(1-1/(n:ℝ))*H n p := by
  have hH := (H_bounds n (by omega) p hp.1 hp.2).2
  have hh := weighted_Hslope_gap hn hp
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hn1 : 0≤(n:ℝ)-1 := by
    have hh : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
    linarith
  have hx : H n p-1/(n:ℝ)≤(1-1/(n:ℝ))*H n p := by
    apply sub_nonneg.mp
    have he : (1-1/(n:ℝ))*H n p-(H n p-1/(n:ℝ))=(1-H n p)/(n:ℝ) := by ring
    rw [he]
    exact div_nonneg (sub_nonneg.mpr hH) hnR.le
  exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left hx hn1])

def referenceOwnScale (n : ℕ) (R rho : ℝ) : ℝ :=
  (R/(R+1))*H n rho/Hslope n rho

def referenceCurvature (n : ℕ) (R rho w B : ℝ) : ℝ :=
  (n:ℝ)*(w*((n:ℝ)-1)*(1-rho)^(n-2)+
    B*(2*Hslope n rho/R+rho*Hcurvature n rho/R^2))*(referenceOwnScale n R rho/B)^2

def referenceCommonSensitivity (n : ℕ) (R rho w B : ℝ) : ℝ :=
  w*(n:ℝ)*(1-rho)^(n-1)*referenceOwnScale n R rho/B^2

theorem referenceOwnScale_pos {n : ℕ} (hn : 2≤n) {R rho : ℝ}
    (hR : 0<R) (hrho : rho∈Ioo (0:ℝ) 1) : 0<referenceOwnScale n R rho := by
  unfold referenceOwnScale
  exact div_pos (mul_pos (div_pos hR (by linarith))
    (H_pos n (by omega) rho hrho.1.le hrho.2.le))
    (Hslope_pos hn ⟨hrho.1.le,hrho.2.le⟩)

theorem referenceCurvature_pos {n : ℕ} (hn : 2≤n) {R rho w B : ℝ}
    (hR : 0<R) (hrho : rho∈Ioo (0:ℝ) 1) (hw : 0<w) (hB : 0<B) :
    0<referenceCurvature n R rho w B := by
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hn1 : 0<(n:ℝ)-1 := by
    have hh : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
    linarith
  have hsl := Hslope_pos hn ⟨hrho.1.le,hrho.2.le⟩
  have hq := Hcurvature_nonneg n hrho.2.le
  have hk := referenceOwnScale_pos hn hR hrho
  have hz : 0<1-rho := sub_pos.mpr hrho.2
  have hrho0 : 0≤rho := hrho.1.le
  unfold referenceCurvature
  positivity

theorem referenceCommonSensitivity_pos {n : ℕ} (hn : 2≤n) {R rho w B : ℝ}
    (hR : 0<R) (hrho : rho∈Ioo (0:ℝ) 1) (hw : 0<w) (hB : 0<B) :
    0<referenceCommonSensitivity n R rho w B := by
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hk := referenceOwnScale_pos hn hR hrho
  have hz : 0<1-rho := sub_pos.mpr hrho.2
  unfold referenceCommonSensitivity
  positivity

theorem referenceCommonSensitivity_le_curvature {n : ℕ} (hn : 2≤n) {R rho w B : ℝ}
    (hR : 1≤R) (hrho : rho∈Ioo (0:ℝ) 1) (hw : 0<w) (hB : 0<B) :
    referenceCommonSensitivity n R rho w B ≤
      (2-2/(n:ℝ))*referenceCurvature n R rho w B := by
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hn1 : 0<(n:ℝ)-1 := by
    have hh : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
    linarith
  have hR0 : 0<R := lt_of_lt_of_le zero_lt_one hR
  have hD := Hslope_pos hn ⟨hrho.1.le,hrho.2.le⟩
  have hH := H_pos n (by omega) rho hrho.1.le hrho.2.le
  have hq := Hcurvature_nonneg n hrho.2.le
  have hk := referenceOwnScale_pos hn hR0 hrho
  have hz : 0<1-rho := sub_pos.mpr hrho.2
  have hrho0 : 0≤rho := hrho.1.le
  have hcoeff : 0≤2-2/(n:ℝ) := by rw [sub_nonneg,div_le_iff₀ hnR]; nlinarith
  have hscale : 1-rho ≤ (2-2/(n:ℝ))*((n:ℝ)-1)*referenceOwnScale n R rho := by
    have hgap := weighted_Hslope_relative_gap hn ⟨hrho.1.le,hrho.2.le⟩
    have hhalf : (1:ℝ)/2≤R/(R+1) := (le_div_iff₀ (by linarith)).mpr (by linarith)
    have hcoef : 0≤((n:ℝ)-1)*(1-1/(n:ℝ))*H n rho := by
      have hnc : 0≤1-1/(n:ℝ) := by rw [sub_nonneg,div_le_one hnR]; linarith
      positivity
    have hh := mul_le_mul_of_nonneg_right hhalf hcoef
    unfold referenceOwnScale
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hD).mpr
    have hh' : ((n:ℝ)-1)*(1-1/(n:ℝ))*H n rho≤
        (2-2/(n:ℝ))*((n:ℝ)-1)*(R/(R+1)*H n rho) := by
      calc
        _≤2*(R/(R+1)*(((n:ℝ)-1)*(1-1/(n:ℝ))*H n rho)) := by linarith only [hh]
        _=_ := by ring
    convert (hgap.trans hh') using 1
  have hpow : (1-rho)^(n-1)=(1-rho)^(n-2)*(1-rho) := by
    rw [← pow_succ]; congr 1; omega
  have hmain : referenceCommonSensitivity n R rho w B≤
      (2-2/(n:ℝ))*((n:ℝ)*(w*((n:ℝ)-1)*(1-rho)^(n-2))*(referenceOwnScale n R rho/B)^2) := by
    unfold referenceCommonSensitivity
    rw [hpow]
    have hh := mul_le_mul_of_nonneg_left hscale
      (by positivity : 0≤w*(n:ℝ)*(1-rho)^(n-2)*referenceOwnScale n R rho/B^2)
    convert hh using 1 <;> first | rfl | field_simp
  refine hmain.trans ?_
  unfold referenceCurvature
  gcongr
  apply le_add_of_nonneg_right
  positivity

end FCAppendix.Existence.NarrowPayOnce
