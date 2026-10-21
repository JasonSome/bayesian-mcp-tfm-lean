import FCAppendix.Affine.Uniform06.ActualRootDerivative
import FCAppendix.Affine.Uniform06.CanonicalCoarse
import FCAppendix.Affine.Uniform06.FullReciprocalMean

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.FiniteRootReplacements

open Set MeasureTheory Filter Topology
open FCAppendix.Affine.ClippedResidual
open ReciprocalSecantBounds EntryOwnImpact CanonicalCoarse CanonicalInterior
open scoped BigOperators

lemma inverse_difference_bound {x y r : ℝ} (hr : 0 < r)
    (hx : r ≤ x) (hy : r ≤ y) : |x⁻¹-y⁻¹| ≤ |x-y| /(r*r) := by
  have hx0 := hr.trans_le hx
  have hy0 := hr.trans_le hy
  have he : x⁻¹-y⁻¹=(y-x)/(x*y) := by field_simp
  rw [he,abs_div,abs_sub_comm,abs_of_pos (mul_pos hx0 hy0)]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos hr hr)
    (mul_le_mul hx hy hr.le hx0.le)

theorem normalized_response_error {N b c ν K D H p : ℝ}
    (hN : 0 < N) (hb : 0 < b) (hc : 0 < c) (hcν : c ≤ ν)
    (hK : c ≤ K/N) (hD : 0 ≤ D) (hDH : D ≤ H)
    (hp : p=D/(1+b*K)) :
    |N*p-D/(b*ν)| ≤ H/(b^2*c^2)*(1/N+b*|K/N-ν|) ∧
      0 ≤ N*p ∧ N*p ≤ H/(b*c) := by
  have hν := hc.trans_le hcν
  have hK0 : 0 < K := by
    have hh := (le_div_iff₀ hN).mp hK
    nlinarith [mul_pos hc hN]
  have hden : 0 < 1+b*K := by positivity
  let x := 1/N+b*(K/N)
  have hx : b*c ≤ x := by
    have hmul := mul_le_mul_of_nonneg_left hK hb.le
    dsimp [x]
    linarith [one_div_pos.mpr hN]
  have hy : b*c ≤ b*ν := mul_le_mul_of_nonneg_left hcν hb.le
  have he : N*p=D*x⁻¹ := by
    rw [hp]
    dsimp [x]
    field_simp [hN.ne',hden.ne']
  have hx0 := (mul_pos hb hc).trans_le hx
  have hdiff : |x-b*ν| ≤ 1/N+b*|K/N-ν| := by
    have ht := abs_add_le (1/N) (b*(K/N-ν))
    rw [abs_of_pos (one_div_pos.mpr hN),abs_mul,abs_of_pos hb] at ht
    convert! ht using 1
    dsimp [x]
    ring
  have hi := inverse_difference_bound (mul_pos hb hc) hx hy
  constructor
  · rw [he,div_eq_mul_inv,← mul_sub,abs_mul,abs_of_nonneg hD]
    have hh := mul_le_mul hDH (hi.trans (div_le_div_of_nonneg_right hdiff
      (mul_nonneg (mul_pos hb hc).le (mul_pos hb hc).le))) (abs_nonneg _) (hD.trans hDH)
    convert! hh using 1
    field_simp [hb.ne',hc.ne']
  · constructor
    · rw [he]
      exact mul_nonneg hD (inv_pos.mpr hx0).le
    · rw [he]
      calc
        D*x⁻¹ ≤ H*x⁻¹ := mul_le_mul_of_nonneg_right hDH (inv_pos.mpr hx0).le
        _ ≤ H*(b*c)⁻¹ := mul_le_mul_of_nonneg_left
          (by simpa only [one_div] using one_div_le_one_div_of_le (mul_pos hb hc) hx) (hD.trans hDH)
        _ = _ := (div_eq_mul_inv _ _).symm

def impact (ξ b p K : ℝ) : ℝ := (1-ξ*p)*K/(ξ*(1+b*K))

theorem impact_error {ξ b p K : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hb : 0 < b) (hp : p ∈ Icc (0:ℝ) 1) (hK : 0 < K) :
    0 ≤ impact ξ b p K ∧ impact ξ b p K ≤ 1/(ξ*b) ∧
      |impact ξ b p K-1/(ξ*b)| ≤ p/b+1/(ξ*b^2*K) := by
  have hd : 0 < ξ*(1+b*K) := by positivity
  have hf : 0 ≤ 1-ξ*p := by nlinarith [mul_le_mul_of_nonneg_left hp.2 hξ.le]
  have hnon : 0 ≤ impact ξ b p K := div_nonneg (mul_nonneg hf hK.le) hd.le
  have hid : 1/(ξ*b)-impact ξ b p K=
      1/(ξ*b*(1+b*K))+p*K/(1+b*K) := by
    unfold impact
    field_simp [hξ.ne',hb.ne',show (1+b*K)≠0 by positivity]
    ring
  have hsmall : 0 ≤ 1/(ξ*b)-impact ξ b p K := by
    rw [hid]
    have hp0 := hp.1
    positivity
  refine ⟨hnon,by linarith,?_⟩
  rw [abs_sub_comm,abs_of_nonneg hsmall,hid]
  rw [add_comm (p/b)]
  apply add_le_add
  · have hle : ξ*b^2*K ≤ ξ*b*(1+b*K) := by nlinarith [mul_pos hξ hb]
    simpa using one_div_le_one_div_of_le (by positivity : 0 < ξ*b^2*K) hle
  · apply (div_le_div_iff₀ (by positivity : 0 < 1+b*K) hb).mpr
    nlinarith [hp.1]

theorem impact_window_error {N ξ b c K D H p : ℝ}
    (hN : 0 < N) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hb : 0 < b) (hc : 0 < c)
    (hK : c*N ≤ K) (hp : p ∈ Icc (0:ℝ) 1)
    (hpup : p ≤ D/(b*c*N)) (hDH : D ≤ H) :
    |impact ξ b p K-1/(ξ*b)| ≤ (H+1/ξ)/(b^2*c*N) := by
  have hK0 := (mul_pos hc hN).trans_le hK
  have hh := (impact_error hξ hξ1 hb hp hK0).2.2
  have ht1 : p/b ≤ H/(b^2*c*N) := by
    have hh' := div_le_div_of_nonneg_right
      (hpup.trans (div_le_div_of_nonneg_right hDH (by positivity))) hb.le
    convert! hh' using 1
    field_simp
  have ht2 : 1/(ξ*b^2*K) ≤ (1/ξ)/(b^2*c*N) := by
    have hh' := one_div_le_one_div_of_le (by positivity : 0 < ξ*b^2*(c*N))
      (mul_le_mul_of_nonneg_left hK (by positivity : 0 ≤ ξ*b^2))
    convert! hh' using 1
    field_simp
  exact hh.trans ((add_le_add ht1 ht2).trans_eq (by ring))

theorem square_response_error {x y H b c e : ℝ}
    (_hb : 0 < b) (_hc : 0 < c) (_hH : 0 ≤ H)
    (hx : x ∈ Icc (0:ℝ) (H/(b*c)))
    (hy : y ∈ Icc (0:ℝ) (H/(b*c))) (he : |x-y| ≤ e) :
    |x^2-y^2| ≤ 2*H/(b*c)*e := by
  have hh : x^2-y^2=(x-y)*(x+y) := by ring
  rw [hh,abs_mul,abs_of_nonneg (add_nonneg hx.1 hy.1)]
  have hu : x+y ≤ 2*H/(b*c) := by
    calc
      x+y ≤ H/(b*c)+H/(b*c) := add_le_add hx.2 hy.2
      _ = _ := by ring
  have h0e := (abs_nonneg _).trans he
  exact (mul_le_mul he hu (add_nonneg hx.1 hy.1) h0e).trans_eq (mul_comm _ _)

theorem duplicate_derivative_error {x y d a H b c e f : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hH : 0 ≤ H) (ha : 0 ≤ a)
    (hx : |x| ≤ H/(b*c)) (he : |x-y| ≤ e) (hf : |d-a| ≤ f) :
    |2*x*d-2*y*a| ≤ 2*a*e+2*H/(b*c)*f := by
  have hid : 2*x*d-2*y*a=2*((x-y)*a+x*(d-a)) := by ring
  rw [hid,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have ht := abs_add_le ((x-y)*a) (x*(d-a))
  rw [abs_mul,abs_of_nonneg ha,abs_mul] at ht
  have h0f := (abs_nonneg _).trans hf
  have h1 := mul_le_mul_of_nonneg_right he ha
  have h2 := mul_le_mul hx hf (abs_nonneg _) (by positivity : 0 ≤ H/(b*c))
  have hh := mul_le_mul_of_nonneg_left (ht.trans (add_le_add h1 h2))
    (by norm_num : (0:ℝ) ≤ 2)
  convert! hh using 1
  ring

section Actual

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem derivative_reciprocal_eq {ξ U z : ℝ} (hξ1 : ξ < 1)
    (B : ι → ℝ) (j : ι) (hBU : ∀ k,B k ≤ U) (hguard : (1-ξ)*U < z) :
    ActualRootDerivative.reciprocal ξ B j z=reciprocalSum B {j} z := by
  unfold ActualRootDerivative.reciprocal reciprocalSum
  apply Finset.sum_congr rfl
  intro k _
  have hk : (1-ξ)*B k < z :=
    (mul_le_mul_of_nonneg_left (hBU k) (sub_pos.mpr hξ1).le).trans_lt hguard
  by_cases hkj : k=j <;> by_cases hzb : z< B k <;>
    simp [hkj,hzb,hk,reciprocalTerm]

theorem boundaryCount_mono_left (B : ι → ℝ) (E : Finset ι)
    {a z b : ℝ} (haz : a ≤ z) : boundaryCount B E z b ≤ boundaryCount B E a b := by
  apply Finset.card_le_card
  intro k hk
  have hh := Finset.mem_filter.mp hk
  exact Finset.mem_filter.mpr ⟨hh.1,hh.2.1,haz.trans_lt hh.2.2.1,hh.2.2.2⟩

theorem actual_window_geometry {ξ lo U H : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hlo : 0 < lo)
    (C : ℕ) (B : ι → ℝ) (j : ι)
    (hlb : lo < B j) (hBU : ∀ k,B k ≤ U) (hguard : (1-ξ)*U ≤ lo)
    (hR : 0 < reciprocalSum B {j} (B j))
    (hD : 0 < (C:ℝ)-remainingDemand ξ B {j} (B j))
    (hDH : (C:ℝ)-remainingDemand ξ B {j} (B j) ≤ H)
    (hsmall : H/gain ξ lo (B j) (reciprocalSum B {j} (B j)) <
      (B j-lo)/(ξ*B j)) :
    let p := EqualCapacity.positiveMarginal ξ C B j
    let Λ := B j*(1-ξ*p)
    let Kbar := rightSecant ξ B {j} Λ (B j)
    let K := ActualRootDerivative.reciprocal ξ B j Λ
    p ∈ Ioo (0:ℝ) 1 ∧ lo < Λ ∧ Λ < B j ∧
      reciprocalSum B {j} (B j) ≤ Kbar ∧ reciprocalSum B {j} (B j) ≤ K ∧
      p=((C:ℝ)-remainingDemand ξ B {j} (B j))/(1+B j*Kbar) ∧
      ActualRootDerivative.derivative ξ C B j (B j)=impact ξ (B j) p K := by
  let p := EqualCapacity.positiveMarginal ξ C B j
  let Λ := B j*(1-ξ*p)
  have hloc := actual_root_located_on_window hξ hξ1 hlo C B j hlb hBU hguard hR hD hDH hsmall
  have hp := EqualCapacity.positiveMarginal_spec ξ C hξ hξ1 B
  have hb := hlo.trans hlb
  have hΛ : 0 < Λ := hlo.trans hloc.1
  have he := actual_interior_positive_part hξ hξ1 C B j hb hloc.2
  rw [max_eq_right hD.le] at he
  have hKb := rightSecant_nonneg (b:=B j) B {j} hξ hΛ
  have hd : 0 < 1+B j*rightSecant ξ B {j} Λ (B j) := by positivity
  have hp0 : 0 < p := by
    change 0 < EqualCapacity.positiveMarginal ξ C B j
    rw [he]
    exact div_pos hD hd
  have hΛb : Λ < B j := by dsimp [Λ]; nlinarith [mul_pos hb (mul_pos hξ hp0)]
  have hs := rightSecant_bracket B {j} hξ hξ1 hΛ hΛb hBU (hguard.trans hloc.1.le)
  have hK := derivative_reciprocal_eq hξ1 B j hBU (hguard.trans_lt hloc.1)
  refine ⟨⟨hp0,hloc.2⟩,hloc.1,hΛb,hs.1,?_,he,?_⟩
  · rw [hK]
    exact hs.1.trans hs.2
  · have hu : Function.update B j (B j)=B := Function.update_eq_self _ _
    have hpi : 0 < EqualCapacity.positiveMarginal ξ C B j ∧
        EqualCapacity.positiveMarginal ξ C B j < 1 := ⟨hp0,hloc.2⟩
    simp only [ActualRootDerivative.derivative,ActualRootDerivative.marginal,hu,
      if_pos hpi,ActualRootDerivative.receipt,impact]

theorem actual_receipt_shift {ξ lo U H N c : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hlo : 0 < lo) (hN : 0 < N) (hc : 0 < c)
    (C : ℕ) (B : ι → ℝ) (j : ι)
    (hlb : lo < B j) (hBU : ∀ k,B k ≤ U) (hguard : (1-ξ)*U ≤ lo)
    (hR : c*N ≤ reciprocalSum B {j} (B j))
    (hD : 0 < (C:ℝ)-remainingDemand ξ B {j} (B j))
    (hDH : (C:ℝ)-remainingDemand ξ B {j} (B j) ≤ H)
    (hsmall : H/gain ξ lo (B j) (reciprocalSum B {j} (B j)) <
      (B j-lo)/(ξ*B j)) :
    B j-ξ*H/(c*N) ≤ B j*(1-ξ*EqualCapacity.positiveMarginal ξ C B j) := by
  have hR0 := (mul_pos hc hN).trans_le hR
  have hg := actual_window_geometry hξ hξ1 hlo C B j hlb hBU hguard hR0 hD hDH hsmall
  dsimp only at hg
  have hb := hlo.trans hlb
  have hk := hR.trans hg.2.2.2.1
  have hK0 := (mul_pos hc hN).trans_le hk
  have hd : 0 < 1+B j*rightSecant ξ B {j}
      (B j*(1-ξ*EqualCapacity.positiveMarginal ξ C B j)) (B j) := by positivity
  have hpup : EqualCapacity.positiveMarginal ξ C B j ≤ H/(B j*c*N) := by
    rw [hg.2.2.2.2.2.1]
    exact (div_le_div_of_nonneg_right hDH hd.le).trans
      (div_le_div_of_nonneg_left (hD.le.trans hDH) (by positivity)
        (by nlinarith [mul_le_mul_of_nonneg_left hk hb.le]))
  have hm := mul_le_mul_of_nonneg_left hpup (mul_pos hξ hb).le
  have hid : ξ*B j*(H/(B j*c*N))=ξ*H/(c*N) := by field_simp
  rw [hid] at hm
  nlinarith

theorem actual_secant_boundary_replacement {ξ lo U H N c ν a : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hlo : 0 < lo) (hN : 0 < N)
    (ha : 0 < a) (hc : 0 < c)
    (C : ℕ) (B : ι → ℝ) (j : ι)
    (hlb : lo < B j) (hBU : ∀ k,B k ≤ U) (hguard : (1-ξ)*U ≤ lo)
    (hR : c*N ≤ reciprocalSum B {j} (B j))
    (hD : 0 < (C:ℝ)-remainingDemand ξ B {j} (B j))
    (hDH : (C:ℝ)-remainingDemand ξ B {j} (B j) ≤ H)
    (hsmall : H/gain ξ lo (B j) (reciprocalSum B {j} (B j)) <
      (B j-lo)/(ξ*B j))
    (haΛ : a ≤ B j-ξ*H/(c*N)) :
    |rightSecant ξ B {j} (B j*(1-ξ*EqualCapacity.positiveMarginal ξ C B j)) (B j)/N-ν| ≤
      |reciprocalSum B {j} (B j)/N-ν|+(boundaryCount B {j} a (B j):ℝ)/(a*N) := by
  have hR0 := (mul_pos hc hN).trans_le hR
  have hg := actual_window_geometry hξ hξ1 hlo C B j hlb hBU hguard hR0 hD hDH hsmall
  dsimp only at hg
  let Λ := B j*(1-ξ*EqualCapacity.positiveMarginal ξ C B j)
  have hΛ0 := hlo.trans hg.2.1
  have hΛb := hg.2.2.1
  have hshift := actual_receipt_shift hξ hξ1 hlo hN hc C B j hlb hBU hguard hR hD hDH hsmall
  have haΛ' : a ≤ Λ := haΛ.trans hshift
  have hbnd := rightSecant_boundary_error B {j} hξ hξ1 hΛ0 hΛb hBU
    (hguard.trans hg.2.1.le)
  have hcount : (boundaryCount B {j} Λ (B j):ℝ) ≤ (boundaryCount B {j} a (B j):ℝ) :=
    Nat.cast_le.mpr (boundaryCount_mono_left B {j} haΛ')
  have hnorm : |rightSecant ξ B {j} Λ (B j)/N-reciprocalSum B {j} (B j)/N| ≤
      (boundaryCount B {j} a (B j):ℝ)/(a*N) := by
    rw [← sub_div,abs_div,abs_of_pos hN]
    have hh := div_le_div_of_nonneg_right
      (hbnd.trans ((div_le_div_of_nonneg_right hcount hΛ0.le).trans
        (div_le_div_of_nonneg_left (Nat.cast_nonneg _) ha haΛ'))) hN.le
    simpa only [div_div] using hh
  have ht := abs_sub_le (rightSecant ξ B {j} Λ (B j)/N)
    (reciprocalSum B {j} (B j)/N) ν
  exact (ht.trans (add_le_add hnorm le_rfl)).trans_eq (add_comm _ _)

end Actual
end FCAppendix.Affine.Uniform06.FiniteRootReplacements
