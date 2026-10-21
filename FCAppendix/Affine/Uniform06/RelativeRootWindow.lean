import FCAppendix.Affine.Uniform06.RawPathGlobalResponse
import FCAppendix.Affine.Uniform06.RawMomentPartition

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.RelativeRootWindow

open Set MeasureTheory LowBody
open scoped BigOperators
open Uniform07 LiteralExperiment RawMixedSource RawTiltedSource RawMarkedLaplace
open FCAppendix.Affine.ClippedResidual FCAppendix.Affine.WeightedSampling
open FiniteSampledLaplace RawPathAdapter RawPathRootReplacement RawPathGlobalResponse
open RawMomentPartition RareEmpiricalReplacement

def tailPower (q : ℕ) (H D : ℝ) : ℝ := if H< D then strictPower q D else 0

lemma abs_power_difference_one_two {x y M e : ℝ}
    (hx : x ∈ Icc (0:ℝ) M) (hy : y ∈ Icc (0:ℝ) M)
    (he : |x-y|≤ e) (q : Fin 2) :
    |x^(q.val+1)-y^(q.val+1)|≤(if q.val=0 then 1 else 2*M)*e := by
  fin_cases q
  · simpa using he
  · have hxy : x^2-y^2=(x-y)*(x+y) := by ring
    change |x^2-y^2|≤(2*M)*e
    rw [hxy,abs_mul,abs_of_nonneg (add_nonneg hx.1 hy.1)]
    have he0 : 0≤ e := (abs_nonneg _).trans he
    have hh := mul_le_mul he (show x+y≤2*M by linarith [hx.2,hy.2])
      (add_nonneg hx.1 hy.1) he0
    simpa only [mul_comm] using hh

theorem finite_power_window {Ω : Type*} [Fintype Ω]
    (P : FiniteLaw Ω) (X D : Ω → ℝ) {a K H M E e : ℝ}
    (ha : 0≤ a) (_hK : 0≤ K) (hH : 0≤ H) (hM : 0≤ M) (hE : 0≤ E) (he : 0≤ e)
    (hX : ∀ p,0< P.mass p → 0≤ X p)
    (hzero : ∀ p,0< P.mass p → D p≤0 → X p=0)
    (hglobal : ∀ p,0< P.mass p → X p≤ K*max 0 (D p))
    (hwindow : ∀ p,0< P.mass p → 0< D p → D p≤ H →
      X p≤ M ∧ a*D p≤ M ∧ |X p-a*D p|≤ E)
    (q : Fin 2) :
    |e*P.expect (fun p => X p^(q.val+1))-
      e*a^(q.val+1)*P.expect (fun p => strictPower (q.val+1) (D p))|≤
      (if q.val=0 then 1 else 2*M)*E*
        (e*P.expect (fun p => strictPower 0 (D p)))+
      (K^(q.val+1)+a^(q.val+1))*(e*P.expect (fun p => tailPower (q.val+1) H (D p))) := by
  let L := if q.val=0 then (1:ℝ) else 2*M
  have hL : 0≤ L := by dsimp only [L]; split_ifs <;> positivity
  have hpoint (p : Ω) (hp : 0< P.mass p) :
      |X p^(q.val+1)-a^(q.val+1)*strictPower (q.val+1) (D p)|≤
        L*E*strictPower 0 (D p)+(K^(q.val+1)+a^(q.val+1))*tailPower (q.val+1) H (D p) := by
    by_cases hD : 0< D p
    · by_cases hDH : D p≤ H
      · have hw := hwindow p hp hD hDH
        have hh := abs_power_difference_one_two ⟨hX p hp,hw.1⟩
          ⟨mul_nonneg ha hD.le,hw.2.1⟩ hw.2.2 q
        simpa only [L,strictPower,if_pos hD,pow_zero,mul_one,tailPower,
          if_neg (not_lt.mpr hDH),mul_zero,add_zero,mul_pow] using hh
      · have hXp : X p^(q.val+1)≤ K^(q.val+1)*D p^(q.val+1) := by
          rw [← mul_pow]
          exact pow_le_pow_left₀ (hX p hp) (by simpa only [max_eq_right hD.le] using hglobal p hp) _
        have hdiff := abs_sub (X p^(q.val+1)) (a^(q.val+1)*D p^(q.val+1))
        rw [abs_of_nonneg (pow_nonneg (hX p hp) _),
          abs_of_nonneg (mul_nonneg (pow_nonneg ha _) (pow_nonneg hD.le _))] at hdiff
        simp only [strictPower,if_pos hD,pow_zero,mul_one,tailPower,
          if_pos (lt_of_not_ge hDH)]
        nlinarith [mul_nonneg hL hE]
    · simp only [strictPower,if_neg hD,hzero p hp (le_of_not_gt hD),
        zero_pow (by omega : q.val+1≠0),mul_zero,sub_zero,abs_zero,tailPower,
        if_neg (not_lt.mpr ((le_of_not_gt hD).trans hH)),add_zero,le_refl]
  have hbound := (abs_expect_le P (fun p =>
      X p^(q.val+1)-a^(q.val+1)*strictPower (q.val+1) (D p))).trans
    (expect_le_of_support P _ _ hpoint)
  rw [FCAppendix.FiniteLaw.expect_sub,FCAppendix.FiniteLaw.expect_const_mul,
    FCAppendix.FiniteLaw.expect_add,FCAppendix.FiniteLaw.expect_const_mul,
    FCAppendix.FiniteLaw.expect_const_mul] at hbound
  have hh := mul_le_mul_of_nonneg_left hbound he
  rw [← abs_of_nonneg he,← abs_mul] at hh
  rw [abs_of_nonneg he] at hh
  dsimp only [L] at hh ⊢
  convert! hh using 1 <;> ring

variable {N : ℕ} [Nonempty (Fin N)]

theorem actual_path_power_window (i : Row) (c : ℕ) (g : GuardData)
    {lo U b H γ ν z e : ℝ} (hlo : 0< lo) (hU : 0< U) (hlb : lo< b)
    (hbU : b≤ U) (hclip : (1-xi i)*U≤ lo) (hγ : 0<γ) (hγν : γ≤ν)
    (hz : 0< z) (hH : 0≤ H) (he : 0≤ e) (hN : 0< N)
    (ω : Fin N → RowRival) (hc : ValidCounts c ω)
    (hcap : ∀ j,(ω j).1=0 → (ω j).2≤ U)
    (k : ℕ) (hk : k=(imbalanceSum ω).natAbs)
    (hW : (k:ℝ)< totalWeight (rowWeights (rawWeight (xi i) g) (rawWeight_bounds (xi i) g) ω))
    (hemp : γ+(k:ℝ)/(lo*(N:ℝ))≤ empirical (FullReciprocalMean.reciprocal b) N ω)
    (hsmall : H*(xi i)^2*b<(b-lo)^2*γ*(N:ℝ))
    (hzΛ : z≤ b-xi i*H/(γ*(N:ℝ))) (q : Fin 2) :
    let P := pathLaw (rowWeights (rawWeight (xi i) g) (rawWeight_bounds (xi i) g) ω) k ∅
    let D := selectedDeficit i c b ω k
    let K := xi i/((b-lo)*γ)
    let M := H/(b*γ)
    let E := H/(b^2*γ^2)*(1/(N:ℝ)+b*(
      |empirical (FullReciprocalMean.reciprocal b) N ω-ν|+
        (k:ℝ)/(lo*(N:ℝ))+empirical (FullReciprocalMean.window z b) N ω/z))
    |e*P.expect (fun p => ((N:ℝ)*selectedResponse i c b ω k p)^(q.val+1))-
      e*(1/(b*ν))^(q.val+1)*P.expect (fun p => strictPower (q.val+1) (D p))|≤
      (if q.val=0 then 1 else 2*M)*E*(e*P.expect (fun p => strictPower 0 (D p)))+
      (K^(q.val+1)+(1/(b*ν))^(q.val+1))*(e*P.expect (fun p => tailPower (q.val+1) H (D p))) := by
  dsimp only
  have hb : 0< b := hlo.trans hlb
  have hν : 0<ν := hγ.trans_le hγν
  have hNr : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hw0 : 0≤ empirical (FullReciprocalMean.window z b) N ω := by
    exact div_nonneg (Finset.sum_nonneg (fun j _ => (FullReciprocalMean.window_bounds z b (ω j)).1)) hNr.le
  apply finite_power_window _ _ _ (by positivity) (by have hξ:=xi_pos i; positivity)
    hH (by positivity) (by positivity) he _ _ _ _ q
  · intro p hp
    exact (actual_global_response_bound i c g hlo hU.le hlb hbU hclip hγ hN ω hc hcap k hk hW p hp hemp).1
  · intro p hp hD
    rw [(actual_path_nonpositive i c g hb ω hc k hk hW p hp hD).1,mul_zero]
  · intro p hp
    exact (actual_global_response_bound i c g hlo hU.le hlb hbU hclip hγ hN ω hc hcap k hk hW p hp hemp).2
  · intro p hp hD hDH
    have hh := actual_path_window_errors i c g hlo hU hlb hbU hclip hγ hγν hz hN
      ω hc hcap k hk hW p hp hemp hsmall hzΛ hD hDH
    refine ⟨hh.2.2.1.2,?_,?_⟩
    · have ha := div_le_div_of_nonneg_left hH (mul_pos hb hγ)
        (mul_le_mul_of_nonneg_left hγν hb.le)
      have hd := div_le_div_of_nonneg_right hDH (mul_pos hb hν).le
      simpa only [one_div,div_eq_mul_inv,mul_comm,mul_one] using! hd.trans ha
    · simpa only [one_div,div_eq_mul_inv,mul_comm,mul_one] using! hh.2.1

end FCAppendix.Affine.Uniform06.RelativeRootWindow
