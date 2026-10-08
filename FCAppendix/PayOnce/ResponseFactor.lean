import FCAppendix.PayOnce.RareSuccessSlope
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace FCAppendix.PayOnce.ResponseFactor
open Set Real OwnImpact

noncomputable def J (n : ℕ) (p : ℝ) : ℝ := (n:ℝ)*H n p/Hslope n p

noncomputable def rootFactor (n : ℕ) (p : ℝ) : ℝ :=
  J n p ^ (1/((n:ℝ)-1))*(1-p)

theorem J_pos {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : p ∈ Icc (0:ℝ) 1) :
    0 < J n p :=
  div_pos (mul_pos (Nat.cast_pos.mpr (by omega)) (H_pos n (by omega) p hp.1 hp.2))
    (Hslope_pos hn hp)

theorem J_bounds {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : p ∈ Icc (0:ℝ) 1) :
    1/(n:ℝ) ≤ J n p ∧ J n p ≤ (n:ℝ)^2 := by
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hH := H_bounds n (by omega) p hp.1 hp.2
  have hs := Hslope_bounds hn hp
  have hsp := Hslope_pos hn hp
  have hnum : 1 ≤ (n:ℝ)*H n p := by
    have hh := (div_le_iff₀ hnR).mp hH.1
    nlinarith
  constructor
  · calc
      1/(n:ℝ) ≤ 1/Hslope n p := one_div_le_one_div_of_le hsp hs.2
      _ ≤ J n p := div_le_div_of_nonneg_right hnum hsp.le
  · apply (div_le_iff₀ hsp).mpr
    have hnum' : (n:ℝ)*H n p ≤ n := mul_le_of_le_one_right hnR.le hH.2
    have hden := (div_le_iff₀ hnR).mp hs.1
    have hden' := mul_le_mul_of_nonneg_left hden hnR.le
    nlinarith

theorem phi_eq_J_mul_pow (n : ℕ) (p : ℝ) :
    RareSuccessSlope.phi n p = J n p*(1-p)^(n-1) := by
  unfold RareSuccessSlope.phi J
  ring

theorem phi_one {n : ℕ} (hn : 2 ≤ n) : RareSuccessSlope.phi n 1 = 0 := by
  rw [phi_eq_J_mul_pow]
  simp [show n-1 ≠ 0 by omega]

theorem H_sub_mul_Hslope {n : ℕ} (hn : 0 < n) (p : ℝ) :
    H n p-p*Hslope n p = (1-p)^(n-1) := by
  have hs : HasDerivAt (success n) ((n:ℝ)*(1-p)^(n-1)) p := by
    convert (hasDerivAt_const p (1:ℝ)).sub (((hasDerivAt_id p).const_sub 1).pow n) using 1 <;>
      first | rfl | (simp only [id_eq]; ring)
  have hprod := (((hasDerivAt_id p).const_mul (n:ℝ)).mul (hasDerivAt_H n p))
  change HasDerivAt (fun x => (n:ℝ)*x*H n x)
    ((n:ℝ)*1*H n p+(n:ℝ)*p*(-Hslope n p)) p at hprod
  have hprod' : HasDerivAt (success n) ((n:ℝ)*H n p+(n:ℝ)*p*(-Hslope n p)) p := by
    simpa only [mul_one,H_mul n hn] using hprod
  have he := hprod'.unique hs
  have hnR : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  apply mul_left_cancel₀ hnR
  nlinarith

theorem success_add_phi_eq_J_mul_H {n : ℕ} (hn : 2 ≤ n)
    {p : ℝ} (hp : p ∈ Icc (0:ℝ) 1) :
    success n p+RareSuccessSlope.phi n p = J n p*H n p := by
  rw [phi_eq_J_mul_pow,← H_sub_mul_Hslope (by omega : 0 < n) p,← H_mul n (by omega) p]
  unfold J
  field_simp [(Hslope_pos hn hp).ne']
  ring

theorem rootFactor_nonneg {n : ℕ} (hn : 2 ≤ n)
    {p : ℝ} (hp : p ∈ Icc (0:ℝ) 1) : 0 ≤ rootFactor n p :=
  mul_nonneg (rpow_nonneg (J_pos hn hp).le _) (sub_nonneg.mpr hp.2)

theorem rootFactor_bounds {n : ℕ} (hn : 2 ≤ n)
    {p : ℝ} (hp : p ∈ Icc (0:ℝ) 1) :
    0 ≤ rootFactor n p ∧ rootFactor n p ≤ ((n:ℝ)^2)^(1/((n:ℝ)-1)) := by
  refine ⟨rootFactor_nonneg hn hp,?_⟩
  have hγ : 0 ≤ 1/((n:ℝ)-1) := by
    have : (2:ℝ) ≤ n := by exact_mod_cast hn
    exact (one_div_pos.mpr (by linarith)).le
  exact (mul_le_of_le_one_right (rpow_nonneg (J_pos hn hp).le _) (by linarith [hp.1])).trans
    (rpow_le_rpow (J_pos hn hp).le (J_bounds hn hp).2 hγ)

theorem measurable_J (n : ℕ) : Measurable (J n) := by
  unfold J H Hslope
  fun_prop

theorem measurable_rootFactor (n : ℕ) : Measurable (rootFactor n) := by
  exact ((measurable_J n).pow_const _).mul (measurable_const.sub measurable_id)

theorem rootFactor_pow {n : ℕ} (hn : 2 ≤ n)
    {p : ℝ} (hp : p ∈ Icc (0:ℝ) 1) :
    rootFactor n p^(n-1) = RareSuccessSlope.phi n p := by
  have hcast : ((n-1:ℕ):ℝ) = (n:ℝ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]
  have hexp : 1/((n:ℝ)-1) = (((n-1:ℕ):ℝ))⁻¹ := by rw [hcast,one_div]
  rw [rootFactor,mul_pow,hexp,rpow_inv_natCast_pow (J_pos hn hp).le (by omega),phi_eq_J_mul_pow]

theorem phi_rpow_eq_rootFactor {n : ℕ} (hn : 2 ≤ n)
    {p : ℝ} (hp : p ∈ Icc (0:ℝ) 1) :
    RareSuccessSlope.phi n p ^ (1/((n:ℝ)-1)) = rootFactor n p := by
  have hcast : ((n-1:ℕ):ℝ) = (n:ℝ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]
  have hexp : 1/((n:ℝ)-1) = (((n-1:ℕ):ℝ))⁻¹ := by rw [hcast,one_div]
  rw [← rootFactor_pow hn hp,hexp]
  exact pow_rpow_inv_natCast (rootFactor_nonneg hn hp) (by omega)

theorem contDiff_H (n : ℕ) : ContDiff ℝ 1 (H n) := by
  unfold H
  fun_prop

theorem contDiff_Hslope (n : ℕ) : ContDiff ℝ 1 (Hslope n) := by
  unfold Hslope
  fun_prop

theorem contDiffOn_J {n : ℕ} (hn : 2 ≤ n) : ContDiffOn ℝ 1 (J n) (Icc (0:ℝ) 1) := by
  exact (contDiff_const.mul (contDiff_H n)).contDiffOn.div
    (contDiff_Hslope n).contDiffOn (fun p hp => (Hslope_pos hn hp).ne')

theorem contDiffOn_phi {n : ℕ} (hn : 2 ≤ n) :
    ContDiffOn ℝ 1 (RareSuccessSlope.phi n) (Icc (0:ℝ) 1) := by
  rw [show RareSuccessSlope.phi n = (fun p => J n p*(1-p)^(n-1)) from
    funext (phi_eq_J_mul_pow n)]
  exact (contDiffOn_J hn).mul (((contDiff_const.sub contDiff_id).pow (n-1)).contDiffOn)

theorem contDiffOn_rootFactor {n : ℕ} (hn : 2 ≤ n) :
    ContDiffOn ℝ 1 (rootFactor n) (Icc (0:ℝ) 1) := by
  exact ((contDiffOn_J hn).rpow_const_of_ne (fun p hp => (J_pos hn hp).ne')).mul
    ((contDiff_const.sub contDiff_id).contDiffOn)

private theorem exists_positive_lipschitz_of_contDiffOn {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Icc (0:ℝ) 1)) :
    ∃ K : ℝ, 0 < K ∧ ∀ p ∈ Icc (0:ℝ) 1, ∀ q ∈ Icc (0:ℝ) 1,
      |f p-f q| ≤ K*|p-q| := by
  obtain ⟨K,hK⟩ := hf.exists_lipschitzOnWith (by norm_num) (convex_Icc 0 1) isCompact_Icc
  refine ⟨(K:ℝ)+1,by positivity,?_⟩
  intro p hp q hq
  have hh := hK.dist_le_mul p hp q hq
  rw [Real.dist_eq,Real.dist_eq] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (by linarith : (K:ℝ) ≤ K+1) (abs_nonneg _))

theorem exists_lipschitz_J {n : ℕ} (hn : 2 ≤ n) :
    ∃ K : ℝ, 0 < K ∧ ∀ p ∈ Icc (0:ℝ) 1, ∀ q ∈ Icc (0:ℝ) 1,
      |J n p-J n q| ≤ K*|p-q| :=
  exists_positive_lipschitz_of_contDiffOn (contDiffOn_J hn)

theorem exists_lipschitz_phi {n : ℕ} (hn : 2 ≤ n) :
    ∃ K : ℝ, 0 < K ∧ ∀ p ∈ Icc (0:ℝ) 1, ∀ q ∈ Icc (0:ℝ) 1,
      |RareSuccessSlope.phi n p-RareSuccessSlope.phi n q| ≤ K*|p-q| :=
  exists_positive_lipschitz_of_contDiffOn (contDiffOn_phi hn)

theorem exists_lipschitz_rootFactor {n : ℕ} (hn : 2 ≤ n) :
    ∃ K : ℝ, 0 < K ∧ ∀ p ∈ Icc (0:ℝ) 1, ∀ q ∈ Icc (0:ℝ) 1,
      |rootFactor n p-rootFactor n q| ≤ K*|p-q| :=
  exists_positive_lipschitz_of_contDiffOn (contDiffOn_rootFactor hn)

end FCAppendix.PayOnce.ResponseFactor
