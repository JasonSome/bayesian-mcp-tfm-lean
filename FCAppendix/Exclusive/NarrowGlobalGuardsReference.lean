import FCAppendix.Exclusive.NarrowCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
namespace FCAppendix.Exclusive.Narrow.Global
open MeasureTheory Set Filter Topology

def costIntegral (d y : ℝ) : ℝ := ∫ t : ℝ in (0:ℝ)..1, Real.exp ((d-t)*y)

lemma costIntegral_strictMono (d : ℝ) (hd : 1 ≤ d) : StrictMono (costIntegral d) := by
  intro y z hyz
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    zero_lt_one (by fun_prop) (by fun_prop)
  · intro t ht
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hyz.le (by linarith [ht.2])
  · refine ⟨0,⟨le_refl 0,zero_le_one⟩,?_⟩
    apply Real.exp_lt_exp.mpr
    nlinarith

lemma costIntegral_formula (d y : ℝ) (hy : y ≠ 0) :
    costIntegral d y = Real.exp (d*y)*(1-Real.exp (-y))/y := by
  have hder (t : ℝ) : HasDerivAt (fun t : ℝ => -Real.exp ((d-t)*y)/y)
      (Real.exp ((d-t)*y)) t := by
    apply ((((((hasDerivAt_id t).const_sub d).mul_const y).exp).neg).div_const y).congr_deriv
    simp only [id_eq]
    field_simp [hy]
  have hcont : Continuous (fun t : ℝ => Real.exp ((d-t)*y)) := by fun_prop
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hder t) (hcont.intervalIntegrable 0 1)
  change costIntegral d y = _ at hFTC
  rw [hFTC]
  have he : Real.exp ((d-1)*y) = Real.exp (d*y)*Real.exp (-y) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [sub_zero,he]
  ring

def fixedSuccessCost (n : ℕ) (a : UserTariff) (lam A y : ℝ) : ℝ :=
  match a with
  | .unique => lam*A*Real.exp (-A)*costIntegral n y
  | .affine eta => (1-eta)*(lam*(1-Real.exp (-A))*Real.exp (((n:ℝ)-1)*y)) +
      eta*(lam*A*costIntegral ((n:ℝ)-1) y)

theorem fixedSuccessCost_strictMono (n : ℕ) (hn : 2 ≤ n) (a : UserTariff)
    (ha : a.Allowed) (lam A : ℝ) (hlam : 0 < lam) (hA : 0 < A) :
    StrictMono (fixedSuccessCost n a lam A) := by
  have hnR : (2 : ℝ) ≤ n := Nat.cast_le.mpr hn
  have hcoef : 0 < lam*(1-Real.exp (-A)) := by
    apply mul_pos hlam
    apply sub_pos.mpr
    exact Real.exp_lt_one_iff.mpr (by linarith)
  cases a with
  | unique =>
    intro y z hyz
    dsimp [fixedSuccessCost]
    exact mul_lt_mul_of_pos_left (costIntegral_strictMono n (by linarith) hyz)
      (mul_pos (mul_pos hlam hA) (Real.exp_pos _))
  | affine eta =>
    intro y z hyz
    have h0 : lam*(1-Real.exp (-A))*Real.exp (((n:ℝ)-1)*y) <
        lam*(1-Real.exp (-A))*Real.exp (((n:ℝ)-1)*z) :=
      mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr
        (mul_lt_mul_of_pos_left hyz (by linarith))) hcoef
    have h1 : lam*A*costIntegral ((n:ℝ)-1) y < lam*A*costIntegral ((n:ℝ)-1) z :=
      mul_lt_mul_of_pos_left (costIntegral_strictMono ((n:ℝ)-1) (by linarith) hyz)
        (mul_pos hlam hA)
    dsimp [fixedSuccessCost]
    by_cases he : eta = 1
    · simpa only [he,sub_self,zero_mul,one_mul,zero_add] using h1
    · have hleft := mul_lt_mul_of_pos_left h0 (sub_pos.mpr (lt_of_le_of_ne ha.2 he))
      have hright := mul_le_mul_of_nonneg_left h1.le ha.1
      linarith

theorem fixedSuccessCost_route_strict (n k l : ℕ) (hn : 2 ≤ n)
    (hk : 0 < k) (hkl : k < l) (a : UserTariff) (ha : a.Allowed)
    (lam A : ℝ) (hlam : 0 < lam) (hA : 0 < A) :
    fixedSuccessCost n a lam A (A/l) < fixedSuccessCost n a lam A (A/k) := by
  apply fixedSuccessCost_strictMono n hn a ha lam A hlam hA
  exact div_lt_div_of_pos_left hA (Nat.cast_pos.mpr hk) (Nat.cast_lt.mpr hkl)

theorem unique_full_route_endpoint_gap (d : ℕ) (hd : 1 ≤ d) (v lam p : ℝ)
    (hlam : 0 < lam) (hp : p < 1)
    (hFOC : v*(1-p)^d = lam) :
    (v*PayOnce.success (d+1) p-lam*((d+1:ℕ):ℝ)*p) -
      (v-lam*((d+1:ℕ):ℝ)) = (d:ℝ)*lam*(1-p) ∧
      v-lam*((d+1:ℕ):ℝ) < v*PayOnce.success (d+1) p-lam*((d+1:ℕ):ℝ)*p := by
  have he : (v*PayOnce.success (d+1) p-lam*((d+1:ℕ):ℝ)*p) -
      (v-lam*((d+1:ℕ):ℝ)) = (d:ℝ)*lam*(1-p) := by
    unfold PayOnce.success
    rw [pow_succ]
    have hh := congrArg (fun x : ℝ => x*(1-p)) hFOC
    push_cast
    nlinarith
  refine ⟨he,?_⟩
  have hpos : 0 < (d:ℝ)*lam*(1-p) :=
    mul_pos (mul_pos (Nat.cast_pos.mpr (by omega)) hlam) (sub_pos.mpr hp)
  linarith

theorem fixedSuccessCost_eq_binomial (n k : ℕ) (hk : 0 < k) (a : UserTariff)
    (lam y p : ℝ) (hy : 0 < y) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp : p = 1-Real.exp (-y)) :
    lam*Real.exp (((n:ℝ)-1)*y)*a.expected (IndependentCounts.binomial k p hp0 hp1) =
      fixedSuccessCost n a lam ((k:ℝ)*y) y := by
  have hkcast : ((k-1:ℕ):ℝ) = (k:ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k),Nat.cast_one]
  have hpow : (Real.exp (-y))^k = Real.exp (-(k:ℝ)*y) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  cases a with
  | unique =>
    rw [UserTariff.expected_unique_binomial]
    simp only [hp,sub_sub_cancel,fixedSuccessCost,costIntegral_formula n y hy.ne']
    have he : Real.exp (((n:ℝ)-1)*y)*(Real.exp (-y))^(k-1) =
        Real.exp (-((k:ℝ)*y))*Real.exp ((n:ℝ)*y) := by
      rw [← Real.exp_nat_mul,← Real.exp_add,← Real.exp_add,hkcast]
      congr 1
      ring
    calc
      lam*Real.exp (((n:ℝ)-1)*y)*((k:ℝ)*(1-Real.exp (-y))*(Real.exp (-y))^(k-1)) =
          lam*(k:ℝ)*(1-Real.exp (-y))*
            (Real.exp (((n:ℝ)-1)*y)*(Real.exp (-y))^(k-1)) := by ring
      _ = lam*(k:ℝ)*(1-Real.exp (-y))*
          (Real.exp (-((k:ℝ)*y))*Real.exp ((n:ℝ)*y)) := by rw [he]
      _ = _ := by field_simp [hy.ne']
  | affine eta =>
    rw [UserTariff.expected_affine_binomial]
    simp only [hp,PayOnce.success,sub_sub_cancel,hpow,fixedSuccessCost,
      costIntegral_formula ((n:ℝ)-1) y hy.ne']
    field_simp [hy.ne']

def bidCostAtSuccess (n k : ℕ) (a : UserTariff) (lam A : ℝ) : ℝ :=
  lam*Real.exp (((n:ℝ)-1)*(A/k))*
    binomialPolynomial k a.charge (1-Real.exp (-(A/k)))

lemma bidCostAtSuccess_eq (n k : ℕ) (hk : 0 < k) (a : UserTariff)
    (lam A : ℝ) (hA : 0 < A) :
    bidCostAtSuccess n k a lam A = fixedSuccessCost n a lam A (A/k) := by
  have hkR : (0:ℝ) < k := Nat.cast_pos.mpr hk
  have hy : 0 < A/(k:ℝ) := div_pos hA hkR
  have hp0 : 0 ≤ 1-Real.exp (-(A/(k:ℝ))) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have hp1 : 1-Real.exp (-(A/(k:ℝ))) ≤ 1 := by linarith [Real.exp_pos (-(A/(k:ℝ)))]
  unfold bidCostAtSuccess
  rw [binomialPolynomial_eq_expect k a.charge _ hp0 hp1]
  have h := fixedSuccessCost_eq_binomial n k hk a lam (A/k) _ hy hp0 hp1 rfl
  have he : (k:ℝ)*(A/(k:ℝ)) = A := by field_simp
  simpa only [he,UserTariff.expected] using h

theorem bidCostAtSuccess_route_strict (n k l : ℕ) (hn : 2 ≤ n)
    (hk : 0 < k) (hkl : k < l) (a : UserTariff) (ha : a.Allowed)
    (lam A : ℝ) (hlam : 0 < lam) (hA : 0 < A) :
    bidCostAtSuccess n l a lam A < bidCostAtSuccess n k a lam A := by
  rw [bidCostAtSuccess_eq n l (by omega) a lam A hA,bidCostAtSuccess_eq n k hk a lam A hA]
  exact fixedSuccessCost_route_strict n k l hn hk hkl a ha lam A hlam hA

lemma prescribed_success (k : ℕ) (hk : 0 < k) (A : ℝ) :
    PayOnce.success k (1-Real.exp (-(A/(k:ℝ)))) = 1-Real.exp (-A) := by
  unfold PayOnce.success
  simp only [sub_sub_cancel]
  rw [← Real.exp_nat_mul]
  have hkR : (k:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  congr 2
  field_simp

theorem reference_payoff_route_strict (n k l : ℕ) (hn : 2 ≤ n)
    (hk : 0 < k) (hkl : k < l) (a : UserTariff) (ha : a.Allowed)
    (lam A v : ℝ) (hlam : 0 < lam) (hA : 0 < A) :
    v*PayOnce.success k (1-Real.exp (-(A/(k:ℝ))))-bidCostAtSuccess n k a lam A <
      v*PayOnce.success l (1-Real.exp (-(A/(l:ℝ))))-bidCostAtSuccess n l a lam A := by
  rw [prescribed_success k hk,prescribed_success l (by omega)]
  linarith [bidCostAtSuccess_route_strict n k l hn hk hkl a ha lam A hlam hA]

end FCAppendix.Exclusive.Narrow.Global
