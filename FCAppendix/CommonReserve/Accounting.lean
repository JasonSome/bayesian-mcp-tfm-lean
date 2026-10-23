import FCAppendix.CommonReserve.Actions
import FCAppendix.Finite.NestedRouting

noncomputable section
namespace FCAppendix.CommonReserve
open Game
open scoped BigOperators
variable {m n c : ℕ} {r : ℝ} {Seed : Type*}

def payment (x : Profile m n r) (policy : Fin n → LocalPolicy m c Seed)
    (seed : Fin n → Seed) (i : Fin m) : ℝ :=
  ∑ j ∈ accepted x policy seed i, Bayes.entryBid ((x i).val j)

def shortfall (p : ℝ) (x : Profile m n r) (policy : Fin n → LocalPolicy m c Seed)
    (seed : Fin n → Seed) (i : Fin m) : ℝ :=
  ∑ j ∈ accepted x policy seed i, max (p - Bayes.entryBid ((x i).val j)) 0

def payoff (v g : ℝ) (G : Schedule n) (x : Profile m n r)
    (policy : Fin n → LocalPolicy m c Seed) (seed : Fin n → Seed) (i : Fin m) : ℝ :=
  v * successIndicator (count x policy seed i) - payment x policy seed i -
    g * G.charge (count x policy seed i)

theorem shortfall_nonneg (p : ℝ) (x : Profile m n r)
    (policy : Fin n → LocalPolicy m c Seed) (seed : Fin n → Seed) (i : Fin m) :
    0 ≤ shortfall p x policy seed i :=
  Finset.sum_nonneg fun _ _ => le_max_right _ _

theorem reserve_payment (x : Profile m n r) (policy : Fin n → LocalPolicy m c Seed)
    (seed : Fin n → Seed) (i : Fin m) : r * count x policy seed i ≤ payment x policy seed i := by
  classical
  calc
    _ = ∑ _j ∈ accepted x policy seed i, r := by simp [count, mul_comm]
    _ ≤ _ := Finset.sum_le_sum fun j hj => bid_ge_reserve x policy seed i j hj

theorem price_payment (p : ℝ) (x : Profile m n r) (policy : Fin n → LocalPolicy m c Seed)
    (seed : Fin n → Seed) (i : Fin m) :
    p * count x policy seed i - shortfall p x policy seed i ≤ payment x policy seed i := by
  classical
  have h := Finset.sum_le_sum (s := accepted x policy seed i)
    (fun j _ => show p - max (p - Bayes.entryBid ((x i).val j)) 0 ≤
      Bayes.entryBid ((x i).val j) from by linarith [le_max_left (p - Bayes.entryBid ((x i).val j)) 0])
  simpa [Finset.sum_sub_distrib, shortfall, payment, count, mul_comm] using h

theorem base_charge_ge_success (G : Schedule n) (K : ℕ) (hK : K ≤ n) :
    successIndicator K ≤ G.charge K := by
  by_cases hz : K = 0
  · simp [hz, successIndicator, G.zero]
  · simpa [successIndicator, hz] using G.lower K (by omega) hK

theorem payoff_le_price_error (v g p : ℝ) (hg : 0 ≤ g) (G : Schedule n)
    (x : Profile m n r) (policy : Fin n → LocalPolicy m c Seed)
    (seed : Fin n → Seed) (i : Fin m) :
    payoff v g G x policy seed i ≤
      (v - g - p) * successIndicator (count x policy seed i) -
      p * ((count x policy seed i : ℝ) - successIndicator (count x policy seed i)) +
      shortfall p x policy seed i := by
  have hp := price_payment p x policy seed i
  have hG := mul_le_mul_of_nonneg_left
    (base_charge_ge_success G _ (count_le x policy seed i)) hg
  unfold payoff
  nlinarith

theorem payoff_le_reserve (v g : ℝ) (hr : 0 ≤ r) (hg : 0 ≤ g) (G : Schedule n)
    (x : Profile m n r) (policy : Fin n → LocalPolicy m c Seed)
    (seed : Fin n → Seed) (i : Fin m) :
    payoff v g G x policy seed i ≤ max (v - g - r) 0 := by
  have hT := reserve_payment x policy seed i
  have hS := successIndicator_le_count (count x policy seed i)
  have hG := mul_le_mul_of_nonneg_left
    (base_charge_ge_success G _ (count_le x policy seed i)) hg
  have hrS := mul_le_mul_of_nonneg_left hS hr
  have h01 := successIndicator_nonneg (count x policy seed i)
  have h11 := successIndicator_le_one (count x policy seed i)
  have hnet : (v - g - r) * successIndicator (count x policy seed i) ≤ max (v - g - r) 0 := by
    by_cases h : 0 ≤ v - g - r
    · rw [max_eq_left h]
      nlinarith
    · rw [max_eq_right (le_of_not_ge h)]
      exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) h01
  unfold payoff
  nlinarith

end FCAppendix.CommonReserve
