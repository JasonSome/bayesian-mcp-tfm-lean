import FCAppendix.Game.LocalInformation
import FCAppendix.Probability.IndependentCounts

namespace FCAppendix
namespace Game

variable {m c : ℕ}

abbrev FeasibleLocal (L : LocalList m) (c : ℕ) :=
  {S : Finset (Fin m) // S.card ≤ c ∧ ∀ i ∈ S, L i ≠ none}

abbrev LotteryPolicy (m c : ℕ) :=
  (L : LocalList m) → FiniteLaw (FeasibleLocal L c)

noncomputable def lotteryAccept (L : LocalList m) (S : FeasibleLocal L c) (i : Fin m) : Bool := by
  classical
  exact decide (i ∈ S.val)

noncomputable def localMarginal (policy : LotteryPolicy m c) (L : LocalList m) (i : Fin m) : ℝ :=
  IndependentCounts.acceptance (policy L) (fun S => lotteryAccept L S i)

theorem localMarginal_bounds (policy : LotteryPolicy m c) (L : LocalList m) (i : Fin m) :
    0 ≤ localMarginal policy L i ∧ localMarginal policy L i ≤ 1 :=
  ⟨(policy L).prob_nonneg _, (policy L).prob_le_one _⟩

theorem localMarginal_absent (policy : LotteryPolicy m c) (L : LocalList m) (i : Fin m)
    (hi : L i = none) : localMarginal policy L i = 0 := by
  classical
  have hno : ∀ S : FeasibleLocal L c, i ∉ S.val := by
    intro S hmem
    exact S.property.2 i hmem hi
  simp [localMarginal, IndependentCounts.acceptance, FiniteLaw.prob, lotteryAccept, hno]

noncomputable def commonListCount (policy : LotteryPolicy m c)
    (L : LocalList m) (i : Fin m) (k : ℕ) : CountLaw k :=
  IndependentCounts.independentCount (policy L) (fun S => lotteryAccept L S i) k

theorem commonListCount_binomial (policy : LotteryPolicy m c)
    (L : LocalList m) (i : Fin m) (k : ℕ) :
    commonListCount policy L i k = IndependentCounts.binomial k (localMarginal policy L i)
      (localMarginal_bounds policy L i).1 (localMarginal_bounds policy L i).2 :=
  IndependentCounts.independentCount_bernoulli (policy L) (fun S => lotteryAccept L S i) k

theorem commonListCount_success (policy : LotteryPolicy m c)
    (L : LocalList m) (i : Fin m) (k : ℕ) :
    (commonListCount policy L i k).success = 1 - (1 - localMarginal policy L i) ^ k := by
  rw [commonListCount_binomial, IndependentCounts.binomial_success]

theorem commonListCount_load (policy : LotteryPolicy m c)
    (L : LocalList m) (i : Fin m) (k : ℕ) :
    (commonListCount policy L i k).load = (k : ℝ) * localMarginal policy L i := by
  rw [commonListCount_binomial, IndependentCounts.binomial_load]

end Game
end FCAppendix
