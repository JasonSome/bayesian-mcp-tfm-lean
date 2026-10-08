import FCAppendix.Ample.ActualEventRate
import FCAppendix.Probability.FiniteTiltUniform

namespace FCAppendix.SimultaneousCongestion

open Finset Real CommonList
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem congestionProb_antitone_recipients (μ : FiniteLaw (Finset ι))
    {K L : Finset ι} (hKL : K ⊆ L) (N c : ℕ) :
    congestionProb μ L N c ≤ congestionProb μ K N c := by
  apply (iid μ N).prob_mono
  intro T hT s hs
  exact hT s (hKL hs)

theorem small_tilt_lower_bound {n N c : ℕ} (hn : 0 < n)
    (μ : FiniteLaw (Finset (Fin n)))
    (hsym : SwapInvariant μ (univ : Finset (Fin n)))
    {a b ρ δ : ℝ} (ha0 : 0 < a) (hb0 : 0 < b) (hδ : 0 < δ)
    (ha : a ≤ μ.prob (fun T => T.card = 1))
    (hb : b ≤ μ.prob (fun T => 2 ≤ T.card))
    (hm : (n : ℝ) * (ρ - 2 * δ) ≤ μ.expect (fun T => (T.card : ℝ)))
    (hsmall : 4 * n * δ ≤ exp (-(n : ℝ)) * min a b / 4)
    (hc : (c : ℝ) ≤ N * (ρ + δ))
    (hN : (n : ℝ) ≤ 2 * N * δ ^ 2) :
    exp (-((4 * n * δ / (exp (-(n : ℝ)) * min a b / 4)) * N * n)) / 2 ≤
      congestionProb μ (univ : Finset (Fin n)) N c := by
  classical
  let v : ℝ := exp (-(n : ℝ)) * min a b / 4
  let θ : ℝ := 4 * n * δ / v
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hv : 0 < v := div_pos (mul_pos (exp_pos _) (lt_min ha0 hb0)) (by norm_num)
  have hθ : 0 ≤ θ := (div_pos (by positivity) hv).le
  have hθ1 : θ ≤ 1 := (div_le_iff₀ hv).mpr (by simpa only [one_mul] using hsmall)
  have he : θ * v = 4 * n * δ := by dsimp [θ]; field_simp
  let X : Finset (Fin n) → ℝ := count (univ : Finset (Fin n))
  have hX (T : Finset (Fin n)) : X T = (T.card : ℝ) := by
    simp [X, count, selected]
  have hX0 : ∀ T, 0 ≤ X T := fun T => by rw [hX]; positivity
  have hXB : ∀ T, X T ≤ (n : ℝ) := by
    intro T
    rw [hX]
    exact_mod_cast (show T.card ≤ n by simpa using T.card_le_univ)
  have ha' : a ≤ μ.prob (fun T => X T = 1) := by
    convert ha using 1
    congr 1
    funext T
    rw [hX]
    norm_cast
  have hb' : b ≤ μ.prob (fun T => 2 ≤ X T) := by
    convert hb using 1
    congr 1
    funext T
    rw [hX]
    norm_cast
  have hm' : (n : ℝ) * (ρ - 2 * δ) ≤ μ.expect X := by
    have heq : X = fun T => (T.card : ℝ) := funext hX
    rwa [heq]
  have hraise := FiniteCramer.mean_ge_of_separated_classes μ X hX0 hXB ha' hb' hθ hθ1
  change μ.expect X + v * θ ≤ FiniteCramer.mean μ X θ at hraise
  have hmean : (n : ℝ) * (ρ + 2 * δ) ≤ FiniteCramer.mean μ X θ := by
    nlinarith
  have hmean' : ρ + 2 * δ ≤ tiltMean μ (univ : Finset (Fin n)) θ / n := by
    apply (le_div_iff₀ hnR).mpr
    change (ρ + 2 * δ) * (n : ℝ) ≤ FiniteCramer.mean μ X θ
    nlinarith
  have hcap : (c : ℝ) ≤ N *
      (tiltMean μ (univ : Finset (Fin n)) θ / (univ : Finset (Fin n)).card - δ) := by
    simp only [card_univ, Fintype.card_fin]
    have hgap : ρ + δ ≤ tiltMean μ (univ : Finset (Fin n)) θ / n - δ := by linarith
    exact hc.trans (mul_le_mul_of_nonneg_left hgap (Nat.cast_nonneg N))
  have hh := congestionProb_ge_half_exp_of_tilt_gap hsym N c hθ hδ
    (by simpa only [card_univ, Fintype.card_fin] using hN) hcap
  simpa only [card_univ, Fintype.card_fin, θ, v] using hh

theorem small_tilt_lower_bound_any_recipients {n N c : ℕ} (hn : 0 < n)
    (μ : FiniteLaw (Finset (Fin n)))
    (hsym : SwapInvariant μ (univ : Finset (Fin n)))
    {a b ρ δ : ℝ} (ha0 : 0 < a) (hb0 : 0 < b) (hδ : 0 < δ)
    (ha : a ≤ μ.prob (fun T => T.card = 1))
    (hb : b ≤ μ.prob (fun T => 2 ≤ T.card))
    (hm : (n : ℝ) * (ρ - 2 * δ) ≤ μ.expect (fun T => (T.card : ℝ)))
    (hsmall : 4 * n * δ ≤ exp (-(n : ℝ)) * min a b / 4)
    (hc : (c : ℝ) ≤ N * (ρ + δ))
    (hN : (n : ℝ) ≤ 2 * N * δ ^ 2) (K : Finset (Fin n)) :
    exp (-((4 * n * δ / (exp (-(n : ℝ)) * min a b / 4)) * N * n)) / 2 ≤
      congestionProb μ K N c :=
  (small_tilt_lower_bound hn μ hsym ha0 hb0 hδ ha hb hm hsmall hc hN).trans
    (congestionProb_antitone_recipients μ (subset_univ K) N c)

end FCAppendix.SimultaneousCongestion

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Finset Real
open scoped BigOperators

theorem ppi_failure_ge_small_tilt {n N c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame (N + 1) n c Seed) (hn : 0 < n)
    (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (i : Fin (N + 1)) (act : JointAction n) (hbid : 0 < act.bid)
    {a b ρ δ : ℝ} (ha0 : 0 < a) (hb0 : 0 < b) (hδ : 0 < δ)
    (ha : a ≤ visibleClassMass Γ act.bid 1)
    (hb : b ≤ (visibleLaw Γ act.bid).prob (fun T => 2 ≤ T.card))
    (hm : (n : ℝ) * (ρ - 2 * δ) ≤
      (visibleLaw Γ act.bid).expect (fun T => (T.card : ℝ)))
    (hsmall : 4 * n * δ ≤ exp (-(n : ℝ)) * min a b / 4)
    (hc : (c : ℝ) ≤ N * (ρ + δ)) (hN : (n : ℝ) ≤ 2 * N * δ ^ 2) :
    exp (-((4 * n * δ / (exp (-(n : ℝ)) * min a b / 4)) * N * n)) / 2 ≤
      1 - ((problem Γ i).outcome act).success := by
  have hsym : SimultaneousCongestion.SwapInvariant (visibleLaw Γ act.bid)
      (univ : Finset (Fin n)) := by
    rw [visibleLaw_eq_contactLaw]
    exact Ample.contactLaw_swapInvariant _ _ _ _
  have hh := SimultaneousCongestion.small_tilt_lower_bound_any_recipients hn
    (visibleLaw Γ act.bid) hsym ha0 hb0 hδ ha hb hm hsmall hc hN
    (Ample.selected n act.routeCount)
  rw [visibleLaw_eq_contactLaw, Ample.contactLaw_congestionProb,
    Ample.congestProbAt_eq_congestProb, Ample.card_selected act.routeCount_le] at hh
  rwa [ppi_failure_eq_congestProb Γ hA hatom hj i act hbid]

end FCAppendix.Bayes
