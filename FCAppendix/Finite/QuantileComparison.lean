import FCAppendix.Finite.VisibleQuantiles
import FCAppendix.Finite.RankConcentration

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem quantile_comparison_of_gap (Γ : FiniteGame m n c Seed)
    (hm : 2 ≤ m) (hc0 : 0 < c) (hc : c ≤ m) (hΓ : IsAEEquilibrium Γ)
    (hp : ∀ j, ProposerRationalAtFeasibleLists Γ j) (hatom : PositiveVisibleAtomless Γ)
    (i : Fin m) (j : Fin n) (a : ℝ) (ha : 0 < a)
    (hA : ∀ r : ℕ, 0 < r → r ≤ n → a * (r : ℝ) ≤ Γ.A.charge r)
    (q q' d δ : ℝ) (hq : 0 < q) (hd : 0 < d) (hδ : 0 < δ)
    (hgap : δ ≤ (c : ℝ) - (m - 1 : ℕ) * q)
    (htail : Γ.F.real (Set.Ioi (Γ.g + d / ((m - 1 : ℕ) / (4 * δ ^ 2)))) ≤ q') :
    TailQuantile.quantile (alphaGt Γ j) q' ≤
      TailQuantile.quantile (alphaGt Γ j) q / a + 2 * d := by
  have hm0 : 0 < m := by omega
  have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
  let u := TailQuantile.quantile (alphaGt Γ j) q
  have hu : 0 ≤ u := visible_quantile_nonneg Γ hm0 hc0 hΓ j q hq
  let t := u / a + d
  have ht : 0 < t := add_pos_of_nonneg_of_pos (div_nonneg hu ha.le) hd
  let act : JointAction n := ⟨t, ht.le, 1, hn⟩
  let r : ℝ := (m - 1 : ℕ) / (4 * δ ^ 2)
  have hr : 0 < r := div_pos (Nat.cast_pos.mpr (by omega)) (by positivity)
  have hα : alphaGt Γ j (a * t) ≤ q := by
    have h := alphaGt_above_quantile Γ hm0 hc0 hΓ j q (a * d) hq (mul_pos ha hd)
    have he : a * t = u + a * d := by dsimp [t]; field_simp
    rw [he]
    exact h
  have hslot : δ ≤ (c : ℝ) - (m - 1 : ℕ) * alphaGt Γ j (a * t) := by
    have hmul := mul_le_mul_of_nonneg_left hα (Nat.cast_nonneg (m - 1) : (0 : ℝ) ≤ (m - 1 : ℕ))
    linarith
  have hsuccess : 1 - r ≤ meanAcceptProb Γ i t :=
    meanAcceptProb_lower_of_gap Γ hm0 hc hp hatom i j a ha hA t δ ht hδ hslot
  have htail' := alphaGt_singleton_price_le_value_tail Γ hm0 hc0 hΓ j i act rfl r hr hsuccess d hd
  have hu' := TailQuantile.le_of_tail_le (α := alphaGt Γ j) (show 0 ≤ t + d by positivity)
    (htail'.trans htail)
  dsimp only [t] at hu'
  linarith

end FCAppendix.Bayes
